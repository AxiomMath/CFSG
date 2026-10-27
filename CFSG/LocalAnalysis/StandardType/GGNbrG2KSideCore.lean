module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2KSideField
public import CFSG.LocalAnalysis.StandardType.GGNbrG2KSidePSL
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffCard
public import CFSG.LocalAnalysis.StandardType.GGNbrG2ThreeOffCover
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem ggNbrG2K_three_dvd {n : ℕ} (h6 : 6 ∣ n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := h6
  have h64 : (2 : ℕ) ^ (6 * k) = 64 ^ k := by rw [pow_mul]; norm_num
  have h1 : 1 ≡ 64 ^ k [MOD 3] := by
    have := (Nat.ModEq.pow k (show 64 ≡ 1 [MOD 3] by decide)).symm
    simpa using this
  rw [h64]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h1

private theorem ggNbrG2K_mem_normalizer_inf {G : Type} [Group G] {A C : Subgroup G} {b : G}
    (hA : b ∈ Subgroup.normalizer (A : Set G)) (hC : b ∈ Subgroup.normalizer (C : Set G)) :
    b ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hC h]

private theorem ggNbrG2K_markEquiv
    {G : Type} [Group G] {K : Subgroup G} (hK : commutator K = ⊤)
    {F : Type} [Field F] [Finite F] (h5 : 5 ≤ Nat.card F)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.G2 F) :
    ∃ θ' : K ≃* adjointGroup Tag.G2 F, ∀ k : K, θ' k = θ (k : K ⧸ Subgroup.center K) :=
  have hinj : Function.Injective (ggQuotHom θ) :=
    ggNbrG2Off_cover_injective h5 (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hK
  ⟨MulEquiv.ofBijective (ggQuotHom θ) ⟨hinj, ggQuotHom_surjective θ⟩, fun _ => rfl⟩

theorem ggNbrG2KSide_core
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hKperf : commutator K = ⊤) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (h6 : 6 ∣ n)
    (θ : K ⧸ Subgroup.center K ≃* adjointGroup Tag.G2 F)
    (hI : ggLAut K θ ⟨x, hxK⟩ ∈ (MulAut.conj : adjointGroup Tag.G2 F →*
      MulAut (adjointGroup Tag.G2 F)).range)
    (hcard : Nat.card (ggFix (K.normalizerMonoidHom ⟨x, hxK⟩)) = ggG2SL3Card n) :
    Nat.card B = 3 ^ 4 ∧
      (∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ n ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* projectiveSL 3 F')) ∧
      ∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (J : Set G),
        ¬ GGInnDiagPSL3 (2 ^ n) (↥J ⧸ Subgroup.center ↥J) (ggJQAut J b hb) := by
  classical
  have hn : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    simp [hF] at this
  have h6n : 6 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h6
  have h5 : 5 ≤ Nat.card F := by
    rw [hF]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    exact ggNbrG2K_three_dvd h6
  obtain ⟨θ', hθ'⟩ := ggNbrG2K_markEquiv hKperf h5 θ
  obtain ⟨s, hs⟩ := hI
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hS : LargeEvenSHat 3 B y K := hnb.1
  have hsx : ∀ k : K, θ' (ggGamma K hN ⟨x, hxBs⟩ k) = s * θ' k * s⁻¹ := by
    intro k
    have h1 := ggLAut_apply K θ ⟨x, hxK⟩ k
    rw [← hs, MulAut.conj_apply] at h1
    rw [hθ', hθ']
    exact h1.symm
  have hs1 : s ≠ 1 := by
    intro h1
    refine not_mem_centralizer_of_nbr hnb
      (mem_centralizer_of_ggLAut_eq_one K θ hKperf (g := ⟨x, hxK⟩) ?_)
    rw [← hs, h1, map_one]
  have hfix : (ggFix (ggGamma K hN ⟨x, hxBs⟩)).map θ'.toMonoidHom =
      Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F)) := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hsx k
      rw [mem_ggFix.mp hk] at h1
      show θ' k * s = s * θ' k
      calc θ' k * s = (s * θ' k * s⁻¹) * s := by rw [← h1]
        _ = s * θ' k := by group
    · intro hg
      obtain ⟨k, rfl⟩ := θ'.surjective g
      refine ⟨k, mem_ggFix.mpr ?_, rfl⟩
      apply θ'.injective
      rw [hsx k]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc s * θ' k * s⁻¹ = θ' k * s * s⁻¹ := by rw [h1]
        _ = θ' k := by group
  have hcardΓ : Nat.card (Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) =
      ggG2SL3Card n := by
    rw [← hfix, Subgroup.card_map_of_injective θ'.injective]
    exact hcard
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  let ρ : Bs →* MulAut (adjointGroup Tag.G2 F) := (MulAut.congr θ').toMonoidHom.comp (ggGamma K hN)
  have hρ : ∀ (b : Bs) (k : K), ρ b (θ' k) = θ' (ggGamma K hN b k) := fun b k => by
    simp [ρ, MulAut.congr_apply]
  have hA : IsElemAbelian 3 ρ.range := isElemAbelian_range hBc hBp ρ
  have hcardA : Nat.card ρ.range = Nat.card (ggGamma K hN).range := by
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective (MulAut.congr θ').injective]
  have h27 : 27 ≤ Nat.card ρ.range := by
    rw [hcardA]
    exact le_trans (by norm_num) (pow_three_le_card_range_ggGamma_bstar hcfg hnb hN)
  obtain ⟨hA27, hAI9⟩ := ggNbrG2Off_elemAbelian_card hF (by omega) ρ.range hA h27
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
  have hle : (ggGamma K hBN).range ≤ (ggGamma K hN).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hγ27 : Nat.card (ggGamma K hN).range = 27 := by
    rw [← hcardA]
    exact hA27
  have heq : (ggGamma K hBN).range = (ggGamma K hN).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hγ27]
    have h4' : 81 ≤ Nat.card (ggGamma K hBN).range * 3 := by
      rw [hcA]
      exact le_trans (by norm_num) h4
    omega
  have hB81 : Nat.card B = 3 ^ 4 := by
    have h : Nat.card B = 27 * 3 := by rw [← hcA, heq, hγ27]
    simpa using h
  have hex : ∃ α ∈ ρ.range,
      α ∉ (MulAut.conj : adjointGroup Tag.G2 F →* MulAut (adjointGroup Tag.G2 F)).range := by
    by_contra hcon
    push Not at hcon
    have hle' : ρ.range ≤
        (MulAut.conj : adjointGroup Tag.G2 F →* MulAut (adjointGroup Tag.G2 F)).range :=
      fun α hα => hcon α hα
    rw [inf_eq_left.mpr hle'] at hAI9
    omega
  obtain ⟨α, hαA, hαInn⟩ := hex
  obtain ⟨b₀, rfl⟩ := hαA
  obtain ⟨b, hb⟩ : ggGamma K hN b₀ ∈ (ggGamma K hBN).range := by
    rw [heq]
    exact ⟨b₀, rfl⟩
  have hsA : (MulAut.conj s : MulAut (adjointGroup Tag.G2 F)) ∈ ρ.range := by
    refine ⟨⟨x, hxBs⟩, MulEquiv.ext fun g => ?_⟩
    obtain ⟨k, rfl⟩ := θ'.surjective g
    rw [hρ, MulAut.conj_apply]
    exact hsx k
  obtain ⟨e, σ, d, hσ, hed⟩ := ggNbrG2K_field_part hF h6 ρ.range hA h27 hsA hs1 hcardΓ
    (⟨b₀, rfl⟩ : ρ b₀ ∈ ρ.range) hαInn
  obtain ⟨hJK, hJcomp⟩ := isComponentOf_comap_ggFix_ggGamma_x hLB hP hcfg hnb hN hxBs
  let eC : ↥(ggFix (ggGamma K hN ⟨x, hxBs⟩)) ≃*
      ↥(Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F))) :=
    (Subgroup.equivMapOfInjective _ θ'.toMonoidHom θ'.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let E₁ := eC.trans e
  have hQ : CFSG.IsQuasisimple ↥(ggFix (ggGamma K hN ⟨x, hxBs⟩)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv E₁.symm
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (K := F) (n := 3) le_rfl)
  have hJC : J.comap K.subtype = ggFix (ggGamma K hN ⟨x, hxBs⟩) :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJcomp
      ⟨le_rfl, IsSubnormal.refl _,
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQ⟩
      hJcomp.1
  have hJeq : J = K ⊓ Subgroup.centralizer ({x} : Set G) := by
    have h1 : (ggFix (ggGamma K hN ⟨x, hxBs⟩)).map K.subtype =
        K ⊓ Subgroup.centralizer ({x} : Set G) := map_ggFix_ggGamma K hN ⟨x, hxBs⟩
    have hle : J ≤ K.subtype.range := by
      rw [Subgroup.range_subtype]
      exact hJK
    rw [← hJC, Subgroup.map_comap_eq_self hle] at h1
    exact h1
  have hbJ : (b : G) ∈ Subgroup.normalizer (J : Set G) := by
    have hxb : (b : G) * x = x * b := IsElemAbelian.comm hBs (hBBs b.2) hxBs
    rw [hJeq]
    exact ggNbrG2K_mem_normalizer_inf (hBN b.2)
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hxb))
  have hmem : ∀ k : K, (k : G) ∈ J →
      θ' k ∈ Subgroup.centralizer ({s} : Set (adjointGroup Tag.G2 F)) := by
    intro k hk
    have hk' : k ∈ ggFix (ggGamma K hN ⟨x, hxBs⟩) := by
      rw [← hJC]
      exact hk
    rw [← hfix]
    exact ⟨k, hk', rfl⟩
  let E : ↥J ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (Subgroup.subgroupOfEquivOfLe hJK).symm.trans ((MulEquiv.subgroupCongr hJC).trans E₁)
  have hE : ∀ (j : J) (k : K) (hk : (k : G) = j),
      E j = e ⟨θ' k, hmem k (by rw [hk]; exact j.2)⟩ := by
    intro j k hk
    obtain rfl : k = ⟨j, hJK j.2⟩ := Subtype.ext hk
    rfl
  have hβ : ∀ j : J, E (J.normalizerMonoidHom ⟨b, hbJ⟩ j) =
      d * Matrix.SpecialLinearGroup.map σ.toRingHom (E j) * d⁻¹ := by
    intro j
    have hj : (j : G) ∈ K := hJK j.2
    have hk₂G : ((ggGamma K hBN b ⟨j, hj⟩ : K) : G) = (b : G) * (j : G) * (b : G)⁻¹ :=
      ggGamma_coe K hBN b ⟨j, hj⟩
    have hk₂J : ((ggGamma K hBN b ⟨j, hj⟩ : K) : G) ∈ J := by
      rw [hk₂G]
      exact (J.normalizerMonoidHom ⟨b, hbJ⟩ j).2
    have hθk₂ : θ' (ggGamma K hBN b ⟨j, hj⟩) = ρ b₀ (θ' ⟨j, hj⟩) := by
      rw [hρ, ← hb]
    have h1 := hed ⟨θ' ⟨j, hj⟩, hmem ⟨j, hj⟩ j.2⟩
      ⟨θ' (ggGamma K hBN b ⟨j, hj⟩), hmem _ hk₂J⟩ hθk₂
    rw [hE j ⟨j, hj⟩ rfl, hE (J.normalizerMonoidHom ⟨b, hbJ⟩ j) (ggGamma K hBN b ⟨j, hj⟩) hk₂G]
    exact h1
  obtain ⟨hne, hinn⟩ := ggNbrG2K_psl_not_innDiag h3 E (J.normalizerMonoidHom ⟨b, hbJ⟩) d hσ hβ
  refine ⟨hB81, ⟨F, inferInstance, inferInstance, hF, hne⟩, b, b.2, hbJ, ?_⟩
  rw [← hF]
  exact hinn

end CFSG.StandardType

end
