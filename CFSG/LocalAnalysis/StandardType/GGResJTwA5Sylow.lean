module

public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalTorus
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped Pointwise

theorem ggPGroup_le_centralizer_of_automizer {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hBs : IsMulCommutative Bs) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hA : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1)
    {S : Subgroup G} (hSp : IsPGroup p S) (hBsS : Bs ≤ S) (hSH : S ≤ Bs ⊔ J) :
    S ≤ Subgroup.centralizer (Bs : Set G) := by
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBs.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsC : Bs ≤ Subgroup.centralizer (Bs : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b hb a ha
  have hHmul : ((Bs ⊔ J : Subgroup G) : Set G) = (Bs : Set G) * (J : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Bs J hN
  have hstep1 : ∀ s ∈ S, s ∈ Subgroup.normalizer (Bs : Set G) →
      s ∈ Subgroup.centralizer (Bs : Set G) := by
    intro s hsS hsN
    have hsH : s ∈ ((Bs ⊔ J : Subgroup G) : Set G) := hSH hsS
    rw [hHmul] at hsH
    obtain ⟨b, hb, j, hj, rfl⟩ := Set.mem_mul.mp hsH
    have hbN : b ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.le_normalizer hb
    have hjN : j ∈ Subgroup.normalizer (Bs : Set G) := by
      have hj' : j = b⁻¹ * (b * j) := by group
      rw [hj']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hbN) hsN
    set φ : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨b * j, hsN⟩ with hφ
    have hφapp : ∀ c : ↥Bs, ((φ c : ↥Bs) : G) = b * j * c * (b * j)⁻¹ := fun c => rfl
    have hφind : φ ∈ ggInduced J Bs := by
      refine ⟨j, hj, hjN, fun c => ?_⟩
      rw [hφapp]
      have hjc : j * c * j⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hjN c).mp c.2
      calc b * j * c * (b * j)⁻¹ = b * (j * c * j⁻¹) * b⁻¹ := by group
        _ = j * c * j⁻¹ * b * b⁻¹ := by rw [hcomm b hb _ hjc]
        _ = j * c * j⁻¹ := by group
    obtain ⟨k, hk⟩ := hSp ⟨b * j, hsS⟩
    have hφk : φ ^ p ^ k = 1 := by
      have hk' : (⟨b * j, hsN⟩ : ↥(Subgroup.normalizer (Bs : Set G))) ^ p ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [hφ, ← map_pow, hk', map_one]
    have hφ1 := hA φ (Subgroup.subset_closure hφind) k hφk
    refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    have hfix := congrArg Subtype.val (DFunLike.congr_fun hφ1 ⟨c, hc⟩)
    rw [hφapp, MulAut.one_apply] at hfix
    calc c * (b * j) = b * j * c * (b * j)⁻¹ * (b * j) := by rw [hfix]
      _ = b * j * c := by group
  set T : Subgroup G := S ⊓ Subgroup.centralizer (Bs : Set G) with hT
  have hTS : T ≤ S := inf_le_left
  have hBsT : Bs ≤ T := le_inf hBsS hBsC
  have hconj : ∀ y ∈ Subgroup.normalizer (T : Set G), ∀ c ∈ Bs, y * c * y⁻¹ ∈ Bs := by
    intro y hy c hc
    have hyc : y * c * y⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hy c).mp (hBsT hc)
    refine hSC _ hyc.2 ?_
    rw [conj_pow, hBp c hc, mul_one, mul_inv_cancel]
  have hNT : S ⊓ Subgroup.normalizer (T : Set G) ≤ T := by
    rintro z ⟨hzS, hzN⟩
    have hzNBs : z ∈ Subgroup.normalizer (Bs : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨hconj z hzN c, fun h => ?_⟩
      have h' := hconj z⁻¹ (Subgroup.inv_mem _ hzN) _ h
      have he : z⁻¹ * (z * c * z⁻¹) * z⁻¹⁻¹ = c := by group
      rwa [he] at h'
    exact ⟨hzS, hstep1 z hzS hzNBs⟩
  by_contra hne
  have hlt : T < S := lt_of_le_of_ne hTS fun h => hne (h ▸ inf_le_right)
  exact lt_irrefl T ((CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hSp hlt).trans_le hNT)

theorem ggSylow_exists_conj_mem_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hBs : IsMulCommutative Bs) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hA : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ p ^ k = 1 → a = 1)
    {P : Subgroup G} (hP : IsPGroup p P) (hPJ : P ≤ J) :
    ∃ g ∈ J, ∀ u ∈ P, g * u * g⁻¹ ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  have hBsp : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBp b b.2)⟩
  set H : Subgroup G := Bs ⊔ J with hHdef
  have hHmul : (H : Set G) = (Bs : Set G) * (J : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Bs J hN
  obtain ⟨Q, hQ⟩ := (hBsp.comap_of_injective H.subtype Subtype.coe_injective).exists_le_sylow
  set S : Subgroup G := (Q : Subgroup H).map H.subtype with hSdef
  have hSp : IsPGroup p S := Q.isPGroup'.map _
  have hSH : S ≤ H := Subgroup.map_subtype_le _
  have hBsS : Bs ≤ S := fun b hb =>
    ⟨⟨b, Subgroup.mem_sup_left hb⟩, hQ (Subgroup.mem_comap.mpr hb), rfl⟩
  have hstep2 : S ≤ Subgroup.centralizer (Bs : Set G) :=
    ggPGroup_le_centralizer_of_automizer hBs hBp hSC hN hA hSp hBsS hSH
  obtain ⟨Q₁, hQ₁⟩ := (hP.comap_of_injective H.subtype Subtype.coe_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H Q₁ Q
  have hcS : ∀ u ∈ P, (c : G) * u * (c : G)⁻¹ ∈ S := by
    intro u hu
    have hu' : (⟨u, Subgroup.mem_sup_right (hPJ hu)⟩ : H) ∈ (Q₁ : Subgroup H) :=
      hQ₁ (Subgroup.mem_comap.mpr hu)
    have hmem : MulAut.conj c • (⟨u, Subgroup.mem_sup_right (hPJ hu)⟩ : H) ∈
        (Q : Subgroup H) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hu'
    exact ⟨_, hmem, rfl⟩
  have hcH : (c : G) ∈ (H : Set G) := c.2
  rw [hHmul] at hcH
  obtain ⟨b, hb, j, hj, hbj⟩ := Set.mem_mul.mp hcH
  refine ⟨j, hj, fun u hu => ?_⟩
  have hx := hstep2 (hcS u hu)
  rw [← hbj] at hx
  have hcommb := Subgroup.mem_centralizer_iff.mp hx b hb
  have he : j * u * j⁻¹ = b * j * u * (b * j)⁻¹ := by
    calc j * u * j⁻¹ = b⁻¹ * ((b * j * u * (b * j)⁻¹) * b) := by group
      _ = b⁻¹ * (b * (b * j * u * (b * j)⁻¹)) := by rw [← hcommb]
      _ = b * j * u * (b * j)⁻¹ := by group
  rw [he]
  exact hx

theorem card_le_card_range_ggGamma_mul_of_conj {G : Type} [Group G] [Finite G]
    {Bs J E : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {g : G} (hg : g ∈ J)
    (hE : ∀ u ∈ E, g * u * g⁻¹ ∈ Bs) :
    Nat.card E ≤
      Nat.card (ggGamma J hN).range * Nat.card ↥(E ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  let c : E →* Bs :=
    { toFun := fun u => ⟨g * u * g⁻¹, hE u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let f : E →* MulAut J := (ggGamma J hN).comp c
  have hker : f.ker = (Subgroup.centralizer (J : Set G)).subgroupOf E := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ggGamma J hN (c u) = 1 ↔ _
    rw [ggGamma_eq_one_iff]
    change g * (u : G) * g⁻¹ ∈ Subgroup.centralizer (J : Set G) ↔
      (u : G) ∈ Subgroup.centralizer (J : Set G)
    constructor
    · intro h
      have hgu : g * (g * u * g⁻¹) = g * u * g⁻¹ * g := Subgroup.mem_centralizer_iff.mp h g hg
      have hfix : g * (u : G) * g⁻¹ = u := by
        have h2 : g * (g * u * g⁻¹) = g * u := by rw [hgu]; group
        exact mul_left_cancel h2
      rwa [hfix] at h
    · intro h
      have hgu : g * (u : G) = u * g := Subgroup.mem_centralizer_iff.mp h g hg
      have hfix : g * (u : G) * g⁻¹ = u := by rw [hgu]; group
      rwa [hfix]
  have hcount := TableB.card_range_mul_card_ker f
  have hkerCard : Nat.card f.ker = Nat.card ↥(E ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card f.range ≤ Nat.card (ggGamma J hN).range := by
    refine Subgroup.card_le_of_le ?_
    rw [MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  rw [hkerCard] at hcount
  rw [← hcount]
  exact Nat.mul_le_mul_right _ hrange

theorem largeEvenLabelAll_centralLift81_twA5 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTwA5PlusThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (Y : Type) [Group Y] (φ : Y →* R),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Y →
        ∃ U : Subgroup Y, CFSG.Open.IsElemAbelian 3 U ∧ Nat.card (U.map φ) = 3 ^ 4 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, -, h3⟩ := h
  dsimp only at ht hl h3 ⊢
  subst ht hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro Y _ φ hφ hker
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have h2 : (-1 : K) = 1 := CharTwo.neg_eq 1
  have h3K : 3 ∣ Nat.card Kˣ := by
    have hsq := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow] at hsq
    rw [Nat.card_units, hK, hsq]
    exact Dvd.dvd.mul_right h3 _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3K
  have hωq : ω ^ (2 ^ n + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hω]
    exact h3
  exact CFSG.LocalAnalysis.GLTheoremA.S171Extremal.exists_elemAbelian_card_map_eq h2 hω
    (pow_ne_zero _ two_ne_zero) hωq φ hφ hker

theorem GGResHyp.pow_four_le_card_gamma_J_of_twA5PlusThree_of_sq {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTwA5PlusThreeLabel p Bs J)
    (hA : ∀ a ∈ ggAutomizer J Bs, a ^ 2 = 1) :
    p ^ 4 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range := by
  classical
  have hBs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTwA5PlusThreeLabel p lab)
    (P' := fun R _ _ _ => ∀ (Y : Type) [Group Y] (φ : Y →* R),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Y →
        ∃ U : Subgroup Y, CFSG.Open.IsElemAbelian 3 U ∧ Nat.card (U.map φ) = 3 ^ 4)
    (fun _ hΛ h => largeEvenLabelAll_centralLift81_twA5 hΛ h)
    (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, -, hp3, -⟩, -⟩, hR⟩ := largeEvenRawDatum_exists hraw
  subst hp3
  let φ : ↥J →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
  have hφs : Function.Surjective φ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center ↥J := by
    ext u
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨U, hU, hcard⟩ := hR ↥J φ hφs hker.le
  obtain ⟨E, hEJ, hEab, hE4⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S171Extremal.exists_of_map_card φ hker hU hcard.ge
  have hAp : ∀ a ∈ ggAutomizer J Bs, ∀ k : ℕ, a ^ 3 ^ k = 1 → a = 1 := by
    intro a ha k hk
    have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have hd : orderOf a ∣ Nat.gcd 2 (3 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hA a ha)) (orderOf_dvd_of_pow_eq_one hk)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at hd
    exact orderOf_eq_one_iff.mp hd
  obtain ⟨g, hg, hgE⟩ := ggSylow_exists_conj_mem_centralizer hBs.1 hBs.2 hSC
    hH.Bs_le_normalizer_J hAp (CFSG.Open.IsElemAbelian.isPGroup hEab) hEJ
  have hgBs : ∀ u ∈ E, g * u * g⁻¹ ∈ Bs := fun u hu =>
    hSC _ (hgE u hu) (by rw [conj_pow, hEab.2 u hu, mul_one, mul_inv_cancel])
  have hle := card_le_card_range_ggGamma_mul_of_conj hH.Bs_le_normalizer_J hg hgBs
  exact Nat.le_of_mul_le_mul_right (hE4.trans hle) Nat.card_pos

section Lift

theorem GGResHyp.card_lt_of_twA5PlusThree_of_card_lt {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTwA5PlusThreeLabel p Bs J)
    (h4 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range < p ^ 4) :
    Nat.card Bs < p ^ 6 := by
  have hp : p.Prime := Fact.out
  have hBs := hH.1.tableB_facts.2.1
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTwA5PlusThreeLabel p lab)
    (P' := fun R _ _ _ => GGTorusLift p (ggUnitaryTorusRank p (5 + 1)) R)
    (fun lab hΛ h => by
      have hl := largeEvenLabelAll_torusLift_twA hΛ h.1 hp (by rw [h.2.2.1]; exact h.2.2.2)
      rwa [h.2.1] at hl)
    (fun _ _ _ _ _ _ hP => hP.1) hJ
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, -, hp3, -⟩, -⟩, hLift⟩ := largeEvenRawDatum_exists hraw
  subst hp3
  have hr : ggUnitaryTorusRank 3 (5 + 1) = 3 := by decide
  rw [hr] at hLift
  have hpre : LargeEvenStdSubPre 3 B x L D J := hH.1.2.2.1
  have hJperf : commutator ↥J = ⊤ := hpre.2.2.2.2.2.1.2.2.1
  have hC := CFSG.LocalAnalysis.GLTheoremA.S265.SF.pow_mul_card_le_of_torusLift
    (Ω := G) (K := J) (D := Bs ⊓ Subgroup.centralizer (J : Set G)) Nat.prime_three hJperf θ
    hLift (CFSG.Open.IsElemAbelian.mono hBs inf_le_left) inf_le_right
  have hrank : CFSG.Open.GLATwoLocalRank 3 G = LargeEvenTwoLocalRank 3 G := rfl
  rw [hrank] at hC
  have hm : LargeEvenTwoLocalRank 3 G ≤ 5 := by
    have hlt : 3 ^ (LargeEvenTwoLocalRank 3 G - 2) < 3 ^ 4 := hH.pow_le_card_gamma_J.trans_lt h4
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    omega
  have hC2 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 2 := by
    have h35 : 3 ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 ^ 3 * 3 ^ 2 :=
      hC.trans ((Nat.pow_le_pow_right (by norm_num) hm).trans (by norm_num))
    exact Nat.le_of_mul_le_mul_left h35 (by norm_num)
  have hker : (ggGamma J hH.Bs_le_normalizer_J).ker =
      (Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff]
  have hkerCard : Nat.card ↥((Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcount := TableB.card_range_mul_card_ker (ggGamma J hH.Bs_le_normalizer_J)
  rw [hker, hkerCard] at hcount
  rw [← hcount]
  calc Nat.card (ggGamma J hH.Bs_le_normalizer_J).range *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G))
      ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range * 3 ^ 2 := Nat.mul_le_mul_left _ hC2
    _ < 3 ^ 4 * 3 ^ 2 := Nat.mul_lt_mul_of_pos_right h4 (by norm_num)
    _ = 3 ^ 6 := by norm_num

end Lift

theorem ggAutomizer_eq_bot_or_zpowers_of_card_le_four {G : Type} [Group G] {p : ℕ}
    {Bs J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ} {Λa : Type}
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (hS3 : S.card = 3) (hΛ : Fintype.card Λ ≤ 4)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hclosJ : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j))) :
    ggAutomizer J Bs = ⊥ ∨
      ∃ τ : MulAut ↥Bs, GGIsReflection p τ ∧ ggAutomizer J Bs = Subgroup.zpowers τ := by
  classical
  have hsub : Subsingleton {j : Λ // j ∉ S} := by
    rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_subtype_compl, Fintype.card_coe]
    omega
  rw [hclosJ]
  rcases isEmpty_or_nonempty {j : Λ // j ∉ S} with hE | hne
  · left
    rw [Set.range_eq_empty, Subgroup.closure_empty]
  · right
    obtain ⟨j₀⟩ := hne
    have hr : (Set.range fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) = {φ (Sum.inl j₀)} := by
      ext a
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        rw [Subsingleton.elim j j₀]
      · rintro rfl
        exact ⟨j₀, rfl⟩
    exact ⟨_, hrefl _, by rw [hr, ← Subgroup.zpowers_eq_closure]⟩

theorem ggAutomizer_sq_of_eq_bot_or_zpowers {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)}
    (h : A = ⊥ ∨ ∃ τ : MulAut ↥Bs, GGIsReflection p τ ∧ A = Subgroup.zpowers τ) :
    ∀ a ∈ A, a ^ 2 = 1 := by
  rcases h with h | ⟨τ, hτ, h⟩
  · intro a ha
    rw [h, Subgroup.mem_bot] at ha
    rw [ha, one_pow]
  · intro a ha
    rw [h] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hτ.1, one_zpow]

theorem GGResHyp.automizer_J_bot_or_refl_of_exact3_nonsingular_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 6) :
    ggAutomizer J Bs = ⊥ ∨ (Nat.card Bs = p ^ 5 ∧
      ∃ τ : MulAut ↥Bs, GGIsReflection p τ ∧ ggAutomizer J Bs = Subgroup.zpowers τ) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hS3, -, -, hWML,
    hCLL, -, -, -, hlin, hrefl, hpairL, -, -, ⟨fL, -⟩, -, hclosL, -, -, hclosJ⟩ := id hD
  let := i1
  let := i2
  let := i5
  let := i6
  have hle := ggIntCartan_card_le_rank_add_one hWML hCLL p hp2
  have hrk := Matrix.rank_le_card_width (CL.map (Int.castRingHom (ZMod p)))
  have hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
    by_contra hne
    exact hL (ggSingularWeylOrder_of_type fL
      (ggRC_singular_typeA_or_E6_of_rank hp hp2 hWML hCLL (by omega)))
  have haxis := ggResL_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hc : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
    rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V]
  have hV : Module.finrank (ZMod p) V < 6 := by
    rw [hc] at hBs
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hBs
  rcases isEmpty_or_nonempty {j : Λ // j ∉ S} with hE | ⟨⟨j, hj⟩⟩
  · exact Or.inl (by rw [hclosJ, Set.range_eq_empty, Subgroup.closure_empty])
  have h4 : S.card < Fintype.card Λ := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => hj (h ▸ Finset.mem_univ j))
  refine (ggAutomizer_eq_bot_or_zpowers_of_card_le_four φ hS3 (by omega) hrefl hclosJ).imp_right
    fun h => ⟨?_, h⟩
  rw [hc]
  congr 1
  omega

theorem GGResHyp.automizer_J_sq_of_exact3_nonsingular_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 6) :
    ∀ a ∈ ggAutomizer J Bs, a ^ 2 = 1 :=
  ggAutomizer_sq_of_eq_bot_or_zpowers
    ((hH.automizer_J_bot_or_refl_of_exact3_nonsingular_L hL hD hBs).imp_right And.right)

theorem GGResHyp.automizer_J_bot_or_refl_of_exact3_nonsingular_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 6) :
    ggAutomizer J Bs = ⊥ ∨ (Nat.card Bs = p ^ 5 ∧
      ∃ τ : MulAut ↥Bs, GGIsReflection p τ ∧ ggAutomizer J Bs = Subgroup.zpowers τ) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hS3, -, -, hWML,
    hCLL, -, -, -, hlin, hrefl, hpairL, -, -, ⟨fL, -⟩, -, hclosL, -, -, hclosJ⟩ := id hD
  let := i1
  let := i2
  let := i5
  let := i6
  have hle := ggIntCartan_card_le_rank_add_one hWML hCLL p hp2
  have hrk := Matrix.rank_le_card_width (CL.map (Int.castRingHom (ZMod p)))
  have hrank : Matrix.rank (CL.map (Int.castRingHom (ZMod p))) = Fintype.card Λ := by
    by_contra hne
    exact hK (ggSingularWeylOrder_of_type fL
      (ggRC_singular_typeA_or_E6_of_rank hp hp2 hWML hCLL (by omega)))
  have haxis := ggResK_rank_core_add_one hH (fun i w => hlin (Sum.inl i) w) hpairL hCLL.1 hclosL
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hc : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
    rw [card_eq_of_ggLin ι, ← FiniteField.pow_finrank_eq_natCard p V]
  have hV : Module.finrank (ZMod p) V < 6 := by
    rw [hc] at hBs
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hBs
  rcases isEmpty_or_nonempty {j : Λ // j ∉ S} with hE | ⟨⟨j, hj⟩⟩
  · exact Or.inl (by rw [hclosJ, Set.range_eq_empty, Subgroup.closure_empty])
  have h4 : S.card < Fintype.card Λ := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => hj (h ▸ Finset.mem_univ j))
  refine (ggAutomizer_eq_bot_or_zpowers_of_card_le_four φ hS3 (by omega) hrefl hclosJ).imp_right
    fun h => ⟨?_, h⟩
  rw [hc]
  congr 1
  omega

theorem GGResHyp.automizer_J_sq_of_exact3_nonsingular_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) (hBs : Nat.card Bs < p ^ 6) :
    ∀ a ∈ ggAutomizer J Bs, a ^ 2 = 1 :=
  ggAutomizer_sq_of_eq_bot_or_zpowers
    ((hH.automizer_J_bot_or_refl_of_exact3_nonsingular_K hK hD hBs).imp_right And.right)

section Exclusion

theorem ggResExact3_false_of_nonsingular_L_of_twA5PlusThree {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTwA5PlusThreeLabel p Bs J)
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False := by
  by_cases h4 : p ^ 4 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · exact ggResExact3_false_of_card_L hH
      (hH.fix_mem_centralizer_J_of_twA5PlusThree_of_card hJ h4) hL hD
  · rw [not_le] at h4
    exact (not_le.mpr h4) (hH.pow_four_le_card_gamma_J_of_twA5PlusThree_of_sq hJ
      (hH.automizer_J_sq_of_exact3_nonsingular_L hL hD
        (hH.card_lt_of_twA5PlusThree_of_card_lt hJ h4)))

theorem ggResExact3_false_of_nonsingular_K_of_twA5PlusThree {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJ : GGInnerDiagOnLabel GGTwA5PlusThreeLabel p Bs J)
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False := by
  by_cases h4 : p ^ 4 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range
  · exact ggResExact3_false_of_card_K hH
      (hH.fix_mem_centralizer_J_of_twA5PlusThree_of_card hJ h4) hK hD
  · rw [not_le] at h4
    exact (not_le.mpr h4) (hH.pow_four_le_card_gamma_J_of_twA5PlusThree_of_sq hJ
      (hH.automizer_J_sq_of_exact3_nonsingular_K hK hD
        (hH.card_lt_of_twA5PlusThree_of_card_lt hJ h4)))

end Exclusion

theorem ggResJ_rest_twA5_or_twE6 {G : Type} [Group G] {p : ℕ} {Bs J : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hc : GGInnerDiagOnLabel (fun p lab => S p lab ∧ ggResJFixRestLabel p lab) p Bs J) :
    GGInnerDiagOnLabel (fun p lab => GGTwA5PlusThreeLabel p lab ∨
      (S p lab ∧ GGTableBTwE6ThreeLabel p lab)) p Bs J := by
  refine hc.mono_label fun lab h => ?_
  obtain ⟨hS, hp3, hl, hq⟩ := h
  rcases hl with ⟨ht, hr⟩ | ht
  · exact Or.inl ⟨ht, hr, hp3, hq⟩
  · exact Or.inr ⟨hS, ht, hp3, hq⟩

section Rest

theorem ggResExact3_twE6_of_nonsingular_L_of_tcj (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) :
    GGInnerDiagOnLabel (fun p lab => S p lab ∧ GGTableBTwE6ThreeLabel p lab) p Bs J := by
  rcases hH.fix_mem_centralizer_J_or_rest_of_tcj hT hLift hTCJ hRig h3 hJ with h | hc
  · exact (ggResExact3_false_of_card_L hH h hL hD).elim
  rcases (ggResJ_rest_twA5_or_twE6 hc).elim_or with h | h
  · exact (ggResExact3_false_of_nonsingular_L_of_twA5PlusThree hH h hL hD).elim
  · exact h

theorem ggResExact3_twE6_of_nonsingular_K_of_tcj (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range)
    (hJ : GGInnerDiagOnLabel S p Bs J)
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGInnerDiagOnLabel (fun p lab => S p lab ∧ GGTableBTwE6ThreeLabel p lab) p Bs J := by
  rcases hH.fix_mem_centralizer_J_or_rest_of_tcj hT hLift hTCJ hRig h3 hJ with h | hc
  · exact (ggResExact3_false_of_card_K hH h hK hD).elim
  rcases (ggResJ_rest_twA5_or_twE6 hc).elim_or with h | h
  · exact (ggResExact3_false_of_nonsingular_K_of_twA5PlusThree hH h hK hD).elim
  · exact h

end Rest

end CFSG.StandardType

end
