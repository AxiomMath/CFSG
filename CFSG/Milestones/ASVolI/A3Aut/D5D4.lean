module

public import CFSG.Milestones.ASVolI.A3Aut.D5Base
public import CFSG.Milestones.ASVolI.A3Aut.SBD4
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.A3Aut.Fam
public import CFSG.Milestones.ASVolI.A3Aut.Util

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.KFacts

section D5D4Helpers

theorem burnsideAut_d5_dcq_act {M : Type} [Group M] (H C : Subgroup M) (hHC : ⁅H, H⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) (φ : MulAut ↥C) (act : M → M)
    (hact : ∀ x : ↥C, ((φ x : ↥C) : M) = act x) (g : ↥⁅H, H⁆) :
    ∃ g' : ↥⁅H, H⁆, (g' : M) = act g ∧
      MulAut.congr (burnsideA26_dcqEquiv H C hHC hZ).symm φ (QuotientGroup.mk g) =
        QuotientGroup.mk g' := by
  subst hHC
  refine ⟨φ g, hact g, ?_⟩
  apply (burnsideA26_dcqEquiv H ⁅H, H⁆ rfl hZ).injective
  rw [MulAut.congr_apply, MulEquiv.symm_symm]
  change (burnsideA26_dcqEquiv H ⁅H, H⁆ rfl hZ) ((burnsideA26_dcqEquiv H ⁅H, H⁆ rfl hZ).symm
    (φ ((burnsideA26_dcqEquiv H ⁅H, H⁆ rfl hZ) (QuotientGroup.mk g)))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end D5D4Helpers

section D5D4


theorem burnsideAut_d5d4_coprime {G : Type} [Group G] [Finite G]
    (hSQT3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2) (L : Subgroup G) [L.Normal]
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (Θ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ)
    (hΘker : Θ.ker = (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (e : ↥L ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (x : G) :
    Nat.Coprime (orderOf (Θ (MulAut.congr e (MulAut.conjNormal x)))) 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨σ', hσ', hσ'ord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  rw [hσσ'] at hσ'ord
  haveI : CharP K 2 := burnsideA26_charP_two (n := 3 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨-, hNF, -, hcyc, hcardAut, -, hZC, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  haveI : IsCyclic (K ≃+* K) := hcyc
  have hσ3 : σ ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one σ
    rwa [hσ'ord] at h1
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ'ord
    exact absurd hσ'ord (by decide)
  have hΘF : ∀ δ : K ≃+* K, Θ (fieldActorHom (t := TwistTag.D4) σ δ) = δ := fun δ =>
    hΘ _ 1 δ (by rw [map_one, one_mul]; rfl)
  have hNF' : ∀ m : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃ g, m = MulAut.conj g * fieldActorHom (t := TwistTag.D4) σ (Θ m) := by
    intro m
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF m
    refine ⟨g, ?_⟩
    rw [hΘ m g δ hgδ]
    exact hgδ
  haveI : CharP (fixSubfield σ) 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2
    (by exact_mod_cast two_eq_zero_fixSubfield σ hK2)
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨y₁, y₂, hy₁3, hy₂3, hy₁₂, hy₁1, hy₂⟩ := burnsideA26_g2_E9 (k := fixSubfield σ)
  set ι := trialityG2Incl σ hK2 with hιdef
  have hι : Function.Injective ι := trialityG2Incl_injective σ hK2
  have hιfix : ∀ p, fieldActorHom (t := TwistTag.D4) σ σ (ι p) = ι p := fun p =>
    (mem_range_trialityG2Incl_iff σ hK2 _).1 ⟨p, rfl⟩
  set ρ : G →* MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hρdef
  have hρ : ∀ (x : G) (l : ↥L), e (MulAut.conjNormal x l) = ρ x (e l) := by
    intro x l
    show e (MulAut.conjNormal x l) = MulAut.congr e (MulAut.conjNormal x) (e l)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hρL : ∀ l : ↥L, ρ (l : G) = MulAut.conj (e l) := by
    intro l
    have h1 : (MulAut.conjNormal (l : G) : MulAut ↥L) = MulAut.conj l := by
      ext m
      simp [MulAut.conjNormal_apply]
    show MulAut.congr e (MulAut.conjNormal (l : G)) = _
    rw [h1, congr_mulAutConj]
  have hinn : ∀ c : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∃ y : G,
      ρ y = MulAut.conj c := fun c =>
    ⟨(e.symm c : G), by rw [hρL, MulEquiv.apply_symm_apply]⟩
  have hK₀ : IsPGroup 2 e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact IsPGroup.of_bot
  change Nat.Coprime (orderOf (Θ (ρ x))) 3
  by_contra hnc
  have h3 : 3 ∣ orderOf (Θ (ρ x)) := by
    by_contra hnd
    exact hnc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd).symm
  obtain ⟨z, σ₁, hzp, hσ₁, hρz⟩ :=
    burnsideA26_exists_z (fieldActorHom (t := TwistTag.D4) σ) Θ hNF' ρ hinn hσ3 hσ1 h3
  have hσ₁3 : σ₁ ^ 3 = 1 := by
    rcases hσ₁ with rfl | rfl
    · exact hσ3
    · rw [inv_pow, hσ3, inv_one]
  have hσ₁1 : σ₁ ≠ 1 := by
    rcases hσ₁ with rfl | rfl
    · exact hσ1
    · exact fun h => hσ1 (inv_eq_one.mp h)
  have hz3 : ρ z ^ 3 = 1 := by rw [hρz, ← map_pow, hσ₁3, map_one]
  have hzin : ρ z ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    intro hmem
    have h2 : fieldActorHom (t := TwistTag.D4) σ σ₁ ∈ Θ.ker := by
      rw [hΘker, ← hρz]
      exact hmem
    rw [MonoidHom.mem_ker, hΘF] at h2
    exact hσ₁1 h2
  have hfix : ∀ p, ρ z (ι p) = ι p := by
    intro p
    rw [hρz]
    rcases hσ₁ with rfl | rfl
    · exact hιfix p
    · rw [map_inv, MulAut.inv_def, MulEquiv.symm_apply_eq]
      exact (hιfix p).symm
  have hrk := burnsideA26_rank_ge_three (L := L) e.toMonoidHom e.surjective hK₀ hZC ρ hρ hρL
    hzp hz3 hzin (a := ι y₁) (b := ι y₂)
    (by rw [← map_pow, hy₁3, map_one])
    (by rw [← map_pow, hy₂3, map_one])
    (by rw [← map_mul, ← map_mul, hy₁₂])
    (fun h => hy₁1 (hι (h.trans (map_one ι).symm)))
    (by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      apply hy₂
      refine ⟨k, hι ?_⟩
      rw [map_zpow]
      exact hk)
    (hfix y₁) (hfix y₂)
  omega

theorem burnsideAut_a315_3D4 {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) {n : ℕ} (hn : 2 ≤ n)
    (hL : CFSG.Quasithin.Is3D4 2 n ↥L) : ChA.A315Case5Concrete L T B := by
  haveI := h.sqtk.finite
  haveI hLn : L.Normal := burnsideA315x_normal h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLie : CFSG.Quasithin.A315.IsLieChar2 n ↥L :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))
  have hSQT3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 :=
    h.sqtk.sqt 3 Nat.prime_three (by norm_num)
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hL
  haveI : CharP K 2 := burnsideA26_charP_two (n := 3 * n) (by rw [hK, ← pow_mul, mul_comm])
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨hactEq, hNF, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcardAut, hHC, hZC, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hΘF : ∀ δ, Θ (fieldActorHom (t := TwistTag.D4) σ δ) = δ := fun δ =>
    hΘ (fieldActorHom (t := TwistTag.D4) σ δ) 1 δ (by rw [map_one, one_mul] <;> rfl)
  have hφinj : Function.Injective (fieldActorHom (t := TwistTag.D4) σ) :=
    fun δ₁ δ₂ h12 => by rw [← hΘF δ₁, h12, hΘF]
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ⊤ :=
    burnsideAut_isSylowTwoOf_graphFixedPosUnipotent σ
  have hφU : ∀ δ, ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map
        (fieldActorHom (t := TwistTag.D4) σ δ).toMonoidHom =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun δ =>
    map_graphFixedEntrywiseAut_subgroupOf (ringEquiv_comm_of_finite σ δ)
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)
      (map_units_map_entrywiseHom_graphFixedPosUnipotent (ringEquiv_comm_of_finite σ δ))
  obtain ⟨e, he⟩ := burnsideAut_exists_equiv_sylow e₀
    (burnsideAut_isSylowTwoOf_subgroupOf h.sylow) hUsyl
  have hLa : ∀ a, 4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) := by
    obtain ⟨σ', hσ', -, hcard, -, -⟩ :=
      finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
    have hσσ' : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
    intro a
    rw [hσσ', hcard a]
    have h1 : 1 ≤ (TwistTag.D4.orbit a).card :=
      Finset.card_pos.2 ⟨_, TwistTag.D4.orbitMin_mem a⟩
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ = (2 ^ n) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ n) ^ (TwistTag.D4.orbit a).card :=
        Nat.pow_le_pow_right (by positivity) h1
  refine burnsideAut_case5_of_model2 h n hn hLie hZC e he hUsyl
    (IM := (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (ΦM := (fieldActorHom (t := TwistTag.D4) σ).range) le_rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (burnsideAut_solvBorel_graphFixed σ hLa) ?_
  · exact burnsideAut_inn_relIndex_self _
  · exact burnsideAut_map_inn_le_innDiag e
  · rintro _ ⟨δ₁, rfl⟩ _ ⟨δ₂, rfl⟩
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K δ₁ δ₂]
  · haveI := burnsideAut_inn_normal' ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  · rw [eq_bot_iff]
    rintro _ ⟨hI, ⟨δ, rfl⟩⟩
    have h1 : Θ (fieldActorHom (t := TwistTag.D4) σ δ) = 1 := by
      rw [← MonoidHom.mem_ker, hΘker]
      exact hI
    rw [hΘF] at h1
    rw [h1, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨δ, rfl⟩
    exact burnsideAut_mem_normalizer_map_conj' (hφU δ)
  · intro b _
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF (MulAut.congr e (MulAut.conjNormal b))
    rw [hgδ]
    exact Subgroup.mul_mem_sup ⟨g, rfl⟩ ⟨δ, rfl⟩
  · intro ε hε F hF _ hFB
    obtain ⟨hcycF, hdvd, δ, hord, hpin⟩ := burnsideAut_pinned_of_field
      (fieldActorHom (t := TwistTag.D4) σ) hφinj hcyc (burnsideA26_dcqEquiv _ _ hHC hZC).symm
      hUsyl hφU
      (fun δ mg => ∀ g : ↥⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
          twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆,
        ∃ g' : ↥⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
            twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆,
          (g' : ModGL TwistTag.D4.tag K) =
            Units.map (entrywiseHom (δ : K →+* K)) (g : ModGL TwistTag.D4.tag K) ∧
          mg (QuotientGroup.mk g) = QuotientGroup.mk g')
      (fun δ g => burnsideAut_d5_dcq_act _ _ hHC hZC (fieldActorHom (t := TwistTag.D4) σ δ) _
        (fun x => hactEq δ x) g)
      ε hε F hF
    have hF3 : Nat.Coprime (Nat.card F) 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro h3
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) 3 h3
      have hx3 : orderOf (x : MulAut ↥L) = 3 := (Subgroup.orderOf_coe x).trans hx
      obtain ⟨b, -, hb⟩ := hFB x x.2
      obtain ⟨_, ⟨δ', rfl⟩, hxδ'⟩ := hF x.2
      obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hb
      have h1 : MulAut.congr ε (MulAut.conjNormal b) =
          MulAut.conj c⁻¹ * fieldActorHom (t := TwistTag.D4) σ δ' := by
        have h2 : MulAut.conjNormal b =
            (MulAut.congr ε.symm (MulAut.conj c))⁻¹ * (x : MulAut ↥L) := by
          change MulAut.congr ε.symm (MulAut.conj c) = _ at hc
          rw [hc]
          group
        rw [h2, map_mul, map_inv]
        change (MulAut.congr ε (MulAut.congr ε.symm (MulAut.conj c)))⁻¹ *
          MulAut.congr ε (x : MulAut ↥L) = _
        rw [← hxδ']
        change (MulAut.congr ε (MulAut.congr ε.symm (MulAut.conj c)))⁻¹ *
          MulAut.congr ε (MulAut.congr ε.symm (fieldActorHom (t := TwistTag.D4) σ δ')) = _
        rw [burnsideA26_congr_congr_symm, burnsideA26_congr_congr_symm, map_inv]
      have key : Θ (MulAut.congr ε (MulAut.conjNormal b)) = δ' := hΘ _ _ _ h1
      have hcop := burnsideAut_d5d4_coprime hSQT3 L hf hK σ hσ Θ hΘ hΘker ε b
      rw [key] at hcop
      have hordδ' : orderOf δ' = 3 := by
        rw [← orderOf_injective (fieldActorHom (t := TwistTag.D4) σ) hφinj δ',
          ← orderOf_injective (MulAut.congr ε.symm).toMonoidHom (MulEquiv.injective _)]
        have hxδ'' : MulAut.congr ε.symm (fieldActorHom (t := TwistTag.D4) σ δ') =
            (x : MulAut ↥L) := hxδ'
        change orderOf (MulAut.congr ε.symm (fieldActorHom (t := TwistTag.D4) σ δ')) = 3
        rw [hxδ'']
        exact hx3
      rw [hordδ'] at hcop
      exact absurd hcop (by decide)
    have hδ3 : Nat.Coprime (orderOf δ) 3 := hord ▸ hF3
    refine ⟨hcycF, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨K, inferInstance, inferInstance, σ.toRingHom,
        ε.trans (burnsideA26_dcqEquiv _ _ hHC hZC).symm, δ, hK, ?_⟩))))))⟩
    · rw [hcardAut] at hdvd
      exact hF3.dvd_mul_left.1 hdvd
    · exact burnsideAut_d5_pinned_mono hpin fun mg hmg => ⟨fun c => hσ c, hδ3, hmg⟩

end D5D4

end CFSG.ASVolI
