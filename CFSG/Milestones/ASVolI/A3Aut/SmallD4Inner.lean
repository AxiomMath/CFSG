module

public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.Milestones.ASVolI.A2OddAut

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.KFacts

theorem burnsideAut_d42_conj_inner
    {G : Type} [Group G] [Finite G] (hSQT3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2)
    (L : Subgroup G) [L.Normal] (hL : CFSG.Quasithin.Is3D4 2 1 ↥L) (x : G) :
    ∃ l : ↥L, MulAut.conjNormal x = MulAut.conj l := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hL
  obtain ⟨σ', hσ', hσ'ord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hK
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  rw [hσσ'] at hσ'ord
  haveI : CharP K 2 := burnsideA26_charP_two (n := 3 * 1) (by rw [hK, ← pow_mul, mul_comm])
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcardAut, -, hZC, -⟩ :=
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
  have hcop : Nat.Coprime (orderOf (Θ (ρ x))) 3 := by
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
  have hΘ1 : Θ (ρ x) = 1 := by
    have h1 : orderOf (Θ (ρ x)) ∣ 3 := by
      have h2 := orderOf_dvd_natCard (Θ (ρ x))
      rwa [hcardAut] at h2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) h1)
  have hmem : ρ x ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rw [← hΘker]
    exact hΘ1
  obtain ⟨c, hc⟩ := hmem
  refine ⟨e.symm c, ?_⟩
  have h1 : MulAut.congr e (MulAut.conjNormal x) = MulAut.conj c := hc.symm
  have h2 := congrArg (MulAut.congr e.symm) h1
  rw [congr_mulAutConj] at h2
  rw [← h2]
  exact (burnsideA26_congr_symm_congr e _).symm

theorem burnsideAut_d42_mem
    {G : Type} [Group G] {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    (hL : CFSG.Quasithin.Is3D4 2 1 ↥L) (g : G) : g ∈ L := by
  haveI : Finite G := h.sqtk.finite
  haveI := burnsideA315x_normal h
  have hSQT3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 :=
    h.sqtk.sqt 3 Nat.prime_three (by norm_num)
  obtain ⟨l, hl⟩ := burnsideAut_d42_conj_inner hSQT3 L hL g
  have hc : (l : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨y, hy⟩ : ↥L) : G)) hl
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    calc y * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * g := by group
      _ = (l : G)⁻¹ * (g * y * g⁻¹) * g := by rw [← h1]
      _ = (l : G)⁻¹ * g * y := by group
  rw [burnsideA315x_centralizer_eq_bot h, Subgroup.mem_bot] at hc
  have : g = (l : G) := by
    have := congrArg (fun y => (l : G) * y) hc
    simpa using this
  rw [this]
  exact l.2

end CFSG.ASVolI
