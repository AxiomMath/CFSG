module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Theorem28
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem Thm210.mem_cenIn_iff {X : Subgroup Γ} {S : Set Γ} {x : Γ} :
    x ∈ cenIn X S ↔ x ∈ X ∧ x ∈ Subgroup.centralizer S :=
  Subgroup.mem_inf

theorem Thm210.mem_norIn_iff {X : Subgroup Γ} {S : Set Γ} {x : Γ} :
    x ∈ norIn X S ↔ x ∈ X ∧ x ∈ Subgroup.normalizer S :=
  Subgroup.mem_inf

theorem signalizerNearPSolvable_of_le (hJG : J ≤ G) (h : signalizerNearPSolvable p ↥G) :
    signalizerNearPSolvable p ↥J := by
  obtain ⟨hcop, hsec⟩ := signalizerNearPSolvable_iff.1 h
  refine signalizerNearPSolvable_iff.2 ⟨?_, fun S _ _ hS hnc => ?_⟩
  · exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hJG)
  · exact hsec S (isSectionOf_of_le hJG hS) hnc

theorem exists_mul_ne_of_not_isMulCommutative {X : Type*} [Group X] (h : ¬ IsMulCommutative X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact h (isMulCommutative_iff.mpr hcon)

theorem not_isSolvable_of_mem_lcal {X : Subgroup Γ} (hJ : J ∈ lcal X) :
    ¬ Group.IsSolvable ↥J := by
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  intro hsol
  exact hnc (isMulCommutative_iff.mpr fun a b => IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)

theorem SemisimpleAction.isDirectProduct_lcal [Finite Γ] (h : SemisimpleAction p A G) :
    IsDirectProduct (lcal G) G :=
  h.semisimple.isDirectProduct_lcal

theorem SemisimpleAction.permutes_lcal (h : SemisimpleAction p A G) :
    ∀ a ∈ A, ∀ J ∈ lcal G, J.map (MulAut.conj a).toMonoidHom ∈ lcal G :=
  fun _ ha _ hJ => map_conj_mem_lcal hJ (h.admits ha)

theorem SemisimpleAction.projIn_cenIn [Finite Γ] (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    projIn (lcal G) J (cenIn G A) = cenIn J (norIn A J) :=
  projIn_centralizer_eq h.isDirectProduct_lcal h.permutes_lcal hJ

theorem SemisimpleAction.isSolvable_cenIn_norIn [Finite Γ] (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : Group.IsSolvable ↥(cenIn J (norIn A J)) := by
  rw [← h.projIn_cenIn hJ]
  exact isSolvable_projIn h.isDirectProduct_lcal hJ inf_le_left h.solvable_cen

theorem SemisimpleAction.nearSimple (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    NearSimple p ↥J := by
  obtain ⟨hJG, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  exact ⟨h.prime, hs, exists_mul_ne_of_not_isMulCommutative hnc,
    signalizerNearPSolvable_of_le hJG h.nearPSolvable⟩

theorem SemisimpleAction.exists_frame
    [Finite Γ] (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ (a : Γ) (f : MulAut ↥J), a ∈ norIn A J ∧ (∀ x : ↥J, ((f x : ↥J) : Γ) = a * x * a⁻¹) ∧
      orderOf f = p ∧ (∀ b ∈ norIn A J, ∃ k : ℕ, ∀ x : ↥J, b * x * b⁻¹ = ((f ^ k) x : Γ)) ∧
      (signalizerFixedSubgroup f).map J.subtype = cenIn J (norIn A J) := by
  have hNS : NearSimple p ↥J := h.nearSimple hJ
  have hsol := h.isSolvable_cenIn_norIn hJ
  have hnsol := not_isSolvable_of_mem_lcal hJ
  have hNle : norIn A J ≤ Subgroup.normalizer (J : Set Γ) := inf_le_right
  let ψ : ↥(norIn A J) →* MulAut ↥J := J.normalizerMonoidHom.comp (Subgroup.inclusion hNle)
  have hψ : ∀ (b : ↥(norIn A J)) (x : ↥J), ((ψ b x : ↥J) : Γ) = b * x * b⁻¹ := fun b x => by
    simp [ψ]
  have hψp : ∀ b : ↥(norIn A J), ψ b ^ p = 1 := by
    intro b
    rw [← map_pow]
    have hbA : (b : Γ) ∈ A := (Thm210.mem_norIn_iff.mp b.2).1
    have hb : b ^ p = 1 := Subtype.ext (by simpa using h.elemAbelian.2 b hbA)
    rw [hb, map_one]
  have hP : IsPGroup p ψ.range := by
    rintro ⟨_, b, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hψp b)⟩
  have hcard : Nat.card ψ.range ∣ p := near_aut_pSubgroup_card_dvd hNS _ hP
  have hex : ∃ b : ↥(norIn A J), ψ b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnsol
    have hJc : cenIn J (norIn A J) = J := by
      refine le_antisymm inf_le_left fun x hx => Thm210.mem_cenIn_iff.mpr ⟨hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' := congrArg (fun g : MulAut ↥J => ((g ⟨x, hx⟩ : ↥J) : Γ)) (hcon ⟨b, hb⟩)
      simp only [hψ, MulAut.one_apply] at hb'
      have hb'' : b * x * b⁻¹ = x := hb'
      rw [mul_inv_eq_iff_eq_mul] at hb''
      exact hb''
    rw [hJc] at hsol
    exact hsol
  obtain ⟨b₀, hb₀⟩ := hex
  have := Fact.mk h.prime
  have hord : orderOf (ψ b₀) = p := orderOf_eq_prime (hψp b₀) hb₀
  have hP1 : Nat.card ψ.range = p := by
    rcases (Nat.dvd_prime h.prime).mp hcard with h1 | h1
    · exfalso
      apply hb₀
      have hbot : ψ.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hfr : ψ b₀ ∈ ψ.range := ⟨b₀, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hfr
    · exact h1
  have hzp : Subgroup.zpowers (ψ b₀) = ψ.range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact ⟨b₀, rfl⟩
    · rw [hP1, Nat.card_zpowers, hord]
  have hpow : ∀ b : ↥(norIn A J), ∃ k : ℕ, ψ b = ψ b₀ ^ k := by
    intro b
    have hb : ψ b ∈ Subgroup.zpowers (ψ b₀) := hzp ▸ ⟨b, rfl⟩
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hb)
    exact ⟨k, hk.symm⟩
  refine ⟨b₀, ψ b₀, b₀.2, hψ b₀, hord, fun b hb => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hpow ⟨b, hb⟩
    exact ⟨k, fun x => by rw [← hk, hψ]; rfl⟩
  · ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      refine Thm210.mem_cenIn_iff.mpr ⟨x'.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      obtain ⟨k, hk⟩ := hpow ⟨b, hb⟩
      have hfix : ∀ n : ℕ, (ψ b₀ ^ n) x' = x' := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hx', ih]
      have h1 := hψ ⟨b, hb⟩ x'
      rw [hk, hfix k] at h1
      change ((x' : ↥J) : Γ) = b * x' * b⁻¹ at h1
      rw [eq_mul_inv_iff_mul_eq] at h1
      exact h1.symm
    · intro hx
      obtain ⟨hxJ, hxc⟩ := Thm210.mem_cenIn_iff.mp hx
      refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
      change ψ b₀ ⟨x, hxJ⟩ = ⟨x, hxJ⟩
      apply Subtype.ext
      rw [hψ]
      have := Subgroup.mem_centralizer_iff.mp hxc b₀ b₀.2
      show (b₀ : Γ) * x * (b₀ : Γ)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact this

section Models

variable {X : Type*} [Group X] [Finite X]

theorem Thm210.normalizer_fitting_fixedNormalizer
    (h : NearSimple p X) {f : MulAut X}
    (hf : orderOf f = p) :
    Subgroup.normalizer (CFSG.fittingSubgroupOf (fixedNormalizer f) : Set X) =
      fixedNormalizer f := by
  obtain ⟨hCM, hMtop, -, hmax⟩ := near_unique_maximal h hf
  obtain ⟨-, -, ⟨hFne, -⟩, -, -⟩ := near_frobenius h hf
  refine le_antisymm ?_ (le_normalizer_fittingSubgroupOf _)
  have hFM : CFSG.fittingSubgroupOf (fixedNormalizer f) ≤ fixedNormalizer f :=
    Subgroup.map_subtype_le _
  by_cases hN : Subgroup.normalizer (CFSG.fittingSubgroupOf (fixedNormalizer f) : Set X) = ⊤
  · exfalso
    have hnorm : (CFSG.fittingSubgroupOf (fixedNormalizer f)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hN
    have := h.simple
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (CFSG.fittingSubgroupOf (fixedNormalizer f)) with h1 | h1
    · exact hFne h1
    · rw [h1] at hFM
      exact hMtop (top_le_iff.mp hFM)
  · exact hmax _ (hCM.trans (le_normalizer_fittingSubgroupOf _)) hN

end Models

theorem Thm210.map_subtype_centralizer (S' : Subgroup ↥J) :
    (Subgroup.centralizer (S' : Set ↥J)).map J.subtype = cenIn J (S'.map J.subtype : Set Γ) := by
  ext x
  rw [Thm210.mem_cenIn_iff]
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x'.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y', hy', rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx' y' hy')
  · rintro ⟨hxJ, hxc⟩
    refine ⟨⟨x, hxJ⟩, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y' ⟨y', hy', rfl⟩)

theorem Thm210.map_subtype_normalizer (S' : Subgroup ↥J) :
    (Subgroup.normalizer (S' : Set ↥J)).map J.subtype = norIn J (S'.map J.subtype : Set Γ) := by
  have h1 : (S'.map J.subtype).subgroupOf J = S' :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective S'
  have h2 := Subgroup.subgroupOf_normalizer_eq (H := S'.map J.subtype) (N := J)
    (Subgroup.map_subtype_le S')
  rw [h1] at h2
  rw [← h2, Subgroup.subgroupOf_map_subtype]
  exact inf_comm _ _

theorem SemisimpleAction.exists_frame_data
    [Finite Γ] (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    ∃ f : MulAut ↥J, orderOf f = p ∧
      (signalizerFixedSubgroup f).map J.subtype = cenIn J (norIn A J) ∧
      (fixedFitting f).map J.subtype = CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ∧
      (fixedNormalizer f).map J.subtype = kJ A J ∧
      (CFSG.fittingSubgroupOf (fixedNormalizer f)).map J.subtype =
        CFSG.fittingSubgroupOf (kJ A J) := by
  obtain ⟨-, f, -, -, hf, -, hC⟩ := h.exists_frame hJ
  have hNS : NearSimple p ↥J := h.nearSimple hJ
  have hC₀ : (fixedFitting f).map J.subtype =
      CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
    rw [← hC]
    exact (fittingSubgroupOf_map_of_injective J.subtype J.subtype_injective _).symm
  have hM : (fixedNormalizer f).map J.subtype = kJ A J := by
    unfold kJ
    rw [← hC₀, ← Thm210.map_subtype_centralizer, ← (near_fitting_eq_centralizer hNS hf).1,
      ← Thm210.map_subtype_normalizer, Thm210.normalizer_fitting_fixedNormalizer hNS hf]
  refine ⟨f, hf, hC, hC₀, hM, ?_⟩
  rw [← hM]
  exact (fittingSubgroupOf_map_of_injective J.subtype J.subtype_injective _).symm

theorem Thm210.kJ_le (A J : Subgroup Γ) : kJ A J ≤ J :=
  inf_le_left

section KJ

variable [Finite Γ]

theorem SemisimpleAction.cenIn_norIn_le_kJ
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    cenIn J (norIn A J) ≤ kJ A J := by
  obtain ⟨f, hf, hC, -, hM, -⟩ := h.exists_frame_data hJ
  rw [← hC, ← hM]
  exact Subgroup.map_mono (near_unique_maximal (h.nearSimple hJ) hf).1

theorem SemisimpleAction.isSolvable_kJ
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    Group.IsSolvable ↥(kJ A J) := by
  obtain ⟨f, hf, -, -, hM, -⟩ := h.exists_frame_data hJ
  have := (near_unique_maximal (h.nearSimple hJ) hf).2.2.1
  rw [← hM]
  exact Group.isSolvable_of_surjective (J.subtype.subgroupMap_surjective _)

theorem SemisimpleAction.kJ_ne
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) : kJ A J ≠ J :=
  fun he => not_isSolvable_of_mem_lcal hJ (he ▸ h.isSolvable_kJ hJ)

theorem SemisimpleAction.le_kJ_of_le_of_ne
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {H : Subgroup Γ} (hHJ : H ≤ J) (hCH : cenIn J (norIn A J) ≤ H) (hne : H ≠ J) :
    H ≤ kJ A J := by
  obtain ⟨f, hf, hC, -, hM, -⟩ := h.exists_frame_data hJ
  have hmax := (near_unique_maximal (h.nearSimple hJ) hf).2.2.2
  have hH' : signalizerFixedSubgroup f ≤ H.subgroupOf J := by
    intro x hx
    have : (x : Γ) ∈ cenIn J (norIn A J) := hC ▸ ⟨x, hx, rfl⟩
    exact hCH this
  have hne' : H.subgroupOf J ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hHJ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥J) ∈ H.subgroupOf J := htop ▸ Subgroup.mem_top _
    exact this
  calc H = (H.subgroupOf J).map J.subtype := (Subgroup.map_subgroupOf_eq_of_le hHJ).symm
    _ ≤ (fixedNormalizer f).map J.subtype := Subgroup.map_mono (hmax _ hH' hne')
    _ = kJ A J := hM

theorem SemisimpleAction.isMulCommutative_fittingSubgroupOf_kJ
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : IsMulCommutative ↥(CFSG.fittingSubgroupOf (kJ A J)) := by
  obtain ⟨f, hf, -, -, -, hFM⟩ := h.exists_frame_data hJ
  have := (near_frobenius (h.nearSimple hJ) hf).2.2.2.2
  rw [← hFM]
  exact (isMulCommutative_congr
    (Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective)).mp this

theorem SemisimpleAction.fittingSubgroupOf_kJ_eq
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (kJ A J) =
      cenIn J (CFSG.fittingSubgroupOf (cenIn J (norIn A J))) := by
  obtain ⟨f, hf, -, hC₀, -, hFM⟩ := h.exists_frame_data hJ
  rw [← hFM, ← hC₀, (near_fitting_eq_centralizer (h.nearSimple hJ) hf).1,
    Thm210.map_subtype_centralizer]

theorem SemisimpleAction.fittingSubgroupOf_cenIn_ne_bot
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≠ ⊥ := by
  obtain ⟨f, hf, -, hC₀, -, -⟩ := h.exists_frame_data hJ
  obtain ⟨-, ⟨hne, -⟩, -, -, -⟩ := near_frobenius (h.nearSimple hJ) hf
  rw [← hC₀]
  exact fun h0 => hne ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp h0)

theorem SemisimpleAction.fittingSubgroupOf_kJ_ne_bot
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : CFSG.fittingSubgroupOf (kJ A J) ≠ ⊥ := by
  obtain ⟨f, hf, -, -, -, hFM⟩ := h.exists_frame_data hJ
  obtain ⟨-, -, ⟨hne, -⟩, -, -⟩ := near_frobenius (h.nearSimple hJ) hf
  rw [← hFM]
  exact fun h0 => hne ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp h0)

theorem SemisimpleAction.fittingSubgroupOf_cenIn_le_kJ
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≤ CFSG.fittingSubgroupOf (kJ A J) := by
  obtain ⟨f, hf, -, hC₀, -, hFM⟩ := h.exists_frame_data hJ
  obtain ⟨-, -, -, hcomm, -⟩ := near_frobenius (h.nearSimple hJ) hf
  have h1 : fixedFitting f ≤ CFSG.fittingSubgroupOf (fixedNormalizer f) := by
    rw [(near_fitting_eq_centralizer (h.nearSimple hJ) hf).1]
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
  rw [← hC₀, ← hFM]
  exact Subgroup.map_mono h1

theorem SemisimpleAction.le_fittingSubgroupOf_kJ_of_nilpotent
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {Y : Subgroup Γ} (hYJ : Y ≤ J) (hY : Group.IsNilpotent Y)
    (hC : cenIn J (norIn A J) ≤ Subgroup.normalizer (Y : Set Γ)) :
    Y ≤ CFSG.fittingSubgroupOf (kJ A J) := by
  obtain ⟨f, hf, hC', -, -, hFM⟩ := h.exists_frame_data hJ
  have hY' : Group.IsNilpotent (Y.subgroupOf J) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYJ).symm
  have hC'' : signalizerFixedSubgroup f ≤
      Subgroup.normalizer ((Y.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
    intro c hc
    have hcC : (c : Γ) ∈ cenIn J (norIn A J) := hC' ▸ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.mp (hC hcC) (y : Γ)
  have := near_nilpotent_le_fitting (h.nearSimple hJ) hf _ hY' hC''
  calc Y = (Y.subgroupOf J).map J.subtype := (Subgroup.map_subgroupOf_eq_of_le hYJ).symm
    _ ≤ (CFSG.fittingSubgroupOf (fixedNormalizer f)).map J.subtype := Subgroup.map_mono this
    _ = CFSG.fittingSubgroupOf (kJ A J) := hFM

theorem SemisimpleAction.norIn_fittingSubgroupOf_kJ
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : norIn J (CFSG.fittingSubgroupOf (kJ A J)) = kJ A J := by
  obtain ⟨f, hf, -, -, hM, hFM⟩ := h.exists_frame_data hJ
  rw [← hFM, ← Thm210.map_subtype_normalizer,
    Thm210.normalizer_fitting_fixedNormalizer (h.nearSimple hJ) hf, hM]

theorem SemisimpleAction.fittingSubgroupOf_cenIn_le_of_normal
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {N : Subgroup Γ} (hNC : N ≤ cenIn J (norIn A J))
    (hN : (N.subgroupOf (cenIn J (norIn A J))).Normal) (hN1 : N ≠ ⊥) :
    CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≤ N := by
  obtain ⟨f, hf, hC, hC₀, -, -⟩ := h.exists_frame_data hJ
  have hmin := (near_minimal_normal (h.nearSimple hJ) hf).2.2
  have hNJ : N ≤ J := hNC.trans inf_le_left
  have hN'C : N.subgroupOf J ≤ signalizerFixedSubgroup f := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ : (x : Γ) ∈ (signalizerFixedSubgroup f).map J.subtype :=
      hC ▸ hNC hx
    exact (Subtype.ext hyx : y = x) ▸ hy
  have hN'norm : ((N.subgroupOf J).subgroupOf (signalizerFixedSubgroup f)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN'C]
    intro n c hn hc
    have hcC : (c : Γ) ∈ cenIn J (norIn A J) := hC ▸ ⟨c, hc, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hNC).mp hN (n : Γ) (c : Γ) hn hcC
  have hN'1 : N.subgroupOf J ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [← Subgroup.map_subgroupOf_eq_of_le hNJ, hbot, Subgroup.map_bot]
  calc CFSG.fittingSubgroupOf (cenIn J (norIn A J))
      = (fixedFitting f).map J.subtype := hC₀.symm
    _ ≤ (N.subgroupOf J).map J.subtype := Subgroup.map_mono (hmin _ hN'C hN'norm hN'1)
    _ = N := Subgroup.map_subgroupOf_eq_of_le hNJ

end KJ

end CFSG.SignalizerFunctorTheorem.McBride.Near
