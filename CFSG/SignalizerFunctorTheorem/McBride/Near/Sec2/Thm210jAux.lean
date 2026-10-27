module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupOrbit
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem Thm210.eq_one_of_central_frobenius {X : Type*} [Group X] {H K : Subgroup X}
    (hF : IsFrobeniusWithKernel H K) (hK : IsMulCommutative K) {z : X} (hz : z ∈ H)
    (hc : ∀ y ∈ H, y * z = z * y) : z = 1 := by
  obtain ⟨hKne, hKH, hKn, V, hVne, hVH, hdisj, hsup, hfrob⟩ := hF
  have := hKn
  have hsupH : V.subgroupOf H ⊔ K.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hVH hKH, sup_comm, hsup, Subgroup.subgroupOf_self]
  have hzmem : (⟨z, hz⟩ : ↥H) ∈ (↑(V.subgroupOf H ⊔ K.subgroupOf H) : Set ↥H) := by
    rw [hsupH]
    exact Subgroup.mem_top _
  rw [Subgroup.mul_normal] at hzmem
  obtain ⟨v', hv', k', hk', hvk⟩ := hzmem
  have hv : (v' : X) ∈ V := hv'
  have hk : (k' : X) ∈ K := hk'
  have hzvk : z = (v' : X) * (k' : X) := (congrArg Subtype.val hvk).symm
  have hvH : (v' : X) ∈ H := v'.2
  have hvK : ∀ k ∈ K, (v' : X) * k = k * (v' : X) := by
    intro k hk0
    have h1 := hc k (hKH hk0)
    have h2 : (k' : X) * k = k * (k' : X) := by
      have := hK.is_comm.comm (⟨k', hk'⟩ : K) ⟨k, hk0⟩
      exact congrArg Subtype.val this
    rw [hzvk] at h1
    have h3 : (v' : X) * k * (k' : X) = k * (v' : X) * (k' : X) := by
      calc (v' : X) * k * (k' : X) = (v' : X) * (k * (k' : X)) := by group
        _ = (v' : X) * ((k' : X) * k) := by rw [h2]
        _ = (v' : X) * (k' : X) * k := by group
        _ = k * ((v' : X) * (k' : X)) := h1.symm
        _ = k * (v' : X) * (k' : X) := by group
    exact mul_right_cancel h3
  have hv1 : (v' : X) = 1 := by
    by_contra hne
    apply hKne
    rw [eq_bot_iff]
    intro k hk0
    exact Subgroup.mem_bot.mpr (hfrob _ hv hne k hk0 (hvK k hk0))
  have hz1 : z = (k' : X) := by rw [hzvk, hv1, one_mul]
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hwz := hc w (hVH hw)
  rw [hz1] at hwz ⊢
  refine hfrob w hw (fun h1 => hw1 (Subtype.ext h1)) _ hk hwz

section Finite

variable [Finite Γ]

theorem SemisimpleAction.eq_one_of_central_smear
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {y : Γ} (hy : y ∈ smear J A) (hc : ∀ x ∈ smear J A, x * y = y * x) : y = 1 := by
  have hG := h.isDirectProduct_lcal
  have hyG : y ∈ G := (Subgroup.mem_inf.mp (h.smear_le_cenIn hJ hy)).1
  set c : ↥J := hG.coord hJ ⟨y, hyG⟩ with hcdef
  have hproj : ∀ z : Γ, z ∈ cenIn J (norIn A J) ↔
      ∃ x : ↥G, (x : Γ) ∈ smear J A ∧ ((hG.coord hJ x : ↥J) : Γ) = z := by
    intro z
    rw [← h.projIn_smear hJ, hG.mem_projIn_iff hJ]
  obtain ⟨f, hf, hfix, -, -, -⟩ := h.exists_frame_data hJ
  have hcC : (c : Γ) ∈ cenIn J (norIn A J) := (hproj _).mpr ⟨⟨y, hyG⟩, hy, rfl⟩
  obtain ⟨c', hc'C, hc'⟩ : (c : Γ) ∈ (signalizerFixedSubgroup f).map J.subtype := hfix ▸ hcC
  have hc'c : c' = c := Subtype.ext hc'
  rw [hc'c] at hc'C
  obtain ⟨-, hF, -, hK, -⟩ := near_frobenius (h.nearSimple hJ) hf
  have hc1 : c = 1 := by
    refine Thm210.eq_one_of_central_frobenius hF hK hc'C fun d hd => ?_
    have hdC : (d : Γ) ∈ cenIn J (norIn A J) := hfix ▸ ⟨d, hd, rfl⟩
    obtain ⟨x, hxS, hxd⟩ := (hproj _).mp hdC
    have hxy : x * ⟨y, hyG⟩ = ⟨y, hyG⟩ * x := Subtype.ext (hc _ hxS)
    have := congrArg (hG.coord hJ) hxy
    rw [map_mul, map_mul, Subtype.ext hxd] at this
    exact this
  have hy1 : y ∈ sSup (lcal G \ {J}) := by
    refine (hG.coord_eq_one_iff hJ ⟨y, hyG⟩).mp ?_
    rw [← hcdef, hc1]
  have : y ∈ smear J A ⊓ sSup (lcal G \ {J}) := Subgroup.mem_inf.mpr ⟨hy, hy1⟩
  rw [h.smear_inf_sSup hJ] at this
  exact Subgroup.mem_bot.mp this

theorem SemisimpleAction.cenIn_cenIn_smear
    (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    cenIn (cenIn G A) (smear J A) =
      sSup ({X | ∃ K ∈ lcal G, X = smear K A} \ {smear J A}) := by
  have hT := h.isDirectProduct_smear
  have hS : smear J A ∈ {X | ∃ K ∈ lcal G, X = smear K A} := ⟨J, hJ, rfl⟩
  refine le_antisymm (fun x hx => ?_) (sSup_le ?_)
  · obtain ⟨hxD, hxc⟩ := Subgroup.mem_inf.mp hx
    have h1 : hT.coord hS ⟨x, hxD⟩ = 1 := by
      refine Subtype.ext (h.eq_one_of_central_smear hJ (hT.coord hS ⟨x, hxD⟩).2 fun z hz => ?_)
      have hzD : z ∈ cenIn G A := h.smear_le_cenIn hJ hz
      have hxz : (⟨z, hzD⟩ : ↥(cenIn G A)) * ⟨x, hxD⟩ = ⟨x, hxD⟩ * ⟨z, hzD⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc z hz)
      have := congrArg (hT.coord hS) hxz
      rw [map_mul, map_mul] at this
      have hcz : hT.coord hS ⟨z, hzD⟩ = ⟨z, hz⟩ := Subtype.ext (hT.coord_of_mem hS hz)
      rw [hcz] at this
      exact congrArg Subtype.val this
    exact (hT.coord_eq_one_iff hS ⟨x, hxD⟩).mp h1
  · rintro K ⟨hKT, hKne⟩ k hk
    refine Subgroup.mem_inf.mpr ⟨hT.le hKT hk, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (hT.commute K hKT _ hS hKne k hk z hz).symm.eq

theorem SemisimpleAction.isDirectProduct_cenIn_cenIn_smear
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    IsDirectProduct {S | ∃ K ∈ lcal G, S = smear K A ∧ S ≠ smear J A}
      (cenIn (cenIn G A) (smear J A)) := by
  have hset : {S | ∃ K ∈ lcal G, S = smear K A ∧ S ≠ smear J A} =
      {X | ∃ K ∈ lcal G, X = smear K A} \ {smear J A} := by
    ext S
    constructor
    · rintro ⟨K, hK, rfl, hne⟩
      exact ⟨⟨K, hK, rfl⟩, hne⟩
    · rintro ⟨⟨K, hK, rfl⟩, hne⟩
      exact ⟨K, hK, rfl, hne⟩
  rw [hset, h.cenIn_cenIn_smear hJ]
  exact isDirectProduct_of_subset h.isDirectProduct_smear Set.sdiff_subset

theorem SemisimpleAction.inf_smear_eq_bot
    (h : SemisimpleAction p A G) {X : Subgroup Γ}
    (hX : Admits (cenIn G A ⊔ A) X) (hJ : J ∈ lcal G)
    (hFX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X) : X ⊓ smear J A = ⊥ := by
  have hDX : ∀ d ∈ cenIn G A, ∀ x ∈ X, d * x * d⁻¹ ∈ X := fun d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hX (Subgroup.mem_sup_left hd)) x).mp hx
  have hSD := h.smear_le_cenIn hJ
  have hNS : X ⊓ smear J A ≤ smear J A := inf_le_right
  have hNnorm : ((X ⊓ smear J A).subgroupOf (smear J A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNS]
    intro n y hn hy
    obtain ⟨hnX, hnS⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨hDX y (hSD hy) n hnX, mul_mem (mul_mem hy hnS) (inv_mem hy)⟩
  by_contra hne
  exact hFX ((h.fittingSubgroupOf_smear_le_of_normal hJ hNS hNnorm hne).trans inf_le_left)

theorem SemisimpleAction.inf_cenIn_le_cenIn_smear
    (h : SemisimpleAction p A G) {X : Subgroup Γ}
    (hX : Admits (cenIn G A ⊔ A) X) (hJ : J ∈ lcal G)
    (hFX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X) :
    X ⊓ cenIn G A ≤ cenIn (cenIn G A) (smear J A) := by
  have hDX : ∀ d ∈ cenIn G A, ∀ x ∈ X, d * x * d⁻¹ ∈ X := fun d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp (hX (Subgroup.mem_sup_left hd)) x).mp hx
  have hSD := h.smear_le_cenIn hJ
  have hNbot := h.inf_smear_eq_bot hX hJ hFX
  intro x hx
  obtain ⟨hxX, hxD⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨hxD, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ smear J A := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (h.conj_mem_smear hJ hxD hy) (inv_mem hy)⟩
    have := mul_mem hxX (hDX y (hSD hy) x⁻¹ (inv_mem hxX))
    simpa [mul_assoc] using this
  rw [hNbot, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near
