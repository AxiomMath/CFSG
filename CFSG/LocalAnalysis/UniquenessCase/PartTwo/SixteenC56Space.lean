module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

@[expose] def IsSub (U : Subgroup W) : Prop :=
  ∀ (c : S.K) (u : W), u ∈ U → S.smul c u ∈ U

theorem pol_one_left (w : W) : S.pol 1 w = 0 := by
  simp [pol, Q_one]

@[expose] def perp (U : Subgroup W) : Subgroup W where
  carrier := {x | ∀ u ∈ U, S.pol x u = 0}
  one_mem' := fun u _ => S.pol_one_left u
  mul_mem' := fun {a b} ha hb u hu => by
    rw [S.pol_mul_left, ha u hu, hb u hu, add_zero]
  inv_mem' := fun {a} ha u hu => by
    have h := S.pol_mul_left a a⁻¹ u
    rw [mul_inv_cancel, S.pol_one_left, ha u hu, zero_add] at h
    exact h.symm

theorem mem_perp {U : Subgroup W} {x : W} : x ∈ S.perp U ↔ ∀ u ∈ U, S.pol x u = 0 := Iff.rfl

theorem isSub_perp (U : Subgroup W) : S.IsSub (S.perp U) := fun c x hx => by
  rw [mem_perp] at hx ⊢
  intro u hu
  rw [S.pol_smul_left, hx u hu, mul_zero]

theorem isSub_inf {U V : Subgroup W} (hU : S.IsSub U) (hV : S.IsSub V) : S.IsSub (U ⊓ V) :=
  fun c u hu => ⟨hU c u hu.1, hV c u hu.2⟩

private def toSub {U : Subgroup W} (hU : S.IsSub U) : Submodule S.K (OmI → S.K) where
  carrier := S.vec '' (U : Set W)
  zero_mem' := ⟨1, U.one_mem, S.vec_one⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, U.mul_mem ha hb, S.vec_mul a b⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨S.smul c a, hU c a ha, S.vec_smul c a⟩

private theorem mem_toSub {U : Subgroup W} (hU : S.IsSub U) {v : OmI → S.K} :
    v ∈ S.toSub hU ↔ ∃ u ∈ U, S.vec u = v := Iff.rfl

private def subEquiv {U : Subgroup W} (hU : S.IsSub U) : U ≃ S.toSub hU where
  toFun u := ⟨S.vec u, ⟨u, u.2, rfl⟩⟩
  invFun v := ⟨S.ofVec v.1, by
    obtain ⟨u, hu, hvu⟩ := (S.mem_toSub hU).mp v.2
    rw [← hvu, S.ofVec_vec]
    exact hu⟩
  left_inv u := Subtype.ext (S.ofVec_vec u)
  right_inv v := Subtype.ext (S.vec_ofVec v.1)

theorem exists_card_eq_pow {U : Subgroup W} (hU : S.IsSub U) :
    ∃ d : ℕ, Nat.card U = Nat.card S.K ^ d := by
  refine ⟨Module.finrank S.K (S.toSub hU), ?_⟩
  rw [Nat.card_congr (S.subEquiv hU),
    Module.natCard_eq_pow_finrank (K := S.K) (V := S.toSub hU)]

private def Bf : LinearMap.BilinForm S.K (OmI → S.K) :=
  LinearMap.mk₂ S.K
    (fun v v' => v (Sum.inl 0) * v' (Sum.inr 0) + v' (Sum.inl 0) * v (Sum.inr 0) +
      v (Sum.inl 1) * v' (Sum.inr 1) + v' (Sum.inl 1) * v (Sum.inr 1))
    (fun v₁ v₂ v' => by simp only [Pi.add_apply]; ring)
    (fun c v v' => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun v v₁ v₂ => by simp only [Pi.add_apply]; ring)
    (fun c v v' => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

private theorem Bf_apply (v v' : OmI → S.K) :
    S.Bf v v' = v (Sum.inl 0) * v' (Sum.inr 0) + v' (Sum.inl 0) * v (Sum.inr 0) +
      v (Sum.inl 1) * v' (Sum.inr 1) + v' (Sum.inl 1) * v (Sum.inr 1) := by
  simp only [Bf, LinearMap.mk₂_apply]

private theorem Bf_comm (v v' : OmI → S.K) : S.Bf v v' = S.Bf v' v := by
  rw [S.Bf_apply, S.Bf_apply]
  ring

private theorem pol_eq_Bf (w w' : W) : S.pol w w' = S.Bf (S.vec w) (S.vec w') := by
  rw [S.pol_eq, S.Bf_apply]

private theorem Bf_separatingLeft : (S.Bf).SeparatingLeft := by
  intro v hv
  have h1 : S.ofVec v = 1 := by
    apply S.eq_one_of_pol_eq_zero
    intro w'
    rw [S.pol_eq_Bf, S.vec_ofVec]
    exact hv (S.vec w')
  rw [← S.vec_ofVec v, h1, S.vec_one]

private theorem Bf_nondegenerate : (S.Bf).Nondegenerate :=
  ⟨S.Bf_separatingLeft, fun v hv => S.Bf_separatingLeft v fun v' => by
    rw [S.Bf_comm]; exact hv v'⟩

private theorem mem_perp_iff_vec_mem_orthogonal {U : Subgroup W} (hU : S.IsSub U) {x : W} :
    x ∈ S.perp U ↔ S.vec x ∈ S.Bf.orthogonal (S.toSub hU) := by
  rw [S.mem_perp]
  constructor
  · intro h
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨u, hu, rfl⟩ := (S.mem_toSub hU).mp hn
    rw [S.Bf_comm, ← S.pol_eq_Bf]
    exact h u hu
  · intro h u hu
    have hv := h (S.vec u) ((S.mem_toSub hU).mpr ⟨u, hu, rfl⟩)
    rwa [S.Bf_comm, ← S.pol_eq_Bf] at hv

private theorem card_perp_eq_card_orthogonal {U : Subgroup W} (hU : S.IsSub U) :
    Nat.card (S.perp U) = Nat.card (S.Bf.orthogonal (S.toSub hU)) := by
  have h : S.toSub (S.isSub_perp U) = S.Bf.orthogonal (S.toSub hU) := by
    ext v
    rw [S.mem_toSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (S.mem_perp_iff_vec_mem_orthogonal hU).mp hx
    · intro hv
      exact ⟨S.ofVec v, (S.mem_perp_iff_vec_mem_orthogonal hU).mpr (by rwa [S.vec_ofVec]),
        S.vec_ofVec v⟩
  calc Nat.card (S.perp U) = Nat.card (S.toSub (S.isSub_perp U)) :=
        Nat.card_congr (S.subEquiv (S.isSub_perp U))
    _ = Nat.card (S.Bf.orthogonal (S.toSub hU)) := by rw [h]

private theorem finrank_omI : Module.finrank S.K (OmI → S.K) = 4 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [OmI, Fintype.card_sum]

theorem card_mul_card_perp {U : Subgroup W} (hU : S.IsSub U) :
    Nat.card U * Nat.card (S.perp U) = Nat.card S.K ^ 4 := by
  have hle : Module.finrank S.K (S.toSub hU) ≤ 4 := by
    have := Submodule.finrank_le (R := S.K) (M := OmI → S.K) (s := S.toSub hU)
    rwa [S.finrank_omI] at this
  have hUcard : Nat.card U = Nat.card S.K ^ Module.finrank S.K (S.toSub hU) := by
    rw [Nat.card_congr (S.subEquiv hU),
      Module.natCard_eq_pow_finrank (K := S.K) (V := S.toSub hU)]
  have hPcard : Nat.card (S.perp U) =
      Nat.card S.K ^ (4 - Module.finrank S.K (S.toSub hU)) := by
    rw [S.card_perp_eq_card_orthogonal hU,
      Module.natCard_eq_pow_finrank (K := S.K) (V := S.Bf.orthogonal (S.toSub hU)),
      LinearMap.BilinForm.finrank_orthogonal S.Bf_nondegenerate (S.toSub hU), S.finrank_omI]
  rw [hUcard, hPcard, ← pow_add, Nat.add_sub_cancel' hle]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
