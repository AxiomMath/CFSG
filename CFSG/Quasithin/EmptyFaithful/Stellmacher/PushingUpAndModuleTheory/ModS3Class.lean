module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModelBase

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

theorem s3d_sq_ne_one : s3d ^ 2 ≠ 1 := by decide +kernel

theorem zpow_eq_one_or_self {W : Type} [CommGroup W] (hsq : ∀ w : W, w * w = 1) (v : W) (k : ℤ) :
    v ^ k = 1 ∨ v ^ k = v := by
  have hv2 : v ^ 2 = 1 := by
    rw [pow_two]
    exact hsq v
  rw [zpow_eq_zpow_emod' k hv2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have : k % (2 : ℕ) = 0 := by exact_mod_cast h
    rw [this]
    simp
  · right
    have : k % (2 : ℕ) = 1 := by exact_mod_cast h
    rw [this]
    simp

structure S3Frame (M : Model 3) (u : M.W) : Prop where
  fix_t : M.act s3t u = u
  ne_one : u ≠ 1
  d_ne : M.act s3d u ≠ u
  rel : M.act s3d (M.act s3d u) = u * M.act s3d u
  span : ∀ w : M.W, w = 1 ∨ w = u ∨ w = M.act s3d u ∨ w = u * M.act s3d u

namespace S3Frame

variable {M : Model 3} {u : M.W}

theorem ne_one_d (h : S3Frame M u) : M.act s3d u ≠ 1 := fun h1 =>
  h.ne_one ((M.act s3d).injective (by rw [h1, map_one]))

theorem fourFrame (h : S3Frame M u) : FourFrame u (M.act s3d u) where
  sq := M.sq
  ne_a := h.ne_one
  ne_b := h.ne_one_d
  ne_ab := fun h1 => h.d_ne h1.symm
  span := h.span

theorem act_t_d (h : S3Frame M u) : M.act s3t (M.act s3d u) = u * M.act s3d u := by
  rw [s3_act_t_d, h.fix_t, h.rel]

theorem exists_iso {N : Model 3} {u' : N.W} (h : S3Frame M u) (h' : S3Frame N u') :
    ∃ e : M.Iso N, e.toMulEquiv u = u' := by
  obtain ⟨e, he1, he2⟩ := h.fourFrame.exists_mulEquiv h'.fourFrame
  have hd : ∀ w, e (M.act s3d w) = N.act s3d (e w) := by
    intro w
    have key := FourFrame.hom_ext h.fourFrame (e.toMonoidHom.comp (M.act s3d).toMonoidHom)
      ((N.act s3d).toMonoidHom.comp e.toMonoidHom) ?_ ?_
    · exact DFunLike.congr_fun key w
    · show e (M.act s3d u) = N.act s3d (e u)
      rw [he1, he2]
    · show e (M.act s3d (M.act s3d u)) = N.act s3d (e (M.act s3d u))
      rw [h.rel, map_mul, he1, he2, h'.rel]
  have ht : ∀ w, e (M.act s3t w) = N.act s3t (e w) := by
    intro w
    have key := FourFrame.hom_ext h.fourFrame (e.toMonoidHom.comp (M.act s3t).toMonoidHom)
      ((N.act s3t).toMonoidHom.comp e.toMonoidHom) ?_ ?_
    · exact DFunLike.congr_fun key w
    · show e (M.act s3t u) = N.act s3t (e u)
      rw [h.fix_t, he1, h'.fix_t]
    · show e (M.act s3t (M.act s3d u)) = N.act s3t (e (M.act s3d u))
      rw [h.act_t_d, map_mul, he1, he2, h'.act_t_d]
  exact ⟨⟨e, act_eq_of_gens e hd ht⟩, he1⟩

end S3Frame

theorem exists_fixed_t (M : Model 3) {w : M.W} (hw : w ≠ 1) : ∃ v : M.W, v ≠ 1 ∧ M.act s3t v = v := by
  by_cases h : M.act s3t w = w
  · exact ⟨w, hw, h⟩
  · refine ⟨M.act s3t w * w⁻¹, fun h1 => h (mul_inv_eq_one.mp h1), ?_⟩
    rw [map_mul, map_inv, s3_act_t_t, inv_eq_of_mul_eq_one_right (M.sq w),
      inv_eq_of_mul_eq_one_right (M.sq (M.act s3t w)), mul_comm]

theorem exists_frame_of_irred {M : Model 3} (hM : M.IsIrred) (hC : ∀ w : M.W, M.act s3d w = w → w = 1) :
    ∃ u : M.W, S3Frame M u := by
  obtain ⟨w, hw⟩ := hM.1
  obtain ⟨u, hu1, hut⟩ := exists_fixed_t M hw
  have hdne : M.act s3d u ≠ u := fun h => hu1 (hC u h)
  have hrel : M.act s3d (M.act s3d u) = u * M.act s3d u := by
    have hx : M.act s3d (u * M.act s3d u * M.act s3d (M.act s3d u)) =
        u * M.act s3d u * M.act s3d (M.act s3d u) := by
      rw [map_mul, map_mul, s3_act_d_three]
      rw [mul_comm (M.act s3d u * M.act s3d (M.act s3d u)) u, mul_assoc]
    have h1 := hC _ hx
    have h2 := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (M.sq _)
  let U : Subgroup M.W := Subgroup.closure {u, M.act s3d u}
  have hu : u ∈ U := Subgroup.subset_closure (by simp)
  have hdu : M.act s3d u ∈ U := Subgroup.subset_closure (by simp)
  have hd : ∀ x ∈ U, M.act s3d x ∈ U := by
    have : U ≤ U.comap (M.act s3d).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x (h | h)
      · rw [h]
        exact hdu
      · rw [Set.mem_singleton_iff.mp h]
        show M.act s3d (M.act s3d u) ∈ U
        rw [hrel]
        exact U.mul_mem hu hdu
    exact fun x hx => this hx
  have ht : ∀ x ∈ U, M.act s3t x ∈ U := by
    have : U ≤ U.comap (M.act s3t).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro x (h | h)
      · rw [h]
        show M.act s3t u ∈ U
        rw [hut]
        exact hu
      · rw [Set.mem_singleton_iff.mp h]
        show M.act s3t (M.act s3d u) ∈ U
        rw [s3_act_t_d, hut, hrel]
        exact U.mul_mem hu hdu
    exact fun x hx => this hx
  have hUtop : U = ⊤ := by
    rcases hM.2 U (isInvSub_top_of_gens hd ht) with h | h
    · exact absurd ((Subgroup.eq_bot_iff_forall U).mp h u hu) hu1
    · exact h
  refine ⟨u, hut, hu1, hdne, hrel, fun w => ?_⟩
  have hw : w ∈ U := by rw [hUtop]; trivial
  obtain ⟨m, k, rfl⟩ := Subgroup.mem_closure_pair.mp hw
  rcases zpow_eq_one_or_self M.sq u m with h1 | h1 <;>
    rcases zpow_eq_one_or_self M.sq (M.act s3d u) k with h2 | h2 <;> simp [h1, h2]

theorem nat3_isIrred : nat3.IsIrred := by
  refine ⟨?_, fun U hU => X1512.coreMod_irreducible (Or.inl rfl) U
    (fun σ y hy => hU σ (Subgroup.mem_top σ) y hy)⟩
  by_contra hcon
  push Not at hcon
  have : Nat.card nat3.W = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
  rw [card_nat3] at this
  omega

theorem nat3_fixed_d {w : nat3.W} (h : nat3.act s3d w = w) : w = 1 := by
  have h1 := idx_mul_card nat3 s3d
  have h0 := idx_nat3 s3d
  simp only [s3d_ne_one, s3d_sq_ne_one, ite_false] at h0
  rw [h0, card_nat3] at h1
  have h2 : Nat.card {w : nat3.W // nat3.act s3d w = w} = 1 := by omega
  rw [Nat.card_eq_one_iff_unique] at h2
  obtain ⟨⟨hsub⟩, _⟩ := h2
  have := hsub ⟨w, h⟩ ⟨1, by simp⟩
  exact congrArg Subtype.val this

theorem exists_frame_nat3 : ∃ u : nat3.W, S3Frame nat3 u :=
  exists_frame_of_irred nat3_isIrred (fun _ h => nat3_fixed_d h)

theorem fixW_A3_eq_top_iff (M : Model 3) :
    fixW M (alternatingGroup (Fin 3)) = ⊤ ↔ ∀ w : M.W, M.act s3d w = w := by
  rw [alternatingGroup_three, eq_top_iff]
  constructor
  · intro h w
    exact (mem_fixW_zpowers M).mp (h (Subgroup.mem_top w))
  · intro h w _
    exact (mem_fixW_zpowers M).mpr (h w)

theorem nat3_faithful : nat3.Faithful := by
  rw [Model.Faithful, injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  have h1 : fixW nat3 (Subgroup.zpowers σ) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [mem_fixW_zpowers, hσ]
    rfl
  have h2 : idx nat3 σ = 1 := by
    unfold idx
    rw [h1]
    exact Subgroup.index_top
  rw [idx_nat3] at h2
  simp only [hne, ite_false] at h2
  split_ifs at h2 <;> omega

theorem Model.Iso.faithful {M N : Model 3} (e : M.Iso N) (h : N.Faithful) : M.Faithful := by
  intro σ τ hστ
  apply h
  ext y
  obtain ⟨w, rfl⟩ := e.toMulEquiv.surjective y
  rw [← e.map_act, ← e.map_act, hστ]

end CFSG.Quasithin.F53Mod
