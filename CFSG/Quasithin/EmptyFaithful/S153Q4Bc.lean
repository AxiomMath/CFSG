module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Bb

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4B

open Equiv

section Cen

variable {W : Type} [CommGroup W] {Ah : Subgroup (MulAut W)} {z : MulAut W}
  {lab : Fin 6 → Subgroup W}

@[expose] def nHom (p : MulAut W) : W →* W where
  toFun w := p w * w⁻¹
  map_one' := by simp
  map_mul' a b := by simp [mul_comm, mul_left_comm, mul_assoc]

@[expose] def cen (p : MulAut W) : Subgroup W := (nHom p).range

theorem nHom_apply (p : MulAut W) (w : W) : nHom p w = p w * w⁻¹ := rfl

theorem mem_cen {p : MulAut W} {y : W} : y ∈ cen p ↔ ∃ w : W, p w * w⁻¹ = y := Iff.rfl

theorem nHom_mem_cen (p : MulAut W) (w : W) : p w * w⁻¹ ∈ cen p := ⟨w, rfl⟩

private theorem bc_apply_comm {p : MulAut W} (hpz : p * z = z * p) (w : W) :
    p (z w) = z (p w) := by
  simpa only [MulAut.mul_apply] using congrArg (fun g : MulAut W => g w) hpz

private theorem bc_invol_apply {p : MulAut W} (hpp : p * p = 1) (w : W) :
    p (p w) = w := by
  simpa only [MulAut.mul_apply, MulAut.one_apply] using congrArg (fun g : MulAut W => g w) hpp

theorem ZCtx.pt_triv [Finite W] (C : ZCtx W z) {o : Subgroup W} (ho : IsPt z o) {p : MulAut W}
    (hpz : p * z = z * p) (hpp : p * p = 1) (hpo : ∀ w ∈ o, p w ∈ o) : ∀ w ∈ o, p w = w := by
  intro w hw
  by_cases hw1 : w = 1
  · subst hw1
    exact map_one p
  · have hpc := bc_apply_comm hpz
    have hp2 := bc_invol_apply hpp
    rcases C.pt_elems ho hw hw1 (hpo w hw) with h | h | h | h
    · exact absurd (calc w = p (p w) := (hp2 w).symm
        _ = p 1 := by rw [h]
        _ = 1 := map_one p) hw1
    · exact h
    · refine absurd ?_ (C.zz_ne hw1)
      calc z (z w) = z (p w) := by rw [h]
        _ = p (z w) := (hpc w).symm
        _ = p (p w) := by rw [h]
        _ = w := hp2 w
    · have h1 : w = z (z (z (z w))) := by
        calc w = p (p w) := (hp2 w).symm
          _ = p (z (z w)) := by rw [h]
          _ = z (p (z w)) := hpc _
          _ = z (z (p w)) := by rw [hpc w]
          _ = z (z (z (z w))) := by rw [h]
      refine absurd ?_ (C.z_ne hw1)
      calc z w = z (z (z (z w))) := (C.apply_z3 (z w)).symm
        _ = w := h1.symm

theorem Ctx.fix_sup [Finite W] (C : Ctx W Ah z lab) {p : MulAut W} (hp : p ∈ Ah)
    (hpp : p * p = 1) {σ : Perm (Fin 6)} (hps : Ind lab p σ) (h4 : σ 4 = 4) (h5 : σ 5 = 5) :
    ∀ v ∈ lab 4 ⊔ lab 5, p v = v := by
  have hpz : p * z = z * p := C.zc p hp
  have t4 : ∀ w ∈ lab 4, p w = w := C.toZCtx.pt_triv (C.O.pt 4) hpz hpp fun w hw => by
    simpa only [h4] using hps 4 w hw
  have t5 : ∀ w ∈ lab 5, p w = w := C.toZCtx.pt_triv (C.O.pt 5) hpz hpp fun w hw => by
    simpa only [h5] using hps 5 w hw
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, t4 a ha, t5 b hb]

theorem Ctx.cen_spec [Finite W] (C : Ctx W Ah z lab) {p : MulAut W} (hp : p ∈ Ah) (hp1 : p ≠ 1)
    (hpp : p * p = 1) {V : Subgroup W} (hV : Nat.card ↥V = 16) (hpV : ∀ v ∈ V, p v = v) :
    IsPt z (cen p) ∧ cen p ≤ V := by
  have hpc := bc_apply_comm (C.zc p hp)
  have hp2 := bc_invol_apply hpp
  have hVker : V ≤ (nHom p).ker := fun v hv => by
    rw [MonoidHom.mem_ker, nHom_apply, hpV v hv, mul_inv_cancel]
  have hzinv : ∀ y ∈ cen p, z y ∈ cen p := by
    rintro y ⟨w, rfl⟩
    exact ⟨z w, by rw [nHom_apply, nHom_apply, map_mul, map_inv, hpc]⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w, p w ≠ w := by
    by_contra hcon
    exact hp1 (MulEquiv.ext fun w => by_contra fun h => hcon ⟨w, h⟩)
  have h4le : 4 ≤ Nat.card ↥(cen p) :=
    C.toZCtx.four_le hzinv (nHom_mem_cen p w₀) fun h => hw₀ (mul_inv_eq_one.1 h)
  have hmul : Nat.card ↥(nHom p).ker * Nat.card ↥(cen p) = 64 := by
    rw [cen, Subgroup.card_ker_mul_card_range, C.card]
    norm_num
  have hkle : 16 ≤ Nat.card ↥(nHom p).ker := hV ▸ Subgroup.card_le_of_le hVker
  have hcard : Nat.card ↥(cen p) = 4 := by
    have : 16 * Nat.card ↥(cen p) ≤ Nat.card ↥(nHom p).ker * Nat.card ↥(cen p) :=
      Nat.mul_le_mul_right _ hkle
    omega
  have hker : Nat.card ↥(nHom p).ker = 16 := by
    rw [hcard] at hmul
    omega
  have hnn : ∀ w, nHom p (nHom p w) = 1 := fun w => by
    rw [nHom_apply, nHom_apply, map_mul, map_inv, hp2]
    simp only [C.inv_eq]
    calc w * p w * (p w * w) = w * (p w * p w) * w := by simp only [mul_assoc]
      _ = 1 := by rw [C.sq (p w), mul_one, C.sq w]
  have hle : cen p ≤ (nHom p).ker := by
    rintro y ⟨w, rfl⟩
    exact hnn w
  have hVeq : V = (nHom p).ker :=
    Subgroup.eq_of_le_of_card_ge hVker (by rw [hker, hV])
  exact ⟨⟨hcard, hzinv⟩, hVeq ▸ hle⟩

theorem lab_le_sup_cen {p : MulAut W} (hpp : p * p = 1) {s : Perm (Fin 6)} (hss : s * s = 1)
    (hps : Ind lab p s) (k : Fin 6) : lab (s k) ≤ lab k ⊔ cen p := by
  intro y hy
  have hss' : s (s k) = k := by
    simpa only [Perm.mul_apply, Perm.one_apply] using congrArg (fun g : Perm (Fin 6) => g k) hss
  have hx : p y ∈ lab k := by simpa only [hss'] using hps (s k) y hy
  have e : p (p y) * (p y)⁻¹ * p y = y := by
    rw [inv_mul_cancel_right, bc_invol_apply hpp]
  rw [sup_comm]
  simpa only [e] using Subgroup.mul_mem_sup (nHom_mem_cen p (p y)) hx

end Cen

end Q4B

end S153Q

end CFSG.Quasithin
