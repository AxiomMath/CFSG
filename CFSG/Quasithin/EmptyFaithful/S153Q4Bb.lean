module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Ba

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4B

open Equiv

structure Ctx (W : Type) [CommGroup W] (Ah : Subgroup (MulAut W)) (z : MulAut W)
    (lab : Fin 6 → Subgroup W) : Prop extends ZCtx W z where
  card : Nat.card W = 2 ^ 6
  zA : z ∈ Ah
  zc : ∀ g ∈ Ah, g * z = z * g
  O : OvalData Ah z lab

section Ind

variable {W : Type} [CommGroup W] {Ah : Subgroup (MulAut W)} {z : MulAut W}
  {lab : Fin 6 → Subgroup W}

@[expose] def Ind (lab : Fin 6 → Subgroup W) (g : MulAut W) (σ : Perm (Fin 6)) : Prop :=
  ∀ k, ∀ w ∈ lab k, g w ∈ lab (σ k)

theorem Ind.one : Ind lab 1 1 := fun k w hw => by simpa using hw

theorem Ind.mul {g h : MulAut W} {σ ρ : Perm (Fin 6)} (hg : Ind lab g σ) (hh : Ind lab h ρ) :
    Ind lab (g * h) (σ * ρ) := fun k w hw => by
  simpa only [MulAut.mul_apply, Perm.mul_apply] using hg (ρ k) (h w) (hh k w hw)

theorem Ctx.pt (C : Ctx W Ah z lab) (k : Fin 6) : IsPt z (lab k) := C.O.pt k

theorem Ctx.ind_zpowers (C : Ctx W Ah z lab) {g : MulAut W} (hg : g ∈ Subgroup.zpowers z) :
    Ind lab g 1 := by
  have hz : Ind lab z 1 := fun k w hw => by simpa using (C.O.pt k).2 w hw
  rcases C.mem_zpowers hg with h | h | h
  · rw [h]; exact Ind.one
  · rw [h]; exact hz
  · rw [h]
    simpa only [mul_one] using hz.mul hz

theorem Ctx.ind_unique [Finite W] (C : Ctx W Ah z lab) {g : MulAut W} {σ σ' : Perm (Fin 6)}
    (h : Ind lab g σ) (h' : Ind lab g σ') : σ = σ' := by
  refine Equiv.ext fun l => ?_
  obtain ⟨w, hw, hw1⟩ := pt_exists_ne_one (C.O.pt l)
  have hgw1 : g w ≠ 1 := fun h1 => hw1 (EmbeddingLike.map_eq_one_iff.1 h1)
  exact C.O.inj (C.pt_eq_of_mem (C.O.pt _) (C.O.pt _) (h l w hw) (h' l w hw) hgw1)

theorem Ctx.mem_zpowers_of_ind (C : Ctx W Ah z lab) {g : MulAut W} (hg : g ∈ Ah)
    (h : Ind lab g 1) : g ∈ Subgroup.zpowers z :=
  C.O.ker g hg fun k w hw => by simpa using h k w hw

theorem Ctx.ind_inv [Finite W] (C : Ctx W Ah z lab) {g : MulAut W} (hg : g ∈ Ah)
    {σ : Perm (Fin 6)} (h : Ind lab g σ) : Ind lab g⁻¹ σ⁻¹ := by
  obtain ⟨σ', -, hσ'⟩ := C.O.equiv g⁻¹ (inv_mem hg)
  have hσ'' : Ind lab g⁻¹ σ' := hσ'
  have h1 : Ind lab (g * g⁻¹) (σ * σ') := h.mul hσ''
  rw [mul_inv_cancel] at h1
  have h2 : σ * σ' = 1 := C.ind_unique h1 Ind.one
  have h3 : σ' = σ⁻¹ := eq_inv_of_mul_eq_one_right h2
  rwa [h3] at hσ''

theorem Ctx.ne_one_of_ind [Finite W] (C : Ctx W Ah z lab) {g : MulAut W} {σ : Perm (Fin 6)}
    (h : Ind lab g σ) (hσ : σ ≠ 1) : g ≠ 1 := by
  rintro rfl
  exact hσ (C.ind_unique h Ind.one)

theorem Ind.mem_sup_of_fix {g : MulAut W} {σ : Perm (Fin 6)} (h : Ind lab g σ) (h4 : σ 4 = 4)
    (h5 : σ 5 = 5) {v : W} (hv : v ∈ lab 4 ⊔ lab 5) : g v ∈ lab 4 ⊔ lab 5 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul]
  have ha' : g a ∈ lab 4 := by simpa only [h4] using h 4 a ha
  have hb' : g b ∈ lab 5 := by simpa only [h5] using h 5 b hb
  exact Subgroup.mul_mem_sup ha' hb'

private theorem z_mul_mul {z : MulAut W} (C : ZCtx W z) : z * (z * z) = 1 := by
  simpa [pow_succ, mul_assoc] using C.cube

theorem Ctx.exists_inv_lift [Finite W] (C : Ctx W Ah z lab) {s : Perm (Fin 6)}
    (hs : s ∈ alternatingGroup (Fin 6)) (hss : s * s = 1) :
    ∃ p ∈ Ah, p * p = 1 ∧ Ind lab p s := by
  obtain ⟨g, hg, hgs⟩ := C.O.surj s hs
  have hgs' : Ind lab g s := hgs
  have h2 : Ind lab (g * g) 1 := by
    have := hgs'.mul hgs'
    rwa [hss] at this
  have hzg : g * g ∈ Subgroup.zpowers z := C.mem_zpowers_of_ind (mul_mem hg hg) h2
  have hc : g * z = z * g := C.zc g hg
  have hzz : Ind lab z 1 := C.ind_zpowers (Subgroup.mem_zpowers z)
  have hz3 : z * (z * z) = 1 := z_mul_mul C.toZCtx
  rcases C.mem_zpowers hzg with h | h | h
  · exact ⟨g, hg, h, hgs'⟩
  · refine ⟨g * z, mul_mem hg C.zA, ?_, by simpa only [mul_one] using hgs'.mul hzz⟩
    calc g * z * (g * z) = g * (z * g) * z := by simp only [mul_assoc]
      _ = g * (g * z) * z := by rw [← hc]
      _ = g * g * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [h, hz3]
  · have hc2 : g * (z * z) = z * z * g :=
      (Commute.mul_right (show Commute g z from hc) (show Commute g z from hc)).eq
    refine ⟨g * (z * z), mul_mem hg (mul_mem C.zA C.zA), ?_,
      by simpa only [mul_one] using hgs'.mul (hzz.mul hzz)⟩
    calc g * (z * z) * (g * (z * z)) = g * ((z * z) * g) * (z * z) := by simp only [mul_assoc]
      _ = g * (g * (z * z)) * (z * z) := by rw [← hc2]
      _ = g * g * ((z * z) * (z * z)) := by simp only [mul_assoc]
      _ = 1 := by
        rw [h]
        calc z * z * (z * z * (z * z)) = (z * (z * z)) * (z * (z * z)) := by
              simp only [mul_assoc]
          _ = 1 := by rw [hz3, one_mul]

theorem Ctx.inv_lift_unique [Finite W] (C : Ctx W Ah z lab) {s : Perm (Fin 6)} (hss : s * s = 1)
    {p q : MulAut W} (hp : p ∈ Ah) (hq : q ∈ Ah) (hpp : p * p = 1) (hqq : q * q = 1)
    (hps : Ind lab p s) (hqs : Ind lab q s) : p = q := by
  have h1 : Ind lab (p * q) 1 := by
    have := hps.mul hqs
    rwa [hss] at this
  have hx : p * q ∈ Subgroup.zpowers z := C.mem_zpowers_of_ind (mul_mem hp hq) h1
  have hcomm : p * (p * q) = (p * q) * p := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hpz : Commute p z := C.zc p hp
    have h3 : Commute p (z ^ m) := hpz.zpow_right m
    rw [hm] at h3
    exact h3
  have e1 : p * (p * q) = q := by rw [← mul_assoc, hpp, one_mul]
  rw [e1] at hcomm
  have hqp : q * p = p * q := by
    calc q * p = (p * q * p) * p := by rw [← hcomm]
      _ = p * q := by rw [mul_assoc, hpp, mul_one]
  have hxx : (p * q) * (p * q) = 1 := by
    calc (p * q) * (p * q) = p * (q * p) * q := by simp only [mul_assoc]
      _ = p * (p * q) * q := by rw [hqp]
      _ = (p * p) * (q * q) := by simp only [mul_assoc]
      _ = 1 := by rw [hpp, hqq, one_mul]
  have hpq1 : p * q = 1 := C.zpowers_sq hx hxx
  have hq' : q = p⁻¹ := eq_inv_of_mul_eq_one_right hpq1
  rw [hq', inv_eq_of_mul_eq_one_right hpp]

end Ind

end Q4B

end S153Q

end CFSG.Quasithin
