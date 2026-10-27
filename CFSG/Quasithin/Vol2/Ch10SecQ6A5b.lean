module

public import CFSG.Quasithin.Vol2.Ch10SecQ6A5a
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

variable {W : Type*} [CommGroup W]

theorem pv_pv_inv (σ : Perm (Fin 5)) (u : Fin 5 → ZMod 2) : pv σ (pv σ⁻¹ u) = u := by
  rw [← pv_mul, mul_inv_cancel, pv_one]

theorem wv_ne_zero (k : Fin 5) : wv k ≠ 0 := by
  revert k
  decide

theorem exists_perm_of_normalizes {Λ : Subgroup (MulAut W)} {π : alternatingGroup (Fin 5) →* Λ}
    {Ψ : W → Fin 5 → ZMod 2} (hc : IsA5Coord Λ π Ψ) {n : MulAut W}
    (hn : n ∈ Subgroup.normalizer (Λ : Set (MulAut W))) :
    ∃ σ : Perm (Fin 5), ∀ w, Ψ (n w) = pv σ (Ψ w) := by
  obtain ⟨hsurj, hmul, hinj, hO, honto, heq⟩ := hc
  have hΨ1 : Ψ 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero (Ψ 1)).symm)
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply eq_one_of_fix_O
    intro u hu
    obtain ⟨w, rfl⟩ := honto u hu
    rw [← heq, hγ]
    rfl
  let πe := MulEquiv.ofBijective π ⟨hπinj, hsurj⟩
  have hmemΛ : ∀ l : MulAut W, l ∈ Λ ↔ n * l * n⁻¹ ∈ Λ := fun l =>
    Subgroup.mem_normalizer_iff.mp hn l
  let cn : Λ ≃* Λ :=
    { toFun := fun l => ⟨n * l * n⁻¹, (hmemΛ l).mp l.2⟩
      invFun := fun l => ⟨n⁻¹ * l * n, (hmemΛ _).mpr (by
        rw [show n * (n⁻¹ * (l : MulAut W) * n) * n⁻¹ = l by group]
        exact l.2)⟩
      left_inv := fun l => Subtype.ext (by
        change n⁻¹ * (n * (l : MulAut W) * n⁻¹) * n = l
        group)
      right_inv := fun l => Subtype.ext (by
        change n * (n⁻¹ * (l : MulAut W) * n) * n⁻¹ = l
        group)
      map_mul' := fun a b => Subtype.ext (by
        change n * ((a : MulAut W) * b) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹)
        group) }
  let α : MulAut (alternatingGroup (Fin 5)) := πe.trans (cn.trans πe.symm)
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).2 α
  have hconj : ∀ γ : alternatingGroup (Fin 5),
      ((π (MulAut.conjNormal σ γ) : Λ) : MulAut W) = n * (π γ : MulAut W) * n⁻¹ := by
    intro γ
    rw [hσ]
    have h1 : π (πe.symm (cn (πe γ))) = cn (πe γ) := πe.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hDmul : ∀ a b : W, pv σ⁻¹ (Ψ (n (a * b))) = pv σ⁻¹ (Ψ (n a)) + pv σ⁻¹ (Ψ (n b)) := by
    intro a b
    rw [map_mul, hmul, pv_add]
  have hDeq : ∀ (γ : alternatingGroup (Fin 5)) (w : W),
      pv σ⁻¹ (Ψ (n ((π γ : MulAut W) w))) = pv γ (pv σ⁻¹ (Ψ (n w))) := by
    intro γ w
    have h1 : n ((π γ : MulAut W) w) = (π (MulAut.conjNormal σ γ) : MulAut W) (n w) := by
      rw [hconj]
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [h1, heq, MulAut.conjNormal_apply, ← pv_mul, ← pv_mul,
      show σ⁻¹ * (σ * (γ : Perm (Fin 5)) * σ⁻¹) = (γ : Perm (Fin 5)) * σ⁻¹ by group]
  obtain ⟨w4, hw4⟩ := honto (wv 4) (isO_wv 4)
  have hfix4 : ∀ (v : Perm (Fin 5)) (hv : v ∈ alternatingGroup (Fin 5)), v 4 = 4 →
      (π ⟨v, hv⟩ : MulAut W) w4 = w4 := by
    intro v hv hv4
    apply hinj
    rw [heq, hw4, pv_wv]
    change wv (v 4) = wv 4
    rw [hv4]
  have hD4 : pv σ⁻¹ (Ψ (n w4)) = wv 4 := by
    have ha := hDeq ⟨va, va_mem⟩ w4
    have hb := hDeq ⟨vb, vb_mem⟩ w4
    rw [hfix4 va va_mem (by decide)] at ha
    rw [hfix4 vb vb_mem (by decide)] at hb
    rcases fixO_V4 _ ((isO_pv _ _).mpr (hO _)) ha.symm hb.symm with h | h
    · exfalso
      have h1 : Ψ (n w4) = Ψ 1 := by rw [hΨ1, ← pv_pv_inv σ (Ψ (n w4)), h, pv_zero]
      have h2 : w4 = 1 := by
        have h3 := hinj h1
        rw [← map_one n] at h3
        exact n.injective h3
      rw [h2, hΨ1] at hw4
      exact wv_ne_zero 4 hw4.symm
    · exact h
  have hDk : ∀ k : Fin 5, ∃ wk : W, Ψ wk = wv k ∧ pv σ⁻¹ (Ψ (n wk)) = wv k := by
    intro k
    obtain ⟨γ, hγ, hγk⟩ := exists_alt_apply k
    refine ⟨(π ⟨γ, hγ⟩ : MulAut W) w4, ?_, ?_⟩
    · rw [heq, hw4, pv_wv]
      change wv (γ 4) = wv k
      rw [hγk]
    · rw [hDeq, hD4, pv_wv]
      change wv (γ 4) = wv k
      rw [hγk]
  refine ⟨σ, fun w => ?_⟩
  obtain ⟨k1, k2, k3, k4, hk⟩ := exists_four_wv (Ψ w) (hO w)
  obtain ⟨a1, ha1, hb1⟩ := hDk k1
  obtain ⟨a2, ha2, hb2⟩ := hDk k2
  obtain ⟨a3, ha3, hb3⟩ := hDk k3
  obtain ⟨a4, ha4, hb4⟩ := hDk k4
  have hw : w = a1 * a2 * a3 * a4 := hinj (by rw [hk, hmul, hmul, hmul, ha1, ha2, ha3, ha4])
  have hD : pv σ⁻¹ (Ψ (n w)) = Ψ w := by
    rw [hw, hDmul, hDmul, hDmul, hb1, hb2, hb3, hb4, hmul, hmul, hmul, ha1, ha2, ha3, ha4]
  rw [← hD, pv_pv_inv]

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
