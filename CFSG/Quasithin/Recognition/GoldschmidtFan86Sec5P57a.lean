module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P57Mech
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan57a (F : FanTree Γ G) (h53a : Fan53a F) (h53b : Fan53b F) (h54 : Fan54 F) :
    Fan57a F := by
  intro h40 ℓ z z' a b tL tR a' b' tL' tR' hz hz' hd hd' hb
  have hr : 1 ≤ tR - b := (h53a h40 ℓ z a b tL tR hz hd).1
  have hl : 1 ≤ a' - tL' := (h53a h40 ℓ z' a' b' tL' tR' hz' hd').2.1
  have e1 := P55.fix_tL_le hd
  have e2 := P55.fix_a_lt hd
  have e3 := P55.fix_le_tR hd
  have e4 := P55.fix_tL_le hd'
  have e5 := P55.fix_a_lt hd'
  have e6 := P55.fix_le_tR hd'
  have hz2 : z * z = 1 := hz.1
  have hz'2 : z' * z' = 1 := hz'.1
  have hvp : Γ.Adj (ℓ.vert b) (ℓ.vert (b - 1)) := ℓ.adj_pred b
  have hvq : Γ.Adj (ℓ.vert b) (ℓ.vert (b + 1)) := ℓ.adj b
  have hzp : z • ℓ.vert (b - 1) = ℓ.vert (b - 1) := (hd.fix (b - 1)).2 ⟨by omega, by omega⟩
  have hzq : z • ℓ.vert (b + 1) = ℓ.vert (b + 1) := (hd.fix (b + 1)).2 ⟨by omega, by omega⟩
  have hzK : z ∈ nbrStab Γ G (ℓ.vert b) := F.fix_two_nbrs hvp hvq (ℓ.vert_pred_ne_succ b) hzp hzq
  have hzc : ∀ h : G, h • ℓ.vert (b - 1) = ℓ.vert (b - 1) → h • ℓ.vert b = ℓ.vert b →
      h * z = z * h := by
    intro h h1 h2
    have hc := hd.core.2.2.1 (b - 1) (by omega) (by omega)
    refine hc.2 h ⟨MulAction.mem_stabilizer_iff.2 h1, MulAction.mem_stabilizer_iff.2 ?_⟩
    rw [sub_add_cancel]
    exact h2
  have hz'v : z' • ℓ.vert b = ℓ.vert b := (hd'.fix b).2 ⟨by omega, by omega⟩
  have hz'q : z' • ℓ.vert (b + 1) = ℓ.vert (b + 1) := (hd'.fix (b + 1)).2 ⟨by omega, by omega⟩
  have hz'p : z' • ℓ.vert (b - 1) ≠ ℓ.vert (b - 1) := fun h => by
    have := (hd'.fix (b - 1)).1 h
    omega
  have hz'K : z' ∉ nbrStab Γ G (ℓ.vert b) := fun h => hz'p (mem_nbrStab.1 h _ hvp)
  obtain ⟨hu2, hucomm⟩ := P57.mech F hvp hvq hz2 hz'2 hzK hzc hz'v hz'q hz'K
  have hinv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  have hinv0 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hfc : fcomm z z' = z * (z' * z * z'⁻¹) := by
    simp only [fcomm, hinv, hinv0, mul_assoc]
  have hnc : z' * z ≠ z * z' := by
    have hcore : ℓ.IsCoreC z a b := h53b h40 ℓ z a b hz hd.core
    exact h54 h40 ℓ z a b (P55.zz_le_zc hz) hcore b (b - 1) (Or.inl ⟨rfl, rfl⟩) z'
      (MulAction.mem_stabilizer_iff.2 hz'v) (fun h => hz'p (MulAction.mem_stabilizer_iff.1 h))
  have hne1 : fcomm z z' ≠ 1 := by
    intro h1
    apply hnc
    have h2 : z * z' * (z * z') = 1 := by
      have := h1
      simp only [fcomm, hinv, hinv0, mul_assoc] at this
      simpa [mul_assoc] using this
    have h3 : z * z' = z' * z := by
      have := inv_eq_of_mul_eq_one_right h2
      simpa [hinv, hinv0, mul_inv_rev] using this.symm
    exact h3.symm
  refine ⟨hne1, by rw [hfc]; exact hu2, ?_⟩
  rw [hfc]
  have huv : (z * (z' * z * z'⁻¹)) • ℓ.vert b = ℓ.vert b := by
    have h1 : z'⁻¹ • ℓ.vert b = ℓ.vert b := inv_smul_eq_iff.2 hz'v.symm
    have h2 : z • ℓ.vert b = ℓ.vert b := MulAction.mem_stabilizer_iff.1
      (F.nbrStab_le_stabilizer _ hzK)
    simp only [mul_smul, h1, h2, hz'v]
  have huq : (z * (z' * z * z'⁻¹)) • ℓ.vert (b + 1) = ℓ.vert (b + 1) := by
    have h1 : z'⁻¹ • ℓ.vert (b + 1) = ℓ.vert (b + 1) := inv_smul_eq_iff.2 hz'q.symm
    simp only [mul_smul, h1, hz'q, hzq]
  refine ⟨P55.mem_edgeCirc_of_fix hu2 huv huq, fun h hh => ?_⟩
  have hfix := ℓ.edgeCirc_fix hh
  exact hucomm h hfix.1 hfix.2 (P57.edgeCirc_cond F ℓ hh).1

end CFSG.Quasithin.Fan86
