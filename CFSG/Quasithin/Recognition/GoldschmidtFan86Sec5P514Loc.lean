module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def cj (z z' : G) : G := z' * z * z'

theorem cj_mul_self {z z' : G} (hz : z * z = 1) (hz' : z' * z' = 1) : cj z z' * cj z z' = 1 := by
  have : cj z z' * cj z z' = z' * (z * (z' * z') * z) * z' := by simp only [cj]; group
  rw [this, hz', mul_one, hz]
  simpa using hz'

theorem cj_mem_nbrStab (F : FanTree Γ G) {v : V} {z z' : G} (hz' : z' * z' = 1)
    (hv : z' • v = v) (hz : z ∈ nbrStab Γ G v) : cj z z' ∈ nbrStab Γ G v := by
  have h := F.conj_mem_nbrStab_smul z' hz
  rw [hv, inv_eq_of_mul_eq_one_right hz'] at h
  exact h

theorem gcirc_cases (F : FanTree Γ G) {v q : V} (hvq : Γ.Adj v q) {z' : G}
    (hz' : z' ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G q)
    (hz2 : z' * z' = 1) (hzn : z' ∉ nbrStab Γ G v) {g : G} (hg : g ∈ Gcirc Γ G v q) :
    g ∈ nbrStab Γ G v ∨ z' * g ∈ nbrStab Γ G v := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hvq
  let e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G q) := ⟨g, hg.1⟩
  let e' : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G q) := ⟨z', hz'⟩
  have hp : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  have h2 : φ e * φ e = 1 := by
    rw [← map_mul]
    exact (hφ (e * e)).1 hg.2
  have he2' : e' * e' = 1 := Subtype.ext hz2
  have h2' : φ e' * φ e' = 1 := by rw [← map_mul, he2', map_one]
  have h1' : φ e' ≠ 1 := fun h => hzn ((hφ e').2 h)
  by_cases h1 : φ e = 1
  · exact Or.inl ((hφ e).2 h1)
  · right
    have h3 := units_sq_eq_one_unique hp (φ e) (φ e') h1 h2 h1' h2'
    have h4 : φ (e'⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, ← h3, inv_mul_cancel]
    have h5 := (hφ (e'⁻¹ * e)).2 h4
    have h6 : ((e'⁻¹ * e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G q)) : G) =
        z' * g := by
      simp [e, e', inv_eq_of_mul_eq_one_right hz2]
    rwa [h6] at h5

theorem comm_cj_aux {z' a b : G} (hz2 : z' * z' = 1)
    (h : (z' * a * z') * b = b * (z' * a * z')) : a * (z' * b * z') = (z' * b * z') * a := by
  calc a * (z' * b * z') = z' * ((z' * a * z') * b) * z' := by
        calc a * (z' * b * z') = (z' * z') * a * (z' * b * z') := by rw [hz2, one_mul]
          _ = z' * ((z' * a * z') * b) * z' := by simp only [mul_assoc]
    _ = z' * (b * (z' * a * z')) * z' := by rw [h]
    _ = z' * b * z' * a * (z' * z') := by simp only [mul_assoc]
    _ = (z' * b * z') * a := by rw [hz2, mul_one]

theorem perm_cen (F : FanTree Γ G) {v p q : V} (hvp : Γ.Adj v p) (hvq : Γ.Adj v q) (hpq : p ≠ q)
    {z z' : G} (hz2 : z * z = 1) (hz2' : z' * z' = 1) (hzv : z • v = v) (hzp : z • p = p)
    (hzq : z • q = q) (hcen : z ∈ Cen (Gcirc Γ G v p)) (hz'v : z' • v = v) (hz'q : z' • q = q)
    (hz'p : z' • p ≠ p) :
    (z * cj z z') * (z * cj z z') = 1 ∧ z * cj z z' ∈ Cen (Gcirc Γ G v q) := by
  have hzK : z ∈ nbrStab Γ G v := mem_nbrStab.2 fun w hw =>
    F.frobenius_two v p q hvp hvq hpq z (MulAction.mem_stabilizer_iff.2 hzv) hzp hzq w hw
  have hsK : cj z z' ∈ nbrStab Γ G v := cj_mem_nbrStab F hz2' hz'v hzK
  have hs2 : cj z z' * cj z z' = 1 := cj_mul_self hz2 hz2'
  have hsz : cj z z' * z = z * cj z z' := hcen.2 _ (F.nbrStab_le_gcirc hvp hsK)
  have hw2 : (z * cj z z') * (z * cj z z') = 1 := by
    calc (z * cj z z') * (z * cj z z') = z * (cj z z' * z) * cj z z' := by simp only [mul_assoc]
      _ = (z * z) * (cj z z' * cj z z') := by rw [hsz]; simp only [mul_assoc]
      _ = 1 := by rw [hz2, hs2, one_mul]
  have hwK : z * cj z z' ∈ nbrStab Γ G v := (nbrStab Γ G v).mul_mem hzK hsK
  have hz'n : z' ∉ nbrStab Γ G v := fun h => hz'p (mem_nbrStab.1 h p hvp)
  have hz'st : z' ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G q :=
    ⟨MulAction.mem_stabilizer_iff.2 hz'v, MulAction.mem_stabilizer_iff.2 hz'q⟩
  have hK : ∀ g ∈ nbrStab Γ G v, g * (z * cj z z') = (z * cj z z') * g := by
    intro g hg
    have h1 : g * z = z * g := hcen.2 _ (F.nbrStab_le_gcirc hvp hg)
    have h2 : (cj g z') * z = z * (cj g z') := hcen.2 _ (F.nbrStab_le_gcirc hvp
      (cj_mem_nbrStab F hz2' hz'v hg))
    have h3 : g * cj z z' = cj z z' * g := comm_cj_aux hz2' h2
    calc g * (z * cj z z') = (g * z) * cj z z' := by rw [mul_assoc]
      _ = z * (g * cj z z') := by rw [h1, mul_assoc]
      _ = z * (cj z z' * g) := by rw [h3]
      _ = (z * cj z z') * g := by rw [mul_assoc]
  refine ⟨hw2, F.nbrStab_le_gcirc hvq hwK, fun g hg => ?_⟩
  have hz'zz : z' * cj z z' * z' = z := by
    calc z' * cj z z' * z' = (z' * z') * z * (z' * z') := by simp only [cj, mul_assoc]
      _ = z := by rw [hz2', one_mul, mul_one]
  have hz'w : z' * (z * cj z z') = (z * cj z z') * z' := by
    have e : z' * (z * cj z z') * z' = z * cj z z' := by
      calc z' * (z * cj z z') * z' = (z' * z * z') * (z' * cj z z' * z') := by
            calc z' * (z * cj z z') * z' = z' * z * (z' * z') * cj z z' * z' := by
                  rw [hz2', mul_one]; simp only [mul_assoc]
              _ = (z' * z * z') * (z' * cj z z' * z') := by simp only [mul_assoc]
        _ = cj z z' * z := by rw [hz'zz]; rfl
        _ = z * cj z z' := hsz
    calc z' * (z * cj z z') = z' * (z * cj z z') * (z' * z') := by rw [hz2', mul_one]
      _ = (z' * (z * cj z z') * z') * z' := by simp only [mul_assoc]
      _ = (z * cj z z') * z' := by rw [e]
  rcases gcirc_cases F hvq hz'st hz2' hz'n hg with hg1 | hg1
  · exact hK g hg1
  · have hk := hK _ hg1
    have hg' : g = z' * (z' * g) := by rw [← mul_assoc, hz2', one_mul]
    calc g * (z * cj z z') = (z' * (z' * g)) * (z * cj z z') := by rw [← hg']
      _ = z' * ((z' * g) * (z * cj z z')) := by rw [mul_assoc]
      _ = z' * ((z * cj z z') * (z' * g)) := by rw [hk]
      _ = (z' * (z * cj z z')) * (z' * g) := by simp only [mul_assoc]
      _ = ((z * cj z z') * z') * (z' * g) := by rw [hz'w]
      _ = (z * cj z z') * (z' * (z' * g)) := by simp only [mul_assoc]
      _ = (z * cj z z') * g := by rw [← hg']

theorem perm_ne_one {z z' : G} (hz2 : z * z = 1) (hz2' : z' * z' = 1) (hne : z' * z ≠ z * z') :
    z * cj z z' ≠ 1 := by
  intro h
  apply hne
  have h1 : cj z z' = z := by
    have := eq_inv_of_mul_eq_one_right h
    rwa [inv_eq_of_mul_eq_one_right hz2] at this
  calc z' * z = z' * z * (z' * z') := by rw [hz2', mul_one]
    _ = (z' * z * z') * z' := by simp only [mul_assoc]
    _ = z * z' := by rw [show z' * z * z' = cj z z' from rfl, h1]

end P514

end CFSG.Quasithin.Fan86
