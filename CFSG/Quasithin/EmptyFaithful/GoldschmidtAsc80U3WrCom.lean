module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3WrSyl
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Gen

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.B6 CFSG.QuasithinUnique

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (hF : Nat.card F = p ^ 2)

theorem commutator_monoCU_le_diagCU [Finite F] : ⁅monoCU hF, monoCU hF⁆ ≤ diagCU hF :=
  commutator_le_of_relIndex_eq_two (relIndex_diagCU_monoCU hF)

variable {hF}

theorem diagU_comm {a b : SU3F p F} (ha : a ∈ diagU hF) (hb : b ∈ diagU hF) : a * b = b * a := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  apply ext_matU
  rw [matU_mul, matU_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6,
      mul_comm]

theorem diagCU_comm {a b : PSU3F p F} (ha : a ∈ diagCU hF) (hb : b ∈ diagCU hF) :
    a * b = b * a := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  rw [← map_mul, ← map_mul, diagU_comm ha hb]

@[expose] noncomputable def xEU (hF : Nat.card F = p ^ 2) (u : ↥(muU hF)) : SU3F p F :=
  diagHomU hF (u, 1)

@[expose] noncomputable def xOU (hF : Nat.card F = p ^ 2) (u : ↥(muU hF)) : SU3F p F :=
  diagHomU hF (u, u⁻¹)

theorem matU_xEU (u : ↥(muU hF)) :
    matU (xEU hF u) = Matrix.diagonal ![((u : Fˣ) : F), 1, (((u * 1)⁻¹ : ↥(muU hF)) : Fˣ)] := rfl

theorem matU_xOU (u : ↥(muU hF)) :
    matU (xOU hF u) = Matrix.diagonal ![((u : Fˣ) : F), (((u⁻¹ : ↥(muU hF)) : Fˣ) : F), 1] := by
  rw [xOU, matU_diagHomU]
  congr 1
  ext j
  fin_cases j
  · rfl
  · rfl
  · simp

theorem xEU_mul_eq (u : ↥(muU hF)) {g : SU3F p F} (h02 : matU g 0 2 = 0) (h12 : matU g 1 2 = 0)
    (h20 : matU g 2 0 = 0) (h21 : matU g 2 1 = 0) (h00 : matU g 0 0 = 0) (h11 : matU g 1 1 = 0) :
    xEU hF u * g = xOU hF u * g * xEU hF u := by
  have hinv : (((u⁻¹ : ↥(muU hF)) : Fˣ) : F) * ((u : Fˣ) : F) = 1 := by
    simp
  apply ext_matU
  rw [matU_mul, matU_mul, matU_mul, matU_xEU, matU_xOU]
  exact diag_mul_eq hinv (by rw [mul_one]) h02 h12 h20 h21 h00 h11

theorem piU_xEU_mem_evenCU [Finite F] {u : ↥(muU hF)} (hu4 : u ^ 4 = 1) :
    piU p F (xEU hF u) ∈ evenCU hF := by
  have hm : (u, (1 : ↥(muU hF))) ∈ fourKU hF := by
    rw [fourKU, MonoidHom.mem_ker, powMonoidHom_apply, Prod.pow_def]
    exact Prod.ext hu4 (one_pow 4)
  exact ⟨xEU hF u, ⟨(u, 1), hm, rfl⟩, rfl⟩

theorem piU_xOU_mem_commutator [Finite F] {u : ↥(muU hF)} (hu4 : u ^ 4 = 1)
    {U : Subgroup (PSU3F p F)} (hE : evenCU hF ≤ U) (hUm : U ≤ monoCU hF)
    (hUD : ¬ U ≤ diagCU hF) : piU p F (xOU hF u) ∈ ⁅U, U⁆ := by
  obtain ⟨s, hsU, hsD⟩ := Set.not_subset.mp hUD
  obtain ⟨g, hgm, rfl⟩ := hUm hsU
  obtain ⟨h02, h12, h20, h21, ⟨h01, h10⟩ | ⟨h00, h11⟩⟩ := hgm
  · exact absurd ⟨g, ⟨h01, h02, h10, h12, h20, h21⟩, rfl⟩ hsD
  · have hx := xEU_mul_eq u h02 h12 h20 h21 h00 h11
    have h1 : xEU hF u * g * (xEU hF u)⁻¹ = xOU hF u * g := mul_inv_eq_iff_eq_mul.mpr hx
    have hc : xEU hF u * g * (xEU hF u)⁻¹ * g⁻¹ = xOU hF u := by
      rw [h1]
      simp
    have hmem := Subgroup.commutator_mem_commutator (hE (piU_xEU_mem_evenCU hu4)) hsU
    rw [commutatorElement_def] at hmem
    have e : piU p F (xEU hF u) * piU p F g * (piU p F (xEU hF u))⁻¹ * (piU p F g)⁻¹ =
        piU p F (xOU hF u) := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hc]
    rwa [e] at hmem

theorem commutator_le_diagCU [Finite F] {U : Subgroup (PSU3F p F)} (hUm : U ≤ monoCU hF) :
    ⁅U, U⁆ ≤ diagCU hF :=
  (Subgroup.commutator_mono hUm hUm).trans (commutator_monoCU_le_diagCU hF)

end CFSG.Quasithin.E2P.Asc80
