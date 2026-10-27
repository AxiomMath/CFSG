module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2F48Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelGen
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigSwapMain
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigCent

public section

namespace CFSG.Quasithin.H13.F431.G2.F48

open CFSG.Blueprint CFSG.GH74.GLS.Stage4.Hex CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.BN CFSG.Quasithin.H13.F431.F48Rig CFSG.Quasithin.H13.F48Rig


set_option linter.unusedSectionVars false

theorem cartanFPF_or_swap_g2 (f : ℕ) (hm : F431ModelFacts .G2 0 f) (D : Type) [Group D]
    (hD : LieModel D .G2 0 2 f) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .G2) (three_le_polyNumber .G2)).CartanFPF ∨
      (A.swap.setting (hm D hD).1 (polyNumber .G2) (three_le_polyNumber .G2)).CartanFPF := by
  obtain ⟨hf, K, hF, hFin, hcp, h3, hK, ⟨e⟩⟩ := g2_quot_data hD
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := isSimpleGroup_adjointQuotient h3
  have hU := isSylowTwoOf_modelU h3
  have hcen : Subgroup.center D = ⊥ := (hm D hD).2
  obtain ⟨e', -, hP | hP⟩ := exists_iso_of_yam (g2ModelSystem K h3) hU e A
  · have hgen := range_conj_le_of_rankTwo (g2ModelSystem K h3) hU e A
    exact Or.inl (cartanFPF_g2Model h3 hU (hm D hD).1 A h4
      (xdatum_of_labelling (g2ModelSystem K h3) hU (hm D hD).1 (by norm_num) e' A hcen hgen true
        hP.1 hP.2))
  · have hgen := range_conj_le_of_rankTwo (g2ModelSystem K h3) hU e A.swap
    exact Or.inr (cartanFPF_g2Model h3 hU (hm D hD).1 A.swap h4
      (xdatum_of_labelling (g2ModelSystem K h3) hU (hm D hD).1 (by norm_num) e' A.swap hcen hgen
        true hP.2 hP.1))

theorem faithfulOnType_g2 (f : ℕ) (hm : F431ModelFacts .G2 0 f) (D : Type) [Group D]
    (hD : LieModel D .G2 0 2 f) (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .G2) (three_le_polyNumber .G2)).FaithfulOnType s := by
  obtain ⟨-, K, hF, hFin, hcp, h3, -, ⟨e⟩⟩ := g2_quot_data hD
  have := isSimpleGroup_adjointQuotient h3
  have hU := isSylowTwoOf_modelU h3
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (g2ModelSystem K h3) hU (hm D hD).1 (by norm_num) e A
  exact faithfulOnType_g2Model h3 hU (hm D hD).1 A b XD
    (fun k hk => centralizer_inn_trivial A (hm D hD).1 6 (by norm_num) (hm D hD).2 hgen e'.symm
      k hk) s

theorem f431F48_g2 (f : ℕ) (hm : F431ModelFacts .G2 0 f) : F431F48 .G2 0 f hm :=
  f431F48_of_model_swap hm (f431Facts45_g2 f hm) (f431Generation_g2 f)
    (fun D _ hD A => cartanFPF_or_swap_g2 f hm D hD A)
    (fun D _ hD A => faithfulOnType_g2 f hm D hD A _)

end CFSG.Quasithin.H13.F431.G2.F48
