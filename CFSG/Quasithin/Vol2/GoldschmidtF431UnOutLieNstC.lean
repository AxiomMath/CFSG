module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNstB
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLift
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Perfect
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieCom
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieFld

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H13.F431
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem nst_commutator_Ssd_le {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)} :
    ⁅Ssd h B hB F, Ssd h B hB F⁆ ≤ Ssd h B hB ⊥ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hθ : miyamotoFieldFactor h ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (aut_comm h _ _)
  obtain ⟨s, hs⟩ := (miyamotoFieldFactor_eq_one_iff h _).1 hθ
  have hmem : ⁅a, b⁆ ∈ Ssd h B hB F := by
    rw [commutatorElement_def]
    exact (Ssd h B hB F).mul_mem ((Ssd h B hB F).mul_mem ((Ssd h B hB F).mul_mem ha hb)
      ((Ssd h B hB F).inv_mem ha)) ((Ssd h B hB F).inv_mem hb)
  have hsB : s ∈ B := by
    rw [hs] at hmem
    have hmem' : cj h s * fa h 1 ∈ Ssd h B hB F := by
      rw [fa_one, mul_one]
      exact hmem
    exact ((cj_mul_fa_mem_Ssd_iff h).1 hmem').1
  rw [hs]
  exact cj_mem_Ssd h hsB

theorem Ssd_bot_eq_map {B : Subgroup (Xg h)} {hB : FStab h B} :
    Ssd h B hB ⊥ = B.map (MulAut.conj : Xg h →* MulAut (Xg h)) := by
  ext α
  constructor
  · rintro ⟨s, hs, φ, hφ, rfl⟩
    rw [Subgroup.mem_bot] at hφ
    subst hφ
    exact ⟨s, hs, by rw [fa_one, mul_one]⟩
  · rintro ⟨s, hs, rfl⟩
    exact cj_mem_Ssd h hs

theorem I2X_le_normalizer_H : I2X h ≤ Subgroup.normalizer ((A2X h ⊔ N2X h : Subgroup (Xg h)) :
    Set (Xg h)) := by
  intro i hi
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
  have hA : (A2X h).map (↑(MulAut.conj i) : Xg h →* Xg h) = A2X h :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (I2X_le_Pt h hi)
  have hN : (N2X h).map (↑(MulAut.conj i) : Xg h →* Xg h) = N2X h := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      have : (MulAut.conj i) n = n := by
        have e : i * n = n * i := Subtype.ext (miyamotoI2_commute_N2 h hi hn)
        rw [MulAut.conj_apply, e]
        group
      rw [MonoidHom.coe_ofClass, this]
      exact hn
    · intro hy
      refine ⟨y, hy, ?_⟩
      have e : i * y = y * i := Subtype.ext (miyamotoI2_commute_N2 h hi hy)
      rw [MonoidHom.coe_ofClass, MulAut.conj_apply, e]
      group
  rw [hA, hN]

theorem Pt_eq_sup_I2X : Pt h = (A2X h ⊔ N2X h) ⊔ I2X h := by
  rw [Pt_eq, sup_comm (I2X h) (N2X h), ← sup_assoc]

theorem A2X_sup_N2X_perfect (hf : 2 ≤ f) :
    ⁅A2X h ⊔ N2X h, A2X h ⊔ N2X h⁆ = A2X h ⊔ N2X h := by
  have e := commutator_miyamotoA2G_sup_N2G h (⊤ : Subgroup (Xg h)) (etaX h) hf
  have h1 : A2X h = miyamotoA2G h ⊤ (etaX h) := sg_eq_pull h _
  have h3 : N2X h = miyamotoN2G h ⊤ (etaX h) := sg_eq_pull h _
  rw [h1, h3]
  exact e

theorem perfectCore_Pt (hf : 2 ≤ f) : perfectCore (Pt h) = A2X h ⊔ N2X h := by
  have hHP : A2X h ⊔ N2X h ≤ Pt h := sup_le (A2X_le_Pt h) (N2X_le_Pt h)
  have hc : ⁅Pt h, Pt h⁆ ≤ A2X h ⊔ N2X h := by
    rw [Pt_eq_sup_I2X]
    refine commutator_sup_le_of_comm (I2X_le_normalizer_H h) fun x hx y hy => ?_
    exact Subtype.ext (miyamotoI2_commute' h hx hy)
  rw [perfectCore_eq_of_commutator_le hHP hc]
  exact perfectCore_eq_self_of_perfect (A2X_sup_N2X_perfect h hf)

theorem centerOf_perfectCore_Ssd_Pt (hf : 2 ≤ f) (F : Subgroup (K ≃+* K)) :
    centerOf (perfectCore (Ssd h (Pt h) (fStab_Pt h) F)) = Ssd h (ZX h) (fStab_ZX h) ⊥ := by
  have hle : Ssd h (Pt h) (fStab_Pt h) ⊥ ≤ Ssd h (Pt h) (fStab_Pt h) F :=
    Ssd_mono h le_rfl bot_le
  rw [perfectCore_eq_of_commutator_le hle (nst_commutator_Ssd_le h), Ssd_bot_eq_map,
    perfectCore_map_of_injective _ (conj_hom_injective h), perfectCore_Pt h hf,
    centerOf_map_of_injective _ (conj_hom_injective h), centerOf_A2X_sup_N2X h hf,
    Ssd_bot_eq_map]

end CFSG.Quasithin.H13.F431.Un.OL
