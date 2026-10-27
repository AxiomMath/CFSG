module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpAbs
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieBar

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

@[expose] def wcl_xe (a b c d : K) (hm : miyamotoXGL h a b c d ∈ miyamotoP h) : Xg h :=
  ⟨miyamotoXGL h a b c d, miyamotoUnipotent_le_SU h false false hm⟩

theorem wcl_coe_xe (a b c d : K) (hm : miyamotoXGL h a b c d ∈ miyamotoP h) :
    ((wcl_xe h a b c d hm : Xg h) : GL (Fin 4) K) = miyamotoXGL h a b c d := rfl

theorem wcl_xe_mem_Psy (a b c d : K) (hm : miyamotoXGL h a b c d ∈ miyamotoP h) :
    wcl_xe h a b c d hm ∈ Psy h := hm

theorem wcl_fbar_xe (a b c d : K) (hm : miyamotoXGL h a b c d ∈ miyamotoP h) (ha : h.bar a = a)
    (hb : h.bar b = b) (hc : h.bar c = c) (hd : h.bar d = d) :
    fbar h (wcl_xe h a b c d hm) = wcl_xe h a b c d hm := by
  apply Subtype.ext
  rw [coe_miyamotoFieldAut_apply, wcl_coe_xe, glAut_miyamotoXGL]
  simp only [miyamotoBarEquiv_apply, ha, hb, hc, hd]

theorem wcl_xe_mem_Pfx (a b c d : K) (hm : miyamotoXGL h a b c d ∈ miyamotoP h)
    (ha : h.bar a = a) (hb : h.bar b = b) (hc : h.bar c = c) (hd : h.bar d = d) :
    wcl_xe h a b c d hm ∈ Pfx h :=
  ⟨wcl_xe_mem_Psy h a b c d hm, wcl_fbar_xe h a b c d hm ha hb hc hd⟩

theorem wcl_mem_P_of_bar (a b c d : K) (ha : h.bar a = a) (hb : h.bar b = b)
    (hc : h.bar c = c) (hd : h.bar d = d) : miyamotoXGL h a b c d ∈ miyamotoP h := by
  rw [miyamotoXGL_mem_P]
  refine ⟨hb, ?_⟩
  rw [ha, hc, hd]
  linear_combination (d + a * c) * CharTwo.two_eq_zero (R := K)

theorem wcl_comm_z1X {u : Xg h} (hu : u ∈ Psy h) : u * z1X h = z1X h * u := by
  have hz : (z1X h : GL (Fin 4) K) ∈ CFSG.centerIn (miyamotoP h) := by
    rw [centerIn_miyamotoP]
    exact z1X_mem_ZX h
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (u : GL (Fin 4) K) hu)

theorem wcl_z1X_mem_Pfx : z1X h ∈ Pfx h := ⟨z1X_mem_Psy h, fa_z1X h _⟩

theorem wcl_cj_z1X_mem_center (F₂ : Subgroup (K ≃+* K)) :
    cj h (z1X h) ∈ centerOf (spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h)) := by
  rw [mem_centerOf_iff, spTf_Ssd]
  refine ⟨cj_mem_Ssd h (wcl_z1X_mem_Pfx h), fun t ht => ?_⟩
  obtain ⟨u, hu, φ, -, rfl⟩ := ht
  have e1 : fa h φ * cj h (z1X h) = cj h (z1X h) * fa h φ := by
    have := fa_mul_cj_mul_inv h φ (z1X h)
    rw [fa_z1X] at this
    calc fa h φ * cj h (z1X h) = (fa h φ * cj h (z1X h) * (fa h φ)⁻¹) * fa h φ := by group
      _ = cj h (z1X h) * fa h φ := by rw [this]
  rw [mul_assoc, e1, ← mul_assoc, ← mul_assoc, ← cj_mul, ← cj_mul, wcl_comm_z1X h hu.1]

theorem wcl_exists_lambda (hf : 2 ≤ f) : ∃ l : K, h.bar l = l ∧ l ≠ 0 ∧ l ≠ 1 := by
  have := h.finite
  by_contra hno
  push Not at hno
  have hsub : {d : K | h.bar d = d} ⊆ ({0, 1} : Set K) := fun d hd => by
    by_cases h0 : d = 0
    · exact Or.inl h0
    · exact Or.inr (hno d hd h0)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [ncard_fixed h, Set.ncard_pair zero_ne_one] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem wcl_commutator_z1 {l : K} (hl : h.bar l = l) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    ∃ u₁ ∈ Pfx h, ∃ u₂ ∈ Pfx h, ⁅u₁, u₂⁆ = z1X h := by
  have hne : l + l ^ 2 ≠ 0 := by
    have h1l : 1 + l ≠ 0 := fun e => hl1 (by linear_combination e - CharTwo.two_eq_zero (R := K))
    have : l + l ^ 2 = l * (1 + l) := by ring
    rw [this]
    exact mul_ne_zero hl0 h1l
  set s : K := (l + l ^ 2)⁻¹ with hs
  have hbs : h.bar s = s := by rw [hs, map_inv₀, map_add, map_pow, hl]
  have hsl : s * (l + l ^ 2) = 1 := inv_mul_cancel₀ hne
  have hb1 : h.bar (1 : K) = 1 := map_one _
  have hb0 : h.bar (0 : K) = 0 := map_zero _
  have hbls : h.bar (l * s) = l * s := by rw [map_mul, hl, hbs]
  have hP1 := wcl_mem_P_of_bar h 1 s 0 0 hb1 hbs hb0 hb0
  have hP2 := wcl_mem_P_of_bar h l (l * s) 0 0 hl hbls hb0 hb0
  refine ⟨wcl_xe h 1 s 0 0 hP1, wcl_xe_mem_Pfx h _ _ _ _ hP1 hb1 hbs hb0 hb0,
    wcl_xe h l (l * s) 0 0 hP2, wcl_xe_mem_Pfx h _ _ _ _ hP2 hl hbls hb0 hb0, ?_⟩
  apply Subtype.ext
  have hc := miyamotoXGL_commutator h hbs hbls (a := 1) (c := 0) (d := 0) (a' := l) (c' := 0)
    (d' := 0)
  have e : ((⁅wcl_xe h 1 s 0 0 hP1, wcl_xe h l (l * s) 0 0 hP2⁆ : Xg h) : GL (Fin 4) K) =
      ⁅miyamotoXGL h 1 s 0 0, miyamotoXGL h l (l * s) 0 0⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, wcl_coe_xe]
  rw [e, hc, coe_z1X, miyamotoXGL_inj]
  simp only [hb1, hb0, hl, mul_zero, add_zero, zero_add, one_mul, mul_one]
  refine ⟨trivial, trivial, ?_, ?_⟩
  · linear_combination (s * l) * CharTwo.two_eq_zero (R := K)
  · linear_combination hsl + (l * (s + l * s)) * CharTwo.two_eq_zero (R := K)

theorem W_ne (hf : 2 ≤ f) (F₂ : Subgroup (K ≃+* K)) :
    cj h (z1X h) ∈ spWf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h) := by
  obtain ⟨l, hl, hl0, hl1⟩ := wcl_exists_lambda h hf
  obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := wcl_commutator_z1 h hl hl0 hl1
  refine ⟨wcl_cj_z1X_mem_center h F₂, ?_⟩
  rw [spTf_Ssd]
  have hcj : cj h ⁅u₁, u₂⁆ = ⁅cj h u₁, cj h u₂⁆ :=
    map_commutatorElement (MulAut.conj : Xg h →* MulAut (Xg h)) u₁ u₂
  rw [← hu, hcj]
  exact Subgroup.commutator_mem_commutator (cj_mem_Ssd h hu₁) (cj_mem_Ssd h hu₂)

end CFSG.Quasithin.H13.F431.Un.OL
