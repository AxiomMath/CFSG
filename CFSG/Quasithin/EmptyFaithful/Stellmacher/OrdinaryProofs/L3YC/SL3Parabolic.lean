module

public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.GL3TwoOrder
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

open CFSG.Open
open scoped Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) (ZMod 2)

def vPt : Fin 3 → ZMod 2 := Pi.single 0 1

def vPl : Fin 3 → ZMod 2 := Pi.single 2 1

def stabPoint : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | (g : Mat3) *ᵥ vPt = vPt}
  mul_mem' {g h} hg hh := by
    show ((g * h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ vPt = vPt
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have hh' : (h : Mat3) *ᵥ vPt = vPt := hh
    have hg' : (g : Mat3) *ᵥ vPt = vPt := hg
    rw [hh', hg']
  one_mem' := by
    show ((1 : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ vPt = vPt
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {g} hg := by
    show ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ vPt = vPt
    have hg' : (g : Mat3) *ᵥ vPt = vPt := hg
    calc ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ vPt
        = ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ ((g : Mat3) *ᵥ vPt) := by rw [hg']
      _ = (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) * (g : Mat3)) *ᵥ vPt := by
          rw [Matrix.mulVec_mulVec]
      _ = vPt := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

def stabPlane : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | Matrix.vecMul vPl (g : Mat3) = vPl}
  mul_mem' {g h} hg hh := by
    show Matrix.vecMul vPl ((g * h : GL (Fin 3) (ZMod 2)) : Mat3) = vPl
    have hg' : Matrix.vecMul vPl (g : Mat3) = vPl := hg
    have hh' : Matrix.vecMul vPl (h : Mat3) = vPl := hh
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, hg', hh']
  one_mem' := by
    show Matrix.vecMul vPl ((1 : GL (Fin 3) (ZMod 2)) : Mat3) = vPl
    rw [Units.val_one, Matrix.vecMul_one]
  inv_mem' {g} hg := by
    show Matrix.vecMul vPl ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) = vPl
    have hg' : Matrix.vecMul vPl (g : Mat3) = vPl := hg
    calc Matrix.vecMul vPl ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3)
        = Matrix.vecMul (Matrix.vecMul vPl (g : Mat3)) ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) := by
          rw [hg']
      _ = Matrix.vecMul vPl ((g : Mat3) * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3)) := by
          rw [Matrix.vecMul_vecMul]
      _ = vPl := by rw [Units.mul_inv, Matrix.vecMul_one]

def U8 : Finset Mat3 :=
  Finset.univ.filter fun M : Mat3 =>
    M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 2 2 = 1

lemma U8_mul : ∀ A ∈ U8, ∀ B ∈ U8, A * B ∈ U8 := by
  decide +kernel

lemma U8_inv : ∀ A ∈ U8, ∃ B ∈ U8, A * B = 1 := by
  decide +kernel

def U3 : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := {g | (g : Mat3) ∈ U8}
  mul_mem' {g h} hg hh := by
    show ((g * h : GL (Fin 3) (ZMod 2)) : Mat3) ∈ U8
    have hg' : (g : Mat3) ∈ U8 := hg
    have hh' : (h : Mat3) ∈ U8 := hh
    rw [Units.val_mul]
    exact U8_mul _ hg' _ hh'
  one_mem' := by
    show ((1 : GL (Fin 3) (ZMod 2)) : Mat3) ∈ U8
    rw [Units.val_one]
    decide +kernel
  inv_mem' {g} hg := by
    show ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) ∈ U8
    have hg' : (g : Mat3) ∈ U8 := hg
    obtain ⟨B, hB, hAB⟩ := U8_inv _ hg'
    have hinv : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) = B := by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_eq_right_inv hAB
    rw [hinv]
    exact hB

lemma det_ne_zero_of_unit (g : GL (Fin 3) (ZMod 2)) : (g : Mat3).det ≠ 0 := by
  intro h0
  have h : (g : Mat3).det * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [h0, zero_mul] at h
  exact zero_ne_one h

lemma mem_U8_of_stab (M : Mat3) (hdet : M.det ≠ 0) (hpt : M *ᵥ vPt = vPt)
    (hpl : Matrix.vecMul vPl M = vPl) : M ∈ U8 := by
  revert M
  decide +kernel

lemma U8_stab : ∀ M ∈ U8, M *ᵥ vPt = vPt ∧ Matrix.vecMul vPl M = vPl := by
  decide +kernel

theorem U3_le_stabs : U3 ≤ stabPoint ∧ U3 ≤ stabPlane := by
  constructor
  · intro g hg
    have hg' : (g : Mat3) ∈ U8 := hg
    exact (U8_stab _ hg').1
  · intro g hg
    have hg' : (g : Mat3) ∈ U8 := hg
    exact (U8_stab _ hg').2

def ptSet : Finset Mat3 :=
  Finset.univ.filter fun M : Mat3 => M.det ≠ 0 ∧ M *ᵥ vPt = vPt

def plSet : Finset Mat3 :=
  Finset.univ.filter fun M : Mat3 => M.det ≠ 0 ∧ Matrix.vecMul vPl M = vPl

lemma natCard_eq_card_of (H : Subgroup (GL (Fin 3) (ZMod 2))) (S : Finset Mat3)
    (h1 : ∀ g ∈ H, (g : Mat3) ∈ S) (h2 : ∀ M ∈ S, ∃ g ∈ H, (g : Mat3) = M) :
    Nat.card H = S.card := by
  have hinj : Function.Injective (fun g : H => ((g : GL (Fin 3) (ZMod 2)) : Mat3)) := by
    intro a b hab
    exact Subtype.ext (Units.ext hab)
  have hr : Set.range (fun g : H => ((g : GL (Fin 3) (ZMod 2)) : Mat3)) = (S : Set Mat3) := by
    ext M
    constructor
    · rintro ⟨g, rfl⟩
      exact h1 _ g.2
    · intro hM
      obtain ⟨g, hg, rfl⟩ := h2 M hM
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [← Nat.card_range_of_injective hinj, hr, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem card_stabPoint : Nat.card stabPoint = 24 := by
  rw [natCard_eq_card_of stabPoint ptSet]
  · decide +kernel
  · intro g hg
    have hg' : (g : Mat3) *ᵥ vPt = vPt := hg
    simp only [ptSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨det_ne_zero_of_unit g, hg'⟩
  · intro M hM
    simp only [ptSet, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM.1, hM.2, rfl⟩

theorem card_stabPlane : Nat.card stabPlane = 24 := by
  rw [natCard_eq_card_of stabPlane plSet]
  · decide +kernel
  · intro g hg
    have hg' : Matrix.vecMul vPl (g : Mat3) = vPl := hg
    simp only [plSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨det_ne_zero_of_unit g, hg'⟩
  · intro M hM
    simp only [plSet, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM.1, hM.2, rfl⟩

theorem card_U3 : Nat.card U3 = 8 := by
  rw [natCard_eq_card_of U3 U8]
  · decide +kernel
  · intro g hg
    exact hg
  · intro M hM
    have hdet : ∀ A ∈ U8, A.det ≠ 0 := by decide +kernel
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (hdet M hM), hM, rfl⟩

theorem stabPoint_inf_stabPlane : stabPoint ⊓ stabPlane = U3 := by
  ext g
  constructor
  · rintro ⟨hp, hq⟩
    have hp' : (g : Mat3) *ᵥ vPt = vPt := hp
    have hq' : Matrix.vecMul vPl (g : Mat3) = vPl := hq
    have hU : (g : Mat3) ∈ U8 := mem_U8_of_stab _ (det_ne_zero_of_unit g) hp' hq'
    exact hU
  · intro hg
    have hg' : (g : Mat3) ∈ U8 := hg
    obtain ⟨hp, hq⟩ := U8_stab _ hg'
    exact ⟨hp, hq⟩

lemma U8_det : ∀ A ∈ U8, A.det ≠ 0 := by
  decide +kernel

def Jw : Mat3 := Matrix.of ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]

abbrev BigCell (N : Mat3) : Prop :=
  N 2 0 ≠ 0 ∧ N 1 0 * N 2 1 - N 1 1 * N 2 0 ≠ 0

lemma bigCell_U8 : ∀ N : Mat3, N.det ≠ 0 → BigCell N →
    ∃ a ∈ U8, ∃ b ∈ U8, a * N * b = Jw := by
  decide +kernel

lemma outside_witness : ∀ N : Mat3, N.det ≠ 0 → ¬ (N *ᵥ vPt = vPt) →
    ¬ (Matrix.vecMul vPl N = vPl) → ∃ u ∈ U8, BigCell (N * u * N) := by
  decide +kernel

def bigOrbit : Finset Mat3 := (U8 ×ˢ U8).image fun p => p.1 * Jw * p.2

lemma bigOrbit_card : bigOrbit.card = 64 := by
  decide +kernel

lemma card_le_natCard_of (H : Subgroup (GL (Fin 3) (ZMod 2))) (S : Finset Mat3)
    (h : ∀ M ∈ S, ∃ g ∈ H, (g : Mat3) = M) : S.card ≤ Nat.card H := by
  have hinj : Function.Injective (fun g : H => ((g : GL (Fin 3) (ZMod 2)) : Mat3)) := by
    intro a b hab
    exact Subtype.ext (Units.ext hab)
  have hsub : (S : Set Mat3) ⊆ Set.range (fun g : H => ((g : GL (Fin 3) (ZMod 2)) : Mat3)) := by
    intro M hM
    obtain ⟨g, hg, rfl⟩ := h M (Finset.mem_coe.mp hM)
    exact ⟨⟨g, hg⟩, rfl⟩
  rw [← Nat.card_range_of_injective hinj, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.finite_range _)

lemma card_ge_of_big (P : Subgroup (GL (Fin 3) (ZMod 2))) (hU : U3 ≤ P)
    (y : GL (Fin 3) (ZMod 2)) (hy : y ∈ P) (hb : BigCell (y : Mat3)) : 64 ≤ Nat.card P := by
  obtain ⟨a, ha, b, hb', hab⟩ := bigCell_U8 _ (det_ne_zero_of_unit y) hb
  have hgA : Matrix.GeneralLinearGroup.mkOfDetNeZero a (U8_det a ha) ∈ U3 := ha
  have hgB : Matrix.GeneralLinearGroup.mkOfDetNeZero b (U8_det b hb') ∈ U3 := hb'
  set gJ : GL (Fin 3) (ZMod 2) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero a (U8_det a ha) * y *
      Matrix.GeneralLinearGroup.mkOfDetNeZero b (U8_det b hb') with hgJdef
  have hgJ : gJ ∈ P := P.mul_mem (P.mul_mem (hU hgA) hy) (hU hgB)
  have hgJc : (gJ : Mat3) = Jw := by
    rw [hgJdef, Units.val_mul, Units.val_mul]
    exact hab
  have hle : bigOrbit.card ≤ Nat.card P := by
    apply card_le_natCard_of P bigOrbit
    intro M hM
    unfold bigOrbit at hM
    rw [Finset.mem_image] at hM
    obtain ⟨⟨a', b'⟩, hp, rfl⟩ := hM
    rw [Finset.mem_product] at hp
    have hA' : Matrix.GeneralLinearGroup.mkOfDetNeZero a' (U8_det a' hp.1) ∈ U3 := hp.1
    have hB' : Matrix.GeneralLinearGroup.mkOfDetNeZero b' (U8_det b' hp.2) ∈ U3 := hp.2
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a' (U8_det a' hp.1) * gJ *
      Matrix.GeneralLinearGroup.mkOfDetNeZero b' (U8_det b' hp.2), ?_, ?_⟩
    · exact P.mul_mem (P.mul_mem (hU hA') hgJ) (hU hB')
    · rw [Units.val_mul, Units.val_mul, hgJc]
      rfl
  rw [bigOrbit_card] at hle
  exact hle

lemma top_of_card (P : Subgroup (GL (Fin 3) (ZMod 2))) (hU : U3 ≤ P) (h64 : 64 ≤ Nat.card P) :
    P = ⊤ := by
  have h8 : 8 ∣ Nat.card P := by
    have := Subgroup.card_dvd_of_le hU
    rwa [card_U3] at this
  have hd : Nat.card P ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card P
    rwa [card_GL_three_two] at this
  have hn : Nat.card P = 168 := by
    have hle := Nat.le_of_dvd (by norm_num) hd
    generalize Nat.card P = n at h8 hd hle h64 ⊢
    interval_cases n <;> omega
  exact Subgroup.eq_top_of_card_eq P (by rw [hn, card_GL_three_two])

lemma top_of_outside (P : Subgroup (GL (Fin 3) (ZMod 2))) (hU : U3 ≤ P) (g : GL (Fin 3) (ZMod 2))
    (hg : g ∈ P) (hn : ¬ (g ∈ stabPoint ∨ g ∈ stabPlane)) : P = ⊤ := by
  have n1 : ¬ ((g : Mat3) *ᵥ vPt = vPt) := fun h1 => hn (Or.inl h1)
  have n2 : ¬ (Matrix.vecMul vPl (g : Mat3) = vPl) := fun h1 => hn (Or.inr h1)
  obtain ⟨u, hu, hbig⟩ := outside_witness (g : Mat3) (det_ne_zero_of_unit g) n1 n2
  have hgu : Matrix.GeneralLinearGroup.mkOfDetNeZero u (U8_det u hu) ∈ U3 := hu
  have hy : g * Matrix.GeneralLinearGroup.mkOfDetNeZero u (U8_det u hu) * g ∈ P :=
    P.mul_mem (P.mul_mem hg (hU hgu)) hg
  have hycoe : ((g * Matrix.GeneralLinearGroup.mkOfDetNeZero u (U8_det u hu) * g :
      GL (Fin 3) (ZMod 2)) : Mat3) = (g : Mat3) * u * (g : Mat3) := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  have hb : BigCell ((g * Matrix.GeneralLinearGroup.mkOfDetNeZero u (U8_det u hu) * g :
      GL (Fin 3) (ZMod 2)) : Mat3) := by
    rw [hycoe]
    exact hbig
  exact top_of_card P hU (card_ge_of_big P hU _ hy hb)

lemma le_of_le_union (P A B : Subgroup (GL (Fin 3) (ZMod 2)))
    (h : ∀ g ∈ P, g ∈ A ∨ g ∈ B) : P ≤ A ∨ P ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨a, ha, haA⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨b, hb, hbB⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  have haB : a ∈ B := (h a ha).resolve_left haA
  have hbA : b ∈ A := (h b hb).resolve_right hbB
  rcases h (a * b) (P.mul_mem ha hb) with hab | hab
  · apply haA
    have := A.mul_mem hab (A.inv_mem hbA)
    simpa using this
  · apply hbB
    have := B.mul_mem (B.inv_mem haB) hab
    simpa using this

lemma eight_or_24 (n : ℕ) (h8 : 8 ∣ n) (hd : n ∣ 24) : n = 8 ∨ n = 24 := by
  have hle := Nat.le_of_dvd (by norm_num) hd
  interval_cases n <;> omega

theorem overgroups_U3 (P : Subgroup (GL (Fin 3) (ZMod 2))) (h : U3 ≤ P) :
    P = U3 ∨ P = stabPoint ∨ P = stabPlane ∨ P = ⊤ := by
  by_cases htop : P = ⊤
  · exact Or.inr (Or.inr (Or.inr htop))
  have hsub : ∀ g ∈ P, g ∈ stabPoint ∨ g ∈ stabPlane := by
    intro g hg
    by_contra hn
    exact htop (top_of_outside P h g hg hn)
  have h8 : 8 ∣ Nat.card P := by
    have := Subgroup.card_dvd_of_le h
    rwa [card_U3] at this
  rcases le_of_le_union P stabPoint stabPlane hsub with hle | hle
  · have hd : Nat.card P ∣ 24 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [card_stabPoint] at this
    rcases eight_or_24 _ h8 hd with hc | hc
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (le_of_eq (by rw [hc, card_U3]))).symm
    · exact Or.inr (Or.inl (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_stabPoint, hc]))))
  · have hd : Nat.card P ∣ 24 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [card_stabPlane] at this
    rcases eight_or_24 _ h8 hd with hc | hc
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (le_of_eq (by rw [hc, card_U3]))).symm
    · exact Or.inr (Or.inr (Or.inl
        (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_stabPlane, hc])))))

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

end
