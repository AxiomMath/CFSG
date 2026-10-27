module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartDefs
public import CFSG.LinearAlgebra.LinearGroups.SubspaceSpecialLinear
import CFSG.LinearAlgebra.LinearGroups.ScalarSubspaceSpecialLinear
import CFSG.LinearAlgebra.SpecialLinearBlockJoin
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.StandardType.N2Chart

open Matrix

theorem map_stabSub_toLin'_eq {P E : Submodule F4 V6} (hc : IsCompl E P) :
    (stabSub P E).map Matrix.SpecialLinearGroup.toLin' =
      (Submodule.specialLinearEmbedding E P hc).range := by
  let theta : SL6 →* (V6 ≃ₗ[F4] V6) := Matrix.SpecialLinearGroup.toLin'
  let beta := Submodule.specialLinearEmbedding E P hc
  apply le_antisymm
  · rintro f ⟨g, hg, rfl⟩
    apply Submodule.mem_range_specialLinearEmbedding_of_det_eq_one hc
    · rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.det_toLin',
        Matrix.SpecialLinearGroup.det_coe]
    · exact hg.1
    · exact hg.2.1
    · intro v hv
      have hinv : (theta g).symm = theta (g⁻¹) := (map_inv theta g).symm
      rw [hinv]
      exact hg.2.2 v hv
  · rintro f ⟨g, rfl⟩
    let fSL : _root_.SpecialLinearGroup F4 V6 := ⟨beta g, by
      apply Units.ext
      simpa only [LinearEquiv.coe_det, Units.val_one] using
        Submodule.det_specialLinearEmbedding hc g⟩
    let z : SL6 := Matrix.SpecialLinearGroup.toLin'_equiv.symm fSL
    have hz : theta z = beta g := by
      change (Matrix.SpecialLinearGroup.toLin'_equiv
        (Matrix.SpecialLinearGroup.toLin'_equiv.symm fSL)).val = beta g
      rw [MulEquiv.apply_symm_apply]
    refine ⟨z, ?_, hz⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      change theta z v = v
      rw [hz]
      exact Submodule.specialLinearEmbedding_apply_right hc g ⟨v, hv⟩
    · intro v hv
      change theta z v ∈ E
      rw [hz]
      change beta g ((⟨v, hv⟩ : E) : V6) ∈ E
      rw [Submodule.specialLinearEmbedding_apply_left]
      exact (g ⟨v, hv⟩).property
    · intro v hv
      change theta (z⁻¹) v ∈ E
      rw [map_inv, hz, ← map_inv beta]
      change beta (g⁻¹) ((⟨v, hv⟩ : E) : V6) ∈ E
      rw [Submodule.specialLinearEmbedding_apply_left]
      exact (g⁻¹ ⟨v, hv⟩).property

theorem exists_scalar_mem_stabSub {P E : Submodule F4 V6} (hc : IsCompl E P)
    (a : F4) (ha0 : a ≠ 0) (hpow : a ^ Module.finrank F4 E = 1) :
    ∃ z ∈ stabSub P E,
      (∀ v ∈ E, (z : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = a • v) ∧
      (∀ v ∈ P, (z : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v) ∧
      ∀ t ∈ stabSub P E, Commute z t := by
  let theta : SL6 →* (V6 ≃ₗ[F4] V6) := Matrix.SpecialLinearGroup.toLin'
  obtain ⟨f, hf, hfE, hfP, hfc⟩ :=
    Submodule.exists_scalar_mem_specialLinearEmbedding hc a ha0 hpow
  have hfm : f ∈ (stabSub P E).map theta := by
    rw [map_stabSub_toLin'_eq hc]
    exact hf
  obtain ⟨z, hz, hzf⟩ := hfm
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · intro v hv
    change theta z v = a • v
    rw [hzf]
    exact hfE v hv
  · intro v hv
    change theta z v = v
    rw [hzf]
    exact hfP v hv
  · intro t ht
    have htm : theta t ∈ (Submodule.specialLinearEmbedding E P hc).range := by
      rw [← map_stabSub_toLin'_eq hc]
      exact ⟨t, ht, rfl⟩
    change z * t = t * z
    apply Matrix.SpecialLinearGroup.toLin'_injective
    change theta (z * t) = theta (t * z)
    rw [map_mul, map_mul, hzf]
    exact (hfc (theta t) htm).eq

theorem normalizer_stabSub_preserves_complements {P E : Submodule F4 V6}
    (hc : IsCompl E P) (a : F4) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hpow : a ^ Module.finrank F4 E = 1) {g : SL6}
    (hg : g ∈ Subgroup.normalizer (stabSub P E : Set SL6)) :
    (∀ v ∈ E, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ E) ∧
      (∀ v ∈ P, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ P) := by
  let theta : SL6 →* (V6 ≃ₗ[F4] V6) := Matrix.SpecialLinearGroup.toLin'
  have hm := Subgroup.le_normalizer_map theta (show theta g ∈
      (Subgroup.normalizer (stabSub P E : Set SL6)).map theta from ⟨g, hg, rfl⟩)
  rw [map_stabSub_toLin'_eq hc] at hm
  exact Submodule.normalizer_specialLinearEmbedding_preserves_complements
    hc a ha0 ha1 hpow hm

private theorem isCompl_of_sup_eq_top_of_finrank_add_le
    {U W : Submodule F4 V6} (hsup : U ⊔ W = ⊤)
    (hbound : Module.finrank F4 U + Module.finrank F4 W ≤ 6) : IsCompl U W := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hsup] at hd
  have htopdim : Module.finrank F4 (⊤ : Submodule F4 V6) = 6 := by simp
  rw [htopdim] at hd
  have hzero : Module.finrank F4 ↥(U ⊓ W) = 0 := by omega
  exact isCompl_iff.mpr ⟨disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hzero),
    codisjoint_iff.mpr hsup⟩

private theorem mem_right_of_mem_sup_of_disjoint
    {C W U D : Submodule F4 V6} (hCW : Disjoint C W)
    (hUC : U ≤ C) (hDW : D ≤ W) {v : V6} (hv : v ∈ U ⊔ D) (hvW : v ∈ W) : v ∈ D := by
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
  have huW : u ∈ W := by
    simpa only [add_sub_cancel_right] using W.sub_mem hvW (hDW hd)
  have hu0 : u = 0 := by
    have him : u ∈ C ⊓ W := ⟨hUC hu, huW⟩
    simpa only [hCW.eq_bot, Submodule.mem_bot] using him
  simpa only [hu0, zero_add] using hd

theorem line_pair_eq_or_eq_swap_of_center_normalizes
    (A B a a' b b' : Submodule F4 V6)
    (hA : Module.finrank F4 A = 2) (hB : Module.finrank F4 B = 2)
    (ha : Module.finrank F4 a = 1) (ha' : Module.finrank F4 a' = 1)
    (hb : Module.finrank F4 b = 1) (hb' : Module.finrank F4 b' = 1)
    (htop : A ⊔ B ⊔ a ⊔ a' = ⊤) (hbW : b ≤ a ⊔ a') (hb'W : b' ≤ a ⊔ a')
    (hbb' : Disjoint b b')
    (hnorm : ∀ z ∈ stabSub (B ⊔ a') (A ⊔ a),
      (∀ h ∈ stabSub (B ⊔ a') (A ⊔ a), Commute z h) →
      ∀ g ∈ stabSub (A ⊔ b') (B ⊔ b), z * g * z⁻¹ ∈ stabSub (A ⊔ b') (B ⊔ b)) :
    (b = a ∧ b' = a') ∨ (b = a' ∧ b' = a) := by
  have hCbound : Module.finrank F4 ↥(A ⊔ B) ≤ 4 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hA, hB] at hd
    omega
  have hWbound : Module.finrank F4 ↥(a ⊔ a') ≤ 2 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq a a'
    rw [ha, ha'] at hd
    omega
  have hCWtop : (A ⊔ B) ⊔ (a ⊔ a') = ⊤ := by
    calc
      (A ⊔ B) ⊔ (a ⊔ a') = A ⊔ B ⊔ a ⊔ a' := by ac_rfl
      _ = ⊤ := htop
  have hCW := isCompl_of_sup_eq_top_of_finrank_add_le hCWtop (by omega)
  have hWdim : Module.finrank F4 ↥(a ⊔ a') = 2 := by
    have hd := Submodule.finrank_add_eq_of_isCompl hCW
    have hdim : Module.finrank F4 V6 = 6 := by simp
    omega
  have haa' : Disjoint a a' := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq a a'
    rw [hWdim, ha, ha'] at hd
    have hzero : Module.finrank F4 ↥(a ⊓ a') = 0 := by omega
    exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hzero)
  have hbbdim : Module.finrank F4 ↥(b ⊔ b') = 2 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq b b'
    rw [hbb'.eq_bot] at hd
    simpa [hb, hb'] using hd
  have hbbW : b ⊔ b' = a ⊔ a' :=
    Submodule.eq_of_le_of_finrank_eq (sup_le hbW hb'W) (hbbdim.trans hWdim.symm)
  have hE2bound : Module.finrank F4 ↥(A ⊔ a) ≤ 3 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq A a
    rw [hA, ha] at hd
    omega
  have hP2bound : Module.finrank F4 ↥(B ⊔ a') ≤ 3 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq B a'
    rw [hB, ha'] at hd
    omega
  have hE2P2top : (A ⊔ a) ⊔ (B ⊔ a') = ⊤ := by
    calc
      (A ⊔ a) ⊔ (B ⊔ a') = A ⊔ B ⊔ a ⊔ a' := by ac_rfl
      _ = ⊤ := htop
  have hc2 := isCompl_of_sup_eq_top_of_finrank_add_le hE2P2top (by omega)
  have hE2dim : Module.finrank F4 ↥(A ⊔ a) = 3 := by
    have hd := Submodule.finrank_add_eq_of_isCompl hc2
    have hdim : Module.finrank F4 V6 = 6 := by simp
    omega
  have hE1bound : Module.finrank F4 ↥(B ⊔ b) ≤ 3 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq B b
    rw [hB, hb] at hd
    omega
  have hP1bound : Module.finrank F4 ↥(A ⊔ b') ≤ 3 := by
    have hd := Submodule.finrank_sup_add_finrank_inf_eq A b'
    rw [hA, hb'] at hd
    omega
  have hE1P1top : (B ⊔ b) ⊔ (A ⊔ b') = ⊤ := by
    calc
      (B ⊔ b) ⊔ (A ⊔ b') = (A ⊔ B) ⊔ (b ⊔ b') := by ac_rfl
      _ = (A ⊔ B) ⊔ (a ⊔ a') := by rw [hbbW]
      _ = ⊤ := hCWtop
  have hc1 := isCompl_of_sup_eq_top_of_finrank_add_le hE1P1top (by omega)
  have hE1dim : Module.finrank F4 ↥(B ⊔ b) = 3 := by
    have hd := Submodule.finrank_add_eq_of_isCompl hc1
    have hdim : Module.finrank F4 V6 = 6 := by simp
    omega
  letI : Fintype F4 := Fintype.ofFinite F4
  have hFcard : Nat.card F4 = 4 := by
    rw [Nat.card_eq_fintype_card, TauCeti.card_galoisField_two_two]
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hFcard
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    simpa only [one_pow, CharTwo.add_self_eq_zero, zero_add, one_ne_zero] using hω
  have hω3 : ω ^ 3 = 1 := by
    simpa [TauCeti.card_galoisField_two_two] using FiniteField.pow_card_sub_one_eq_one ω hω0
  obtain ⟨z, hz, hzE, hzP, hzc⟩ :=
    exists_scalar_mem_stabSub hc2 ω hω0 (by rw [hE2dim]; exact hω3)
  have hzinvc : ∀ t ∈ stabSub (B ⊔ a') (A ⊔ a), Commute z⁻¹ t :=
    fun t ht => (hzc t ht).inv_left
  have hnz := hnorm z hz hzc
  have hnzinv := hnorm z⁻¹ (inv_mem hz) hzinvc
  have hnormal : z ∈ Subgroup.normalizer (stabSub (A ⊔ b') (B ⊔ b) : Set SL6) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hnz g
    · intro hg
      have h := hnzinv (z * g * z⁻¹) hg
      simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  have hpres := normalizer_stabSub_preserves_complements hc1 ω hω0 hω1
    (by rw [hE1dim]; exact hω3) hnormal
  let f : V6 →ₗ[F4] V6 := Matrix.toLin' (z : Matrix (Fin 6) (Fin 6) F4)
  have hfa : ∀ v ∈ a, f v = ω • v :=
    fun v hv => hzE v ((le_sup_right : a ≤ A ⊔ a) hv)
  have hfa' : ∀ v ∈ a', f v = v :=
    fun v hv => hzP v ((le_sup_right : a' ≤ B ⊔ a') hv)
  have hfW : ∀ v ∈ a ⊔ a', f v ∈ a ⊔ a' := by
    intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hfa u hu, hfa' w hw]
    exact (a ⊔ a').add_mem
      ((a ⊔ a').smul_mem ω ((le_sup_left : a ≤ a ⊔ a') hu))
      ((le_sup_right : a' ≤ a ⊔ a') hw)
  have hfb : ∀ v ∈ b, f v ∈ b := by
    intro v hv
    exact mem_right_of_mem_sup_of_disjoint hCW.disjoint le_sup_right hbW
      (hpres.1 v ((le_sup_right : b ≤ B ⊔ b) hv)) (hfW v (hbW hv))
  have hfb' : ∀ v ∈ b', f v ∈ b' := by
    intro v hv
    exact mem_right_of_mem_sup_of_disjoint hCW.disjoint le_sup_left hb'W
      (hpres.2 v ((le_sup_right : b' ≤ A ⊔ b') hv)) (hfW v (hb'W hv))
  have hfa'1 : ∀ v ∈ a', f v = (1 : F4) • v := by simpa only [one_smul] using hfa'
  have hbalt : b = a ∨ b = a' := by
    rcases Submodule.le_left_or_le_right_of_scalar_invariant_line haa' hb hbW
      hω1 hfa hfa'1 hfb with h | h
    · exact Or.inl (Submodule.eq_of_le_of_finrank_eq h (hb.trans ha.symm))
    · exact Or.inr (Submodule.eq_of_le_of_finrank_eq h (hb.trans ha'.symm))
  have hb'alt : b' = a ∨ b' = a' := by
    rcases Submodule.le_left_or_le_right_of_scalar_invariant_line haa' hb' hb'W
      hω1 hfa hfa'1 hfb' with h | h
    · exact Or.inl (Submodule.eq_of_le_of_finrank_eq h (hb'.trans ha.symm))
    · exact Or.inr (Submodule.eq_of_le_of_finrank_eq h (hb'.trans ha'.symm))
  have hne : b ≠ b' := by
    intro heq
    have hbot : b = ⊥ := disjoint_self.mp (by simpa only [← heq] using hbb')
    have hzero := Submodule.finrank_eq_zero.mpr hbot
    omega
  rcases hbalt with hba | hba <;> rcases hb'alt with hb'a | hb'a
  · exact False.elim (hne (hba.trans hb'a.symm))
  · exact Or.inl ⟨hba, hb'a⟩
  · exact Or.inr ⟨hba, hb'a⟩
  · exact False.elim (hne (hba.trans hb'a.symm))

private theorem commute_stabSub_of_isCompl {P E : Submodule F4 V6} (hc : IsCompl E P)
    {g h : SL6} (hg : g ∈ stabSub E P) (hh : h ∈ stabSub P E) : Commute g h := by
  let theta : SL6 →* (V6 ≃ₗ[F4] V6) := Matrix.SpecialLinearGroup.toLin'
  change g * h = h * g
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ E ⊔ P := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  change theta (g * h) (u + w) = theta (h * g) (u + w)
  rw [map_mul, map_mul]
  have hgE : ∀ v ∈ E, theta g v = v := hg.1
  have hhP : ∀ v ∈ P, theta h v = v := hh.1
  have hgP : ∀ v ∈ P, theta g v ∈ P := hg.2.1
  have hhE : ∀ v ∈ E, theta h v ∈ E := hh.2.1
  simp only [LinearEquiv.mul_apply, map_add, hhP w hw, hgE u hu,
    hgE (theta h u) (hhE u hu), hhP (theta g w) (hgP w hw)]

private theorem span_range_basis_submodule {ι : Type*} {S : Submodule F4 V6}
    (b : Module.Basis ι F4 S) :
    Submodule.span F4 (Set.range fun i => (b i : V6)) = S := by
  have hset : S.subtype '' Set.range b = Set.range fun i => (b i : V6) := by
    ext x
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, rfl⟩
  simpa only [Submodule.map_span, hset, Submodule.map_top,
    Submodule.range_subtype] using
    congrArg (fun U : Submodule F4 S => U.map S.subtype) b.span_eq

private theorem exists_basis_four_summands
    (A B a a' : Submodule F4 V6)
    (hA : Module.finrank F4 A = 2) (hB : Module.finrank F4 B = 2)
    (ha : Module.finrank F4 a = 1) (ha' : Module.finrank F4 a' = 1)
    (htop : A ⊔ B ⊔ a ⊔ a' = ⊤) :
    ∃ β : Module.Basis (Fin 6) F4 V6,
      Submodule.span F4 (β '' ({0, 1} : Set (Fin 6))) = A ∧
      Submodule.span F4 (β '' ({2, 3} : Set (Fin 6))) = B ∧
      Submodule.span F4 (β '' ({4} : Set (Fin 6))) = a ∧
      Submodule.span F4 (β '' ({5} : Set (Fin 6))) = a' := by
  let bA := Module.finBasisOfFinrankEq F4 A hA
  let bB := Module.finBasisOfFinrankEq F4 B hB
  let ba := Module.finBasisOfFinrankEq F4 a ha
  let ba' := Module.finBasisOfFinrankEq F4 a' ha'
  let v : Fin 6 → V6 := ![(bA 0 : V6), (bA 1 : V6), (bB 0 : V6),
    (bB 1 : V6), (ba 0 : V6), (ba' 0 : V6)]
  have hArange : (Set.range fun i : Fin 2 => (bA i : V6)) = v '' ({0, 1} : Set (Fin 6)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases hi with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hBrange : (Set.range fun i : Fin 2 => (bB i : V6)) = v '' ({2, 3} : Set (Fin 6)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨2, by simp, rfl⟩
      · exact ⟨3, by simp, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases hi with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have harange : (Set.range fun i : Fin 1 => (ba i : V6)) = v '' ({4} : Set (Fin 6)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      exact ⟨4, by simp, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hi4 : i = 4 := hi
      subst i
      exact ⟨0, rfl⟩
  have ha'range : (Set.range fun i : Fin 1 => (ba' i : V6)) = v '' ({5} : Set (Fin 6)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      exact ⟨5, by simp, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hi5 : i = 5 := hi
      subst i
      exact ⟨0, rfl⟩
  have hsA : Submodule.span F4 (v '' ({0, 1} : Set (Fin 6))) = A :=
    hArange ▸ span_range_basis_submodule bA
  have hsB : Submodule.span F4 (v '' ({2, 3} : Set (Fin 6))) = B :=
    hBrange ▸ span_range_basis_submodule bB
  have hsa : Submodule.span F4 (v '' ({4} : Set (Fin 6))) = a :=
    harange ▸ span_range_basis_submodule ba
  have hsa' : Submodule.span F4 (v '' ({5} : Set (Fin 6))) = a' :=
    ha'range ▸ span_range_basis_submodule ba'
  have hle : ∀ S : Set (Fin 6), Submodule.span F4 (v '' S) ≤
      Submodule.span F4 (Set.range v) := by
    intro S
    apply Submodule.span_mono
    rintro _ ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  have hs : Submodule.span F4 (Set.range v) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← htop, ← hsA, ← hsB, ← hsa, ← hsa']
    exact sup_le (sup_le (sup_le (hle _) (hle _)) (hle _)) (hle _)
  have hli : LinearIndependent F4 v := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change Fintype.card (Fin 6) = Module.finrank F4 ↥(Submodule.span F4 (Set.range v))
    rw [hs]
    simp
  let β : Module.Basis (Fin 6) F4 V6 :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hβ : (β : Fin 6 → V6) = v :=
    coe_basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  exact ⟨β, by simpa only [hβ] using hsA, by simpa only [hβ] using hsB,
    by simpa only [hβ] using hsa, by simpa only [hβ] using hsa'⟩

private theorem map_blockSpecialLinear_to_stabSub
    (β : Module.Basis (Fin 6) F4 V6) (I : Finset (Fin 6)) :
    (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) I).map
      ((Matrix.SpecialLinearGroup.toLin_equiv β).trans
        Matrix.SpecialLinearGroup.toLin'_equiv.symm).toMonoidHom =
      stabSub (Submodule.span F4 (β '' (↑Iᶜ : Set (Fin 6))))
        (Submodule.span F4 (β '' (↑I : Set (Fin 6)))) := by
  classical
  let Φ : SL6 ≃* SL6 := (Matrix.SpecialLinearGroup.toLin_equiv β).trans
    Matrix.SpecialLinearGroup.toLin'_equiv.symm
  let E : Submodule F4 V6 := Submodule.span F4 (β '' (↑I : Set (Fin 6)))
  let P : Submodule F4 V6 := Submodule.span F4 (β '' (↑Iᶜ : Set (Fin 6)))
  have hmem : ∀ (S : Set (Fin 6)) (v : V6), v ∈ Submodule.span F4 (β '' S) ↔
      ∀ i ∉ S, (β.repr v) i = 0 := by
    intro S v
    rw [β.mem_span_image]
    constructor
    · intro h i hi
      by_contra hne
      exact hi (h (Finsupp.mem_support_iff.mpr hne))
    · intro h i hi
      by_contra hnot
      exact (Finsupp.mem_support_iff.mp hi) (h i hnot)
  have hentry : ∀ (g : SL6) (i j : Fin 6),
      (β.repr ((Φ g : Matrix (Fin 6) (Fin 6) F4) *ᵥ β j)) i =
        (g : Matrix (Fin 6) (Fin 6) F4) i j := by
    intro g i j
    have heq : Matrix.SpecialLinearGroup.toLin'_equiv (Φ g) =
        Matrix.SpecialLinearGroup.toLin_equiv β g := by
      change Matrix.SpecialLinearGroup.toLin'_equiv
        (Matrix.SpecialLinearGroup.toLin'_equiv.symm
          (Matrix.SpecialLinearGroup.toLin_equiv β g)) = _
      exact MulEquiv.apply_symm_apply _ _
    have hlin : Matrix.toLin' (Φ g : Matrix (Fin 6) (Fin 6) F4) =
        Matrix.toLin β β (g : Matrix (Fin 6) (Fin 6) F4) := by
      have h := congrArg (fun u : _root_.SpecialLinearGroup F4 V6 =>
        (u : V6 →ₗ[F4] V6)) heq
      change (Matrix.SpecialLinearGroup.toLin' (Φ g)).toLinearMap =
        (Matrix.SpecialLinearGroup.toLin_equiv β g : V6 →ₗ[F4] V6) at h
      simpa only [Matrix.SpecialLinearGroup.toLin'_to_linearMap,
        Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq] using h
    change (β.repr (Matrix.toLin' (Φ g : Matrix (Fin 6) (Fin 6) F4) (β j))) i = _
    rw [← LinearMap.toMatrix_apply β β _ i j, hlin, LinearMap.toMatrix_toLin]
  have hmap : ∀ g ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) I,
      ∀ v ∈ E, (Φ g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ E := by
    intro g hg
    have hle : E ≤ E.comap (Matrix.toLin' (Φ g : Matrix (Fin 6) (Fin 6) F4)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      change (Φ g : Matrix (Fin 6) (Fin 6) F4) *ᵥ β j ∈
        Submodule.span F4 (β '' (↑I : Set (Fin 6)))
      apply (hmem _ _).mpr
      intro i hi
      rw [hentry, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hg i j (Or.inl hi)]
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp only [Matrix.one_apply, if_neg hij]
    exact fun v hv => hle hv
  have hfix : ∀ g ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) I,
      ∀ v ∈ P, (Φ g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v := by
    intro g hg
    have hle : P ≤ LinearMap.ker
        (Matrix.toLin' (Φ g : Matrix (Fin 6) (Fin 6) F4) - LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      have hjnot : j ∉ I := by simpa only [Finset.mem_coe, Finset.mem_compl] using hj
      change (Φ g : Matrix (Fin 6) (Fin 6) F4) *ᵥ β j - β j = 0
      apply sub_eq_zero.mpr
      apply β.repr.injective
      ext i
      rw [hentry, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hg i j (Or.inr hjnot)]
      simp only [β.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]
    intro v hv
    have h := hle hv
    change (Φ g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v - v = 0 at h
    exact sub_eq_zero.mp h
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨hfix g hg, hmap g hg, ?_⟩
    intro v hv
    have h := hmap g⁻¹ (inv_mem hg) v hv
    rw [map_inv] at h
    exact h
  · intro h hh
    let g := Φ.symm h
    have hΦ : Φ g = h := Φ.apply_symm_apply h
    refine ⟨g, ?_, hΦ⟩
    change g ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) I
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    intro i j hij
    have hentry' : (g : Matrix (Fin 6) (Fin 6) F4) i j =
        (β.repr ((h : Matrix (Fin 6) (Fin 6) F4) *ᵥ β j)) i := by
      rw [← hΦ]
      exact (hentry g i j).symm
    by_cases hj : j ∈ I
    · have hi : i ∉ I := hij.resolve_right (not_not.mpr hj)
      have hjE : β j ∈ E := Submodule.subset_span ⟨j, hj, rfl⟩
      have hz : (β.repr ((h : Matrix (Fin 6) (Fin 6) F4) *ᵥ β j)) i = 0 :=
        (hmem _ _).mp (hh.2.1 _ hjE) i hi
      have hne : i ≠ j := fun h => hi (h.symm ▸ hj)
      rw [hentry', hz]
      simp only [Matrix.one_apply, if_neg hne]
    · have hjP : β j ∈ P := Submodule.subset_span ⟨j, by
        simpa only [Finset.mem_coe, Finset.mem_compl] using hj, rfl⟩
      rw [hentry', hh.1 _ hjP]
      simp only [β.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]

theorem stabSub_sup_eq_of_common_line (A B a a' : Submodule F4 V6)
    (hA : Module.finrank F4 A = 2) (hB : Module.finrank F4 B = 2)
    (ha : Module.finrank F4 a = 1) (ha' : Module.finrank F4 a' = 1)
    (htop : A ⊔ B ⊔ a ⊔ a' = ⊤) :
    stabSub (A ⊔ a') (B ⊔ a) ⊔ stabSub (B ⊔ a') (A ⊔ a) =
      stabSub a' (A ⊔ B ⊔ a) := by
  classical
  obtain ⟨β, hsA, hsB, hsa, hsa'⟩ := exists_basis_four_summands A B a a' hA hB ha ha' htop
  let Φ : SL6 ≃* SL6 := (Matrix.SpecialLinearGroup.toLin_equiv β).trans
    Matrix.SpecialLinearGroup.toLin'_equiv.symm
  let I : Finset (Fin 6) := {0, 1, 4}
  let J : Finset (Fin 6) := {2, 3, 4}
  have hI : (↑I : Set (Fin 6)) = ({0, 1} : Set (Fin 6)) ∪ {4} := by
    ext i; fin_cases i <;> simp [I]
  have hIc : (↑Iᶜ : Set (Fin 6)) = ({2, 3} : Set (Fin 6)) ∪ {5} := by
    ext i; fin_cases i <;> simp [I]
  have hJ : (↑J : Set (Fin 6)) = ({2, 3} : Set (Fin 6)) ∪ {4} := by
    ext i; fin_cases i <;> simp [J]
  have hJc : (↑Jᶜ : Set (Fin 6)) = ({0, 1} : Set (Fin 6)) ∪ {5} := by
    ext i; fin_cases i <;> simp [J]
  have hU : (↑(I ∪ J) : Set (Fin 6)) =
      (({0, 1} : Set (Fin 6)) ∪ {2, 3}) ∪ {4} := by
    ext i; fin_cases i <;> simp [I, J]
  have hUc : (↑(I ∪ J)ᶜ : Set (Fin 6)) = {5} := by
    ext i; fin_cases i <;> simp [I, J]
  have hmI : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) I).map
      Φ.toMonoidHom = stabSub (B ⊔ a') (A ⊔ a) := by
    rw [map_blockSpecialLinear_to_stabSub]
    simp only [hIc, hI, Set.image_union, Submodule.span_union, hsA, hsB, hsa, hsa']
  have hmJ : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) J).map
      Φ.toMonoidHom = stabSub (A ⊔ a') (B ⊔ a) := by
    rw [map_blockSpecialLinear_to_stabSub]
    simp only [hJc, hJ, Set.image_union, Submodule.span_union, hsA, hsB, hsa, hsa']
  have hmU : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F4) (I ∪ J)).map
      Φ.toMonoidHom = stabSub a' (A ⊔ B ⊔ a) := by
    rw [map_blockSpecialLinear_to_stabSub]
    simp only [hUc, hU, Set.image_union, Submodule.span_union, hsA, hsB, hsa, hsa']
  have hu := CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_union_eq_sup
    (K := F4) (I := I) (J := J) (c := (4 : Fin 6)) (by simp [I]) (by simp [J])
  rw [hu, Subgroup.map_sup, hmI, hmJ, sup_comm] at hmU
  exact hmU

theorem ggN2LineAlignmentInput_holds : GGN2LineAlignmentInput := by
  intro A B a a' b b' hA hB ha ha' hb hb' htop hbW hb'W hbb' hnorm
  rcases line_pair_eq_or_eq_swap_of_center_normalizes A B a a' b b'
    hA hB ha ha' hb hb' htop hbW hb'W hbb' hnorm with ⟨hba, hb'a'⟩ | ⟨hba', hb'a⟩
  · refine Or.inr ⟨hba, hb'a', ?_⟩
    rw [hba, hb'a']
    exact (stabSub_sup_eq_of_common_line A B a a' hA hB ha ha' htop).symm.le
  · left
    rw [hba', hb'a]
    have hEbound : Module.finrank F4 ↥(A ⊔ a) ≤ 3 := by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq A a
      rw [hA, ha] at hd
      omega
    have hPbound : Module.finrank F4 ↥(B ⊔ a') ≤ 3 := by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq B a'
      rw [hB, ha'] at hd
      omega
    have hEPtop : (A ⊔ a) ⊔ (B ⊔ a') = ⊤ := by
      calc
        (A ⊔ a) ⊔ (B ⊔ a') = A ⊔ B ⊔ a ⊔ a' := by ac_rfl
        _ = ⊤ := htop
    have hc := isCompl_of_sup_eq_top_of_finrank_add_le hEPtop (by omega)
    exact fun g hg h hh => commute_stabSub_of_isCompl hc hg hh

end CFSG.StandardType.N2Chart

end
