module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorusLayer
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofSL3
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Heis
import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL3Model
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofD4

public section

open CFSG.RankThree.PartTwo.Sec19
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Leaves


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

open CFSG.RankThree.PartTwo.Sec11 (d4ThreeASL3Model_holds)
open CFSG.RankThree.PartTwo.Sec11.Item1118Res2Proof (IsSL3Model isSL3Model_comap)

theorem layer_rep (P : D4Par n X σ) {x : C0 σ} (hx : IsClassX σ x) :
    ∃ (L : Type) (_ : Field L) (ρ : cenX σ x →* Matrix.SpecialLinearGroup (Fin 3) L),
      IsSL3Model ρ := by
  unfold IsClassX at hx
  obtain ⟨hx3, hx1, g, hg⟩ := hx
  have hv3 : (g * x * g⁻¹) ^ 3 = 1 := TorusLayerAux.conj_pow_eq_one hx3
  have hv1 : g * x * g⁻¹ ≠ 1 := TorusLayerAux.conj_ne_one hx1
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨L, _, ρ₀, hρ₀⟩ := d4ThreeASL3Model_holds X (2 ^ n) σ P.card P.frob h3 (g * x * g⁻¹) hg
    hv3 hv1
  obtain ⟨ρ, hρ⟩ := isSL3Model_comap (MulAut.conj g) (v := x) (ρ₀ := ρ₀) hρ₀
  exact ⟨L, _, ρ, hρ⟩

theorem centralizer_layer_le_cenX (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    Subgroup.centralizer (layerSub σ x : Set (C0 σ)) ≤ cenX σ x := by
  intro z hz
  have hxD : x ∈ layerSub σ x := (classX_layer σ P hn hx).1
  rw [Subgroup.mem_centralizer_iff] at hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz x hxD).symm

theorem layer_centralizer_scalar (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    ∃ (L : Type) (_ : Field L) (ρ : cenX σ x →* Matrix.SpecialLinearGroup (Fin 3) L),
      IsSL3Model ρ ∧ ∀ z : cenX σ x, (z : C0 σ) ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)) →
        ρ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) := by
  obtain ⟨L, _, ρ, hρ⟩ := layer_rep P hx
  refine ⟨L, _, ρ, hρ, ?_⟩
  obtain ⟨hH, -⟩ := layer_facts P hn hx
  obtain ⟨y, hy, p, hp, u, hu, hu1, hu3, huc, hup⟩ := hH
  obtain ⟨-, hzx⟩ := classX_layer σ P hn hx
  have hux : u ∈ Subgroup.zpowers x := hzx u hu hu3 huc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hux
  have hDC : layerSub σ x ≤ cenX σ x := layerSub_le_self _
  have hx3 : x ^ 3 = 1 := hx.1
  set y' : cenX σ x := ⟨y, hDC hy⟩ with hy'
  set p' : cenX σ x := ⟨p, hDC hp⟩ with hp'
  set u' : cenX σ x := ⟨u, hDC hu⟩ with hu'
  set x' : cenX σ x := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ with hx'
  have hux' : u' = x' ^ k := Subtype.ext (by simp [hu', hx', hk])
  have hcomm : p' * y' * p'⁻¹ * y'⁻¹ = u' := Subtype.ext (by simpa [hy', hp', hu'] using hup)
  have hρu : ρ u' ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) := by
    rw [hux', map_zpow]
    exact Subgroup.zpow_mem _ hρ.1 k
  have hu3' : ∃ m : ℕ, u' ^ 3 ^ m = 1 :=
    ⟨1, Subtype.ext (by simpa [hu'] using hu3)⟩
  have hρu1 : ρ u' ≠ 1 := by
    intro h1
    apply hu1
    have := hρ.eq_one hx3 hu3' h1
    simpa [hu'] using congrArg Subtype.val this
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hρu
  have hc1 : c ≠ 1 := by
    intro h1
    apply hρu1
    apply Subtype.ext
    rw [← hc, h1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hrel : ρ p' * ρ y' = ρ u' * (ρ y' * ρ p') := by
    calc ρ p' * ρ y' = (ρ p' * ρ y' * (ρ p')⁻¹ * (ρ y')⁻¹) * (ρ y' * ρ p') := by group
      _ = ρ u' * (ρ y' * ρ p') := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hcomm]
  have hrelm : ((ρ p' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
      ((ρ y' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      c • (((ρ y' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
        ((ρ p' : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) L =>
      (g : Matrix (Fin 3) (Fin 3) L)) hrel
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rw [this, ← hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hunit : ∀ A : Matrix.SpecialLinearGroup (Fin 3) L,
      IsUnit (A : Matrix (Fin 3) (Fin 3) L) := fun A =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [A.2]; exact isUnit_one)
  intro z hz
  have hz' := Subgroup.mem_centralizer_iff.mp hz
  have hzy : ρ z * ρ y' = ρ y' * ρ z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz' y (SetLike.mem_coe.mpr hy)).symm
  have hzp : ρ z * ρ p' = ρ p' * ρ z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz' p (SetLike.mem_coe.mpr hp)).symm
  obtain ⟨r, hr⟩ := heis_scalar (hunit _) (hunit _) hc1 hrelm
    (g := ((ρ z : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))
    (by simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hzy)
    (by simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hzp)
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨r, ?_, hr.symm ▸ rfl⟩
  have hdet := (ρ z).2
  rw [hr, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  rw [Fintype.card_fin]
  exact hdet

theorem layer_centralizer_abelian (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    ∀ a ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)),
      ∀ b ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)), a * b = b * a := by
  obtain ⟨L, _, ρ, hρ, hscal⟩ := layer_centralizer_scalar P hn hx
  obtain ⟨-, hcube⟩ := layer_facts P hn hx
  intro a ha b hb
  have hDC : layerSub σ x ≤ cenX σ x := layerSub_le_self _
  have haC : a ∈ cenX σ x := centralizer_layer_le_cenX P hn hx ha
  have hbC : b ∈ cenX σ x := centralizer_layer_le_cenX P hn hx hb
  set a' : cenX σ x := ⟨a, haC⟩ with ha'
  set b' : cenX σ x := ⟨b, hbC⟩ with hb'
  have hcD : a * b * a⁻¹ * b⁻¹ ∈ layerSub σ x := by
    have := Subgroup.commutator_mem_commutator haC hbC
    rwa [commutatorElement_def] at this
  have hcZ : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
      (Subgroup.inv_mem _ hb)
  have hcc : ∀ d ∈ layerSub σ x, (a * b * a⁻¹ * b⁻¹) * d = d * (a * b * a⁻¹ * b⁻¹) := by
    intro d hd
    exact ((Subgroup.mem_centralizer_iff.mp hcZ) d (SetLike.mem_coe.mpr hd)).symm
  have hc3 : (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := hcube _ hcD hcc
  have hρ1 : ρ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
    have hA := hscal a' ha
    have hB := hscal b' hb
    have hcomm : ρ a' * ρ b' = ρ b' * ρ a' :=
      Subgroup.mem_center_iff.mp hB (ρ a')
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hx3 : x ^ 3 = 1 := hx.1
  have h3' : ∃ m : ℕ, (a' * b' * a'⁻¹ * b'⁻¹) ^ 3 ^ m = 1 :=
    ⟨1, Subtype.ext (by simpa [ha', hb'] using hc3)⟩
  have h1 := hρ.eq_one hx3 h3' hρ1
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := by simpa [ha', hb'] using congrArg Subtype.val h1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h2, one_mul]

theorem layer_centralizer_three_part (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    ∀ z ∈ Subgroup.centralizer (layerSub σ x : Set (C0 σ)), (∃ k : ℕ, z ^ (3 ^ k) = 1) →
      z ∈ Subgroup.zpowers x := by
  obtain ⟨L, _, ρ, hρ, hscal⟩ := layer_centralizer_scalar P hn hx
  intro z hz hz3
  have hzC : z ∈ cenX σ x := centralizer_layer_le_cenX P hn hx hz
  have h3' : ∃ k : ℕ, (⟨z, hzC⟩ : cenX σ x) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hz3
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  exact hρ.2.2.1 ⟨z, hzC⟩ h3' (hscal ⟨z, hzC⟩ hz)

theorem layer_center_cube (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ} (hx : IsClassX σ x) :
    ∀ w ∈ layerSub σ x, (∀ d ∈ layerSub σ x, w * d = d * w) → w ^ 3 = 1 :=
  (layer_facts P hn hx).2

end Leaves

end CFSG.RankThree.PartTwo.Sec4.E27
