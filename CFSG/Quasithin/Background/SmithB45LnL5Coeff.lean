module

public import CFSG.Quasithin.Background.JonesParshallCurtisType
public import CFSG.Quasithin.Background.SmithB42LnL5Gen
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.JonesParshallNatural
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45L5

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

theorem det_of_isLoU {M : 𝕄} (h : IsLoU M) : M.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular M fun i j hij =>
    (h i j).1 (OrderDual.toDual_lt_toDual.mp hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem det_of_isUpU {M : 𝕄} (h : IsUpU M) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (M := M) fun i j hij => (h i j).1 hij]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

@[expose] def cellVal (J : Fin 4 → Bool) (k : Fin 120) : ZMod 2 :=
  if (canW k).all J then 1 else 0

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem form_val
    {ρ : Representation (ZMod 2) G5 V}
    {f : Module.Dual (ZMod 2) V} (hf : ∀ z ∈ augL ρ, f z = 0) {y : V} (hy : y ∈ fixU ρ)
    (hfy : f y = 1) (heig : ∀ s, Th ρ s y = 0 ∨ Th ρ s y = y) {J : Fin 4 → Bool}
    (hJ : ∀ s, Th ρ s y = 0 ↔ J s = true) {g : G5} {gb : BM} (hg : (g : 𝕄) = toMat gb)
    {d : BM × Fin 120 × BM} (hd1 : IsLoU (toMat d.1)) (hd2 : IsUpU (toMat d.2.2))
    (hd : gb = bmul d.1 (bmul (bword (canW d.2.1)) d.2.2)) : f (ρ g y) = cellVal J d.2.1 := by
  let q : G5 := ⟨toMat d.1, det_of_isLoU hd1⟩
  let u : G5 := ⟨toMat d.2.2, det_of_isUpU hd2⟩
  have hq : q ∈ Lgrp := hd1
  have hu : u ∈ Ugrp := hd2
  have e : g = q * wE d.2.1 * u := by
    apply Subtype.ext
    rw [hg, hd, toMat_bmul, toMat_bmul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, wE, wordProd_coe, Matrix.mul_assoc]
  rw [form_cell ρ hf hy hq hu e, cellVal]
  split_ifs with h
  · rw [hW_of_forall ρ fun s hs => (hJ s).mpr (List.all_eq_true.mp h s hs), hfy]
  · rw [List.all_eq_true] at h
    push Not at h
    obtain ⟨s, hs, hJs⟩ := h
    rw [hW_of_exists ρ heig ⟨s, hs, fun h0 => hJs ((hJ s).mp h0)⟩, map_zero]

theorem le_finrank_of_cells
    [Finite V] {ρ : Representation (ZMod 2) G5 V}
    (hρ : IsSimpleRep ρ) {y : V} (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) {J : Fin 4 → Bool}
    (hJ : ∀ s, Th ρ s y = 0 ↔ J s = true) {m r : ℕ} (a : G5) (aB : BM) (haB : (a : 𝕄) = toMat aB)
    (gB gI hB hI : Fin m → BM) (hgI : ∀ i, bmul (gI i) (gB i) = bone)
    (hhI : ∀ j, bmul (hB j) (hI j) = bone) (cA c0 : Fin m → Fin m → BM × Fin 120 × BM)
    (hcA : ∀ i j, IsLoU (toMat (cA i j).1) ∧ IsUpU (toMat (cA i j).2.2) ∧
      bmul (gI i) (bmul aB (hB j)) =
        bmul (cA i j).1 (bmul (bword (canW (cA i j).2.1)) (cA i j).2.2))
    (hc0 : ∀ i j, IsLoU (toMat (c0 i j).1) ∧ IsUpU (toMat (c0 i j).2.2) ∧
      bmul (gI i) (hB j) = bmul (c0 i j).1 (bmul (bword (canW (c0 i j).2.1)) (c0 i j).2.2))
    (ri ci : Fin r → Fin m) (Y : Matrix (Fin r) (Fin r) (ZMod 2))
    (hY : Y * Matrix.of (fun p q => cellVal J (cA (ri p) (ci q)).2.1 -
      cellVal J (c0 (ri p) (ci q)).2.1) = 1) :
    r ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
  obtain ⟨f, hf, hfy⟩ := exists_form hρ hy hy0
  have heig := eigen_of_simple hρ hy hy0
  have hG : ∀ i, toMat (gI i) * toMat (gB i) = 1 := fun i => by
    rw [← toMat_bmul, hgI, toMat_bone]
  have hH : ∀ j, toMat (hB j) * toMat (hI j) = 1 := fun j => by
    rw [← toMat_bmul, hhI, toMat_bone]
  let G : Fin m → G5 := fun i => B42Ln.ofMatInv (toMat (gI i)) (toMat (gB i)) (hG i)
  let H : Fin m → G5 := fun j => B42Ln.ofMatInv (toMat (hB j)) (toMat (hI j)) (hH j)
  have hGa : ∀ i j, ((G i * a * H j : G5) : 𝕄) = toMat (bmul (gI i) (bmul aB (hB j))) :=
    fun i j => by
      rw [toMat_bmul, toMat_bmul, ← haB, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
      rfl
  have hG0 : ∀ i j, ((G i * H j : G5) : 𝕄) = toMat (bmul (gI i) (hB j)) := fun i j => by
    rw [toMat_bmul, Matrix.SpecialLinearGroup.coe_mul]
    rfl
  have hval : ∀ i j, f (ρ (G i) ((ρ a - 1) (ρ (H j) y))) =
      cellVal J (cA i j).2.1 - cellVal J (c0 i j).2.1 := fun i j => by
    have e1 : f (ρ (G i) ((ρ a - 1) (ρ (H j) y))) =
        f (ρ (G i * a * H j) y) - f (ρ (G i * H j) y) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, map_mul, map_mul, map_mul,
        Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
    obtain ⟨a1, a2, a3⟩ := hcA i j
    obtain ⟨b1, b2, b3⟩ := hc0 i j
    rw [e1, form_val hf hy hfy heig hJ (hGa i j) a1 a2 a3, form_val hf hy hfy heig hJ (hG0 i j)
      b1 b2 b3]
  let v : Fin r → V := fun q => (ρ a - 1) (ρ (H (ci q)) y)
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hM : Matrix.of (fun p q => cellVal J (cA (ri p) (ci q)).2.1 -
        cellVal J (c0 (ri p) (ci q)).2.1) *ᵥ c = 0 := by
      funext p
      have h1 := congrArg (fun z => f (ρ (G (ri p)) z)) hc
      simp only [map_sum, map_smul, smul_eq_mul, map_zero, v, hval] at h1
      rw [Pi.zero_apply, ← h1]
      simp only [mulVec, dotProduct, Matrix.of_apply]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    have h2 : c = Y *ᵥ (Matrix.of (fun p q => cellVal J (cA (ri p) (ci q)).2.1 -
        cellVal J (c0 (ri p) (ci q)).2.1) *ᵥ c) := by
      rw [mulVec_mulVec, hY, one_mulVec]
    intro q
    rw [h2, hM, mulVec_zero, Pi.zero_apply]
  have hv : ∀ q, v q ∈ LinearMap.range (ρ a - 1) := fun q => ⟨_, rfl⟩
  have hli' : LinearIndependent (ZMod 2)
      (fun q => (⟨v q, hv q⟩ : LinearMap.range (ρ a - 1))) :=
    LinearIndependent.of_comp (LinearMap.range (ρ a - 1)).subtype hli
  simpa using hli'.fintype_card_le_finrank

theorem finrank_range_conj (ρ : Representation (ZMod 2) G5 V) {a b c : G5}
    (h : c * b * c⁻¹ = a) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ b - 1)) := by
  have hinv : ∀ x, ρ c (ρ c⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinj : Function.Injective (ρ c) := fun x x' hxx' => by
    have := congrArg (ρ c⁻¹) hxx'
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have hact : ∀ x, (ρ a - 1) (ρ c x) = ρ c ((ρ b - 1) x) := fun x => by
    rw [← h, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ c⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have heq : LinearMap.range (ρ a - 1) = (LinearMap.range (ρ b - 1)).map (ρ c) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(ρ b - 1) (ρ c⁻¹ x), ⟨_, rfl⟩, ?_⟩
      rw [← hact, hinv]
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨ρ c x, hact x⟩
  rw [heq]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

end CFSG.Quasithin.B45L5
