module

public import CFSG.Quasithin.Background.SmithB42LnL5W4
public import CFSG.Quasithin.Background.SmithB42LnL5Par
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
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.SmithB42LnL5Inv
public import CFSG.Quasithin.Background.SmithB51LnModel
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def topB (u : 𝕄) : 𝕄₄ := Matrix.of fun i j => u i.castSucc j.castSucc

@[expose] def idxH : Fin 6 → Fin 10 := ![0, 1, 2, 4, 5, 7]

@[expose] def idxE : Fin 4 → Fin 10 := ![3, 6, 8, 9]

@[expose] def crdH (x : Fin 10 → ZMod 2) : Fin 6 → ZMod 2 := fun k => x (idxH k)

@[expose] def crdE (x : Fin 10 → ZMod 2) : Fin 4 → ZMod 2 := fun i => x (idxE i)

theorem crdH_sub (x y : Fin 10 → ZMod 2) : crdH (x - y) = crdH x - crdH y := rfl

theorem crdE_sub (x y : Fin 10 → ZMod 2) : crdE (x - y) = crdE x - crdE y := rfl

theorem eq_of_crd {x y : Fin 10 → ZMod 2} (hH : crdH x = crdH y) (hE : crdE x = crdE y) :
    x = y := by
  funext i
  fin_cases i
  · exact congrFun hH 0
  · exact congrFun hH 1
  · exact congrFun hH 2
  · exact congrFun hE 0
  · exact congrFun hH 3
  · exact congrFun hH 4
  · exact congrFun hE 1
  · exact congrFun hH 5
  · exact congrFun hE 2
  · exact congrFun hE 3

theorem crdE_wedgeMat_upMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2) (x : Fin 10 → ZMod 2) :
    crdE (wedgeMat (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) *ᵥ x) =
      topB (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) *ᵥ crdE x := by
  funext i
  fin_cases i <;>
    simp [crdE, idxE, topB, wedgeMat, pr5, upMat, mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem crdH_wedgeMat_upMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2) {x : Fin 10 → ZMod 2}
    (h : crdE x = 0) :
    crdH (wedgeMat (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉) *ᵥ x) =
      w4 (topB (upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉)) *ᵥ crdH x := by
  have h3 : x 3 = 0 := congrFun h 0
  have h6 : x 6 = 0 := congrFun h 1
  have h8 : x 8 = 0 := congrFun h 2
  have h9 : x 9 = 0 := congrFun h 3
  funext k
  fin_cases k <;>
    simp [crdH, idxH, topB, wedgeMat, w4, pr4', pr5, upMat, mulVec, dotProduct, Fin.sum_univ_succ,
      h3, h6, h8, h9]

theorem zmod2_eq_of_add_eq_zero : ∀ {a b : ZMod 2}, a + b = 0 → a = b := by decide

theorem wedge_cond_upMat (c₃ c₆ c₈ c₉ : ZMod 2) {x : Fin 10 → ZMod 2}
    (h : wedgeMat (upMat 0 0 0 c₃ 0 0 c₆ 0 c₈ c₉) *ᵥ x = x) :
    ∀ k : Fin 6, ![c₃, c₆, c₈, c₉] (pr4' k).1 * crdE x (pr4' k).2 =
      ![c₃, c₆, c₈, c₉] (pr4' k).2 * crdE x (pr4' k).1 := by
  intro k
  have := congrFun h (idxH k)
  fin_cases k <;>
    simp [crdE, idxE, idxH, wedgeMat, pr4', pr5, upMat, mulVec, dotProduct,
      Fin.sum_univ_succ] at this ⊢ <;>
    exact zmod2_eq_of_add_eq_zero (by linear_combination this)

theorem wedge_zero_cases : ∀ w h : Fin 4 → ZMod 2,
    (∀ k : Fin 6, w (pr4' k).1 * h (pr4' k).2 = w (pr4' k).2 * h (pr4' k).1) → w ≠ 0 →
    h = 0 ∨ h = w := by
  decide

section Block

variable {u v : 𝕄}

theorem crdE_wedgeMat (hu : IsUpU u) (x : Fin 10 → ZMod 2) :
    crdE (wedgeMat u *ᵥ x) = topB u *ᵥ crdE x := by
  rw [eq_upMat hu]
  exact crdE_wedgeMat_upMat _ _ _ _ _ _ _ _ _ _ x

theorem crdH_wedgeMat (hu : IsUpU u) {x : Fin 10 → ZMod 2} (h : crdE x = 0) :
    crdH (wedgeMat u *ᵥ x) = w4 (topB u) *ᵥ crdH x := by
  rw [eq_upMat hu]
  exact crdH_wedgeMat_upMat _ _ _ _ _ _ _ _ _ _ h

theorem topB_mul (hu : IsUpU u) (hv : IsUpU v) : topB (u * v) = topB u * topB v := by
  rw [eq_upMat hu, eq_upMat hv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topB, upMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem topB_one : topB (1 : 𝕄) = 1 := by
  ext i j
  simp [topB, Matrix.one_apply, Fin.castSucc_inj]

theorem isUp4_topB (hu : IsUpU u) : IsUp4 (topB u) := fun a b =>
  ⟨fun h => (hu a.castSucc b.castSucc).1 (Fin.castSucc_lt_castSucc_iff.2 h),
    fun h => (hu a.castSucc b.castSucc).2 (by rw [h])⟩

theorem det_eq_one_of_isUp4 {M : 𝕄₄} (hM : IsUp4 M) : M.det = 1 := by
  rw [det_of_isUpperTriangular fun i j h => (hM i j).1 h]
  exact Finset.prod_eq_one fun i _ => (hM i i).2 rfl

end Block

@[expose] noncomputable def topHomOf {X : Subgroup G5} (hXU : X ≤ Ugrp) : ↥X →* G4 where
  toFun u := ⟨topB ((u : G5) : 𝕄), det_eq_one_of_isUp4 (isUp4_topB (hXU u.2))⟩
  map_one' := Subtype.ext topB_one
  map_mul' u v := Subtype.ext (topB_mul (hXU u.2) (hXU v.2))

theorem coe_topHomOf {X : Subgroup G5} (hXU : X ≤ Ugrp) (u : ↥X) :
    ((topHomOf hXU u : G4) : 𝕄₄) = topB ((u : G5) : 𝕄) := rfl

@[expose] def R4 : Subgroup G5 where
  carrier := {u | IsUpU ((u : G5) : 𝕄) ∧ topB ((u : G5) : 𝕄) = 1}
  one_mem' := ⟨Ugrp.one_mem, topB_one⟩
  mul_mem' {u v} hu hv := ⟨Ugrp.mul_mem hu.1 hv.1, by
    show topB ((u : 𝕄) * (v : 𝕄)) = 1
    rw [topB_mul hu.1 hv.1, hu.2, hv.2, Matrix.one_mul]⟩
  inv_mem' {u} hu := ⟨Ugrp.inv_mem hu.1, by
    have h1 : topB (((u⁻¹ : G5) : 𝕄) * (u : 𝕄)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, topB_one]
    rw [topB_mul (Ugrp.inv_mem hu.1) hu.1, hu.2, Matrix.mul_one] at h1
    exact h1⟩

@[expose] def colR (u : 𝕄) : Fin 4 → ZMod 2 := ![u 0 4, u 1 4, u 2 4, u 3 4]

theorem eq_of_mem_R4 {u : G5} (hu : u ∈ R4) :
    ((u : G5) : 𝕄) = upMat 0 0 0 (u 0 4) 0 0 (u 1 4) 0 (u 2 4) (u 3 4) := by
  have h := eq_upMat hu.1
  have ht := hu.2
  have e01 : (u : 𝕄) 0 1 = 0 := by simpa [topB] using congrFun (congrFun ht 0) 1
  have e02 : (u : 𝕄) 0 2 = 0 := by simpa [topB] using congrFun (congrFun ht 0) 2
  have e03 : (u : 𝕄) 0 3 = 0 := by simpa [topB] using congrFun (congrFun ht 0) 3
  have e12 : (u : 𝕄) 1 2 = 0 := by simpa [topB] using congrFun (congrFun ht 1) 2
  have e13 : (u : 𝕄) 1 3 = 0 := by simpa [topB] using congrFun (congrFun ht 1) 3
  have e23 : (u : 𝕄) 2 3 = 0 := by simpa [topB] using congrFun (congrFun ht 2) 3
  rw [e01, e02, e03, e12, e13, e23] at h
  exact h

theorem colR_injective {u v : G5} (hu : u ∈ R4) (hv : v ∈ R4)
    (h : colR (u : 𝕄) = colR (v : 𝕄)) : u = v := by
  apply Subtype.ext
  rw [eq_of_mem_R4 hu, eq_of_mem_R4 hv]
  have h0 : (u : 𝕄) 0 4 = (v : 𝕄) 0 4 := congrFun h 0
  have h1 : (u : 𝕄) 1 4 = (v : 𝕄) 1 4 := congrFun h 1
  have h2 : (u : 𝕄) 2 4 = (v : 𝕄) 2 4 := congrFun h 2
  have h3 : (u : 𝕄) 3 4 = (v : 𝕄) 3 4 := congrFun h 3
  rw [h0, h1, h2, h3]

theorem colR_one : colR (1 : 𝕄) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem card_R4_le : Nat.card R4 ≤ 16 := by
  have hinj : Function.Injective fun u : ↥R4 => colR ((u : G5) : 𝕄) := fun u v h =>
    Subtype.ext (colR_injective u.2 v.2 h)
  calc Nat.card R4 ≤ Nat.card (Fin 4 → ZMod 2) := Nat.card_le_card_of_injective _ hinj
    _ = 16 := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]; rfl

theorem wedge_cond {u : G5} (hu : u ∈ R4) {x : Fin 10 → ZMod 2}
    (hx : wedgeMat ((u : G5) : 𝕄) *ᵥ x = x) :
    ∀ k : Fin 6, colR (u : 𝕄) (pr4' k).1 * crdE x (pr4' k).2 =
      colR (u : 𝕄) (pr4' k).2 * crdE x (pr4' k).1 := by
  rw [eq_of_mem_R4 hu] at hx
  have := wedge_cond_upMat _ _ _ _ hx
  intro k
  have hk := this k
  simpa [colR] using hk

theorem eT_mem_R4 (i : Fin 4) (h : i.castSucc ≠ 4) : eT i.castSucc 4 h ∈ R4 := by
  refine ⟨?_, ?_⟩
  · show IsUpU (eTM i.castSucc 4)
    intro a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;> decide
  · show topB (eTM i.castSucc 4) = 1
    ext a b
    fin_cases i <;> fin_cases a <;> fin_cases b <;> decide

theorem mem_R4_of_comm {u : G5} (hu : u ∈ Ugrp)
    (hc : ∀ (i : Fin 4) (h : i.castSucc ≠ 4), u * eT i.castSucc 4 h = eT i.castSucc 4 h * u) :
    u ∈ R4 := by
  refine ⟨hu, ?_⟩
  have hU : IsUpU ((u : G5) : 𝕄) := hu
  have h44 : (u : 𝕄) 4 4 = 1 := (hU 4 4).2 rfl
  have hcol : ∀ (i : Fin 4) (a : Fin 5),
      (u : 𝕄) a i.castSucc = if a = i.castSucc then 1 else 0 := by
    intro i a
    have h1 := congrArg (fun g : G5 => (g : 𝕄) a 4) (hc i (by fin_cases i <;> decide))
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_eT] at h1
    have h2 : ((u : 𝕄) * eTM i.castSucc 4) a 4 = (u : 𝕄) a 4 + (u : 𝕄) a i.castSucc := by
      fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_five, eTMc] <;> ring
    have h3 : (eTM i.castSucc 4 * (u : 𝕄)) a 4 =
        (u : 𝕄) a 4 + if a = i.castSucc then (u : 𝕄) 4 4 else 0 := by
      fin_cases i <;> fin_cases a <;> simp [Matrix.mul_apply, Fin.sum_univ_five, eTMc]
    rw [h2, h3, h44] at h1
    exact add_left_cancel h1
  ext a b
  have := hcol b a.castSucc
  simp only [topB, Matrix.of_apply, Matrix.one_apply, Fin.castSucc_inj] at this ⊢
  exact this

abbrev FixW (X : Subgroup G5) : Type :=
  {x : Fin 10 → ZMod 2 // ∀ u ∈ X, wedgeMat ((u : G5) : 𝕄) *ᵥ x = x}

theorem card_mul_fixW_le {X : Subgroup G5} (hXU : X ≤ Ugrp)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1) :
    Nat.card X * Nat.card (FixW X) ≤ 2 ^ 10 ∧
      (2 ^ 10 ≤ Nat.card X * Nat.card (FixW X) → X ≠ ⊥ → X = R4) := by
  classical
  set τ := topHomOf hXU with hτ
  have hcard : Nat.card X = Nat.card τ.ker * Nat.card τ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup τ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange τ).toEquiv]
  have hU1 : ∀ M ∈ τ.range, IsUp4 ((M : G4) : 𝕄₄) := by
    rintro _ ⟨u, rfl⟩
    exact isUp4_topB (hXU u.2)
  have hc1 : ∀ a ∈ τ.range, ∀ b ∈ τ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc a a.2 b b.2)
  have h21 : ∀ a ∈ τ.range, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (h2 a a.2)
    rw [this, map_one]
  have h4 := card_mul_fix4_le hU1 hc1 h21
  have hK : ∀ k ∈ τ.ker, ((k : ↥X) : G5) ∈ R4 := fun k hk =>
    ⟨hXU k.2, congrArg (fun M : G4 => (M : 𝕄₄)) (MonoidHom.mem_ker.1 hk)⟩
  set F : Finset (Fin 10 → ZMod 2) :=
    Finset.univ.filter fun x => ∀ u ∈ X, wedgeMat ((u : G5) : 𝕄) *ᵥ x = x with hF
  have hFW : Nat.card (FixW X) = F.card := card_subtype_eq _
  have hmemF : ∀ x, x ∈ F ↔ ∀ u ∈ X, wedgeMat ((u : G5) : 𝕄) *ᵥ x = x := fun x => by
    simp [hF]
  set I := F.image crdE with hI
  set n₄ := Nat.card {x : Fin 6 → ZMod 2 // ∀ M ∈ τ.range, w4 ((M : G4) : 𝕄₄) *ᵥ x = x}
    with hn₄
  have hfib : F.card ≤ n₄ * I.card := by
    refine Finset.card_le_mul_card_image F n₄ fun a ha => ?_
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 ha
    have key : ∀ x ∈ F.filter (fun x => crdE x = crdE x₀),
        ∀ M ∈ τ.range, w4 ((M : G4) : 𝕄₄) *ᵥ crdH (x - x₀) = crdH (x - x₀) := by
      intro x hx M hM
      obtain ⟨u, rfl⟩ := hM
      rw [Finset.mem_filter] at hx
      have hd : crdE (x - x₀) = 0 := by rw [crdE_sub, hx.2, sub_self]
      rw [coe_topHomOf, ← crdH_wedgeMat (hXU u.2) hd, mulVec_sub, (hmemF x).1 hx.1 u u.2,
        (hmemF x₀).1 hx₀ u u.2]
    let g : ↥(F.filter (fun x => crdE x = crdE x₀)) →
        {x : Fin 6 → ZMod 2 // ∀ M ∈ τ.range, w4 ((M : G4) : 𝕄₄) *ᵥ x = x} :=
      fun x => ⟨crdH ((x : Fin 10 → ZMod 2) - x₀), key x x.2⟩
    have hg : Function.Injective g := by
      intro x y hxy
      have h1 : crdH ((x : Fin 10 → ZMod 2) - x₀) = crdH ((y : Fin 10 → ZMod 2) - x₀) :=
        congrArg Subtype.val hxy
      rw [crdH_sub, crdH_sub, sub_left_inj] at h1
      have h2 := (Finset.mem_filter.1 x.2).2
      have h3 := (Finset.mem_filter.1 y.2).2
      exact Subtype.ext (eq_of_crd h1 (h2.trans h3.symm))
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  have hIle : I.card ≤ 16 := by
    calc I.card ≤ (Finset.univ : Finset (Fin 4 → ZMod 2)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 16 := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]; rfl
  have hI0 : ∀ k ∈ τ.ker, ((k : ↥X) : G5) ≠ 1 → ∀ h ∈ I,
      h = 0 ∨ h = colR (((k : ↥X) : G5) : 𝕄) := by
    intro k hk hk1 h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
    refine wedge_zero_cases _ _ (wedge_cond (hK k hk) ((hmemF x).1 hx _ k.2)) fun h0 => hk1 ?_
    exact colR_injective (hK k hk) R4.one_mem (h0.trans colR_one.symm)
  have hKle : Nat.card τ.ker ≤ 16 := by
    have hinj : Function.Injective fun k : ↥τ.ker => (⟨((k : ↥X) : G5), hK k k.2⟩ : ↥R4) :=
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun r : ↥R4 => (r : G5)) h))
    exact (Nat.card_le_card_of_injective _ hinj).trans card_R4_le
  have hKI : Nat.card τ.ker * I.card ≤ 16 ∧
      (16 ≤ Nat.card τ.ker * I.card → (τ.ker = ⊥ ∧ I.card = 16) ∨ Nat.card τ.ker = 16) := by
    by_cases hK1 : ∃ k₁ ∈ τ.ker, ((k₁ : ↥X) : G5) ≠ 1
    · obtain ⟨k₁, hk₁, hk₁1⟩ := hK1
      by_cases hK2 : ∃ k₂ ∈ τ.ker, ((k₂ : ↥X) : G5) ≠ 1 ∧ k₂ ≠ k₁
      · obtain ⟨k₂, hk₂, hk₂1, hk₂₁⟩ := hK2
        have hI1 : I.card ≤ 1 := by
          have h0 : ∀ a ∈ I, a = 0 := by
            intro a ha
            rcases hI0 k₁ hk₁ hk₁1 a ha with h | h
            · exact h
            rcases hI0 k₂ hk₂ hk₂1 a ha with h' | h'
            · exact h'
            exfalso
            apply hk₂₁
            exact Subtype.ext (colR_injective (hK k₂ hk₂) (hK k₁ hk₁) (h'.symm.trans h))
          rw [Finset.card_le_one]
          intro a ha b hb
          rw [h0 a ha, h0 b hb]
        refine ⟨?_, fun h16 => Or.inr ?_⟩
        · calc Nat.card τ.ker * I.card ≤ 16 * 1 := Nat.mul_le_mul hKle hI1
            _ = 16 := by norm_num
        · have : Nat.card τ.ker * I.card ≤ Nat.card τ.ker := by
            calc Nat.card τ.ker * I.card ≤ Nat.card τ.ker * 1 := Nat.mul_le_mul_left _ hI1
              _ = _ := mul_one _
          omega
      · push Not at hK2
        have hK2' : Nat.card τ.ker ≤ 2 := by
          have hinj : Function.Injective fun k : ↥τ.ker => decide (((k : ↥X) : G5) = 1) := by
            intro a b hab
            by_cases ha : ((a : ↥X) : G5) = 1 <;> by_cases hb : ((b : ↥X) : G5) = 1
            · exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
            · simp [ha, hb] at hab
            · simp [ha, hb] at hab
            · exact Subtype.ext ((hK2 a a.2 ha).trans (hK2 b b.2 hb).symm)
          have := Nat.card_le_card_of_injective _ hinj
          simpa using this
        have hI2 : I.card ≤ 2 := by
          have hsub : I ⊆ {0, colR (((k₁ : ↥X) : G5) : 𝕄)} := by
            intro a ha
            rcases hI0 k₁ hk₁ hk₁1 a ha with h | h
            · rw [h]; exact Finset.mem_insert_self _ _
            · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          exact (Finset.card_le_card hsub).trans Finset.card_le_two
        refine ⟨?_, fun h16 => ?_⟩
        · calc Nat.card τ.ker * I.card ≤ 2 * 2 := Nat.mul_le_mul hK2' hI2
            _ ≤ 16 := by norm_num
        · exfalso
          have : Nat.card τ.ker * I.card ≤ 2 * 2 := Nat.mul_le_mul hK2' hI2
          omega
    · push Not at hK1
      have hK0 : τ.ker = ⊥ := by
        rw [eq_bot_iff]
        intro k hk
        rw [Subgroup.mem_bot]
        exact Subtype.ext (hK1 k hk)
      have hK1' : Nat.card τ.ker = 1 := by rw [hK0, Subgroup.card_bot]
      refine ⟨by rw [hK1', one_mul]; exact hIle, fun h16 => Or.inl ⟨hK0, ?_⟩⟩
      rw [hK1', one_mul] at h16
      omega
  have hmain : Nat.card X * Nat.card (FixW X) ≤
      (Nat.card τ.range * n₄) * (Nat.card τ.ker * I.card) := by
    rw [hcard, hFW]
    calc Nat.card τ.ker * Nat.card τ.range * F.card ≤
        Nat.card τ.ker * Nat.card τ.range * (n₄ * I.card) := Nat.mul_le_mul_left _ hfib
      _ = (Nat.card τ.range * n₄) * (Nat.card τ.ker * I.card) := by ring
  refine ⟨hmain.trans ?_, fun hge hX1 => ?_⟩
  · calc (Nat.card τ.range * n₄) * (Nat.card τ.ker * I.card) ≤ 64 * 16 :=
        Nat.mul_le_mul h4 hKI.1
      _ = 2 ^ 10 := by norm_num
  have h16 : 16 ≤ Nat.card τ.ker * I.card := by
    by_contra hlt
    push Not at hlt
    have h1 : (Nat.card τ.range * n₄) * (Nat.card τ.ker * I.card) ≤ 64 * 15 :=
      Nat.mul_le_mul h4 (by omega)
    have : (64 : ℕ) * 15 < 2 ^ 10 := by norm_num
    omega
  rcases hKI.2 h16 with ⟨hK0, hI16⟩ | hK16
  ·
    exfalso
    apply hX1
    have hIuniv : I = Finset.univ :=
      Finset.eq_univ_of_card I (by rw [hI16, Fintype.card_fun, ZMod.card]; rfl)
    have htriv : ∀ u : ↥X, τ u = 1 := by
      intro u
      apply Subtype.ext
      rw [coe_topHomOf, Matrix.SpecialLinearGroup.coe_one]
      refine (Matrix.ext_iff_mulVec).2 fun h => ?_
      have hh : h ∈ I := by rw [hIuniv]; exact Finset.mem_univ h
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hh
      rw [one_mulVec, ← crdE_wedgeMat (hXU u.2), (hmemF x).1 hx u u.2]
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : ↥X) ∈ τ.ker := MonoidHom.mem_ker.2 (htriv _)
    rw [hK0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  ·
    have hinj : Function.Injective fun k : ↥τ.ker => (⟨((k : ↥X) : G5), hK k k.2⟩ : ↥R4) :=
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun r : ↥R4 => (r : G5)) h))
    have hbij := hinj.bijective_of_nat_card_le (by rw [hK16]; exact card_R4_le)
    have hRX : ∀ r ∈ R4, r ∈ X := by
      intro r hr
      obtain ⟨k, hk⟩ := hbij.2 ⟨r, hr⟩
      have : ((k : ↥X) : G5) = r := congrArg Subtype.val hk
      rw [← this]
      exact (k : ↥X).2
    have hXR : X ≤ R4 := fun u hu => mem_R4_of_comm (hXU hu) fun i h =>
      hc u hu _ (hRX _ (eT_mem_R4 i h))
    refine Subgroup.eq_of_le_of_card_ge hXR (card_R4_le.trans ?_)
    rw [hcard, hK16]
    have : 0 < Nat.card τ.range := Nat.card_pos
    omega

end CFSG.Quasithin.B42Ln
