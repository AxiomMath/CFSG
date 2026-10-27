module

public import CFSG.RankThree.PartOne.KS.ScalFiveBasic
public import CFSG.RankThree.PartOne.KS.ScalFiveDefs

public section

namespace CFSG.RankThree.PartOne.KS.ScalFive

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.Monster.B.Pinned
open scoped Matrix

section Sound

variable {M V : Type} {O : Ops M V} {p d : ℕ} {Sp : OpsSpec O p d} {G : Type*} [Group G]
  {φ : G →* Matrix (Fin d) (Fin d) (ZMod p)}

theorem eq_of_toMat (hφ : Function.Injective φ) {g h : G} {X Y : M} (hX : Sp.WF X)
    (hY : Sp.WF Y) (hg : Sp.toMat X = φ g) (hh : Sp.toMat Y = φ h) (e : O.eq X Y = true) :
    g = h :=
  hφ (by rw [← hg, ← hh]; exact Sp.toMat_eq hX hY e)

theorem powOK_sound (hφ : Function.Injective φ) {g : G} {X : M × M} (hg : Rep Sp φ g X) {e : ℕ}
    (h : powOK O X.1 e = true) : g ^ e = 1 := by
  obtain ⟨hw, -, ht, -⟩ := Rep.pow hg e
  exact eq_of_toMat hφ hw Sp.one_wf ht (by rw [Sp.toMat_one, map_one]) h

theorem commOK_sound (hφ : Function.Injective φ) {g h : G} {X Y : M × M} (hg : Rep Sp φ g X)
    (hh : Rep Sp φ h Y) (hc : commOK O X.1 Y.1 = true) : g * h = h * g := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul hg hh
  obtain ⟨hw2, -, ht2, -⟩ := Rep.mul hh hg
  exact eq_of_toMat hφ hw1 hw2 ht1 ht2 hc

theorem neOne_sound {g : G} {X : M × M} (hg : Rep Sp φ g X) {t : ℕ}
    (h : neOne O X.1 t = true) : g ≠ 1 := by
  intro hg1
  have h1 := Sp.toVec_ne h
  apply h1
  rw [Sp.toVec_vmul (Sp.unit_wf t) hg.1, hg.2.2.1, hg1, map_one, Matrix.vecMul_one]

theorem foldProd_sound {n : ℕ} {q : Fin n → G} {Q : Fin n → M × M}
    (hq : ∀ j, Rep Sp φ (q j) (Q j)) (a : Fin n → ℕ) (l : List (Fin n)) :
    Sp.WF (l.foldr (fun j acc => O.mul (O.pow (Q j).1 (a j)) acc) O.one) ∧
      Sp.toMat (l.foldr (fun j acc => O.mul (O.pow (Q j).1 (a j)) acc) O.one) =
        φ ((l.map fun j => q j ^ a j).prod) := by
  induction l with
  | nil =>
    refine ⟨Sp.one_wf, ?_⟩
    simp only [List.foldr_nil, List.map_nil, List.prod_nil]
    rw [Sp.toMat_one, map_one]
  | cons j l ih =>
    have hp := Rep.pow (hq j) (a j)
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    refine ⟨Sp.mul_wf hp.1 ih.1, ?_⟩
    rw [Sp.toMat_mul hp.1 ih.1, hp.2.2.1, ih.2, map_mul]

theorem prodPow_sound {n : ℕ} {q : Fin n → G} {z : G} {Q : Fin n → M × M} {Z : M × M}
    (hq : ∀ j, Rep Sp φ (q j) (Q j)) (hz : Rep Sp φ z Z) (a : Fin n → ℕ) (c : ℕ) :
    Sp.WF (prodPow O (fun j => (Q j).1) Z.1 a c) ∧
      Sp.toMat (prodPow O (fun j => (Q j).1) Z.1 a c) =
        φ ((List.ofFn fun j => q j ^ a j).prod * z ^ c) := by
  have h1 := foldProd_sound (O := O) (Sp := Sp) hq a (List.finRange n)
  have hpz := Rep.pow hz c
  rw [List.ofFn_eq_map]
  exact ⟨Sp.mul_wf h1.1 hpz.1, by
    unfold prodPow
    rw [Sp.toMat_mul h1.1 hpz.1, h1.2, hpz.2.2.1, map_mul]⟩

theorem bcomm_sound (hφ : Function.Injective φ) {g h z : G} {X Y Z : M × M} (hg : Rep Sp φ g X)
    (hh : Rep Sp φ h Y) (hz : Rep Sp φ z Z) {e : ℕ}
    (hc : O.eq (pBcomm O X Y) (O.pow Z.1 e) = true) : bcomm g h = z ^ e := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul (Rep.mul hg.inv hh.inv) (Rep.mul hg hh)
  obtain ⟨hw2, -, ht2, -⟩ := Rep.pow hz e
  have := eq_of_toMat hφ hw1 hw2 ht1 ht2 hc
  rw [← this, bcomm, mul_assoc, mul_assoc]

theorem bcomm_prodPow_sound (hφ : Function.Injective φ) {g h z : G} {X Y Z : M × M}
    {n : ℕ} {q : Fin n → G} {Q : Fin n → M × M} (hg : Rep Sp φ g X) (hh : Rep Sp φ h Y)
    (hq : ∀ j, Rep Sp φ (q j) (Q j)) (hz : Rep Sp φ z Z) (a : Fin n → ℕ) (c : ℕ)
    (hc : O.eq (pBcomm O X Y) (prodPow O (fun j => (Q j).1) Z.1 a c) = true) :
    bcomm g h = (List.ofFn fun j => q j ^ a j).prod * z ^ c := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul (Rep.mul hg.inv hh.inv) (Rep.mul hg hh)
  obtain ⟨hw2, ht2⟩ := prodPow_sound hq hz a c
  have := eq_of_toMat hφ hw1 hw2 ht1 ht2 hc
  rw [← this, bcomm, mul_assoc, mul_assoc]

theorem conj_sound (hφ : Function.Injective φ) {g z : G} {n : ℕ} {q : Fin n → G} {X Z : M × M}
    {Q : Fin n → M × M} (hg : Rep Sp φ g X) (hq : ∀ j, Rep Sp φ (q j) (Q j))
    (hz : Rep Sp φ z Z) (i : Fin n) (a : Fin n → ℕ) (c : ℕ)
    (hc : O.eq (pConj O X (Q i)) (prodPow O (fun j => (Q j).1) Z.1 a c) = true) :
    g⁻¹ * q i * g = (List.ofFn fun j => q j ^ a j).prod * z ^ c := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul (Rep.mul hg.inv (hq i)) hg
  obtain ⟨hw2, ht2⟩ := prodPow_sound hq hz a c
  have := eq_of_toMat hφ hw1 hw2 ht1 ht2 hc
  rw [← this, mul_assoc]

theorem conjScalar_sound (hφ : Function.Injective φ) {g z : G} {n : ℕ} {q : Fin n → G}
    {X Z : M × M} {Q : Fin n → M × M} (hg : Rep Sp φ g X) (hq : ∀ j, Rep Sp φ (q j) (Q j))
    (hz : Rep Sp φ z Z) (i : Fin n) (e c : ℕ)
    (hc : O.eq (pConj O X (Q i)) (O.mul (O.pow (Q i).1 e) (O.pow Z.1 c)) = true) :
    g⁻¹ * q i * g = q i ^ e * z ^ c := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.mul (Rep.mul hg.inv (hq i)) hg
  obtain ⟨hw2, -, ht2, -⟩ := Rep.mul (Rep.pow (hq i) e) (Rep.pow hz c)
  have := eq_of_toMat hφ hw1 hw2 ht1 ht2 hc
  rw [← this, mul_assoc]

theorem pow_prodPow_sound (hφ : Function.Injective φ) {g z : G} {n : ℕ} {q : Fin n → G}
    {X Z : M × M} {Q : Fin n → M × M} (hg : Rep Sp φ g X) (hq : ∀ j, Rep Sp φ (q j) (Q j))
    (hz : Rep Sp φ z Z) (e : ℕ) (a : Fin n → ℕ) (c : ℕ)
    (hc : O.eq (O.pow X.1 e) (prodPow O (fun j => (Q j).1) Z.1 a c) = true) :
    g ^ e = (List.ofFn fun j => q j ^ a j).prod * z ^ c := by
  obtain ⟨hw1, -, ht1, -⟩ := Rep.pow hg e
  obtain ⟨hw2, ht2⟩ := prodPow_sound hq hz a c
  exact eq_of_toMat hφ hw1 hw2 ht1 ht2 hc

end Sound

theorem allFin_iff {n : ℕ} {f : Fin n → Bool} : allFin n f = true ↔ ∀ i, f i = true := by
  simp [allFin, List.all_eq_true, List.mem_finRange]

section Rels

variable {M V : Type} {O : Ops M V} {p d : ℕ} {Sp : OpsSpec O p d} {G : Type*} [Group G]
  {φ : G →* Matrix (Fin d) (Fin d) (ZMod p)} [Inhabited M]

@[expose] def Data.Mm {n : ℕ} (D : Data n) : Matrix (Fin n) (Fin n) (ZMod 5) :=
  Matrix.of fun i j => (D.exM i j : ZMod 5)

@[expose] def Data.Sm {n : ℕ} (D : Data n) : Matrix (Fin n) (Fin n) (ZMod 5) :=
  Matrix.of fun i j => (D.exS i j : ZMod 5)

theorem relsOK_sound {n : ℕ} (D : Data n) {R : ℕ → G} {Rn : Array (M × M)}
    (hφ : Function.Injective φ) (hR : ∀ r, r < D.nreg → Rep Sp φ (R r) Rn[r]!)
    (hQlt : ∀ j, D.iQ j < D.nreg) (hZlt : D.iZ < D.nreg) (hSlt : D.iS < D.nreg)
    (hTlt : D.iT < D.nreg) (hM : ∀ i j, D.exM i j < 5) (hS : ∀ i j, D.exS i j < 5)
    (hr : D.rT < 5) (hdet : IsUnit D.Mm.det) {i₀ j₀ : Fin n} (hi : D.exM i₀ j₀ = 1)
    (h : relsOK O D Rn = true) :
    ScalRel (fun j => R (D.iQ j)) (R D.iZ) (R D.iS) (R D.iT) D.Mm D.Sm i₀ j₀ D.cs
      (D.rT : ZMod 5) D.ct := by
  have := fact5
  have hz := hR _ hZlt
  have hs := hR _ hSlt
  have ht := hR _ hTlt
  have hq : ∀ j, Rep Sp φ (R (D.iQ j)) Rn[D.iQ j]! := fun j => hR _ (hQlt j)
  unfold relsOK at h
  simp only [Bool.and_eq_true, allFin_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz5, hzne⟩, hqpc⟩, hbc⟩, hcs⟩, hct⟩, hs5⟩, ht4⟩, hts⟩ := h
  have hbq : ∀ i j, bcomm (R (D.iQ i)) (R (D.iQ j)) = R D.iZ ^ D.exM i j :=
    fun i j => bcomm_sound hφ (hq i) (hq j) hz (hbc i j)
  have hz_eq : bcomm (R (D.iQ i₀)) (R (D.iQ j₀)) = R D.iZ := by
    rw [hbq i₀ j₀, hi]
    exact pow_one _
  have hmemz : R D.iZ ∈ QG (fun j => R (D.iQ j)) := by
    rw [← hz_eq]
    unfold bcomm
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i₀, rfl⟩))
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨j₀, rfl⟩)))
      (Subgroup.subset_closure ⟨i₀, rfl⟩)) (Subgroup.subset_closure ⟨j₀, rfl⟩)
  refine ⟨⟨fun i => powOK_sound hφ (hq i) (hqpc i).1, ?_,
    fun i => commOK_sound hφ (hq i) hz (hqpc i).2, fun i j => ?_, hdet, hmemz⟩, hz_eq,
    fun i => ?_, fun i => ?_, ?_, powOK_sound hφ ht ht4, ?_⟩
  · exact orderOf_eq_prime (powOK_sound hφ hz hz5) (neOne_sound hz hzne)
  · rw [hbq i j]
    show _ = _ ^ (((D.exM i j : ℕ) : ZMod 5)).val
    rw [ZMod.val_natCast_of_lt (hM i j)]
  · have := conj_sound hφ hs hq hz i (D.exS i) (D.cs i) (hcs i)
    have hval : ∀ j, (((D.exS i j : ℕ) : ZMod 5)).val = D.exS i j :=
      fun j => ZMod.val_natCast_of_lt (hS i j)
    simpa only [Data.Sm, Matrix.of_apply, hval] using this
  · have := conjScalar_sound hφ ht hq hz i D.rT (D.ct i) (hct i)
    rwa [ZMod.val_natCast_of_lt hr]
  · rw [pow_prodPow_sound hφ hs hq hz 5 D.e5 D.c5 hs5]
    exact prod_mem_of_mem_z hmemz _ _
  · have := bcomm_prodPow_sound hφ ht hs hq hz D.eTS D.cTS hts
    rw [show (R D.iT)⁻¹ * (R D.iS)⁻¹ * R D.iT * R D.iS = bcomm (R D.iT) (R D.iS) from rfl, this]
    exact prod_mem_of_mem_z hmemz _ _

end Rels

end CFSG.RankThree.PartOne.KS.ScalFive
