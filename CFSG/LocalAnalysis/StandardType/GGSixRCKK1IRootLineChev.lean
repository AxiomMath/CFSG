module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusModels
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutRoots
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusMain
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.Blueprint.ChevalleyRootsInputs
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Open
open CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Balance
open CliffordAlgebra TauCeti.GLSymplecticFin

private theorem rckRLt1_pair_simplyLaced {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (hA : TauCeti.IsFiniteType A)
    (hlong : ∀ k, IsLongest hA ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, A j k = -1)
    {β : Fin r → ℤ} (hβ : β ∈ CFSG.LieType.RootSystem.roots hA ∅) :
    ∃ i, ChevAut.pair A β i = 1 ∨ ChevAut.pair A β i = -1 := by
  obtain ⟨i, hi⟩ := ChevAut.exists_odd_pair hA hlong hnb hβ
  have hb := ChevAut.abs_pair_le hA hlong hβ i
  rw [abs_le] at hb
  rw [Int.not_even_iff] at hi
  refine ⟨i, ?_⟩
  omega

private theorem rckRLt1_pair_simplyLaced_roots {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (hA : TauCeti.IsFiniteType A)
    (hlong : ∀ k, IsLongest hA ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, A j k = -1)
    {β : Fin r → ℤ} (hβ : β ∈ CFSG.LieType.RootSystem.roots hA ∅) :
    ∃ i, (∑ j, A i j * β j) = 1 ∨ (∑ j, A i j * β j) = 2 ∨
      (∑ j, A i j * β j) = -1 ∨ (∑ j, A i j * β j) = -2 := by
  obtain ⟨i, hi⟩ := rckRLt1_pair_simplyLaced hA hlong hnb hβ
  refine ⟨i, ?_⟩
  rcases hi with h | h
  · exact Or.inl (by simpa [ChevAut.pair] using h)
  · exact Or.inr (Or.inr (Or.inl (by simpa [ChevAut.pair] using h)))

private theorem rckRLt1_hnb_A {m : ℕ} (hm : 2 ≤ m) :
    ∀ k : Fin m, ∃ j : Fin m, CartanMatrix.A m j k = -1 := by
  intro k
  by_cases h : k.val + 1 < m
  · refine ⟨⟨k.val + 1, h⟩, ?_⟩
    rw [CartanMatrix.A, Matrix.of_apply,
      if_neg (Fin.ne_of_val_ne (by omega : k.val + 1 ≠ k.val)),
      if_pos (Or.inr (by simp))]
  · refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
    rw [CartanMatrix.A, Matrix.of_apply,
      if_neg (Fin.ne_of_val_ne (by omega : k.val - 1 ≠ k.val)),
      if_pos (Or.inl (by simp only [Fin.val_mk]; omega))]

private theorem rckRLt1_hnb_D {n : ℕ} (hn : 3 ≤ n) :
    ∀ k : Fin n, ∃ j : Fin n, cartanD n j k = -1 := by
  intro k
  by_cases h : k.val + 1 < n
  · by_cases h2 : k.val + 2 < n
    · refine ⟨⟨k.val + 1, h⟩, ?_⟩
      rw [cartanD, Matrix.of_apply,
        if_neg (Fin.ne_of_val_ne (by omega : k.val + 1 ≠ k.val)),
        if_pos (Or.inr (Or.inl ⟨rfl, by omega⟩))]
    · refine ⟨⟨n - 3, by omega⟩, ?_⟩
      rw [cartanD, Matrix.of_apply,
        if_neg (Fin.ne_of_val_ne (by omega : n - 3 ≠ k.val)),
        if_pos (Or.inl ⟨by simp only [Fin.val_mk]; omega, by omega⟩)]
  · refine ⟨⟨n - 3, by omega⟩, ?_⟩
    rw [cartanD, Matrix.of_apply,
      if_neg (Fin.ne_of_val_ne (by omega : n - 3 ≠ k.val)),
      if_pos (Or.inr (Or.inr (Or.inl ⟨by simp only [Fin.val_mk]; omega, by omega⟩)))]

private theorem rckRLt1_rootLineAll_of_pair
    {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hcard : Nat.card F = 2 ^ f)
    (hpair : ∀ β ∈ D.roots, ∃ i, (∑ j, D.cartan i j * β j) = 1 ∨
      (∑ j, D.cartan i j * β j) = 2 ∨ (∑ j, D.cartan i j * β j) = -1 ∨
      (∑ j, D.cartan i j * β j) = -2)
    {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D F x C O) :
    RCKRootLineAll ⟨K, D⟩ f := by
  intro β hβ _
  obtain ⟨i, hi⟩ := hpair β hβ
  obtain ⟨ε, -, hsc⟩ := rckRootLine_of_chevalleyExtras hE hβ i hi
  exact ⟨F, inferInstance, inferInstance, ε, hcard, hsc⟩

private theorem rckRLt1_PSL {m f : ℕ} (hm : 2 ≤ m) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ f)
    {x : (Fin m → ℤ) → F → Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    {C : (Fin m → ℤ) → (Fin m → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (SpecialLinear.rootDatum m F).isFiniteType
      (SpecialLinear.rootDatum m F).divisible)}
    (hE : ChevalleyExtras (SpecialLinear.rootDatum m F) F x C O) :
    0 < (SpecialLinear.rootDatum m F).rank ∧
      RCKRootLineAll ⟨Matrix.SpecialLinearGroup (Fin (m + 1)) F,
        SpecialLinear.rootDatum m F⟩ f := by
  refine ⟨by show 0 < m; omega, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  have hβ' : β ∈ CFSG.LieType.RootSystem.roots (SpecialLinear.rootDatum m F).isFiniteType ∅ := hβ
  exact rckRLt1_pair_simplyLaced_roots _ 
    (fun k => isLongest_single_A (m := m) (by omega) rfl
      (SpecialLinear.rootDatum m F).isFiniteType k)
    (rckRLt1_hnb_A hm) hβ'

private theorem rckRLt1_POmegaPlus {n f : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hcard : Nat.card F = 2 ^ f)
    {x : (Fin n → ℤ) → F → spinGroup (Spin.quadPlus n F)}
    {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (Spin.plusDatum n F hn).isFiniteType
      (Spin.plusDatum n F hn).divisible)}
    (hE : ChevalleyExtras (Spin.plusDatum n F hn) F x C O) :
    0 < (Spin.plusDatum n F hn).rank ∧
      RCKRootLineAll ⟨spinGroup (Spin.quadPlus n F), Spin.plusDatum n F hn⟩ f := by
  refine ⟨by show 0 < n; omega, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  have hβ' : β ∈ CFSG.LieType.RootSystem.roots (Spin.plusDatum n F hn).isFiniteType ∅ := hβ
  exact rckRLt1_pair_simplyLaced_roots _
    (fun k => isLongest_single_cartanD hn rfl (Spin.plusDatum n F hn).isFiniteType k)
    (rckRLt1_hnb_D (by omega)) hβ'

private theorem rckRLt1_E6 {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ f)
    {x : (Fin 6 → ℤ) → F → ↥(e6Data_valid.minGroup F)}
    {C : (Fin 6 → ℤ) → (Fin 6 → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (e6Datum F).isFiniteType (e6Datum F).divisible)}
    (hE : ChevalleyExtras (e6Datum F) F x C O) :
    0 < (e6Datum F).rank ∧
      RCKRootLineAll ⟨↥(e6Data_valid.minGroup F), e6Datum F⟩ f := by
  refine ⟨by show 0 < 6; norm_num, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  have hβ' : β ∈ CFSG.LieType.RootSystem.roots (e6Datum F).isFiniteType ∅ := hβ
  exact rckRLt1_pair_simplyLaced_roots _
    (fun k => isLongest_single_E6 (M := (e6Datum F).cartan) rfl (e6Datum F).isFiniteType k)
    ChevAut.cartanE6_nb hβ'

private theorem rckRLt1_E7 {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ f)
    {x : (Fin 7 → ℤ) → F → ↥(e7Data_valid.minGroup F)}
    {C : (Fin 7 → ℤ) → (Fin 7 → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (e7Datum F).isFiniteType (e7Datum F).divisible)}
    (hE : ChevalleyExtras (e7Datum F) F x C O) :
    0 < (e7Datum F).rank ∧
      RCKRootLineAll ⟨↥(e7Data_valid.minGroup F), e7Datum F⟩ f := by
  refine ⟨by show 0 < 7; norm_num, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  have hβ' : β ∈ CFSG.LieType.RootSystem.roots (e7Datum F).isFiniteType ∅ := hβ
  exact rckRLt1_pair_simplyLaced_roots _
    (fun k => isLongest_single_E7 (M := (e7Datum F).cartan) rfl (e7Datum F).isFiniteType k)
    ChevAut.cartanE7_nb hβ'

private theorem rckRLt1_E8 {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ f)
    {x : (Fin 8 → ℤ) → F → ↥(adjointGroup .E8 F)}
    {C : (Fin 8 → ℤ) → (Fin 8 → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (e8Datum F).isFiniteType (e8Datum F).divisible)}
    (hE : ChevalleyExtras (e8Datum F) F x C O) :
    0 < (e8Datum F).rank ∧
      RCKRootLineAll ⟨↥(adjointGroup .E8 F), e8Datum F⟩ f := by
  refine ⟨by show 0 < 8; norm_num, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  have hβ' : β ∈ CFSG.LieType.RootSystem.roots (e8Datum F).isFiniteType ∅ := hβ
  exact rckRLt1_pair_simplyLaced_roots _
    (fun k => isLongest_single_E8 (M := (e8Datum F).cartan) rfl (e8Datum F).isFiniteType k)
    ChevAut.cartanE8_nb hβ'

private def rckRLt1_f4PairCheck : Bool :=
  (List.range (Tag.rootCertificate Tag.F4).roots.length).all fun k =>
    (List.finRange 4).any fun i =>
      (ChevAut.pair (Tag.cartan .F4) ((Tag.rootCertificate Tag.F4).root k) i == 1) ||
      (ChevAut.pair (Tag.cartan .F4) ((Tag.rootCertificate Tag.F4).root k) i == 2) ||
      (ChevAut.pair (Tag.cartan .F4) ((Tag.rootCertificate Tag.F4).root k) i == -1) ||
      (ChevAut.pair (Tag.cartan .F4) ((Tag.rootCertificate Tag.F4).root k) i == -2)

private theorem rckRLt1_f4PairCheck_eq_true :
    rckRLt1_f4PairCheck = true := by
  decide +kernel

private theorem rckRLt1_pair_f4 {β : Fin 4 → ℤ} (hβ : IsRoot .F4 β) :
    ∃ i : Fin 4, ChevAut.pair (Tag.cartan .F4) β i = 1 ∨
      ChevAut.pair (Tag.cartan .F4) β i = 2 ∨ ChevAut.pair (Tag.cartan .F4) β i = -1 ∨
      ChevAut.pair (Tag.cartan .F4) β i = -2 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβ
  have hc := rckRLt1_f4PairCheck_eq_true
  simp only [rckRLt1_f4PairCheck, List.all_eq_true, List.mem_range] at hc
  have hk' := hc k hk
  simp only [List.any_eq_true, List.mem_finRange, Bool.or_eq_true, beq_iff_eq,
    true_and, or_assoc] at hk'
  exact hk'

private theorem rckRLt1_F4 {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ f)
    {x : (Fin 4 → ℤ) → F → ↥(adjointGroup .F4 F)}
    {C : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (f4Datum F).isFiniteType (f4Datum F).divisible)}
    (hE : ChevalleyExtras (f4Datum F) F x C O) :
    0 < (f4Datum F).rank ∧ RCKRootLineAll ⟨↥(adjointGroup .F4 F), f4Datum F⟩ f := by
  refine ⟨by show 0 < 4; norm_num, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  have hβ' : IsRoot .F4 β := mem_adjDatum_roots.mp hβ
  obtain ⟨i, hi⟩ := rckRLt1_pair_f4 hβ'
  refine ⟨i, ?_⟩
  rcases hi with h | h | h | h
  · exact Or.inl (by simpa [ChevAut.pair] using h)
  · exact Or.inr (Or.inl (by simpa [ChevAut.pair] using h))
  · exact Or.inr (Or.inr (Or.inl (by simpa [ChevAut.pair] using h)))
  · exact Or.inr (Or.inr (Or.inr (by simpa [ChevAut.pair] using h)))

private def rckRLt1_toStdLin (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := toStd n
  map_add' v w := by
    funext a
    simp only [toStd, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext a
    simp only [toStd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem rckRLt1_toStdLin_apply (n : ℕ) (v : Fin n → ℤ) :
    rckRLt1_toStdLin n v = toStd n v := rfl

private theorem rckRLt1_coroot_cartanC_of_lt {n : ℕ} {k : Fin n} (h : k.val + 1 < n)
    (v : Fin n → ℤ) :
    coroot (cartanC n) k v = toStd n v k - toStd n v ⟨k.val + 1, h⟩ := by
  have key : coroot (cartanC n) k =
      ((LinearMap.proj k : (Fin n → ℤ) →ₗ[ℤ] ℤ) -
        LinearMap.proj (⟨k.val + 1, h⟩ : Fin n)).comp (rckRLt1_toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, rckRLt1_toStdLin_apply, toStd, cartanC,
      Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem rckRLt1_coroot_cartanC_of_not_lt {n : ℕ} {k : Fin n} (h : ¬k.val + 1 < n)
    (v : Fin n → ℤ) :
    coroot (cartanC n) k v = toStd n v k := by
  have key : coroot (cartanC n) k = (LinearMap.proj k).comp (rckRLt1_toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single, coroot_single,
      rckRLt1_toStdLin_apply, toStd, cartanC, Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem rckRLt1_pair_cartanC {n : ℕ} (hn : 2 ≤ n) {β : Fin n → ℤ}
    (hβ : β ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅) :
    ∃ i : Fin n, (∑ j, cartanC n i j * β j) = 1 ∨
      (∑ j, cartanC n i j * β j) = 2 ∨
      (∑ j, cartanC n i j * β j) = -1 ∨
      (∑ j, cartanC n i j * β j) = -2 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  cases r with
  | positiveLong a =>
    refine ⟨a, Or.inr (Or.inl ?_)⟩
    by_cases ha : a.val + 1 < n
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_lt ha, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_not_lt ha, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
  | negativeLong a =>
    refine ⟨a, Or.inr (Or.inr (Or.inr ?_))⟩
    by_cases ha : a.val + 1 < n
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_lt ha, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_not_lt ha, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
  | difference a b hab =>
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨b, Or.inr (Or.inr (Or.inl ?_))⟩
      by_cases hb : b.val + 1 < n
      · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_lt hb, ← hr]
        simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
      · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_not_lt hb, ← hr]
        simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
    · refine ⟨a, Or.inl ?_⟩
      by_cases ha : a.val + 1 < n
      · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_lt ha, ← hr]
        simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
      · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_not_lt ha, ← hr]
        simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
  | positiveSum a b hab =>
    refine ⟨b, Or.inl ?_⟩
    by_cases hb : b.val + 1 < n
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_lt hb, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_not_lt hb, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
  | negativeSum a b hab =>
    refine ⟨b, Or.inr (Or.inr (Or.inl ?_))⟩
    by_cases hb : b.val + 1 < n
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_lt hb, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega
    · rw [← coroot_apply, rckRLt1_coroot_cartanC_of_not_lt hb, ← hr]
      simp [stdVec, Pi.single_apply, Fin.ext_iff] <;> (try split_ifs) <;> omega

private theorem rckRLt1_PSp {n f : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ f)
    {x : (Fin n → ℤ) → F → StatedSp n F}
    {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (Symplectic.rootDatum n F).isFiniteType
      (Symplectic.rootDatum n F).divisible)}
    (hE : ChevalleyExtras (Symplectic.rootDatum n F) F x C O) :
    0 < (Symplectic.rootDatum n F).rank ∧
      RCKRootLineAll ⟨StatedSp n F, Symplectic.rootDatum n F⟩ f := by
  refine ⟨by show 0 < n; omega, rckRLt1_rootLineAll_of_pair hcard ?_ hE⟩
  intro β hβ
  exact rckRLt1_pair_cartanC hn hβ

theorem rckK1I_rootLine_chev
    {t : StatedLieTag} {n f : ℕ}
    (ht : (t = .PSL ∧ 3 ≤ n) ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) :
    0 < (ggU t n f).D.rank ∧ RCKRootLineAll (ggU t n f) f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  rcases ht with ⟨rfl, hn3⟩ | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 2 ≤ m := by omega
    obtain ⟨x, C, O, hE⟩ := exists_chevalleyExtras_model .PSL (m + 1) f hadm
      (Or.inl ⟨rfl, by omega⟩)
    change 0 < (SpecialLinear.rootDatum m (GaloisField 2 f)).rank ∧
      RCKRootLineAll (⟨Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
        SpecialLinear.rootDatum m (GaloisField 2 f)⟩ : LieUniversal) f
    change ChevalleyExtras (SpecialLinear.rootDatum m (GaloisField 2 f))
      (GaloisField 2 f) x C O at hE
    exact rckRLt1_PSL hm (GaloisField.card 2 f (by omega)) hE
  ·
    have hn : 2 ≤ n := hadm.2.2.1
    obtain ⟨x, C, O, hE⟩ := exists_chevalleyExtras_model_nonSimplyLaced (p := 2) .PSp n f
      (Or.inl ⟨rfl, hn⟩)
    change 0 < (Symplectic.rootDatum n (GaloisField 2 f)).rank ∧
      RCKRootLineAll (⟨StatedSp n (GaloisField 2 f),
        Symplectic.rootDatum n (GaloisField 2 f)⟩ : LieUniversal) f
    change ChevalleyExtras (Symplectic.rootDatum n (GaloisField 2 f))
      (GaloisField 2 f) x C O at hE
    exact rckRLt1_PSp hn (GaloisField.card 2 f (by omega)) hE
  ·
    have hn4 : 4 ≤ n := hadm.2.2
    have hn : 3 ≤ n := by omega
    have hext := exists_chevalleyExtras_model .POmegaPlus n f hadm (Or.inr (Or.inl rfl))
    change ∃ x C O, ChevalleyExtras
      (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n 2 f Fact.out).D
      (GaloisField 2 f) x C O at hext
    rw [CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn] at hext
    obtain ⟨x, C, O, hE⟩ := hext
    rw [show ggU .POmegaPlus n f =
        (⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn⟩ : LieUniversal) from by
      simp only [ggU, lieUniversal, dif_pos hn]]
    exact rckRLt1_POmegaPlus hn (GaloisField.card 2 f (by omega)) hE
  ·
    obtain ⟨x, C, O, hE⟩ := exists_chevalleyExtras_model_nonSimplyLaced (p := 2) .F4 n f
      (Or.inr (Or.inr rfl))
    change 0 < (f4Datum (GaloisField 2 f)).rank ∧
      RCKRootLineAll (⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f)),
        f4Datum (GaloisField 2 f)⟩ : LieUniversal) f
    change ChevalleyExtras (f4Datum (GaloisField 2 f)) (GaloisField 2 f) x C O at hE
    exact rckRLt1_F4 (GaloisField.card 2 f (by omega)) hE
  ·
    obtain ⟨x, C, O, hE⟩ := exists_chevalleyExtras_model .E6 n f hadm
      (Or.inr (Or.inr (Or.inl rfl)))
    change 0 < (e6Datum (GaloisField 2 f)).rank ∧
      RCKRootLineAll (⟨↥(e6Data_valid.minGroup (GaloisField 2 f)),
        e6Datum (GaloisField 2 f)⟩ : LieUniversal) f
    change ChevalleyExtras (e6Datum (GaloisField 2 f)) (GaloisField 2 f) x C O at hE
    exact rckRLt1_E6 (GaloisField.card 2 f (by omega)) hE
  ·
    obtain ⟨x, C, O, hE⟩ := exists_chevalleyExtras_model .E7 n f hadm
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    change 0 < (e7Datum (GaloisField 2 f)).rank ∧
      RCKRootLineAll (⟨↥(e7Data_valid.minGroup (GaloisField 2 f)),
        e7Datum (GaloisField 2 f)⟩ : LieUniversal) f
    change ChevalleyExtras (e7Datum (GaloisField 2 f)) (GaloisField 2 f) x C O at hE
    exact rckRLt1_E7 (GaloisField.card 2 f (by omega)) hE
  ·
    obtain ⟨x, C, O, hE⟩ := exists_chevalleyExtras_model .E8 n f hadm
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    change 0 < (e8Datum (GaloisField 2 f)).rank ∧
      RCKRootLineAll (⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f)),
        e8Datum (GaloisField 2 f)⟩ : LieUniversal) f
    change ChevalleyExtras (e8Datum (GaloisField 2 f)) (GaloisField 2 f) x C O at hE
    exact rckRLt1_E8 (GaloisField.card 2 f (by omega)) hE

end CFSG.StandardType.RCKK1I
