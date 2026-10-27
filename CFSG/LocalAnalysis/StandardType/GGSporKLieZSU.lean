module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSUEmb
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSpCent
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZQuot
import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUAlg
import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.StandardType.ClassicalBlocks Matrix

private lemma l937z_suu_scalar_units_injective {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
  intro c d h
  have h' : Matrix.scalar (Fin n) (c : K) = Matrix.scalar (Fin n) (d : K) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
  let i : Fin n := ⟨0, hn⟩
  have h2 := congrFun (congrFun h' i) i
  apply Units.ext
  simpa [Matrix.scalar_apply] using h2

private lemma l937z_suu_scalar_step {K : Type} [Field K] {n q : ℕ} (hn : 1 ≤ n)
    {fb : K →+* K} (hfbq : ∀ x : K, fb x = x ^ q) {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n q K) :
    fb (c : K) * (c : K) = 1 := by
  have h1 := (CFSG.HardMathSupport.Foote.ModuleExclusions.unitary_of_mem_statedSU
    fb hfbq hc).1
  rw [Matrix.GeneralLinearGroup.coe_scalar] at h1
  have hmap : (Matrix.scalar (Fin n) (c : K)).map (⇑fb) =
      Matrix.scalar (Fin n) (fb (c : K)) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply, h]
  rw [hmap, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at h1
  let i : Fin n := ⟨0, hn⟩
  have h2 := congrFun (congrFun h1 i) i
  simpa using h2

private lemma l937z_suu_map_centralizer_singleton {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e a} : Set H) := by
  apply le_antisymm
  · simpa [Set.image_singleton] using
      Subgroup.map_centralizer_le_centralizer_image ({a} : Set G) e.toMonoidHom
  · rintro y hy
    rw [Subgroup.mem_map]
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

private noncomputable def l937z_suu_centralizerMulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (a : G) :
    ↥(Subgroup.centralizer ({a} : Set G)) ≃* ↥(Subgroup.centralizer ({e a} : Set H)) :=
  (MulEquiv.subgroupMap e (Subgroup.centralizer ({a} : Set G))).trans
    (MulEquiv.subgroupCongr (l937z_suu_map_centralizer_singleton e a))

private lemma l937z_suu_comap_centralizer_subtype {G : Type*} [Group G] (H : Subgroup G)
    (a : ↥H) :
    (Subgroup.centralizer ({(a : G)} : Set G)).comap H.subtype =
      Subgroup.centralizer ({a} : Set ↥H) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

private lemma l937z_suu_map_centralizer_subgroupOf {G : Type*} [Group G] {P : Subgroup G}
    (a : ↥P) :
    (Subgroup.centralizer ({a} : Set ↥P)).map P.subtype =
      Subgroup.centralizer ({(a : G)} : Set G) ⊓ P := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, z.2⟩
    change z ∈ Subgroup.centralizer ({a} : Set ↥P) at hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact congrArg Subtype.val hz
  · rintro hg
    rw [Subgroup.mem_inf] at hg
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hg.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact Subtype.ext hg.1

private lemma l937z_suu_centralizer_mul_eq {G : Type*} [Group G] {y t : G} {q : ℕ}
    (hcomm : Commute y t) (hy : orderOf y = 7) (ht : orderOf t = q + 1)
    (hcop : Nat.Coprime 7 (q + 1)) (hq1 : 1 < q + 1) :
    Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) =
      Subgroup.centralizer ({y * t} : Set G) := by
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm (by norm_num : 1 < 7)
  obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq1
  have hyu : y ^ ((q + 1) * u) = y := by
    rw [← pow_mod_orderOf y ((q + 1) * u), hy, hu, pow_one]
  have htv : t ^ ((q + 1) * u) = 1 := by
    rw [pow_mul, ← ht, pow_orderOf_eq_one, one_pow]
  have hy_b : y = (y * t) ^ ((q + 1) * u) := by
    rw [hcomm.mul_pow, hyu, htv, mul_one]
  have htv' : t ^ (7 * v) = t := by
    rw [← pow_mod_orderOf t (7 * v), ht, hv, pow_one]
  have hyv : y ^ (7 * v) = 1 := by
    rw [pow_mul, ← hy, pow_orderOf_eq_one, one_pow]
  have ht_b : t = (y * t) ^ (7 * v) := by
    rw [hcomm.mul_pow, hyv, htv', one_mul]
  apply le_antisymm
  · rintro g ⟨hgy, hgt⟩
    change g ∈ Subgroup.centralizer ({y} : Set G) at hgy
    change g ∈ Subgroup.centralizer ({t} : Set G) at hgt
    rw [Subgroup.mem_centralizer_singleton_iff] at hgy hgt
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * (y * t) = (g * y) * t := (mul_assoc g y t).symm
      _ = (y * g) * t := by rw [hgy]
      _ = y * (g * t) := mul_assoc y g t
      _ = y * (t * g) := by rw [hgt]
      _ = y * t * g := (mul_assoc y t g).symm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_inf]
    constructor
    · have hb : Commute g (y * t) := hg
      have : Commute g y := by
        rw [hy_b]
        exact hb.pow_right ((q + 1) * u)
      rwa [Subgroup.mem_centralizer_singleton_iff]
    · have hb : Commute g (y * t) := hg
      have : Commute g t := by
        rw [ht_b]
        exact hb.pow_right (7 * v)
      rwa [Subgroup.mem_centralizer_singleton_iff]

private lemma l937z_suu_map_pCoreOf_injective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) (K : Subgroup G) :
    (pCoreOf 2 K).map φ = pCoreOf 2 (K.map φ) := by
  rw [pCoreOf, pCoreOf, Subgroup.map_map]
  have he := pCore_map_iso 2 (Subgroup.equivMapOfInjective K φ hφ)
  rw [← he, Subgroup.map_map]
  congr 1

private lemma l937z_suu_map_pCoreOf_subgroupOf {G : Type*} [Group G] {X N : Subgroup G}
    (h : X ≤ N) :
    (pCoreOf 2 (X.subgroupOf N)).map N.subtype = pCoreOf 2 X := by
  rw [pCoreOf, pCoreOf, Subgroup.map_map]
  let e : ↥(X.subgroupOf N) ≃* ↥X :=
    { toFun := fun x => ⟨(x : ↥N), x.2⟩
      invFun := fun x => ⟨⟨(x : G), h x.2⟩, x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hcomp : N.subtype.comp (X.subgroupOf N).subtype = X.subtype.comp e.toMonoidHom := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map, pCore_map_iso 2 e]

private lemma l937z_suu_pCoreOf_le_of_normal {G : Type*} [Group G] {A M : Subgroup G}
    (hle : A ≤ M) (hN : (A.subgroupOf M).Normal) :
    pCoreOf 2 A ≤ pCoreOf 2 M := by
  have hnorm : ((pCore 2 ↥(A.subgroupOf M)).map (A.subgroupOf M).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (G := ↥M) (H := A.subgroupOf M)
      (K := pCore 2 ↥(A.subgroupOf M))
  have hp : IsPGroup 2 ((pCore 2 ↥(A.subgroupOf M)).map (A.subgroupOf M).subtype) :=
    IsPGroup.map (pCore_isPGroup) (A.subgroupOf M).subtype
  have h1 : pCoreOf 2 (A.subgroupOf M) ≤ pCore 2 ↥M := by
    rw [pCoreOf, pCore]
    exact le_sSup ⟨hnorm, hp⟩
  have h2 := Subgroup.map_mono (f := M.subtype) h1
  rwa [l937z_suu_map_pCoreOf_subgroupOf hle] at h2

private lemma l937z_suu_pCoreOf_centralizer_eq_bot_of_normal {G : Type*} [Group G] [Finite G]
    {S : Subgroup G} (hS : S.Normal) {a : G} (ha : a ∈ S)
    (hCG : pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥) :
    pCoreOf 2 (Subgroup.centralizer ({⟨a, ha⟩} : Set ↥S)) = ⊥ := by
  let CSU : Subgroup ↥S := Subgroup.centralizer ({⟨a, ha⟩} : Set ↥S)
  let CG : Subgroup G := Subgroup.centralizer ({a} : Set G)
  have hmap : (pCoreOf 2 CSU).map S.subtype = pCoreOf 2 (CG ⊓ S) := by
    rw [l937z_suu_map_pCoreOf_injective S.subtype (Subgroup.subtype_injective S) CSU,
      l937z_suu_map_centralizer_subgroupOf (⟨a, ha⟩ : ↥S)]
  have hN : ((CG ⊓ S).subgroupOf CG).Normal := by
    have h := hS.subgroupOf CG
    convert h using 1
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hle : pCoreOf 2 (CG ⊓ S) ≤ pCoreOf 2 CG :=
    l937z_suu_pCoreOf_le_of_normal inf_le_left hN
  have hbot : pCoreOf 2 (CG ⊓ S) = ⊥ := by
    rw [hCG] at hle
    exact le_bot_iff.mp hle
  have hmapbot : (pCoreOf 2 CSU).map S.subtype = ⊥ := by rw [hmap, hbot]
  exact (Subgroup.map_eq_bot_iff_of_injective (pCoreOf 2 CSU)
    (Subgroup.subtype_injective S)).mp hmapbot

private lemma l937z_suu_exists_unitaryFieldData {K : Type} [Field K] [Finite K] (q : ℕ)
    (hK : Nat.card K = q ^ 2) :
    ∃ (p d : ℕ) (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p d K),
      ∀ x : K, h.bar x = x ^ q := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hcardF⟩ := FiniteField.card K (ringChar K)
  let m' : ℕ := m
  have hcardF' : Fintype.card K = (ringChar K) ^ m' := by simpa [m'] using hcardF
  have hcard : Nat.card K = (ringChar K) ^ m' := by
    rw [Nat.card_eq_fintype_card, hcardF']
  have hsq : q ^ 2 = (ringChar K) ^ m' := hK.symm.trans hcard
  obtain ⟨d, hmd, hq⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot.exists_exponent hp hsq
  have hmpos : 0 < m' := by simpa [m'] using m.pos
  have hd : 1 ≤ d := by omega
  refine ⟨ringChar K, d, ⟨hp, hd, by rw [hcard, hmd]⟩, ?_⟩
  intro x
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← hq]

private lemma l937z_suu_GUFull_eq_primeFormUnitary {E : Type} [Field E] {m p f Q : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hbar : ∀ x : E, h.bar x = x ^ Q) :
    GUFull m Q E =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram E m) := by
  apply le_antisymm
  · rw [GUFull, Subgroup.closure_le]
    intro A hA
    rw [Set.mem_setOf_eq] at hA
    change A ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram E m)
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) := by
      ext i j; simp only [Matrix.map_apply, hbar]
    rw [hmap]
    simpa only [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one,
      Matrix.mul_one] using hA
  · intro A hA
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    have hA' := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary.mp hA)
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) := by
      ext i j; simp only [Matrix.map_apply, hbar]
    rw [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one] at hA'
    rwa [hmap] at hA'

private lemma l937z_suu_SU_eq {K : Type} [Field K] [Finite K] [CharP K 2] (n q : ℕ)
    (hK : Nat.card K = q ^ 2) :
    StatedSU n q K = GUFull n q K ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  obtain ⟨p, d, h, hbar⟩ := l937z_suu_exists_unitaryFieldData q hK
  rw [l937z_suu_GUFull_eq_primeFormUnitary h hbar]
  apply le_antisymm
  · rw [StatedSU, Subgroup.closure_le]
    rintro A ⟨hdet, huni⟩
    change A ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ⊓
        (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
      have hmap : (A : Matrix (Fin n) (Fin n) K).map h.bar =
          (A : Matrix (Fin n) (Fin n) K).map (· ^ q) := by
        ext i j; simp only [Matrix.map_apply, hbar]
      rw [hmap, CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one]
      exact huni
    · rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact hdet
  · intro A hA
    rw [Subgroup.mem_inf] at hA
    rw [StatedSU]
    apply Subgroup.subset_closure
    have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
      have h := MonoidHom.mem_ker.mp hA.2
      have h' := congrArg Units.val h
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'
    refine ⟨hdet, ?_⟩
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary.mp hA.1)
    rw [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one] at h1
    have hmap : (A : Matrix (Fin n) (Fin n) K).map h.bar =
        (A : Matrix (Fin n) (Fin n) K).map (· ^ q) := by
      ext i j; simp only [Matrix.map_apply, hbar]
    rwa [hmap] at h1

private lemma l937z_suu_SU_normal {K : Type} [Field K] [Finite K] [CharP K 2] (n q : ℕ)
    (hK : Nat.card K = q ^ 2) :
    ((StatedSU n q K).subgroupOf (GUFull n q K)).Normal := by
  have hsu := l937z_suu_SU_eq n q hK
  have hker : (StatedSU n q K).subgroupOf (GUFull n q K) =
      (Matrix.GeneralLinearGroup.det.comp (GUFull n q K).subtype).ker := by
    ext A
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.comp_apply]
    rw [hsu, Subgroup.mem_inf]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨A.2, h⟩
  rw [hker]
  infer_instance

theorem pCoreSevenTrivial_StatedSU {K : Type} [Field K] [Finite K] [CharP K 2] (n q : ℕ)
    (hK : Nat.card K = q ^ 2) (h7 : Nat.Coprime 7 (q + 1)) :
    PCoreSevenTrivial ↥(StatedSU n q K) := by
  intro x hx7
  by_cases hn : n = 0
  · subst hn
    haveI : Subsingleton ↥(StatedSU 0 q K) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have h1 : orderOf x = 1 := orderOf_eq_one_iff.mpr (Subsingleton.elim x 1)
    omega
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨k, hkField, hkFinite, hkCharP, hkcard, t, ht, ⟨ψ⟩⟩ :=
      exists_guFull_equiv_centralizer_statedSp q n hn1 hK
    letI : Field k := hkField
    letI : Finite k := hkFinite
    letI : CharP k 2 := hkCharP
    haveI : Fintype k := Fintype.ofFinite k
    let x' : GL (Fin n) K := (x : GL (Fin n) K)
    have hx' : x' ∈ GUFull n q K := statedSU_le_guFull n q x.2
    let xGU : ↥(GUFull n q K) := ⟨x', hx'⟩
    let T : Subgroup ↥(StatedSp n k) := Subgroup.centralizer ({t} : Set ↥(StatedSp n k))
    let ψx : ↥T := ψ xGU
    let y : ↥(StatedSp n k) := (ψx : ↥(StatedSp n k))
    let b : ↥(StatedSp n k) := y * t
    have hx'ord : orderOf x' = 7 := by
      change orderOf (x : GL (Fin n) K) = 7
      rw [← Subgroup.orderOf_mk (x : GL (Fin n) K) x.2]
      exact hx7
    have hxGUord : orderOf xGU = 7 := by
      change orderOf (⟨x', hx'⟩ : ↥(GUFull n q K)) = 7
      rw [Subgroup.orderOf_mk]
      exact hx'ord
    have hψxord : orderOf ψx = 7 := by
      change orderOf (ψ xGU) = 7
      rw [MulEquiv.orderOf_eq]
      exact hxGUord
    have hyord : orderOf y = 7 := by
      have h := (Subgroup.orderOf_mk (ψx : ↥(StatedSp n k)) ψx.2).symm
      rw [h]
      exact hψxord
    have hcomm : Commute y t := by
      have hmem : y ∈ T := ψx.2
      change y ∈ Subgroup.centralizer ({t} : Set ↥(StatedSp n k)) at hmem
      rwa [Subgroup.mem_centralizer_singleton_iff] at hmem
    have hq1 : 1 < q + 1 := by
      have h2 : 2 ≤ Nat.card K := by
        haveI : Fintype K := Fintype.ofFinite K
        have h := Fintype.one_lt_card (α := K)
        rw [Nat.card_eq_fintype_card]
        omega
      have hq0 : q ≠ 0 := by
        rintro rfl
        norm_num at hK
        omega
      have hq1' : q ≠ 1 := by
        rintro rfl
        norm_num at hK
        omega
      omega
    have hqodd : Odd (q + 1) := by
      obtain ⟨f, -, hkpow⟩ := FiniteField.card k 2
      have hqpow : q = 2 ^ (f : ℕ) := by
        rw [← hkcard, Nat.card_eq_fintype_card, hkpow]
      rw [hqpow]
      obtain ⟨g, hg⟩ := Nat.exists_eq_succ_of_ne_zero (f.pos.ne')
      rw [hg]
      exact Even.add_one ⟨2 ^ g, by rw [pow_succ]; ring⟩
    have hbord : orderOf b = 7 * (q + 1) := by
      change orderOf (y * t) = 7 * (q + 1)
      rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm]
      · rw [hyord, ht]
      · rw [hyord, ht]; exact h7
    have hodd : Odd (orderOf (b : GL (Fin n ⊕ Fin n) k)) := by
      rw [← Subgroup.orderOf_mk (b : GL (Fin n ⊕ Fin n) k) b.2, hbord]
      exact Nat.odd_mul.mpr ⟨by norm_num, hqodd⟩
    have hB := pCoreOf_centralizer_StatedSp_eq_bot (b : GL (Fin n ⊕ Fin n) k) b.2 hodd
    have hCSpb : pCore 2 ↥(Subgroup.centralizer ({b} : Set ↥(StatedSp n k))) = ⊥ := by
      rw [l937z_suu_comap_centralizer_subtype (StatedSp n k) b] at hB
      rw [pCoreOf] at hB
      exact (Subgroup.map_eq_bot_iff_of_injective
        (pCore 2 ↥(Subgroup.centralizer ({b} : Set ↥(StatedSp n k))))
        (Subgroup.subtype_injective _)).mp hB
    let C1 : Subgroup ↥(GUFull n q K) := Subgroup.centralizer ({xGU} : Set ↥(GUFull n q K))
    let C2 : Subgroup ↥T := Subgroup.centralizer ({ψx} : Set ↥T)
    let C3 : Subgroup ↥(StatedSp n k) := C2.map T.subtype
    have hC3 : C3 = Subgroup.centralizer ({b} : Set ↥(StatedSp n k)) := by
      have h1 : C3 = Subgroup.centralizer ({y} : Set ↥(StatedSp n k)) ⊓
          Subgroup.centralizer ({t} : Set ↥(StatedSp n k)) := by
        change C2.map T.subtype = Subgroup.centralizer ({y} : Set ↥(StatedSp n k)) ⊓ T
        rw [l937z_suu_map_centralizer_subgroupOf (a := ψx)]
      rw [h1]
      change Subgroup.centralizer ({y} : Set ↥(StatedSp n k)) ⊓
          Subgroup.centralizer ({t} : Set ↥(StatedSp n k)) =
        Subgroup.centralizer ({y * t} : Set ↥(StatedSp n k))
      exact l937z_suu_centralizer_mul_eq hcomm hyord ht h7 hq1
    have hC3bot : pCore 2 ↥C3 = ⊥ := by rw [hC3]; exact hCSpb
    have hC2bot : pCore 2 ↥C2 = ⊥ :=
      pCore_trivial_of_mulEquiv
        (Subgroup.equivMapOfInjective C2 T.subtype (Subgroup.subtype_injective T)).symm hC3bot
    have hC1bot : pCore 2 ↥C1 = ⊥ :=
      pCore_trivial_of_mulEquiv (l937z_suu_centralizerMulEquiv ψ xGU).symm hC2bot
    have hC1of : pCoreOf 2 C1 = ⊥ := by rw [pCoreOf, hC1bot, Subgroup.map_bot]
    have hSUnorm : ((StatedSU n q K).subgroupOf (GUFull n q K)).Normal :=
      l937z_suu_SU_normal n q hK
    have ha : xGU ∈ (StatedSU n q K).subgroupOf (GUFull n q K) := x.2
    have hSUbot := l937z_suu_pCoreOf_centralizer_eq_bot_of_normal hSUnorm ha hC1of
    let e : ↥((StatedSU n q K).subgroupOf (GUFull n q K)) ≃* ↥(StatedSU n q K) :=
      Subgroup.subgroupOfEquivOfLe (statedSU_le_guFull n q)
    have hea : e ⟨xGU, ha⟩ = x := Subtype.ext rfl
    have hmap := l937z_suu_map_pCoreOf_injective e.toMonoidHom e.injective
      (Subgroup.centralizer ({⟨xGU, ha⟩} : Set ↥((StatedSU n q K).subgroupOf (GUFull n q K))))
    rw [l937z_suu_map_centralizer_singleton e ⟨xGU, ha⟩] at hmap
    have hfin : pCoreOf 2
        (Subgroup.centralizer ({e ⟨xGU, ha⟩} : Set ↥(StatedSU n q K))) = ⊥ := by
      rw [← hmap, hSUbot, Subgroup.map_bot]
    rwa [hea] at hfin

theorem card_statedScalars_subgroupOf_statedSU_dvd {K : Type} [Field K] [Finite K] (n q : ℕ)
    (hK : Nat.card K = q ^ 2) :
    Nat.card ↥((StatedScalars (Fin n) K).subgroupOf (StatedSU n q K)) ∣ q + 1 := by
  by_cases hn : n = 0
  · subst hn
    have hbot : StatedScalars (Fin 0) K = ⊥ := by
      rw [StatedScalars]
      apply le_antisymm _ bot_le
      rintro A ⟨c, rfl⟩
      rw [Subgroup.mem_bot]
      exact Subsingleton.elim _ _
    rw [hbot]
    have hbotZ : (⊥ : Subgroup (GL (Fin 0) K)).subgroupOf (StatedSU 0 q K) = ⊥ := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hbotZ, Subgroup.card_bot]
    exact one_dvd _
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨m, hp, hcardF⟩ := FiniteField.card K (ringChar K)
    let m' : ℕ := m
    have hcardF' : Fintype.card K = (ringChar K) ^ m' := by simpa [m'] using hcardF
    have hcard : Nat.card K = (ringChar K) ^ m' := by
      rw [Nat.card_eq_fintype_card, hcardF']
    have hsq : q ^ 2 = (ringChar K) ^ m' := hK.symm.trans hcard
    obtain ⟨d, hmd, hq⟩ :=
      CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot.exists_exponent hp hsq
    have hmpos : 0 < m' := by simpa [m'] using m.pos
    have hd : 1 ≤ d := by omega
    let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData (ringChar K) d K :=
      ⟨hp, hd, by rw [hcard, hmd]⟩
    have hfbq : ∀ x : K, h.bar x = x ^ q := by
      intro x
      rw [h.bar_apply, ← hq]
    set U : Subgroup Kˣ := (powMonoidHom (q + 1) : Kˣ →* Kˣ).ker with hUdef
    set R : Subgroup (GL (Fin n) K) :=
      U.map (Matrix.GeneralLinearGroup.scalar (Fin n)) with hRdef
    have hZmap_le : ((StatedScalars (Fin n) K).subgroupOf
        (StatedSU n q K)).map (StatedSU n q K).subtype ≤ R := by
      rintro A ⟨z, hz, rfl⟩
      have hzscal : (z : GL (Fin n) K) ∈ StatedScalars (Fin n) K :=
        Subgroup.mem_subgroupOf.mp hz
      rw [StatedScalars, MonoidHom.mem_range] at hzscal
      obtain ⟨c, hc⟩ := hzscal
      have hcSU : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n q K :=
        hc ▸ z.2
      have hcU : c ∈ U := by
        rw [hUdef, MonoidHom.mem_ker, powMonoidHom_apply]
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← hfbq (c : K)]
        exact l937z_suu_scalar_step hn1 hfbq hcSU
      rw [hRdef]
      exact Subgroup.mem_map.mpr ⟨c, hcU, hc⟩
    have hcardR : Nat.card ↥R = q + 1 := by
      have hmapcard : Nat.card ↥R = Nat.card ↥U := by
        rw [hRdef]
        exact Subgroup.card_map_of_injective (l937z_suu_scalar_units_injective hn1)
      rw [hmapcard, hUdef, IsCyclic.card_powMonoidHom_ker Kˣ (q + 1), Nat.card_units, hK]
      apply Nat.gcd_eq_right
      exact ⟨q - 1, by simpa using (Nat.sq_sub_sq q 1)⟩
    have hcard_map : Nat.card ↥(((StatedScalars (Fin n) K).subgroupOf
        (StatedSU n q K)).map (StatedSU n q K).subtype) =
        Nat.card ↥((StatedScalars (Fin n) K).subgroupOf (StatedSU n q K)) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective (StatedSU n q K))
    rw [← hcard_map]
    exact (Subgroup.card_dvd_of_le hZmap_le).trans (by rw [hcardR])

theorem lieZRow_PSU {K : Type} [Field K] [Finite K] [CharP K 2] (n q : ℕ)
    (hK : Nat.card K = q ^ 2) (h7 : Nat.Coprime 7 (q + 1)) :
    LieZRow (StatedProj (StatedSU n q K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hZ : Nat.Coprime 14
      (Nat.card ↥((StatedScalars (Fin n) K).subgroupOf (StatedSU n q K))) := by
    have hdiv := card_statedScalars_subgroupOf_statedSU_dvd n q hK
    have hqeven : Even q := by
      have hchar : ringChar K = 2 := ringChar.eq K 2
      have hev : Even (q ^ 2) := by
        rw [← hK, Nat.card_eq_fintype_card]
        exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two hchar)
      have hev' : Even (q * q) := by simpa [pow_two] using hev
      rcases (Nat.even_mul.mp hev') with h | h
      · exact h
      · exact h
    have h14 : Nat.Coprime 14 (q + 1) := by
      rw [show (14 : ℕ) = 2 * 7 by norm_num, Nat.coprime_mul_iff_left]
      exact ⟨Nat.coprime_two_left.mpr (Even.add_one hqeven), h7⟩
    exact h14.coprime_dvd_right hdiv
  exact lieZRow_statedProj (StatedSU n q K) hZ
    (lieZRow_of_pCoreSevenTrivial (pCoreSevenTrivial_StatedSU n q hK h7))

end CFSG.StandardType.SporadicShape
