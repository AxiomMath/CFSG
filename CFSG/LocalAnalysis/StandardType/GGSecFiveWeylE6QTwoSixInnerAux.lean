module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAutLQAux
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat

public section

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.USixTwo
open Matrix

namespace CFSG.StandardType.E6QTwo

variable {K : Type} [Field K] [Finite K]

theorem mem_largeEvenGUSet_iff (hK : Nat.card K = 4) {A : GL (Fin 6) K} :
    A ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) ↔
      ((A : Matrix (Fin 6) (Fin 6) K).map (fieldDataFour hK).bar)ᵀ *
        (A : Matrix (Fin 6) (Fin 6) K) = 1 := by
  constructor
  · rintro ⟨μ, hμ0, hμq, hA⟩
    have hμ1 : μ = 1 := by
      have hfac : μ * (μ - 1) = 0 := by
        rw [mul_sub, mul_one]
        rw [show μ * μ = μ from ?_]
        · ring
        · simpa [pow_two] using hμq
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hμ0
      · exact sub_eq_zero.mp h
    rw [hμ1, one_smul] at hA
    have hmapbar : (A : Matrix (Fin 6) (Fin 6) K).map (· ^ (2 ^ 1)) =
        (A : Matrix (Fin 6) (Fin 6) K).map (fieldDataFour hK).bar := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, fieldDataFour_bar hK]
      norm_num
    rw [hmapbar] at hA
    exact hA
  · intro hA
    refine ⟨1, one_ne_zero, by norm_num, ?_⟩
    rw [one_smul]
    have hmapbar : (A : Matrix (Fin 6) (Fin 6) K).map (· ^ (2 ^ 1)) =
        (A : Matrix (Fin 6) (Fin 6) K).map (fieldDataFour hK).bar := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, fieldDataFour_bar hK]
      norm_num
    rw [hmapbar]
    exact hA

theorem mem_largeEvenGUSet_of_mem_SU (hK : Nat.card K = 4)
    {u : GL (Fin 6) K} (hu : u ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :
    u ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) := by
  rw [mem_largeEvenGUSet_iff hK]
  exact ((mem_SU_iff (fieldDataFour hK)).mp hu).2

theorem mul_mem_largeEvenGUSet (hK : Nat.card K = 4)
    {A B : GL (Fin 6) K} (hA : A ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1))
    (hB : B ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1)) :
    A * B ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) := by
  rw [mem_largeEvenGUSet_iff hK] at hA hB ⊢
  have hmul : (((A * B : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) =
      (A : Matrix (Fin 6) (Fin 6) K) * (B : Matrix (Fin 6) (Fin 6) K) := rfl
  rw [hmul]
  have hmap : ((A : Matrix (Fin 6) (Fin 6) K) * (B : Matrix (Fin 6) (Fin 6) K)).map
      (fieldDataFour hK).bar =
      (A : Matrix (Fin 6) (Fin 6) K).map (fieldDataFour hK).bar *
        (B : Matrix (Fin 6) (Fin 6) K).map (fieldDataFour hK).bar := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  have hAB : ((A : Matrix (Fin 6) (Fin 6) K).map (fieldDataFour hK).bar)ᵀ *
      ((A : Matrix (Fin 6) (Fin 6) K) * (B : Matrix (Fin 6) (Fin 6) K)) =
      (B : Matrix (Fin 6) (Fin 6) K) := by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  rw [hmap, Matrix.transpose_mul, Matrix.mul_assoc, hAB, hB]

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] [Finite K]

theorem conj_mem_largeEvenSUGroup (hK : Nat.card K = 4) {A g : GL (Fin 6) K}
    (hA : A ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1))
    (hg : g ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :
    A * g * A⁻¹ ∈ LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
  haveI : CharP K 2 := USixTwo.charP_two_of_card_four hK
  exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.conj_mem_su (j := 1) hA hg

theorem exists_inducing_conj (hK : Nat.card K = 4)
    {L : Type} [Group L]
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {g : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))}
    (hψ : ψ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1))) {rel : L → L → Prop}
    (hψind : LargeEvenInduces θ rel ψ) :
    ∃ ψ' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces (θ.trans (MulAut.conj g)) rel ψ' := by
  classical
  let P : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) g
  have huP : P u = g := hu
  obtain ⟨A, hA, hAgr⟩ := hψ
  have huGU : (u : GL (Fin 6) K) ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) :=
    mem_largeEvenGUSet_of_mem_SU hK u.2
  have huInvGU : ((u : GL (Fin 6) K))⁻¹ ∈ LargeEvenGUSet (Fin 6) K (2 ^ 1) :=
    mem_largeEvenGUSet_of_mem_SU hK (by
      simpa using (LargeEvenSUGroup (Fin 6) K (2 ^ 1)).inv_mem u.2)
  have hA'GU : (u : GL (Fin 6) K) * A * (u : GL (Fin 6) K)⁻¹ ∈
      LargeEvenGUSet (Fin 6) K (2 ^ 1) := by
    have hAu : (A * (u : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) ∈
        LargeEvenGUSet (Fin 6) K (2 ^ 1) := mul_mem_largeEvenGUSet hK hA huInvGU
    simpa [mul_assoc] using mul_mem_largeEvenGUSet hK huGU hAu
  refine ⟨MulAut.conj g * ψ * (MulAut.conj g)⁻¹, ?_, ?_⟩
  · refine ⟨u * A * u⁻¹, ?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hA'GU
    · intro h h' hrel
      have h1mem : ((u : GL (Fin 6) K)⁻¹ * (h : GL (Fin 6) K) * (u : GL (Fin 6) K)) ∈
          LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
        simpa using conj_mem_largeEvenSUGroup hK huInvGU h.2
      have h1'mem : ((u : GL (Fin 6) K)⁻¹ * (h' : GL (Fin 6) K) * (u : GL (Fin 6) K)) ∈
          LargeEvenSUGroup (Fin 6) K (2 ^ 1) := by
        simpa using conj_mem_largeEvenSUGroup hK huInvGU h'.2
      let h1 : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
        ⟨(u : GL (Fin 6) K)⁻¹ * (h : GL (Fin 6) K) * (u : GL (Fin 6) K), h1mem⟩
      let h1' : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
        ⟨(u : GL (Fin 6) K)⁻¹ * (h' : GL (Fin 6) K) * (u : GL (Fin 6) K), h1'mem⟩
      have hrel1 : (h1' : GL (Fin 6) K) = A * (h1 : GL (Fin 6) K) * A⁻¹ := by
        show (u : GL (Fin 6) K)⁻¹ * (h' : GL (Fin 6) K) * (u : GL (Fin 6) K) =
          A * ((u : GL (Fin 6) K)⁻¹ * (h : GL (Fin 6) K) * (u : GL (Fin 6) K)) * A⁻¹
        rw [hrel]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hψh : ψ (P h1) = P h1' := hAgr h1 h1' hrel1
      have e1 : g⁻¹ * P h * g = P h1 := by
        rw [← huP, ← map_inv, ← map_mul, ← map_mul]
        rfl
      have e2 : g * P h1' * g⁻¹ = P h' := by
        rw [← huP, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (by
          simp only [h1', Subgroup.coe_mul, Subgroup.coe_inv]
          group)
      change (MulAut.conj g * ψ * (MulAut.conj g)⁻¹) (P h) = P h'
      calc (MulAut.conj g * ψ * (MulAut.conj g)⁻¹) (P h)
          = g * ψ (g⁻¹ * P h * g) * g⁻¹ := by
            simp [MulAut.mul_apply, MulAut.conj_apply]
        _ = g * ψ (P h1) * g⁻¹ := by rw [e1]
        _ = g * P h1' * g⁻¹ := by rw [hψh]
        _ = P h' := e2
  · intro l l' hl'
    show (MulAut.conj g * ψ * (MulAut.conj g)⁻¹)
      ((θ.trans (MulAut.conj g)) (QuotientGroup.mk l)) =
      (θ.trans (MulAut.conj g)) (QuotientGroup.mk l')
    simp only [MulEquiv.trans_apply, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.conj_inv_apply, MulEquiv.symm_apply_apply]
    have h1 : g⁻¹ * (g * θ (QuotientGroup.mk l) * g⁻¹) * g = θ (QuotientGroup.mk l) := by
      group
    rw [h1, hψind l l' hl']

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G} {ω : K}

theorem piOf_ker_aux
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    (piOf (K := K) θ).ker = Subgroup.center L := by
  ext y
  rw [MonoidHom.mem_ker, piOf, MonoidHom.comp_apply]
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (Subgroup.center L) y = 1 := by
      apply θ.injective
      simpa using h
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center L) y).mp h1
  · intro h
    rw [QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff (N := Subgroup.center L) y).mpr h, map_one]

theorem piOf_inj_inf (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    {z z' : ↥L} (hz : z ∈ (Bs ⊓ L).subgroupOf L) (hz' : z' ∈ (Bs ⊓ L).subgroupOf L)
    (h : piOf (K := K) θ z = piOf (K := K) θ z') : z = z' :=
  piOf_injective_of_pow_three θ hZ2 (pow_three_of_mem_inf hBs hz)
    (pow_three_of_mem_inf hBs hz') h

@[expose] def ZL : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)

theorem mem_ZL {z : G} : z ∈ ZL (L := L) ↔ z ∈ L ∧ z ∈ Subgroup.centralizer (L : Set G) :=
  Subgroup.mem_inf

theorem ZL_central {z l : G} (hz : z ∈ ZL (L := L)) (hl : l ∈ L) : z * l = l * z :=
  (Subgroup.mem_centralizer_iff.mp hz.2 l hl).symm

theorem isMulCommutative_ZL : IsMulCommutative ↥(ZL (L := L)) :=
  ⟨⟨fun (a b : ↥(ZL (L := L))) => by
    apply Subtype.ext
    show ((a * b : ↥(ZL (L := L))) : G) = ((b * a : ↥(ZL (L := L))) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (ZL_central (L := L) b.2 ((mem_ZL (L := L)).mp a.2).1).symm⟩⟩

theorem isPGroup_ZL (hZ2 : IsPGroup 2 (Subgroup.center L)) :
    IsPGroup 2 ↥(ZL (L := L)) := by
  rw [isPGroup_iff_orderOf_dvd_pow] at hZ2 ⊢
  intro z
  have hzL : (z : G) ∈ L := ((mem_ZL (L := L)).mp z.2).1
  have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) := ((mem_ZL (L := L)).mp z.2).2
  let zc : ↥(Subgroup.center L) := ⟨⟨(z : G), hzL⟩, by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (l : G) l.2)⟩
  obtain ⟨k, hk⟩ := hZ2 zc
  refine ⟨k, ?_⟩
  have e1 : orderOf z = orderOf (z : G) := (Subgroup.orderOf_coe z).symm
  have e2 : orderOf (z : G) = orderOf (⟨(z : G), hzL⟩ : ↥L) :=
    Subgroup.orderOf_coe (⟨(z : G), hzL⟩ : ↥L)
  have e3 : orderOf (⟨(z : G), hzL⟩ : ↥L) = orderOf zc :=
    Subgroup.orderOf_coe zc
  rw [e1, e2, e3]
  exact hk

theorem le_normalizer_ZL_of_le_normalizer {H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (L : Set G)) :
    H ≤ Subgroup.normalizer (ZL (L := L) : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨hyL, hyC⟩ := (mem_ZL (L := L)).mp hy
    refine (mem_ZL (L := L)).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hH hb) y).mp hyL
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hbl' : (b : G)⁻¹ * l * (b : G) ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (L : Set G)).inv_mem (hH hb)) l).mp hl
      have hcomm : ((b : G)⁻¹ * l * (b : G)) * y =
          y * ((b : G)⁻¹ * l * (b : G)) :=
        Subgroup.mem_centralizer_iff.mp hyC _ hbl'
      calc l * ((b : G) * y * (b : G)⁻¹)
          = (b : G) * (((b : G)⁻¹ * l * (b : G)) * y) * (b : G)⁻¹ := by group
        _ = (b : G) * (y * ((b : G)⁻¹ * l * (b : G))) * (b : G)⁻¹ := by rw [hcomm]
        _ = ((b : G) * y * (b : G)⁻¹) * l := by group
  · intro hy
    obtain ⟨hyL, hyC⟩ := (mem_ZL (L := L)).mp hy
    have hb' : (b : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem (hH hb)
    refine (mem_ZL (L := L)).mpr ⟨?_, ?_⟩
    · have h1 : (b : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * (b : G) ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.mp hb' ((b : G) * y * (b : G)⁻¹)).mp hyL
      have h2 : (b : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * (b : G) = y := by group
      rwa [h2] at h1
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hbl : (b : G) * l * (b : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hH hb) l).mp hl
      have hcomm : ((b : G) * l * (b : G)⁻¹) * ((b : G) * y * (b : G)⁻¹) =
          ((b : G) * y * (b : G)⁻¹) * ((b : G) * l * (b : G)⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hyC _ hbl
      have hy : y * l = l * y := by
        calc y * l
            = (b : G)⁻¹ * (((b : G) * y * (b : G)⁻¹) * ((b : G) * l * (b : G)⁻¹)) * (b : G) := by
              group
          _ = (b : G)⁻¹ * (((b : G) * l * (b : G)⁻¹) * ((b : G) * y * (b : G)⁻¹)) * (b : G) := by
              rw [hcomm.symm]
          _ = l * y := by group
      exact hy.symm
theorem le_normalizer_ZL (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Bs ≤ Subgroup.normalizer (ZL (L := L) : Set G) :=
  le_normalizer_ZL_of_le_normalizer hNL

theorem le_normalizer_ZL_self :
    L ≤ Subgroup.normalizer (ZL (L := L) : Set G) :=
  le_normalizer_ZL_of_le_normalizer Subgroup.le_normalizer

@[expose] def conjBL (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs) (y : ↥L) : ↥L :=
  ⟨(b : G) * (y : G) * (b : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hNL b.2) (y : G)).mp y.2⟩

@[expose] def conjBLinv (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs) (y : ↥L) : ↥L :=
  ⟨(b : G)⁻¹ * (y : G) * (b : G),
    by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem (hNL b.2)) (y : G)).mp y.2
      simpa using h⟩

@[expose] def deltaElem (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (n : ↥L) (b : ↥Bs) : ↥L :=
  conjBLinv hNL b n * n⁻¹

@[expose] def cElem (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (n : ↥L) (b : ↥Bs) : ↥L :=
  n * conjBL hNL b n⁻¹

@[simp] theorem deltaElem_coe (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (n : ↥L) (b : ↥Bs) :
    ((deltaElem hNL n b : ↥L) : G) =
      (b : G)⁻¹ * (n : G) * (b : G) * (n : G)⁻¹ := by
  simp [deltaElem, conjBLinv, mul_assoc]

@[simp] theorem cElem_coe (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (n : ↥L) (b : ↥Bs) :
    ((cElem hNL n b : ↥L) : G) =
      (n : G) * (b : G) * (n : G)⁻¹ * (b : G)⁻¹ := by
  simp [cElem, conjBL, mul_assoc]

end CFSG.StandardType.E6QTwo

end
