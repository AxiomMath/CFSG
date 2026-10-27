module

public import CFSG.Quasithin.EmptyFaithful.SzC4Sl4Def
public import CFSG.Quasithin.EmptyFaithful.A38c10Psi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat4A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.Quasithin.EmptyFaithful.A38c10Mat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzC4

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.Quasithin.A38c10
  CFSG.Quasithin.S15223P4.C.Nat4 CFSG.LieType.SteinbergBR.BlockPar
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

theorem r1_mem_QI (v : Fin 3 → ZMod 2) : r1 v ∈ QI 4 {1} :=
  (mem_QI_one_iff (m := 3)).2 fun i => by fin_cases i <;> rfl

theorem s3_mem_QI (u : Fin 3 → ZMod 2) : s3 u ∈ QI 4 {3} := by
  rw [QI_four_three_eq, mem_stabilizer_flagSpace_iff]
  intro i j hi hj
  revert u
  revert i j
  decide

@[expose] def lev1 : ↥(QI 4 {1}) →* SLt 3 := blkHom 3

@[expose] noncomputable def lev3 : ↥(QI 4 {3}) →* SLt 3 :=
  (blk3Hom (by norm_num : 3 ≤ 4)).comp (Subgroup.inclusion QI_four_three_eq.le)

theorem lev1_surjective : Function.Surjective lev1 := blkHom_surjective 3

theorem lev3_surjective : Function.Surjective lev3 := by
  have hle : QI 4 {3} ≤ stabilizer (flagSpace 4 (ZMod 2) 3) := QI_four_three_eq.le
  have h3 : (3 : ℕ) ≤ 4 := by norm_num
  have h4 : (3 : ℕ) < 4 := by norm_num
  have h45 : (4 : ℕ) = 4 ∨ (4 : ℕ) = 5 := Or.inl rfl
  have hmem1 : T1 4 h3 ∈ QI 4 {3} := QI_four_three_eq ▸ T1_mem_stab3 h3 h4
  have hmem2 : T2 4 h3 ∈ QI 4 {3} := QI_four_three_eq ▸ T2_mem_stab3 h3 h4
  have hA : gen3A ∈ lev3.range := by
    refine ⟨⟨T1 4 h3, hmem1⟩, Subtype.ext ?_⟩
    show blk3 h3 (T1 4 h3) = a3T1
    exact blk3_T1 h45 h3
  have hB : gen3B ∈ lev3.range := by
    refine ⟨⟨T2 4 h3, hmem2⟩, Subtype.ext ?_⟩
    show blk3 h3 (T2 4 h3) = b3T2
    exact blk3_T2 h45 h3
  intro y
  have hy : y ∈ Subgroup.closure ({gen3A, gen3B} : Set (SLt 3)) := by
    rw [closure_gen3A_gen3B]
    exact Subgroup.mem_top y
  have hle' : Subgroup.closure ({gen3A, gen3B} : Set (SLt 3)) ≤ lev3.range := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hA
    · exact hB
  exact hle' hy

theorem zmod2_eq_one_of_mul_eq_one : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide

theorem eq_r1_of_lev1_eq_one {x : SLt 4} (hx : x ∈ QI 4 {1}) (h : lev1 ⟨x, hx⟩ = 1) :
    ∃ v, x = r1 v := by
  have h1 := (mem_QI_one_iff (m := 3)).1 hx
  have h3 : ∀ i j : Fin 3, (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.succ j.succ =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
    intro i j
    have := congrArg (fun y : SLt 3 => (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) h
    simpa [lev1, blkHom_coe] using this
  have h2 : (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 0 = 1 := by
    have hd := det_eq_mul_det_blk (m := 3) hx
    have hb : blk x = 1 := by
      ext i j
      exact h3 i j
    rw [Matrix.SpecialLinearGroup.det_coe, hb, Matrix.det_one, mul_one] at hd
    exact hd.symm
  refine ⟨fun j => (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 j.succ, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h2
  · rfl
  · rfl
  · rfl
  · exact h1 0
  · exact h3 0 0
  · exact h3 0 1
  · exact h3 0 2
  · exact h1 1
  · exact h3 1 0
  · exact h3 1 1
  · exact h3 1 2
  · exact h1 2
  · exact h3 2 0
  · exact h3 2 1
  · exact h3 2 2

theorem lev1_r1 (v : Fin 3 → ZMod 2) : lev1 ⟨r1 v, r1_mem_QI v⟩ = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_s3_of_lev3_eq_one {x : SLt 4} (hx : x ∈ QI 4 {3}) (h : lev3 ⟨x, hx⟩ = 1) :
    ∃ u, x = s3 u := by
  have hst : x ∈ stabilizer (flagSpace 4 (ZMod 2) 3) := QI_four_three_eq ▸ hx
  have hst' : x⁻¹ ∈ stabilizer (flagSpace 4 (ZMod 2) 3) := (stabilizer _).inv_mem hst
  have e0 := (mem_stabilizer_flagSpace_iff (d := 3)).1 hst
  have e0' := (mem_stabilizer_flagSpace_iff (d := 3)).1 hst'
  have h3 : ∀ i j : Fin 3, (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) i.castSucc j.castSucc =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
    intro i j
    have := congrArg (fun y : SLt 3 => (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) h
    exact this
  have hlast : (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 = 1 := by
    have h1 : ((x * x⁻¹ : SLt 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) 3 3 = 1 := by
      rw [mul_inv_cancel]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_four] at h1
    have a0 := e0 3 0 (by decide) (by decide)
    have a1 := e0 3 1 (by decide) (by decide)
    have a2 := e0 3 2 (by decide) (by decide)
    simp only [a0, a1, a2, zero_mul, zero_add] at h1
    exact zmod2_eq_one_of_mul_eq_one _ _ h1
  refine ⟨fun j => (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) j.castSucc 3, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h3 0 0
  · exact h3 0 1
  · exact h3 0 2
  · rfl
  · exact h3 1 0
  · exact h3 1 1
  · exact h3 1 2
  · rfl
  · exact h3 2 0
  · exact h3 2 1
  · exact h3 2 2
  · rfl
  · exact e0 3 0 (by decide) (by decide)
  · exact e0 3 1 (by decide) (by decide)
  · exact e0 3 2 (by decide) (by decide)
  · exact hlast

theorem lev3_s3 (u : Fin 3 → ZMod 2) : lev3 ⟨s3 u, s3_mem_QI u⟩ = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem Rrad1_le_QI : Rrad1 ≤ QI 4 {1} := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_Rrad1_iff.1 hx
  exact r1_mem_QI v

theorem Rrad3_le_QI : Rrad3 ≤ QI 4 {3} := by
  intro x hx
  obtain ⟨u, rfl⟩ := mem_Rrad3_iff.1 hx
  exact s3_mem_QI u

theorem mem_Rrad1_iff_lev1 {x : SLt 4} (hx : x ∈ QI 4 {1}) :
    x ∈ Rrad1 ↔ lev1 ⟨x, hx⟩ = 1 := by
  constructor
  · intro h
    obtain ⟨v, rfl⟩ := mem_Rrad1_iff.1 h
    exact lev1_r1 v
  · intro h
    obtain ⟨v, rfl⟩ := eq_r1_of_lev1_eq_one hx h
    exact r1_mem_Rrad1 v

theorem mem_Rrad3_iff_lev3 {x : SLt 4} (hx : x ∈ QI 4 {3}) :
    x ∈ Rrad3 ↔ lev3 ⟨x, hx⟩ = 1 := by
  constructor
  · intro h
    obtain ⟨u, rfl⟩ := mem_Rrad3_iff.1 h
    exact lev3_s3 u
  · intro h
    obtain ⟨u, rfl⟩ := eq_s3_of_lev3_eq_one hx h
    exact s3_mem_Rrad3 u

theorem Rrad1_normal {x r : SLt 4} (hx : x ∈ QI 4 {1}) (hr : r ∈ Rrad1) :
    x * r * x⁻¹ ∈ Rrad1 := by
  have hrQ := Rrad1_le_QI hr
  have hm : x * r * x⁻¹ ∈ QI 4 {1} := (QI 4 {1}).mul_mem ((QI 4 {1}).mul_mem hx hrQ)
    ((QI 4 {1}).inv_mem hx)
  rw [mem_Rrad1_iff_lev1 hm]
  have e : (⟨x * r * x⁻¹, hm⟩ : ↥(QI 4 {1})) = ⟨x, hx⟩ * ⟨r, hrQ⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, (mem_Rrad1_iff_lev1 hrQ).1 hr]
  simp

theorem Rrad3_normal {x r : SLt 4} (hx : x ∈ QI 4 {3}) (hr : r ∈ Rrad3) :
    x * r * x⁻¹ ∈ Rrad3 := by
  have hrQ := Rrad3_le_QI hr
  have hm : x * r * x⁻¹ ∈ QI 4 {3} := (QI 4 {3}).mul_mem ((QI 4 {3}).mul_mem hx hrQ)
    ((QI 4 {3}).inv_mem hx)
  rw [mem_Rrad3_iff_lev3 hm]
  have e : (⟨x * r * x⁻¹, hm⟩ : ↥(QI 4 {3})) = ⟨x, hx⟩ * ⟨r, hrQ⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, (mem_Rrad3_iff_lev3 hrQ).1 hr]
  simp

theorem not_isPGroup_SLt3 : ¬ IsPGroup 2 (SLt 3) := by
  intro h
  have hdet : Cm.det = 1 := by decide
  let c : SLt 3 := ⟨Cm, hdet⟩
  have hpow : c ^ 7 = 1 := by
    apply Subtype.ext
    show Cm ^ 7 = 1
    exact Cm_pow
  have hne : c ≠ 1 := fun h1 => Cm_ne (congrArg (fun x : SLt 3 => (x : Matrix (Fin 3) (Fin 3)
    (ZMod 2))) h1)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ho : orderOf c = 7 := orderOf_eq_prime hpow hne
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h) c
  rw [ho] at hk
  have h7 : (7 : ℕ) ∣ 2 ^ k := hk ▸ dvd_refl 7
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h7)
  omega

theorem map_eq_bot_of_normal2 {Q : Subgroup (SLt 4)} (ψ : ↥Q →* SLt 3)
    (hψ : Function.Surjective ψ) (N : Subgroup (SLt 4)) (hN : N ≤ Q)
    (hnorm : ∀ x ∈ Q, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (h2 : IsPGroup 2 ↥N) :
    ∀ n (hn : n ∈ N), ψ ⟨n, hN hn⟩ = 1 := by
  have hsimple : IsSimpleGroup (SLt 3) :=
    CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 (by norm_num)
  set N' : Subgroup (SLt 3) := (N.subgroupOf Q).map ψ with hN'
  have hnormal : N'.Normal := by
    refine ⟨fun y hy z => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨b, rfl⟩ := hψ z
    refine Subgroup.mem_map.2 ⟨b * a * b⁻¹, ?_, by simp⟩
    exact hnorm b b.2 a (Subgroup.mem_subgroupOf.1 ha)
  have hp2 : IsPGroup 2 ↥N' := by
    have h2' : IsPGroup 2 ↥(N.subgroupOf Q) := by
      intro x
      obtain ⟨k, hk⟩ := h2 ⟨(x : Q).1, Subgroup.mem_subgroupOf.1 x.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun y : ↥N => (y : SLt 4)) hk
      simpa using this
    exact h2'.map ψ
  have := hnormal
  rcases hsimple.eq_bot_or_eq_top_of_normal N' with hb | ht
  · intro n hn
    have : ψ ⟨n, hN hn⟩ ∈ N' := Subgroup.mem_map.2 ⟨⟨n, hN hn⟩, Subgroup.mem_subgroupOf.2 hn, rfl⟩
    rw [hb] at this
    exact this
  · exfalso
    apply not_isPGroup_SLt3
    have : IsPGroup 2 ↥(⊤ : Subgroup (SLt 3)) := ht ▸ hp2
    exact this.of_equiv Subgroup.topEquiv

theorem le_Rrad1_of_normal2 (N : Subgroup (SLt 4)) (hN : N ≤ QI 4 {1})
    (hnorm : ∀ x ∈ QI 4 {1}, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (h2 : IsPGroup 2 ↥N) : N ≤ Rrad1 := by
  intro n hn
  exact (mem_Rrad1_iff_lev1 (hN hn)).2
    (map_eq_bot_of_normal2 lev1 lev1_surjective N hN hnorm h2 n hn)

theorem le_Rrad3_of_normal2 (N : Subgroup (SLt 4)) (hN : N ≤ QI 4 {3})
    (hnorm : ∀ x ∈ QI 4 {3}, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (h2 : IsPGroup 2 ↥N) : N ≤ Rrad3 := by
  intro n hn
  exact (mem_Rrad3_iff_lev3 (hN hn)).2
    (map_eq_bot_of_normal2 lev3 lev3_surjective N hN hnorm h2 n hn)

end CFSG.Quasithin.SzC4
