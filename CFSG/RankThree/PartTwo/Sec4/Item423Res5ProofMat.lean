module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofMono
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofCoreDefs
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

namespace Res423Five

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

section Conj

theorem mk_mem_normalizer (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) :
    ProjGenLinGroup.mk g ∈ Subgroup.normalizer
      ((projImage (slPi π 3 (p ^ f) K) : Subgroup (ProjGenLinGroup (Fin 3) K)) :
        Set (ProjGenLinGroup (Fin 3) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨g * s * g⁻¹, conj_mem_slPi hπ hg hs, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨s, hs, hsx⟩
    refine ⟨g⁻¹ * s * g, ?_, ?_⟩
    · have := conj_mem_slPi hπ (inv_mem hg) hs
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, map_inv, hsx]
      group

@[expose] noncomputable def pglConj (hK : PiField π p f K) :
    glPi π 3 (p ^ f) K →* MulAut (projImage (slPi π 3 (p ^ f) K)) :=
  (projImage (slPi π 3 (p ^ f) K)).normalizerMonoidHom.comp
    (((ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp
      (glPi π 3 (p ^ f) K).subtype).codRestrict _ fun g => mk_mem_normalizer hK g.2)

variable (hK : PiField π p f K)

theorem coe_pglConj_apply (g : glPi π 3 (p ^ f) K) (x : projImage (slPi π 3 (p ^ f) K)) :
    ((pglConj hK g x : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g : GL (Fin 3) K) * x * (ProjGenLinGroup.mk (g : GL (Fin 3) K))⁻¹ :=
  rfl

theorem pglConj_eq_of_mk_eq {g g' : glPi π 3 (p ^ f) K}
    (h : ProjGenLinGroup.mk (g : GL (Fin 3) K) = ProjGenLinGroup.mk (g' : GL (Fin 3) K)) :
    pglConj hK g = pglConj hK g' := by
  ext x
  rw [coe_pglConj_apply, coe_pglConj_apply, h]

theorem pglConj_eq_one_iff (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (g : glPi π 3 (p ^ f) K) :
    pglConj hK g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  constructor
  · intro h
    refine CFSG.RankThree.PartTwo.Sec13.mem_statedScalars_of_commute_mk hK hq hq2
      fun s hs => ?_
    have h1 := congrArg (fun σ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      ((σ ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩ :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) h
    simp only [coe_pglConj_apply, MulAut.one_apply] at h1
    calc ProjGenLinGroup.mk (g : GL (Fin 3) K) * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk (g : GL (Fin 3) K) * ProjGenLinGroup.mk s *
          (ProjGenLinGroup.mk (g : GL (Fin 3) K))⁻¹ * ProjGenLinGroup.mk (g : GL (Fin 3) K) := by
          group
      _ = ProjGenLinGroup.mk s * ProjGenLinGroup.mk (g : GL (Fin 3) K) := by rw [h1]
  · intro h
    have h1 : ProjGenLinGroup.mk (g : GL (Fin 3) K) = 1 := mk_eq_one_iff_mem_statedScalars.mpr h
    ext x
    rw [coe_pglConj_apply, h1, MulAut.one_apply]
    group

theorem pglConj_commute_iff (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (g h : glPi π 3 (p ^ f) K) :
    pglConj hK g * pglConj hK h = pglConj hK h * pglConj hK g ↔
      (g : GL (Fin 3) K) * h * (g : GL (Fin 3) K)⁻¹ * (h : GL (Fin 3) K)⁻¹ ∈
        StatedScalars (Fin 3) K := by
  have e : (g : GL (Fin 3) K) * h * (g : GL (Fin 3) K)⁻¹ * (h : GL (Fin 3) K)⁻¹ =
      ((g * h * g⁻¹ * h⁻¹ : glPi π 3 (p ^ f) K) : GL (Fin 3) K) := by simp
  rw [e, ← pglConj_eq_one_iff hK hq hq2, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro hc
    rw [hc]
    group
  · intro hc
    calc pglConj hK g * pglConj hK h =
        pglConj hK g * pglConj hK h * (pglConj hK g)⁻¹ * (pglConj hK h)⁻¹ *
          (pglConj hK h * pglConj hK g) := by group
      _ = pglConj hK h * pglConj hK g := by rw [hc, one_mul]

theorem conj_mk_eq_pglConj {g : GL (Fin 3) K} (hg : g ∈ slPi π 3 (p ^ f) K)
    (hgH : g ∈ glPi π 3 (p ^ f) K) :
    MulAut.conj (⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      projImage (slPi π 3 (p ^ f) K)) = pglConj hK ⟨g, hgH⟩ := by
  ext x
  rw [coe_pglConj_apply]
  rfl

theorem exists_conj_eq_pglConj (w : projImage (slPi π 3 (p ^ f) K)) :
    ∃ (g : GL (Fin 3) K) (_ : g ∈ slPi π 3 (p ^ f) K) (hgH : g ∈ glPi π 3 (p ^ f) K),
      MulAut.conj w = pglConj hK ⟨g, hgH⟩ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨g, hg, hgw⟩ := w.2
  refine ⟨g, hg, slPi_le_glPi hπ hg, ?_⟩
  rw [← conj_mk_eq_pglConj hK hg]
  congr 1
  exact Subtype.ext hgw.symm

theorem mem_inndiagPi_iff_pglConj (β : MulAut (projImage (slPi π 3 (p ^ f) K))) :
    β ∈ Sec14.inndiagPi π (p ^ f) K ↔ ∃ g, β = pglConj hK g := by
  constructor
  · rintro ⟨g, hg, hβ⟩
    exact ⟨⟨g, hg⟩, by ext x; rw [hβ x, coe_pglConj_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, fun x => coe_pglConj_apply hK g x⟩

theorem conj_range_normal :
    ((MulAut.conj : projImage (slPi π 3 (p ^ f) K) →*
      MulAut (projImage (slPi π 3 (p ^ f) K))).range).Normal :=
  ⟨fun _ ⟨w, hw⟩ g => ⟨g w, by rw [← hw, Res423Two.mulAut_mul_conj_mul_inv]⟩⟩

end Conj

section Std

theorem diagUnits_one' : diagUnits (1 : Kˣ) 1 1 = 1 := by
  apply Units.ext
  rw [coe_diagUnits, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal]

@[expose] noncomputable def stdDiag (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    rootsOfUnity 3 K × rootsOfUnity 3 K →* glPi π 3 (p ^ f) K where
  toFun st := ⟨diagUnits 1 (st.1 : Kˣ) (st.2 : Kˣ), diagUnits_mem_glPi hK (one_mem _)
    (cube_root_mem_qSubPi hq st.1.2) (cube_root_mem_qSubPi hq st.2.2)⟩
  map_one' := Subtype.ext diagUnits_one'
  map_mul' st st' := Subtype.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, diagUnits_mul, mul_one])

variable (hK : PiField π p f K) (hq : ModThree π (p ^ f))

theorem coe_stdDiag (st : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    ((stdDiag hK hq st : glPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      diagUnits 1 (st.1 : Kˣ) (st.2 : Kˣ) :=
  rfl

@[expose] noncomputable def stdPlane : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))) :=
  ((pglConj hK).comp (stdDiag hK hq)).range

theorem mem_stdPlane {β : MulAut (projImage (slPi π 3 (p ^ f) K))} :
    β ∈ stdPlane hK hq ↔ ∃ st, pglConj hK (stdDiag hK hq st) = β :=
  Iff.rfl

theorem stdPlane_le_inndiagPi : stdPlane hK hq ≤ Sec14.inndiagPi π (p ^ f) K := by
  rintro _ ⟨st, rfl⟩
  exact (mem_inndiagPi_iff_pglConj hK _).mpr ⟨_, rfl⟩

theorem stdPlane_comm : ∀ x ∈ stdPlane hK hq, ∀ y ∈ stdPlane hK hq, x * y = y * x := by
  rintro _ ⟨st, rfl⟩ _ ⟨st', rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem pow_three_of_mem_stdPlane : ∀ x ∈ stdPlane hK hq, x ^ 3 = 1 := by
  rintro _ ⟨st, rfl⟩
  have h3 : st ^ 3 = 1 := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (mem_rootsOfUnity _ _).mp st.1.2
    · exact (mem_rootsOfUnity _ _).mp st.2.2
  rw [← map_pow, h3, map_one]

theorem stdDiag_mem_statedScalars_iff (st : rootsOfUnity 3 K × rootsOfUnity 3 K) :
    ((stdDiag hK hq st : glPi π 3 (p ^ f) K) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K ↔
      st = 1 := by
  rw [coe_stdDiag]
  have h := scalar_mul_diagUnits_mem_iff (K := K) 1 (st.1 : Kˣ) (st.2 : Kˣ)
  rw [map_one, one_mul] at h
  rw [h]
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem pglConj_stdDiag_injective (hq2 : 2 < p ^ f) :
    Function.Injective ((pglConj hK).comp (stdDiag hK hq)) := by
  rw [injective_iff_map_eq_one]
  intro st h
  exact (stdDiag_mem_statedScalars_iff hK hq st).mp
    ((pglConj_eq_one_iff hK hq hq2 _).mp h)

theorem card_stdPlane (hq2 : 2 < p ^ f) : Nat.card (stdPlane hK hq) = 9 := by
  rw [stdPlane, ← Nat.card_congr (MonoidHom.ofInjective
    (pglConj_stdDiag_injective hK hq hq2)).toEquiv, Nat.card_prod,
    card_rootsOfUnity_three hK hq]

end Std

section TypeOne

theorem commute_diagonal_of_commute {M : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (hd : Function.Injective d) (h : M * diagonal d = diagonal d * M) (e : Fin 3 → K) :
    M * diagonal e = diagonal e * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · rw [hij, mul_comm]
  · rw [entry_eq_zero_of_commute_diagonal h (fun h' => hij (hd h')), zero_mul, mul_zero]

theorem commute_of_commute_pow_three {G : Type*} [Group G] {d x : G}
    (hd3 : Nat.Coprime 3 (orderOf d)) (h : Commute (d ^ 3) x) : Commute d x := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 3 + b * (orderOf d : ℤ) = 1 := by
    obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.mpr hd3
    exact ⟨a, b, by exact_mod_cast h⟩
  have e : d = (d ^ 3) ^ a * (d ^ orderOf d) ^ b := by
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add,
      show ((3 : ℕ) : ℤ) * a + (orderOf d : ℤ) * b = 1 by push_cast; linarith, zpow_one]
  rw [e, pow_orderOf_eq_one, _root_.one_zpow, mul_one]
  exact h.zpow_left a

variable (hK : PiField π p f K) (hq : ModThree π (p ^ f))

theorem commute_stdPlane_of_commute_diagonal (X : glPi π 3 (p ^ f) K)
    (hX : ∀ e : Fin 3 → K, ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal e =
      diagonal e * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    ∀ x ∈ stdPlane hK hq, pglConj hK X * x = x * pglConj hK X := by
  rintro _ ⟨st, rfl⟩
  rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_stdDiag,
    coe_diagUnits]
  exact hX _

theorem typeOne_stdPlane (hq2 : 2 < p ^ f) {st : rootsOfUnity 3 K × rootsOfUnity 3 K}
    (hs : st.1 ≠ 1) (ht : st.2 ≠ 1) (hst : st.1 ≠ st.2)
    {d : MulAut (projImage (slPi π 3 (p ^ f) K))} (hd : d ∈ Sec14.inndiagPi π (p ^ f) K)
    (hdb : d * pglConj hK (stdDiag hK hq st) = pglConj hK (stdDiag hK hq st) * d)
    (hd3 : Nat.Coprime 3 (orderOf d)) : ∀ x ∈ stdPlane hK hq, d * x = x * d := by
  obtain ⟨g, rfl⟩ := (mem_inndiagPi_iff_pglConj hK d).mp hd
  obtain ⟨l, hl⟩ := (pglConj_commute_iff hK hq hq2 g (stdDiag hK hq st)).mp hdb
  set D : GL (Fin 3) K := diagUnits 1 (st.1 : Kˣ) (st.2 : Kˣ) with hD
  rw [coe_stdDiag, ← hD] at hl
  have hgD : (g : GL (Fin 3) K) * D * (g : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l * D := by
    rw [hl]
    group
  have hl3 : l ^ 3 = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hgD
    rw [map_mul, map_mul, map_inv, map_mul, mul_comm (GeneralLinearGroup.det
      (g : GL (Fin 3) K)), mul_assoc, mul_inv_cancel, mul_one] at h1
    have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) l) = l ^ 3 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
    rw [h2] at h1
    exact mul_eq_right.mp h1.symm
  have hsc3 : GeneralLinearGroup.scalar (Fin 3) l ^ 3 = 1 := by
    rw [← map_pow (GeneralLinearGroup.scalar (Fin 3)) l 3, hl3, map_one]
  have hg3 : (g : GL (Fin 3) K) ^ 3 * D = D * (g : GL (Fin 3) K) ^ 3 := by
    have h1 := Sec11.KS11LieProof.pow_conj_eq_of_conj_eq
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l (g : GL (Fin 3) K)).symm hgD 3
    rw [hsc3, one_mul] at h1
    calc (g : GL (Fin 3) K) ^ 3 * D =
        (g : GL (Fin 3) K) ^ 3 * D * ((g : GL (Fin 3) K) ^ 3)⁻¹ * (g : GL (Fin 3) K) ^ 3 := by
          group
      _ = D * (g : GL (Fin 3) K) ^ 3 := by rw [h1]
  have hg3' := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hg3
  simp only [Units.val_mul, hD, coe_diagUnits] at hg3'
  have hinj : Function.Injective ![((1 : Kˣ) : K), ((st.1 : Kˣ) : K), ((st.2 : Kˣ) : K)] := by
    have h1 : ((st.1 : Kˣ) : K) ≠ 1 := fun h => hs (Subtype.ext (Units.ext h))
    have h2 : ((st.2 : Kˣ) : K) ≠ 1 := fun h => ht (Subtype.ext (Units.ext h))
    have h12 : ((st.1 : Kˣ) : K) ≠ ((st.2 : Kˣ) : K) := fun h =>
      hst (Subtype.ext (Units.ext h))
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | (simp at hij
         first
          | exact absurd hij.symm h1 | exact absurd hij h1 | exact absurd hij.symm h2
          | exact absurd hij h2 | exact absurd hij h12 | exact absurd hij.symm h12
          | exact absurd hij hs | exact absurd hij ht)
  have hcomm := commute_diagonal_of_commute hinj hg3'
  intro x hx
  refine (commute_of_commute_pow_three hd3 ?_).eq
  rw [← map_pow (pglConj hK) g 3]
  exact commute_stdPlane_of_commute_diagonal hK hq (g ^ 3) (fun e => by
    rw [SubgroupClass.coe_pow]
    exact hcomm e) x hx

end TypeOne

section Block

@[expose] def cyc (m : Fin 3) : GL (Fin 3) K :=
  ![1, cycThree, cycThree⁻¹] m

theorem cyc_mem_slPi (hπ : π = false → UnitaryFieldData p f K) (m : Fin 3) :
    cyc (K := K) m ∈ slPi π 3 (p ^ f) K := by
  fin_cases m
  · exact one_mem _
  · exact cycThree_mem_slPi hπ
  · exact inv_mem (cycThree_mem_slPi hπ)

theorem coe_cyc_diagE (m : Fin 3) (e : Kˣ) :
    ((cyc m * diagE e * (cyc m)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => if i = m then (e : K) else 1 := by
  fin_cases m
  · change ((1 * diagE e * 1⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [inv_one, one_mul, mul_one, coe_diagE]
    congr 1
    funext i
    fin_cases i <;> simp
  · change ((cycThree * diagE e * cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [diagE, cycThree_conj_diagUnits, coe_diagUnits]
    congr 1
    funext i
    fin_cases i <;> simp
  · change ((cycThree⁻¹ * diagE e * cycThree⁻¹⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = _
    rw [inv_inv, diagE, cycThree_inv_conj_diagUnits, coe_diagUnits]
    congr 1
    funext i
    fin_cases i <;> simp

theorem inv_cyc_conj_apply_zero (m : Fin 3) (X : GL (Fin 3) K) :
    (((cyc m)⁻¹ * X * cyc m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      (X : Matrix (Fin 3) (Fin 3) K) m m := by
  have hc : ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl
  fin_cases m
  · change ((1⁻¹ * X * 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = _
    rw [inv_one, one_mul, mul_one]
    rfl
  · change ((cycThree⁻¹ * X * cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = _
    rw [Units.val_mul, Units.val_mul, hc, coe_cycThree]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
  · change ((cycThree⁻¹⁻¹ * X * cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = _
    rw [inv_inv, Units.val_mul, Units.val_mul, hc, coe_cycThree]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]

theorem commute_of_rowcol {m : Fin 3} {X : Matrix (Fin 3) (Fin 3) K}
    (hrow : ∀ j, X m j = (1 : Matrix (Fin 3) (Fin 3) K) m j)
    (hcol : ∀ i, X i m = (1 : Matrix (Fin 3) (Fin 3) K) i m) (e : K) :
    X * diagonal (fun i => if i = m then e else 1) =
      diagonal (fun i => if i = m then e else 1) * X := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i = m
  · subst hi
    by_cases hj : j = i
    · subst hj
      ring
    · rw [hrow j, Matrix.one_apply_ne (Ne.symm hj)]
      ring
  · by_cases hj : j = m
    · subst hj
      rw [hcol i, Matrix.one_apply_ne hi]
      ring
    · simp [hi, hj]

theorem exists_block_of_rowcol (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (m : Fin 3)
    {X : GL (Fin 3) K} (hX : X ∈ slPi π 3 (p ^ f) K)
    (hrow : ∀ j, (X : Matrix (Fin 3) (Fin 3) K) m j = (1 : Matrix (Fin 3) (Fin 3) K) m j)
    (hcol : ∀ i, (X : Matrix (Fin 3) (Fin 3) K) i m = (1 : Matrix (Fin 3) (Fin 3) K) i m) :
    ∃ B ∈ slPi π 2 (p ^ f) K, X = cyc m * blockHom B * (cyc m)⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have he1 : Units.mk0 τ hτ0 ≠ 1 := fun h => hτ1 (by rw [← Units.val_mk0 hτ0, h, Units.val_one])
  have hcm := slPi_le_glPi hπ (cyc_mem_slPi hπ m)
  have hX'L : (cyc m)⁻¹ * X * cyc m ∈ slPi π 3 (p ^ f) K := by
    have := conj_mem_slPi hπ (inv_mem hcm) hX
    rwa [inv_inv] at this
  have hcomm : X * (cyc m * diagE (Units.mk0 τ hτ0) * (cyc m)⁻¹) =
      (cyc m * diagE (Units.mk0 τ hτ0) * (cyc m)⁻¹) * X := by
    apply Units.ext
    rw [Units.val_mul X, Units.val_mul _ X, coe_cyc_diagE]
    exact commute_of_rowcol hrow hcol _
  have hX'C : (cyc m)⁻¹ * X * cyc m ∈ Subgroup.centralizer {diagE (Units.mk0 τ hτ0)} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (cyc m)⁻¹ * X * cyc m * diagE (Units.mk0 τ hτ0) =
        (cyc m)⁻¹ * (X * (cyc m * diagE (Units.mk0 τ hτ0) * (cyc m)⁻¹)) * cyc m := by group
      _ = (cyc m)⁻¹ * ((cyc m * diagE (Units.mk0 τ hτ0) * (cyc m)⁻¹) * X) * cyc m := by
          rw [hcomm]
      _ = diagE (Units.mk0 τ hτ0) * ((cyc m)⁻¹ * X * cyc m) := by group
  obtain ⟨M, hM, hMX⟩ : (cyc m)⁻¹ * X * cyc m ∈ (glPi π 2 (p ^ f) K).map blockHom := by
    rw [← centralizer_diagE_eq hK he1]
    exact Subgroup.mem_inf.mpr ⟨hX'L, hX'C⟩
  have h00 := inv_cyc_conj_apply_zero m X
  rw [← hMX, coe_blockHom, hrow m, Matrix.one_apply_eq] at h00
  have hdet : GeneralLinearGroup.det M = 1 := by
    have h1 : (((GeneralLinearGroup.det M)⁻¹ : Kˣ) : K) = 1 := by
      simpa [blockMat] using h00
    exact inv_eq_one.mp (Units.ext h1)
  refine ⟨M, (mem_slPi_iff hπ).mpr ⟨hM, ?_⟩, ?_⟩
  · rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  · rw [hMX]
    group

@[expose] def blockSet (π : Bool) (q : ℕ) (K : Type) [Field K] : Set (GL (Fin 3) K) :=
  {X | ∃ m : Fin 3, ∃ B ∈ slPi π 2 q K, X = cyc m * blockHom B * (cyc m)⁻¹}

theorem exists_ne_ne : ∀ i j : Fin 3, i ≠ j → ∃ m : Fin 3, m ≠ i ∧ m ≠ j := by
  decide

theorem slPi_true_le_closure (hK : PiField true p f K) (hq : ModThree true (p ^ f)) :
    slPi true 3 (p ^ f) K ≤ Subgroup.closure (blockSet true (p ^ f) K) := by
  intro g hg
  have hg' : g ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range := by
    rw [← CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL]
    exact hg
  obtain ⟨M, rfl⟩ := hg'
  have hgen : ∀ (N : SpecialLinearGroup (Fin 3) K) (m : Fin 3),
      (∀ j, (N : Matrix (Fin 3) (Fin 3) K) m j = (1 : Matrix (Fin 3) (Fin 3) K) m j) →
      (∀ i, (N : Matrix (Fin 3) (Fin 3) K) i m = (1 : Matrix (Fin 3) (Fin 3) K) i m) →
        SpecialLinearGroup.toGL N ∈ Subgroup.closure (blockSet true (p ^ f) K) := by
    intro N m hr hc
    obtain ⟨B, hB, hNB⟩ := exists_block_of_rowcol hK hq m (X := SpecialLinearGroup.toGL N)
      ((mem_slPi_true _).mpr N.2) hr hc
    exact Subgroup.subset_closure ⟨m, B, hB, hNB⟩
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun N =>
    SpecialLinearGroup.toGL N ∈ Subgroup.closure (blockSet true (p ^ f) K)) M ?_ ?_ ?_
  · intro i j hij c hc
    obtain ⟨m, hmi, hmj⟩ := exists_ne_ne i j hij
    refine hgen _ m (fun l => ?_) (fun l => ?_)
    · simp [SpecialLinearGroup.diag2n, Matrix.diagonal_apply, Matrix.one_apply, hmi, hmj]
    · by_cases hl : l = m
      · subst hl
        simp [SpecialLinearGroup.diag2n, hmi, hmj]
      · simp [SpecialLinearGroup.diag2n, hl]
  · intro i j hij a
    obtain ⟨m, hmi, hmj⟩ := exists_ne_ne i j hij
    refine hgen _ m (fun l => ?_) (fun l => ?_)
    · simp [SpecialLinearGroup.transvection, Matrix.transvection, Matrix.add_apply, Ne.symm hmi]
    · simp [SpecialLinearGroup.transvection, Matrix.transvection, Matrix.add_apply, Ne.symm hmj]
  · intro A B hA hB
    rw [map_mul]
    exact mul_mem hA hB

theorem slPi_false_le_closure (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    (hq2 : 2 < p ^ f) :
    slPi false 3 (p ^ f) K ≤ Subgroup.closure (blockSet false (p ^ f) K) := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have : CharP K p := hK.charP
  have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
  have hq2' : p ^ f ≠ 2 := by omega
  have hSU := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hcard 3
  intro g hg
  have hg' : g ∈ CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution K p f) 3 := by
    rw [hSU]
    exact hg
  have htop := CFSG.ClassicalInvolution.Phan.iSup_range_blockEmb2 hcard hq2' 2
  have hx : (⟨g, hg'⟩ : CFSG.ClassicalInvolution.Phan.Su K p f 3) ∈
      ⨆ i : Fin 2, (CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 2 i).range :=
    htop ▸ Subgroup.mem_top _
  have hmem : ∀ x : CFSG.ClassicalInvolution.Phan.Su K p f 3,
      (x : GL (Fin 3) K) ∈ slPi false 3 (p ^ f) K := fun x =>
    (Subgroup.ext_iff.mp hSU _).mp x.2
  refine (iSup_le fun i => ?_ :
    ⨆ i : Fin 2, (CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 2 i).range ≤
      (Subgroup.closure (blockSet false (p ^ f) K)).comap
        (CFSG.LieType.Universal.Unitary.SUid
          (CFSG.LieType.BorelTits.unitaryInvolution K p f) 3).subtype) hx
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_comap]
  fin_cases i
  · have hcoe := CFSG.ClassicalInvolution.Phan.coe_coe_blockEmb2 2 0 A
    obtain ⟨B, hB, hXB⟩ := exists_block_of_rowcol hK hq 2
      (X := ((CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 2 0 A :
        CFSG.ClassicalInvolution.Phan.Su K p f 3) : GL (Fin 3) K)) (hmem _)
      (fun j => by
        rw [hcoe]
        exact CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left _ (by simp) _)
      (fun i => by
        rw [hcoe]
        exact CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_right _ _ (by simp))
    exact Subgroup.subset_closure ⟨2, B, hB, hXB⟩
  · have hcoe := CFSG.ClassicalInvolution.Phan.coe_coe_blockEmb2 2 1 A
    obtain ⟨B, hB, hXB⟩ := exists_block_of_rowcol hK hq 0
      (X := ((CFSG.ClassicalInvolution.Phan.blockEmb2 K p f 2 1 A :
        CFSG.ClassicalInvolution.Phan.Su K p f 3) : GL (Fin 3) K)) (hmem _)
      (fun j => by
        rw [hcoe]
        exact CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left _ (by simp) _)
      (fun i => by
        rw [hcoe]
        exact CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_right _ _ (by simp))
    exact Subgroup.subset_closure ⟨0, B, hB, hXB⟩

theorem slPi_le_closure_blockSet (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) : slPi π 3 (p ^ f) K ≤ Subgroup.closure (blockSet π (p ^ f) K) := by
  cases π
  · exact slPi_false_le_closure hK hq hq2
  · exact slPi_true_le_closure hK hq

end Block

end Res423Five

end CFSG.RankThree.PartTwo.Sec4
