module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.Quasithin.EmptyFaithful.S151S4A
public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.QuasithinUnique
open CFSG.Quasithin.S151S4
open scoped Matrix

noncomputable def statedSLNatAct (K : Type) [Field K] :
    ↥(StatedSL 2 K) →* MulAut (SL2Model.Wm K) :=
  SL2Model.natAct.comp
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.toMonoidHom

noncomputable def statedSLNatImage (K : Type) [Field K] :
    Subgroup (MulAut (SL2Model.Wm K)) :=
  (statedSLNatAct K).range

@[expose] def line0 (K : Type) [Field K] : Subgroup (SL2Model.Wm K) where
  carrier := {x | (Multiplicative.toAdd x) 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, toAdd_mul, Pi.add_apply] at hx hy ⊢
    rw [hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    simpa using hx

theorem mem_line0 {K : Type} [Field K] {x : SL2Model.Wm K} :
    x ∈ line0 K ↔ (Multiplicative.toAdd x) 1 = 0 := Iff.rfl

theorem fixedPointSubgroup_Rg_image (K : Type) [Field K] :
    letI : MulDistribMulAction ↥((SL2Model.Rg K).map SL2Model.natAct) (SL2Model.Wm K) :=
      MulDistribMulAction.compHom (SL2Model.Wm K) ((SL2Model.Rg K).map SL2Model.natAct).subtype
    fixedPointSubgroup ↥((SL2Model.Rg K).map SL2Model.natAct) (SL2Model.Wm K) = line0 K := by
  letI : MulDistribMulAction ↥((SL2Model.Rg K).map SL2Model.natAct) (SL2Model.Wm K) :=
    MulDistribMulAction.compHom (SL2Model.Wm K) ((SL2Model.Rg K).map SL2Model.natAct).subtype
  ext x
  constructor
  · intro hx
    have hmem : (SL2Model.natAct (SL2Model.e12 (1 : K))) ∈
        (SL2Model.Rg K).map SL2Model.natAct := by
      exact Subgroup.mem_map_of_mem _ (SL2Model.e12_mem_Rg 1)
    have hfix := hx ⟨_, hmem⟩
    have h1 : SL2Model.natAct (SL2Model.e12 (1 : K)) x = x := hfix
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
    rw [SL2Model.natAct_apply, toAdd_ofAdd, SL2Model.e12_smul] at h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_one] at h2
    rw [mem_line0]
    linear_combination h2
  · intro hx
    rw [mem_line0] at hx
    intro u
    obtain ⟨a, ha, hau⟩ := Subgroup.mem_map.mp u.2
    change (u : MulAut (SL2Model.Wm K)) x = x
    rw [← hau]
    obtain ⟨t, rfl⟩ := SL2Model.mem_Rg.mp ha
    show SL2Model.natAct (SL2Model.e12 t) x = x
    apply Multiplicative.toAdd.injective
    rw [SL2Model.natAct_apply, toAdd_ofAdd, SL2Model.e12_smul]
    ext i
    fin_cases i <;> simp [hx]

section LineStabilizer

open CFSG.Quasithin.S151S4

theorem Bsub_smul_mem_line0 (K : Type) [Field K] {A : SL2 K} (hA : A ∈ Bsub K)
    {x : SL2Model.Wm K} (hx : x ∈ line0 K) :
    letI : MulDistribMulAction (SL2 K) (SL2Model.Wm K) :=
      MulDistribMulAction.compHom (SL2Model.Wm K) SL2Model.natAct
    A • x ∈ line0 K := by
  letI : MulDistribMulAction (SL2 K) (SL2Model.Wm K) :=
    MulDistribMulAction.compHom (SL2Model.Wm K) SL2Model.natAct
  rw [mem_line0] at hx ⊢
  change (Multiplicative.toAdd (SL2Model.natAct A x)) 1 = 0
  rw [SL2Model.natAct_apply, toAdd_ofAdd, SL2Model.smul_eq_mulVec']
  rw [mem_Bsub] at hA
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA, hx]

end LineStabilizer

section FixedPointConjugation

variable {V : Type} [Group V]

theorem fixedPointSubgroup_map_conj (A : Subgroup (MulAut V)) (h : MulAut V) :
    letI : MulDistribMulAction ↥(A.map (MulAut.conj h).toMonoidHom) V :=
      MulDistribMulAction.compHom V (A.map (MulAut.conj h).toMonoidHom).subtype
    letI : MulDistribMulAction ↥A V :=
      MulDistribMulAction.compHom V A.subtype
    fixedPointSubgroup ↥(A.map (MulAut.conj h).toMonoidHom) V =
      (fixedPointSubgroup ↥A V).map h.toMonoidHom := by
  letI : MulDistribMulAction ↥(A.map (MulAut.conj h).toMonoidHom) V :=
    MulDistribMulAction.compHom V (A.map (MulAut.conj h).toMonoidHom).subtype
  letI : MulDistribMulAction ↥A V :=
    MulDistribMulAction.compHom V A.subtype
  ext v
  constructor
  · intro hv
    refine Subgroup.mem_map.mpr ⟨h⁻¹ v, ?_, by simp⟩
    intro a
    have hmem : h * (a : MulAut V) * h⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem _ a.2
    have hfix := hv ⟨_, hmem⟩
    change (h * (a : MulAut V) * h⁻¹) v = v at hfix
    have := congrArg (fun w => h⁻¹ w) hfix
    change (a : MulAut V) (h⁻¹ v) = h⁻¹ v
    simpa [MulAut.mul_apply, mul_assoc] using this
  · rintro ⟨w, hw, rfl⟩
    intro a
    obtain ⟨b, hb, hau⟩ := Subgroup.mem_map.mp a.2
    change (a : MulAut V) (h w) = h w
    rw [← hau]
    change (h * (b : MulAut V) * h⁻¹) (h w) = h w
    simp only [MulAut.mul_apply]
    rw [MulAut.inv_apply_self]
    have hbw := hw ⟨b, hb⟩
    change (b : MulAut V) w = w at hbw
    rw [hbw]

end FixedPointConjugation

section Model

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem natImageRg_isSylowTwoOf :
    IsSylowTwoOf ((SL2Model.Rg K).map (SL2Model.natAct (F := K)))
      (SL2Model.natAct (F := K)).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Matrix.SpecialLinearGroup (Fin 2) K →* MulAut (SL2Model.Wm K) := SL2Model.natAct
  let Q : Sylow 2 f.range :=
    (SL2Model.Rg_isPGroup (F := K)).toSylow (SL2Model.Rg_index_odd (F := K)) |>.mapSurjective
      (MonoidHom.rangeRestrict_surjective f)
  have hcomp : f.range.subtype.comp f.rangeRestrict = f := by
    ext x
    rfl
  have hcoe : ((Q : Subgroup f.range).map f.range.subtype) =
      (SL2Model.Rg K).map f := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, hcomp, IsPGroup.toSylow_coe]
  rw [← hcoe]
  exact isSylowTwoOf_map _ Q

end Model

section SetStabilizer

variable {V : Type} [Group V]

@[expose] def setStabilizer (s : Set V) : Subgroup (MulAut V) where
  carrier := {g | ∀ x : V, g x ∈ s ↔ x ∈ s}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [MulAut.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg x
    have := hg (g⁻¹ x)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem mem_setStabilizer {s : Set V} {g : MulAut V} :
    g ∈ setStabilizer s ↔ ∀ x : V, g x ∈ s ↔ x ∈ s := Iff.rfl

theorem map_conj_le_setStabilizer {A : Subgroup (MulAut V)} {s : Set V}
    (hA : A ≤ setStabilizer s) (h : MulAut V) :
    A.map (MulAut.conj h).toMonoidHom ≤ setStabilizer (h '' s) := by
  rintro x ⟨b, hb, rfl⟩ y
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h1 : z = b (h⁻¹ y) := by
      apply h.injective
      simpa [MulAut.mul_apply, mul_assoc] using hzy
    have h2 : h⁻¹ y ∈ s := by
      have := (hA hb (h⁻¹ y)).mp (h1 ▸ hz)
      exact this
    exact ⟨h⁻¹ y, h2, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨b z, (hA hb z).mpr hz, ?_⟩
    simp [MulAut.mul_apply, mul_assoc]

end SetStabilizer
theorem Bsub_map_natAct_le_setStabilizer_line0 (K : Type) [Field K] :
    (Bsub K).map (SL2Model.natAct (F := K)) ≤
      setStabilizer (line0 K : Set (SL2Model.Wm K)) := by
  rintro x ⟨A, hA, rfl⟩ y
  constructor
  · intro hy
    have hAinv : A⁻¹ ∈ Bsub K := (Bsub K).inv_mem hA
    have h1 : (SL2Model.natAct (F := K) A⁻¹) ((SL2Model.natAct (F := K) A) y) ∈ line0 K := by
      change A⁻¹ • ((SL2Model.natAct (F := K) A) y) ∈ line0 K
      exact Bsub_smul_mem_line0 K hAinv (by simpa using hy)
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h1
  · intro hy
    exact Bsub_smul_mem_line0 K hA hy

theorem fixedPointSubgroup_sylow_map {V : Type} [Group V] {H : Subgroup (MulAut V)}
    (S : Sylow 2 H) :
    letI : MulDistribMulAction ↥S V :=
      MulDistribMulAction.compHom V (H.subtype.comp (S : Subgroup H).subtype)
    letI : MulDistribMulAction ↥((S : Subgroup H).map H.subtype) V :=
      MulDistribMulAction.compHom V ((S : Subgroup H).map H.subtype).subtype
    fixedPointSubgroup ↥S V = fixedPointSubgroup ↥((S : Subgroup H).map H.subtype) V := by
  letI : MulDistribMulAction ↥S V :=
    MulDistribMulAction.compHom V (H.subtype.comp (S : Subgroup H).subtype)
  letI : MulDistribMulAction ↥((S : Subgroup H).map H.subtype) V :=
    MulDistribMulAction.compHom V ((S : Subgroup H).map H.subtype).subtype
  ext v
  constructor
  · intro hv x
    obtain ⟨s, hs, hxs⟩ := Subgroup.mem_map.mp x.2
    have h1 := hv ⟨s, hs⟩
    change (s : MulAut V) v = v at h1
    change (x : MulAut V) v = v
    rw [← hxs]
    exact h1
  · intro hv s
    have hmem : (s : MulAut V) ∈ (S : Subgroup H).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype s.2
    have h1 := hv ⟨(s : MulAut V), hmem⟩
    change (s : MulAut V) v = v
    exact h1

section MainModel

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem natImage_rank_one
    (S : Sylow 2 ↥(SL2Model.natAct (F := K)).range)
    (P : Subgroup ↥(SL2Model.natAct (F := K)).range)
    (hSP : (S : Subgroup ↥(SL2Model.natAct (F := K)).range) ≤ P)
    (hP : P ≠ ⊤) :
    letI : MulDistribMulAction ↥(SL2Model.natAct (F := K)).range (SL2Model.Wm K) :=
      MulDistribMulAction.compHom (SL2Model.Wm K) (SL2Model.natAct (F := K)).range.subtype
    letI : MulAction ↥(SL2Model.natAct (F := K)).range (SL2Model.Wm K) :=
      MulDistribMulAction.toMulAction
    letI : MulAction ↥(SL2Model.natAct (F := K)).range (Set (SL2Model.Wm K)) :=
      Set.mulActionSet
    P ≤ MulAction.stabilizer ↥(SL2Model.natAct (F := K)).range
      (fixedPointSubgroup ↥S (SL2Model.Wm K) : Set (SL2Model.Wm K)) := by
  let V := SL2Model.Wm K
  let f := SL2Model.natAct (F := K)
  let H : Subgroup (MulAut V) := f.range
  letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
  letI : MulAction ↥H V := MulDistribMulAction.toMulAction
  letI : MulAction ↥H (Set V) := Set.mulActionSet
  change P ≤ MulAction.stabilizer H (fixedPointSubgroup ↥S V : Set V)
  let SH : Subgroup (MulAut V) := (S : Subgroup H).map H.subtype
  let PH : Subgroup (MulAut V) := P.map H.subtype
  let UH : Subgroup (MulAut V) := (SL2Model.Rg K).map f
  have hSH : IsSylowTwoOf SH H := isSylowTwoOf_map H S
  have hUH : IsSylowTwoOf UH H := natImageRg_isSylowTwoOf K
  obtain ⟨h, hh, hconj⟩ := exists_conj_of_isSylowTwoOf hUH hSH
  have hSH_eq : SH = UH.map (MulAut.conj h).toMonoidHom := by
    ext x
    rw [hconj x]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨h⁻¹ * x * h, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
  have hSHPH : SH ≤ PH := Subgroup.map_mono hSP
  let PH' : Subgroup (MulAut V) := PH.map (MulAut.conj h⁻¹).toMonoidHom
  have hU_le_PH' : UH ≤ PH' := by
    intro x hx
    have hxSH : h * x * h⁻¹ ∈ SH := by
      rw [hSH_eq]
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
    exact Subgroup.mem_map.mpr ⟨h * x * h⁻¹, hSHPH hxSH, by
      simp [MulAut.conj_apply, mul_assoc]⟩
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* H :=
    MonoidHom.ofInjective (SL2Model.natAct_injective (F := K))
  have hPH'_le_H : PH' ≤ H := by
    rintro x ⟨p, hp, rfl⟩
    have hp' : p ∈ Subgroup.map H.subtype P := hp
    have hpH : p ∈ H := Subgroup.map_subtype_le P hp'
    have h1 : h⁻¹ * p ∈ H := H.mul_mem (H.inv_mem hh) hpH
    have h2 : (h⁻¹ * p) * h ∈ H := H.mul_mem h1 hh
    simpa [mul_assoc] using h2
  let Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (PH'.subgroupOf H).map e.symm.toMonoidHom
  have hRg_le_Q : SL2Model.Rg K ≤ Q := by
    intro x hx
    have hfxH : f x ∈ H := ⟨x, rfl⟩
    have hfxPH' : f x ∈ PH' := hU_le_PH' (Subgroup.mem_map_of_mem f hx)
    refine Subgroup.mem_map.mpr ⟨⟨f x, hfxH⟩, Subgroup.mem_subgroupOf.mpr hfxPH', ?_⟩
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  have huU : ∀ t : K, uU t ∈ Q := by
    intro t
    have hx : uU t ∈ SL2Model.Rg K := by
      simpa [SL2Model.e12, uU] using SL2Model.e12_mem_Rg t
    exact hRg_le_Q hx
  rcases borel_or_top huU with hQle | hQtop
  · have hPH'_le_B : PH' ≤ (Bsub K).map f := by
      intro x hx
      have hxH : x ∈ H := hPH'_le_H hx
      have hxQ : e.symm ⟨x, hxH⟩ ∈ Q :=
        Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      have hxB : e.symm ⟨x, hxH⟩ ∈ Bsub K := hQle hxQ
      have hxmap : f (e.symm ⟨x, hxH⟩) ∈ (Bsub K).map f := Subgroup.mem_map_of_mem f hxB
      have hxe : f (e.symm ⟨x, hxH⟩) = x := by
        change (e (e.symm ⟨x, hxH⟩) : MulAut V) = x
        rw [e.apply_symm_apply]
      rwa [hxe] at hxmap
    have hPH_le_Bh : PH ≤ ((Bsub K).map f).map (MulAut.conj h).toMonoidHom := by
      intro x hx
      have hx' : h⁻¹ * x * h ∈ PH' :=
        Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hx'' : h⁻¹ * x * h ∈ (Bsub K).map f := hPH'_le_B hx'
      exact Subgroup.mem_map.mpr ⟨h⁻¹ * x * h, hx'', by simp [MulAut.conj_apply, mul_assoc]⟩
    have hline_sub : fixedPointSubgroup ↥UH V = line0 K :=
      fixedPointSubgroup_Rg_image K
    have hfix : (h '' (line0 K : Set V)) = (fixedPointSubgroup ↥SH V : Set V) := by
      rw [hSH_eq]
      rw [show fixedPointSubgroup ↥(UH.map (MulAut.conj h).toMonoidHom) V =
          (fixedPointSubgroup ↥UH V).map h.toMonoidHom from
        fixedPointSubgroup_map_conj UH h,
        hline_sub, Subgroup.coe_map]
      rfl
    have hB_le : ((Bsub K).map f).map (MulAut.conj h).toMonoidHom ≤
        setStabilizer (fixedPointSubgroup ↥SH V : Set V) := by
      rw [← hfix]
      exact map_conj_le_setStabilizer (Bsub_map_natAct_le_setStabilizer_line0 K) h
    have hPH_le_stab : PH ≤ setStabilizer (fixedPointSubgroup ↥SH V : Set V) :=
      hPH_le_Bh.trans hB_le
    intro p hp
    have hpPH : (p : MulAut V) ∈ PH := Subgroup.mem_map_of_mem H.subtype hp
    have hpstab : (p : MulAut V) ∈ setStabilizer (fixedPointSubgroup ↥SH V : Set V) :=
      hPH_le_stab hpPH
    rw [mem_setStabilizer] at hpstab
    change (p : ↥H) • (fixedPointSubgroup ↥S V : Set V) = (fixedPointSubgroup ↥S V : Set V)
    have hC : (fixedPointSubgroup ↥S V : Set V) = (fixedPointSubgroup ↥SH V : Set V) :=
      congrArg (fun K : Subgroup V => (K : Set V)) (fixedPointSubgroup_sylow_map S)
    rw [hC]
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change (p : MulAut V)⁻¹ v ∈ (fixedPointSubgroup ↥SH V : Set V) ↔
      v ∈ (fixedPointSubgroup ↥SH V : Set V)
    have := hpstab ((p : MulAut V)⁻¹ v)
    rw [MulAut.apply_inv_self] at this
    exact this.symm
  · exfalso
    apply hP
    have hsub : PH'.subgroupOf H = ⊤ := by
      have h1 : Q = (⊤ : Subgroup ↥H).map e.symm.toMonoidHom := by
        rw [hQtop]
        exact (Subgroup.map_top_of_surjective _ e.symm.surjective).symm
      exact Subgroup.map_injective e.symm.injective h1
    have hPH'_top : PH' = H := by
      have hle : H ≤ PH' := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥H) ∈ PH'.subgroupOf H := hsub ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hx'
      exact le_antisymm hPH'_le_H hle
    have hHconj : H.map (MulAut.conj h).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
    have hPH_top : PH = H := by
      have h2 : PH'.map (MulAut.conj h).toMonoidHom = PH := by
        dsimp [PH']
        rw [Subgroup.map_map]
        change Subgroup.map ((MulEquiv.toMonoidHom (MulAut.conj h)).comp
          (MulEquiv.toMonoidHom (MulAut.conj h⁻¹))) PH = PH
        have hcomp : (MulEquiv.toMonoidHom (MulAut.conj h)).comp
            (MulEquiv.toMonoidHom (MulAut.conj h⁻¹)) = MonoidHom.id _ := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [hcomp, Subgroup.map_id]
      rw [← h2, hPH'_top, hHconj]
    have hPtop : P = ⊤ := by
      refine Subgroup.map_injective H.subtype_injective ?_
      have hp : P.map H.subtype = H := hPH_top
      rw [hp]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hPtop

end MainModel

theorem statedSLNatImage_eq_range (K : Type) [Field K] :
    statedSLNatImage K = (SL2Model.natAct (F := K)).range := by
  rw [statedSLNatImage, statedSLNatAct, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.surjective,
    MonoidHom.range_eq_map]

theorem l2ParabolicLeStabilizer_statedSL
    (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (hK : Nat.card K = 2 ^ n) :
    L2ParabolicLeStabilizer (SL2Model.Wm K) (statedSLNatImage K) n := by
  intro hL2 hBin
  rw [statedSLNatImage_eq_range]
  intro S
  letI : MulAction ↥(SL2Model.natAct (F := K)).range (Set (SL2Model.Wm K)) :=
    Set.mulActionSet
  let ℓ : Subgroup (SL2Model.Wm K) := fixedPointSubgroup ↥S (SL2Model.Wm K)
  let Pℓ : Subgroup ↥(SL2Model.natAct (F := K)).range :=
    MulAction.stabilizer ↥(SL2Model.natAct (F := K)).range
      (ℓ : Set (SL2Model.Wm K))
  dsimp only
  intro Pstar hpar hSP hne
  change Pstar ≤ MulAction.stabilizer ↥(SL2Model.natAct (F := K)).range
    (fixedPointSubgroup ↥S (SL2Model.Wm K) : Set (SL2Model.Wm K))
  exact natImage_rank_one K S Pstar hSP hne

theorem natAct_eq_matAut (K : Type) [Field K]
    (B : Matrix.SpecialLinearGroup (Fin 2) K) :
    SL2Model.natAct B =
      CFSG.Quasithin.H.matAut
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K B) := by
  ext x
  simp [SL2Model.natAct_apply, CFSG.Quasithin.H.matAut, SL2Model.smul_eq_mulVec',
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]

theorem natImage_statedSL_eq_statedSLNatImage (K : Type) [Field K] :
    CFSG.Quasithin.H.natImage (StatedSL 2 K) = statedSLNatImage K := by
  ext γ
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨A, ?_⟩
    change SL2Model.natAct
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm A) =
        CFSG.Quasithin.H.matAut A
    rw [natAct_eq_matAut]
    simp
  · rintro ⟨B, rfl⟩
    refine ⟨B, ?_⟩
    change CFSG.Quasithin.H.matAut B =
      SL2Model.natAct
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm B)
    rw [natAct_eq_matAut]
    simp

theorem exists_natural_image_of_binaryNaturalSL
    {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ)
    (hBin : CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ e : W ≃* SL2Model.Wm K,
        H.map (MulAut.congr e).toMonoidHom = statedSLNatImage K := by
  obtain ⟨K, hF, hFin, hK, π, hπ⟩ := hBin
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.exists_mulEquiv_of_realizesVia (StatedSL 2 K) hπ
  refine ⟨K, hF, hFin, hK, e, ?_⟩
  rw [CFSG.Quasithin.H.map_congrHom_eq_natImage (StatedSL 2 K) hπ.1 e he,
    natImage_statedSL_eq_statedSLNatImage K]

@[expose] def L2ParabolicLeStabilizerTransport : Prop :=
  ∀ (W V : Type) [CommGroup W] [CommGroup V] [Finite W] [Finite V]
    (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V)) (n : ℕ) (e : W ≃* V),
    H' = H.map (MulAut.congr e).toMonoidHom →
    L2ParabolicLeStabilizer V H' n →
    L2ParabolicLeStabilizer W H n

theorem l2ParabolicLeStabilizer_of_transport
    (hTrans : L2ParabolicLeStabilizerTransport) :
    ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      L2ParabolicLeStabilizer W H n := by
  intro W _ _ H n hL2 hBin
  obtain ⟨K, hF, hFin, hK, e, hH'⟩ := exists_natural_image_of_binaryNaturalSL H n hBin
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
  exact (hTrans W (SL2Model.Wm K) H (statedSLNatImage K) n e hH'.symm
    (l2ParabolicLeStabilizer_statedSL K n hK)) hL2 hBin

end CFSG.LocalAnalysis.UniquenessCase.UC22
