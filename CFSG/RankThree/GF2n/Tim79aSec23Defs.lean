module

public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Tim79aSec2Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def preimOf (V H : Subgroup G) (S : Subgroup (Hbar V H)) : Subgroup G :=
  (S.comap (piBar V H)).map H.subtype

theorem mem_preimOf {V H : Subgroup G} {S : Subgroup (Hbar V H)} {g : G} :
    g ∈ preimOf V H S ↔ ∃ h : ↥H, (h : G) = g ∧ piBar V H h ∈ S := by
  simp [preimOf, Subgroup.mem_map, Subgroup.mem_comap]

theorem preimOf_le_H (V H : Subgroup G) (S : Subgroup (Hbar V H)) : preimOf V H S ≤ H := by
  rintro g hg
  obtain ⟨h, rfl, -⟩ := mem_preimOf.mp hg
  exact h.2

theorem wOf_le_preimOf (V H : Subgroup G) (S : Subgroup (Hbar V H)) :
    wOf V H ≤ preimOf V H S := by
  intro w hw
  refine mem_preimOf.mpr ⟨⟨w, wOf_le_H V H hw⟩, rfl, ?_⟩
  rw [(piBar_eq_one_iff _).2 hw]
  exact S.one_mem

theorem barOf_preimOf (V H : Subgroup G) (S : Subgroup (Hbar V H)) :
    barOf V H (preimOf V H S) = S := by
  ext y
  rw [mem_barOf_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨h, hh, hS⟩ := mem_preimOf.mp hx
    have : h = x := Subtype.ext hh
    rw [← this]; exact hS
  · intro hy
    obtain ⟨x, rfl⟩ := piBar_surjective V H y
    exact ⟨x, mem_preimOf.mpr ⟨x, rfl, hy⟩, rfl⟩

theorem normal_barOf_xOf (V H : Subgroup G) : (barOf V H (xOf V H)).Normal := by
  refine ⟨fun y hy h => ?_⟩
  obtain ⟨y', hy', rfl⟩ := mem_barOf_iff.mp hy
  obtain ⟨h', rfl⟩ := piBar_surjective V H h
  refine mem_barOf_iff.mpr ⟨h' * y' * h'⁻¹, ?_, by simp⟩
  have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H h'.2) (y' : G)).mp hy'
  simpa using this

theorem preimOf_le_xOf {V H : Subgroup G} {S : Subgroup (Hbar V H)}
    (hSX : S ≤ barOf V H (xOf V H)) :
    preimOf V H S ≤ xOf V H := by
  intro g hg
  obtain ⟨h, rfl, hS⟩ := mem_preimOf.mp hg
  obtain ⟨x, hx, hxh⟩ := mem_barOf_iff.mp (hSX hS)
  have h1 : piBar V H (x⁻¹ * h) = 1 := by rw [map_mul, map_inv, hxh]; simp
  have h2 : ((x⁻¹ * h : ↥H) : G) ∈ wOf V H := (piBar_eq_one_iff _).1 h1
  have h3 : (h : G) = (x : G) * ((x⁻¹ * h : ↥H) : G) := by simp
  rw [h3]
  exact (xOf V H).mul_mem hx (wOf_le_xOf V H h2)

theorem normalizer_preimOf {V H : Subgroup G} {S : Subgroup (Hbar V H)} [S.Normal] :
    H ≤ Subgroup.normalizer (preimOf V H S : Set G) := by
  intro h' hh'
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ k ∈ H, ∀ g ∈ preimOf V H S, k * g * k⁻¹ ∈ preimOf V H S := by
    intro k hk g hg
    obtain ⟨x, rfl, hS⟩ := mem_preimOf.mp hg
    refine mem_preimOf.mpr ⟨⟨k, hk⟩ * x * ⟨k, hk⟩⁻¹, by simp, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.Normal.conj_mem ‹S.Normal› _ hS _
  intro g
  refine ⟨fun hg => key h' hh' g hg, fun hg => ?_⟩
  have := key h'⁻¹ (H.inv_mem hh') _ hg
  simpa [mul_assoc] using this

section OddCore

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  rw [oddCore_eq_pPrimeCore_two]
  have := CFSG.pPrimeCore_coprime_card (p := 2) (G := X)
  simpa [Nat.coprime_two_left] using this

instance oddCore_characteristic (X : Type*) [Group X] : (CFSG.oddCore X).Characteristic := by
  rw [oddCore_eq_pPrimeCore_two]
  infer_instance

theorem normal_map_subtype_of_characteristic {Γ : Type*} [Group Γ] {K : Subgroup Γ} [K.Normal]
    (C : Subgroup K) [C.Characteristic] : (C.map K.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hn
  have h := (inferInstance : C.Characteristic).fixed (MulAut.conjNormal g)
  have hc' : MulAut.conjNormal g c ∈ C := by
    have : c ∈ C.comap (MulAut.conjNormal g : K ≃* K).toMonoidHom := by rw [h]; exact hc
    exact this
  exact ⟨_, hc', by simp [MulAut.conjNormal_apply]⟩

end OddCore

theorem V_mem_omegaOf (V H : Subgroup G) : V ∈ omegaOf V H :=
  ⟨1, H.one_mem, (conjSubgroup_one V).symm⟩

theorem barOf_V_le (V H : Subgroup G) : barOf V H V ≤ barOf V H (xOf V H) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_barOf_iff.mp hy
  exact mem_barOf_iff.mpr ⟨x, le_xOf (V_mem_omegaOf V H) hx, rfl⟩

theorem barOf_mono {V H S T : Subgroup G} (h : S ≤ T) : barOf V H S ≤ barOf V H T :=
  Subgroup.map_mono (Subgroup.comap_mono h)

abbrev Xbar (V H : Subgroup G) : Type := ↥(barOf V H (xOf V H))

@[expose] def oddCoreX (V H : Subgroup G) : Subgroup (Hbar V H) :=
  (CFSG.oddCore (Xbar V H)).map (barOf V H (xOf V H)).subtype

theorem isPGroup_preimOf {V H : Subgroup G} {S : Subgroup (Hbar V H)}
    (hS : ∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) (hW : IsPGroup 2 (wOf V H)) :
    IsPGroup 2 (preimOf V H S) := by
  intro g
  obtain ⟨h, hg, hhS⟩ := mem_preimOf.mp g.2
  obtain ⟨k, hk⟩ := hS _ hhS
  have h1 : h ^ 2 ^ k ∈ (piBar V H).ker := by
    rw [MonoidHom.mem_ker, map_pow, hk]
  have h2 : ((h ^ 2 ^ k : ↥H) : G) ∈ wOf V H := (piBar_eq_one_iff _).1 h1
  obtain ⟨j, hj⟩ := hW ⟨_, h2⟩
  refine ⟨k + j, ?_⟩
  apply Subtype.ext
  have hj' := congrArg Subtype.val hj
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at hj'
  have hgh : (g : G) = (h : G) := hg.symm
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [hgh, pow_add, pow_mul]
  exact hj'

theorem normal_oddCoreX (V H : Subgroup G) : (oddCoreX V H).Normal := by
  haveI := normal_barOf_xOf V H
  exact normal_map_subtype_of_characteristic (CFSG.oddCore (Xbar V H))

theorem oddCoreX_le (V H : Subgroup G) : oddCoreX V H ≤ barOf V H (xOf V H) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem odd_card_oddCoreX [Finite G] (V H : Subgroup G) : Odd (Nat.card (oddCoreX V H)) := by
  have h := odd_card_oddCore (Xbar V H)
  have e := Nat.card_congr ((CFSG.oddCore (Xbar V H)).equivMapOfInjective
    (barOf V H (xOf V H)).subtype (barOf V H (xOf V H)).subtype_injective).toEquiv
  rw [oddCoreX, ← e]
  exact h

theorem oddCoreX_central_iff (V H : Subgroup G) :
    (∀ s ∈ oddCoreX V H, ∀ y ∈ barOf V H (xOf V H), s * y = y * s) ↔
      CFSG.oddCore (Xbar V H) ≤ Subgroup.center (Xbar V H) := by
  constructor
  · intro h s hs
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h s.1 ⟨s, hs, rfl⟩ g.1 g.2).symm
  · intro h s hs y hy
    obtain ⟨s', hs', rfl⟩ := hs
    have := Subgroup.mem_center_iff.mp (h hs') ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm

@[expose] def Dy (V H : Subgroup G) : Set (Xbar V H) := {y | (y : Hbar V H) ∈ dbarOf V H}

@[expose] def Vy (V H : Subgroup G) : Subgroup (Xbar V H) :=
  (barOf V H V).subgroupOf (barOf V H (xOf V H))

theorem solvable_normal_le_center {Y : Type} [Group Y] [Finite Y]
    (hF : CFSG.fittingSubgroup Y ≤ Subgroup.center Y)
    {N : Subgroup Y} [N.Normal] (hsol : Group.IsSolvable N) : N ≤ Subgroup.center Y := by
  have hFn : ((CFSG.fittingSubgroup N).map N.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hn
    have h := CFSG.WholeGroup.fittingSubgroup_map_mulEquiv (MulAut.conjNormal g : N ≃* N)
    have h2 : MulAut.conjNormal g c ∈ CFSG.fittingSubgroup N := by
      rw [← h]; exact ⟨c, hc, rfl⟩
    exact ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩
  have hFnil : Group.IsNilpotent ↥((CFSG.fittingSubgroup N).map N.subtype) :=
    (Group.isNilpotent_congr ((CFSG.fittingSubgroup N).equivMapOfInjective N.subtype
      N.subtype_injective)).mp inferInstance
  have hle : (CFSG.fittingSubgroup N).map N.subtype ≤ CFSG.fittingSubgroup Y :=
    le_sSup ⟨hFn, hFnil⟩
  intro x hx
  have hx' : (⟨x, hx⟩ : N) ∈ Subgroup.centralizer (CFSG.fittingSubgroup N : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have : (f : Y) ∈ Subgroup.center Y := hF (hle ⟨f, hf, rfl⟩)
    exact Subtype.ext (Subgroup.mem_center_iff.mp this x).symm
  have := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsol hx'
  exact hF (hle ⟨_, this, rfl⟩)

structure Sec23Data (V H : Subgroup G) : Prop where
  isClass : ∃ d₀ : Xbar V H, Dy V H = {g | IsConj d₀ g}
  root : CFSG.Timmesfeld.IsRootInvolutionSet (Dy V H)
  gen : Subgroup.closure (Dy V H) = ⊤
  solv : ∀ N : Subgroup (Xbar V H), N.Normal → Group.IsSolvable N →
    N ≤ Subgroup.center (Xbar V H)
  noncentral : ∀ d ∈ Dy V H, d ∉ Subgroup.center (Xbar V H)

end CFSG.RankThree.GF2n.Tim79a
