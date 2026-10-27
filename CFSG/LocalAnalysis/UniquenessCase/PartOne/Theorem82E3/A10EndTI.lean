module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKey
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c
import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private noncomputable def phiL (F : A10Frame c) : ↥c.L →* alternatingGroup (Fin 10) :=
  (F.phiA.comp (Subgroup.inclusion c.hyp81.1)).codRestrict (alternatingGroup (Fin 10))
    fun x => by
      have hx : F.phiA (Subgroup.inclusion c.hyp81.1 x) ∈ (c.L.subgroupOf D.M).map F.phiA :=
        Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr x.2)
      rwa [F.map_L_phiA] at hx

private theorem phiL_surjective (F : A10Frame c) : Function.Surjective F.phiL := by
  intro y
  have hy : (y : Equiv.Perm (Fin 10)) ∈ (c.L.subgroupOf D.M).map F.phiA := by
    rw [F.map_L_phiA]
    exact y.2
  obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩, Subtype.ext ?_⟩
  have hinc : Subgroup.inclusion c.hyp81.1
      (⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩ : ↥c.L) = m := Subtype.ext rfl
  change F.phiA (Subgroup.inclusion c.hyp81.1
    (⟨(m : G), Subgroup.mem_subgroupOf.mp hm⟩ : ↥c.L)) = (y : Equiv.Perm (Fin 10))
  rw [hinc]
  exact hmy

private theorem normal_subgroupOf_inf_centralizer (F : A10Frame c) {V : Subgroup G}
    (hMV : D.M ≤ Subgroup.normalizer (V : Set G)) :
    ((c.L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf c.L).Normal := by
  let N : Subgroup G := c.L ⊓ Subgroup.centralizer (V : Set G)
  have hNL : N ≤ c.L := inf_le_left
  have hLnC : c.L ≤ Subgroup.normalizer ((Subgroup.centralizer (V : Set G)) : Set G) := by
    have h := (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (V : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (V : Set G))
    exact (c.hyp81.1.trans hMV).trans h
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNL]
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨c.L.mul_mem (c.L.mul_mem hl hx.1) (c.L.inv_mem hl),
      (Subgroup.mem_normalizer_iff.mp (hLnC hl) x).mp hx.2⟩
  · intro hx
    have hxL : x ∈ c.L := by
      have h := c.L.mul_mem (c.L.mul_mem (c.L.inv_mem hl) hx.1) hl
      rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h
    refine ⟨hxL, ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hLnC (Subgroup.inv_mem _ hl))
      (l * x * l⁻¹)).mp hx.2
    rwa [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group] at h

private theorem map_subgroupOf_inf_centralizer_eq_top (F : A10Frame c) {V : Subgroup G}
    (hMV : D.M ≤ Subgroup.normalizer (V : Set G))
    (hAV : F.A ≤ Subgroup.centralizer (V : Set G)) :
    ((c.L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf c.L).map F.phiL = ⊤ := by
  classical
  let N : Subgroup G := c.L ⊓ Subgroup.centralizer (V : Set G)
  let H : Subgroup (alternatingGroup (Fin 10)) := (N.subgroupOf c.L).map F.phiL
  have hHnormal : H.Normal :=
    (normal_subgroupOf_inf_centralizer F hMV).map F.phiL F.phiL_surjective
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (by
    intro hbot
    have hcard := congrArg (fun K : Subgroup G => Nat.card K) hbot
    rw [F.card_A] at hcard
    simp at hcard)
  have haA : (a : G) ∈ F.A := a.2
  have haL : (a : G) ∈ c.L := F.P_le_L (F.A_le haA)
  have hfne : F.phiL ⟨(a : G), haL⟩ ≠ 1 := by
    intro h1
    have h1' : F.phiA ⟨(a : G), c.hyp81.1 haL⟩ = 1 := by
      have hval := congrArg (fun z : alternatingGroup (Fin 10) => (z : Equiv.Perm (Fin 10))) h1
      have hval' : F.phiA (Subgroup.inclusion c.hyp81.1 ⟨(a : G), haL⟩) = 1 := by
        simpa [phiL] using hval
      rw [show Subgroup.inclusion c.hyp81.1 ⟨(a : G), haL⟩ =
        (⟨(a : G), c.hyp81.1 haL⟩ : ↥D.M) from Subtype.ext rfl] at hval'
      exact hval'
    have haO : (a : G) ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype :=
      (F.phiA_eq_one_iff haL).mp h1'
    have h2 : IsPGroup 2 (Subgroup.zpowers (a : G)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L).to_le
        (Subgroup.zpowers_le.mpr haO)
    have h3 : 3 ∣ Nat.card (Subgroup.zpowers (a : G)) := by
      rw [F.card_zpowers_of_mem_A haA (fun h => ha1 (Subtype.ext h))]
    exact (CFSG.GroupTheory.not_dvd_card_of_isPGroup (p := 2) (q := 3) h2 Nat.prime_three
      (by norm_num)) h3
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hmem : F.phiL ⟨(a : G), haL⟩ ∈ H :=
      Subgroup.mem_map.mpr
        ⟨⟨(a : G), haL⟩, Subgroup.mem_subgroupOf.mpr ⟨haL, hAV haA⟩, rfl⟩
    rw [hbot] at hmem
    exact hfne (by simpa using hmem)
  haveI : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact absurd h hHne
  · exact h

private theorem le_sup_of_map_subgroupOf_inf_centralizer_eq_top (F : A10Frame c) {V : Subgroup G}
    (hHtop : ((c.L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf c.L).map F.phiL = ⊤) :
    c.L ≤ (c.L ⊓ Subgroup.centralizer (V : Set G)) ⊔ CFSG.Open.pCoreOf 2 c.L := by
  intro x hx
  let N : Subgroup G := c.L ⊓ Subgroup.centralizer (V : Set G)
  let O : Subgroup G := CFSG.Open.pCoreOf 2 c.L
  have hxH : F.phiL ⟨x, hx⟩ ∈ (N.subgroupOf c.L).map F.phiL := by
    rw [show (N.subgroupOf c.L).map F.phiL = ⊤ from hHtop]
    exact Subgroup.mem_top _
  obtain ⟨n, hnNl, hfn⟩ := Subgroup.mem_map.mp hxH
  have hnN : ((n : c.L) : G) ∈ N := Subgroup.mem_subgroupOf.mp hnNl
  have hnL : ((n : c.L) : G) ∈ c.L := (n : c.L).2
  have hfn' : F.phiA ⟨((n : c.L) : G), c.hyp81.1 hnL⟩ =
      F.phiA ⟨x, c.hyp81.1 hx⟩ := by
    have hval := congrArg (fun z : alternatingGroup (Fin 10) => (z : Equiv.Perm (Fin 10))) hfn
    have hval' : F.phiA (Subgroup.inclusion c.hyp81.1 n) =
        F.phiA (Subgroup.inclusion c.hyp81.1 ⟨x, hx⟩) := by
      simpa [phiL] using hval
    rw [show Subgroup.inclusion c.hyp81.1 n =
        (⟨((n : c.L) : G), c.hyp81.1 hnL⟩ : ↥D.M) from Subtype.ext rfl,
      show Subgroup.inclusion c.hyp81.1 ⟨x, hx⟩ =
        (⟨x, c.hyp81.1 hx⟩ : ↥D.M) from Subtype.ext rfl] at hval'
    exact hval'
  have hphi : F.phiA ⟨((n : c.L) : G)⁻¹ * (x : G),
      c.hyp81.1 (c.L.mul_mem (c.L.inv_mem hnL) hx)⟩ = 1 := by
    have h1 : (⟨((n : c.L) : G)⁻¹ * (x : G),
          c.hyp81.1 (c.L.mul_mem (c.L.inv_mem hnL) hx)⟩ : ↥D.M) =
        (⟨((n : c.L) : G), c.hyp81.1 hnL⟩ : ↥D.M)⁻¹ * ⟨x, c.hyp81.1 hx⟩ := by
      ext
      simp
    rw [h1, map_mul, map_inv, hfn', inv_mul_cancel]
  have hkerO : ((n : c.L) : G)⁻¹ * (x : G) ∈ O :=
    (F.phiA_eq_one_iff (c.L.mul_mem (c.L.inv_mem hnL) hx)).mp hphi
  have hxeq : (x : G) = ((n : c.L) : G) * (((n : c.L) : G)⁻¹ * (x : G)) := by group
  rw [hxeq]
  exact (N ⊔ O).mul_mem (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right hkerO)

private theorem le_centralizer_of_le_centralizer (F : A10Frame c) {V : Subgroup G}
    (hMV : D.M ≤ Subgroup.normalizer (V : Set G))
    (hAV : F.A ≤ Subgroup.centralizer (V : Set G)) :
    c.L ≤ Subgroup.centralizer (V : Set G) := by
  have hNnorm : ((c.L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf c.L).Normal :=
    normal_subgroupOf_inf_centralizer F hMV
  have hLO : c.L ≤ (c.L ⊓ Subgroup.centralizer (V : Set G)) ⊔ CFSG.Open.pCoreOf 2 c.L :=
    le_sup_of_map_subgroupOf_inf_centralizer_eq_top F
      (map_subgroupOf_inf_centralizer_eq_top F hMV hAV)
  have hLN : c.L ≤ c.L ⊓ Subgroup.centralizer (V : Set G) :=
    CFSG.LocalAnalysis.GLTheoremB.le_of_perfect_of_le_sup_pGroup (q := 2)
      c.hyp81.2.2.1 inf_le_left hNnorm (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L) hLO
  exact hLN.trans inf_le_right

private theorem normalizer_zpowers_le_M (F : A10Frame c) {V : Subgroup G}
    (hVab : CFSG.Open.IsElemAbelian 2 V)
    (hLV : c.L ≤ Subgroup.centralizer (V : Set G))
    {v : G} (hvV : v ∈ V) (hv1 : v ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers v : Set G) ≤ D.M := by
  classical
  have hord : orderOf v = 2 := orderOf_eq_prime (hVab.2 v hvV) hv1
  have hp2 : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hord])
  have hne : Subgroup.zpowers v ≠ ⊥ := fun h => hv1 (Subgroup.zpowers_eq_bot.mp h)
  have hH2 : CFSG.Open.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers v : Set G)) :=
    ⟨_, hne, hp2, rfl⟩
  have hLleH : c.L ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    have h1 : c.L ≤ Subgroup.centralizer ({v} : Set G) :=
      hLV.trans (Subgroup.centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        exact hx.symm ▸ hvV))
    refine h1.trans ?_
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  exact F.le_M_of_L_le hH2 hLleH

private theorem conjSubgroup_eq_of_inf_ne_bot (F : A10Frame c) {V : Subgroup G}
    (hMV : D.M ≤ Subgroup.normalizer (V : Set G))
    (hVab : CFSG.Open.IsElemAbelian 2 V)
    (hLV : c.L ≤ Subgroup.centralizer (V : Set G))
    {g v : G} (hv : v ∈ V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V) (hv1 : v ≠ 1) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g V = V := by
  classical
  have hvV : v ∈ V := hv.1
  have hvmem : g⁻¹ * v * g ∈ V :=
    (CFSG.CGT.Timmesfeld75.mem_conjSubgroup).mp hv.2
  have hHM : Subgroup.normalizer (Subgroup.zpowers v : Set G) ≤ D.M :=
    normalizer_zpowers_le_M F hVab hLV hvV hv1
  have hconjL : CFSG.CGT.Timmesfeld75.conjSubgroup g c.L ≤
      Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    have hcent : CFSG.CGT.Timmesfeld75.conjSubgroup g c.L ≤
        Subgroup.centralizer ({v} : Set G) := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hcomm : (g⁻¹ * v * g) * l = l * (g⁻¹ * v * g) :=
        Subgroup.mem_centralizer_iff.mp (hLV hl) (g⁻¹ * v * g) hvmem
      show v * MulAut.conj g l = MulAut.conj g l * v
      simp only [MulAut.conj_apply]
      calc v * (g * l * g⁻¹) = g * ((g⁻¹ * v * g) * l) * g⁻¹ := by group
        _ = g * (l * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * l * g⁻¹) * v := by group
    refine hcent.trans ?_
    rw [Subgroup.zpowers_eq_closure, ← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hLleM : c.L ≤ CFSG.Open.uniqueFourConj g D.M := by
    intro l hl
    have hgl : MulAut.conj g l ∈ D.M := hHM (hconjL (Subgroup.mem_map_of_mem _ hl))
    exact Subgroup.mem_map.mpr ⟨MulAut.conj g l, hgl, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hM2 : CFSG.Open.IsTwoLocal (CFSG.Open.uniqueFourConj g D.M) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.isTwoLocal_conj D.maxLocal.1 g
  have hle : CFSG.Open.uniqueFourConj g D.M ≤ D.M := F.le_M_of_L_le hM2 hLleM
  have heq : CFSG.Open.uniqueFourConj g D.M = D.M :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (CFSG.LocalAnalysis.UniquenessCase.UC6.card_uniqueFourConj D.M g).symm)
  have hg : g ∈ Subgroup.normalizer (D.M : Set G) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6.uniqueFourConj_eq_self_iff (H := D.M)).mp heq
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal] at hg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMV hg)

theorem not_le_centralizer_of_inCalVStar (F : A10Frame c) (h639 : PartTwo.R6_39 D)
    {V : Subgroup G} (hV : PartTwo.InCalVStar D.M V) :
    ¬ F.A ≤ Subgroup.centralizer (V : Set G) := by
  intro hAV
  have hMV : D.M ≤ Subgroup.normalizer (V : Set G) := hV.1.2.2.1
  have hLV : c.L ≤ Subgroup.centralizer (V : Set G) :=
    le_centralizer_of_le_centralizer F hMV hAV
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V := by
    intro g
    by_cases h : V ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g V = ⊥
    · exact Or.inl h
    · right
      obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
      have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V :=
        conjSubgroup_eq_of_inf_ne_bot F hMV hV.1.2.2.2 hLV v.2
          (fun h1 => hv1 (Subtype.ext h1))
      rw [hconj, inf_idem]
  exact h639 V hV hTI

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
