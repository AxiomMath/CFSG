module

public import CFSG.Quasithin.Recognition.Stroth.U54VertexFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNst
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3M
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.U5Par

open Matrix Subgroup CFSG.Open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.Stroth

variable {f : ℕ} {K : Type} [Field K]

theorem perfectCore_u5PtP_eq_map (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    perfectCore (u5PtP h) = (N₂sub h ⊔ A₂sub h).map (hypProj h 2 1) := by
  haveI := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [u5PtP, projIsoStabilizer, ← map_perfectCore, perfectCore_u5PtStab h hf,
    sup_comm (A₂sub h) (N₂sub h)]

private theorem n2_le_normalizer_a2 (h : UnitaryFieldData 2 f K) :
    N₂sub h ≤ Subgroup.normalizer (A₂sub h : Set (hypSU h 2 1)) :=
  le_sup_left.trans (N₂sub_sup_Isub_le_normalizer_A₂sub (h := h))

private theorem a2_inf_n2 (h : UnitaryFieldData 2 f K) : A₂sub h ⊓ N₂sub h = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgA, hgN⟩ := Subgroup.mem_inf.1 hg
  have hgU : g ∈ hypUnitriangular h 2 1 := A₂sub_le_U hgA
  obtain ⟨-, hcol2⟩ := (mem_N₂sub (h := h)).1 hgN
  obtain ⟨-, a1, a2, a3⟩ := mem_A₂sub.1 hgA
  obtain ⟨r1, r2, r3⟩ := A₂_rel hgA
  have e12 : mat g ιe₁ ιe₂ = 0 := by
    apply h.bar.injective
    have hb : h.bar (mat g ιe₁ ιe₂) = 0 := by
      rw [← r1]
      exact (hcol2 _).trans (one_apply_ne (by decide))
    simpa using hb
  have e1z : mat g ιe₁ ιz = 0 := by
    apply h.bar.injective
    have hb : h.bar (mat g ιe₁ ιz) = 0 := by
      rw [← r2]
      exact (hcol2 _).trans (one_apply_ne (by decide))
    simpa using hb
  have e1f2 : mat g ιe₁ ιf₂ = 0 := by
    apply h.bar.injective
    have hb : h.bar (mat g ιe₁ ιf₂) = 0 := by
      rw [← r3]
      exact (hcol2 _).trans (one_apply_ne (by decide))
    simpa using hb
  refine eq_one_of_U_entries (h := h) hgU e12 e1z e1f2
    ((hcol2 _).trans (one_apply_ne (by decide))) a1 a3
    ((hcol2 _).trans (one_apply_ne (by decide))) a2
    ((hcol2 _).trans (one_apply_ne (by decide)))
    ((hcol2 _).trans (one_apply_ne (by decide)))

private theorem exists_quot_hom (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    ∃ q : ↥(N₂sub h ⊔ A₂sub h) →* ↥(N₂sub h), Function.Surjective q ∧
      q.ker = CFSG.pCore 2 ↥(N₂sub h ⊔ A₂sub h) := by
  have hNA : N₂sub h ≤ Subgroup.normalizer (A₂sub h : Set (hypSU h 2 1)) :=
    n2_le_normalizer_a2 h
  have hAN' : (A₂sub h).subgroupOf (N₂sub h) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : hypSU h 2 1) ∈ A₂sub h ⊓ N₂sub h := ⟨hx, x.2⟩
    rw [a2_inf_n2 h] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hNA' : (N₂sub h ⊔ A₂sub h) ≤
      Subgroup.normalizer (A₂sub h : Set (hypSU h 2 1)) :=
    sup_le hNA (Subgroup.le_normalizer)
  haveI hAN_normal : ((A₂sub h).subgroupOf (N₂sub h)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNA
  haveI hAN_normal2 : ((A₂sub h).subgroupOf (N₂sub h ⊔ A₂sub h)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNA'
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (N₂sub h) (A₂sub h) hNA
  let eN : (↥(N₂sub h ⊔ A₂sub h) ⧸ (A₂sub h).subgroupOf (N₂sub h ⊔ A₂sub h)) ≃*
      ↥(N₂sub h) :=
    (e.symm.trans (QuotientGroup.quotientMulEquivOfEq hAN')).trans QuotientGroup.quotientBot
  let q : ↥(N₂sub h ⊔ A₂sub h) →* ↥(N₂sub h) :=
    eN.toMonoidHom.comp (QuotientGroup.mk' ((A₂sub h).subgroupOf (N₂sub h ⊔ A₂sub h)))
  have hq : Function.Surjective q := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = (A₂sub h).subgroupOf (N₂sub h ⊔ A₂sub h) := by
    ext x
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' ((A₂sub h).subgroupOf (N₂sub h ⊔ A₂sub h)) x = 1 := by
        apply eN.injective
        simpa [q] using hx
      exact (QuotientGroup.eq_one_iff x).mp (by simpa using h1)
    · intro hx
      rw [MonoidHom.mem_ker]
      have h1 : QuotientGroup.mk' ((A₂sub h).subgroupOf (N₂sub h ⊔ A₂sub h)) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      simp only [q, MonoidHom.comp_apply, h1, map_one]
  refine ⟨q, hq, ?_⟩
  rw [hqker, ← CFSG.openPCoreOf_subgroupOf 2 (N₂sub h ⊔ A₂sub h),
    pCoreOf_a2sub_sup_n2sub h hf]

private theorem injOn_subgroupMap (h : UnitaryFieldData 2 f K) :
    Function.Injective ⇑((hypProj h 2 1).subgroupMap (N₂sub h ⊔ A₂sub h)) := by
  intro x y hxy
  have hxy' : hypProj h 2 1 (x : hypSU h 2 1) = hypProj h 2 1 (y : hypSU h 2 1) :=
    congrArg Subtype.val hxy
  have hx' : x.1 ∈ A₂sub h ⊔ N₂sub h := by
    rw [sup_comm (A₂sub h) (N₂sub h)]
    exact x.2
  have hy' : y.1 ∈ A₂sub h ⊔ N₂sub h := by
    rw [sup_comm (A₂sub h) (N₂sub h)]
    exact y.2
  have h' : hypProj h 2 1 (⟨x.1, hx'⟩ : ↥(A₂sub h ⊔ N₂sub h)) =
      hypProj h 2 1 (⟨y.1, hy'⟩ : ↥(A₂sub h ⊔ N₂sub h)) := hxy'
  have h2 := injOn_hypProj_a2sub_sup_n2sub (h := h) h'
  exact Subtype.ext
    (congrArg (fun t : ↥(A₂sub h ⊔ N₂sub h) => (t : ↥(hypSU h 2 1))) h2)

private noncomputable def piEquiv (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    ↥(N₂sub h ⊔ A₂sub h) ≃* ↥(perfectCore (u5PtP h)) := by
  rw [perfectCore_u5PtP_eq_map h hf]
  exact MulEquiv.ofBijective ((hypProj h 2 1).subgroupMap (N₂sub h ⊔ A₂sub h))
    ⟨injOn_subgroupMap h, (hypProj h 2 1).subgroupMap_surjective _⟩

theorem nonempty_modO2_perfectCore_u5PtP_equiv (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    Nonempty (CFSG.Quasithin.ModO2 (perfectCore (u5PtP h)) ≃* ↥(N₂sub h)) := by
  obtain ⟨q, hq, hqker⟩ := exists_quot_hom h hf
  let e := piEquiv h hf
  let α : ↥(perfectCore (u5PtP h)) →* ↥(N₂sub h) := q.comp e.symm.toMonoidHom
  have hα : Function.Surjective α := hq.comp e.symm.surjective
  have hαker : α.ker = CFSG.pCore 2 ↥(perfectCore (u5PtP h)) := by
    rw [← CFSG.pCore_map_iso 2 e, ← hqker]
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : q y = 1 := hy
      show q (e.symm (e y)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact hy'
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hαker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

theorem centerOf_pCoreOf_perfectCore_u5PtP (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    centerOf (CFSG.Open.pCoreOf 2 (perfectCore (u5PtP h))) = (ZPsub h).map (hypProj h 2 1) := by
  haveI := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [pCoreOf_perfectCore_u5PtP h hf, CFSG.Quasithin.centerOf]
  apply le_antisymm
  · rintro x ⟨hxA, hxC⟩
    obtain ⟨a, haA, rfl⟩ := hxA
    have haZ : a ∈ ZPsub h := by
      rw [← centerIn_A₂sub (h := h)]
      refine ⟨haA, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      exact CFSG.Quasithin.H13.F431.Un.hypProj_eq_of_mem_U (A₂sub_le_U (mul_mem hb haA))
        (A₂sub_le_U (mul_mem haA hb))
        (by
          rw [map_mul, map_mul]
          exact Subgroup.mem_centralizer_iff.mp hxC (hypProj h 2 1 b)
            (Subgroup.mem_map_of_mem _ hb))
    exact Subgroup.mem_map_of_mem _ haZ
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hzA : z ∈ A₂sub h := Z₂Psub_le_A₂sub (ZPsub_le_Z₂Psub hz)
    have hzc : hypProj h 2 1 z ∈ centerOf (perfectCore (u5PtP h)) := by
      rw [CFSG.Quasithin.H13.F431.Un.OL5.centerOf_perfectCore_u5PtP h hf]
      exact Subgroup.mem_map_of_mem _ hz
    have hAle : (A₂sub h).map (hypProj h 2 1) ≤ perfectCore (u5PtP h) := by
      rw [perfectCore_u5PtP_eq_map h hf]
      exact Subgroup.map_mono le_sup_right
    have hcent : hypProj h 2 1 z ∈
        Subgroup.centralizer ((A₂sub h).map (hypProj h 2 1) : Set (hypPSU h 2 1)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact Subgroup.mem_centralizer_iff.mp hzc.2 (hypProj h 2 1 b)
        (hAle (Subgroup.mem_map_of_mem _ hb))
    exact ⟨Subgroup.mem_map_of_mem _ hzA, hcent⟩

theorem perfectCore_u5PtP_le_centralizer (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    perfectCore (u5PtP h) ≤ Subgroup.centralizer
      (centerOf (CFSG.Open.pCoreOf 2 (perfectCore (u5PtP h))) : Set (hypPSU h 2 1)) := by
  rw [centerOf_pCoreOf_perfectCore_u5PtP h hf,
    ← CFSG.Quasithin.H13.F431.Un.OL5.centerOf_perfectCore_u5PtP h hf]
  refine Subgroup.le_centralizer_iff.mpr ?_
  rw [CFSG.Quasithin.centerOf]
  exact inf_le_right

theorem isSimpleGroup_modO2_perfectCore_u5PtP {K : Type} [Field K]
    (h : UnitaryFieldData 2 2 K) :
    IsSimpleGroup (CFSG.Quasithin.ModO2 (perfectCore (u5PtP h))) := by
  haveI := h.finite
  haveI : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hmq : (2 * 1 + 1, 2 ^ 2) ≠ (3, 2) := by norm_num
  obtain ⟨hq, -⟩ := CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le (s := 1) (ε := 1) h
    (by norm_num) hmq
  have hcard : Nat.card ↥(hypScalars h 1 1) = 1 := by
    rw [card_hypScalars h (r := 1) (ε := 1) (by norm_num)]
    norm_num
  have hbot : hypScalars h 1 1 = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  have hZ : Subgroup.center ↥(hypSU h 1 1) = ⊥ := by
    rw [← CFSG.Quasithin.H13.P31X.u3_hypScalars_eq_center h (by norm_num)]
    exact hbot
  have hsimple : IsSimpleGroup ↥(hypSU h 1 1) :=
    (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)).mp hq.2
  haveI : IsSimpleGroup ↥(N₂sub h) := (MulEquiv.isSimpleGroup_congr (N₂equiv h)).mp hsimple
  obtain ⟨e⟩ := nonempty_modO2_perfectCore_u5PtP_equiv h (by norm_num)
  exact e.isSimpleGroup

end CFSG.Quasithin.H13.U5Par

end
