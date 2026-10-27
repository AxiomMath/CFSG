module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA4Sec
public import CFSG.GroupTheory.K462SLTwoQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S23_9_AdjData

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} {hV : IsElemAbelian 2 c.V}
  {d : S23_9_A0Data D Ch c} {b : G} {hb : b ∈ c.B0} {r : ℕ}

noncomputable abbrev qX2 (a : S23_9_AdjData D Ch c hV d b hb r) : ↥(X2 a) →* Bar2 a.X :=
  a.qX.comp (Subgroup.inclusion (X2_le_X a))

theorem qX2_surjective (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) : Function.Surjective (qX2 a) := by
  intro y
  have hy : y ∈ ((X2 a).subgroupOf a.X).map a.qX := by
    rw [map_qX_X2_eq_top a hbr hr3]
    exact Subgroup.mem_top y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, hxy⟩

theorem qX2_ker (a : S23_9_AdjData D Ch c hV d b hb r) :
    (qX2 a).ker = (CFSG.pCore 2 ↥a.X).comap (Subgroup.inclusion (X2_le_X a)) := by
  ext x
  simp [qX2, S23_9_AdjData.qX, QuotientGroup.ker_mk']

theorem isPGroup_ker_qX2 (a : S23_9_AdjData D Ch c hV d b hb r) :
    IsPGroup 2 (qX2 a).ker := by
  rw [qX2_ker]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥a.X)).comap_of_injective _
    (Subgroup.inclusion_injective (X2_le_X a))

@[expose] noncomputable def rhoW (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) :
    Representation (ZMod d.q) ↥(X2 a) ↥W :=
  (rhoX a).subrepresentation W (fun g w hw => hWinv g w hw)

theorem rhoW_apply (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (g : ↥(X2 a)) (w : ↥W) : ((rhoW a hWinv) g w : A0V d) = rhoX a g w.1 := by
  rw [rhoW, Representation.subrepresentation_apply]
  rfl

theorem rhoW_irreducible (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) (hWne : W ≠ ⊥)
    (hWmin : ∀ W' : Submodule (ZMod d.q) (A0V d), W' ≤ W →
      (∀ g : ↥(X2 a), ∀ w ∈ W', rhoX a g w ∈ W') → W' = ⊥ ∨ W' = W)
    [Fact d.q.Prime] :
    Representation.IsIrreducible (rhoW a hWinv) := by
  unfold Representation.IsIrreducible
  rw [isSimpleOrder_iff_isAtom_top, isAtom_iff_le_of_ge]
  refine ⟨?_, ?_⟩
  · haveI : Nontrivial ↥W := by
      rwa [Submodule.nontrivial_iff_ne_bot]
    exact top_ne_bot
  · intro τ hτne hτle
    have hmapne : τ.toSubmodule.map W.subtype ≠ ⊥ := by
      intro h
      apply hτne
      apply Subrepresentation.toSubmodule_injective
      have h' : τ.toSubmodule.map W.subtype =
          (⊥ : Submodule (ZMod d.q) ↥W).map W.subtype := by
        simpa using h
      have hbot : (⊥ : Subrepresentation (rhoW a hWinv)).toSubmodule = ⊥ := rfl
      rw [hbot]
      exact Submodule.map_injective_of_injective W.subtype_injective h'
    have hinv : ∀ g : ↥(X2 a), ∀ v ∈ τ.toSubmodule.map W.subtype,
        rhoX a g v ∈ τ.toSubmodule.map W.subtype := by
      intro g v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      change (rhoX a g) (w : A0V d) ∈ τ.toSubmodule.map W.subtype
      rw [← rhoW_apply a hWinv g w]
      exact Submodule.mem_map_of_mem (f := W.subtype) (τ.apply_mem_toSubmodule g hw)
    have hle : τ.toSubmodule.map W.subtype ≤ W := Submodule.map_subtype_le _ _
    rcases hWmin _ hle hinv with hbot | htop
    · exact absurd hbot hmapne
    · have hτtop : τ = ⊤ := by
        apply le_antisymm le_top
        intro w _
        have hw : (w : A0V d) ∈ τ.toSubmodule.map W.subtype := by
          rw [htop]
          exact w.2
        obtain ⟨u, hu, huw⟩ := Submodule.mem_map.mp hw
        exact (Subtype.ext huw) ▸ hu
      rw [hτtop]

abbrev Hq (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) : Type :=
  ↥(X2 a) ⧸ (rhoW a hWinv).ker

@[expose] noncomputable def rhoH (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) :
    Representation (ZMod d.q) (Hq a hWinv) ↥W :=
  Theory.Representation.kerRepresentation (rhoW a hWinv)

theorem rhoH_faithful (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) :
    Function.Injective (rhoH a hWinv) :=
  Theory.Representation.kerRepresentation_faithful _

theorem rhoH_irreducible (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    [Fact d.q.Prime] [Representation.IsIrreducible (rhoW a hWinv)] :
    Representation.IsIrreducible (rhoH a hWinv) :=
  Theory.Representation.kerRepresentation_irreducible (rhoW a hWinv)

theorem rhoH_mk (a : S23_9_AdjData D Ch c hV d b hb r)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) (x : ↥(X2 a))
    [Fact d.q.Prime] :
    rhoH a hWinv (QuotientGroup.mk' (rhoW a hWinv).ker x) = rhoW a hWinv x := rfl

@[expose] noncomputable def Dsub (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) : Subgroup (Hq a hWinv) :=
  (Subgroup.zpowers (⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩ : ↥(X2 a))).map
    (QuotientGroup.mk' (rhoW a hWinv).ker)

theorem fixV_rhoH_Dsub_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (hWU : W ≤ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))) [Fact d.q.Prime] :
    CFSG.LocalAnalysis.UniquenessCase.UCK.fixV (rhoH a hWinv) (Dsub a hbr hr3 hWinv) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  let x : ↥(X2 a) := ⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩
  have hxmem : QuotientGroup.mk' (rhoW a hWinv).ker x ∈ Dsub a hbr hr3 hWinv :=
    Subgroup.mem_map_of_mem (f := QuotientGroup.mk' (rhoW a hWinv).ker)
      (Subgroup.mem_zpowers x)
  have hvfix : rhoH a hWinv (QuotientGroup.mk' (rhoW a hWinv).ker x) v = v := hv _ hxmem
  rw [rhoH_mk] at hvfix
  have hvval : rhoX a x v.1 = v.1 := congrArg Subtype.val hvfix
  rw [rhoX_apply] at hvval
  have hfixd : v.1 ∈ d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) := by
    rw [barImage_zpowers_eq a.dRoot_mem_DM]
    exact (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6 d.rep _ v.1).mpr
      (by simpa using hvval)
  have hmemc : v.1 ∈ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) := hWU v.2
  have hbot := a.fixV_ctilde_inf_fixV_dRoot_eq_bot hfixb
  have hmem : v.1 ∈ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) ⊓
      d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) := ⟨hmemc, hfixd⟩
  rw [hbot] at hmem
  exact Subtype.ext (by simpa using hmem)

theorem map_ker_rhoW_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (hWU : W ≤ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))) (hWne : W ≠ ⊥) :
    (rhoW a hWinv).ker.map (qX2 a) = ⊥ := by
  by_contra hne
  haveI : IsSimpleGroup (Bar2 a.X) := CFSG.GroupTheory.isSimpleGroup_of_isSLn_two a.hm2 a.hXsl
  have hq2surj : Function.Surjective (qX2 a) := qX2_surjective a hbr hr3
  haveI : ((rhoW a hWinv).ker.map (qX2 a)).Normal :=
    (MonoidHom.normal_ker (rhoW a hWinv)).map (qX2 a) hq2surj
  have htop : (rhoW a hWinv).ker.map (qX2 a) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((rhoW a hWinv).ker.map (qX2 a)) with h | h
    · exact absurd h hne
    · exact h
  have hsup : (⊤ : Subgroup ↥(X2 a)) ≤ (rhoW a hWinv).ker ⊔ (qX2 a).ker := by
    intro y _
    have hy : (qX2 a) y ∈ (rhoW a hWinv).ker.map (qX2 a) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hqm⟩ := Subgroup.mem_map.mp hy
    have hk : m⁻¹ * y ∈ (qX2 a).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqm, inv_mul_cancel]
    rw [show y = m * (m⁻¹ * y) by group]
    exact Subgroup.mul_mem_sup (G := ↥(X2 a)) (S := (rhoW a hWinv).ker)
      (T := (qX2 a).ker) hm hk
  have hP : IsPGroup 2 (qX2 a).ker := isPGroup_ker_qX2 a
  have hperf : ⁅(⊤ : Subgroup ↥(X2 a)), (⊤ : Subgroup ↥(X2 a))⁆ = ⊤ := by
    haveI : Group.IsPerfect ↥(X2 a) := Subgroup.isPerfect_iff.mpr (X2_perfect a)
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hle : (⊤ : Subgroup ↥(X2 a)) ≤ (rhoW a hWinv).ker :=
    CFSG.GroupTheory.le_of_commutator_eq_self_of_le_sup_of_isPGroup
      (K := ⊤) (N := (rhoW a hWinv).ker) (P := (qX2 a).ker) hP hperf hsup
  obtain ⟨x, w, hw, hne'⟩ := a.exists_X2_act_ne hbr hr3 hfixb hWU hWne
  have hxmem : x ∈ (rhoW a hWinv).ker := hle (Subgroup.mem_top x)
  have h1 : rhoW a hWinv x = 1 := MonoidHom.mem_ker.mp hxmem
  have h2 : ((rhoW a hWinv) x ⟨w, hw⟩ : A0V d) = w := by
    rw [h1]
    rfl
  exact hne' ((rhoW_apply a hWinv x ⟨w, hw⟩).trans h2)

theorem ker_rhoW_le_ker_qX2 (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (hWU : W ≤ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))) (hWne : W ≠ ⊥) :
    (rhoW a hWinv).ker ≤ (qX2 a).ker := by
  have hmap := map_ker_rhoW_eq_bot a hbr hr3 hfixb hWinv hWU hWne
  intro n hn
  rw [MonoidHom.mem_ker]
  have hmem : (qX2 a) n ∈ (rhoW a hWinv).ker.map (qX2 a) :=
    Subgroup.mem_map_of_mem (f := qX2 a) hn
  rw [hmap] at hmem
  simpa using hmem

theorem not_three_dvd_ker_rhoW (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (hWU : W ≤ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))) (hWne : W ≠ ⊥) :
    ¬ 3 ∣ Nat.card (rhoW a hWinv).ker := by
  have hle := ker_rhoW_le_ker_qX2 a hbr hr3 hfixb hWinv hWU hWne
  have hdvd : Nat.card (rhoW a hWinv).ker ∣ Nat.card (qX2 a).ker :=
    Subgroup.card_dvd_of_le hle
  have h3 : ¬ 3 ∣ Nat.card (qX2 a).ker := by
    obtain ⟨k, hk⟩ := (isPGroup_ker_qX2 a).exists_card_eq
    rw [hk]
    intro h
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    omega
  exact fun h => h3 (h.trans hdvd)

theorem normalClosure_zpowers_dRoot_eq_top (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) :
    Subgroup.normalClosure
      (Subgroup.zpowers (⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩ : ↥(X2 a)) : Set ↥(X2 a)) = ⊤ := by
  let x : ↥(X2 a) := ⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩
  let M : Subgroup ↥(X2 a) := Subgroup.normalClosure (Subgroup.zpowers x : Set ↥(X2 a))
  have hq2surj : Function.Surjective (qX2 a) := qX2_surjective a hbr hr3
  haveI : IsSimpleGroup (Bar2 a.X) := CFSG.GroupTheory.isSimpleGroup_of_isSLn_two a.hm2 a.hXsl
  have hMnormal : M.Normal := Subgroup.normalClosure_normal
  haveI : (M.map (qX2 a)).Normal := hMnormal.map (qX2 a) hq2surj
  have hq2x : (qX2 a) x = a.dhat := rfl
  have hq2x_ne : (qX2 a) x ≠ 1 := by
    have hord : orderOf ((qX2 a) x) = 3 := by
      rw [hq2x, a.orderOf_dhat (hr3 ▸ Nat.prime_three)
        (hr3 ▸ (by norm_num : (3 : ℕ) ≠ 2)), hr3]
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hnt : M.map (qX2 a) ≠ ⊥ := by
    intro h
    have hmem : (qX2 a) x ∈ (⊥ : Subgroup (Bar2 a.X)) := by
      rw [← h]
      exact Subgroup.mem_map_of_mem (f := qX2 a)
        (Subgroup.le_normalClosure (Subgroup.mem_zpowers x))
    exact hq2x_ne (Subgroup.mem_bot.mp hmem)
  have htop : M.map (qX2 a) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (qX2 a)) with h | h
    · exact absurd h hnt
    · exact h
  have hsup : (⊤ : Subgroup ↥(X2 a)) ≤ M ⊔ (qX2 a).ker := by
    intro y _
    have hy : (qX2 a) y ∈ M.map (qX2 a) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hqm⟩ := Subgroup.mem_map.mp hy
    have hk : m⁻¹ * y ∈ (qX2 a).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqm, inv_mul_cancel]
    rw [show y = m * (m⁻¹ * y) by group]
    exact Subgroup.mul_mem_sup (G := ↥(X2 a)) (S := M)
      (T := (qX2 a).ker) hm hk
  have hP : IsPGroup 2 (qX2 a).ker := isPGroup_ker_qX2 a
  have hperf : ⁅(⊤ : Subgroup ↥(X2 a)), (⊤ : Subgroup ↥(X2 a))⁆ = ⊤ := by
    haveI : Group.IsPerfect ↥(X2 a) := Subgroup.isPerfect_iff.mpr (X2_perfect a)
    rw [← _root_.commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hle : (⊤ : Subgroup ↥(X2 a)) ≤ M :=
    CFSG.GroupTheory.le_of_commutator_eq_self_of_le_sup_of_isPGroup
      (K := ⊤) (N := M) (P := (qX2 a).ker) hP hperf hsup
  exact top_le_iff.mp hle

theorem normalClosure_Dsub_eq_top (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) :
    Subgroup.normalClosure (Dsub a hbr hr3 hWinv : Set (Hq a hWinv)) = ⊤ := by
  have hMtop := normalClosure_zpowers_dRoot_eq_top a hbr hr3
  rw [Dsub, Subgroup.coe_map, ← Subgroup.map_normalClosure
    (Subgroup.zpowers (⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩ : ↥(X2 a)) : Set ↥(X2 a))
    (QuotientGroup.mk' (rhoW a hWinv).ker) (QuotientGroup.mk'_surjective _)]
  rw [hMtop, Subgroup.map_top, MonoidHom.range_eq_top.mpr
    (QuotientGroup.mk'_surjective (rhoW a hWinv).ker)]

theorem card_Dsub (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (hWU : W ≤ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))) (hWne : W ≠ ⊥) :
    Nat.card (Dsub a hbr hr3 hWinv) = 3 := by
  let x : ↥(X2 a) := ⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩
  have hxorder : orderOf x = 3 := by
    change orderOf (⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩ : ↥(X2 a)) = 3
    rw [Subgroup.orderOf_mk a.dRoot (a.dRoot_mem_X2 hbr hr3), a.hdorder, hr3]
  have hzx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxorder]
  have hxN : x ∉ (rhoW a hWinv).ker := by
    intro hxN
    have h1 : rhoW a hWinv x = 1 := MonoidHom.mem_ker.mp hxN
    obtain ⟨w, hw, hne⟩ := a.exists_dRoot_act_ne hfixb hWU hWne
    have h2 : ((rhoW a hWinv) x ⟨w, hw⟩ : A0V d) = w := by
      rw [h1]
      rfl
    rw [rhoW_apply, rhoX_apply] at h2
    exact hne h2
  have hdisj : Subgroup.zpowers x ⊓ (rhoW a hWinv).ker = ⊥ := by
    haveI : Fact (Nat.card ↥(Subgroup.zpowers x)).Prime := ⟨by rw [hzx]; norm_num⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers x ⊓ (rhoW a hWinv).ker).subgroupOf (Subgroup.zpowers x))
    rcases h with hbot | htop
    · rw [eq_bot_iff]
      intro y hy
      have hyH : (⟨y, hy.1⟩ : ↥(Subgroup.zpowers x)) ∈
          (Subgroup.zpowers x ⊓ (rhoW a hWinv).ker).subgroupOf (Subgroup.zpowers x) :=
        Subgroup.mem_subgroupOf.mpr hy
      rw [hbot] at hyH
      have hy1 : (⟨y, hy.1⟩ : ↥(Subgroup.zpowers x)) = 1 := Subgroup.mem_bot.mp hyH
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy1)
    · exfalso
      apply hxN
      have hxH : (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) ∈
          (Subgroup.zpowers x ⊓ (rhoW a hWinv).ker).subgroupOf (Subgroup.zpowers x) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hxH).2
  have hcard := CFSG.card_map_eq_card_of_inf_ker_eq_bot
    (f := QuotientGroup.mk' (rhoW a hWinv).ker) (J := Subgroup.zpowers x)
    (by rw [QuotientGroup.ker_mk']; exact hdisj)
  rw [Dsub, hcard, hzx]

theorem isElemAbelian_Dsub (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)}
    (hWinv : ∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W)
    (hWU : W ≤ d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))) (hWne : W ≠ ⊥) :
    IsElemAbelian 3 (Dsub a hbr hr3 hWinv) := by
  have hcard := card_Dsub a hbr hr3 hfixb hWinv hWU hWne
  constructor
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic ↥(Dsub a hbr hr3 hWinv) := isCyclic_of_prime_card (p := 3) hcard
    exact IsCyclic.isMulCommutative
  · intro x hx
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥(Dsub a hbr hr3 hWinv)))
    rw [hcard] at h
    simpa using h

theorem exists_k462_quotient (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) (hq3 : r ≠ d.q)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    (hc : d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) ≠ ⊥)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H),
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
          Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (∃ n : ℕ, Odd n ∧ CFSG.Blueprint.LieModel H .PSL 2 2 n) ∨
        CFSG.Quasithin.IsExt H
          (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
          (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) ∧
      ∃ f : H →* Bar2 a.X, Function.Surjective f := by
  classical
  obtain ⟨W, hWU, hWne, hWinv, hWmin⟩ := a.exists_W hc
  haveI : Fact d.q.Prime := ⟨d.hq⟩
  have h2q : 2 < d.q := by
    rcases lt_or_eq_of_le d.hq.two_le with h | h
    · exact h
    · exact absurd h.symm d.hq2
  haveI hIrrW : Representation.IsIrreducible (rhoW a hWinv) :=
    a.rhoW_irreducible hWinv hWne hWmin
  have hFaith : Function.Injective (rhoH a hWinv) := a.rhoH_faithful hWinv
  have hIrrH : Representation.IsIrreducible (rhoH a hWinv) := a.rhoH_irreducible hWinv
  have hDcard : Nat.card (Dsub a hbr hr3 hWinv) = 3 :=
    a.card_Dsub hbr hr3 hfixb hWinv hWU hWne
  have hDnc : Subgroup.normalClosure (Dsub a hbr hr3 hWinv : Set (Hq a hWinv)) = ⊤ :=
    a.normalClosure_Dsub_eq_top hbr hr3 hWinv
  have hFixD : CFSG.LocalAnalysis.UniquenessCase.UCK.fixV (rhoH a hWinv)
      (Dsub a hbr hr3 hWinv) = ⊥ :=
    a.fixV_rhoH_Dsub_eq_bot hbr hr3 hfixb hWinv hWU
  have hDsub_el : IsElemAbelian 3 (Dsub a hbr hr3 hWinv) :=
    a.isElemAbelian_Dsub hbr hr3 hfixb hWinv hWU hWne
  have hN3 : ¬ 3 ∣ Nat.card (rhoW a hWinv).ker :=
    a.not_three_dvd_ker_rhoW hbr hr3 hfixb hWinv hWU hWne
  have hpRank_le : CFSG.Open.pRank 3 (⊤ : Subgroup (Hq a hWinv)) ≤ 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    calc CFSG.Open.pRank 3 (⊤ : Subgroup (Hq a hWinv))
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(X2 a)) :=
          CFSG.SectionRank.pRank_quotient_eq (rhoW a hWinv).ker hN3
      _ = CFSG.Open.pRank 3 (X2 a) :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (X2 a)).symm
      _ ≤ CFSG.Open.pRank 3 (a.X) := CFSG.SectionRank.pRank_mono (by norm_num) (X2_le_X a)
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 a.X)) :=
          (CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd (Y := a.X)
            Nat.prime_three (by norm_num)).symm
      _ ≤ 1 := CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_le_one_of_isL2_or_isSz
          (Or.inl (CFSG.GroupTheory.isL2_of_isSLn_two a.hm2 a.hXsl))
          Nat.prime_three (by norm_num)
  have hpRank_ge : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Hq a hWinv)) := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤)
      (E := Dsub a hbr hr3 hWinv) le_top hDsub_el (k := 1) (by rw [hDcard]; norm_num)
    simpa using h
  have hpRank : CFSG.Open.pRank 3 (⊤ : Subgroup (Hq a hWinv)) = 1 :=
    le_antisymm hpRank_le hpRank_ge
  have hKG : CFSG.Open.IsKGroup ↥D.M :=
    D.standing.kProper.isKGroup D.M (uc22p20a_M_ne_top D)
  have hKX2 : CFSG.Open.IsKGroup ↥(X2 a) :=
    CFSG.Open.IsKGroup.of_le (H := D.M) hKG (X2_le_DM a)
  have hKH : CFSG.Open.IsKGroup (Hq a hWinv) := hKX2.quotient (rhoW a hWinv).ker
  have hcomm : commutator (Hq a hWinv) = ⊤ := by
    haveI : Group.IsPerfect ↥(X2 a) := Subgroup.isPerfect_iff.mpr (X2_perfect a)
    haveI : Group.IsPerfect (Hq a hWinv) := inferInstance
    exact Group.IsPerfect.commutator_eq_top
  have hconc := hK462 d.q h2q (Hq a hWinv) hKH ↥W (rhoH a hWinv) hFaith hIrrH
    (Dsub a hbr hr3 hWinv) hDcard hDnc hFixD hpRank hcomm
  have hNle : (rhoW a hWinv).ker ≤ (qX2 a).ker :=
    a.ker_rhoW_le_ker_qX2 hbr hr3 hfixb hWinv hWU hWne
  let f : Hq a hWinv →* Bar2 a.X :=
    QuotientGroup.lift (rhoW a hWinv).ker (qX2 a)
      (fun n hn => MonoidHom.mem_ker.mp (hNle hn))
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := qX2_surjective a hbr hr3 y
    exact ⟨QuotientGroup.mk' (rhoW a hWinv).ker x, by
      rw [show f (QuotientGroup.mk' (rhoW a hWinv).ker x) = qX2 a x from
        QuotientGroup.lift_mk' (N := (rhoW a hWinv).ker) (φ := qX2 a) hNle x]
      exact hx⟩
  exact ⟨Hq a hWinv, inferInstance, inferInstance, hconc, f, hfsurj⟩

end S23_9_AdjData

theorem s23_9_A4_of (D : Data G) (Ch : Choice2011 G) : S23_9_A4 D Ch := by
  intro h1930 c hpr hV d b hb r hr hr2 hbr hr3 hfixb hrq hpow hnsu44 a hK462
  have hc : d.fixV (barImage D.M (Subgroup.zpowers (a.ctilde))) ≠ ⊥ :=
    a.fixV_ctilde_ne_bot hbr hr3 hrq hfixb
  obtain ⟨H, hHgrp, hHfin, hHalt, f, hfsurj⟩ :=
    a.exists_k462_quotient hbr hr3 hrq hfixb hc hK462
  letI : Group H := hHgrp
  letI : Finite H := hHfin
  exact CFSG.GroupTheory.not_surjective_of_k462_alternative
    (a.hparity hpow hnsu44).1 (a.hparity hpow hnsu44).2 a.hXsl hHalt f hfsurj

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
