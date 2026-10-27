module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E10Sub
public import CFSG.RankThree.PartTwo.Setup
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E1Basic
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E5Normal
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E9Mp

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem normalizer_ne_top (s : Setting443 G T M L B Tp VB) :
    Subgroup.normalizer (B : Set G) ≠ ⊤ := by
  intro h
  have hBn : B.Normal := Subgroup.normalizer_eq_top_iff.mp h
  have := s.hyp.simple
  rcases hBn.eq_bot_or_eq_top with hB | hB
  · exact s.hyp.B_ne_bot hB
  · obtain ⟨a, b, hab⟩ := s.hyp.nonabelian
    have hc := s.hyp.B_comm
    have ha : a ∈ B := hB ▸ Subgroup.mem_top a
    have hb : b ∈ B := hB ▸ Subgroup.mem_top b
    exact hab (congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))

theorem isQuasithin_normalizer (s : Setting443 G T M L B Tp VB) :
    IsQuasithin ↥(Subgroup.normalizer (B : Set G)) :=
  (CFSG.RankThree.PartTwo.evenRank_subgroup_le _).trans s.hyp.qtke.2.2

theorem isKGroupCat_normalizer (s : Setting443 G T M L B Tp VB) :
    CFSG.SectionRank.IsKGroupCat ↥(Subgroup.normalizer (B : Set G)) :=
  isKGroupCat_of_kProper s.hyp.qtke.1 (normalizer_ne_top s)

theorem locConf_of (s : Setting443 G T M L B Tp VB)
    (hU : IsUniqueM (perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) ⊔
      (Tp ⊓ Subgroup.normalizer (B : Set G))) M)
    (h448 : oddCoreIn (Subgroup.normalizer (B : Set G)) ≤ M ⊓ Subgroup.normalizer (B : Set G))
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hVL : VB = ⁅VB, perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))⁆) :
    LocConf ↥(Subgroup.normalizer (B : Set G))
      (VB.subgroupOf (Subgroup.normalizer (B : Set G)))
      ((perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))).subgroupOf
        (Subgroup.normalizer (B : Set G)))
      ((Tp ⊓ Subgroup.normalizer (B : Set G)).subgroupOf (Subgroup.normalizer (B : Set G)))
      (M.subgroupOf (Subgroup.normalizer (B : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set GB := Subgroup.normalizer (B : Set G) with hGB
  set LB := perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G)) with hLB
  set TB := Tp ⊓ GB with hTB
  have hT2 : IsPGroup 2 T := s.hyp.sylow.1
  have hVGB : VB ≤ GB := VB_le_normalizer s
  have hLBGB : LB ≤ GB :=
    (perfectCore_le _).trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hLBM : LB ≤ M := (LB_le L T B).trans (conjClosure_le_M s)
  have hTBT : TB ≤ T := inf_le_left.trans s.hyp.Tp_le
  have hLBV : LB ≤ Subgroup.normalizer (VB : Set G) :=
    (LB_le L T B).trans (le_sup_left.trans s.hyp.VB_normalized)
  have hTBV : TB ≤ Subgroup.normalizer (VB : Set G) :=
    hTBT.trans (le_sup_right.trans s.hyp.VB_normalized)
  refine
    { qt := isQuasithin_normalizer s
      kgroup := isKGroupCat_normalizer s
      o2 := pCoreOf_top_eq_bot (s.pCoreOf_normalizer_eq_bot hU)
      v_two := isPGroup_subgroupOf (hT2.to_le (VB_le_T s)) GB
      v_ne := subgroupOf_ne_bot hVGB s.hyp.VB_ne_bot
      v_odd := ?_
      v_eq := (commutator_subgroupOf_eq hVGB hLBGB hVL.symm).symm
      l_perfect := commutator_subgroupOf_eq hLBGB hLBGB (perfectCore_perfect _)
      l_le := fun _ hx => hLBM hx
      l_normal := fun x hx => mem_normalizer_subgroupOf
        (MB_le_normalizer_LB s h37 h38 h39 ⟨hx, x.2⟩)
      s_two := isPGroup_subgroupOf (hT2.to_le hTBT) GB
      s_le := fun _ hx => s.hyp.T_le (hTBT hx)
      v_norm := sup_le (le_normalizer_subgroupOf GB hLBV) (le_normalizer_subgroupOf GB hTBV)
      v_le := fun _ hx => subgroupOf_pCoreOf_le 2 M GB (VB_le_pCoreOf s hx)
      uniq := ?_
      cent := fun x hx => s.normalizer_VB_le hU
        (Subgroup.centralizer_le_normalizer _ (coe_mem_centralizer hVGB hx))
      cent_mod := ?_ }
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : (o : G) ∈ oddCoreIn GB := (mem_oddCoreIn_iff GB o).mpr ho
    have h1 : ⁅(v : G), (o : G)⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator (show (v : G) ∈ VB from hv) ho'
      rwa [commutator_VB_oddCoreIn s h448, Subgroup.mem_bot] at this
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · intro P hP hP2 hPN y hy
    have hP' : P.map GB.subtype ≠ ⊥ := fun h =>
      hP ((Subgroup.map_eq_bot_iff_of_injective _ GB.subtype_injective).mp h)
    have hXP : LB ⊔ TB ≤ Subgroup.normalizer ((P.map GB.subtype : Subgroup G) : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact coe_mem_normalizer_map (x := ⟨x, hLBGB hx⟩) (hPN (Subgroup.mem_sup_left hx))
      · exact coe_mem_normalizer_map (x := ⟨x, hx.2⟩) (hPN (Subgroup.mem_sup_right hx))
    exact isUniqueM_normalizer_le hU hP' (hP2.map GB.subtype) hXP (coe_mem_normalizer_map hy)
  · intro N hNL _ hNV
    have hN'L : N.map GB.subtype ≤ LB := Subgroup.map_le_iff_le_comap.mpr hNL
    have hN'V : N.map GB.subtype ≤ Subgroup.centralizer (VB : Set G) := by
      rintro _ ⟨n, hn, rfl⟩
      exact coe_mem_centralizer hVGB (hNV hn)
    have h1 : (⁅N, LB.subgroupOf GB⁆).map GB.subtype ≤ pCoreOf 2 LB := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLBGB]
      exact commutator_le_pCoreOf_LB s h37 h39 hN'L hN'V
    exact fun x hx => subgroupOf_pCoreOf_le 2 LB GB (h1 (Subgroup.mem_map_of_mem _ hx))

end CFSG.Quasithin.H13.Ch4.E443
