module

public import CFSG.Quasithin.Vol2.Ch10SecKRTi
public import CFSG.Quasithin.Vol2.Ch10SecKRTb

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

omit [Finite G] in
theorem isPerfect_of_commutator_eq {X : Subgroup G} (h : ⁅X, X⁆ = X) : Group.IsPerfect ↥X := by
  refine ⟨?_⟩
  rw [_root_.commutator_def]
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]

theorem not_isSolvable_Kbar (cfg : B0KConfig G T L I H K M₁ J n m) :
    ¬ Group.IsSolvable ↥(modO2Image M₁ K) :=
  not_isSolvable_of_mem_cComp (Kbar_mem_lFamily cfg)

theorem K_le_thompsonJ (h1022 : Stmt10_2_2) (cfg : B0KConfig G T L I H K M₁ J n m)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) : K ≤ thompsonJ (J ⊔ T) := by
  have hKT : conjClosure K T ≤ J := conjClosure_le fun t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTJ ht) k).mp (cfg.hKJ hk)
  have hHH₀ : H ≤ J ⊔ T := H_le_of cfg le_sup_right (hKT.trans le_sup_left)
  have hO2H := ((h1022 G T L I cfg.hyp H cfg.hH cfg.hZH).2 (Or.inl ⟨n, cfg.case1⟩)).1.1
  have hK1 : K ≤ oTwoUpper H :=
    (eq_oTwoUpper_of_perfect (perfect_of_mem_cComp cfg.hK)).le.trans
      (oTwoUpper_mono (le_of_mem_cComp cfg.hK))
  rw [hO2H] at hK1
  refine hK1.trans ((Subgroup.commutator_mono ((oTwoUpper_le H).trans hHH₀)
    (thompsonJ_le_thompsonJ_of_isSylowTwoOf
      (sylow_of_le cfg (le_sup_right : T ≤ J ⊔ T)))).trans ?_)
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp (B6.le_normalizer_thompsonJ _)

theorem le_thompsonJ (h1022 : Stmt10_2_2) (cfg : B0KConfig G T L I H K M₁ J n m)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpSL : IsSL2 p (↥(modO2Image M₁ J) ⧸ CFSG.oddCore ↥(modO2Image M₁ J))) :
    J ≤ thompsonJ (J ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ := J ⊔ T with hH₀
  set N := J ⊓ thompsonJ H₀ with hNdef
  have hH₀N : H₀ ≤ Subgroup.normalizer (N : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := Subgroup.mem_normalizer_iff.mp ((sup_le Subgroup.le_normalizer hTJ) hx) g
    have h2 := Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_thompsonJ H₀ hx) g
    exact ⟨fun hg => ⟨h1.mp hg.1, h2.mp hg.2⟩, fun hg => ⟨h1.mpr hg.1, h2.mpr hg.2⟩⟩
  have hKN : K ≤ N := le_inf cfg.hKJ (K_le_thompsonJ h1022 cfg hTJ)
  have hNJ : modO2Image M₁ N ≤ modO2Image M₁ J := Subgroup.map_mono fun _ hx => hx.1
  have hNn : ((modO2Image M₁ N).subgroupOf (modO2Image M₁ J)).Normal := by
    refine ⟨fun y hy z => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := z.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hay, ← hbz, ← map_mul,
      ← map_inv, ← map_mul]
    refine ⟨b * a * b⁻¹, ?_, rfl⟩
    have hbG : ((b : ↥M₁) : G) ∈ H₀ := Subgroup.mem_sup_left hb
    exact (Subgroup.mem_normalizer_iff.mp (hH₀N hbG) (a : G)).mp ha
  have hns : ¬ Group.IsSolvable ↥((modO2Image M₁ N).subgroupOf (modO2Image M₁ J)) := by
    intro hs
    have hs' : Group.IsSolvable ↥(modO2Image M₁ N) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hNJ).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNJ).symm.injective
    have hKb : modO2Image M₁ K ≤ modO2Image M₁ N := Subgroup.map_mono fun _ hx => hKN hx
    exact not_isSolvable_Kbar cfg (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hKb) (Subgroup.inclusion_injective hKb))
  have htop := eq_top_of_not_isSolvable
    (isPerfect_of_commutator_eq (perfect_of_mem_cComp (Jbar_mem_cComp cfg))) hp hp5 hpSL hNn hns
  have hJN : modO2Image M₁ J ≤ modO2Image M₁ N := Subgroup.subgroupOf_eq_top.mp htop
  have hJsup := le_sup_pCoreOf_of_le (J_le cfg) hJN
  have hQT : pCoreOf 2 M₁ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf (sylow cfg)
  have hNn' : (N.subgroupOf (N ⊔ pCoreOf 2 M₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer ((hQT.trans le_sup_right).trans hH₀N))
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 M₁) := by
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₁).isNilpotent
    infer_instance
  have hP : perfectCore (N ⊔ pCoreOf 2 M₁) ≤ N :=
    perfectCore_le_of_sup_solvable le_sup_left hNn' rfl hsolv
  exact ((le_perfectCore_of_perfect hJsup (perfect_of_mem_cComp cfg.hJ)).trans hP).trans
    inf_le_right

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
