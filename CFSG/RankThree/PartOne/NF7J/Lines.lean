module

public import CFSG.RankThree.PartOne.K1320.Pair
public import CFSG.RankThree.PartOne.NF7J.LRoots2

public section

namespace CFSG.RankThree.PartOne.NF7J

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor rt permSL IsZeta diagSL tSep)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

section Members

variable {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem member_package' (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 3)
    {z : MulAut E}
    (h6 : ∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z)
    (h8 : ∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1) (hinv : ∀ e : E, z e = e⁻¹)
    {J : Subgroup G} (hJ : J ∈ thetaCompZeroStarE p E) :
    ∃ (B : Subgroup G) (c' : G), Sec12Hyp G p B c' J E ∧ Sec12Facts G p B c' J E ∧ c' ∈ E ∧
      c' ≠ 1 ∧ E = B ∧ ∃ r : ℕ, (r = 1 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8) ∧ RowModel p J r ∧
        RowWeylIso E (torusImage E J) r := by
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate J hJ
  have hc'E : c' ∈ E := hB.1 hc'B
  have hBE : B = E := Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hcard, hB.2.2.1])
  obtain ⟨r, hr, hmodel, hW⟩ := K1320.member_row h' hF' hcard h6 h8
    (K1320.inverter_not_mem_torusImage h' hc'E hc'1 hinv)
  exact ⟨B, c', h', hF', hc'E, hc'1, hBE.symm, r, hr, hmodel, hW⟩

end Members

section Chevalley

variable {K : Type} [Field K] {ρ : SL3 K →* G}

omit [Finite G] in
theorem rootG_commute {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) :
    ∀ a ∈ rootG ρ hij, ∀ b ∈ rootG ρ hkl, a * b = b * a := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, rootGrp_commute hij hkl hjk hli x hx y hy]

theorem swap_comm_cases : ∀ a b c d : Fin 3, a ≠ b → c ≠ d → Equiv.swap a b ≠ Equiv.swap c d →
    ((b ≠ c ∧ d ≠ a) ∨ (b ≠ d ∧ c ≠ a)) ∧ ((a ≠ c ∧ d ≠ b) ∨ (a ≠ d ∧ c ≠ b)) := by decide

end Chevalley

section Main

variable {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

omit [Finite G] in
theorem refl_sq {u : MulAut E} (hu : u ∈ reflectionSet p E) : u * u = 1 := by
  have := pow_orderOf_eq_one u
  rwa [hu.1.1, sq] at this

theorem linesComm_of
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A) (hdvd : p ∣ 2 ^ f - 1)
    (hmem : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s * t ≠ t * s →
      ∃ J ∈ thetaCompZeroStarE p E, s ∈ torusImage E J ∧ t ∈ torusImage E J)
    (hkfat : ∀ s ∈ reflectionSet p E, KFAt p E f s) {z : MulAut E}
    (h6 : ∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z)
    (h8 : ∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1) (hinv : ∀ e : E, z e = e⁻¹) :
    ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, orderOf (s * t) = 3 →
      ∀ T ∈ RootGp p E f s, ∃ S ∈ RootGp p E f t, ∀ a ∈ T, ∀ b ∈ S, a * b = b * a := by
  intro s hs t ht hord T hT'
  have hst : s * t ≠ t * s := by
    intro hc
    have h2 : (s * t) ^ 2 = 1 := by
      calc (s * t) ^ 2 = s * t * (s * t) := pow_two _
        _ = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [← hc]
        _ = (s * s) * (t * t) := by group
        _ = 1 := by rw [refl_sq hs, refl_sq ht, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at this
    omega
  obtain ⟨I, hI, hsI, htI⟩ := hmem s hs t ht hst
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨B, c', h', hF', hc'E, hc'1, hEB, r, hr, hmodel', hW⟩ :=
    member_package' hF13 hcard h6 h8 hinv hI
  have hg : s * t ∈ torusImage E I := (torusImage E I).mul_mem hsI htI
  have hg3 : (s * t) ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hg1 : s * t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    omega
  have hr1 : r = 1 := K1320.row_one_of_order_three hr hW hg hg3 hg1
  subst hr1
  subst hEB
  obtain ⟨fI, hfI1, hfIp, hmI⟩ := hmodel'
  have hJ : JGood p E c' I := S13K.jGood_of_row1 h' hF' rfl ⟨fI, hfI1, hfIp, hmI⟩
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA hJ hfIp hmI
  have hchar : CharP K 2 := charP_two_of_card hK
  obtain ⟨τ, hAt, hkz, hk, hse⟩ := S13K.kfAt_of_cover hJ hρ hK hfI1 hfIp hs hsI
  obtain ⟨τ', hAt', hkz', hk', hte⟩ := S13K.kfAt_of_cover hJ hρ hK hfI1 hfIp ht htI
  have hff : fI = f := K1320.psl_two_degree_eq hAt.2.1 (hkfat s hs).2.1
  have hK' : Nat.card K = 2 ^ f := by rw [← hff]; exact hK
  have hL : LineHyp p E c' I f ρ := ⟨hJ, hρ, hK', hdvd⟩
  have hij : τ 0 ≠ τ 1 := τ.injective.ne (by decide)
  have hkl : τ' 0 ≠ τ' 1 := τ'.injective.ne (by decide)
  have hs_node : s = nodeOf E ρ (τ 0) (τ 1) := by
    rw [← hse]
    unfold nodeOf
    rw [piAut_of_mem hk]
    rfl
  have ht_node : t = nodeOf E ρ (τ' 0) (τ' 1) := by
    rw [← hte]
    unfold nodeOf
    rw [piAut_of_mem hk']
    rfl
  have hswap : Equiv.swap (τ 0) (τ 1) ≠ Equiv.swap (τ' 0) (τ' 1) := by
    intro heq
    have hst' : s = t := by
      rw [hs_node, ht_node]
      unfold nodeOf
      rw [heq]
    have : orderOf (s * t) = 1 := by rw [hst', refl_sq ht, orderOf_one]
    omega
  have hKs : kZero p E s = Kof E I (nodeOf E ρ (τ 0) (τ 1)) :=
    hkz.trans (hL.kof_nodeOf rfl rfl).symm
  have hKt : kZero p E t = Kof E I (nodeOf E ρ (τ' 0) (τ' 1)) :=
    hkz'.trans (hL.kof_nodeOf rfl rfl).symm
  have hRs : RootGp p E f s = {rootG ρ hij, rootG ρ hij.symm} := by
    rw [← hL.rootSetJ_eq hij]
    ext S
    simp only [RootGp, RootSetJ, Set.mem_ofPred_eq, hKs]
  have hRt : RootGp p E f t = {rootG ρ hkl, rootG ρ hkl.symm} := by
    rw [← hL.rootSetJ_eq hkl]
    ext S
    simp only [RootGp, RootSetJ, Set.mem_ofPred_eq, hKt]
  obtain ⟨hc1, hc2⟩ := swap_comm_cases (τ 0) (τ 1) (τ' 0) (τ' 1) hij hkl hswap
  rw [hRs] at hT'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT'
  rcases hT' with rfl | rfl
  · rcases hc1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨rootG ρ hkl, by rw [hRt]; exact Set.mem_insert _ _, rootG_commute hij hkl h1 h2⟩
    · exact ⟨rootG ρ hkl.symm, by rw [hRt]; exact Set.mem_insert_of_mem _ rfl,
        rootG_commute hij hkl.symm h1 h2⟩
  · rcases hc2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨rootG ρ hkl, by rw [hRt]; exact Set.mem_insert _ _, rootG_commute hij.symm hkl h1 h2⟩
    · exact ⟨rootG ρ hkl.symm, by rw [hRt]; exact Set.mem_insert_of_mem _ rfl,
        rootG_commute hij.symm hkl.symm h1 h2⟩

end Main

end CFSG.RankThree.PartOne.NF7J
