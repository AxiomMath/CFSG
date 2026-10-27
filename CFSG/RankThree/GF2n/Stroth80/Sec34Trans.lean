module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
public import CFSG.RankThree.GF2n.Stroth80.Sec39
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic
public import CFSG.CGT.Timmesfeld75.Forms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
private theorem mk_mem_bar_iff [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (y : M) : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q S ↔ (y : G) ∈ S := by
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    have h1 : s⁻¹ * y ∈ Q.subgroupOf M := QuotientGroup.eq.mp hsy
    have h2 : (s : G)⁻¹ * y ∈ S := hQS h1
    have e : (y : G) = s * ((s : G)⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem hs h2
  · intro hy
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

omit [Finite G] in
private theorem mk_mem_conj_bar_iff [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (m y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) ↔
      (y : G) ∈ conjSubgroup (m : G) S := by
  rw [mem_conjSubgroup, mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff hQS]
  rfl

private theorem mem_normalizer_of_mk_mem_normalizer [(Q.subgroupOf M).Normal] {L : Subgroup G}
    (hQL : Q ≤ L) (hLM : L ≤ M) (y : M)
    (hN : QuotientGroup.mk' (Q.subgroupOf M) y ∈
      Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    (y : G) ∈ Subgroup.normalizer (L : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hLM hz⟩ : M) ∈ bar M Q L :=
    (mk_mem_bar_iff hQL _).mpr hz
  have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp h1
  rw [← map_inv, ← map_mul, ← map_mul] at h2
  exact (mk_mem_bar_iff hQL _).mp h2

theorem Ctx.isElemAbelian_bar_LB [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    IsElemAbelian 2 (bar M Q (LB M Q B)) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : Mbar M Q) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    apply QuotientGroup.eq.mpr
    have hxy : ⁅(y : G)⁻¹, (x : G)⁻¹⁆ ∈ Q :=
      Subgroup.commutator_le.mp hc.commutator_LB_le_Q _ ((LB M Q B).inv_mem hy) _
        ((LB M Q B).inv_mem hx)
    have e : (((x * y)⁻¹ * (y * x) : M) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show (((x * y)⁻¹ * (y * x) : M) : G) ∈ Q
    rw [e]
    exact hxy
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hc.sq_mem_Q_of_mem_LB hx)

omit [Finite G] in
theorem isTI_bar_of_isTIMod [(Q.subgroupOf M).Normal] {L : Subgroup G} (hQL : Q ≤ L)
    (hTI : IsTIMod M Q L) (g : Mbar M Q) :
    bar M Q L ⊓ conjSubgroup g⁻¹ (bar M Q L) = ⊥ ∨
      bar M Q L ⊓ conjSubgroup g⁻¹ (bar M Q L) = bar M Q L := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g⁻¹
  rw [← hm]
  rcases hTI m m.2 with h | h
  · left
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    have h3 : (y : G) ∈ L ⊓ conjSubgroup (m : G) L :=
      ⟨(mk_mem_bar_iff hQL y).mp hx1, (mk_mem_conj_bar_iff hQL m y).mp hx2⟩
    rw [h] at h3
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).mpr h3
  · right
    refine inf_eq_left.mpr fun x hx => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    exact (mk_mem_conj_bar_iff hQL m y).mpr (inf_eq_left.mp h ((mk_mem_bar_iff hQL y).mp hx))

theorem weaklyClosed_bar_of_weaklyClosed [(Q.subgroupOf M).Normal] {L : Subgroup G}
    (hQL : Q ≤ L) (hLM : L ≤ M)
    (hWC : ∀ m ∈ M, conjSubgroup m L ≤ Subgroup.normalizer (L : Set G) → conjSubgroup m L = L)
    (g : Mbar M Q)
    (hg : conjSubgroup g⁻¹ (bar M Q L) ≤ Subgroup.normalizer (bar M Q L : Set (Mbar M Q))) :
    conjSubgroup g⁻¹ (bar M Q L) = bar M Q L := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g⁻¹
  rw [← hm] at hg ⊢
  have key : conjSubgroup (m : G) L ≤ Subgroup.normalizer (L : Set G) := by
    intro y hy
    have hyM : y ∈ M := by
      have h1 := M.mul_mem (M.mul_mem m.2 (hLM (mem_conjSubgroup.mp hy))) (M.inv_mem m.2)
      rwa [show (m : G) * ((m : G)⁻¹ * y * m) * (m : G)⁻¹ = y by group] at h1
    exact mem_normalizer_of_mk_mem_normalizer hQL hLM ⟨y, hyM⟩
      (hg ((mk_mem_conj_bar_iff hQL m ⟨y, hyM⟩).mpr hy))
  have hL := hWC m m.2 key
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
  rw [mk_mem_conj_bar_iff hQL, mk_mem_bar_iff hQL, hL]

theorem Ctx.normal_isPGroup_two_Mbar_eq_bot [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (N : Subgroup (Mbar M Q)) (hN : N.Normal) (hP : IsPGroup 2 N) : N = ⊥ := by
  rw [eq_bot_iff, ← hc.pCore_two_Mbar]
  exact le_sSup ⟨hN, hP⟩

theorem Ctx.exists_conj_LB_of_transitivityTI (hc : Ctx M Q Z B)
    (hT75 : TimmesfeldTransitivityTI) (hTI : IsTIMod M Q (LB M Q B))
    (hWC : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
      conjSubgroup m (LB M Q B) = LB M Q B)
    {t t' : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q) (ht' : t' ∈ LB M Q B) (ht'Q : t' ∉ Q) :
    ∃ m ∈ M, m ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ (m * t * m⁻¹)⁻¹ * t' ∈ Q := by
  haveI := hc.normal_Q_in_M
  have hQL : Q ≤ LB M Q B := le_sup_left
  have htM : t ∈ M := hc.LB_le_M ht
  have ht'M : t' ∈ M := hc.LB_le_M ht'
  have hx1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨t, htM⟩ : M) ≠ 1 := fun h =>
    htQ ((QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (⟨t, htM⟩ : M)).mp h)
  have hy1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨t', ht'M⟩ : M) ≠ 1 := fun h =>
    ht'Q ((QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (⟨t', ht'M⟩ : M)).mp h)
  obtain ⟨g, hgN, hg⟩ := hT75 (Mbar M Q) (bar M Q (LB M Q B)) hc.isElemAbelian_bar_LB
    (isTI_bar_of_isTIMod hQL hTI) (weaklyClosed_bar_of_weaklyClosed hQL hc.LB_le_M hWC)
    (fun N hN hP => hc.normal_isPGroup_two_Mbar_eq_bot N hN hP)
    _ ((mk_mem_bar_iff hQL _).mpr ht) hx1 _ ((mk_mem_bar_iff hQL _).mpr ht') hy1
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
  rw [← map_inv, ← map_mul, ← map_mul] at hg
  exact ⟨m, m.2, mem_normalizer_of_mk_mem_normalizer hQL hc.LB_le_M m hgN,
    QuotientGroup.eq (s := Q.subgroupOf M) |>.mp hg⟩

theorem stroth34_caseA_n3 (hT75 : TimmesfeldTransitivityTI) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B))
    (hTI : IsTIMod M Q (LB M Q B))
    (hWC : ∀ m ∈ M, conjSubgroup m (LB M Q B) ≤ Subgroup.normalizer (LB M Q B : Set G) →
      conjSubgroup m (LB M Q B) = LB M Q B)
    (hSQ : ¬ hc.Spure ≤ Q) :
    n = 3 ∧ hc.Spure = LB M Q B := by
  obtain ⟨t, htS, htQ⟩ := SetLike.not_le_iff_exists.mp hSQ
  have hSL : hc.Spure = LB M Q B := by
    refine le_antisymm (fun s hs => hs.1) fun t' ht' => ?_
    by_cases ht'Q : t' ∈ Q
    · exact hc.Q_le_Spure ht'Q
    obtain ⟨m, hm, hmN, hq⟩ := hc.exists_conj_LB_of_transitivityTI hT75 hTI hWC htS.1 htQ ht' ht'Q
    have hmt : m * t * m⁻¹ ∈ LB M Q B := (Subgroup.mem_normalizer_iff.mp hmN t).mp htS.1
    have e : t' = (m * t * m⁻¹) * ((m * t * m⁻¹)⁻¹ * t') := by group
    rw [e]
    exact hc.Spure.mul_mem (hc.conj_mem_Spure hno hm htS hmt) (hc.Q_le_Spure hq)
  refine ⟨?_, hSL⟩
  have h33 := (hc.card_of_3_3 hw (by omega) hno (stroth_3_3 hc hw (by omega))).1
  have hle := hc.card_Spure_le hno
  rw [hSL, h33] at hle
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have h2 : Nat.card Z ^ (n - 1) ≤ Nat.card Z ^ 2 := Nat.le_of_mul_le_mul_left hle Nat.card_pos
  have h3 : n - 1 ≤ 2 := (Nat.pow_le_pow_iff_right (by omega)).mp h2
  omega

end CFSG.RankThree.GF2n.Stroth80
