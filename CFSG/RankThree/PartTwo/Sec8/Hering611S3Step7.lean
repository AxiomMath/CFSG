module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Step6
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LieType.BorelTits.Basic
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Odd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open scoped Bracket

variable {G : Type*} [Group G] [Finite G]

private theorem three_subgroups_comm_eq_bot {W X : Subgroup G} {d : G}
    (hXd : X ≤ Subgroup.centralizer ({d} : Set G))
    (hWX : ∀ w ∈ W, ∀ x ∈ X, w * x * w⁻¹ ∈ X) (hW : W ≤ ⁅W, Subgroup.zpowers d⁆) :
    ⁅W, X⁆ = ⊥ := by
  have hdX : ∀ x ∈ X, Commute d x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hXd hx) d (Set.mem_singleton d)
  have hXD : X ≤ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((hdX x hx).zpow_left k).eq
  have hWX' : ⁅W, X⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro w hw x hx
    rw [commutatorElement_def]
    exact X.mul_mem (hWX w hw x hx) (X.inv_mem hx)
  have h1 : ⁅⁅W, X⁆, Subgroup.zpowers d⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅W, X⁆, Subgroup.zpowers d⁆ ≤ ⁅X, Subgroup.zpowers d⁆ :=
          Subgroup.commutator_mono hWX' le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXD
  have h2 : ⁅⁅X, Subgroup.zpowers d⁆, W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXD, Subgroup.commutator_bot_left]
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  refine eq_bot_iff.mpr ?_
  have hWc : W ≤ ⁅Subgroup.zpowers d, W⁆ :=
    hW.trans (le_of_eq (Subgroup.commutator_comm W (Subgroup.zpowers d)))
  calc ⁅W, X⁆ ≤ ⁅⁅Subgroup.zpowers d, W⁆, X⁆ := Subgroup.commutator_mono hWc le_rfl
    _ = ⊥ := h3

private theorem normalizes_centralizer_of_comm {S : Subgroup G} {x : G}
    (hx : ∀ s ∈ S, x * s = s * x) :
    x ∈ Subgroup.normalizer ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
  have hxi : ∀ s ∈ S, x⁻¹ * s = s * x⁻¹ := by
    intro s hs
    calc x⁻¹ * s = x⁻¹ * (s * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * s) * x⁻¹ := by rw [hx s hs]
      _ = s * x⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc s hs
    calc s * (x * c * x⁻¹) = (s * x) * c * x⁻¹ := by group
      _ = (x * s) * c * x⁻¹ := by rw [← hx s hs]
      _ = x * (s * c) * x⁻¹ := by group
      _ = x * (c * s) * x⁻¹ := by rw [hc s hs]
      _ = x * c * (s * x⁻¹) := by group
      _ = x * c * (x⁻¹ * s) := by rw [hxi s hs]
      _ = x * c * x⁻¹ * s := by group
  · intro hc s hs
    have hsx : x⁻¹ * s * x = s := by
      rw [mul_assoc, ← hx s hs, ← mul_assoc, inv_mul_cancel, one_mul]
    calc s * c = (x⁻¹ * s * x) * c := by rw [hsx]
      _ = x⁻¹ * (s * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * (x * c * x⁻¹ * s) * x := by rw [hc s hs]
      _ = (x⁻¹ * x) * c * (x⁻¹ * s * x) := by group
      _ = c * s := by rw [inv_mul_cancel, one_mul, hsx]

private theorem step7_aux (hchar : CFSG.Assembly.IsCharTwoType G) {d : G} (hd3 : d ^ 3 = 1)
    {V X : Fin 2 → Subgroup G} (hV2 : ∀ i, IsPGroup 2 (V i)) (hV1 : ∀ i, V i ≠ ⊥)
    (hVc : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x * y = y * x) (hX : ∀ i, Group.IsPerfect (X i))
    (hXd : ∀ i, X i ≤ Subgroup.centralizer ({d} : Set G))
    (hXN : ∀ i, X i ≤ Subgroup.normalizer (V i : Set G)) (hVX : ∀ i j, V j ≤ X i)
    (hUX : ∀ i, ⁅CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)), X i⁆ ≤ V i)
    (hUd : ∀ i, ¬ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)) ≤
      Subgroup.centralizer ({d} : Set G)) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ j, X j ≤ Subgroup.centralizer (U : Set G)) ∧
      d ∈ Subgroup.normalizer (U : Set G) := by
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hUd 0 (by intro x _; simp [Subgroup.mem_centralizer_iff])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Fin 2 → Subgroup G,
      ∀ i, U i = CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)) :=
    ⟨fun i => CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)), fun i => rfl⟩
  have hU2 : ∀ i, IsPGroup 2 (U i) := fun i => by
    rw [hUdef]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hUN : ∀ i, U i ≤ Subgroup.centralizer (V i : Set G) := fun i => by
    rw [hUdef]; exact Subgroup.map_subtype_le _
  have hNU : ∀ i, Subgroup.centralizer (V i : Set G) ≤ Subgroup.normalizer (U i : Set G) :=
    fun i => by rw [hUdef]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hUd' : ∀ i, ¬ U i ≤ Subgroup.centralizer ({d} : Set G) := fun i => by
    rw [hUdef]; exact hUd i
  have hdV : ∀ i, ∀ v ∈ V i, d * v = v * d := fun i v hv =>
    Subgroup.mem_centralizer_iff.mp (hXd i (hVX i i hv)) d (Set.mem_singleton d)
  have hdU : ∀ i, d ∈ Subgroup.normalizer (U i : Set G) := fun i => by
    rw [hUdef]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (normalizes_centralizer_of_comm (hdV i))
  have hDU : ∀ i, Subgroup.zpowers d ≤ Subgroup.normalizer (U i : Set G) :=
    fun i => Subgroup.zpowers_le.mpr (hdU i)
  have hcop : ∀ i, Nat.Coprime (Nat.card (Subgroup.zpowers d)) (Nat.card (U i)) := by
    intro i
    have hD3 : Nat.card (Subgroup.zpowers d) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hU2 i)
    rw [hD3, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hWeq : ∀ i,
      ⁅⁅U i, Subgroup.zpowers d⁆, Subgroup.zpowers d⁆ = ⁅U i, Subgroup.zpowers d⁆ := fun i =>
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_coprime
      (hDU i) (hcop i)
  have hWle : ∀ i, ⁅U i, Subgroup.zpowers d⁆ ≤ U i := fun i =>
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hDU i)
  have hWne : ∀ i, ⁅U i, Subgroup.zpowers d⁆ ≠ ⊥ := by
    intro i hbot
    apply hUd' i
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers d)))
  have hstep6 : ∀ i, ∀ x ∈ Subgroup.centralizer (V i : Set G), ∀ y ∈ X i,
      x * y * x⁻¹ ∈ X i :=
    fun i => step6_normalizes hchar (hV2 i) (hV1 i) (hVc i) (hX i) (hXN i) (hVX i i) (hUX i)
  have hWX : ∀ i, ⁅⁅U i, Subgroup.zpowers d⁆, X i⁆ = ⊥ := fun i =>
    three_subgroups_comm_eq_bot (hXd i)
      (fun w hw x hx => hstep6 i w ((hWle i).trans (hUN i) hw) x hx)
      (le_of_eq (hWeq i).symm)
  have hWC : ∀ i, ⁅U i, Subgroup.zpowers d⁆ ≤ Subgroup.centralizer (X i : Set G) := fun i =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hWX i)
  obtain ⟨N01, hN01⟩ : ∃ N : Subgroup G,
      N = Subgroup.centralizer ((V 0 ⊔ V 1 : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hVsup : ∀ i, V i ≤ V 0 ⊔ V 1 := Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩
  have hN1 : ∀ i, N01 ≤ Subgroup.centralizer (V i : Set G) := fun i => by
    rw [hN01]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hVsup i))
  have hWN01 : ∀ i, ⁅U i, Subgroup.zpowers d⁆ ≤ N01 := fun i => by
    rw [hN01]
    refine (hWC i).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ?_))
    exact sup_le (hVX i 0) (hVX i 1)
  have hnorm : ∀ i, N01 ≤ Subgroup.normalizer ((U i ⊓ N01 : Subgroup G) : Set G) := fun i => by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    have hk' : k ∈ U i ⊓ N01 := hk
    show h * k * h⁻¹ ∈ U i ⊓ N01
    rw [Subgroup.mem_inf] at hk' ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hNU i (hN1 i hh)) k).mp hk'.1,
      N01.mul_mem (N01.mul_mem hh hk'.2) (N01.inv_mem hh)⟩
  have hWO : ∀ i, ⁅U i, Subgroup.zpowers d⁆ ≤ CFSG.Assembly.pCoreOf 2 N01 := fun i =>
    (le_inf (hWle i) (hWN01 i)).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (hnorm i)
        ((hU2 i).to_le inf_le_left))
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup G,
      T = ⁅U 0, Subgroup.zpowers d⁆ ⊔ ⁅U 1, Subgroup.zpowers d⁆ := ⟨_, rfl⟩
  have hWT : ∀ i, ⁅U i, Subgroup.zpowers d⁆ ≤ T := by
    rw [hTdef]
    exact Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩
  have hOle : CFSG.Assembly.pCoreOf 2 N01 ≤ N01 := Subgroup.map_subtype_le _
  have hTO : T ≤ CFSG.Assembly.pCoreOf 2 N01 := by
    rw [hTdef]
    exact sup_le (hWO 0) (hWO 1)
  have hTpg : IsPGroup 2 T :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N01).to_le hTO
  have hTne : T ≠ ⊥ := by
    intro hbot
    have h0 := hWT 0
    rw [hbot] at h0
    exact hWne 0 (eq_bot_iff.mpr h0)
  have hdW : ∀ i, d ∈ Subgroup.normalizer ((⁅U i, Subgroup.zpowers d⁆ : Subgroup G) : Set G) :=
    fun i => Subgroup.normalizer_commutator_ge_right (U i) (Subgroup.zpowers d)
      (Subgroup.mem_zpowers d)
  have hTd : d ∈ Subgroup.normalizer (T : Set G) := by
    rw [hTdef]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr ⟨hdW 0, hdW 1⟩)
  have hTsup : T ≤ ⁅T, Subgroup.zpowers d⁆ := by
    calc T = ⁅U 0, Subgroup.zpowers d⁆ ⊔ ⁅U 1, Subgroup.zpowers d⁆ := hTdef
      _ ≤ ⁅T, Subgroup.zpowers d⁆ := by
        refine sup_le ?_ ?_
        · exact (le_of_eq (hWeq 0).symm).trans (Subgroup.commutator_mono_left (hWT 0))
        · exact (le_of_eq (hWeq 1).symm).trans (Subgroup.commutator_mono_left (hWT 1))
  have hTC : ∀ j, T ≤ Subgroup.centralizer (V j : Set G) := fun j =>
    hTO.trans (hOle.trans (hN1 j))
  have hXc : ∀ j, ⁅T, X j⁆ = ⊥ := fun j =>
    three_subgroups_comm_eq_bot (hXd j) (fun t ht x hx => hstep6 j t (hTC j ht) x hx) hTsup
  refine ⟨T, hTne, hTpg, fun j => ?_, hTd⟩
  have hXT : ⁅X j, T⁆ = ⊥ := (Subgroup.commutator_comm (X j) T).trans (hXc j)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXT

theorem false_of_steps (hchar : CFSG.Assembly.IsCharTwoType G) (hbig : NoBig3 G) {d : G}
    (hd3 : d ^ 3 = 1) {V X : Fin 2 → Subgroup G} (hV2 : ∀ i, IsPGroup 2 (V i))
    (hV1 : ∀ i, V i ≠ ⊥) (hVc : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, x * y = y * x)
    (hX : ∀ i, Group.IsPerfect (X i)) (hXd : ∀ i, X i ≤ Subgroup.centralizer ({d} : Set G))
    (hXN : ∀ i, X i ≤ Subgroup.normalizer (V i : Set G)) (hVX : ∀ i j, V j ≤ X i)
    (hUX : ∀ i, ⁅CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)), X i⁆ ≤ V i)
    (hUd : ∀ i, ¬ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V i : Set G)) ≤
      Subgroup.centralizer ({d} : Set G))
    (hB : ∃ B : Subgroup G, B ≤ X 0 ⊔ X 1 ∧ CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 27 ∧ Disjoint (Subgroup.zpowers d) B) : False := by
  obtain ⟨U, hU1, hU2, hUc, hdU⟩ :=
    step7_aux hchar hd3 hV2 hV1 hVc hX hXd hXN hVX hUX hUd
  obtain ⟨B, hBX, hBe, hB27, hBdisj⟩ := hB
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hUd 0 (by intro x _; simp [Subgroup.mem_centralizer_iff])
  have hBd : B ≤ Subgroup.centralizer ({d} : Set G) := hBX.trans (sup_le (hXd 0) (hXd 1))
  have hBC : B ≤ Subgroup.centralizer (U : Set G) := hBX.trans (sup_le (hUc 0) (hUc 1))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD3 : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers d) := by
    rw [Subgroup.zpowers_eq_closure]
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
    · intro a ha
      rw [Set.mem_singleton_iff.mp ha]
      exact hd3
  have hcomm : ∀ a ∈ Subgroup.zpowers d, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hdb : Commute d b := Subgroup.mem_centralizer_iff.mp (hBd hb) d (Set.mem_singleton d)
    exact (hdb.zpow_left k).eq
  have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers d ⊔ B) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hD3 hBe hcomm
  have hEN : Subgroup.zpowers d ⊔ B ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hdU) (hBC.trans (Subgroup.centralizer_le_normalizer _))
  have hdB : d ∉ B := fun hdB' =>
    hd1 (Subgroup.disjoint_def.mp hBdisj (Subgroup.mem_zpowers d) hdB')
  have hle : Nat.card B ≤ Nat.card ↥(Subgroup.zpowers d ⊔ B) :=
    Subgroup.card_le_of_le le_sup_right
  have hne : Nat.card ↥(Subgroup.zpowers d ⊔ B) ≠ Nat.card B := by
    intro heq
    apply hdB
    have hBeq : B = Subgroup.zpowers d ⊔ B :=
      Subgroup.eq_of_le_of_card_ge le_sup_right heq.le
    rw [hBeq]
    exact (le_sup_left : Subgroup.zpowers d ≤ Subgroup.zpowers d ⊔ B) (Subgroup.mem_zpowers d)
  have hbound : Nat.card ↥(Subgroup.zpowers d ⊔ B) ≤ 27 := hbig U _ hU1 hU2 hE hEN
  omega

end CFSG.RankThree.PartTwo.Sec8.Hering611
