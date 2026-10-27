module

public import CFSG.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.Quasithin.Vol2.Ch12Sec7Orb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

namespace S127.L712

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_center {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) :
    ∃ y ∈ N, y ∈ T ⊓ Subgroup.centralizer (T : Set G) ∧ y ^ 2 = 1 ∧ y ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnormal : (N.subgroupOf T).Normal :=
    ⟨fun n hn t => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hTN t.2) n).mp hn⟩
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hNT hx⟩ : ↥T) ∈ N.subgroupOf T := hx
    rw [hb, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set K : Subgroup ↥T := N.subgroupOf T ⊓ Subgroup.center ↥T with hK
  have hKp : IsPGroup 2 ↥K := hT.to_subgroup K
  have h2 : 2 ∣ Nat.card ↥K := by
    rcases hKp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) h1
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2
  refine ⟨((y : ↥T) : G), (y.2.1 : (y : ↥T) ∈ N.subgroupOf T),
    Subgroup.mem_inf.mpr ⟨(y : ↥T).2, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hc := Subgroup.mem_center_iff.mp y.2.2 ⟨x, hx⟩
    exact congrArg Subtype.val hc
  · have h3 : orderOf ((y : ↥T) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    rw [← h3]
    exact pow_orderOf_eq_one _
  · intro h0
    have h3 : orderOf ((y : ↥T) : G) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
    rw [h0, orderOf_one] at h3
    norm_num at h3

omit [Finite G] in
theorem le_normalizer_inf_centralizer {T L : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem hx hw.1) (T.inv_mem hx), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : x⁻¹ * l * x ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem hx)) l).mp hl
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ hl'
  calc l * (x * w * x⁻¹) = x * ((x⁻¹ * l * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
    _ = x * w * x⁻¹ * l := by group

theorem exists_conj_le {H T S : Subgroup G} (hT : QuasithinUnique.IsSylowTwoOf T H)
    (hS : IsPGroup 2 S) (hSH : S ≤ H) : ∃ c ∈ H, ∀ s ∈ S, c * s * c⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let PT : Sylow 2 ↥H := hTX.toSylow hT.2.2
  have hSX : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨Q, hQ⟩ := hSX.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥H) Q PT
  refine ⟨(c : G), c.2, fun s hs => ?_⟩
  have hsQ : (⟨s, hSH hs⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.mpr hs)
  have h2 : c * ⟨s, hSH hs⟩ * c⁻¹ ∈ ((c • Q : Sylow 2 ↥H) : Subgroup ↥H) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨_, hsQ, by simp [MulAut.conj_apply]⟩
  rw [hc] at h2
  exact h2

end S127.L712

open S127.L712 in
theorem lemma12_7_12_of (h1222 : Stmt12_2_2) (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1)
    (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) : Lemma12_7_12 := by
  intro G _ _ T L V t hS
  have h := hS.hyp
  have hy := h.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hT2 : IsPGroup 2 T := hy.sylow.1
  have hVT : V ≤ T := by
    obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
      hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
    exact (hall V hy.irrPlus).1.1
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hVab : IsElemAbelian 2 V := ⟨hcomm, fun x hx => S127.sq_eq_one_of_mem hy hx⟩
  by_contra hne
  obtain ⟨y, hyN, hyZ, hy2, hy1⟩ := exists_involution_center hT2 inf_le_left
    (le_normalizer_inf_centralizer hy.normalizes) hne
  have hZ : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro hb
    have hmem : y ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨Subgroup.subset_closure ⟨hyZ, hy2⟩, hyN.2⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact hy1 hmem
  have hCZ := (h129 G T L V hy).1 hZ
  have hs : 1 < E3.sParam hVab := by
    rw [(h10 G T L V t hS).2.1.2 hVab]
    norm_num
  obtain ⟨g, hne1, hle1⟩ := h1241 G T L V hy hCZ hVab hs
  set W : Subgroup G := CFSG.conjugate V g with hW
  have hcomm1 : ∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ * w⁻¹ ∈ V ⊓ W := fun v hv w hw =>
    hle1 (Subgroup.commutator_mem_commutator hv hw)
  have hWN : W ≤ Subgroup.normalizer (V : Set G) := by
    refine le_normalizer_of_conj_mem fun w hw v hv => ?_
    have hc := (hcomm1 v hv w hw).1
    have e : w * v * w⁻¹ = (v * w * v⁻¹ * w⁻¹)⁻¹ * v := by group
    rw [e]
    exact V.mul_mem (V.inv_mem hc) hv
  have hW2 : IsPGroup 2 W := hV2.map _
  have hP : IsPGroup 2 (V ⊔ W : Subgroup G) := hV2.to_sup_of_normal_left' hW2 hWN
  have hPN : V ⊔ W ≤ Subgroup.normalizer (V : Set G) := sup_le Subgroup.le_normalizer hWN
  have hsylN : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
    ⟨hTV, hT2, fun h2 => hy.sylow.2 (h2.trans (by
      simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTV))⟩
  obtain ⟨c, hcN, hcT⟩ := exists_conj_le hsylN hP hPN
  set A : Subgroup G := conjSubgroup V (g * c⁻¹) with hA
  have hAW : ∀ x ∈ A, c⁻¹ * x * c ∈ W := by
    intro x hx
    rw [hA, mem_conjSubgroup_iff] at hx
    change c⁻¹ * x * c ∈ conjSubgroup V g
    rw [mem_conjSubgroup_iff]
    have e : g * (c⁻¹ * x * c) * g⁻¹ = g * c⁻¹ * x * (g * c⁻¹)⁻¹ := by group
    rw [e]
    exact hx
  have hAT : A ≤ T := by
    intro x hx
    have := hcT _ (Subgroup.mem_sup_right (hAW x hx))
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at this
  have hAg : A ∈ E3.gammaSet V 0 T := ⟨hAT, g * c⁻¹, le_rfl, E3.mQuot_self _⟩
  have hAC : A ≤ Subgroup.centralizer (V : Set G) :=
    ((le_iSup₂_of_le A hAg le_rfl : A ≤ E3.wClos V 0 T).trans
      ((h11 G T L V t hS).1)).trans inf_le_right
  apply hne1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hcv : c * v * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcN v).mp hv
  have hcw : c * w * c⁻¹ ∈ A := by
    rw [hA, mem_conjSubgroup_iff]
    have e : g * c⁻¹ * (c * w * c⁻¹) * (g * c⁻¹)⁻¹ = g * w * g⁻¹ := by group
    rw [e]
    exact mem_conjSubgroup_iff.mp (show w ∈ conjSubgroup V g from hw)
  have hc := Subgroup.mem_centralizer_iff.mp (hAC hcw) _ hcv
  have h3 : c * (v * w) * c⁻¹ = c * (w * v) * c⁻¹ := by
    calc c * (v * w) * c⁻¹ = (c * v * c⁻¹) * (c * w * c⁻¹) := by group
      _ = (c * w * c⁻¹) * (c * v * c⁻¹) := hc
      _ = c * (w * v) * c⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel h3)).symm

end CFSG.Quasithin.H13
