module

public import CFSG.RankThree.GF2n.Parrott.FixDimIII
public import CFSG.RankThree.GF2n.Parrott.CommutatorDetermined
public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem conjV_pi_eq_self_of_mem_centerIn (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    {y : G} (hy : y ∈ centerIn (J z ⊓ centralizer ({(x : G)} : Set G))) :
    conjV h x (QuotientV.pi z ⟨y, hy.1.1⟩) = QuotientV.pi z ⟨y, hy.1.1⟩ := by
  have hyx : y ∈ Subgroup.centralizer ({(x : G)} : Set G) := hy.1.2
  rw [conjV_mk]
  congr 1
  apply Subtype.ext
  rw [conjJ'_apply_coe]
  have hxy : (x : G) * (y : G) = (y : G) * (x : G) :=
    (mem_centralizer_singleton_iff.mp hyx).symm
  calc (x : G) * (y : G) * (x : G)⁻¹ = (y : G) * (x : G) * (x : G)⁻¹ := by rw [hxy]
    _ = (y : G) := by group

private theorem conjV_trace_eq_self (h : Tim79a.ParrottHyp z) {x : ↥(H z)} (hx3 : x ^ 3 = 1)
    (w : QuotientV.V z) :
    conjV h x (w * conjV h x w * conjV h x (conjV h x w)) =
      w * conjV h x w * conjV h x (conjV h x w) := by
  have hcommV : ∀ u v : QuotientV.V z, u * v = v * u :=
    (QuotientV.isMulCommutative_V h).is_comm.comm
  have hx3w : conjV h x (conjV h x (conjV h x w)) = w := by
    have hh := congrArg (fun τ : MulAut (QuotientV.V z) => τ w)
      (show conjV h x ^ 3 = 1 by rw [← map_pow, hx3, map_one])
    simpa [pow_succ, MulAut.mul_apply] using hh
  rw [map_mul, map_mul, hx3w]
  calc conjV h x w * conjV h x (conjV h x w) * w
      = w * (conjV h x w * conjV h x (conjV h x w)) := hcommV _ _
    _ = w * conjV h x w * conjV h x (conjV h x w) := by rw [mul_assoc]

private theorem polarVZMod_trace_eq (h : Tim79a.ParrottHyp z) {x : ↥(H z)} {v : QuotientV.V z}
    (hv : conjV h x v = v) (w : QuotientV.V z) :
    polarVZMod h v (w * conjV h x w * conjV h x (conjV h x w)) = polarVZMod h v w := by
  have hbw : polarVZMod h v (conjV h x w) = polarVZMod h v w :=
    polarVZMod_conj_eq_of_fixed h hv w
  have hbw2 : polarVZMod h v (conjV h x (conjV h x w)) = polarVZMod h v w := by
    rw [polarVZMod_conj_eq_of_fixed h hv (conjV h x w), hbw]
  rw [polarVZMod_add_right, polarVZMod_add_right, hbw, hbw2]
  exact (by decide : ∀ a : ZMod 2, a + a + a = a) _

private theorem mem_centralizer_of_mem_centerIn_J_inf_centralizer (h : Tim79a.ParrottHyp z)
    {x : ↥(H z)} (hx3 : x ^ 3 = 1) (hZx : conjZ z x = 1) {y : G}
    (hy : y ∈ centerIn (J z ⊓ centralizer ({(x : G)} : Set G))) :
    y ∈ Subgroup.centralizer (J z : Set G) := by
  refine (pi_mem_radical_iff h ⟨y, hy.1.1⟩).mp fun w => ?_
  obtain ⟨j', hj'⟩ := QuotientV.pi_surjective z (w * conjV h x w * conjV h x (conjV h x w))
  have hj'cent : j' ∈ centralizerJ x :=
    mem_centralizerJ_of_conjV_pi_eq h hx3 hZx (by rw [hj']; exact conjV_trace_eq_self h hx3 w)
  have hj'K : (j' : G) ∈ J z ⊓ centralizer ({(x : G)} : Set G) :=
    mem_inf.mpr ⟨j'.2, mem_centralizer_singleton_iff.mpr (mem_centralizerJ_iff.mp hj'cent)⟩
  rw [← polarVZMod_trace_eq h (conjV_pi_eq_self_of_mem_centerIn h hy) w, ← hj']
  exact (polarVZMod_pi_eq_zero_iff h ⟨y, hy.1.1⟩ j').mpr
    (Subgroup.mem_centralizer_iff.mp hy.2 (j' : G) hj'K).symm

theorem J_inf_centralizer_le_of_isSylowOf (h : Tim79a.ParrottHyp z) {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({x} : Set G))) :
    J z ⊓ centralizer ({x} : Set G) ≤ T := by
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  refine le_isSylowOf_of_isPGroup_of_le_normalizer hT
    (fun j hj => mem_inf.mpr ⟨J_le_H hj.1, hj.2⟩) ?_ (isPGroup_J h).to_inf_left
  have key : ∀ c ∈ H z ⊓ centralizer ({x} : Set G), ∀ j ∈ J z ⊓ centralizer ({x} : Set G),
      c * j * c⁻¹ ∈ J z ⊓ centralizer ({x} : Set G) := by
    intro c hc j hj
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1) j).mp hj.1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc.2
    have hjx : j * x = x * j := mem_centralizer_singleton_iff.mp hj.2
    have hcx' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
        _ = x * c⁻¹ := by group
    calc c * j * c⁻¹ * x = c * j * (c⁻¹ * x) := by group
      _ = c * j * (x * c⁻¹) := by rw [hcx']
      _ = c * (j * x) * c⁻¹ := by group
      _ = c * (x * j) * c⁻¹ := by rw [hjx]
      _ = (c * x) * j * c⁻¹ := by group
      _ = (x * c) * j * c⁻¹ := by rw [hcx]
      _ = x * (c * j * c⁻¹) := by group
  intro c hc
  rw [mem_normalizer_iff]
  intro j
  refine ⟨key c hc j, fun hj => ?_⟩
  have h1 := key c⁻¹ (inv_mem hc) _ hj
  simpa [mul_assoc] using h1

theorem centerIn_J_inf_centralizer_eq (h : Tim79a.ParrottHyp z) {x : ↥(H z)} (hx3 : x ^ 3 = 1)
    (hZx : conjZ z x = 1) :
    centerIn (J z ⊓ centralizer ({(x : G)} : Set G)) = centerIn (J z) := by
  have hKleJ : J z ⊓ centralizer ({(x : G)} : Set G) ≤ J z := inf_le_left
  apply le_antisymm
  · intro y hy
    exact mem_inf.mpr ⟨hy.1.1,
      mem_centralizer_of_mem_centerIn_J_inf_centralizer h hx3 hZx hy⟩
  · intro e he
    have heJ : e ∈ J z := he.1
    have hecentJ : e ∈ Subgroup.centralizer (J z : Set G) := he.2
    have hex : e ∈ Subgroup.centralizer ({(x : G)} : Set G) :=
      centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZx he
    have heK : e ∈ J z ⊓ centralizer ({(x : G)} : Set G) := mem_inf.mpr ⟨heJ, hex⟩
    have hecentK : e ∈ Subgroup.centralizer
        ((J z ⊓ centralizer ({(x : G)} : Set G)) : Set G) :=
      Subgroup.centralizer_le hKleJ hecentJ
    exact mem_inf.mpr ⟨heK, hecentK⟩

private theorem exists_three_of_eight_le_card (F : Subgroup (QuotientV.V z))
    (hF8 : 8 ≤ Nat.card ↥F) :
    ∃ a b c : ↥F, a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ b ≠ a ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b := by
  classical
  haveI : Fintype ↥F := Fintype.ofFinite _
  let s : Finset ↥F := Finset.univ
  have hs_card : s.card = Nat.card ↥F := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have h1card : (s.erase (1 : ↥F)).card = s.card - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ _)
  have hpos1 : 0 < (s.erase (1 : ↥F)).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos1
  have ha1 : a ≠ 1 := (Finset.mem_erase.mp ha).1
  have h2card : ((s.erase (1 : ↥F)).erase a).card = (s.erase (1 : ↥F)).card - 1 :=
    Finset.card_erase_of_mem ha
  have hpos2 : 0 < ((s.erase (1 : ↥F)).erase a).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos2
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hb1 : b ≠ 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb)).1
  have h3card : (((s.erase (1 : ↥F)).erase a).erase b).card =
      ((s.erase (1 : ↥F)).erase a).card - 1 :=
    Finset.card_erase_of_mem hb
  have h4lower : ((((s.erase (1 : ↥F)).erase a).erase b).erase (a * b)).card ≥
      (((s.erase (1 : ↥F)).erase a).erase b).card - 1 := by
    by_cases hm : (a * b) ∈ (((s.erase (1 : ↥F)).erase a).erase b)
    · rw [Finset.card_erase_of_mem hm]
    · rw [Finset.erase_eq_of_notMem hm]
      exact Nat.sub_le _ _
  have hpos4 : 0 < ((((s.erase (1 : ↥F)).erase a).erase b).erase (a * b)).card := by
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos4
  have hc_ne_ab : c ≠ a * b := (Finset.mem_erase.mp hc).1
  have hc3 : c ∈ (((s.erase (1 : ↥F)).erase a).erase b) := Finset.mem_of_mem_erase hc
  have hc_ne_b : c ≠ b := (Finset.mem_erase.mp hc3).1
  have hc2 : c ∈ ((s.erase (1 : ↥F)).erase a) := Finset.mem_of_mem_erase hc3
  have hc_ne_a : c ≠ a := (Finset.mem_erase.mp hc2).1
  have hc1 : c ∈ (s.erase (1 : ↥F)) := Finset.mem_of_mem_erase hc2
  have hc_ne_1 : c ≠ 1 := (Finset.mem_erase.mp hc1).1
  exact ⟨a, b, c, ha1, hb1, hc_ne_1, hba, hc_ne_a, hc_ne_b, hc_ne_ab⟩

private theorem polarVZMod_eq_one_of_forall_qVZMod_eq_one (h : Tim79a.ParrottHyp z)
    {F : Subgroup (QuotientV.V z)}
    (hq1 : ∀ v : QuotientV.V z, v ∈ F → v ≠ 1 → qVZMod h v = 1) :
    ∀ a b : QuotientV.V z, a ∈ F → b ∈ F → a ≠ 1 → b ≠ 1 → a ≠ b →
      polarVZMod h a b = 1 := by
  intro a b haF hbF ha1 hb1 hab
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have hh := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at hh
  have habF : a * b ∈ F := F.mul_mem haF hbF
  have hab1 : a * b ≠ 1 := by
    intro h1
    have h' : a * b = a * a := by rw [h1, hsq a]
    exact hab (mul_left_cancel h').symm
  have hqa : qVZMod h a = 1 := hq1 a haF ha1
  have hqb : qVZMod h b = 1 := hq1 b hbF hb1
  have hqab' : qVZMod h (a * b) = 1 := hq1 (a * b) habF hab1
  have hmain : (1 : ZMod 2) + 1 + polarVZMod h a b = 1 := by
    calc (1 : ZMod 2) + 1 + polarVZMod h a b
        = qVZMod h a + qVZMod h b + polarVZMod h a b := by rw [hqa, hqb]
      _ = qVZMod h (a * b) := (qVZMod_mul_add h a b).symm
      _ = 1 := hqab'
  have h2 : (1 : ZMod 2) + 1 = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  rwa [h2, zero_add] at hmain

private theorem false_of_eight_le_card_of_forall_qVZMod_eq_one (h : Tim79a.ParrottHyp z)
    {F : Subgroup (QuotientV.V z)} (hF8 : 8 ≤ Nat.card ↥F)
    (hq1 : ∀ v : QuotientV.V z, v ∈ F → v ≠ 1 → qVZMod h v = 1) : False := by
  classical
  obtain ⟨a, b, c, ha1, hb1, hc1, hba, hca, hcb, hcab⟩ := exists_three_of_eight_le_card F hF8
  have hcommV : ∀ u v : QuotientV.V z, u * v = v * u :=
    (QuotientV.isMulCommutative_V h).is_comm.comm
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have hh := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at hh
  have hsqF : ∀ u : ↥F, u * u = 1 := fun u => Subtype.ext (by simpa using hsq (u : QuotientV.V z))
  have haV1 : (a : QuotientV.V z) ≠ 1 := fun hv => ha1 (Subtype.ext (by simpa using hv))
  have hbV1 : (b : QuotientV.V z) ≠ 1 := fun hv => hb1 (Subtype.ext (by simpa using hv))
  have hcV1 : (c : QuotientV.V z) ≠ 1 := fun hv => hc1 (Subtype.ext (by simpa using hv))
  have habV : (a : QuotientV.V z) ≠ (b : QuotientV.V z) :=
    fun hv => hba (Subtype.ext hv).symm
  have hacV : (a : QuotientV.V z) ≠ (c : QuotientV.V z) :=
    fun hv => hca (Subtype.ext hv).symm
  have hab1 : a * b ≠ 1 := by
    intro h1
    have h' : a * (a * b) = a * 1 := by rw [h1]
    rw [← mul_assoc, hsqF a, one_mul, mul_one] at h'
    exact hba h'
  have hbc1 : b * c ≠ 1 := by
    intro h1
    have h' : b * (b * c) = b * 1 := by rw [h1]
    rw [← mul_assoc, hsqF b, one_mul, mul_one] at h'
    exact hcb h'
  have hbca : ((b * c : ↥F) : QuotientV.V z) ≠ (a : QuotientV.V z) := by
    intro hv
    apply hcab
    apply Subtype.ext
    have h' : (b : QuotientV.V z) * ((b : QuotientV.V z) * (c : QuotientV.V z)) =
        (b : QuotientV.V z) * (a : QuotientV.V z) := by
      simpa using congrArg (fun t : QuotientV.V z => (b : QuotientV.V z) * t) hv
    rw [← mul_assoc, hsq (b : QuotientV.V z), one_mul] at h'
    change (c : QuotientV.V z) = (a : QuotientV.V z) * (b : QuotientV.V z)
    rw [h', hcommV (b : QuotientV.V z) (a : QuotientV.V z)]
  have hbcV1 : ((b * c : ↥F) : QuotientV.V z) ≠ 1 := by
    intro hv
    apply hbc1
    apply Subtype.ext
    simpa using hv
  have h1 : polarVZMod h (a : QuotientV.V z) ((b * c : ↥F) : QuotientV.V z) = 1 :=
    polarVZMod_eq_one_of_forall_qVZMod_eq_one h hq1 (a : QuotientV.V z)
      ((b * c : ↥F) : QuotientV.V z) a.2 (b * c).2 haV1 hbcV1 (fun hv => hbca hv.symm)
  have h2' : polarVZMod h (a : QuotientV.V z) ((b * c : ↥F) : QuotientV.V z) = 0 := by
    rw [show ((b * c : ↥F) : QuotientV.V z) = (b : QuotientV.V z) * (c : QuotientV.V z) from rfl,
      polarVZMod_add_right,
      polarVZMod_eq_one_of_forall_qVZMod_eq_one h hq1 (a : QuotientV.V z) (b : QuotientV.V z)
        a.2 b.2 haV1 hbV1 habV,
      polarVZMod_eq_one_of_forall_qVZMod_eq_one h hq1 (a : QuotientV.V z) (c : QuotientV.V z)
        a.2 c.2 haV1 hcV1 hacV]
    rw [← two_mul, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]
  exact one_ne_zero (h1.symm.trans h2')

theorem exists_fixed_singular_of_three_le_fixDimV (h : Tim79a.ParrottHyp z) {x : ↥(H z)}
    (hx : 3 ≤ fixDimV h x) :
    ∃ v : QuotientV.V z, v ≠ 1 ∧ conjV h x v = v ∧ qVZMod h v = 0 := by
  classical
  let F : Subgroup (QuotientV.V z) := autFixedSubgroup (conjV h x)
  have hFcard : Nat.card ↥F = 2 ^ fixDimV h x := card_fix h x
  have hF8 : 8 ≤ Nat.card ↥F := by
    rw [hFcard]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ fixDimV h x := Nat.pow_le_pow_right (by norm_num : 0 < 2) hx
  by_contra hcon
  have hq1 : ∀ v : QuotientV.V z, v ∈ F → v ≠ 1 → qVZMod h v = 1 := by
    intro v hvF hv1
    have hfixv : conjV h x v = v := (mem_autFixedSubgroup).mp hvF
    have hne : qVZMod h v ≠ 0 := by
      intro hq
      exact hcon ⟨v, hv1, hfixv, hq⟩
    have hlt : (qVZMod h v).val < 2 := ZMod.val_lt _
    rcases (show (qVZMod h v).val = 0 ∨ (qVZMod h v).val = 1 by omega) with hv | hv
    · exact absurd (ZMod.val_injective 2 (by simpa using hv)) hne
    · exact ZMod.val_injective 2 (by rw [ZMod.val_one]; exact hv)
  exact false_of_eight_le_card_of_forall_qVZMod_eq_one h hF8 hq1

end CFSG.RankThree.GF2n.Parrott
