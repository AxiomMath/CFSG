module

public import CFSG.RankThree.GF2n.Parrott.EqualityBranchModuleV
public import CFSG.RankThree.GF2n.Parrott.Lemma15Equality

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

section Counting

variable {G : Type} [Group G] [Finite G]

theorem exists_two_conj_of_ncard_mul_card_lt {K : Subgroup G} {S T : Set G} (hST : S ⊆ T)
    (hT : ∀ x ∈ T, ∀ k ∈ K, k * x * k⁻¹ ∈ T)
    (hlt : ∀ x ∈ S,
      T.ncard * Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ K) < 3 * Nat.card K) :
    ∃ x₁ x₂ : G, ∀ x ∈ S, ∃ k ∈ K, k * x * k⁻¹ = x₁ ∨ k * x * k⁻¹ = x₂ := by
  classical
  let φ : ↥K →* MulAut G := MulAut.conj.comp K.subtype
  let _ : MulAction ↥K G := MulAction.compHom G φ
  have hsmul : ∀ (k : ↥K) (g : G), k • g = (k : G) * g * (k : G)⁻¹ := fun _ _ => rfl
  have hmem : ∀ x y : G, y ∈ MulAction.orbit ↥K x ↔ ∃ k ∈ K, k * x * k⁻¹ = y := by
    intro x y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, (hsmul k x).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, hsmul _ x⟩
  have hcard : ∀ x : G, (MulAction.orbit ↥K x).ncard *
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ K) = Nat.card K := by
    intro x
    have hstab : (MulAction.stabilizer ↥K x).map K.subtype =
        Subgroup.centralizer ({x} : Set G) ⊓ K := by
      ext g
      rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [MulAction.mem_stabilizer_iff, hsmul] at hk
        refine ⟨?_, k.2⟩
        calc (k : G) * x = (k : G) * x * (k : G)⁻¹ * k := by group
          _ = x * k := by rw [hk]
      · rintro ⟨hg, hgK⟩
        refine ⟨⟨g, hgK⟩, ?_, rfl⟩
        rw [MulAction.mem_stabilizer_iff, hsmul]
        change g * x * g⁻¹ = x
        rw [hg, mul_inv_cancel_right]
    rw [← hstab, Subgroup.card_map_of_injective K.subtype_injective,
      ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  have hsub : ∀ x ∈ T, MulAction.orbit ↥K x ⊆ T := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := (hmem x y).mp hy
    exact hT x hx k hk
  have hbig : ∀ x ∈ S, T.ncard < 3 * (MulAction.orbit ↥K x).ncard := by
    intro x hx
    have h1 := hlt x hx
    rw [← hcard x, ← mul_assoc] at h1
    exact Nat.lt_of_mul_lt_mul_right h1
  have hdisj : ∀ x y : G, (∀ k ∈ K, k * y * k⁻¹ ≠ x) →
      Disjoint (MulAction.orbit ↥K x) (MulAction.orbit ↥K y) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro w hwx hwy
    obtain ⟨k, hk, rfl⟩ := (hmem x w).mp hwx
    obtain ⟨k', hk', hk'w⟩ := (hmem y _).mp hwy
    apply hxy (k⁻¹ * k') (mul_mem (inv_mem hk) hk')
    calc k⁻¹ * k' * y * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * y * k'⁻¹) * k := by group
      _ = x := by rw [hk'w]; group
  by_contra hne
  push Not at hne
  obtain ⟨a, haS, -⟩ := hne 1 1
  obtain ⟨b, hbS, hba⟩ := hne a a
  obtain ⟨c, hcS, hcab⟩ := hne a b
  have hab := hdisj a b fun k hk => (hba k hk).1
  have hac := hdisj a c fun k hk => (hcab k hk).1
  have hbc := hdisj b c fun k hk => (hcab k hk).2
  have hU : MulAction.orbit ↥K a ∪ MulAction.orbit ↥K b ∪ MulAction.orbit ↥K c ⊆ T :=
    Set.union_subset (Set.union_subset (hsub a (hST haS)) (hsub b (hST hbS)))
      (hsub c (hST hcS))
  have hle := Set.ncard_le_ncard hU
  rw [Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hac, hbc⟩),
    Set.ncard_union_eq hab] at hle
  have ha := hbig a haS
  have hb := hbig b hbS
  have hc := hbig c hcS
  omega

end Counting

section Involutions

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_conj_eq_mul_z_of_qH_eq_uvt (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {y : G} (hyH : y ∈ H z)
    (hqy : qH D ⟨y, hyH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩)
    (hyy : y * y = 1) :
    ∃ j ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      j * j = z ∧ y * j * y⁻¹ = j * z := by
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσdef
  set Q : Subgroup G := CJ z (σ : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆
  have hzz : z * z = 1 := sq_eq_one_of_mem_zpowers h (Subgroup.mem_zpowers z)
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hcomJ : ∀ r₁ ∈ J z, ∀ r₂ ∈ J z, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers z := by
    intro r₁ hr₁ r₂ hr₂
    rw [← h.2.2.1]
    have := Subgroup.commutator_mem_commutator hr₁ hr₂
    rwa [commutatorElement_def] at this
  have hzQ : z ∈ Q := by
    have hzA : z ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      rw [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
      exact Subgroup.mem_zpowers z
    exact ⟨mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (hcent z (Subgroup.mem_zpowers z) _ σ.2).symm, z_mem_J h⟩, hzA.2⟩
  have hσ3 : orderOf σ = 3 := orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hqσ : qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
    rw [hσdef, map_mul, map_inv, qH_sigma1Nine, hq₂]
  have huvtσ : ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) *
      qH D σ =
      qH D σ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) := by
    rw [hqσ]; exact Subtype.ext uvt_mul_sigma1_mul_sigma2_inv
  obtain ⟨s, hsq, hsσ⟩ := exists_lift_centralizer D hσ3 huvtσ
  have hsσ' : (s : G) ∈ Subgroup.centralizer ({(σ : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val hsσ
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at this
  have hj₀ : (s : G)⁻¹ * y ∈ J z := by
    have h1 : qH D (s⁻¹ * ⟨y, hyH⟩) = 1 := by rw [map_mul, map_inv, hsq, hqy, inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  have hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q := by
    intro q hq
    have hqJ : q ∈ J z := (mem_CJ.mp hq.1).2
    have hc := hcomJ _ hj₀ q hqJ
    have e : y * q * y⁻¹ = (s : G) * ((((s : G)⁻¹ * y) * q * ((s : G)⁻¹ * y)⁻¹ * q⁻¹) * q) *
        (s : G)⁻¹ := by group
    rw [e]
    exact conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq s.2 hsσ'
      (Q.mul_mem (Subgroup.zpowers_le_of_mem hzQ hc) hq)
  obtain ⟨k, hk, hkz⟩ :=
    exists_conj_mul_inv_not_mem_zpowers (z := z) D h hσ₂ hq₂ hcomm hEq hyH hqy
  obtain ⟨j, hj⟩ : ∃ j, y * k * y⁻¹ * k⁻¹ = j := ⟨_, rfl⟩
  have hjQ : j ∈ Q := hj ▸ Q.mul_mem (hyQ k hk) (Q.inv_mem hk)
  have hjz : j ∉ Subgroup.zpowers z := hj ▸ hkz
  have hjj : j * j = z :=
    mul_self_eq_of_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq hjQ hjz
  refine ⟨j, hjQ, hjj, ?_⟩
  have h1 : y * j * y⁻¹ = j⁻¹ := by
    rw [← hj]; exact conj_commutator_eq_inv_of_mul_self_eq_one hyy
  rw [h1]
  calc j⁻¹ = j⁻¹ * (z * z) := by rw [hzz, mul_one]
    _ = j⁻¹ * (j * j) * z := by rw [hjj]; group
    _ = j * z := by group

theorem card_CJ_le_of_qH_eq_uvt (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {y : G} (hyH : y ∈ H z)
    (hqy : qH D ⟨y, hyH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩)
    (hyy : y * y = 1) (hyE : IsElemAbelian 2 (CJ z y)) :
    Nat.card (CJ z y) ≤ 32 := by
  classical
  set J₀ : Subgroup G := CJ z (sigma1Nine (z := z) D : G)
  set Z : Subgroup G := centerIn (J z)
  set C : Subgroup G := CJ z y
  have hz2 : orderOf z = 2 := h.1
  have hz1 : z ≠ 1 := by
    intro hz; rw [hz, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hzz : z * z = 1 := sq_eq_one_of_mem_zpowers h (Subgroup.mem_zpowers z)
  have hzZ : z ∈ Z := ⟨z_mem_J h, z_centralizes_J h⟩
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hCmem : ∀ g ∈ J z, y * g * y⁻¹ * g⁻¹ = 1 → g ∈ C := by
    intro g hgJ hg
    refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hgJ⟩
    have h1 : y * g * y⁻¹ = g := mul_inv_eq_one.mp hg
    calc g * y = y * g * y⁻¹ * y := by rw [h1]
      _ = y * g := by group
  have hδC : ∀ g ∈ C, y * g * y⁻¹ * g⁻¹ = 1 := by
    intro g hg
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hg).1]
    group
  have hδmul : ∀ a b : G, y * (a * b) * y⁻¹ * (a * b)⁻¹ =
      (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := fun a b => by group
  have hδinv : ∀ a : G, y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a :=
    fun a => by group
  obtain ⟨j, hjQ, hjj, hyj⟩ :=
    exists_conj_eq_mul_z_of_qH_eq_uvt D h hσ₂ hq₂ hcomm hEq hyH hqy hyy
  have hjJ : j ∈ J z := (mem_CJ.mp hjQ.1).2
  have hδj : y * j * y⁻¹ * j⁻¹ = z := by
    rw [hyj, hcent z (Subgroup.mem_zpowers z) j (J_le_H hjJ)]; group
  let C' : Subgroup G :=
    { carrier := {g | g ∈ J z ∧ y * g * y⁻¹ * g⁻¹ ∈ Subgroup.zpowers z}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [hδmul, hcent _ hb.2 a (J_le_H ha.1), mul_inv_cancel_right]
        exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [hδinv, hcent _ (inv_mem ha.2) a⁻¹ (J_le_H (inv_mem ha.1)), inv_mul_cancel_right]
        exact inv_mem ha.2⟩ }
  have hmemC' : ∀ g, g ∈ C' ↔ g ∈ J z ∧ y * g * y⁻¹ * g⁻¹ ∈ Subgroup.zpowers z :=
    fun _ => Iff.rfl
  set Fix : Subgroup (QuotientV.V z) := autFixedSubgroup (conjV h ⟨y, hyH⟩)
  set L : Subgroup G := (Fix.comap (QuotientV.pi z)).map (J z).subtype with hL
  have hmemL : ∀ g : G, g ∈ L ↔ g ∈ J z ∧ y * g * y⁻¹ * g⁻¹ ∈ Z := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, (conjV_pi_eq_iff h ⟨y, hyH⟩ g').mp
        (mem_autFixedSubgroup.mp (Subgroup.mem_comap.mp hg'))⟩
    · rintro ⟨hgJ, hgZ⟩
      exact ⟨⟨g, hgJ⟩, Subgroup.mem_comap.mpr (mem_autFixedSubgroup.mpr
        ((conjV_pi_eq_iff h ⟨y, hyH⟩ ⟨g, hgJ⟩).mpr hgZ)), rfl⟩
  have hLcard : Nat.card L = 4 * Nat.card Fix := by
    rw [hL, Subgroup.card_map_of_injective (J z).subtype_injective]
    have h1 := Subgroup.card_mul_index (Fix.comap (QuotientV.pi z))
    have h2 := Subgroup.card_mul_index Fix
    rw [Subgroup.index_comap_of_surjective (hf := QuotientV.pi_surjective z), card_J h] at h1
    rw [QuotientV.card_V h] at h2
    have hi : 0 < Fix.index :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at h2; norm_num at h2
    exact Nat.eq_of_mul_eq_mul_right hi (h1.trans (by rw [mul_assoc, h2]; norm_num))
  have hCC' : C ≤ C' := fun g hg =>
    (hmemC' g).mpr ⟨(mem_CJ.mp hg).2, by rw [hδC g hg]; exact one_mem _⟩
  have hC'L : C' ≤ L := fun g hg =>
    (hmemL g).mpr ⟨((hmemC' g).mp hg).1, Subgroup.zpowers_le_of_mem hzZ ((hmemC' g).mp hg).2⟩
  have hjC' : j ∈ C' := (hmemC' j).mpr ⟨hjJ, by rw [hδj]; exact Subgroup.mem_zpowers z⟩
  have hjC : j ∉ C := fun hm => hz1 (hδj.symm.trans (hδC j hm))
  have hhalf : ∀ {A B : Subgroup G}, A ≤ B → ∀ b ∈ B, b ∉ A → 2 * Nat.card A ≤ Nat.card B := by
    intro A B hAB b hb hbA
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAB
    have hpos : 0 < Nat.card A := Nat.card_pos
    have hlt : Nat.card A < Nat.card B := by
      by_contra hge
      push Not at hge
      exact hbA (by rw [Subgroup.eq_of_le_of_card_ge hAB hge]; exact hb)
    rw [hm] at hlt ⊢
    have hm2 : 2 ≤ m := by
      by_contra hm2
      push Not at hm2
      interval_cases m <;> omega
    nlinarith
  have hCC'card : 2 * Nat.card C ≤ Nat.card C' := hhalf hCC' j hjC' hjC
  have hC'Lcard : Nat.card C' ≤ Nat.card L := Subgroup.card_le_of_le hC'L
  obtain ⟨B, hBH, hB5, hBuv⟩ := exists_order_five_subgroup_conj_mem_uvJ D h
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hall
    push Not at hall
    rw [(Subgroup.eq_bot_iff_forall B).mpr hall, Subgroup.card_bot] at hB5
    norm_num at hB5
  have hbord : orderOf b = 5 := by
    have hdvd : orderOf b ∣ 5 := hB5 ▸ Subgroup.orderOf_dvd_natCard B hbB
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hb1
    · exact h1
  have hbH5 : orderOf (⟨b, hBH hbB⟩ : ↥(H z)) = 5 := by
    rw [← Subgroup.orderOf_coe]; exact hbord
  have hbuv : qH D ⟨b, hBH hbB⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) =
      ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) * qH D ⟨b, hBH hbB⟩ := by
    obtain ⟨j', hj'J, hj'⟩ := hBuv b hbB
    have e : (⟨b, hBH hbB⟩ : ↥(H z)) * (uH D * vH D) * (⟨b, hBH hbB⟩ : ↥(H z))⁻¹ =
        uH D * vH D * ⟨j', J_le_H hj'J⟩ := Subtype.ext hj'
    have hj'1 : qH D ⟨j', J_le_H hj'J⟩ = 1 :=
      (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj'J)
    have e2 := congrArg (qH D) e
    simp only [map_mul, map_inv, hj'1, mul_one, qH_uH, qH_vH] at e2
    calc qH D ⟨b, hBH hbB⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩)
        = qH D ⟨b, hBH hbB⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) *
            (qH D ⟨b, hBH hbB⟩)⁻¹ * qH D ⟨b, hBH hbB⟩ := by group
      _ = ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩) * qH D ⟨b, hBH hbB⟩ := by
          rw [e2]
  have hW8 : Nat.card ↥(Wsub h (sigma1Nine D) ⊓ Fix) = 8 :=
    card_Wsub_inf_autFixedSubgroup_conjV_eq_eight D h hσ₂ hq₂ hcomm hEq hbH5 hbuv hqy
  have hFix8 : Nat.card ↥Fix = Nat.card ↥(Fsub (z := z) (sigma1Nine D) ⊓ Fix) * 8 := by
    rw [← hW8]; exact card_autFixedSubgroup_conjV_eq_mul D h hσ₂ hq₂ hcomm hEq ⟨y, hyH⟩
  have hfdvd : Nat.card ↥(Fsub (z := z) (sigma1Nine D) ⊓ Fix) ∣ 4 := by
    rw [← card_Fsub_sigma1Nine (z := z) (D := D) h]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨f, hf⟩ : ∃ f, Nat.card ↥(Fsub (z := z) (sigma1Nine D) ⊓ Fix) = f := ⟨_, rfl⟩
  rw [hf] at hfdvd hFix8
  have hf' : f ≤ 2 ∨ f = 4 := by
    have hf4 : f ≤ 4 := Nat.le_of_dvd (by norm_num) hfdvd
    revert hfdvd
    interval_cases f <;> decide
  rcases hf' with hf2 | hf4
  ·
    have hL64 : Nat.card L ≤ 64 := by rw [hLcard, hFix8]; omega
    omega
  ·
    have hFle : Fsub (z := z) (sigma1Nine D) ≤ Fix := by
      have heq : Fsub (z := z) (sigma1Nine D) ⊓ Fix = Fsub (z := z) (sigma1Nine D) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [card_Fsub_sigma1Nine (z := z) (D := D) h, hf, hf4])
      rw [← heq]; exact inf_le_right
    have hJ₀L : ∀ e ∈ J₀, e ∈ L := by
      intro e he
      obtain ⟨hes, heJ⟩ := mem_CJ.mp he
      have hmemF : QuotientV.pi z ⟨e, heJ⟩ ∈ Fsub (z := z) (sigma1Nine D) :=
        Subgroup.mem_map_of_mem (QuotientV.pi z)
          (mem_centralizerJ_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hes))
      exact ⟨⟨e, heJ⟩, Subgroup.mem_comap.mpr (hFle hmemF), rfl⟩
    by_cases hJ₀C' : ∀ e ∈ J₀, e ∈ C'
    · exfalso
      obtain ⟨a, ha, a', ha', hne⟩ := exists_not_commute_CJ_sigma1Nine (z := z) D h
      have hjc : ∀ e ∈ J₀, Commute j e := fun e he =>
        (show Commute e j from
          commute_of_mem_CJ_sigma1Nine_of_mem_commutator (z := z) D h he hjQ.2).symm
      have hlift : ∀ e ∈ J₀, ∃ q ∈ Subgroup.zpowers j, e * q ∈ C := by
        intro e he
        have heJ : e ∈ J z := (mem_CJ.mp he).2
        rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp
            ((hmemC' e).mp (hJ₀C' e he)).2 with hd | hd
        · exact ⟨1, one_mem _, by rw [mul_one]; exact hCmem e heJ hd⟩
        · refine ⟨j, Subgroup.mem_zpowers j, hCmem _ (mul_mem heJ hjJ) ?_⟩
          rw [hδmul, hd, hδj, hcent z (Subgroup.mem_zpowers z) e (J_le_H heJ),
            mul_inv_cancel_right, hzz]
      obtain ⟨q, hq, hqC⟩ := hlift a ha
      obtain ⟨q', hq', hq'C⟩ := hlift a' ha'
      have hqa : ∀ w ∈ Subgroup.zpowers j, ∀ e ∈ J₀, w * e = e * w := by
        rintro w ⟨n, rfl⟩ e he
        exact ((hjc e he).zpow_left n).eq
      have hqq : q * q' = q' * q := by
        obtain ⟨i, rfl⟩ := hq
        obtain ⟨l, rfl⟩ := hq'
        exact (Commute.zpow_zpow_self j i l).eq
      have hCab : a * q * (a' * q') = a' * q' * (a * q) :=
        (commute_of_mem_of_isMulCommutative hyE.1 hqC hq'C).eq
      apply hne
      have e1 : a * q * (a' * q') = a * a' * (q * q') := by
        calc a * q * (a' * q') = a * (q * a') * q' := by group
          _ = a * (a' * q) * q' := by rw [hqa q hq a' ha']
          _ = a * a' * (q * q') := by group
      have e2 : a' * q' * (a * q) = a' * a * (q * q') := by
        calc a' * q' * (a * q) = a' * (q' * a) * q := by group
          _ = a' * (a * q') * q := by rw [hqa q' hq' a ha]
          _ = a' * a * (q' * q) := by group
          _ = a' * a * (q * q') := by rw [hqq]
      exact mul_right_cancel (e1.symm.trans (hCab.trans e2))
    · push Not at hJ₀C'
      obtain ⟨e₁, he₁, he₁C'⟩ := hJ₀C'
      have hC'L2 : 2 * Nat.card C' ≤ Nat.card L := hhalf hC'L e₁ (hJ₀L e₁ he₁) he₁C'
      rw [hLcard, hFix8, hf4] at hC'L2
      omega

theorem ncard_le_two_mul_card_CJ_of_qH_eq_uvt (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {y₀ : G}
    (hy₀H : y₀ ∈ H z)
    (hqy₀ : qH D ⟨y₀, hy₀H⟩ =
      (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩)
    (hy₀y₀ : y₀ * y₀ = 1) :
    {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2}.ncard ≤
      2 * Nat.card (CJ z y₀) := by
  classical
  set C : Subgroup G := CJ z y₀
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  obtain ⟨j, hjQ, -, hyj⟩ :=
    exists_conj_eq_mul_z_of_qH_eq_uvt D h hσ₂ hq₂ hcomm hEq hy₀H hqy₀ hy₀y₀
  have hjJ : j ∈ J z := (mem_CJ.mp hjQ.1).2
  have hy₀i : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right hy₀y₀
  have hy₀J : ((uH D * vH D * tH D : ↥(H z)) : G)⁻¹ * y₀ ∈ J z := by
    have h1 : qH D ((uH D * vH D * tH D)⁻¹ * ⟨y₀, hy₀H⟩) = 1 := by
      rw [map_mul, map_inv, hqy₀, map_mul, map_mul, qH_uH, qH_vH, qH_tH, inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  have hsub : {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2} ⊆
      (fun c => y₀ * c) '' (C : Set G) ∪ (fun c => y₀ * j * c) '' (C : Set G) := by
    rintro x ⟨⟨j₁, hj₁J, hxj₁⟩, hx2⟩
    obtain ⟨g, hgJ, hg⟩ : ∃ g ∈ J z, x = y₀ * g :=
      ⟨(((uH D * vH D * tH D : ↥(H z)) : G)⁻¹ * y₀)⁻¹ * j₁, mul_mem (inv_mem hy₀J) hj₁J,
        by rw [hxj₁]; group⟩
    rw [hg] at hx2 ⊢
    have hxx : y₀ * g * (y₀ * g) = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one _
    have hyg : y₀ * g * y₀⁻¹ = g⁻¹ := by
      rw [hy₀i]; exact eq_inv_of_mul_eq_one_left (by rw [← hxx]; group)
    have hδ : y₀ * g * y₀⁻¹ * g⁻¹ ∈ Subgroup.zpowers z := by
      rw [hyg, ← mul_inv_rev]; exact inv_mem (sq_mem_zpowers_z h hgJ)
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hδ with hd | hd
    · refine Or.inl ⟨g, mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hgJ⟩, rfl⟩
      have h1 : y₀ * g * y₀⁻¹ = g := mul_inv_eq_one.mp hd
      calc g * y₀ = y₀ * g * y₀⁻¹ * y₀ := by rw [h1]
        _ = y₀ * g := by group
    · refine Or.inr ⟨j⁻¹ * g, mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        mul_mem (inv_mem hjJ) hgJ⟩, show y₀ * j * (j⁻¹ * g) = y₀ * g by group⟩
      have hyg' : y₀ * g * y₀⁻¹ = z * g := by rw [← hd]; group
      have hyj' : y₀ * j⁻¹ * y₀⁻¹ = (j * z)⁻¹ := by rw [← hyj]; group
      have hzj : z * j = j * z := (hcent z (Subgroup.mem_zpowers z) j (J_le_H hjJ)).symm
      calc j⁻¹ * g * y₀ = (j * z)⁻¹ * (z * g) * y₀ := by rw [← hzj]; group
        _ = (y₀ * j⁻¹ * y₀⁻¹) * (y₀ * g * y₀⁻¹) * y₀ := by rw [hyj', hyg']
        _ = y₀ * (j⁻¹ * g) := by group
  calc {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2}.ncard
      ≤ ((fun c => y₀ * c) '' (C : Set G) ∪ (fun c => y₀ * j * c) '' (C : Set G)).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ ((fun c => y₀ * c) '' (C : Set G)).ncard +
        ((fun c => y₀ * j * c) '' (C : Set G)).ncard := Set.ncard_union_le _ _
    _ ≤ (C : Set G).ncard + (C : Set G).ncard :=
        add_le_add (Set.ncard_image_le (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
    _ = 2 * Nat.card C := by rw [two_mul, ← Nat.card_coe_set_eq]; rfl

theorem exists_two_J_classes_of_mem_uvtJ (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    ∃ x₁ x₂ : G, ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      IsElemAbelian 2 (CJ z x) → ∃ j ∈ J z, j * x * j⁻¹ = x₁ ∨ j * x * j⁻¹ = x₂ := by
  classical
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hmemH : ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → x ∈ H z := by
    rintro x ⟨j, hjJ, rfl⟩
    exact mul_mem (uH D * vH D * tH D).2 (J_le_H hjJ)
  have hqH : ∀ x (hx : cosetJ (z := z) (uH D * vH D * tH D) x), qH D ⟨x, hmemH x hx⟩ =
      (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩ := by
    intro x hx
    obtain ⟨j, hjJ, hxj⟩ := hx
    have e : (⟨x, hmemH x ⟨j, hjJ, hxj⟩⟩ : ↥(H z)) = uH D * vH D * tH D * ⟨j, J_le_H hjJ⟩ :=
      Subtype.ext hxj
    have hj1 : qH D ⟨j, J_le_H hjJ⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hjJ)
    rw [e, map_mul, hj1, mul_one, map_mul, map_mul, qH_uH, qH_vH, qH_tH]
  have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
    rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  by_cases hne : ∃ y₀ : G, cosetJ (z := z) (uH D * vH D * tH D) y₀ ∧ orderOf y₀ = 2 ∧
      IsElemAbelian 2 (CJ z y₀)
  · obtain ⟨y₀, hy₀c, hy₀2, hy₀E⟩ := hne
    have hT64 : {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2}.ncard ≤ 64 := by
      have h1 := ncard_le_two_mul_card_CJ_of_qH_eq_uvt D h hσ₂ hq₂ hcomm hEq (hmemH y₀ hy₀c)
        (hqH y₀ hy₀c) (hsq y₀ hy₀2)
      have h2 := card_CJ_le_of_qH_eq_uvt D h hσ₂ hq₂ hcomm hEq (hmemH y₀ hy₀c) (hqH y₀ hy₀c)
        (hsq y₀ hy₀2) hy₀E
      omega
    have hTcl : ∀ x ∈ {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2},
        ∀ k ∈ J z,
          k * x * k⁻¹ ∈ {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2} := by
      rintro x ⟨⟨j, hjJ, hxj⟩, hx2⟩ k hk
      have hk' : ((uH D * vH D * tH D : ↥(H z)) : G)⁻¹ * k *
          ((uH D * vH D * tH D : ↥(H z)) : G) ∈ J z := by
        have := (Subgroup.mem_normalizer_iff.mp (hHN (inv_mem (uH D * vH D * tH D).2)) k).mp hk
        rwa [inv_inv] at this
      have hc : cosetJ (z := z) (uH D * vH D * tH D) (k * x * k⁻¹) :=
        ⟨_, mul_mem (mul_mem hk' hjJ) (inv_mem hk), by rw [hxj]; group⟩
      have hsc : SemiconjBy k x (k * x * k⁻¹) := by
        unfold SemiconjBy; group
      exact ⟨hc, by rw [← SemiconjBy.orderOf_eq k hsc]; exact hx2⟩
    obtain ⟨x₁, x₂, hx⟩ := exists_two_conj_of_ncard_mul_card_lt (K := J z)
      (S := {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2 ∧
        IsElemAbelian 2 (CJ z x)})
      (T := {x : G | cosetJ (z := z) (uH D * vH D * tH D) x ∧ orderOf x = 2})
      (fun x hx => ⟨hx.1, hx.2.1⟩) hTcl (fun x hx => by
        have hCJ : Subgroup.centralizer ({x} : Set G) ⊓ J z = CJ z x := by
          ext g; rw [Subgroup.mem_inf, mem_CJ]
        rw [hCJ, card_J h]
        have h2 := card_CJ_le_of_qH_eq_uvt D h hσ₂ hq₂ hcomm hEq (hmemH x hx.1) (hqH x hx.1)
          (hsq x hx.2.1) hx.2.2
        calc _ ≤ 64 * 32 := Nat.mul_le_mul hT64 h2
          _ < 3 * 2 ^ 10 := by norm_num)
    exact ⟨x₁, x₂, fun x hxc hx2 hxE => hx x ⟨hxc, hx2, hxE⟩⟩
  · push Not at hne
    exact ⟨1, 1, fun x hxc hx2 hxE => absurd hxE (hne x hxc hx2)⟩

end Involutions

end CFSG.RankThree.GF2n.Parrott
