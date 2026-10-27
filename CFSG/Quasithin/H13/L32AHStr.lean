module

public import CFSG.Quasithin.H13.L32A71
public import CFSG.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L32A

theorem perm5_sign_of_pow15 : ∀ x : Equiv.Perm (Fin 5), x ^ 15 = 1 →
    Equiv.Perm.sign x = 1 := by
  decide +kernel

theorem perm5_card_pow15 :
    (Finset.univ.filter fun x : Equiv.Perm (Fin 5) => x ^ 15 = 1).card = 45 := by
  decide +kernel

theorem perm5_card_comm : ∀ c : Equiv.Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (Finset.univ.filter fun d : Equiv.Perm (Fin 5) => d * c = c * d).card = 6 := by
  decide +kernel

theorem perm5_nodup : ∀ n c : Equiv.Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    Equiv.Perm.sign n = -1 → n * c ≠ c * n →
    [1, n, c * n * c⁻¹, c * c * n * c⁻¹ * c⁻¹, n * (c * n * c⁻¹)].Nodup := by
  decide +kernel

theorem perm5_card_centralizer {c : Equiv.Perm (Fin 5)} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 5)))) = 6 := by
  have e : ((Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 5)))) : Set (Equiv.Perm (Fin 5))) =
      ↑(Finset.univ.filter fun d : Equiv.Perm (Fin 5) => d * c = c * d) := by
    ext d
    simp [Subgroup.mem_centralizer_singleton_iff]
  show Set.ncard _ = 6
  rw [e, Set.ncard_coe_finset, perm5_card_comm c hc3 hc1]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_iff' {H : Subgroup G} {x : ↥H} :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.Open.pCore 2 ↥H :=
  Subgroup.mem_map_iff_mem H.subtype_injective

omit [Finite G] in
theorem pCoreOf_subgroupOf (H : Subgroup G) :
    (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 ↥H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

section Phi

variable {H : Subgroup G} {φ : ↥H →* Equiv.Perm (Fin 5)}

omit [Finite G] in
theorem sign_phi_of_pow (x : ↥H) {m : ℕ} (hm : Odd m) (hx : x ^ m = 1) :
    Equiv.Perm.sign (φ x) = 1 := by
  have h1 : Equiv.Perm.sign (φ x) ^ m = 1 := by rw [← map_pow, ← map_pow, hx, map_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (φ x)) with h | h
  · exact h
  · rw [h, hm.neg_one_pow] at h1
    exact absurd h1 (by decide)

omit [Finite G] in
theorem sign_phi_kz {k : G} (hk : k ∈ oTwoUpper H) :
    Equiv.Perm.sign (φ ⟨k, oTwoUpper_le H hk⟩) = 1 := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    refine sign_phi_of_pow _ hx.2 (Subtype.ext ?_)
    simp [pow_orderOf_eq_one]
  | one =>
    show Equiv.Perm.sign (φ 1) = 1
    rw [map_one, map_one]
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, oTwoUpper_le H (mul_mem ha hb)⟩ : ↥H) =
        ⟨a, oTwoUpper_le H ha⟩ * ⟨b, oTwoUpper_le H hb⟩ := rfl
    rw [e, map_mul, map_mul, iha, ihb, mul_one]
  | inv a ha iha =>
    have e : (⟨a⁻¹, oTwoUpper_le H (inv_mem ha)⟩ : ↥H) = (⟨a, oTwoUpper_le H ha⟩)⁻¹ := rfl
    rw [e, map_inv, map_inv, iha, inv_one]

variable (hs : Function.Surjective φ) (hk : φ.ker = CFSG.Open.pCore 2 ↥H)
include hs hk

theorem phi_map_kz : ((oTwoUpper H).subgroupOf H).map φ = alternatingGroup (Fin 5) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ((oTwoUpper H).subgroupOf H).map φ ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    exact sign_phi_kz (Subgroup.mem_subgroupOf.mp hx)
  have hsub : ∀ y : Equiv.Perm (Fin 5), y ^ 15 = 1 → y ∈ ((oTwoUpper H).subgroupOf H).map φ := by
    intro y hy
    obtain ⟨x, rfl⟩ := hs y
    have hx15 : ((x ^ 15 : ↥H) : G) ∈ pCoreOf 2 H := by
      rw [mem_pCoreOf_iff', ← hk, MonoidHom.mem_ker, map_pow, hy]
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨_, hx15⟩
    have hxn : x ^ (15 * 2 ^ n) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hn
      simpa [pow_mul] using this
    obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 15)) (by norm_num : 1 < 15)
    refine ⟨x ^ (2 ^ n * j), Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · refine mem_oTwoUpper_of_odd (x ^ (2 ^ n * j)).2 ?_
      have h1 : ((x ^ (2 ^ n * j) : ↥H) : G) ^ 15 = 1 := by
        rw [← Subgroup.coe_pow, ← pow_mul, show 2 ^ n * j * 15 = 15 * 2 ^ n * j by ring, pow_mul,
          hxn, one_pow]
        rfl
      exact Odd.of_dvd_nat (by decide : Odd 15) (orderOf_dvd_of_pow_eq_one h1)
    · rw [map_pow, ← Nat.mod_add_div (2 ^ n * j) 15, hj, pow_add, pow_mul, hy, one_pow, mul_one,
        pow_one]
  have hcard : 45 ≤ Nat.card ↥(((oTwoUpper H).subgroupOf H).map φ) := by
    have h1 : ((Finset.univ.filter fun x : Equiv.Perm (Fin 5) => x ^ 15 = 1 :
        Finset (Equiv.Perm (Fin 5))) : Set (Equiv.Perm (Fin 5))) ⊆
        (((oTwoUpper H).subgroupOf H).map φ : Set (Equiv.Perm (Fin 5))) := by
      intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
      exact hsub y hy
    have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
    rw [Set.ncard_coe_finset, perm5_card_pow15] at h2
    exact h2
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hA5] at hdvd
  have h60 := Nat.le_of_dvd (by norm_num) hdvd
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hA5]
  set c := Nat.card ↥(((oTwoUpper H).subgroupOf H).map φ) with hc
  interval_cases c <;> first | exact le_rfl | (norm_num at hdvd)

theorem mem_kz_sup_of_sign {x : ↥H} (hx : Equiv.Perm.sign (φ x) = 1) :
    (x : G) ∈ oTwoUpper H ⊔ pCoreOf 2 H := by
  have hxA : φ x ∈ ((oTwoUpper H).subgroupOf H).map φ := by
    rw [phi_map_kz hs hk, Equiv.Perm.mem_alternatingGroup]
    exact hx
  obtain ⟨y, hy, hyx⟩ := hxA
  have hq : y⁻¹ * x ∈ CFSG.Open.pCore 2 ↥H := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have e : (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) := by simp
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hy))
    (Subgroup.mem_sup_right (mem_pCoreOf_iff'.mpr hq))

omit [Finite G] hs in
theorem card_map_phi {R : Subgroup G} (hRH : R ≤ H) :
    Nat.card ↥((R.subgroupOf H).map φ) = (pCoreOf 2 H).relIndex R := by
  rw [← Subgroup.relIndex_ker, hk, ← pCoreOf_subgroupOf, Subgroup.relIndex_subgroupOf hRH]

omit [Finite G] in
theorem relIndex_phi_sylow {T : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 ↥T)
    (hTi : ¬ 2 ∣ (T.subgroupOf H).index) : (pCoreOf 2 H).relIndex T = 8 := by
  rw [← card_map_phi hk hTH]
  have h2 : IsPGroup 2 ↥((T.subgroupOf H).map φ) :=
    (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map φ
  have h3 : ¬ 2 ∣ ((T.subgroupOf H).map φ).index := fun hd =>
    hTi (hd.trans (Subgroup.index_map_dvd _ hs))
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have h4 := ((T.subgroupOf H).map φ).card_mul_index
  rw [h120] at h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := h2.exists_card_eq
  rw [ha] at h4 ⊢
  have ha7 : a < 7 := by
    by_contra hlt
    have h5 : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : 0 < ((T.subgroupOf H).map φ).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    nlinarith
  interval_cases a <;> omega

omit [Finite G] hs in
theorem sign_phi_of_card_four {R : Subgroup G} (hRH : R ≤ H)
    (hcard : (pCoreOf 2 H).relIndex R = 4) {x : G} (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hx1 : x ∉ pCoreOf 2 H) (hxR : x ∈ Subgroup.normalizer (R : Set G)) {r : G} (hr : r ∈ R) :
    Equiv.Perm.sign (φ ⟨r, hRH hr⟩) = 1 := by
  set N := (R.subgroupOf H).map φ with hN
  have hN4 : Nat.card ↥N = 4 := by rw [card_map_phi hk hRH, hcard]
  set c := φ ⟨x, hxH⟩ with hcdef
  have hc3 : c ^ 3 = 1 := by
    rw [hcdef, ← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hc1 : c ≠ 1 := by
    intro h1
    apply hx1
    have : (⟨x, hxH⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by rw [← hk, MonoidHom.mem_ker]; exact h1
    exact mem_pCoreOf_iff'.mpr this
  have hcN : ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
    have h1 : x * (y : G) * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR _).mp hy'
    refine ⟨⟨x * (y : G) * x⁻¹, hRH h1⟩, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    have e : (⟨x * (y : G) * x⁻¹, hRH h1⟩ : ↥H) = ⟨x, hxH⟩ * y * ⟨x, hxH⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hodd : ∀ n ∈ N, Equiv.Perm.sign n = -1 → n * c = c * n := by
    intro n hn hsn
    by_contra hnc
    have hnd := perm5_nodup n c hc3 hc1 hsn hnc
    have hm : c * n * c⁻¹ ∈ N := hcN n hn
    have hm' : c * c * n * c⁻¹ * c⁻¹ ∈ N := by
      have := hcN _ hm
      rwa [show c * (c * n * c⁻¹) * c⁻¹ = c * c * n * c⁻¹ * c⁻¹ by group] at this
    have hsub : (↑([1, n, c * n * c⁻¹, c * c * n * c⁻¹ * c⁻¹, n * (c * n * c⁻¹)].toFinset) :
        Set (Equiv.Perm (Fin 5))) ⊆ (N : Set (Equiv.Perm (Fin 5))) := by
      intro y hy
      simp only [List.coe_toFinset, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_ofPred_eq] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact one_mem N
      · exact hn
      · exact hm
      · exact hm'
      · exact mul_mem hn hm
    have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h5
    have : (N : Set (Equiv.Perm (Fin 5))).ncard = 4 := hN4
    simp only [List.length_cons, List.length_nil] at h5
    omega
  by_contra hr1
  have hsr : Equiv.Perm.sign (φ ⟨r, hRH hr⟩) = -1 :=
    (Int.units_eq_one_or _).resolve_left hr1
  have hrN : φ ⟨r, hRH hr⟩ ∈ N := ⟨⟨r, hRH hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hcomm : N ≤ Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 5))) := by
    intro k hkN
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Int.units_eq_one_or (Equiv.Perm.sign k) with hk1 | hk1
    · have h1 : Equiv.Perm.sign (φ ⟨r, hRH hr⟩ * k) = -1 := by
        rw [map_mul, hsr, hk1, mul_one]
      have h2 := hodd _ (mul_mem hrN hkN) h1
      have h3 := hodd _ hrN hsr
      calc k * c = (φ ⟨r, hRH hr⟩)⁻¹ * ((φ ⟨r, hRH hr⟩ * k) * c) := by group
        _ = (φ ⟨r, hRH hr⟩)⁻¹ * (c * (φ ⟨r, hRH hr⟩ * k)) := by rw [h2]
        _ = (φ ⟨r, hRH hr⟩)⁻¹ * (c * φ ⟨r, hRH hr⟩) * k := by group
        _ = (φ ⟨r, hRH hr⟩)⁻¹ * (φ ⟨r, hRH hr⟩ * c) * k := by rw [h3]
        _ = c * k := by group
    · exact hodd k hkN hk1
  have hdvd := Subgroup.card_dvd_of_le hcomm
  rw [hN4, perm5_card_centralizer hc3 hc1] at hdvd
  norm_num at hdvd

end Phi

variable {T L V : Subgroup G}

theorem exists_phi (h : Hyp147 G T L V) (h63 : Thm14_7_63) :
    ∃ φ : ↥(hz T V) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = CFSG.Open.pCore 2 ↥(hz T V) :=
  (h63 G T L V h).2.2.2.2.1

theorem R1_le_kz_sup (S : Setting147 G T L V (hz T V)) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h63 : Thm14_7_63) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ kz T V ⊔ pCoreOf 2 (hz T V) ∧
      (pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = 4 := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := S.hyp.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  have S14 := S.hyp.set14 h1222 h1332 h1334 hV2
  obtain ⟨φ, hs, hk⟩ := exists_phi S.hyp h63
  have hT := S.hyp.fsu.sylow
  have hTH : T ≤ hz T V := le_sup_right.trans hF.L₁T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans hF.L₁T_le_H
  have hTi : ¬ 2 ∣ (T.subgroupOf (hz T V)).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  have hQHT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le S.hyp hTH
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le S.hyp le_sup_right
  have hQHR : pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hQHT.trans le_sup_right)
      ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have h8 := relIndex_phi_sylow hs hk hTH hT.1 hTi
  have h2 := S14.index2_eq
  have h4 : (pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = 4 := by
    have := Subgroup.relIndex_mul_relIndex _ _ _ hQHR hR1T
    rw [h2, h8] at this
    omega
  refine ⟨fun r hr => ?_, h4⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x, hxL0, hx3, hxz, hxa, -⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  have hxL : x ∈ L₁Of L (fsuV1 T V) :=
    Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1 hz0 hz1 hxz⟩, 3, by decide, hx3⟩
  have hxH : x ∈ hz T V := hL1H hxL
  have hx1 : x ∉ pCoreOf 2 (hz T V) := by
    intro hxQ
    obtain ⟨k, hk'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (hz T V)) ⟨x, hxQ⟩
    have h2k : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk'
    have hord : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
        (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one h2k)
    rw [orderOf_eq_one_iff] at hord
    subst hord
    apply hbV
    rw [← hxa]
    simpa using ha
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL)
  have hsign := sign_phi_of_card_four hk ((hR1T.trans hTH)) h4 hxH hx3 hx1 hxR hr
  exact mem_kz_sup_of_sign hs hk hsign

theorem relIndex_kz_sup (h : Hyp147 G T L V) (h63 : Thm14_7_63) :
    (pCoreOf 2 (hz T V)).relIndex (kz T V ⊔ pCoreOf 2 (hz T V)) = 60 := by
  obtain ⟨φ, hs, hk⟩ := exists_phi h h63
  have hle : kz T V ⊔ pCoreOf 2 (hz T V) ≤ hz T V := sup_le (oTwoUpper_le _) (pCoreOf_le 2 _)
  have hmap : ((kz T V ⊔ pCoreOf 2 (hz T V)).subgroupOf (hz T V)).map φ =
      alternatingGroup (Fin 5) := by
    rw [Subgroup.subgroupOf_sup (oTwoUpper_le _) (pCoreOf_le 2 _), Subgroup.map_sup,
      phi_map_kz hs hk, pCoreOf_subgroupOf, ← hk,
      (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  rw [← card_map_phi hk hle, hmap, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem lemma14_7_66 (S : Setting147 G T L V (hz T V))
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h63 : Thm14_7_63) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14)
    {γ γ' : F8.Geom T L (hz T V)} {g h : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g h) :
    conjSub (h : G) (F8.Uγ V (hz T V) (g : G)) ≤ pCoreOf 2 (L ⊔ T) ⊔ pCoreOf 2 (hz T V) ∧
      pCoreOf 2 (L ⊔ T) ⊔ pCoreOf 2 (hz T V) ≤ kz T V ⊔ pCoreOf 2 (hz T V) ∧
      (pCoreOf 2 (hz T V)).relIndex (pCoreOf 2 (L ⊔ T) ⊔ pCoreOf 2 (hz T V)) = 4 ∧
      (pCoreOf 2 (hz T V)).relIndex (kz T V ⊔ pCoreOf 2 (hz T V)) = 60 := by
  rw [lemma14_7_4_four S hF h1222 h1332 h1334 h13314]
  obtain ⟨h1, h2⟩ := R1_le_kz_sup S hF h63 h1222 h1332 h1334
  exact ⟨N.uα_le hF, h1, h2, relIndex_kz_sup S.hyp h63⟩

end L32A

end CFSG.Quasithin.H13
