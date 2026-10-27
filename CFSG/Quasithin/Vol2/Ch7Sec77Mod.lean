module

public import CFSG.Quasithin.Vol2.Ch7Sec77Cases1
public import CFSG.Quasithin.Background.HA7Fix

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Quasithin.H.A7F
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_blockU_of_surj {K : Subgroup G} {W : Type*} [Group W] (β : ↥(blockU K) →* W)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ K).subgroupOf (blockU K)) :
    Nat.card (blockU K) = Nat.card W * Nat.card (blockZ K) := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβs
  rw [hβk] at h1
  have h2 : Nat.card ((blockZ K).subgroupOf (blockU K)) = Nat.card (blockZ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  rw [← h1, mul_comm]

theorem mem_pCoreOf_of_comm_of_simple {K : Subgroup G} (hshort : IsShort2 K) {X : Type*}
    [Group X] (α : ↥K →* X) (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥K)
    (hX : IsSimpleGroup X) (hUZ : 2 * Nat.card (blockZ K) < Nat.card (blockU K)) {s : G}
    (hs : s ∈ K) (hc : ∀ u ∈ blockU K, s * u * s⁻¹ * u⁻¹ ∈ blockZ K) : s ∈ pCoreOf 2 K := by
  classical
  obtain ⟨-, -, ⟨hUQ, hU2⟩, -, -, hirr⟩ := hshort
  have hZc : ∀ k ∈ K, ∀ z ∈ blockZ K, k * z * k⁻¹ = z := fun k hk z hz => by
    rw [Subgroup.mem_centralizer_iff.mp hz.2 k hk, mul_inv_cancel_right]
  have hUn : ∀ k ∈ K, ∀ u ∈ blockU K, k * u * k⁻¹ ∈ blockU K := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) u).mp hu
  have hUcomm : ∀ u ∈ blockU K, ∀ v ∈ blockU K, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.mp (hUQ hv).2 u (hUQ hu).1)
  let N : Subgroup ↥K :=
    { carrier := {k | ∀ u ∈ blockU K, (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ blockZ K}
      one_mem' := fun u _ => by
        simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _
      mul_mem' := fun {a b} ha hb u hu => by
        have h1 := hb u hu
        have h2 := ha u hu
        have e : ((a * b : ↥K) : G) * u * ((a * b : ↥K) : G)⁻¹ * u⁻¹ =
            ((a : G) * ((b : G) * u * (b : G)⁻¹ * u⁻¹) * (a : G)⁻¹) *
              ((a : G) * u * (a : G)⁻¹ * u⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e, hZc a a.2 _ h1]
        exact (blockZ K).mul_mem h1 h2
      inv_mem' := fun {a} ha u hu => by
        have hu' : (a : G)⁻¹ * u * (a : G) ∈ blockU K := by
          have := hUn _ (K.inv_mem a.2) u hu
          simpa using this
        have h1 := ha _ hu'
        have e : ((a⁻¹ : ↥K) : G) * u * ((a⁻¹ : ↥K) : G)⁻¹ * u⁻¹ =
            ((a : G) * ((a : G)⁻¹ * u * (a : G)) * (a : G)⁻¹ *
              ((a : G)⁻¹ * u * (a : G))⁻¹)⁻¹ := by
          simp only [InvMemClass.coe_inv]
          group
        rw [e]
        exact (blockZ K).inv_mem h1 }
  have hNn : N.Normal := ⟨fun n hn k u hu => by
    have hu' : (k : G)⁻¹ * u * (k : G) ∈ blockU K := by
      have := hUn _ (K.inv_mem k.2) u hu
      simpa using this
    have h1 := hn _ hu'
    have e : ((k * n * k⁻¹ : ↥K) : G) * u * ((k * n * k⁻¹ : ↥K) : G)⁻¹ * u⁻¹ =
        (k : G) * ((n : G) * ((k : G)⁻¹ * u * (k : G)) * (n : G)⁻¹ *
          ((k : G)⁻¹ * u * (k : G))⁻¹) * (k : G)⁻¹ := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e, hZc k k.2 _ h1]
    exact h1⟩
  have hON : CFSG.pCore 2 ↥K ≤ N := fun p hp u hu => by
    have hpQ : (p : G) ∈ blockQ K := coe_mem_pCoreOf hp
    have h1 : (p : G) * u = u * (p : G) :=
      Subgroup.mem_centralizer_iff.mp (hUQ hu).2 _ hpQ
    rw [h1, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hmapN : (N.map α).Normal := Subgroup.Normal.map hNn α hαs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map α) with hbot | htop
  · have hsN : (⟨s, hs⟩ : ↥K) ∈ N := hc
    have h1 : α ⟨s, hs⟩ ∈ N.map α := ⟨_, hsN, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨s, hs⟩ : ↥K) ∈ α.ker := h1
    rw [hαk] at h2
    exact coe_mem_pCoreOf h2
  · exfalso
    have hall : ∀ k : ↥K, k ∈ N := by
      intro k
      have hk : α k ∈ N.map α := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      have hp : n⁻¹ * k ∈ CFSG.pCore 2 ↥K := by
        rw [← hαk, MonoidHom.mem_ker, map_mul, map_inv, hnk, inv_mul_cancel]
      have := N.mul_mem hn (hON hp)
      simpa using this
    obtain ⟨u₀, hu₀U, hu₀Z⟩ : ∃ u₀ ∈ blockU K, u₀ ∉ blockZ K := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show blockU K ≤ blockZ K from hcon)
      omega
    set W := blockZ K ⊔ Subgroup.zpowers u₀ with hW
    have hu₀N : Subgroup.zpowers u₀ ≤ Subgroup.normalizer (blockZ K : Set G) :=
      (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun z hz => (hUcomm _ hu₀U _ hz.1).symm))
    have hZW : blockZ K ≤ W := le_sup_left
    have hWU : W ≤ blockU K := sup_le inf_le_left ((Subgroup.zpowers_le).mpr hu₀U)
    have hconj : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
      intro k hk w hw
      obtain ⟨z, hz, h, hh, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hu₀N).1 hw
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      set c := k * u₀ * k⁻¹ * u₀⁻¹ with hcdef
      have hcZ : c ∈ blockZ K := hall ⟨k, hk⟩ u₀ hu₀U
      have hcu : c * u₀ = u₀ * c := hUcomm _ hcZ.1 _ hu₀U
      have e1 : k * u₀ * k⁻¹ = c * u₀ := by rw [hcdef]; group
      have e2 : k * (z * u₀ ^ j) * k⁻¹ = (k * z * k⁻¹) * (k * u₀ * k⁻¹) ^ j := by
        rw [conj_zpow]; group
      rw [e2, e1, hZc k hk z hz, (Commute.mul_zpow hcu j)]
      exact W.mul_mem (hZW hz) (W.mul_mem (hZW (Subgroup.zpow_mem _ hcZ j))
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u₀) j)))
    have hKW : K ≤ Subgroup.normalizer (W : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hconj k hk w, fun h => ?_⟩
      have h1 := hconj k⁻¹ (K.inv_mem hk) _ h
      simpa [mul_assoc] using h1
    rcases hirr W hZW hWU hKW with h | h
    · exact hu₀Z (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u₀))
    · have hcard := Lin2.card_sup_mul_card_inf hu₀N
      have h2 : Nat.card (Subgroup.zpowers u₀) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hU2 u₀ hu₀U))
      have h3 : 1 ≤ Nat.card (Subgroup.zpowers u₀ ⊓ blockZ K : Subgroup G) := Nat.card_pos
      rw [sup_comm, ← hW, h] at hcard
      have h4 : Nat.card (blockU K) ≤ 2 * Nat.card (blockZ K) := by
        calc Nat.card (blockU K) ≤ Nat.card (blockU K) *
              Nat.card (Subgroup.zpowers u₀ ⊓ blockZ K : Subgroup G) := Nat.le_mul_of_pos_right _ h3
          _ = Nat.card (Subgroup.zpowers u₀) * Nat.card (blockZ K) := hcard
          _ ≤ 2 * Nat.card (blockZ K) := Nat.mul_le_mul_right _ h2
      omega

theorem card_altHeart_six_le : Nat.card (↥(evenWeight 6) ⧸ constWeight 6) ≤ 16 := by
  classical
  have h1 : Nat.card ↥(evenWeight 6) = 32 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 6 → ZMod 2 =>
      (show x ∈ evenWeight 6 ↔ ∑ i, x i = 0 from Iff.rfl)))]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  have hone : (fun _ => 1 : Fin 6 → ZMod 2) ∈ evenWeight 6 := by
    show ∑ _i : Fin 6, (1 : ZMod 2) = 0
    decide
  have h2 : 2 ≤ Nat.card ↥(constWeight 6) := by
    refine Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨0, ⟨⟨_, hone⟩, fun i j => rfl⟩, ?_⟩⟩
    intro h
    have := congrArg (fun x : ↥(constWeight 6) => ((x : ↥(evenWeight 6)) : Fin 6 → ZMod 2) 0) h
    simp at this
  have h3 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (constWeight 6)
  rw [h1] at h3
  have h4 : Nat.card (↥(evenWeight 6) ⧸ constWeight 6) * 2 ≤ 32 :=
    calc Nat.card (↥(evenWeight 6) ⧸ constWeight 6) * 2
        ≤ Nat.card (↥(evenWeight 6) ⧸ constWeight 6) * Nat.card ↥(constWeight 6) :=
          Nat.mul_le_mul_left _ h2
      _ = 32 := h3.symm
  omega

theorem exists_threePart (θ : G) : ∃ r b : ℕ, ¬ 3 ∣ r ∧ orderOf (θ ^ r) = 3 ^ b := by
  have h0 : orderOf θ ≠ 0 := (orderOf_pos θ).ne'
  obtain ⟨b, r, hr, hθr⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 3 (by norm_num)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr (dvd_zero 3)
  refine ⟨r, b, hr, ?_⟩
  rw [orderOf_pow_of_dvd hr0 (Dvd.intro_left _ hθr.symm), hθr,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem th_mul_inv_pow_mem (hc : S.Coord θ e) {r : ℕ} (hr : ¬ 3 ∣ r) :
    θ * ((θ ^ r) ^ r)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have h3 := th_pow_three_mem hc
  have hmod : r * r % 3 = 1 := by
    rw [Nat.mul_mod]
    have : r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  obtain ⟨q, hq⟩ : ∃ q, r * r = 3 * q + 1 := ⟨r * r / 3, by omega⟩
  have e1 : (θ ^ r) ^ r = (θ ^ 3) ^ q * θ := by
    rw [← pow_mul, ← pow_mul, ← pow_succ, hq]
  have e2 : θ * ((θ ^ 3) ^ q * θ)⁻¹ = ((θ ^ 3) ^ q)⁻¹ := by group
  rw [e1, e2]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ h3 q)

theorem pow_not_mem (hc : S.Coord θ e) {r : ℕ} (hr : ¬ 3 ∣ r) :
    θ ^ r ∉ Subgroup.centralizer (fsuV T I : Set G) := fun h =>
  th_not_mem hc (by
    have h2 := Subgroup.mul_mem _ (th_mul_inv_pow_mem hc hr) (Subgroup.pow_mem _ h r)
    simpa using h2)

theorem mul_conj_mul_conj_eq_one (hc : S.Coord θ e) {r : ℕ} (hr : ¬ 3 ∣ r) {v : G}
    (hv : v ∈ S.vm e) :
    v * (θ ^ r * v * (θ ^ r)⁻¹) * (θ ^ r * (θ ^ r * v * (θ ^ r)⁻¹) * (θ ^ r)⁻¹) = 1 := by
  set y := θ ^ r with hy
  have hyN : y ∈ Subgroup.normalizer (S.vm e : Set G) :=
    Subgroup.pow_mem _ (mem_normalizer_vm hc) r
  have hconj : ∀ w ∈ S.vm e, y * w * y⁻¹ ∈ S.vm e := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
  have hy3 : y ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [hy, ← pow_mul, mul_comm, pow_mul]
    exact Subgroup.pow_mem _ (th_pow_three_mem hc) r
  have hcomm : ∀ a ∈ S.vm e, ∀ b ∈ S.vm e, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (S.comm.is_comm.comm ⟨a, vm_le ha⟩ ⟨b, vm_le hb⟩)
  set a := y * v * y⁻¹ with ha
  set b := y * a * y⁻¹ with hb
  have hav : a ∈ S.vm e := hconj v hv
  have hbv : b ∈ S.vm e := hconj a hav
  have hv3 : y * b * y⁻¹ = v := by
    have h1 := Subgroup.mem_centralizer_iff.mp hy3 v (vm_le hv)
    calc y * b * y⁻¹ = y ^ 3 * v * (y ^ 3)⁻¹ := by rw [hb, ha, pow_three]; group
      _ = v := by rw [← h1, mul_inv_cancel_right]
  set w := v * a * b with hw
  have hwm : w ∈ S.vm e := (S.vm e).mul_mem ((S.vm e).mul_mem hv hav) hbv
  have hyw : y * w * y⁻¹ = w := by
    have e1 : y * w * y⁻¹ = (y * v * y⁻¹) * (y * a * y⁻¹) * (y * b * y⁻¹) := by rw [hw]; group
    rw [e1, ← ha, ← hb, hv3, hw, mul_assoc, hcomm b hbv v hv, ← mul_assoc, hcomm a hav v hv]
  have hyw' : y * w = w * y := by
    calc y * w = y * w * y⁻¹ * y := by group
      _ = w * y := by rw [hyw]
  exact eq_one_of_mem_vm hc (th_mul_inv_pow_mem hc hr) hwm hyw'

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem vm_le_blockU (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H) {y : G} (hyK : y ∈ K)
    (hyM : y ∈ fsuM T L) (hyo : Odd (orderOf y))
    (hyV : y ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    S.vm e ≤ blockU K ∧ S.vm e ⊓ blockZ K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hy0 : y ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G) := by
    have := C.conf.hHG (hKH hyK)
    rwa [C.hVp] at this
  have hyN : y ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN hyM
  have hYK : Subgroup.zpowers y ≤ K := (Subgroup.zpowers_le).mpr hyK
  obtain ⟨m, hm⟩ := exists_pow_of_odd hc hyM hy0 hyo hyV
  obtain ⟨-, hred⟩ := C.isTwoReduced_U hF
  have hVO : fsuV T I ≤ pCoreOf 2 H :=
    C.V_le_U.trans (CFSG.Quasithin.A4.le_pCoreOf_of_isTwoReducedIn hred)
  have hON : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.Quasithin.P134.pCoreOf_le_normalizer_of_mem_cComp hK
  have hOK : pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 H (hKH hk), Subgroup.le_normalizer hk⟩)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have hcomm : ⁅S.vm e, Subgroup.zpowers y⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro v hv t ht
    have hvO : v ∈ pCoreOf 2 H := hVO (vm_le hv)
    have htK : t ∈ K := hYK ht
    refine hOK ⟨?_, ?_⟩
    · have h1 : t * v⁻¹ * t⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH htK)) _).mp
          (Subgroup.inv_mem _ hvO)
      rw [commutatorElement_def]
      have e1 : v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem _ hvO h1
    · have h1 : v * t * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hON hvO) t).mp htK
      rw [commutatorElement_def]
      exact K.mul_mem h1 (K.inv_mem htK)
  have hvmc : S.vm e ≤ ⁅S.vm e, Subgroup.zpowers y⁆ := vm_le_commutator hc hm hyN
  have hvmK : S.vm e ≤ pCoreOf 2 K := hvmc.trans hcomm
  refine ⟨hvmc.trans (Subgroup.commutator_mono hvmK hYK), ?_⟩
  rw [eq_bot_iff]
  intro v hv
  have h1 : y * v = v * y := Subgroup.mem_centralizer_iff.mp hv.2.2 y hyK
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_vm hc hm hv.1 h1)

theorem not_inf_le_pCoreOf_alt {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (α : ↥K →* alternatingGroup (Fin n)) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥K) :
    ¬ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K ≤ pCoreOf 2 K := by
  have hαker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → α k = 1 := by
    rintro k ⟨k', hk', hkk'⟩
    have e : k' = k := Subtype.ext hkk'
    subst e
    have : k' ∈ α.ker := by rw [hαk]; assumption
    exact this
  refine C.not_inf_le_pCoreOf_of_hom hK α hαker fun X hX => ?_
  rw [card_map_sylow_eq α hαs hX]
  have hfac : 2 ≤ (Nat.card (alternatingGroup (Fin n))).factorization 2 := by
    rcases hn with rfl | rfl <;>
      (rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide +kernel)
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (Nat.card (alternatingGroup (Fin n))).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hfac

theorem false_of_block16 (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hshort : IsShort2 K) {X : Type*} [Group X] (α : ↥K →* X) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥K) (hX : IsSimpleGroup X)
    (hcard : Nat.card (blockU K) ≤ 16 * Nat.card (blockZ K)) {y : G} (hyK : y ∈ K)
    (hyM : y ∈ fsuM T L) (hyo : Odd (orderOf y))
    (hyV : y ∉ Subgroup.centralizer (fsuV T I : Set G))
    (hQK : ¬ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K ≤ pCoreOf 2 K) : False := by
  obtain ⟨hvmU, hvmZ⟩ := C.vm_le_blockU hF hK hyK hyM hyo hyV
  have hUQ : blockU K ≤ blockQ K := hshort.2.2.1.1.trans inf_le_left
  have hZK : blockZ K ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hvmN : S.vm e ≤ Subgroup.normalizer (blockZ K : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZK hz) v ((pCoreOf_le 2 K) (hUQ (hvmU hv)))).symm)
  have h1 := Lin2.card_sup_mul_card_inf hvmN
  rw [hvmZ, Subgroup.card_bot, mul_one, card_vm] at h1
  have hsup : S.vm e ⊔ blockZ K = blockU K :=
    Subgroup.eq_of_le_of_card_ge (sup_le hvmU inf_le_left) (by rw [h1]; exact hcard)
  have hZ1 : 0 < Nat.card (blockZ K) := Nat.card_pos
  have h2Z : 2 * Nat.card (blockZ K) < Nat.card (blockU K) := by
    rw [← hsup, h1]
    omega
  apply hQK
  intro s hs
  refine mem_pCoreOf_of_comm_of_simple hshort α hαs hαk hX h2Z hs.2 fun u hu => ?_
  have hle : blockU K ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [← hsup]
    refine sup_le (fun v hv => ?_) (fun z hz => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hs.1.2 v (vm_le hv)))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hZK hz) s hs.2).symm)
  have h3 : s * u = u * s := (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)).symm
  have e1 : s * u * s⁻¹ * u⁻¹ = 1 := by rw [h3]; group
  rw [e1]
  exact Subgroup.one_mem _

theorem false_of_altBlock6 (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (h6 : CFSG.Quasithin.IsAltBlockType K 6) {r b : ℕ} (hr : ¬ 3 ∣ r) (hyK : θ ^ r ∈ K)
    (hyb : orderOf (θ ^ r) = 3 ^ b) : False := by
  have hc := C.conf.hc
  obtain ⟨hshort, α, hαs, hαk, β, hβs, hβk, -⟩ := h6
  have hcard : Nat.card (blockU K) ≤ 16 * Nat.card (blockZ K) := by
    rw [card_blockU_of_surj β hβs hβk, Nat.card_congr Multiplicative.toAdd]
    exact Nat.mul_le_mul_right _ card_altHeart_six_le
  exact C.false_of_block16 hF hK hshort α hαs hαk (alternatingGroup.isSimpleGroup (by simp))
    hcard hyK ((fsuM T L).pow_mem (S.L_le_fsuM hc.mem) r)
    (by rw [hyb]; exact Odd.pow (by decide)) (pow_not_mem hc hr)
    (C.not_inf_le_pCoreOf_alt hK (Or.inl rfl) α hαs hαk)

theorem false_of_excA7 (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (h : CFSG.Quasithin.IsExcA7Block K) {r b : ℕ} (hr : ¬ 3 ∣ r) (hyK : θ ^ r ∈ K)
    (hyb : orderOf (θ ^ r) = 3 ^ b) : False := by
  have hc := C.conf.hc
  obtain ⟨hshort, ⟨α, hαs, hαk⟩, hidx⟩ := h
  have hcard : Nat.card (blockU K) ≤ 16 * Nat.card (blockZ K) := by
    have h1 := Subgroup.card_mul_index ((blockZ K).subgroupOf (blockU K))
    have h2 : Nat.card ((blockZ K).subgroupOf (blockU K)) = Nat.card (blockZ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2, hidx, show (2 : ℕ) ^ 4 = 16 by norm_num] at h1
    omega
  exact C.false_of_block16 hF hK hshort α hαs hαk (alternatingGroup.isSimpleGroup (by simp))
    hcard hyK ((fsuM T L).pow_mem (S.L_le_fsuM hc.mem) r)
    (by rw [hyb]; exact Odd.pow (by decide)) (pow_not_mem hc hr)
    (C.not_inf_le_pCoreOf_alt hK (Or.inr rfl) α hαs hαk)

theorem false_of_altType7 (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (h7 : CFSG.QuasithinUnique.IsAltType K 7) {r b : ℕ} (hr : ¬ 3 ∣ r) (hyK : θ ^ r ∈ K)
    (hyb : orderOf (θ ^ r) = 3 ^ b) : False := by
  classical
  have hc := C.conf.hc
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h7
  have hyM : θ ^ r ∈ fsuM T L := (fsuM T L).pow_mem (S.L_le_fsuM hc.mem) r
  have hyo : Odd (orderOf (θ ^ r)) := by rw [hyb]; exact Odd.pow (by decide)
  have hyV : θ ^ r ∉ Subgroup.centralizer (fsuV T I : Set G) := pow_not_mem hc hr
  obtain ⟨hvmU, hvmZ⟩ := C.vm_le_blockU hF hK hyK hyM hyo hyV
  have hαone : ∀ k : ↥K, α k = 1 → (k : G) ∈ pCoreOf 2 K := fun k hk =>
    coe_mem_pCoreOf (by rw [← hαk]; exact hk)
  set σ : Equiv.Perm (Fin 7) := (α ⟨θ ^ r, hyK⟩ : Equiv.Perm (Fin 7)) with hσdef
  have hσ1 : σ ≠ 1 := by
    intro h
    have h1 : α ⟨θ ^ r, hyK⟩ = 1 := Subtype.ext h
    exact hyV (C.pCoreOf_le_centralizer hF hK (hαone _ h1))
  have hσ3 : orderOf σ = 3 := by
    have h1 : orderOf σ ∣ 3 ^ b := by
      rw [hσdef, Subgroup.orderOf_coe, ← hyb]
      calc orderOf (α ⟨θ ^ r, hyK⟩) ∣ orderOf (⟨θ ^ r, hyK⟩ : ↥K) := orderOf_map_dvd α _
        _ = orderOf (θ ^ r) := (Subgroup.orderOf_coe _).symm
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    have h420 := orderOf_dvd_420 σ
    rw [hk] at h420
    have hk1 : k ≤ 1 := by
      by_contra hcon
      have h9 : 9 ∣ 3 ^ k := by
        have := pow_dvd_pow 3 (show 2 ≤ k by omega)
        simpa using this
      have := h9.trans h420
      norm_num at this
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hσ1
    · simpa using hk
  let f : ↥(S.vm e) → (Fin 7 → ZMod 2) := fun v =>
    ((Multiplicative.toAdd (β ⟨v, hvmU v.2⟩) : evenWeight 7) : Fin 7 → ZMod 2)
  have hfinj : Function.Injective f := by
    intro v₁ v₂ h
    have h1 : β ⟨v₁, hvmU v₁.2⟩ = β ⟨v₂, hvmU v₂.2⟩ := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h
    have h2 : (⟨v₁, hvmU v₁.2⟩ : ↥(blockU K)) * (⟨v₂, hvmU v₂.2⟩)⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    have h3 : (v₁ : G) * (v₂ : G)⁻¹ ∈ S.vm e ⊓ blockZ K :=
      ⟨(S.vm e).mul_mem v₁.2 ((S.vm e).inv_mem v₂.2), h2⟩
    rw [hvmZ, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact Subtype.ext h3
  have hconjU : ∀ k ∈ K, ∀ u ∈ blockU K, k * u * k⁻¹ ∈ blockU K := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) u).mp hu
  have hfS : ∀ v : ↥(S.vm e), f v ∈ kerSet σ := by
    intro v
    rw [mem_kerSet]
    refine ⟨?_, ?_⟩
    · have := (Multiplicative.toAdd (β ⟨v, hvmU v.2⟩)).2
      exact this
    · have hid := mul_conj_mul_conj_eq_one hc hr v.2
      set u₁ : ↥(blockU K) := ⟨v, hvmU v.2⟩ with hu₁
      set u₂ : ↥(blockU K) := ⟨θ ^ r * v * (θ ^ r)⁻¹, hconjU _ hyK _ (hvmU v.2)⟩ with hu₂
      set u₃ : ↥(blockU K) := ⟨θ ^ r * (θ ^ r * v * (θ ^ r)⁻¹) * (θ ^ r)⁻¹,
        hconjU _ hyK _ u₂.2⟩ with hu₃
      have h12 := hβe ⟨θ ^ r, hyK⟩ u₁ u₂ rfl
      have h23 := hβe ⟨θ ^ r, hyK⟩ u₂ u₃ rfl
      have hprod : u₁ * u₂ * u₃ = 1 := Subtype.ext hid
      have hsum : Multiplicative.toAdd (β u₁) + Multiplicative.toAdd (β u₂) +
          Multiplicative.toAdd (β u₃) = 0 := by
        have := congrArg (fun z => Multiplicative.toAdd (β z)) hprod
        simpa [map_mul] using this
      intro j
      have hj := congrArg (fun x : ↥(evenWeight 7) => (x : Fin 7 → ZMod 2) (σ (σ j))) hsum
      simp only [AddSubgroup.coe_add, Pi.add_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at hj
      rw [← hσdef] at h12 h23
      simp only [h23, h12, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at hj
      show ((Multiplicative.toAdd (β u₁) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) j +
          ((Multiplicative.toAdd (β u₁) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) (σ j) +
          ((Multiplicative.toAdd (β u₁) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) (σ (σ j)) = 0
      linear_combination hj
  have hginj : Function.Injective (fun v : ↥(S.vm e) => (⟨f v, hfS v⟩ : ↥(kerSet σ))) :=
    fun a b hab => hfinj (congrArg (fun z : ↥(kerSet σ) => (z : Fin 7 → ZMod 2)) hab)
  have hcardle : 16 ≤ (kerSet σ).card := by
    have h1 := Nat.card_le_card_of_injective _ hginj
    rwa [card_vm, Nat.card_eq_finsetCard] at h1
  rcases isConj_c71_or_c72 hσ3 with hπ | hπ
  ·
    obtain ⟨π, hπ⟩ := isConj_iff.mp hπ
    rw [← hπ, card_kerSet_conj] at hcardle
    have h4 : (kerSet c71).card = 4 := card_ker_c71
    omega
  ·
    obtain ⟨π, hπ⟩ := isConj_iff.mp hπ
    have h16 : (kerSet σ).card = 16 := by rw [← hπ, card_kerSet_conj]; exact card_ker_c72
    have hbij := hginj.bijective_of_nat_card_le (by rw [card_vm, Nat.card_eq_finsetCard, h16])
    apply C.not_inf_le_pCoreOf_alt hK (Or.inr rfl) α hαs hαk
    intro s hs
    refine hαone ⟨s, hs.2⟩ (Subtype.ext ?_)
    show ((α ⟨s, hs.2⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = 1
    apply eq_one_of_fix_kerSet π
    intro x hx i
    obtain ⟨v, hv⟩ := hbij.2 ⟨x, hπ ▸ hx⟩
    have hvx : f v = x := congrArg (fun z : ↥(kerSet σ) => (z : Fin 7 → ZMod 2)) hv
    rw [← hvx]
    have hsv : ((⟨v, hvmU v.2⟩ : ↥(blockU K)) : G) = s * (⟨v, hvmU v.2⟩ : ↥(blockU K)) * s⁻¹ := by
      show (v : G) = s * v * s⁻¹
      rw [← Subgroup.mem_centralizer_iff.mp hs.1.2 v (vm_le v.2), mul_inv_cancel_right]
    exact (hβe ⟨s, hs.2⟩ _ _ hsv i).symm

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
