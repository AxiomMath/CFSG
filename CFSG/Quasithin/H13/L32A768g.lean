module

public import CFSG.Quasithin.H13.L32A768f
public import CFSG.Quasithin.H13.L32A767t
public import CFSG.Quasithin.H13.L32AKG1468b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {N P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hP : IsPGroup 2 P) {y : G} (hy : y ∈ N ⊔ P) (hodd : Odd (orderOf y)) : y ∈ N := by
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPN] at hy
  obtain ⟨r, hr, d, hd, rfl⟩ := hy
  obtain ⟨d', hd', e⟩ := pow_mul_mem_of_le_normalizer (hPN hr) hd (orderOf (r * d))
  rw [pow_orderOf_eq_one] at e
  have hrn : r ^ orderOf (r * d) ∈ N := by
    rw [eq_inv_of_mul_eq_one_left e.symm]
    exact inv_mem hd'
  obtain ⟨n, hn⟩ := hP ⟨r, hr⟩
  have hr2 : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime (orderOf (r * d)) (orderOf r) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hr2)
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hrN : r ∈ N := hm ▸ pow_mem hrn m
  exact mul_mem hrN hd

omit [Finite G] in
theorem oTwoUpper_sup_le {N P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hP : IsPGroup 2 P) : oTwoUpper (N ⊔ P) ≤ N :=
  (Subgroup.closure_le _).mpr fun _ hx => mem_of_odd_of_mem_sup hPN hP hx.1 hx.2

omit [Finite G] in
theorem relIndex_centralizer_le_two {u z : G}
    (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) (hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z) :
    (Subgroup.centralizer ({u} : Set G)).relIndex T ≤ 2 := by
  have hz : ∀ t ∈ T, t ∉ Subgroup.centralizer ({u} : Set G) → t * u * t⁻¹ = z * u := by
    intro t ht htC
    rcases hgen _ (hT t ht) with h | h
    · exfalso
      apply htC
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * u = t * u * t⁻¹ * u⁻¹ * (u * t) := by group
        _ = u * t := by rw [h, one_mul]
    · calc t * u * t⁻¹ = t * u * t⁻¹ * u⁻¹ * u := by group
        _ = z * u := by rw [h]
  refine relIndex_le_two_of fun a ha b hb haC hbC => ?_
  have ha' := hz a ha haC
  have hb' := hz b hb hbC
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e1 : (a⁻¹ * b) * u * (a⁻¹ * b)⁻¹ = u := by
    calc (a⁻¹ * b) * u * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * u * b⁻¹) * a := by group
      _ = a⁻¹ * (z * u) * a := by rw [hb']
      _ = a⁻¹ * (a * u * a⁻¹) * a := by rw [ha']
      _ = u := by group
  calc a⁻¹ * b * u = (a⁻¹ * b) * u * (a⁻¹ * b)⁻¹ * (a⁻¹ * b) := by group
    _ = u * (a⁻¹ * b) := by rw [e1]

theorem eq_sup_pCoreOf_of_relIndex {L₀ L : Subgroup G} (hL₀L : L₀ ≤ L) {n : ℕ}
    (h₀ : (pCoreOf 2 L₀).relIndex L₀ = n) (h : (pCoreOf 2 L).relIndex L = n) :
    L = L₀ ⊔ pCoreOf 2 L := by
  have hN : L₀ ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hL₀L.trans (le_normalizer_pCoreOf 2 L)
  have hle : L₀ ⊓ pCoreOf 2 L ≤ pCoreOf 2 L₀ :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) (hN hx))
      ((pCoreOf_isPGroup 2 L).to_le inf_le_right)
  have hsup : L₀ ⊔ pCoreOf 2 L ≤ L := sup_le hL₀L (pCoreOf_le 2 L)
  have e1 : (pCoreOf 2 L).relIndex (L₀ ⊔ pCoreOf 2 L) = (pCoreOf 2 L).relIndex L₀ :=
    A4.relIndex_sup_eq_of_le_normalizer' hN
  have e2 : (L₀ ⊓ pCoreOf 2 L).relIndex L₀ = (pCoreOf 2 L).relIndex L₀ := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right _ _
  have hdvd : n ∣ (pCoreOf 2 L).relIndex (L₀ ⊔ pCoreOf 2 L) := by
    rw [e1, ← e2, ← h₀]
    exact Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ _ hle (pCoreOf_le 2 L₀))
  have hm := Subgroup.relIndex_mul_relIndex (pCoreOf 2 L) (L₀ ⊔ pCoreOf 2 L) L le_sup_right hsup
  rw [h] at hm
  have hpos : 0 < n := by
    rw [← h]
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have e := Subgroup.relIndex_mul_card (pCoreOf 2 L) L
    rw [h0, zero_mul] at e
    exact (Nat.card_pos (α := ↥L)).ne' e.symm
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, mul_assoc] at hm
  have h1 : k * (L₀ ⊔ pCoreOf 2 L).relIndex L = 1 := by
    have := hm
    nlinarith [Nat.mul_le_mul_left n (Nat.zero_le (k * (L₀ ⊔ pCoreOf 2 L).relIndex L))]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_mul_eq_one_left h1)) hsup

theorem relIndex_le_of_eq_sup {L₀ Q : Subgroup G} {u : G}
    (hQN : L₀ ≤ Subgroup.normalizer (Q : Set G)) (hL₀u : L₀ ≤ Subgroup.centralizer ({u} : Set G)) :
    (Subgroup.centralizer ({u} : Set G)).relIndex (L₀ ⊔ Q) ≤
      (Subgroup.centralizer ({u} : Set G)).relIndex Q := by
  set C := Subgroup.centralizer ({u} : Set G) with hC
  have hQ'N : L₀ ≤ Subgroup.normalizer ((Q ⊓ C : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf_of_mem (hQN hx) (Subgroup.le_normalizer (hL₀u hx))
  have e1 := L32NSet14.card_sup_mul_card_inf hQN
  have e2 := L32NSet14.card_sup_mul_card_inf hQ'N
  have e3 : L₀ ⊓ (Q ⊓ C) = L₀ ⊓ Q := by
    rw [inf_comm Q C, ← inf_assoc, inf_eq_left.mpr hL₀u]
  rw [e3] at e2
  have e4 := Subgroup.relIndex_mul_card C (L₀ ⊔ Q)
  have e5 := Subgroup.relIndex_mul_card C Q
  have hsub : L₀ ⊔ (Q ⊓ C) ≤ C ⊓ (L₀ ⊔ Q) :=
    le_inf (sup_le hL₀u (inf_le_right)) (sup_le_sup_left inf_le_left _)
  have hcard := Subgroup.card_le_of_le hsub
  have hpos : 0 < Nat.card ↥(C ⊓ (L₀ ⊔ Q)) * Nat.card ↥(L₀ ⊓ Q) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc C.relIndex (L₀ ⊔ Q) * (Nat.card ↥(C ⊓ (L₀ ⊔ Q)) * Nat.card ↥(L₀ ⊓ Q))
      = Nat.card ↥(L₀ ⊔ Q) * Nat.card ↥(L₀ ⊓ Q) := by rw [← mul_assoc, e4]
    _ = Nat.card ↥L₀ * Nat.card ↥Q := e1
    _ = Nat.card ↥L₀ * (C.relIndex Q * Nat.card ↥(C ⊓ Q)) := by rw [e5]
    _ = C.relIndex Q * (Nat.card ↥L₀ * Nat.card ↥(Q ⊓ C)) := by rw [inf_comm C Q]; ring
    _ = C.relIndex Q * (Nat.card ↥(L₀ ⊔ (Q ⊓ C)) * Nat.card ↥(L₀ ⊓ Q)) := by rw [e2]
    _ ≤ C.relIndex Q * (Nat.card ↥(C ⊓ (L₀ ⊔ Q)) * Nat.card ↥(L₀ ⊓ Q)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard)

theorem le_of_relIndex_le_two {T L N : Subgroup G} (hLf : quasithinIsFaithfulLocal T L)
    (h2 : N.relIndex L ≤ 2) : L ≤ N := by
  have hpos : 0 < N.relIndex L := Nat.pos_of_ne_zero fun h0 => by
    have e := Subgroup.relIndex_mul_card N L
    rw [h0, zero_mul] at e
    exact (Nat.card_pos (α := ↥L)).ne' e.symm
  rcases (show N.relIndex L = 1 ∨ N.relIndex L = 2 by omega) with h1 | h2'
  · exact Subgroup.relIndex_eq_one.mp h1
  · have hidx : (N.subgroupOf L).index = 2 := h2'
    have hnorm : (N.subgroupOf L).Normal := Subgroup.normal_of_index_eq_two hidx
    have heq := hLf.2.1 (N ⊓ L) inf_le_right (by rwa [Subgroup.inf_subgroupOf_right])
      fun x hx => ⟨1, by
        have := Subgroup.mul_self_mem_of_index_two hidx ⟨x, hx⟩
        rw [Subgroup.mem_subgroupOf] at this
        rw [pow_one, pow_two]
        exact Subgroup.mem_inf.mpr ⟨this, mul_mem hx hx⟩⟩
    exact heq ▸ inf_le_left

omit [Finite G] in
theorem exists_ne_one_mem_center [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) :
    ∃ w ∈ N, w ≠ 1 ∧ ∀ t ∈ T, t * w = w * t := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTN
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h1 => hy1 (Subtype.ext (Subtype.ext h1)), fun t ht => ?_⟩
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩) :)

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem false_of_ru (hTwoRu : KG1468TwoRu)
    (hR3 : ∀ w ∈ u0 T V, w ≠ 1 → T ≤ Subgroup.centralizer ({w} : Set G) →
      Subgroup.centralizer ({w} : Set G) ≤ hz T V)
    {u : G} (hu : u ∈ u0 T V) (hu1 : u ≠ 1) (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V)
    (hS : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
      (Subgroup.centralizer ({u} : Set G)))
    {I : Subgroup G} (hIu : I ≤ Subgroup.centralizer ({u} : Set G))
    (hIn : (I.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal) (hKI : kz T V ≤ I)
    (hne : I ≠ kz T V) (hIp : ⁅I, I⁆ = I) (hq : CFSG.IsQuasisimple ↥I)
    (hRu : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* NativeSporadic.Carrier .Ru)) : False := by
  have h := C.hyp
  have h13322 := stmt13_3_2_two_of C.h1332
  obtain ⟨hVe, hV8, -, hV1, -⟩ := C.hMod G T L V h.hyp h.fsu
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hV1
  have hHz := hz_eq_centralizer_singleton hzV1 hgen
  have hIH := not_le_hz_of_ne hKI hne hIp
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  have hVK := v_le_kz h C.hMod C.h1222 C.h1332 C.h1334
  have hzI : z ∈ I := hKI (hVK hzV)
  have hz2 : orderOf z = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hVe.2 z hzV) hz1
  have hzC : z ∉ Subgroup.centralizer (I : Set G) := by
    intro hzc
    apply hIH
    rw [hHz]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzc x hx
  have hK0 : oTwoUpper (I ⊓ Subgroup.centralizer ({z} : Set G)) = kz T V := by
    rw [← hHz]
    exact oTwoUpper_inf_hz_eq hKI
  have hA5 : Nonempty (↥(oTwoUpper (I ⊓ Subgroup.centralizer ({z} : Set G))) ⧸
      CFSG.pCore 2 ↥(oTwoUpper (I ⊓ Subgroup.centralizer ({z} : Set G))) ≃*
        alternatingGroup (Fin 5)) := by
    rw [hK0]
    exact C.nonempty_quot_alt5
  have hVO : V ≤ pCoreOf 2 (oTwoUpper (I ⊓ Subgroup.centralizer ({z} : Set G))) := by
    rw [hK0]
    exact (le_conjClosure V _ : V ≤ fsuU T V).trans C.fsuU_le_pCoreOf_kz
  have hcomm : ∀ e ∈ V, ∀ w ∈ pCoreOf 2 (oTwoUpper (I ⊓ Subgroup.centralizer ({z} : Set G))),
      e * w * e⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
    rw [hK0]
    exact fun e he w hw => C.comm_mem_zpowers hgen he hw
  have hy : ∃ y ∈ oTwoUpper (I ⊓ Subgroup.centralizer ({z} : Set G)), orderOf y = 3 ∧
      y ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ e ∈ V, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers z → e ∈ Subgroup.zpowers z := by
    rw [hK0]
    exact C.exists_three_fpf hzV1 hgen
  have hNV : L ⊔ T = Subgroup.normalizer (V : Set G) :=
    (lemma14_7_67_one_two_five h C.h1222 C.h1332 C.h1334 C.h63 C.hF).2.2
  have hSI : ∃ S : Subgroup G, QuasithinUnique.IsSylowTwoOf S I ∧
      S ≤ Subgroup.normalizer (V : Set G) ∧ S ≤ Subgroup.centralizer ({z} : Set G) := by
    have hzZ : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp hzV1).2
    have hzCT : z ∈ Subgroup.centralizer (T : Set G) :=
      quasithinOmegaOneCenter_le_centralizer T hzZ
    refine ⟨T ⊓ Subgroup.centralizer ({u} : Set G) ⊓ I, A4.isSylowTwoOf_inf_normal hS hIu
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hIu).mp hIn), ?_, ?_⟩
    · exact (inf_le_left.trans inf_le_left).trans (le_sup_right.trans hNV.le)
    · intro t ht
      have htT : t ∈ T := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzCT t htT)
  obtain ⟨eL⟩ := hTwoRu G I hq hRu z hzI hz2 hzC hA5 V hVO hVe hV8 hzV
    (C.inf_centralizer_eq_bot hKI hIH) hcomm hy hSI
  set L₀ := oTwoUpper (I ⊓ Subgroup.normalizer (V : Set G)) with hL₀
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.normalizes h13322
  have hL₀L : L₀ ≤ L :=
    (oTwoUpper_mono (inf_le_right.trans hNV.symm.le)).trans
      (oTwoUpper_sup_le hTL h.fsu.sylow.1)
  have h168 : (pCoreOf 2 L₀).relIndex L₀ = 168 := by
    rw [Subgroup.relIndex, pCoreOf_subgroupOf_self]
    show Nat.card (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) = 168
    rw [Nat.card_congr eL.toEquiv, SL3.card_SL3]
  have h168' : (pCoreOf 2 L).relIndex L = 168 := by
    obtain ⟨θ₀, hθ₀, hker₀⟩ := exists_surj_SL32_of_lieModel h.hyp.linear
    rw [Subgroup.relIndex, ← hker₀]
    show Nat.card (↥L ⧸ θ₀.ker) = 168
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ₀ hθ₀).toEquiv, SL3.card_SL3]
  have hLeq := eq_sup_pCoreOf_of_relIndex hL₀L h168 h168'
  have hL₀u : L₀ ≤ Subgroup.centralizer ({u} : Set G) :=
    (oTwoUpper_le _).trans (inf_le_left.trans hIu)
  have hO : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
      (pCoreOf_isPGroup 2 L)
  have hOT : pCoreOf 2 L ≤ T :=
    hO.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right))
  have hTne : (Subgroup.centralizer ({u} : Set G)).relIndex T ≠ 0 := fun h0 => by
    have e := Subgroup.relIndex_mul_card (Subgroup.centralizer ({u} : Set G)) T
    rw [h0, zero_mul] at e
    exact (Nat.card_pos (α := ↥T)).ne' e.symm
  have hidx : (Subgroup.centralizer ({u} : Set G)).relIndex L ≤ 2 := by
    calc (Subgroup.centralizer ({u} : Set G)).relIndex L
        = (Subgroup.centralizer ({u} : Set G)).relIndex (L₀ ⊔ pCoreOf 2 L) := by rw [← hLeq]
      _ ≤ (Subgroup.centralizer ({u} : Set G)).relIndex (pCoreOf 2 L) :=
          relIndex_le_of_eq_sup (hL₀L.trans (le_normalizer_pCoreOf 2 L)) hL₀u
      _ ≤ (Subgroup.centralizer ({u} : Set G)).relIndex T :=
          Subgroup.relIndex_le_of_le_right hOT hTne
      _ ≤ 2 := relIndex_centralizer_le_two hT hgen
  have hLu : L ≤ Subgroup.centralizer ({u} : Set G) :=
    le_of_relIndex_le_two h.hyp.h13.faithful hidx
  have hU0T : u0 T V ≤ T :=
    ((centralizerMod_le_left _ _ _).trans C.fsuU_le_pCoreOf_kz).trans
      (pCoreOf_kz_le.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
        (isSylowTwoOf_of_le h (T_le_hz h C.h63))))
  have huN : u ∈ u0 T V ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLu hl)⟩
  have hNne : u0 T V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.mem_bot] at huN
    exact hu1 huN
  have hTN : T ≤ Subgroup.normalizer
      ((u0 T V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf_of_mem (hz_le_normalizer_u0 h C.hMod (T_le_hz h C.h63 ht))
      (mem_normalizer_centralizer (hTL ht))
  obtain ⟨w, hwN, hw1, hwT⟩ :=
    exists_ne_one_mem_center h.fsu.sylow.1 (inf_le_left.trans hU0T) hTN hNne
  obtain ⟨hwU, hwL⟩ := Subgroup.mem_inf.mp hwN
  have hTw : T ≤ Subgroup.centralizer ({w} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hwT t ht)
  have hLw : L ≤ Subgroup.centralizer ({w} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwL l hl)
  have hLH := hLw.trans (hR3 w hwU hw1 hTw)
  have hzL : z ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨hzV, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLH hl) z hzV1).symm⟩
  rw [h.inf_centralizer_eq_bot h13322 C.hMod, Subgroup.mem_bot] at hzL
  exact hz1 hzL

end Ctx764

end CFSG.Quasithin.H13.L32A
