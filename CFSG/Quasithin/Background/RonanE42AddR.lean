module

public import CFSG.Quasithin.Background.RonanE42Gen
public import CFSG.Quasithin.Background.RonanE42Idx2
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.Quasithin.RonanE42.Gen

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42 CFSG.Quasithin.RonanE42.Gen

variable {G : Type} [Group G] [Finite G]

abbrev bk (T H : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.normalizer ((T ⊓ fStarPre H : Subgroup G) : Set G)

theorem fStarPre_le' (H : Subgroup G) : fStarPre H ≤ H := Subgroup.map_subtype_le _

theorem fStarPre_conj_mem (H : Subgroup G) :
    ∀ h ∈ H, ∀ x ∈ fStarPre H, h * x * h⁻¹ ∈ fStarPre H := by
  intro h hh x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  haveI hFchar : (fStarMod H).Characteristic := by
    rw [fStarMod, CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.characteristic _
  haveI : ((fStarMod H).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).Normal :=
    Subgroup.Normal.comap inferInstance _
  refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
    (inferInstance : ((fStarMod H).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).Normal).conj_mem
      y hy _, ?_⟩
  simp

theorem sylow_of_le {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) : IsSylowIn 2 T H := by
  have hdiv : T.relIndex H ∣ T.relIndex ⊤ :=
    ⟨_, (Subgroup.relIndex_mul_relIndex T H ⊤ hTH le_top).symm⟩
  exact ⟨hTH, hT.isPGroup, fun h => hT.not_dvd_relIndex (h.trans hdiv)⟩

theorem le_sup_bk {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) :
    H ≤ fStarPre H ⊔ bk T H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := fStarPre H with hX
  have hXH : X ≤ H := fStarPre_le' H
  have hTH2 : IsSylowIn 2 T H := sylow_of_le hT hTH
  haveI : Finite (Sylow 2 H) :=
    Finite.of_injective (fun P : Sylow 2 H => (P : Set H)) SetLike.coe_injective
  obtain ⟨PH, hPH⟩ : ∃ P : Sylow 2 H, (P : Subgroup H) = T.subgroupOf H :=
    ⟨hTH2.toSylow, IsSylowIn.coe_toSylow hTH2⟩
  have hXn : (X.subgroupOf H).Normal :=
    ⟨fun y hy h => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      simpa using fStarPre_conj_mem H h h.2 y hy⟩
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PH hXn.isSubnormal
  have hN := Sylow.normalizer_sup_eq_top P'
  rw [hP'] at hN
  intro x hx
  have hmem : (⟨x, hx⟩ : H) ∈ Subgroup.normalizer
      (((PH : Subgroup H) ⊓ X.subgroupOf H : Subgroup H) : Set H) ⊔ X.subgroupOf H := by
    rw [hN]; exact Subgroup.mem_top _
  obtain ⟨h, hh, m, hm, hhm⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hxe : x = (h : G) * (m : G) := (congrArg Subtype.val hhm).symm
  have hb : (h : G) ∈ bk T H := by
    refine ⟨h.2, ?_⟩
    show (h : G) ∈ Subgroup.normalizer ((T ⊓ fStarPre H : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyH : y ∈ H := hTH hy.1
      have h1 : (⟨y, hyH⟩ : H) ∈ (PH : Subgroup H) ⊓ X.subgroupOf H :=
        ⟨by rw [hPH]; exact hy.1, hy.2⟩
      have h2 := ((Subgroup.mem_normalizer_iff.1 hh) _).1 h1
      rw [hPH] at h2
      exact ⟨h2.1, h2.2⟩
    · intro hy
      have hyH : y ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem h.2) (hTH hy.1)) h.2
        simpa [mul_assoc] using this
      have hc : h * (⟨y, hyH⟩ : H) * h⁻¹ ∈ (PH : Subgroup H) ⊓ X.subgroupOf H := by
        rw [hPH]; exact ⟨hy.1, hy.2⟩
      have h2 := ((Subgroup.mem_normalizer_iff.1 hh) ⟨y, hyH⟩).2 hc
      rw [hPH] at h2
      exact ⟨h2.1, h2.2⟩
  have hm' : (m : G) ∈ X := hm
  rw [hxe, sup_comm]
  exact Subgroup.mul_mem_sup hb hm'

theorem pCoreOf_conj_mem (H : Subgroup G) :
    ∀ h ∈ H, ∀ x ∈ pCoreOf 2 H, h * x * h⁻¹ ∈ pCoreOf 2 H := by
  intro h hh x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥H)).conj_mem y hy _, by simp⟩

theorem le_bk {T H : Subgroup G} (hTH : T ≤ H) : T ≤ bk T H := by
  intro t ht
  refine ⟨hTH ht, ?_⟩
  show t ∈ Subgroup.normalizer ((T ⊓ fStarPre H : Subgroup G) : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨T.mul_mem (T.mul_mem ht hy1) (T.inv_mem ht),
      fStarPre_conj_mem H t (hTH ht) y hy2⟩
  · rintro ⟨hy1, hy2⟩
    have e : y = t⁻¹ * (t * y * t⁻¹) * t := by group
    refine ⟨?_, ?_⟩
    · rw [e]; exact T.mul_mem (T.mul_mem (T.inv_mem ht) hy1) ht
    · have := fStarPre_conj_mem H t⁻¹ (H.inv_mem (hTH ht)) _ hy2
      rw [inv_inv] at this
      rw [e]; exact this

theorem inf_le_pCoreOf_bk {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H) :
    T ⊓ fStarPre H ≤ pCoreOf 2 (bk T H) := by
  set B := bk T H
  have hSB : T ⊓ fStarPre H ≤ B := inf_le_left.trans (le_bk hTH)
  have hn : ((T ⊓ fStarPre H).subgroupOf B).Normal :=
    ⟨fun y hy b => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have := (Subgroup.mem_normalizer_iff.1 b.2.2 (y : G)).1 hy
      simpa using this⟩
  have hp : IsPGroup 2 ((T ⊓ fStarPre H).subgroupOf B) :=
    (hT.isPGroup.to_inf_left).of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
  have hle : (T ⊓ fStarPre H).subgroupOf B ≤ CFSG.pCore 2 ↥B := by
    unfold CFSG.pCore; exact le_sSup ⟨hn, hp⟩
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hSB hx⟩, hle hx, rfl⟩

theorem bk_good {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hidx : (T ⊓ fStarPre H).relIndex T = 2)
    {Y : Subgroup G} (hY : Y ≤ bk T H) (hYn : ∀ h ∈ bk T H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hYT : ¬ (Y ⊓ T ≤ pCoreOf 2 (bk T H))) :
    bk T H ≤ Subgroup.normalizer (T : Set G) ⊔ (T ⊔ Y) := by
  set B := bk T H
  have hTB : T ≤ B := le_bk hTH
  have hRT : pCoreOf 2 B ≤ T := pCoreOf_le_of_sylow hT hTB
  have hSR : T ⊓ fStarPre H ≤ pCoreOf 2 B := inf_le_pCoreOf_bk hT hTH
  have hdvd : (pCoreOf 2 B).relIndex T ∣ 2 := by
    have := Subgroup.relIndex_dvd_of_le_left T hSR
    rwa [hidx] at this
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  ·
    have hTR : T ≤ pCoreOf 2 B := Subgroup.relIndex_eq_one.mp h1
    have hRe : pCoreOf 2 B = T := le_antisymm hRT hTR
    intro b hb
    refine Subgroup.mem_sup_left ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have := pCoreOf_conj_mem B b hb y (hRe ▸ hy)
      rwa [hRe] at this
    · intro hy
      have := pCoreOf_conj_mem B b⁻¹ (B.inv_mem hb) _ (hRe ▸ hy)
      rw [hRe, inv_inv] at this
      have e : b⁻¹ * (b * y * b⁻¹) * b = y := by group
      rwa [e] at this
  · exact CFSG.Quasithin.RonanE42.Gen.good_of_relIndex_two hT hTB h2 hY hYn hYT

theorem bk_rank {T H : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTH : T ≤ H)
    (hidx : (T ⊓ fStarPre H).relIndex T = 2) : iRank (bk T H) ≤ 1 := by
  classical
  set B := bk T H
  have hTB : T ≤ B := le_bk hTH
  have hRT : pCoreOf 2 B ≤ T := pCoreOf_le_of_sylow hT hTB
  have hSR : T ⊓ fStarPre H ≤ pCoreOf 2 B := inf_le_pCoreOf_bk hT hTH
  have hdvd : (pCoreOf 2 B).relIndex T ∣ 2 := by
    have := Subgroup.relIndex_dvd_of_le_left T hSR
    rwa [hidx] at this
  have hTB2 : IsSylowIn 2 T B := sylow_of_le hT hTB
  have hodd : ¬ 2 ∣ T.relIndex B := hTB2.not_dvd_relIndex
  have hidxB : (CFSG.pCore 2 ↥B).index = (pCoreOf 2 B).relIndex T * T.relIndex B := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hRT hTB, Subgroup.relIndex]
    congr 1
    exact (Subgroup.comap_map_eq_self_of_injective B.subtype_injective _).symm
  have h4 : ¬ 4 ∣ Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) := by
    rw [← Subgroup.index, hidxB]
    intro h
    obtain ⟨c, hc⟩ := hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 ⟨c, hc⟩ with h1 | h2
    · rw [h1, one_mul] at h
      obtain ⟨c', hc'⟩ := h
      exact hodd ⟨2 * c', by omega⟩
    · rw [h2] at h
      obtain ⟨c', hc'⟩ := h
      exact hodd ⟨c', by omega⟩
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hk⟩
  by_contra hk1
  apply h4
  have h2 : 4 ∣ Nat.card E := by
    rw [hk, show (4:ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 (by omega : 2 ≤ k)
  exact h2.trans (Subgroup.card_subgroup_dvd_card E)

end CFSG.Quasithin.RonanE42.Gen
