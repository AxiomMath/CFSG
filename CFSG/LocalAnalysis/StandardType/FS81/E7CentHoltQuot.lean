module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.ClassicalInvolution.Models.Transfer.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

private theorem fs81Quot_injective {G : Type*} [Group G] (N K : Subgroup G) [N.Normal]
    (hKN : K ⊓ N = ⊥) : ∀ x ∈ K, QuotientGroup.mk' N x = 1 → x = 1 := by
  intro x hx hx1
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hx1
  have h : x ∈ K ⊓ N := ⟨hx, hxN⟩
  rw [hKN] at h
  exact Subgroup.mem_bot.mp h

private theorem fs81Quot_mem_map_mk' {G : Type*} [Group G] (N K : Subgroup G) [N.Normal] (x : G) :
    (QuotientGroup.mk' N x ∈ K.map (QuotientGroup.mk' N)) ↔ x ∈ N ⊔ K := by
  rw [← Subgroup.mem_comap, QuotientGroup.comap_map_mk']

private theorem fs81Quot_isSylow2In_map {G A : Type} [Group G] [Group A] (f : G →* A)
    {N P : Subgroup G} (hf : ∀ x ∈ N, f x = 1 → x = 1) (h : IsSylow2In P N) :
    IsSylow2In (P.map f) (N.map f) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, fun V hVN hV2 hPV => ?_⟩
  let V' : Subgroup G := V.comap f ⊓ N
  have hV'N : V' ≤ N := inf_le_right
  have hPV' : P ≤ V' := fun x hx => ⟨hPV (Subgroup.mem_map_of_mem f hx), h.1 hx⟩
  have hV'2 : IsPGroup 2 ↥V' := by
    let ψ : ↥V' →* ↥V := (f.comp V'.subtype).codRestrict V (fun x => x.2.1)
    refine hV2.of_injective ψ ?_
    intro x y hxy
    apply Subtype.ext
    have h1 : f ((x : G) * (y : G)⁻¹) = 1 := by
      have h2 : f (x : G) = f (y : G) := congrArg Subtype.val hxy
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h3 := hf _ (N.mul_mem (hV'N x.2) (N.inv_mem (hV'N y.2))) h1
    exact mul_inv_eq_one.mp h3
  have hEq : V' = P := h.2.2 V' hV'N hV'2 hPV'
  have hVP : V ≤ P.map f := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := hVN hv
    have hmem : n ∈ V' := ⟨hv, hn⟩
    rw [hEq] at hmem
    exact Subgroup.mem_map_of_mem f hmem
  exact le_antisymm hVP hPV

private theorem fs81HoltQuot_subgroupOf_inf_bot {G : Type*} [Group G] {H K Q : Subgroup G}
    (hKQ : K ⊓ Q = ⊥) : (K.subgroupOf H) ⊓ (Q.subgroupOf H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
  have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
  have h : (x : G) ∈ K ⊓ Q := Subgroup.mem_inf.mpr ⟨hxK, hxQ⟩
  rw [hKQ] at h
  exact Subtype.ext (Subgroup.mem_bot.mp h)

private theorem fs81HoltQuot_isSylow2In_subgroupOf {G : Type} [Group G] {S L H : Subgroup G}
    (hLH : L ≤ H) (h : IsSylow2In S L) :
    IsSylow2In (S.subgroupOf H) (L.subgroupOf H) := by
  have hSH : S ≤ H := h.1.trans hLH
  refine ⟨Subgroup.subgroupOf_mono H h.1, ?_, ?_⟩
  · exact h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  · intro T hTL hT2 hST
    have hT'L : T.map H.subtype ≤ L := by
      rintro x ⟨t, ht, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hTL ht)
    have hST' : S ≤ T.map H.subtype := by
      intro s hs
      have hsH : (⟨s, hSH hs⟩ : ↥H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.mpr hs
      exact Subgroup.mem_map_of_mem H.subtype (hST hsH)
    have hEq : T.map H.subtype = S := h.2.2 _ hT'L (hT2.map H.subtype) hST'
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (by
        have h := Subgroup.mem_map_of_mem H.subtype hx
        rwa [hEq] at h)
    · intro hx
      exact hST hx

private theorem fs81HoltQuot_mem_Lbar {G : Type*} [Group G] {H Q L : Subgroup G}
    [hN : (Q.subgroupOf H).Normal]
    (hQH : Q ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hLH : L ≤ H) (x : ↥H) :
    (QuotientGroup.mk' (Q.subgroupOf H) x ∈
        (L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))) ↔
      (x : G) ∈ Q ⊔ L := by
  rw [← Subgroup.mem_subgroupOf (H := Q ⊔ L), Subgroup.subgroupOf_sup hQH hLH,
    ← fs81Quot_mem_map_mk']

private theorem fs81HoltQuot_control {G : Type*} [Group G] {H Q L : Subgroup G} {z : G}
    [hN : (Q.subgroupOf H).Normal]
    (hQH : Q ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hLH : L ≤ H)
    (hzH : z ∈ H)
    (hctrl : ∀ x ∈ H, x * z * x⁻¹ ∈ L ⊔ Q → x ∈ L ⊔ Q) :
    ∀ g : ↥H ⧸ (Q.subgroupOf H),
      g * QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩ * g⁻¹ ∈
          (L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)) →
        g ∈ (L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)) := by
  intro g hg
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf H) g
  have hg' : QuotientGroup.mk' (Q.subgroupOf H)
      ((x : ↥H) * (⟨z, hzH⟩ : ↥H) * x⁻¹) ∈
        (L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)) := by
    simpa [map_mul, map_inv] using hg
  have hxQ : (x : ↥H) * (⟨z, hzH⟩ : ↥H) * x⁻¹ ∈
      (Q.subgroupOf H) ⊔ L.subgroupOf H :=
    (fs81Quot_mem_map_mk' (Q.subgroupOf H) (L.subgroupOf H) _).mp hg'
  have hxLQ : (x : G) * z * (x : G)⁻¹ ∈ L ⊔ Q := by
    have h1 : ((x * (⟨z, hzH⟩ : ↥H) * x⁻¹ : ↥H) : G) ∈ Q ⊔ L := by
      rw [← Subgroup.subgroupOf_sup hQH hLH] at hxQ
      exact Subgroup.mem_subgroupOf.mp hxQ
    simpa [sup_comm] using h1
  exact (fs81HoltQuot_mem_Lbar hQH hHQ hLH x).mpr (by
    simpa [sup_comm] using hctrl (x : G) x.2 hxLQ)

private theorem fs81HoltQuot_zbar_centralizer {G : Type} [Group G] {H Q S : Subgroup G} {z : G}
    [hN : (Q.subgroupOf H).Normal] (hzH : z ∈ H) (hzc : ∀ s ∈ S, s * z = z * s) :
    ∀ s ∈ (S.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)),
      s * QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩ =
        QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩ * s := by
  rintro s ⟨t, ht, rfl⟩
  have hcomm : (t : ↥H) * (⟨z, hzH⟩ : ↥H) = (⟨z, hzH⟩ : ↥H) * t := by
    apply Subtype.ext
    simpa using hzc _ (Subgroup.mem_subgroupOf.mp ht)
  rw [← map_mul, ← map_mul, hcomm]

private theorem fs81HoltQuot_zbar_order {G : Type} [Group G] {H Q L : Subgroup G} {z : G}
    [hN : (Q.subgroupOf H).Normal] (hLQ : L ⊓ Q = ⊥) (hzL : z ∈ L) (hzH : z ∈ H)
    (hz2 : orderOf z = 2) :
    orderOf (QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩) = 2 := by
  have hzcoe : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H), hz2]
  have hdvd : orderOf (QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩) ∣ 2 := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (Q.subgroupOf H)) (⟨z, hzH⟩ : ↥H)
    rwa [hzcoe] at h
  have hne : orderOf (QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩) ≠ 1 := by
    intro h1
    have hz1 : QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩ = 1 :=
      orderOf_eq_one_iff.mp h1
    have hzQ : z ∈ Q := Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (⟨z, hzH⟩ : ↥H)).mp hz1)
    have hzbot : z ∈ L ⊓ Q := ⟨hzL, hzQ⟩
    rw [hLQ] at hzbot
    have hz1' : z = 1 := Subgroup.mem_bot.mp hzbot
    rw [hz1', orderOf_one] at hz2
    norm_num at hz2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
  · exact absurd h hne
  · exact h

private theorem fs81HoltQuot_lbar_top {G : Type} [Group G] [Finite G]
    {H Q L S : Subgroup G} {z : G} [hN : (Q.subgroupOf H).Normal]
    (h : HoltSimpleControl)
    (hQH : Q ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hLH : L ≤ H)
    (hLQ : L ⊓ Q = ⊥) (hLsimp : IsSimpleGroup ↥L)
    (hnc : ∃ a c : ↥L, a * c ≠ c * a)
    (hcard : ∀ m : ℕ, 2 ≤ m → 2 * Nat.card ↥L ≠ (2 * m).factorial)
    (hSyl : IsSylow2In S L) (hzS : z ∈ S) (hz2 : orderOf z = 2)
    (hzc : ∀ s ∈ S, s * z = z * s)
    (hctrl : ∀ x ∈ H, x * z * x⁻¹ ∈ L ⊔ Q → x ∈ L ⊔ Q) :
    (L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)) = ⊤ := by
  classical
  have hzL : z ∈ L := hSyl.1 hzS
  have hzH : z ∈ H := hLH hzL
  have hLQ' : (L.subgroupOf H) ⊓ (Q.subgroupOf H) = ⊥ :=
    fs81HoltQuot_subgroupOf_inf_bot hLQ
  have hφ : ∀ x ∈ L.subgroupOf H, QuotientGroup.mk' (Q.subgroupOf H) x = 1 → x = 1 :=
    fs81Quot_injective (Q.subgroupOf H) (L.subgroupOf H) hLQ'
  have hSylbar : IsSylow2In ((S.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)))
      ((L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))) :=
    fs81Quot_isSylow2In_map _ hφ (fs81HoltQuot_isSylow2In_subgroupOf hLH hSyl)
  let e : ↥L ≃* ↥((L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))) :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans
      (CFSG.ClassicalInvolution.Models.Transfer.mulEquivMap
        (θ := QuotientGroup.mk' (Q.subgroupOf H)) (L := L.subgroupOf H)
        (fun z hz hzk => hφ z hz (MonoidHom.mem_ker.mp hzk)))
  let zbar : ↥H ⧸ (Q.subgroupOf H) := QuotientGroup.mk' (Q.subgroupOf H) ⟨z, hzH⟩
  have hzbar2 : orderOf zbar = 2 := fs81HoltQuot_zbar_order hLQ hzL hzH hz2
  have hzbarS : zbar ∈ (S.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzS)
  have hzcbar : ∀ s ∈ (S.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)),
      s * zbar = zbar * s := fs81HoltQuot_zbar_centralizer hzH hzc
  have hncbar : ∃ a c : ↥((L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))),
      a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    exact ⟨e a, e c, fun h' => hac (e.injective (by simpa only [map_mul] using h'))⟩
  have hcardbar : ∀ m : ℕ, 2 ≤ m →
      2 * Nat.card ↥((L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))) ≠
        (2 * m).factorial := by
    intro m hm
    rw [← Nat.card_congr e.toEquiv]
    exact hcard m hm
  have hsimpbar : IsSimpleGroup
      ↥((L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H))) :=
    (MulEquiv.isSimpleGroup_congr e).mp hLsimp
  exact h (↥H ⧸ (Q.subgroupOf H)) _ _ zbar hsimpbar hncbar hcardbar hSylbar hzbarS
    hzbar2 hzcbar (fs81HoltQuot_control hQH hHQ hLH hzH hctrl)

theorem fs81HoltQuot_of_holtSimpleControl (h : HoltSimpleControl) : FS81HoltQuot := by
  classical
  intro X _ _ H Q L S z hQH hHQ hLH hLQ hLsimp hnc hcard hSyl hzS hz2 hzc hctrl
  haveI hN : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHQ
  have htop := fs81HoltQuot_lbar_top h hQH hHQ hLH hLQ hLsimp hnc hcard hSyl hzS hz2 hzc hctrl
  intro x hx
  have hmem : QuotientGroup.mk' (Q.subgroupOf H) ⟨x, hx⟩ ∈
      (L.subgroupOf H).map (QuotientGroup.mk' (Q.subgroupOf H)) := by
    rw [htop]
    exact Subgroup.mem_top _
  simpa [sup_comm] using (fs81HoltQuot_mem_Lbar hQH hHQ hLH ⟨x, hx⟩).mp hmem

end CFSG.StandardType.FrameRoute.FS81
