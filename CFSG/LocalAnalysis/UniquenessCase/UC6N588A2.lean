module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588A

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

section Transport

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem pRank_map_subtype (hp : 1 < p) (K : Subgroup G) (H : Subgroup K) :
    CFSG.Open.pRank p (H.map K.subtype) = CFSG.Open.pRank p H := by
  apply le_antisymm
  · obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp (H.map K.subtype)
    have hEK : E ≤ K := hEH.trans (Subgroup.map_subtype_le H)
    refine CFSG.SectionRank.le_pRank hp (E := E.subgroupOf K) ?_ ?_ ?_
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hEH hx
      have hxy : y = x := Subtype.ext hyx
      exact hxy ▸ hy
    · have hc := hE.1
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have := congrArg Subtype.val
          (mul_comm' (⟨((a : K) : G), a.2⟩ : E) ⟨((b : K) : G), b.2⟩)
        apply Subtype.ext
        apply Subtype.ext
        simpa using this
      · apply Subtype.ext
        simpa using hE.2 _ hx
    · rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  · exact CFSG.SectionRank.pRank_le_map hp K.subtype K.subtype_injective H

theorem card_map_of_injOn {G' : Type} [Group G'] (f : G →* G') {H : Subgroup G}
    (hf : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  have hinj : Function.Injective (f.comp H.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (Subtype.ext (hf x x.2 (MonoidHom.mem_ker.mp hx)))
  have hrange : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem pRank_le_pRank_map {G' : Type} [Group G'] [Finite G'] (hp : 1 < p) (f : G →* G')
    (H : Subgroup G) (hf : ∀ E : Subgroup G, E ≤ H → CFSG.Open.IsElemAbelian p E →
      ∀ x ∈ E, f x = 1 → x = 1) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map f) := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp H
  refine CFSG.SectionRank.le_pRank hp (Subgroup.map_mono hEH)
    (CFSG.SectionRank.isElemAbelian_map hE f) ?_
  rw [card_map_of_injOn f (hf E hEH hE), hcard]

theorem inf_eq_bot_of_coprime [Fact p.Prime] {E N : Subgroup G} (hE : IsPGroup p E)
    (hN : Nat.Coprime p (Nat.card N)) : E ⊓ N = ⊥ := by
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  exact (Subgroup.disjoint_of_coprime_natCard (by rw [hk]; exact hN.pow_left k)).eq_bot

theorem map_conjugate {G' : Type} [Group G'] (f : G →* G') (H : Subgroup G) (g : G) :
    (CFSG.conjugate H g).map f = CFSG.conjugate (H.map f) (f g) := by
  ext x
  rw [mem_conjugate_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, mem_conjugate_iff.mp hy, by simp [map_mul, map_inv]⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨g⁻¹ * y * g, mem_conjugate_iff.mpr (by simpa [mul_assoc] using hy), ?_⟩
    rw [map_mul, map_mul, map_inv, hyx]
    group

theorem exists_isSylowOf_ge_of_le [Fact p.Prime] {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨P, hP⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun x hx => ⟨⟨x, hQK hx⟩, hP hx, rfl⟩⟩

end Transport

namespace Hyp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {S Z : Subgroup G}

theorem conjugate_eq_of_mem (h : Hyp G p S Z) {s : G} (hs : s ∈ S) : CFSG.conjugate Z s = Z := by
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro hx
    have hc := h.comm hx hs
    have e : x = s⁻¹ * ((s * x * s⁻¹) * s) := by group
    rw [e, hc, inv_mul_cancel_left]
    exact hx
  · intro hx
    rw [← h.comm hx hs, mul_inv_cancel_right]
    exact hx

theorem subgroup (h : Hyp G p S Z) (Y : Subgroup G) (hZY : Z ≤ Y) :
    ∃ SY : Subgroup Y, Hyp Y p SY (Z.subgroupOf Y) := by
  haveI := h.fact
  have hZ'p : IsPGroup p (Z.subgroupOf Y) := h.isPGroup.comap_subtype
  obtain ⟨P, hP⟩ := hZ'p.exists_le_sylow
  have hQp : IsPGroup p ((P : Subgroup Y).map Y.subtype) := P.isPGroup'.map _
  obtain ⟨g, hg⟩ := exists_le_conjugate h.sylow hQp
  have hPS : ∀ x : Y, x ∈ (P : Subgroup Y) → g * (x : G) * g⁻¹ ∈ S := fun x hx =>
    mem_conjugate_iff.mp (hg ⟨x, hx, rfl⟩)
  refine ⟨P, ⟨h.isKGroup.subgroup Y, h.prime, h.five_le, isSylowOf_top_of_sylow P, ?_, ?_, hP,
    ?_, ?_⟩⟩
  · intro x hx hxp y hy
    have hxp1 : (x : G) ^ p = 1 := by simpa using congrArg Subtype.val hxp
    have hxp' : (g * (x : G) * g⁻¹) ^ p = 1 := by
      rw [conj_pow, hxp1, mul_one, mul_inv_cancel]
    have hc := h.omega _ (hPS x hx) hxp' _ (hPS y hy)
    apply Subtype.ext
    have e : g * ((x : G) * y) * g⁻¹ = g * ((y : G) * x) * g⁻¹ := by
      calc g * ((x : G) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := hc
        _ = g * ((y : G) * x) * g⁻¹ := by group
    simpa using mul_left_cancel (mul_right_cancel e)
  · rw [← pRank_map_subtype h.prime.one_lt Y]
    exact h.pRank_le_three _
  · rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  · intro y hy
    have hZQ : Z ≤ (P : Subgroup Y).map Y.subtype := fun z hz => ⟨⟨z, hZY hz⟩, hP hz, rfl⟩
    have hyQ : CFSG.conjugate Z (y : G) ≤ (P : Subgroup Y).map Y.subtype := by
      intro x hx
      have hxZ : (y : G) * x * (y : G)⁻¹ ∈ Z := mem_conjugate_iff.mp hx
      have hxY : x ∈ Y := by
        have e : x = (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * y := by group
        rw [e]
        exact Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) (hZY hxZ)) y.2
      refine ⟨⟨x, hxY⟩, hy (mem_conjugate_iff.mpr ?_), rfl⟩
      rw [Subgroup.mem_subgroupOf]
      simpa using hxZ
    have heq := h.conjugate_eq_of_le_isPGroup hQp hZQ hyQ
    have key : ∀ w : G, (y : G) * w * (y : G)⁻¹ ∈ Z ↔ w ∈ Z := fun w => by
      rw [← mem_conjugate_iff, heq]
    ext x
    rw [mem_conjugate_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using key x

theorem pRank_normalClosure_subgroup (ih : IHBelow (Nat.card G)) (h : Hyp G p S Z)
    {Y : Subgroup G} (hZY : Z ≤ Y) (hY : Y ≠ ⊤) :
    CFSG.Open.pRank p ((normalClosure ((Z.subgroupOf Y : Subgroup Y) : Set Y)).map Y.subtype) =
      1 := by
  obtain ⟨SY, hSY⟩ := h.subgroup Y hZY
  have hcard : Nat.card Y < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hY)
  rw [pRank_map_subtype h.prime.one_lt]
  exact ih Y hcard p SY (Z.subgroupOf Y) hSY

theorem quotient (h : Hyp G p S Z) (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) :
    Hyp (G ⧸ N) p (S.map (QuotientGroup.mk' N)) (Z.map (QuotientGroup.mk' N)) := by
  haveI := h.fact
  obtain ⟨P, hPS⟩ := exists_sylow_of_isSylowOf_top h.sylow
  have hSp : IsPGroup p S := hPS ▸ P.isPGroup'
  have hSN : S ⊓ N = ⊥ := inf_eq_bot_of_coprime hSp hN
  have hker : ∀ x ∈ S, QuotientGroup.mk' N x = 1 → x = 1 := fun x hx h1 => by
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp h1
    have hx' : x ∈ S ⊓ N := ⟨hx, hxN⟩
    rwa [hSN, Subgroup.mem_bot] at hx'
  refine ⟨h.isKGroup.quotient N, h.prime, h.five_le, ?_, ?_, ?_, Subgroup.map_mono h.le, ?_, ?_⟩
  · have hs := isSylowOf_top_of_sylow (P.mapSurjective (QuotientGroup.mk'_surjective N))
    rwa [Sylow.coe_mapSurjective, hPS] at hs
  · rintro _ ⟨x, hx, rfl⟩ hxp _ ⟨y, hy, rfl⟩
    have hxp' : x ^ p = 1 := hker _ (S.pow_mem hx p) (by rw [map_pow]; exact hxp)
    rw [← map_mul, ← map_mul, h.omega x hx hxp' y hy]
  · calc CFSG.Open.pRank p (S.map (QuotientGroup.mk' N))
          ≤ CFSG.Open.pRank p (⊤ : Subgroup (G ⧸ N)) :=
          CFSG.SectionRank.pRank_mono h.prime.one_lt le_top
      _ = CFSG.Open.pRank p (⊤ : Subgroup G) :=
          CFSG.SectionRank.pRank_quotient_eq N ((Nat.Prime.coprime_iff_not_dvd h.prime).mp hN)
      _ ≤ 3 := h.pRank_le_three ⊤
  · rw [card_map_of_injOn _ (fun x hx => hker x (h.le hx)), h.card]
  · intro gbar hgbar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    have hle : CFSG.conjugate Z g ≤ S ⊔ N := by
      intro x hx
      have hfx : QuotientGroup.mk' N x ∈ S.map (QuotientGroup.mk' N) := by
        apply hgbar
        rw [mem_conjugate_iff, ← map_inv, ← map_mul, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (mem_conjugate_iff.mp hx)
      have hx' : x ∈ (S.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hfx
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx'
    have hSSN : IsSylowOf p S (S ⊔ N) := h.sylow.of_le le_sup_left le_top
    obtain ⟨Q, hQ, hZgQ⟩ := exists_isSylowOf_ge_of_le hle (h.isPGroup.map _)
    obtain ⟨k, hk, hkQ⟩ := hSSN.exists_mem_conj hQ
    have h1 : CFSG.conjugate Z (g * k) = Z := by
      apply h.wc
      intro x hx
      rw [mem_conjugate_iff] at hx
      have hx' : k * x * k⁻¹ ∈ CFSG.conjugate Z g := by
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hx
      have hS := (hkQ _).mp (hZgQ hx')
      simpa [mul_assoc] using hS
    have h2 : CFSG.conjugate Z g = CFSG.conjugate Z k⁻¹ := by
      have e := congrArg (fun H => CFSG.conjugate H k⁻¹) h1
      simpa only [conjugate_conjugate, mul_inv_cancel_right] using e
    have hk' : k ∈ ((S ⊔ N : Subgroup G) : Set G) := hk
    rw [Subgroup.mul_normal] at hk'
    obtain ⟨s, hs, n, hn, rfl⟩ := hk'
    have hfn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [← map_conjugate, h2, map_conjugate, map_inv, map_mul, hfn, mul_one, ← map_inv,
      ← map_conjugate, h.conjugate_eq_of_mem (S.inv_mem hs)]

theorem concl_of_pPrimeCore_ne_bot (ih : IHBelow (Nat.card G)) (h : Hyp G p S Z)
    (hcore : CFSG.pPrimeCore p G ≠ ⊥) : CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 := by
  haveI := h.fact
  have hNc : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p G)) := CFSG.pPrimeCore_coprime_card
  have hq := h.quotient (CFSG.pPrimeCore p G) hNc
  have hcard : Nat.card (G ⧸ CFSG.pPrimeCore p G) < Nat.card G := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore p G)
    have h2 : 1 < Nat.card (CFSG.pPrimeCore p G) :=
      (Subgroup.one_lt_card_iff_ne_bot (CFSG.pPrimeCore p G)).mpr hcore
    have h3 : 0 < Nat.card (G ⧸ CFSG.pPrimeCore p G) := Nat.card_pos
    nlinarith
  have hih := ih _ hcard p _ _ hq
  rw [Subgroup.coe_map,
    ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective (CFSG.pPrimeCore p G))] at hih
  refine h.concl_of_le ?_
  rw [← hih]
  apply pRank_le_pRank_map h.prime.one_lt
  intro E _ hE x hx h1
  have hEN := inf_eq_bot_of_coprime (isPGroup_of_isElemAbelian hE) hNc
  have hx' : x ∈ E ⊓ CFSG.pPrimeCore p G := ⟨hx, (QuotientGroup.eq_one_iff x).mp h1⟩
  rwa [hEN, Subgroup.mem_bot] at hx'

end Hyp

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588A
