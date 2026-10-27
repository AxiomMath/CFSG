module

public import CFSG.RankThree.GF2n.Tim77.Cor2Beta
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaLift
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaBender
import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem cor2Beta_c1_isComponentOf_map {H N K : Subgroup G} [N.Normal]
    (hN : N = CFSG.Goldschmidt.oddCoreOf H) (hK : IsComponentOf K H) :
    IsComponentOf (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) := by
  set N' : Subgroup ↥H := CFSG.Open.goldschmidtOddCore ↥H with hN'
  have hN'odd : Odd (Nat.card N') := odd_card_goldschmidtOddCore ↥H
  set ρ : ↥H →* ↥H ⧸ N' := QuotientGroup.mk' N' with hρ
  obtain ⟨ψ, hψinj, hrange, hψcomp⟩ := cor2Beta_exists_psi H N hN
  have hmapψ : ((K.subgroupOf H).map ρ).map ψ = K.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_map, hψcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hK.1]
  have h1 : CFSG.IsComponent ((K.subgroupOf H).map ρ) :=
    CFSG.LocalAnalysis.ComponentInitial.component_quotient_image
      ((cor2Beta_isComponentOf_iff hK.1).mp hK)
      (cor2Beta_component_not_le_odd hN'odd ((cor2Beta_isComponentOf_iff hK.1).mp hK))
  have h2 := cor2Beta_isComponentOf_map_injective ψ hψinj h1
  rwa [hmapψ, hrange] at h2

theorem cor2Beta_c3_component_centralizes {H N K : Subgroup G} [N.Normal]
    (hN : N = CFSG.Goldschmidt.oddCoreOf H) (hK : IsComponentOf K H) :
    ∀ k ∈ K, ∀ n ∈ N, k * n = n * k := by
  have hN'odd : Odd (Nat.card (CFSG.Open.goldschmidtOddCore ↥H)) :=
    odd_card_goldschmidtOddCore ↥H
  intro k hk n hn
  rw [hN] at hn
  obtain ⟨n', hn', rfl⟩ := hn
  have h := cor2Beta_component_commute_odd hN'odd ((cor2Beta_isComponentOf_iff hK.1).mp hK)
  have hmem := Subgroup.commutator_mem_commutator
    (show (⟨k, hK.1 hk⟩ : ↥H) ∈ K.subgroupOf H from hk) hn'
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem cor2Beta_normalizesComponent_of (hB4 : Cor2BetaComponentDataStatement) :
    Cor2BetaNormalizesComponentStatement := by
  intro G _ _ S t hs E Y _ a haH hac K hK
  classical
  set H : Subgroup G := normalClosure ({t} : Set G) with hH
  haveI hHn : H.Normal := inferInstance
  set N : Subgroup G := CFSG.Goldschmidt.oddCoreOf H with hNdef
  haveI hNn : N.Normal := oddCoreOf_normal hHn
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hKbar : IsComponentOf (K.map π) (H.map π) := cor2Beta_c1_isComponentOf_map rfl hK
  obtain ⟨-, V, hVK, hVW, hV4, hVnc⟩ := @hB4 G _ _ S t hs N hNn rfl (K.map π) hKbar
  haveI := hV4
  obtain ⟨v, -, hv1, -, -⟩ := cor2Beta_kleinFour_two (X := ↥V)
  have hv1' : (v : G ⧸ N) ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨w, hwW, hwv⟩ := hVW v.2
  obtain ⟨k, hkK, hkv⟩ := hVK v.2
  obtain ⟨y₀, hy₀, hy₀v⟩ := hVnc v v.2 hv1'
  by_cases hKa : K.map (MulAut.conj a).toMonoidHom = K
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKa
  exfalso
  have hK' := CFSG.Goldschmidt.G310.isComponentOf_conj hHn hK a
  have hcomm := cor2Beta_components_commute hK' hK hKa
  have hwa : a * w * a⁻¹ = w := by rw [hac w hwW]; group
  have hav : π a * (v : G ⧸ N) * (π a)⁻¹ = v := by
    rw [← hwv, ← map_inv, ← map_mul, ← map_mul, hwa]
  obtain ⟨y, hyK, hyy₀⟩ := hy₀
  apply hy₀v
  have hk' : π (a * k * a⁻¹) = v := by
    rw [map_mul, map_mul, map_inv, hkv, hav]
  have hc : (a * k * a⁻¹) * y = y * (a * k * a⁻¹) := hcomm _ ⟨k, hkK, rfl⟩ y hyK
  rw [← hyy₀, ← hk', ← map_mul, ← map_mul, hc]


theorem cor2Beta_c3_mem_center {K : Subgroup G} {z : ↥K} :
    z ∈ Subgroup.center ↥K ↔ ∀ k ∈ K, (z : G) * k = k * z := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h k hk
    exact (congrArg Subtype.val (h ⟨k, hk⟩)).symm
  · intro h g
    exact Subtype.ext (h g g.2).symm

theorem cor2Beta_c3_central_commute {H E Y K : Subgroup G} (hd : Cor2BetaDecomp H E Y)
    (hK : IsComponentOf K H) {z : G} (hzK : z ∈ K) (hz : ∀ k ∈ K, z * k = k * z) :
    ∀ h ∈ H, z * h = h * z := by
  have hKE : K ≤ E := hd.E_eq ▸ le_sSup hK
  have hzE : E ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hd.E_eq]
    refine sSup_le fun L hL x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hLK : L = K
    · subst hLK
      exact (hz x hx).symm
    · exact (cor2Beta_components_commute hK hL (fun h => hLK h.symm) z hzK x hx).symm
  have hzY : Y ≤ Subgroup.centralizer ({z} : Set G) := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hd.comm z (hKE hzK) y hy).symm
  intro h hh
  have := Subgroup.mem_centralizer_singleton_iff.mp (sup_le hzE hzY (hd.sup_eq ▸ hh))
  exact this.symm

theorem cor2Beta_c3_conj_wcl {t a x ζ : G}
    (hac : ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, a * w = w * a)
    (hstar : ∀ g : G, a * (g * t * g⁻¹) = (g * t * g⁻¹) * a →
      g * t * g⁻¹ ∈ CFSG.LargeExtraspecial.S11.wcl t)
    (hax : a * x * a⁻¹ = x * ζ) (hζ : ∀ h ∈ normalClosure ({t} : Set G), ζ * h = h * ζ) :
    ∀ w ∈ CFSG.LargeExtraspecial.S11.wcl t, x * w * x⁻¹ ∈ CFSG.LargeExtraspecial.S11.wcl t := by
  have hle : CFSG.LargeExtraspecial.S11.wcl t ≤
      (CFSG.LargeExtraspecial.S11.wcl t).comap (MulAut.conj x).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨m, hm, hc⟩
    have hyW : y ∈ CFSG.LargeExtraspecial.S11.wcl t :=
      CFSG.LargeExtraspecial.S11.subset_wcl t ⟨m, hm, hc⟩
    have hyH : y ∈ normalClosure ({t} : Set G) := cor2Beta_wcl_le_normalClosure t hyW
    have hζy : ζ * y * ζ⁻¹ = y := by rw [hζ y hyH]; group
    have hay : a * y * a⁻¹ = y := by rw [hac y hyW]; group
    have key : a * (x * y * x⁻¹) * a⁻¹ = x * y * x⁻¹ := by
      calc a * (x * y * x⁻¹) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) * (a * x * a⁻¹)⁻¹ := by group
        _ = (x * ζ) * y * (x * ζ)⁻¹ := by rw [hax, hay]
        _ = x * (ζ * y * ζ⁻¹) * x⁻¹ := by group
        _ = x * y * x⁻¹ := by rw [hζy]
    have e : x * m * t * (x * m)⁻¹ = x * y * x⁻¹ := by rw [hm]; group
    have hg := hstar (x * m) (by rw [e]; exact mul_inv_eq_iff_eq_mul.mp key)
    rw [e] at hg
    exact hg
  intro w hw
  exact hle hw

section InnerOfBender


theorem cor2Beta_c3_exists_inner {Q : Type} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (Q ⧸ Subgroup.center Q)) {τ : MulAut Q}
    (hτ : τ * τ = 1) {s : Q} (hs1 : s ∉ Subgroup.center Q) (hs2 : s * s ∈ Subgroup.center Q)
    (hτs : s⁻¹ * τ s ∈ Subgroup.center Q)
    (hstar : ∀ x : Q, x⁻¹ * τ x ∈ Subgroup.center Q → ⁅x * s * x⁻¹, s⁆ ∈ Subgroup.center Q) :
    ∃ g : Q, ∀ x : Q, τ x = g * x * g⁻¹ := by
  classical
  suffices h : CFSG.RankThree.PartTwo.KFacts.IsInnerAut τ by
    obtain ⟨g, hg⟩ := h
    exact ⟨g, fun x => (congrArg (fun φ : MulAut Q => φ x) hg).symm⟩
  refine CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_isInnerAut_centerDescend ?_
  by_contra hout
  refine cor2Beta_outer_excluded hB (CFSG.RankThree.PartTwo.KFacts.centerDescend Q τ) ?_ ?_
    (s := (s : Q ⧸ Subgroup.center Q)) ?_ ?_ ?_ ?_
  · rw [← map_mul, hτ, map_one]
  · rintro ⟨g, hg⟩
    exact hout ⟨g, MulEquiv.ext fun x => (hg x).symm⟩
  · exact fun h => hs1 ((QuotientGroup.eq_one_iff s).mp h)
  · rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hs2
  · rw [CFSG.RankThree.PartTwo.KFacts.centerDescend_mk]
    exact (QuotientGroup.eq.mpr hτs).symm
  · intro x hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [CFSG.RankThree.PartTwo.KFacts.centerDescend_mk] at hx
      have h1 := (QuotientGroup.eq_one_iff _).mpr (hstar x (QuotientGroup.eq.mp hx.symm))
      have h2 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center Q)) (x * s * x⁻¹) s
      rw [QuotientGroup.mk'_apply, h1] at h2
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
      exact commutatorElement_eq_one_iff_mul_comm.mp h2.symm

theorem cor2Beta_c3_exists_inner_sub {K : Subgroup G} [Group.IsPerfect ↥K]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (↥K ⧸ Subgroup.center ↥K)) {a : G}
    (haK : a ∈ normalizer (K : Set G)) (ha2 : a * a = 1) {s : G} (hsK : s ∈ K)
    (hs1 : ¬ ∀ k ∈ K, s * k = k * s) (hs2 : ∀ k ∈ K, (s * s) * k = k * (s * s))
    (hτs : ∀ k ∈ K, (s⁻¹ * (a * s * a⁻¹)) * k = k * (s⁻¹ * (a * s * a⁻¹)))
    (hstar : ∀ x ∈ K, (∀ k ∈ K, (x⁻¹ * (a * x * a⁻¹)) * k = k * (x⁻¹ * (a * x * a⁻¹))) →
      ∀ k ∈ K, ⁅x * s * x⁻¹, s⁆ * k = k * ⁅x * s * x⁻¹, s⁆) :
    ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹ := by
  classical
  set τ : MulAut ↥K := K.normalizerMonoidHom ⟨a, haK⟩ with hτdef
  have hτx : ∀ x : ↥K, (τ x : G) = a * x * a⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨a, haK⟩ x
  have hττ : τ * τ = 1 := by
    ext x
    rw [MulAut.mul_apply, MulAut.one_apply]
    rw [hτx, hτx]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [ha2]; group
  have hs1' : (⟨s, hsK⟩ : ↥K) ∉ Subgroup.center ↥K := fun h =>
    hs1 fun k hk => (cor2Beta_c3_mem_center.mp h) k hk
  have hs2' : (⟨s, hsK⟩ : ↥K) * ⟨s, hsK⟩ ∈ Subgroup.center ↥K :=
    cor2Beta_c3_mem_center.mpr fun k hk => hs2 k hk
  have hτs' : (⟨s, hsK⟩ : ↥K)⁻¹ * τ ⟨s, hsK⟩ ∈ Subgroup.center ↥K :=
    cor2Beta_c3_mem_center.mpr fun k hk => by
      simpa [hτx] using hτs k hk
  have hstar' : ∀ x : ↥K, x⁻¹ * τ x ∈ Subgroup.center ↥K →
      ⁅x * ⟨s, hsK⟩ * x⁻¹, ⟨s, hsK⟩⁆ ∈ Subgroup.center ↥K := by
    intro x hx
    refine cor2Beta_c3_mem_center.mpr fun k hk => ?_
    have hx' := cor2Beta_c3_mem_center.mp hx
    have := hstar x x.2 (fun k' hk' => by simpa [hτx] using hx' k' hk') k hk
    simpa [commutatorElement_def] using this
  obtain ⟨g, hg⟩ := cor2Beta_c3_exists_inner hB hττ hs1' hs2' hτs' hstar'
  refine ⟨g, g.2, fun x hx => ?_⟩
  have := congrArg Subtype.val (hg ⟨x, hx⟩)
  rw [hτx] at this
  simpa using this

theorem cor2Beta_innerOnComponent_of (hB4 : Cor2BetaComponentDataStatement)
    (hC1 : Cor2BetaNormalizesComponentStatement) : Cor2BetaInnerOnComponentStatement := by
  intro G _ _ S t hs E Y hd a ha2 haH hac hstar K hK
  classical
  set H : Subgroup G := normalClosure ({t} : Set G) with hH
  haveI hHn : H.Normal := inferInstance
  set N : Subgroup G := CFSG.Goldschmidt.oddCoreOf H with hNdef
  haveI hNn : N.Normal := oddCoreOf_normal hHn
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have haK : a ∈ normalizer (K : Set G) := hC1 G hs hd haH hac hK
  have hKN : ∀ k ∈ K, ∀ n ∈ N, k * n = n * k := cor2Beta_c3_component_centralizes rfl hK
  have hKbar : IsComponentOf (K.map π) (H.map π) := cor2Beta_c1_isComponentOf_map rfl hK
  obtain ⟨hBen, V, hVK, hVW, hV4, hVnc⟩ := @hB4 G _ _ S t hs N hNn rfl (K.map π) hKbar
  haveI : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
  have hker : (π.subgroupMap K).ker ≤ Subgroup.center ↥K := by
    rw [Subgroup.ker_subgroupMap, hπ, QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hKN g.1 g.2 x.1 hx)
  obtain ⟨e⟩ := cor2Beta_quotient_center_equiv (π.subgroupMap K) (π.subgroupMap_surjective K) hker
  have hB : CFSG.BenderSuzuki.IsBenderGroup (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.Timmesfeld.Bridge.Asc72.isBenderGroup_of_mulEquiv e hBen
  haveI := hV4
  obtain ⟨v, -, hv1, -, -⟩ := cor2Beta_kleinFour_two (X := ↥V)
  have hv1' : (v : G ⧸ N) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvv : (v : G ⧸ N) * v = 1 := by
    have h := mul_inv_cancel v
    rw [IsKleinFour.inv_eq_self v] at h
    exact congrArg Subtype.val h
  obtain ⟨w, hwW, hwv'⟩ := hVW v.2
  have hwv : π w = (v : G ⧸ N) := hwv'
  obtain ⟨s, hsK, hsv⟩ := hVK v.2
  have hwa : a * w * a⁻¹ = w := by rw [hac w hwW]; group
  have hav : π a * (v : G ⧸ N) * (π a)⁻¹ = v := by
    rw [← hwv, ← map_inv, ← map_mul, ← map_mul, hwa]
  have hN1 : ∀ z : G, π z = 1 → ∀ k ∈ K, z * k = k * z := fun z hz k hk =>
    (hKN k hk z ((QuotientGroup.eq_one_iff z).mp hz)).symm
  refine cor2Beta_c3_exists_inner_sub hB haK ha2 hsK ?_ ?_ ?_ ?_
  ·
    intro h
    obtain ⟨y₀, ⟨y, hyK, rfl⟩, hy₀⟩ := hVnc v v.2 hv1'
    apply hy₀
    rw [← hsv, ← map_mul, ← map_mul, h y hyK]
  · intro k hk
    exact hN1 _ (by rw [map_mul, hsv]; exact hvv) k hk
  · intro k hk
    exact hN1 _ (by simp only [map_mul, map_inv, hsv, hav, inv_mul_cancel]) k hk
  · intro x hxK hζ k hk
    have haxK : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haK x).mp hxK
    have hζK : x⁻¹ * (a * x * a⁻¹) ∈ K := K.mul_mem (K.inv_mem hxK) haxK
    have hζH := cor2Beta_c3_central_commute hd hK hζK hζ
    have hxW := cor2Beta_c3_conj_wcl hac hstar (x := x) (ζ := x⁻¹ * (a * x * a⁻¹)) (by group) hζH
    have hxwW := hxW w hwW
    have hcomm : (x * w * x⁻¹) * w = w * (x * w * x⁻¹) :=
      congrArg Subtype.val (hs.abelian.is_comm.comm ⟨_, hxwW⟩ ⟨_, hwW⟩)
    refine hN1 _ ?_ k hk
    have h1 : π (x * s * x⁻¹) = π (x * w * x⁻¹) := by
      simp only [map_mul, map_inv, hsv, hwv]
    rw [map_commutatorElement, h1, hsv, ← hwv, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr hcomm, map_one]

theorem tim77BetaBox_of_componentData (hGold : Goldschmidt1974)
    (hB4 : Cor2BetaComponentDataStatement) : Tim77BetaBox :=
  tim77BetaBox_of_nodes (cor2Beta_shultDecomp_of hGold hB4)
    (cor2Beta_innerOnComponent_of hB4 (cor2Beta_normalizesComponent_of hB4))

end InnerOfBender

end CFSG.RankThree.GF2n.Tim77
