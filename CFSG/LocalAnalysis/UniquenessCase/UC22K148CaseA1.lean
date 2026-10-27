module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22K148CaseA2
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.QuasithinUnique.Setup.Offender (weight commGL)
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem conj_eq_inv_of_card_three {Q : Subgroup G} {b : G} (hQ3 : Nat.card ↥Q = 3)
    (hb2 : b * b = 1) (hbQ : b ∈ Subgroup.normalizer (Q : Set G))
    (hne : ⁅Q, Subgroup.zpowers b⁆ ≠ ⊥) : ∀ q ∈ Q, b * q * b⁻¹ = q⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hQ3]; norm_num)
  have hcyc : IsCyclic ↥Q := isCyclic_of_prime_card hQ3
  have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hcyc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hC : Q ⊓ Subgroup.centralizer {b} = ⊥ := by
    have hdvd : Nat.card ↥(Q ⊓ Subgroup.centralizer {b}) ∣ 3 :=
      hQ3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hne
      have hCQ : Q ⊓ Subgroup.centralizer {b} = Q :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hQ3])
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hqb : q * b = b * q :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hCQ.symm ▸ hq)).2
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact ((Commute.zpow_left hqb.symm n).eq)
  intro q hq
  set c := b * q * b⁻¹ with hc
  have hcQ : c ∈ Q := (Subgroup.mem_normalizer_iff.1 hbQ q).1 hq
  have hbc : b * c * b⁻¹ = q := by
    rw [hc]
    calc b * (b * q * b⁻¹) * b⁻¹ = (b * b) * q * (b * b)⁻¹ := by group
      _ = q := by rw [hb2]; group
  have hconj : b * (q * c) * b⁻¹ = q * c := by
    calc b * (q * c) * b⁻¹ = (b * q * b⁻¹) * (b * c * b⁻¹) := by group
      _ = q * c := by rw [hbc, ← hc, hcomm c hcQ q hq]
  have hmem : q * c ∈ Q ⊓ Subgroup.centralizer {b} := by
    refine Subgroup.mem_inf.2 ⟨Q.mul_mem hq hcQ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc q * c * b = (b * (q * c) * b⁻¹) * b := by rw [hconj]
      _ = b * (q * c) := by group
  rw [hC, Subgroup.mem_bot] at hmem
  exact eq_inv_of_mul_eq_one_right hmem

private theorem le_normalizer_commutator_zpowers_of_commute {K A : Subgroup G} {b : G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hAb : ∀ a ∈ A, a * b = b * a) :
    A ≤ Subgroup.normalizer ((⁅K, Subgroup.zpowers b⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun a ha n hn => ?_
  have hle : ⁅K, Subgroup.zpowers b⁆ ≤
      (⁅K, Subgroup.zpowers b⁆ : Subgroup G).comap (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro k hk z hz
    rw [Subgroup.mem_comap, map_commutatorElement]
    have hz' : (MulAut.conj a).toMonoidHom z = z := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [map_zpow]
      congr 1
      change a * b * a⁻¹ = b
      rw [hAb a ha, mul_inv_cancel_right]
    rw [hz']
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hAK ha) k).1 hk) hz
  exact hle hn

theorem commOn_top_le_commOn_of_odd [Finite V] {K X : Subgroup G} (hXK : X ≤ K)
    (hodd : ∀ x ∈ X, Odd (orderOf x)) : commOn ρ X ⊤ ≤ commOn ρ X (commOn ρ K ⊤) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, v, -, rfl⟩
  set T : Module.End (ZMod 2) V := ρ x - 1 with hT
  have hTv : ∀ z, T z = ρ x z - z := fun z => by
    rw [hT, LinearMap.sub_apply, Module.End.one_apply]
  let f : LinearMap.range T → LinearMap.range T := fun w => ⟨T w, LinearMap.mem_range_self T w⟩
  have hf : Function.Injective f := by
    intro w₁ w₂ h
    have h1 : T ((w₁ : V) - w₂) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (congrArg Subtype.val h)
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 (Submodule.sub_mem _ w₁.2 w₂.2)
    have h2 : ρ x (ρ x z - z) = ρ x z - z := by
      have h3 : T (T z) = 0 := by rw [hz]; exact h1
      rw [hTv, hTv, sub_eq_zero] at h3
      exact h3
    have h4 := apply_eq_self_of_odd_of_fixes_sub (hodd x hx) h2
    apply Subtype.ext
    rw [← sub_eq_zero, ← hz, hTv, h4, sub_self]
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hf) ⟨T v, LinearMap.mem_range_self T v⟩
  have hwK : (w : V) ∈ commOn ρ K ⊤ := by
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 w.2
    rw [← hz, hTv]
    exact sub_mem_commOn (hXK hx) Submodule.mem_top
  have e : ρ x v - v = ρ x w - w := by
    rw [← hTv, ← hTv]
    exact (congrArg Subtype.val hw).symm
  rw [SetLike.mem_coe, e]
  exact sub_mem_commOn hx hwK

private theorem imgGL_commutator {H : Subgroup G} {U : Submodule (ZMod 2) V}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H U) {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    imgGL ρ H U hU ⁅X, Y⁆ = ⁅imgGL ρ H U hU X, imgGL ρ H U hU Y⁆ := by
  simp only [imgGL]
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
    Subgroup.map_subgroupOf_eq_of_le hY,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hX hY)]

private theorem map_commGL_imgGL_eq_commOn {H : Subgroup G} {U : Submodule (ZMod 2) V}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H U) {X : Subgroup G} (hX : X ≤ H) :
    (commGL (imgGL ρ H U hU X) ⊤).map U.subtype = commOn ρ X U := by
  simp only [commGL, CFSG.QuasithinUnique.Setup.Offender.commSub]
  rw [Submodule.map_span]
  show _ = Submodule.span (ZMod 2) {w | ∃ a ∈ X, ∃ u ∈ U, w = ρ a u - u}
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨m, hm, u, -, rfl⟩, rfl⟩
    obtain ⟨x, hxX, rfl⟩ := mem_imgGL.1 hm
    exact ⟨x, hxX, u, u.2, rfl⟩
  · rintro ⟨x, hxX, u, hu, rfl⟩
    exact ⟨_, ⟨resGL ρ H U hU ⟨x, hX hxX⟩, resGL_mem_imgGL hxX (hX hxX), ⟨u, hu⟩,
      Submodule.mem_top, rfl⟩, rfl⟩

private theorem exists_card_three_of_moving [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {K A : Subgroup G} (hKnil : Group.IsNilpotent ↥K) (hKodd : Odd (Nat.card ↥K))
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKA : ⁅K, A⁆ = K) (hK1 : K ≠ ⊥) (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ b ∈ A, Nat.card ↥(⁅K, Subgroup.zpowers b⁆ : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2) ↥(commOn ρ ⁅K, Subgroup.zpowers b⁆ ⊤) = 2 := by
  classical
  have hKnt : ¬ K ≤ cenOn ρ K ⊤ := by
    intro hle
    apply hK1
    refine (Subgroup.eq_bot_iff_forall K).2 fun k hk => hρ ?_
    refine LinearMap.ext fun v => ?_
    rw [map_one]
    exact (hle hk).2 v Submodule.mem_top
  obtain ⟨B, hBA, hinv, -, hBU, hbest, -, hmove, hstrict⟩ :=
    exists_strictMin_moving K A hA2 hAK hKA hKnt hb
  set U : Submodule (ZMod 2) V := commOn ρ K ⊤ with hUdef
  set H : Subgroup G := K ⊔ B with hHdef
  have hKH : K ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (hBA.trans hAK)
  have hfGL : Finite (U ≃ₗ[ZMod 2] U) :=
    Finite.of_injective (fun f : U ≃ₗ[ZMod 2] U => (f : U → U)) DFunLike.coe_injective
  have hKo : ∀ k ∈ K, Odd (orderOf k) := fun k hk =>
    Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard K hk)
  have hcen : cenOn ρ K U = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun k hk => eq_one_of_fixes_commOn hρ hk.1 (hKo k hk.1) hk.2
  have hcardX : ∀ X : Subgroup G, X ≤ K → Nat.card ↥(imgGL ρ H U hinv X) = Nat.card ↥X := by
    intro X hXK
    have h := card_imgGL_mul_card_cenOn (hU := hinv) (hXK.trans hKH)
    have h1 : cenOn ρ X U = ⊥ := eq_bot_iff.2 ((cenOn_mono_left hXK).trans hcen.le)
    rw [h1, Subgroup.card_bot, mul_one] at h
    exact h
  have hFG : imgGL ρ H U hinv K ≤ imgGL ρ H U hinv H := imgGL_mono hKH
  have hFn : ((imgGL ρ H U hinv K).subgroupOf (imgGL ρ H U hinv H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFG).2 (imgGL_le_normalizer hHN)
  have hnil : Group.IsNilpotent ↥(imgGL ρ H U hinv K) := by
    haveI : Group.IsNilpotent ↥(K.subgroupOf H) :=
      nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm
    exact nilpotent_of_surjective _ (MonoidHom.subgroupMap_surjective (resGL ρ H U hinv) _)
  have hodd : Odd (Nat.card ↥(imgGL ρ H U hinv K)) := by
    rw [hcardX K le_rfl]
    exact hKodd
  have hAG : imgGL ρ H U hinv B ≤ imgGL ρ H U hinv H := imgGL_mono hBH
  have hAel : CFSG.IsElementaryAbelian 2 (imgGL ρ H U hinv B) :=
    isElementaryAbelian_imgGL hBH hA2 hBA
  have hAne : imgGL ρ H U hinv B ≠ ⊥ := fun h => hBU ((imgGL_eq_bot_iff hBH).1 h)
  have hcpos : 0 < Nat.card (cenOn ρ B U) := Nat.card_pos
  have hoff : Nat.card U ≤ weight (MonoidHom.id (U ≃ₗ[ZMod 2] U)) (imgGL ρ H U hinv B) := by
    rw [weight_imgGL hBH]
    have h1 := hbest.isOffenderOn.2
    rw [← card_imgGL_mul_card_cenOn (hU := hinv) hBH, mul_assoc, mul_comm (Nat.card (cenOn ρ B U)),
      ← mul_assoc] at h1
    exact Nat.le_of_mul_le_mul_right h1 hcpos
  have hstr : ∀ B₂ : Subgroup (U ≃ₗ[ZMod 2] U), ⊥ < B₂ → B₂ < imgGL ρ H U hinv B →
      weight (MonoidHom.id (U ≃ₗ[ZMod 2] U)) B₂ <
        weight (MonoidHom.id (U ≃ₗ[ZMod 2] U)) (imgGL ρ H U hinv B) := by
    intro B₂ hbot hlt
    obtain ⟨B', hB'B, hcB', hB'⟩ := exists_imgGL_eq (hU := hinv) hBH hlt.le
    have hB'H : B' ≤ H := hB'B.trans hBH
    have hne : B' ≠ B := by
      rintro rfl
      exact hlt.ne hB'.symm
    have hnc : ¬ B' ≤ cenOn ρ B U := by
      intro h
      have : imgGL ρ H U hinv B' = ⊥ := (imgGL_eq_bot_iff hB'H).2 fun b hb => ⟨hb, (h hb).2⟩
      rw [hB'] at this
      exact hbot.ne' this
    have key := hstrict B' hcB' (lt_of_le_of_ne hB'B hne) hnc
    have hc : cenOn ρ B' U = cenOn ρ B U := by
      rw [cenOn_eq_inf_of_le hB'B]
      exact inf_eq_right.2 hcB'
    have h1 := card_imgGL_mul_card_cenOn (hU := hinv) hB'H
    have h2 := card_imgGL_mul_card_cenOn (hU := hinv) hBH
    rw [hc] at h1
    rw [← h1, ← h2] at key
    have key' : Nat.card (imgGL ρ H U hinv B') * Nat.card (fixOn ρ B' U) <
        Nat.card (imgGL ρ H U hinv B) * Nat.card (fixOn ρ B U) := by
      have : Nat.card (cenOn ρ B U) * (Nat.card (imgGL ρ H U hinv B') * Nat.card (fixOn ρ B' U)) <
          Nat.card (cenOn ρ B U) * (Nat.card (imgGL ρ H U hinv B) * Nat.card (fixOn ρ B U)) := by
        calc _ = Nat.card (imgGL ρ H U hinv B') * Nat.card (cenOn ρ B U) *
              Nat.card (fixOn ρ B' U) := by ring
          _ < Nat.card (imgGL ρ H U hinv B) * Nat.card (cenOn ρ B U) *
              Nat.card (fixOn ρ B U) := key
          _ = _ := by ring
      exact lt_of_mul_lt_mul_left this (Nat.zero_le _)
    have e1 := weight_imgGL (hU := hinv) hB'H
    rw [hB'] at e1
    rw [e1, weight_imgGL hBH, ← hB']
    exact key'
  have hcomm : ⁅imgGL ρ H U hinv K, imgGL ρ H U hinv B⁆ ≠ ⊥ := by
    intro h
    obtain ⟨b, hbB, hbc⟩ := Set.not_subset.1 (fun h' : (B : Set G) ⊆ cenOn ρ B U => hBU h')
    obtain ⟨k, hkK, u, hu, hne⟩ := hmove b hbB hbc
    have hx : resGL ρ H U hinv ⟨k, hKH hkK⟩ ∈ imgGL ρ H U hinv K := resGL_mem_imgGL hkK _
    have hy : resGL ρ H U hinv ⟨b, hBH hbB⟩ ∈ imgGL ρ H U hinv B := resGL_mem_imgGL hbB _
    have h1 : ⁅resGL ρ H U hinv ⟨k, hKH hkK⟩, resGL ρ H U hinv ⟨b, hBH hbB⟩⁆ = 1 := by
      have : ⁅resGL ρ H U hinv ⟨k, hKH hkK⟩, resGL ρ H U hinv ⟨b, hBH hbB⟩⁆ ∈
          (⊥ : Subgroup (U ≃ₗ[ZMod 2] U)) := h ▸ Subgroup.commutator_mem_commutator hx hy
      simpa using this
    have h2 : resGL ρ H U hinv ⟨k, hKH hkK⟩ * resGL ρ H U hinv ⟨b, hBH hbB⟩ =
        resGL ρ H U hinv ⟨b, hBH hbB⟩ * resGL ρ H U hinv ⟨k, hKH hkK⟩ :=
      commutatorElement_eq_one_iff_mul_comm.1 h1
    have h3 := congrArg (fun f : U ≃ₗ[ZMod 2] U => ((f ⟨u, hu⟩ : U) : V)) h2
    exact hne h3.symm
  have hres := CFSG.QuasithinUnique.Setup.Layer.nilpotent_offender_natural_S3_factors.{0, 0, 0}
    (k := ZMod 2) (V := ↥U) hFG hFn (hodd := hodd) hAG hAel hAne hoff hstr hcomm
  have hB2 : Nat.card ↥(imgGL ρ H U hinv B) = 2 := hres.2.1
  have hL3 := hres.2.2.2.1
  have hLr := hres.2.2.2.2.2.2.1
  obtain ⟨b, hbB, hbc⟩ := Set.not_subset.1 (fun h' : (B : Set G) ⊆ cenOn ρ B U => hBU h')
  have hzB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.2 hbB
  have hzH : Subgroup.zpowers b ≤ H := hzB.trans hBH
  have hzimg : imgGL ρ H U hinv (Subgroup.zpowers b) = imgGL ρ H U hinv B := by
    refine Subgroup.eq_of_le_of_card_ge (imgGL_mono hzB) ?_
    have hne : imgGL ρ H U hinv (Subgroup.zpowers b) ≠ ⊥ := by
      intro h
      apply hbc
      exact ⟨hbB, ((imgGL_eq_bot_iff hzH).1 h (Subgroup.mem_zpowers b)).2⟩
    have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  have hQK : ⁅K, Subgroup.zpowers b⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hzB.trans (hBA.trans hAK))
  have himgQ : imgGL ρ H U hinv ⁅K, Subgroup.zpowers b⁆ =
      ⁅imgGL ρ H U hinv K, imgGL ρ H U hinv B⁆ := by
    rw [imgGL_commutator hinv hKH hzH, hzimg]
  refine ⟨b, hBA hbB, ?_, ?_⟩
  · rw [← hcardX _ hQK, himgQ]
    exact hL3
  · have hQU : commOn ρ ⁅K, Subgroup.zpowers b⁆ ⊤ = commOn ρ ⁅K, Subgroup.zpowers b⁆ U :=
      le_antisymm (commOn_top_le_commOn_of_odd hQK fun x hx => hKo x (hQK hx))
        (commOn_mono_right le_top)
    rw [hQU, ← map_commGL_imgGL_eq_commOn hinv (hQK.trans hKH), Submodule.finrank_map_subtype_eq,
      himgQ]
    exact hLr

theorem exists_Q_of_moving [Finite G] [Finite V] (hρ : Function.Injective ρ) {K A : Subgroup G}
    (hKnil : Group.IsNilpotent ↥K) (hKodd : Odd (Nat.card ↥K))
    (hA2 : CFSG.IsElementaryAbelian 2 ↥A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKA : ⁅K, A⁆ ≠ ⊥) (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ b ∈ A,
      Nat.card ↥(⁅K, Subgroup.zpowers b⁆ : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2) ↥(commOn ρ ⁅K, Subgroup.zpowers b⁆ ⊤) = 2 ∧
      ⁅K, Subgroup.zpowers b⁆ ≤ K ∧
      A ≤ Subgroup.normalizer ((⁅K, Subgroup.zpowers b⁆ : Subgroup G) : Set G) ∧
      ∀ q ∈ ⁅K, Subgroup.zpowers b⁆, b * q * b⁻¹ = q⁻¹ := by
  classical
  have hK'K : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hAK
  have h2K : ¬ 2 ∣ Nat.card ↥K := fun h => (Nat.not_even_iff_odd.2 hKodd) (even_iff_two_dvd.2 h)
  have hAp : IsPGroup 2 ↥A := CFSG.IsElementaryAbelian.isPGroup 2 ↥A
  have hK'A : ⁅⁅K, A⁆, A⁆ = ⁅K, A⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq Nat.prime_two hAp hAK h2K
  have hAK' : A ≤ Subgroup.normalizer ((⁅K, A⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right K A
  have hK'nil : Group.IsNilpotent ↥(⁅K, A⁆ : Subgroup G) := by
    haveI : Group.IsNilpotent ↥((⁅K, A⁆ : Subgroup G).subgroupOf K) := Subgroup.isNilpotent _
    exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'K)
  have hK'odd : Odd (Nat.card ↥(⁅K, A⁆ : Subgroup G)) :=
    Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le hK'K)
  obtain ⟨b, hbA, hcard, hrank⟩ :=
    exists_card_three_of_moving hρ hK'nil hK'odd hA2 hAK' hK'A hKA hb
  have hzA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.2 hbA
  have hzK : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) := hzA.trans hAK
  have hcc : ⁅⁅K, Subgroup.zpowers b⁆, Subgroup.zpowers b⁆ = ⁅K, Subgroup.zpowers b⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq Nat.prime_two
      (hAp.to_le hzA) hzK h2K
  have hQ : ⁅K, Subgroup.zpowers b⁆ = ⁅⁅K, A⁆, Subgroup.zpowers b⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_mono_left hK'K)
    calc ⁅K, Subgroup.zpowers b⁆ = ⁅⁅K, Subgroup.zpowers b⁆, Subgroup.zpowers b⁆ := hcc.symm
      _ ≤ ⁅⁅K, A⁆, Subgroup.zpowers b⁆ :=
        Subgroup.commutator_mono_left (Subgroup.commutator_mono_right hzA)
  have hQ3 : Nat.card ↥(⁅K, Subgroup.zpowers b⁆ : Subgroup G) = 3 := by
    rw [hQ]
    exact hcard
  have hAb : ∀ a ∈ A, a * b = b * a := fun a ha =>
    congrArg Subtype.val (hA2.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩)
  have hAQ : A ≤ Subgroup.normalizer ((⁅K, Subgroup.zpowers b⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_zpowers_of_commute hAK hAb
  refine ⟨b, hbA, hQ3, by rw [hQ]; exact hrank,
    Subgroup.le_normalizer_iff_commutator_le_left.mp hzK, hAQ, ?_⟩
  have hb2 : b * b = 1 := by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian b hbA
  refine conj_eq_inv_of_card_three hQ3 hb2 (hAQ hbA) ?_
  rw [hcc]
  intro h
  rw [h, Subgroup.card_bot] at hQ3
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
