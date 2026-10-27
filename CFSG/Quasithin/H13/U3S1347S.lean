module

public import CFSG.Quasithin.H13.U3S1347M
public import CFSG.Quasithin.H13.U3S1347P

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem fix_dv45_iff : ∀ σ : Perm (Fin 6), act4f σ (dv 4 5) = dv 4 5 ↔ InP1 σ := by
  decide +kernel

omit [Finite G] in
theorem le_pCoreOf_of_normal {K M : Subgroup G} (hMK : M ≤ K)
    (hn : K ≤ normalizer (M : Set G)) (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hne : ¬ K ≤ M ⊔ pCoreOf 2 K) : M ≤ pCoreOf 2 K := by
  have hMn : (M.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hMK).2 hn
  have hn' : ((M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective _)
  rcases hn'.eq_bot_or_eq_top with hb | ht
  · intro m hm
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨m, hMK hm⟩ ∈
        (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
      mem_map_of_mem _ (mem_subgroupOf.2 hm)
    rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf] at h1
    exact h1
  · exfalso
    apply hne
    intro k hk
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨k, hk⟩ ∈
        (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      rw [ht]
      exact mem_top _
    obtain ⟨m, hm, hmk⟩ := h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      ← pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf] at hmk
    have e : k = (m : G) * ((m : G)⁻¹ * k) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mem_subgroupOf.1 hm)) (mem_sup_right hmk)

theorem s1347_inf_centralizer_I (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) {K₀ I : Subgroup G} (hKH : K₀ ≤ H₁ ⊔ H₂)
    (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G)) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hs : IsSimpleGroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀)
    (hIV : I ≤ v0Of T H₁ H₂) (hH₀I : H₁ ⊔ H₂ ≤ normalizer (I : Set G))
    (hKI : ¬ K₀ ≤ centralizer (I : Set G)) :
    (H₁ ⊔ H₂) ⊓ centralizer (I : Set G) ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hO : pCoreOf 2 K₀ ≤ centralizer (v0Of T H₁ H₂ : Set G) := hcentK ▸ inf_le_right
  have hCI : centralizer (v0Of T H₁ H₂ : Set G) ≤ centralizer (I : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 hIV)
  have hKC : K₀ ⊓ centralizer (I : Set G) ≤ pCoreOf 2 K₀ := by
    refine le_pCoreOf_of_normal inf_le_left (fun k hk => mem_normalizer_inf_of
      (le_normalizer hk) (mem_normalizer_centralizer_of_mem (hH₀I (hKH hk)))) hs fun hle => ?_
    exact hKI (hle.trans (sup_le inf_le_right (hO.trans hCI)))
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hTN : T ≤ normalizer (K₀ : Set G) := (hsup ▸ le_sup_right : T ≤ H₁ ⊔ H₂).trans hN
  refine hred.2.2.2 _ inf_le_left (fun g hg => mem_normalizer_inf_of (le_normalizer hg)
    (mem_normalizer_centralizer_of_mem (hH₀I hg))) fun d hd => ?_
  obtain ⟨a, ha⟩ := pow_two_mem_of_sup hTN hT2 (show d ∈ K₀ ⊔ T from hsup ▸ (mem_inf.1 hd).1)
  exact ⟨a, hO (hKC (mem_inf.2 ⟨ha, pow_mem (mem_inf.1 hd).2 _⟩))⟩

omit [Finite G] in
theorem conjAct_val {I : Subgroup G} {x : G} (hx : x ∈ normalizer (I : Set G)) (v : ↥I) :
    ((conjAct I ⟨x, hx⟩ v : ↥I) : G) = x * v * x⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe I _ v

omit [Finite G] in
theorem s1347_rho_eq_one_iff {H₀ I : Subgroup G} (hH₀I : H₀ ≤ normalizer (I : Set G))
    {ρ : ↥H₀ →* Perm (Fin 6)} {ψ : ↥I ≃* ↥W4}
    (hψ : ∀ (h : ↥H₀) (v : ↥I), ψ (conjAct I ⟨h, hH₀I h.2⟩ v) = act4 (ρ h) (ψ v))
    (h : ↥H₀) : ρ h = 1 ↔ (h : G) ∈ centralizer (I : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h1 v hv
    have h2 := hψ h ⟨v, hv⟩
    rw [h1, map_one, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (ψ.injective h2)
    rw [conjAct_val] at h3
    have := congrArg (· * (h : G)) h3
    simp only [inv_mul_cancel_right] at this
    exact this.symm
  · intro h1
    apply act4_injective
    rw [map_one]
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.one_apply]
    obtain ⟨v, rfl⟩ := ψ.surjective x
    rw [← hψ]
    congr 1
    apply Subtype.ext
    rw [conjAct_val, ← h1 v v.2, mul_inv_cancel_right]

theorem s1347_centralizer_eq_A6 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) {K₀ : Subgroup G}
    (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G)) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _)
    ((s1347_T_inf_centralizer S h hH₀).ge.trans inf_le_right))
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hTN : T ≤ normalizer (K₀ : Set G) := (hsup ▸ le_sup_right : T ≤ H₁ ⊔ H₂).trans hN
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ inf_le_left
    ((normal_subgroupOf_iff_le_normalizer inf_le_left).2 (s1347_normalizer_centralizer S hH₀))
    ?_
  rintro ⟨d, hd⟩
  obtain ⟨a, ha⟩ := pow_two_mem_of_sup hTN hT2 (show d ∈ K₀ ⊔ T from hsup ▸ (mem_inf.1 hd).1)
  have hdK : d ^ 2 ^ a ∈ pCoreOf 2 K₀ := hcentK ▸ mem_inf.2 ⟨ha, pow_mem (mem_inf.1 hd).2 _⟩
  obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 K₀) ⟨_, hdK⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have hb' : (d ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, hb']

theorem fix_P1_gens : ∀ x : P6, InW4 x → act4f (swap 2 3 * swap 4 5) x = x →
    act4f (swap 1 2 * swap 4 5) x = x → x = 1 ∨ x = dv 4 5 := by
  decide +kernel

theorem fix_P1_gens_tw : ∀ x : P6, InW4 x → act4f (swap 0 3 * swap 1 2) x = x →
    act4f (swap 0 5 * swap 1 4) x = x → x = 1 := by
  decide +kernel

theorem phi_inv_P1_gens : S6Out.phi (S6Out.cc⁻¹ * (swap 2 3 * swap 4 5) * S6Out.cc) =
      swap 0 3 * swap 1 2 ∧
    S6Out.phi (S6Out.cc⁻¹ * (swap 1 2 * swap 4 5) * S6Out.cc) = swap 0 5 * swap 1 4 := by
  decide +kernel

theorem pow_four_of_inD6 : ∀ σ : Perm (Fin 6), InD6 σ → σ ^ 4 = 1 := by
  decide +kernel

omit [Finite G] in
theorem sup_subgroupOf_eq {A B H : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    (A ⊔ B).subgroupOf H = A.subgroupOf H ⊔ B.subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hA hB), map_subgroupOf_eq_of_le hA,
    map_subgroupOf_eq_of_le hB]

theorem s1347_A6_parabolic {H₀ K₀ Hi : Subgroup G} (hT2 : IsPGroup 2 T) (hTH : T ≤ H₀)
    (hKH : K₀ ≤ H₀) {ρ : ↥H₀ →* Perm (Fin 6)}
    (hkerρ : ∀ h : ↥H₀, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H₀)
    (hρD : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      ∃ t, ∃ ht : t ∈ T, ρ ⟨t, hTH ht⟩ = σ)
    (hρK : ∀ k (hk : k ∈ K₀), ρ ⟨k, hKH hk⟩ ∈ alternatingGroup (Fin 6))
    (hHi : Hi ≤ H₀) (hTHi : T ≤ Hi) (h3 : T.relIndex Hi = 3) (hKi : oTwoRes Hi ≤ K₀)
    (hnot : ¬ oTwoRes Hi ≤ pCoreOf 2 H₀) :
    (Hi.subgroupOf H₀).map ρ = (P1sub ⊓ alternatingGroup (Fin 6)) ⊔ (T.subgroupOf H₀).map ρ ∨
      (Hi.subgroupOf H₀).map ρ = (P2sub ⊓ alternatingGroup (Fin 6)) ⊔ (T.subgroupOf H₀).map ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : QA6sub ≤ (Hi.subgroupOf H₀).map ρ ⊓ alternatingGroup (Fin 6) := by
    intro σ hσ
    obtain ⟨t, ht, hσt⟩ := hρD σ (mem_inf.1 hσ).1 (mem_inf.1 hσ).2
    exact mem_inf.2 ⟨⟨⟨t, hTH ht⟩, mem_subgroupOf.2 (hTHi ht), hσt⟩, (mem_inf.1 hσ).2⟩
  have hKmap : ((oTwoRes Hi).subgroupOf H₀).map ρ ≤
      (Hi.subgroupOf H₀).map ρ ⊓ alternatingGroup (Fin 6) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨⟨x, mem_subgroupOf.2 (oTwoRes_le Hi (mem_subgroupOf.1 hx)), rfl⟩, ?_⟩
    exact hρK _ (hKi (mem_subgroupOf.1 hx))
  have hsylHi : IsSylowTwoOf T Hi := ⟨hTHi, hT2, by
    show ¬ 2 ∣ T.relIndex Hi
    rw [h3]
    decide⟩
  have hsup : (Hi.subgroupOf H₀).map ρ ≤
      ((oTwoRes Hi).subgroupOf H₀).map ρ ⊔ (T.subgroupOf H₀).map ρ := by
    rw [← Subgroup.map_sup, ← sup_subgroupOf_eq ((oTwoRes_le Hi).trans hHi) hTH]
    exact map_mono (fun x hx => mem_subgroupOf.2 (le_oTwoRes_sup_of_isSylowTwoOf hsylHi
      (mem_subgroupOf.1 hx)))
  have hTmap : (T.subgroupOf H₀).map ρ ≤ (Hi.subgroupOf H₀).map ρ :=
    map_mono fun x hx => mem_subgroupOf.2 (hTHi (mem_subgroupOf.1 hx))
  have hform : ∀ Y : Subgroup (Perm (Fin 6)),
      (Hi.subgroupOf H₀).map ρ ⊓ alternatingGroup (Fin 6) = Y →
      (Hi.subgroupOf H₀).map ρ = Y ⊔ (T.subgroupOf H₀).map ρ := by
    intro Y hY
    refine le_antisymm (hsup.trans (sup_le_sup_right (hY ▸ hKmap) _)) (sup_le ?_ hTmap)
    rw [← hY]
    exact inf_le_left
  rcases overgroups_QA6 _ hQ inf_le_right with hY | hY | hY | hY
  · exfalso
    apply hnot
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨hxH, m, hm, hxm⟩ := hx
    have hxK : x ∈ oTwoRes Hi := subset_closure ⟨hxH, m, hm, hxm⟩
    have hρx : ρ ⟨x, hHi hxH⟩ ∈ QA6sub := by
      rw [← hY]
      exact hKmap ⟨⟨x, hHi hxH⟩, mem_subgroupOf.2 hxK, rfl⟩
    have h4 := pow_four_of_inD6 _ (mem_inf.1 hρx).1
    have hm' : ρ ⟨x, hHi hxH⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨x, hHi hxH⟩ : ↥H₀) ^ m = 1 := Subtype.ext (by simpa using hxm)
      rw [this, map_one]
    have h1 := A5.eq_one_of_pow_coprime (m := 2 ^ 2) h4 hm'
      (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm))
    exact (hkerρ _).1 h1
  · exact Or.inl (hform _ hY)
  · exact Or.inr (hform _ hY)
  · exfalso
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have hcard : Nat.card Hi = 3 * 2 ^ n := by
      have h1 := relIndex_mul_card T Hi
      rw [inf_eq_left.2 hTHi, h3, hn] at h1
      exact h1.symm
    have hdvd := card_map_dvd (Hi.subgroupOf H₀) ρ
    rw [Nat.card_congr (subgroupOfEquivOfLe hHi).toEquiv, hcard] at hdvd
    have h360 : Nat.card ↥(alternatingGroup (Fin 6)) ∣ Nat.card ↥((Hi.subgroupOf H₀).map ρ) := by
      rw [← hY]
      exact card_dvd_of_le inf_le_left
    have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [hA6] at h360
    have h5 : 5 ∣ 3 * 2 ^ n := (show 5 ∣ 360 by norm_num).trans (h360.trans hdvd)
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h5 with h | h
    · exact absurd h (by norm_num)
    · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h) (by norm_num)

end CFSG.Quasithin.H13.U3
