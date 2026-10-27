module

public import CFSG.Quasithin.H13.U3S1347H

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem quotIso_of_lieModel {K : Subgroup G}
    (hLie : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) : quasithinO2QuotientIso K SL3.S :=
  (quasithinO2QuotientIso_iff K SL3.S).2 (nonempty_equiv_SL32_of_lieModel hLie)

theorem s1347_quotIso_H0 (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    {K₀ : Subgroup G} (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hK : quasithinO2QuotientIso K₀ SL3.S) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T) :
    quasithinO2QuotientIso (H₁ ⊔ H₂) SL3.S := by
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) :=
    A5.isSylowTwoOf_of_le S.h13.sylow (h.inH₁.1.trans le_sup_left)
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  refine quot_SL3_of_sup hsyl₀ hN hsup hK h.inH₁.1 le_sup_left (fun e => ?_) (fun hle => ?_)
  · rw [e, relIndex_self] at h3₁
    exact absurd h3₁ (by norm_num)
  · have h21 : H₂ ≤ H₁ := le_sup_right.trans (hsup.le.trans (sup_le hle h.inH₁.1))
    have hm := relIndex_mul_relIndex T H₂ H₁ h.inH₂.1 h21
    rw [h3₁, h3₂] at hm
    have h1 : H₂.relIndex H₁ = 1 := by omega
    exact h.ne (le_antisymm (relIndex_eq_one.1 h1) h21)

theorem s1347_normalizer_centralizer (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) :
    H₁ ⊔ H₂ ≤ normalizer (((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) :
      Subgroup G) : Set G) := fun _ hg =>
  mem_normalizer_inf_of (le_normalizer hg)
    (mem_normalizer_centralizer_of_mem ((s1347_reduced S hH₀).2.1 hg))

theorem s1347_coprime_centralizer (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) :
    Nat.Coprime 3 (Nat.card ↥((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3d
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 3 h3d
  have hx1 := s1347_eq_one_of_threePow S h hH₀ hx (k := 1) (by
    have h1 := pow_orderOf_eq_one (⟨x, hx⟩ : ↥((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G)))
    rw [hxo] at h1
    simpa using congrArg Subtype.val h1)
  subst hx1
  rw [show (⟨1, hx⟩ : ↥((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G))) = 1 from rfl,
    orderOf_one] at hxo
  omega

theorem s1347_centralizer_eq (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hiso : quasithinO2QuotientIso (H₁ ⊔ H₂) SL3.S) :
    (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂) := by
  obtain ⟨e⟩ := (quasithinO2QuotientIso_iff _ _).1 hiso
  have : IsSimpleGroup SL3.S := HSType.isSimpleGroup_SL_three_two
  have hs : IsSimpleGroup (↥(H₁ ⊔ H₂) ⧸ CFSG.pCore 2 ↥(H₁ ⊔ H₂)) := e.isSimpleGroup
  have h3 : 3 ∣ Nat.card (↥(H₁ ⊔ H₂) ⧸ CFSG.pCore 2 ↥(H₁ ⊔ H₂)) := by
    rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two]
    norm_num
  refine le_antisymm ?_ (le_inf (pCoreOf_le 2 _)
    ((s1347_T_inf_centralizer S h hH₀).ge.trans inf_le_right))
  have := inf_le_pCoreOf_of_coprime_three (s1347_normalizer_centralizer S hH₀)
    (s1347_coprime_centralizer S h hH₀) hs h3
  rwa [← inf_assoc, inf_idem] at this

theorem s1347_map_parabolic {H₀ Hi : Subgroup G} (hsyl : IsSylowTwoOf T H₀)
    {ψ : ↥H₀ →* SL3.S} (hker : ψ.ker = Open.pCore 2 ↥H₀)
    (hTψ : (T.subgroupOf H₀).map ψ = SL3.P0) (hHi : Hi ≤ H₀) (hTHi : T ≤ Hi)
    (h3 : T.relIndex Hi = 3) :
    (Hi.subgroupOf H₀).map ψ = SL3.X1 ∨ (Hi.subgroupOf H₀).map ψ = SL3.X2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : SL3.P0 ≤ (Hi.subgroupOf H₀).map ψ := by
    rw [← hTψ]
    exact map_mono fun x hx => mem_subgroupOf.2 (hTHi (mem_subgroupOf.1 hx))
  rcases SL3.overgroups_SL3 _ hle with hP | hP | hP | hP
  · exfalso
    have hcomap := I51.subgroupOf_eq_comap_map hsyl ψ hker hTHi
    have hcomap' := I51.subgroupOf_eq_comap_map hsyl ψ hker le_rfl
    rw [hTψ] at hcomap'
    rw [hP, ← hcomap'] at hcomap
    have hHT : Hi = T := by
      have := (Subgroup.subgroupOf_inj).1 hcomap
      rwa [inf_eq_left.2 hHi, inf_eq_left.2 hsyl.1] at this
    rw [hHT, relIndex_self] at h3
    exact absurd h3 (by norm_num)
  · exact Or.inl hP
  · exact Or.inr hP
  · exfalso
    obtain ⟨n, hn⟩ := hsyl.2.1.exists_card_eq
    have hcard : Nat.card Hi = 3 * 2 ^ n := by
      have h1 := relIndex_mul_card T Hi
      rw [inf_eq_left.2 hTHi, h3, hn] at h1
      exact h1.symm
    have hdvd := card_map_dvd (Hi.subgroupOf H₀) ψ
    rw [hP, card_top, SL3.card_S, Nat.card_congr (subgroupOfEquivOfLe hHi).toEquiv, hcard] at hdvd
    have h7 : 7 ∣ 3 * 2 ^ n := (show 7 ∣ 168 by norm_num).trans hdvd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h7 with h | h
    · exact absurd h (by norm_num)
    · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h
      exact absurd this (by norm_num)

omit [Finite G] in
theorem s1347_map_ne {H₀ H₁ H₂ : Subgroup G} (hsyl : IsSylowTwoOf T H₀)
    {ψ : ↥H₀ →* SL3.S} (hker : ψ.ker = Open.pCore 2 ↥H₀) (h₁ : H₁ ≤ H₀) (h₂ : H₂ ≤ H₀)
    (hT₁ : T ≤ H₁) (hT₂ : T ≤ H₂) (hne : H₁ ≠ H₂) :
    (H₁.subgroupOf H₀).map ψ ≠ (H₂.subgroupOf H₀).map ψ := by
  intro he
  have hc₁ := I51.subgroupOf_eq_comap_map hsyl ψ hker hT₁
  have hc₂ := I51.subgroupOf_eq_comap_map hsyl ψ hker hT₂
  rw [he, ← hc₂] at hc₁
  have := (Subgroup.subgroupOf_inj).1 hc₁
  rw [inf_eq_left.2 h₁, inf_eq_left.2 h₂] at this
  exact hne this

theorem s1347_map_K0 {H₀ K₀ : Subgroup G} {ψ : ↥H₀ →* SL3.S} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Open.pCore 2 ↥H₀) (hKH : K₀ ≤ H₀) (hN : H₀ ≤ normalizer (K₀ : Set G))
    (hK : quasithinO2QuotientIso K₀ SL3.S) : (K₀.subgroupOf H₀).map ψ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup SL3.S := HSType.isSimpleGroup_SL_three_two
  have hn : ((K₀.subgroupOf H₀).map ψ).Normal :=
    ((normal_subgroupOf_iff_le_normalizer hKH).2 hN).map ψ hψ
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exfalso
    have hK2 : K₀ ≤ pCoreOf 2 H₀ := by
      intro k hk
      have h1 : ψ ⟨k, hKH hk⟩ = 1 := by
        have : ψ ⟨k, hKH hk⟩ ∈ (K₀.subgroupOf H₀).map ψ := mem_map_of_mem _ (mem_subgroupOf.2 hk)
        rw [hb, mem_bot] at this
        exact this
      exact (map_eq_one_iff_of_ker hker _).1 h1
    obtain ⟨n, hn⟩ := ((pCoreOf_isPGroup 2 H₀).to_le hK2).exists_card_eq
    obtain ⟨φ, hφ, -⟩ := hK
    have hdvd : Nat.card SL3.S ∣ Nat.card K₀ := by
      have := card_map_dvd (⊤ : Subgroup ↥K₀) φ
      rwa [map_top_of_surjective φ hφ, card_top, card_top] at this
    rw [SL3.card_S, hn] at hdvd
    have h7 : 7 ∣ 2 ^ n := (show 7 ∣ 168 by norm_num).trans hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h7
    exact absurd this (by norm_num)
  · exact ht

theorem s1347_exists_action (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) {ψ : ↥(H₁ ⊔ H₂) →* SL3.S}
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Open.pCore 2 ↥(H₁ ⊔ H₂)) :
    ∃ σ : SL3.S →* MulAut ↥(v0Of T H₁ H₂), ∀ (x : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((σ (ψ x) w : ↥(v0Of T H₁ H₂)) : G) = x * w * (x : G)⁻¹ := by
  have hN := (s1347_reduced S hH₀).2.1
  let c : ↥(H₁ ⊔ H₂) →* MulAut ↥(v0Of T H₁ H₂) := (conjAct _).comp (Subgroup.inclusion hN)
  have hc : ∀ (x : ↥(H₁ ⊔ H₂)) (w : ↥(v0Of T H₁ H₂)),
      ((c x w : ↥(v0Of T H₁ H₂)) : G) = x * w * (x : G)⁻¹ := fun x w =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w
  have hle : ψ.ker ≤ c.ker := by
    intro x hx
    have hxO := (map_eq_one_iff_of_ker hker x).1 hx
    have hxC : (x : G) ∈ centralizer (v0Of T H₁ H₂ : Set G) :=
      ((s1347_T_inf_centralizer S h hH₀).ge.trans inf_le_right) hxO
    rw [MonoidHom.mem_ker]
    ext w
    rw [hc]
    show (x : G) * w * (x : G)⁻¹ = w
    rw [← mem_centralizer_iff.1 hxC w w.2, mul_inv_cancel_right]
  refine ⟨(QuotientGroup.lift ψ.ker c hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom, fun x w => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ x) =
      (x : ↥(H₁ ⊔ H₂) ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk, hc]

end CFSG.Quasithin.H13.U3
