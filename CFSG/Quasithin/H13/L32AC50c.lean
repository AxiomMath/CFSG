module

public import CFSG.Quasithin.H13.L32AC49e
public import CFSG.Quasithin.H13.L32AC50b
public import CFSG.Quasithin.H13.L32ACSk4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Equiv Equiv.Perm

abbrev Alt7.A7 : Type := ↥(alternatingGroup (Fin 7))

local notation "cS7" =>
  (MulAut.conjNormal : Equiv.Perm (Fin 7) →* MulAut CFSG.Quasithin.H13.L32A.C.Alt7.A7)

theorem Alt7.conjNormal_injective : Function.Injective cS7 := by
  intro σ τ h
  have hc : ∀ c : Perm (Fin 7), sign c = 1 → σ * c * σ⁻¹ = τ * c * τ⁻¹ := fun c hc => by
    have := congrArg (fun f : MulAut Alt7.A7 =>
      ((f ⟨c, mem_alternatingGroup.mpr hc⟩ : Alt7.A7) : Perm (Fin 7))) h
    simpa [MulAut.conjNormal_apply] using this
  set ρ := τ⁻¹ * σ with hρ
  have hcomm : ∀ c ∈ Alt7.cycList, ρ * c = c * ρ := fun c hcl => by
    have h1 := hc c (Alt7.cyc_sign c hcl)
    calc ρ * c = τ⁻¹ * (σ * c * σ⁻¹) * σ := by rw [hρ]; group
      _ = τ⁻¹ * (τ * c * τ⁻¹) * σ := by rw [h1]
      _ = c * ρ := by rw [hρ]; group
  have hfix : ∀ i, ρ i = i := by
    intro i
    obtain ⟨c₁, h₁, c₂, h₂, hi₁, hi₂, hx⟩ := Alt7.exists_cycles i
    have hmov : ∀ c ∈ Alt7.cycList, c i ≠ i → c (ρ i) ≠ ρ i := fun c hcl hci h => by
      have e : c (ρ i) = ρ (c i) := by
        rw [← Perm.mul_apply, ← Perm.mul_apply, hcomm c hcl]
      rw [e] at h
      exact hci (ρ.injective h)
    exact hx _ (hmov c₁ h₁ hi₁) (hmov c₂ h₂ hi₂)
  have hρ1 : ρ = 1 := Equiv.ext hfix
  rw [hρ, inv_mul_eq_one] at hρ1
  exact hρ1.symm

theorem Alt7.conjNormal_surjective : Function.Surjective cS7 :=
  CFSG.ComponentClassification.CatalogueSchreierAlternating.conjugation_surjective
    (Or.inr le_rfl)

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_pi_a7 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h28 : Lemma14_7_28)
    (h32 : Lemma14_7_32) (h47 : Lemma14_7_47) (h48 : Lemma14_7_48) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hA : IsAlt 7 (cStar K)) :
    ∃ π : ↥H →* Equiv.Perm (Fin 7), π.ker = CFSG.Open.pCore 2 ↥H ∧
      alternatingGroup (Fin 7) ≤ π.range := by
  obtain ⟨K', hcK', -, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hL1K := (h47 _ T L V H S K hK).1
  have hKn := le_normalizer_of_setting h37 h38 S hK (h32 _ T L V H S K hK)
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨φ⟩ := hA
  set π₀ : ↥K →* ↥(alternatingGroup (Fin 7)) := φ.toMonoidHom.comp (QuotientGroup.mk' _)
    with hπ₀def
  have hπ₀ : Function.Surjective π₀ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ∀ k : ↥K, π₀ k = 1 ↔ (k : G) ∈ pCoreOf 2 K := fun k => by
    rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := indHom π₀ hπ₀ hker₀ hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π₀ k) = π₀ (conjK (hKn y.2) k) :=
    indHom_apply π₀ hπ₀ hker₀ hKn hHN
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = cS7 (π₀ ⟨k, hk⟩ : Equiv.Perm (Fin 7)) := by
    intro k hk
    have e : MulAut.conj (π₀ ⟨k, hk⟩) = cS7 (π₀ ⟨k, hk⟩ : Equiv.Perm (Fin 7)) := by
      ext x
      simp [MulAut.conjNormal_apply]
    rw [← e]
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ₀ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ MonoidHom.range cS7 := fun y => Alt7.conjNormal_surjective _
  have hZ : Subgroup.center (cStar K) = ⊥ := by
    have hc := card_center_eq_of_mulEquiv φ
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π₀ hπ₀ hker₀ hKH hKn hHN cS7
    Alt7.conjNormal_injective hInn fun x hx hxc => mem_pCoreOf_of_comm h28 S hcK' hL1K hKn hZ hx hxc
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = (π₀ ⟨k, hk⟩ : Equiv.Perm (Fin 7)) := by
    intro k hk
    apply Alt7.conjNormal_injective
    rw [hψ, hKin k hk]
  refine ⟨ψ, hψker, fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := hπ₀ ⟨a, ha⟩
  exact ⟨⟨k, hKH k.2⟩, (hψK k k.2).trans (congrArg Subtype.val hk)⟩

theorem Alt7.tsSub_isPGroup : IsPGroup 2 Alt7.tsSub :=
  IsPGroup.of_card (n := 4) (Alt7.card_tsSub.trans (by norm_num))

theorem Alt7.card_perm7 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem Alt7.card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem Alt7.eq_top_or_eq_alt {R : Subgroup (Equiv.Perm (Fin 7))}
    (hA7 : alternatingGroup (Fin 7) ≤ R) : R = ⊤ ∨ R = alternatingGroup (Fin 7) := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hA7
  rw [Alt7.card_alt7] at hm
  obtain ⟨n, hn⟩ := Subgroup.card_subgroup_dvd_card R
  rw [Alt7.card_perm7, hm] at hn
  have hmn : m * n = 2 := by
    have : 2520 * (m * n) = 2520 * 2 := by rw [← mul_assoc, ← hn]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  rcases (Nat.dvd_prime Nat.prime_two).1 ⟨n, hmn.symm⟩ with rfl | rfl
  · right
    exact (Subgroup.eq_of_le_of_card_ge hA7 (by rw [hm, Alt7.card_alt7])).symm
  · left
    exact Subgroup.eq_top_of_card_eq R (by rw [hm, Alt7.card_perm7])

theorem exists_pi_a7_ts (S : Setting147 G T L V H) (π : ↥H →* Equiv.Perm (Fin 7))
    (hker : π.ker = CFSG.Open.pCore 2 ↥H) (hA7 : alternatingGroup (Fin 7) ≤ π.range) :
    ∃ π' : ↥H →* Equiv.Perm (Fin 7), π'.ker = CFSG.Open.pCore 2 ↥H ∧
      alternatingGroup (Fin 7) ≤ π'.range ∧
      ((π'.range = ⊤ ∧ (T.subgroupOf H).map π' = Alt7.tsSub) ∨
        (π'.range = alternatingGroup (Fin 7) ∧ (T.subgroupOf H).map π' = Alt7.taSub)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hS2 : IsPGroup 2 (T.subgroupOf H) :=
    hTsyl.2.1.comap_of_injective H.subtype H.subtype_injective
  set ρ := π.rangeRestrict with hρdef
  have hρ : Function.Surjective ρ := MonoidHom.rangeRestrict_surjective π
  have key : ∀ (D : Subgroup (Equiv.Perm (Fin 7))), D ≤ π.range →
      IsPGroup 2 (D.subgroupOf π.range) → ¬ 2 ∣ (D.subgroupOf π.range).index →
      ∃ π' : ↥H →* Equiv.Perm (Fin 7), π'.ker = CFSG.Open.pCore 2 ↥H ∧ π'.range = π.range ∧
        (T.subgroupOf H).map π' = D := by
    intro D hDR hD2 hDi
    obtain ⟨h, hh⟩ := exists_conj_map_eq_of_sylow ρ hρ hS2 hTsyl.2.2 hD2 hDi
    set π' : ↥H →* Equiv.Perm (Fin 7) :=
      (MulAut.conj ((h : Equiv.Perm (Fin 7))⁻¹)).toMonoidHom.comp π with hπ'
    have hπ'ρ : ∀ x, π' x = (((MulAut.conj h⁻¹) (ρ x) : ↥π.range) : Equiv.Perm (Fin 7)) :=
      fun x => rfl
    refine ⟨π', ?_, ?_, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, ← hker, MonoidHom.mem_ker]
      show (MulAut.conj ((h : Equiv.Perm (Fin 7))⁻¹)) (π x) = 1 ↔ π x = 1
      exact MulEquiv.map_eq_one_iff _
    · ext y
      constructor
      · rintro ⟨x, rfl⟩
        rw [hπ'ρ]
        exact Subtype.mem _
      · intro hy
        obtain ⟨x, hx⟩ := hρ ((MulAut.conj h) ⟨y, hy⟩)
        refine ⟨x, ?_⟩
        rw [hπ'ρ, hx]
        simp [MulAut.conj_apply, mul_assoc]
    · ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [hπ'ρ]
        have : (MulAut.conj h⁻¹) (ρ t) ∈ D.subgroupOf π.range := by
          rw [← hh]
          exact ⟨ρ t, ⟨t, ht, rfl⟩, rfl⟩
        exact this
      · intro hy
        have hyR : y ∈ π.range := hDR hy
        have : (⟨y, hyR⟩ : ↥π.range) ∈ ((T.subgroupOf H).map ρ).map
            (MulAut.conj h⁻¹).toMonoidHom := by
          rw [hh]
          exact hy
        obtain ⟨_, ⟨t, ht, rfl⟩, hty⟩ := this
        refine ⟨t, ht, ?_⟩
        rw [hπ'ρ]
        exact congrArg Subtype.val hty
  rcases Alt7.eq_top_or_eq_alt hA7 with hR | hR
  · have hDR : Alt7.tsSub ≤ π.range := by rw [hR]; exact le_top
    have hD2 : IsPGroup 2 (Alt7.tsSub.subgroupOf π.range) :=
      Alt7.tsSub_isPGroup.comap_of_injective _ π.range.subtype_injective
    have hDi : ¬ 2 ∣ (Alt7.tsSub.subgroupOf π.range).index := by
      have h1 := (Alt7.tsSub.subgroupOf π.range).card_mul_index
      have h2 : Nat.card (Alt7.tsSub.subgroupOf π.range) = 16 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv, Alt7.card_tsSub]
      have h3 : Nat.card π.range = 5040 := by rw [hR, Subgroup.card_top, Alt7.card_perm7]
      rw [h2, h3] at h1
      rintro ⟨m, hm⟩
      omega
    obtain ⟨π', hk, hr, hm⟩ := key _ hDR hD2 hDi
    exact ⟨π', hk, hr ▸ hA7, Or.inl ⟨hr.trans hR, hm⟩⟩
  · have hDR : Alt7.taSub ≤ π.range := by
      rw [hR]
      intro g hg
      exact mem_alternatingGroup.mpr (Alt7.ta_sign g hg)
    have hD2 : IsPGroup 2 (Alt7.taSub.subgroupOf π.range) :=
      (IsPGroup.of_card (n := 3) (Alt7.card_taSub.trans (by norm_num))).comap_of_injective _
        π.range.subtype_injective
    have hDi : ¬ 2 ∣ (Alt7.taSub.subgroupOf π.range).index := by
      have h1 := (Alt7.taSub.subgroupOf π.range).card_mul_index
      have h2 : Nat.card (Alt7.taSub.subgroupOf π.range) = 8 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv, Alt7.card_taSub]
      have h3 : Nat.card π.range = 2520 := by rw [hR, Alt7.card_alt7]
      rw [h2, h3] at h1
      rintro ⟨m, hm⟩
      omega
    obtain ⟨π', hk, hr, hm⟩ := key _ hDR hD2 hDi
    exact ⟨π', hk, hr ▸ hA7, Or.inr ⟨hr.trans hR, hm⟩⟩

end CFSG.Quasithin.H13.L32A.C
