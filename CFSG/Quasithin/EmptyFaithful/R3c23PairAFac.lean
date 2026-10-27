module

public import CFSG.Quasithin.EmptyFaithful.R3c23Def
import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.Quasithin.Background.InternalSecB56

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace R3c23

open scoped commutatorElement

section Generic

variable {Ω : Type} [Group Ω]

theorem twoG_eq_of_normal_of_isQuasisimple {K E : Subgroup Ω} (hKE : K ≤ E)
    (hn : ∀ x ∈ E, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hE : CFSG.IsQuasisimple ↥E) : K = E := by
  have hnorm : (K.subgroupOf E).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hn g g.2 k hk
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hE) (K.subgroupOf E) with hc | htop
  · exfalso
    refine InternalSec.not_commute_of_isQuasisimple hK fun a ha b hb => ?_
    have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E := hc ha
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
    exact (congrArg Subtype.val h2).symm
  · refine le_antisymm hKE (fun e he => ?_)
    have : (⟨e, he⟩ : ↥E) ∈ K.subgroupOf E := by rw [htop]; trivial
    exact this

theorem twoG_eq_or_eq_of_normal [Finite Ω] {J L₁ L₂ K : Subgroup Ω}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂)
    (hL₁J : L₁ ≤ J) (hL₂J : L₂ ≤ J) (h2 : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hKJ : K ≤ J) (hKn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K = L₁ ∨ K = L₂ := by
  have hKL : K ≤ L₁ ⊔ L₂ :=
    (B1Red.perfect_le_oTwoUpper' hKJ hK.1).trans (oTwoUpper_le_of_pow_mem h2)
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le hL₁J hL₂J
  rcases InternalSec.le_or_le_of_sup_eq rfl hcomm hKL
    (fun x hx k hk => hKn x (hLJ hx) k hk) hK with h | h
  · exact Or.inl
      (twoG_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₁J hx) k hk) hK hq₁)
  · exact Or.inr
      (twoG_eq_of_normal_of_isQuasisimple h (fun x hx k hk => hKn x (hL₂J hx) k hk) hK hq₂)

theorem twoG_le_of_perfect_of_isSolvable {A B P : Subgroup Ω}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hPAB : P ≤ A ⊔ B) (hP : Group.IsPerfect ↥P)
    (hB : Group.IsSolvable ↥B) : P ≤ A := by
  set H := A ⊔ B with hH
  have hBH : B ≤ H := le_sup_right
  set N : Subgroup ↥H := A.subgroupOf H with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc g g.2 n hn
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (Subgroup.inclusion hBH)) := by
    intro q
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hc)).1 hh
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' N ⟨b, hBH hb⟩ = QuotientGroup.mk' N ⟨a * b, hh⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    show (b⁻¹ * (a * b) : Ω) ∈ A
    rw [hc a ha b hb, inv_mul_cancel_left]
    exact ha
  have : Group.IsSolvable (↥H ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hPH : P ≤ H := hPAB
  let φ : ↥P →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hPH)
  have hr : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro p hp
  have h1 : φ ⟨p, hp⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hr, Subgroup.mem_bot] at h1
  have h2 : (⟨p, hPH hp⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  exact h2

theorem twoG_isSolvable_of_card_six {H : Type*} [Group H] (h : Nat.card H = 6) :
    Group.IsSolvable H := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h]; norm_num : 3 ∣ Nat.card H)
  set P := Subgroup.zpowers x with hP
  have hPc : Nat.card ↥P = 3 := by rw [hP, Nat.card_zpowers, hx]
  have hidx : P.index = 2 := by
    have := P.card_mul_index
    rw [hPc, h] at this
    omega
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card hPc
  have hQc : Nat.card (H ⧸ P) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQcyc : IsCyclic (H ⧸ P) := isCyclic_of_prime_card hQc
  exact Group.isSolvable_of_subgroup_quotient P

theorem twoG_inf_eq_bot_of_commute {A B : Subgroup Ω} (hs : IsSimpleGroup ↥A)
    (hq : CFSG.IsQuasisimple ↥A) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊓ B = ⊥ := by
  have hcen : Subgroup.center ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A) with h | h
    · exact h
    · exfalso
      refine InternalSec.not_commute_of_isQuasisimple hq fun a ha b hb => ?_
      have h1 : (⟨b, hb⟩ : ↥A) ∈ Subgroup.center ↥A := by rw [h]; trivial
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨a, ha⟩)
  refine eq_bot_iff.2 fun x hx => ?_
  have hxc : (⟨x, hx.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2 x hx.2)
  rw [hcen, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hxc)

theorem twoG_card_mul_le_card_sup [Finite Ω] {A B : Subgroup Ω} (h : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) := by
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    simp only [f, Subtype.mk.injEq] at hab
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    have h3 : b = b' := mul_left_cancel hab
    subst h3
    rfl
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective f hf

end Generic

section Orders

theorem twoG_card_statedSL_two {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem twoG_card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

end Orders

section Factors

variable {Ω : Type} [Group Ω]

theorem twoG_charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem twoG_isQuasisimple_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : CFSG.IsQuasisimple Q := by
  have hnc : ∃ a b : Q, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := h }
    exact hp IsSimpleGroup.prime_card
  have hperf : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hab h1
    · exact h
  exact B1Red.isQuasisimple_of_open (CFSG.ComponentClassification.Quasisimple.simple_of_perfect Q)

theorem twoG_lin2Cover_facts {L : Type} [Group L] (h : Lin2Cover L) :
    IsSimpleGroup L ∧ 60 ≤ Nat.card L ∧ Nat.card L ≠ 168 := by
  obtain ⟨F, _, _, n, hn, hF, ⟨e⟩⟩ := h
  have hcard : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, twoG_card_statedSL_two]
  have : CharP F 2 := twoG_charP_two hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hs : IsSimpleGroup ↥(StatedSL 2 F) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have h16 : 16 ≤ Nat.card F ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h4 2
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · rw [hcard]
    calc 60 = 4 * 15 := by norm_num
      _ ≤ _ := Nat.mul_le_mul h4 (by omega)
  · rw [hcard]
    by_cases hn2 : n = 2
    · subst hn2
      rw [hF]
      norm_num
    · have h8 : 8 ≤ Nat.card F := by
        rw [hF]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h64 : 64 ≤ Nat.card F ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h8 2
      have : 8 * 63 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
      omega

theorem twoG_fac_of_simple [Finite Ω] {G : Subgroup Ω} (hs : IsSimpleGroup ↥G)
    (hp : ¬ (Nat.card ↥G).Prime) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      (K = G ∨ (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥K = 60)) :=
  ⟨G, le_rfl, fun _ hg _ hk => G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg),
    twoG_isQuasisimple_of_simple hp, Or.inl rfl⟩

theorem twoG_fac_of_perm_five {G : Subgroup Ω} (e : ↥G ≃* Equiv.Perm (Fin 5)) :
    ∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
      (K = G ∨ (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥K = 60)) := by
  set f : Equiv.Perm (Fin 5) →* Ω := G.subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := G.subtype_injective.comp e.symm.injective
  have hcard : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have hA5 : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 5)) :=
    twoG_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have e' := (alternatingGroup (Fin 5)).equivMapOfInjective f hfinj
  refine ⟨(alternatingGroup (Fin 5)).map f, ?_, ?_, ?_, Or.inr ⟨⟨e⟩, ?_⟩⟩
  · rintro _ ⟨σ, -, rfl⟩
    exact (e.symm σ).2
  · rintro g hg _ ⟨a, ha, rfl⟩
    have hg' : f (e ⟨g, hg⟩) = g := by simp [hf]
    refine ⟨e ⟨g, hg⟩ * a * (e ⟨g, hg⟩)⁻¹, Subgroup.Normal.conj_mem inferInstance a ha _, ?_⟩
    rw [map_mul, map_mul, map_inv, hg']
  · exact B1Red.isQuasisimple_of_open
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv e'.symm
        (B1Red.isQuasisimple_to_open hA5))
  · rw [← Nat.card_congr e'.toEquiv, hcard]

theorem twoG_fac_of_factorList [Finite Ω] {G : Subgroup Ω} (h : B56FactorList ↥G) :
    (∃ K : Subgroup Ω, K ≤ G ∧ (∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) ∧ CFSG.IsQuasisimple ↥K ∧
        (K = G ∨ (Nonempty (↥G ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥K = 60))) ∨
      (Group.IsSolvable ↥G ∧ 3 ∣ Nat.card ↥G) := by
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, hm, hmodd, hF, ⟨e⟩⟩
  · have hcard : Nat.card ↥G = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, twoG_card_statedSL_two]
    by_cases hn1 : n = 1
    · subst hn1
      right
      have h6 : Nat.card ↥G = 6 := by rw [hcard, hF]; norm_num
      exact ⟨twoG_isSolvable_of_card_six h6, by rw [h6]; norm_num⟩
    · left
      have : CharP F 2 := twoG_charP_two hF
      have h4 : 4 ≤ Nat.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hs : IsSimpleGroup ↥(StatedSL 2 F) :=
        CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      have : IsSimpleGroup ↥G := e.isSimpleGroup
      refine twoG_fac_of_simple this ?_
      rw [hcard]
      have h16 : 16 ≤ Nat.card F ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h4 2
      exact Nat.not_prime_mul (by omega) (by omega)
  · obtain ⟨e⟩ := he
    exact Or.inl (twoG_fac_of_perm_five e)
  · left
    have hcard : Nat.card ↥G =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr e.toEquiv, twoG_card_statedSL_three]
    have hs : IsSimpleGroup ↥(StatedSL 3 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hmodd
    have : IsSimpleGroup ↥G := e.isSimpleGroup
    refine twoG_fac_of_simple this ?_
    rw [hcard]
    have hq : 2 ≤ Nat.card F := by
      rw [hF]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h8 : 8 ≤ Nat.card F ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
    have h4 : 4 ≤ Nat.card F ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
    exact Nat.not_prime_mul (by omega) (by
      have : 3 * 7 ≤ (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega)

end Factors

end R3c23

end CFSG.Quasithin
