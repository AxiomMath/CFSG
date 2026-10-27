module

public import CFSG.Quasithin.H13.NQRigidB3Aut
public import CFSG.Quasithin.H13.NQRigidB2
public import CFSG.Quasithin.H13.NQRigidCoreQuot

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Orbit

variable {H : Type*} [Group H]

theorem conjugate_inv_of_eq {K K' : Subgroup H} {g : H} (h : CFSG.conjugate K g = K') :
    CFSG.conjugate K' g⁻¹ = K := by
  rw [← h, conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem map_conj_map_of_conjugate {E : Type*} [Group E] (f : H →* E) {K K' : Subgroup H}
    {g : H} (h : CFSG.conjugate K g⁻¹ = K') :
    (K.map f).map (MulAut.conj (f g)).toMonoidHom = K'.map f := by
  rw [← h, map_conjugate_hom, CFSG.conjugate, map_inv f g, inv_inv]

theorem orbit_two_facts {K₁ K₂ : Subgroup H} (hne : K₂ ≠ K₁)
    (horb : ∀ h : H, CFSG.conjugate K₁ h = K₁ ∨ CFSG.conjugate K₁ h = K₂)
    {h₀ : H} (hh₀ : CFSG.conjugate K₁ h₀ = K₂) :
    (∀ g : H, CFSG.conjugate K₂ g = K₁ ∨ CFSG.conjugate K₂ g = K₂) ∧
      ∀ g : H, CFSG.conjugate K₁ g = K₁ ↔ CFSG.conjugate K₂ g = K₂ := by
  have h2 : ∀ g : H, CFSG.conjugate K₂ g = K₁ ∨ CFSG.conjugate K₂ g = K₂ := by
    intro g
    have h := horb (h₀ * g)
    rw [← conjugate_conjugate, hh₀] at h
    exact h
  refine ⟨h2, fun g => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · rcases h2 g with h3 | h3
    · exact absurd (conjugate_injective (h3.trans h1.symm)) hne
    · exact h3
  · rcases horb g with h3 | h3
    · exact h3
    · exact absurd (conjugate_injective (h3.trans h1.symm)).symm hne

theorem sup_normal_of_orbit_two {K₁ K₂ : Subgroup H}
    (horb : ∀ h : H, CFSG.conjugate K₁ h = K₁ ∨ CFSG.conjugate K₁ h = K₂)
    (horb₂ : ∀ g : H, CFSG.conjugate K₂ g = K₁ ∨ CFSG.conjugate K₂ g = K₂)
    (hswap : ∀ g : H, CFSG.conjugate K₁ g = K₁ ↔ CFSG.conjugate K₂ g = K₂) (hne : K₂ ≠ K₁) :
    (K₁ ⊔ K₂).Normal := by
  have hc : ∀ g : H, CFSG.conjugate (K₁ ⊔ K₂) g = K₁ ⊔ K₂ := by
    intro g
    have hsup : CFSG.conjugate (K₁ ⊔ K₂) g = CFSG.conjugate K₁ g ⊔ CFSG.conjugate K₂ g :=
      Subgroup.map_sup _ _ _
    rw [hsup]
    rcases horb g with h1 | h1
    · rw [h1, (hswap g).mp h1]
    · have h2 : CFSG.conjugate K₂ g = K₁ := by
        rcases horb₂ g with h3 | h3
        · exact h3
        · exact absurd (h1.symm.trans ((hswap g).mpr h3)) hne
      rw [h1, h2, sup_comm]
  refine ⟨fun n hn g => ?_⟩
  have h1 := hc g⁻¹
  rw [CFSG.conjugate, inv_inv] at h1
  rw [← h1]
  exact ⟨n, hn, rfl⟩

theorem le_normalizer_of_orbit_two {K₁ K₂ : Subgroup H}
    (horb : ∀ h : H, CFSG.conjugate K₁ h = K₁ ∨ CFSG.conjugate K₁ h = K₂)
    (horb₂ : ∀ g : H, CFSG.conjugate K₂ g = K₁ ∨ CFSG.conjugate K₂ g = K₂)
    (hswap : ∀ g : H, CFSG.conjugate K₁ g = K₁ ↔ CFSG.conjugate K₂ g = K₂) (hne : K₂ ≠ K₁)
    {X : Subgroup H} (hX2 : NoPQuotient 2 X) : X ≤ normalizer (K₁ : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (normalizer (K₁ : Set H)).subgroupOf X with hN
  have hsq : ∀ g : H, g * g ∈ normalizer (K₁ : Set H) := by
    intro g
    rw [← conjugate_eq_self_iff, ← conjugate_conjugate]
    rcases horb g with h1 | h1
    · rw [h1, h1]
    · rw [h1]
      rcases horb₂ g with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans ((hswap g).mpr h2)) hne
  have hNn : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [hN, mem_subgroupOf] at hn ⊢
    rw [← conjugate_eq_self_iff] at hn ⊢
    have hn₂ : CFSG.conjugate K₂ (n : H) = K₂ := (hswap _).mp hn
    rw [coe_mul, coe_mul, coe_inv, ← conjugate_conjugate, ← conjugate_conjugate]
    rcases horb (x : H) with h1 | h1
    · rw [h1, hn]
      exact conjugate_inv_of_eq h1
    · rw [h1, hn₂]
      exact conjugate_inv_of_eq h1
  have := hNn
  have hq : IsPGroup 2 (X ⧸ N) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, mem_subgroupOf, coe_pow,
      sq]
    exact hsq x
  have htop := hX2 N hq
  intro x hx
  have h1 : (⟨x, hx⟩ : X) ∈ N := htop ▸ mem_top _
  exact h1

end Orbit

theorem index_le_two_of_mul_mem {Γ : Type*} [Group Γ] (S : Subgroup Γ)
    (h : ∀ a b : Γ, a ∉ S → b ∉ S → b * a ∈ S) : S.index ≤ 2 := by
  by_cases hS : ∃ a, a ∉ S
  · obtain ⟨a, ha⟩ := hS
    have h2 : S.index = 2 := index_eq_two_iff_exists_notMem_and.mpr ⟨a, ha, fun b => by
      by_cases hb : b ∈ S
      · exact Or.inr hb
      · exact Or.inl (h a b ha hb)⟩
    omega
  · have htop : S = ⊤ := eq_top_iff.mpr fun a _ => not_exists_not.mp hS a
    rw [htop, index_top]
    norm_num

theorem exists_inner_of_mem_inner {E : Type*} [Group E] {J : Subgroup E}
    (y : normalizer (J : Set E)) (h : J.normalizerMonoidHom y ∈ inner J) :
    ∃ j ∈ J, ∀ z ∈ J, (y : E) * z * (y : E)⁻¹ = j * z * j⁻¹ := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, j.2, fun z hz => ?_⟩
  have h1 : ((MulAut.conj j ⟨z, hz⟩ : J) : E) = ((J.normalizerMonoidHom y ⟨z, hz⟩ : J) : E) := by
    rw [hj]
  exact h1.symm

theorem one_le_pRank_of_dvd {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card J) : 1 ≤ CFSG.pRank p J := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := J) p h
  have hE : CFSG.IsElementaryAbelian p (zpowers g) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hg]; exact pow_orderOf_eq_one g)
  have hcard : Nat.card (zpowers g) = p ^ 1 := by rw [Nat.card_zpowers, hg, pow_one]
  exact SteinbergBS.le_pRank_of_card hp.one_lt hE hcard

variable {H : Type*} [Group H] [Finite H]

theorem derived_coprime_outer_two_component_orbit_forces_pair_containment {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpH : CFSG.pRank p H ≤ 2) (C : Subgroup H) [C.Normal]
    (hC : IsPGroup 2 C) {K₁ K₂ : Subgroup H} (hK₁ : CFSG.IsCComponent K₁) (hne : K₂ ≠ K₁)
    (horb : ∀ h : H, CFSG.conjugate K₁ h = K₁ ∨ CFSG.conjugate K₁ h = K₂)
    (hex : ∃ h : H, CFSG.conjugate K₁ h = K₂)
    (hJ₁ : CFSG.IsComponent (K₁.map (QuotientGroup.mk' C)))
    (hZ : ¬ p ∣ Nat.card (center (K₁.map (QuotientGroup.mk' C))))
    (hOD : ¬ p ∣ Nat.card (commutator (Outer (K₁.map (QuotientGroup.mk' C)))))
    {X A : Subgroup H} (Q : Subgroup X) [Q.Normal] (hXA : X ≤ A)
    (hAQ : A ≤ normalizer ((Q.map X.subtype : Subgroup H) : Set H))
    (hAX : A ≤ normalizer (X : Set H)) (hQ2 : IsPGroup 2 Q) (hpow : ∀ x : X, x ^ p ∈ Q)
    (hX2 : NoPQuotient 2 X) (hdim : p ^ 2 ≤ Nat.card ((X ⧸ Q) ⧸ frattini (X ⧸ Q)))
    (hlat : IsFrattiniLatticeIrreducible X A Q)
    (hJX : ⁅(K₁ ⊔ K₂).map (QuotientGroup.mk' C), X.map (QuotientGroup.mk' C)⁆ ≠ ⊥) :
    X ≤ K₁ ⊔ K₂ ∧ (K₁ ⊔ K₂).Normal ∧
      (∀ x ∈ X.map (QuotientGroup.mk' C), ∃ j ∈ (K₁ ⊔ K₂).map (QuotientGroup.mk' C),
        ∀ y ∈ (K₁ ⊔ K₂).map (QuotientGroup.mk' C), x * y * x⁻¹ = j * y * j⁻¹) ∧
      CFSG.pRank p ((K₁ ⊔ K₂).map (QuotientGroup.mk' C)) = 2 ∧
      CFSG.pRank p (K₁.map (QuotientGroup.mk' C)) = 1 ∧
      CFSG.pRank p (K₂.map (QuotientGroup.mk' C)) = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' C with hπ
  obtain ⟨h₀, hh₀⟩ := hex
  obtain ⟨horb₂, hswap⟩ := orbit_two_facts hne horb hh₀
  have hK₀n : (K₁ ⊔ K₂).Normal := sup_normal_of_orbit_two horb horb₂ hswap hne
  have hK₂ : CFSG.IsCComponent K₂ := hh₀ ▸ isCComponent_conjugate hK₁ h₀
  have hCsolv : Group.IsSolvable C := by
    have : Group.IsNilpotent C := hC.isNilpotent
    infer_instance
  set J₁ := K₁.map π with hJ₁def
  set J₂ := K₂.map π with hJ₂def
  set J₀ := (K₁ ⊔ K₂).map π with hJ₀def
  have hJ₀ : J₀ = J₁ ⊔ J₂ := map_sup _ _ _
  have hJ₂map : J₁.map (MulAut.conj (π h₀)⁻¹).toMonoidHom = J₂ := by
    rw [hJ₂def, ← hh₀, map_conjugate_hom]
    rfl
  set φ₁₂ : J₁ ≃* J₂ := conjEquivOfMap _ hJ₂map with hφ₁₂
  have hJ₂ : CFSG.IsComponent J₂ := by
    have h1 := NQTerm.isComponent_conjugate hJ₁ (π h₀)
    rwa [CFSG.conjugate, hJ₂map] at h1
  have hJne : J₁ ≠ J₂ := fun h => hne (eq_of_map_eq_of_isCComponent hCsolv hK₂ hK₁ h.symm)
  have hJc : ⁅J₁, J₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hJ₁ hJ₂).resolve_left hJne
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := fun a ha b hb =>
    ((mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hJc) ha)) b hb).symm
  have hZ₂ : ¬ p ∣ Nat.card (center J₂) := by
    rw [card_center_congr φ₁₂]
    exact hZ
  have hOD₂ : ¬ p ∣ Nat.card (commutator (Outer J₂)) := by
    rw [card_commutator_outer_congr φ₁₂]
    exact hOD
  have hrk₁₂ : CFSG.pRank p J₂ = CFSG.pRank p J₁ := pRank_congr hp.one_lt φ₁₂.symm
  have hXK₁ : X ≤ normalizer (K₁ : Set H) := le_normalizer_of_orbit_two horb horb₂ hswap hne hX2
  have hXK₂ : X ≤ normalizer (K₂ : Set H) := fun x hx => by
    rw [← conjugate_eq_self_iff, ← hswap x]
    exact conjugate_eq_self_iff.mpr (hXK₁ hx)
  set A₁ : Subgroup A :=
    (normalizer (J₁ : Set (H ⧸ C)) ⊓ normalizer (J₂ : Set (H ⧸ C))).comap (π.comp A.subtype)
    with hA₁
  set N₀ : Subgroup A := (aut0Pre J₁ ⊓ aut0Pre J₂).comap (π.comp A.subtype) with hN₀
  have hN₀A₁ : N₀ ≤ A₁ := fun a ha => ⟨aut0Pre_le J₁ ha.1, aut0Pre_le J₂ ha.2⟩
  have hswapA : ∀ a : A, a ∉ A₁ → CFSG.conjugate K₁ (a : H) = K₂ := by
    intro a ha
    rcases horb a with h1 | h1
    · exfalso
      apply ha
      have h2 := (hswap a).mp h1
      exact ⟨le_normalizer_map π ⟨a, conjugate_eq_self_iff.mp h1, rfl⟩,
        le_normalizer_map π ⟨a, conjugate_eq_self_iff.mp h2, rfl⟩⟩
    · exact h1
  have hmapA : ∀ a : A, a ∉ A₁ → J₂.map (MulAut.conj (π (a : H))).toMonoidHom = J₁ ∧
      J₁.map (MulAut.conj (π (a : H))).toMonoidHom = J₂ := by
    intro a ha
    have h1 := hswapA a ha
    have h2 : CFSG.conjugate K₂ (a : H) = K₁ := by
      rcases horb₂ a with h3 | h3
      · exact h3
      · exact absurd (h1.symm.trans ((hswap a).mpr h3)) hne
    exact ⟨map_conj_map_of_conjugate π (conjugate_inv_of_eq h1),
      map_conj_map_of_conjugate π (conjugate_inv_of_eq h2)⟩
  have hN₀n : N₀.Normal := by
    refine ⟨fun n hn a => ?_⟩
    change π ((a : H) * n * (a : H)⁻¹) ∈ aut0Pre J₁ ⊓ aut0Pre J₂
    rw [map_mul, map_mul, map_inv]
    obtain ⟨hn₁, hn₂⟩ := hn
    by_cases haA : a ∈ A₁
    · exact ⟨conj_mem_aut0Pre haA.1 hn₁, conj_mem_aut0Pre haA.2 hn₂⟩
    · obtain ⟨e₂₁, e₁₂⟩ := hmapA a haA
      exact ⟨conj_mem_aut0Pre_of_map e₂₁ hn₂, conj_mem_aut0Pre_of_map e₁₂ hn₁⟩
  have := hN₀n
  set D : Subgroup (A ⧸ N₀) := A₁.map (QuotientGroup.mk' N₀) with hD
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    change π ((⁅b⁻¹, a⁻¹⁆ : A) : H) ∈ aut0Pre J₁ ⊓ aut0Pre J₂
    have e2 : π ((⁅b⁻¹, a⁻¹⁆ : A) : H) = ⁅(π (b : H))⁻¹, (π (a : H))⁻¹⁆ := by
      simp only [commutatorElement_def, coe_mul, coe_inv, map_mul, map_inv]
    rw [e2]
    exact ⟨commutatorElement_mem_aut0Pre (inv_mem hb.1) (inv_mem ha.1),
      commutatorElement_mem_aut0Pre (inv_mem hb.2) (inv_mem ha.2)⟩
  have hA₁idx : A₁.index ≤ 2 := by
    refine index_le_two_of_mul_mem A₁ fun a b ha hb => ?_
    have h1 := hswapA a ha
    have h2 := hswapA b hb
    have h3 : CFSG.conjugate K₁ ((b * a : A) : H) = K₁ := by
      rw [coe_mul, ← conjugate_conjugate, h2]
      rcases horb₂ a with h4 | h4
      · exact h4
      · exact absurd (h1.symm.trans ((hswap a).mpr h4)) hne
    have h4 := (hswap _).mp h3
    exact ⟨le_normalizer_map π ⟨_, conjugate_eq_self_iff.mp h3, rfl⟩,
      le_normalizer_map π ⟨_, conjugate_eq_self_iff.mp h4, rfl⟩⟩
  have hDidx : D.index ≤ 2 := by
    rw [hD, index_map_eq A₁ (QuotientGroup.mk'_surjective N₀)
      (by rw [QuotientGroup.ker_mk']; exact hN₀A₁)]
    exact hA₁idx
  have hDn : D.Normal := by
    have h0 : D.index ≠ 0 := index_ne_zero_of_finite
    rcases (show D.index = 1 ∨ D.index = 2 by omega) with h1 | h1
    · rw [index_eq_one.mp h1]
      infer_instance
    · exact normal_of_index_eq_two h1
  have : (resQ A Q).Normal := resQ_normal Q hXA hAQ
  have : (X.subgroupOf A).Normal := resX_normal hXA hAX
  have hW' : p ^ 2 ≤ Nat.card ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)) ⧸
      frattini ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)))) := by
    rw [card_frattini_resBar Q hXA]
    exact hdim
  have hXN₀ := SteinbergBT.irreducible_two_prime_residual_killed_by_abelian_index_two_target hp
    (resQ A Q) (X.subgroupOf A) (resQ_le_resX Q) (isPGroup_resQ Q hQ2)
    (pow_eq_one_resBar Q hpow) (noPQuotient_resX hXA hX2) hW' (irreducible_resBar Q hXA hlat)
    D hDc hDidx (QuotientGroup.mk' N₀)
  have hXin : ∀ x ∈ X, π x ∈ aut0Pre J₁ ∧ π x ∈ aut0Pre J₂ := by
    intro x hx
    have h1 : QuotientGroup.mk' N₀ (⟨x, hXA hx⟩ : A) ∈
        (X.subgroupOf A).map (QuotientGroup.mk' N₀) := ⟨_, mem_subgroupOf.mpr hx, rfl⟩
    rw [hXN₀, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hXcard : ∃ a b : ℕ, Nat.card X = 2 ^ a * p ^ b :=
    card_eq_two_pow_mul_prime_pow (isPGroup_coreQuot_of_pow_mem Q hQ2 hpow)
  have hinner_of : ∀ J : Subgroup (H ⧸ C), (∀ x ∈ X, π x ∈ normalizer (J : Set (H ⧸ C))) →
      ¬ p ∣ Nat.card (commutator (Outer J)) → (∀ x ∈ X, π x ∈ aut0Pre J) →
      ∀ x ∈ X, ∃ j ∈ J, ∀ y ∈ J, π x * y * (π x)⁻¹ = j * y * j⁻¹ := by
    intro J hXJ hODJ hX0 x hx
    set f : X →* normalizer (J : Set (H ⧸ C)) :=
      (π.comp X.subtype).codRestrict _ (fun x => hXJ x x.2) with hf
    have h1 := inner_of_mem_aut0Pre hp hX2 hXcard hODJ f (fun x => hX0 x x.2) ⟨x, hx⟩
    exact exists_inner_of_mem_inner (f ⟨x, hx⟩) h1
  have hinner₁ := hinner_of J₁ (fun x hx => le_normalizer_map π ⟨x, hXK₁ hx, rfl⟩) hOD
    (fun x hx => (hXin x hx).1)
  have hinner₂ := hinner_of J₂ (fun x hx => le_normalizer_map π ⟨x, hXK₂ hx, rfl⟩) hOD₂
    (fun x hx => (hXin x hx).2)
  have hinner0 : ∀ x ∈ X.map π, ∃ j ∈ J₀, ∀ y ∈ J₀, x * y * x⁻¹ = j * y * j⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j₁, hj₁, hx₁⟩ := hinner₁ x hx
    obtain ⟨j₂, hj₂, hx₂⟩ := hinner₂ x hx
    refine ⟨j₁ * j₂, ?_, ?_⟩
    · rw [hJ₀]
      exact mul_mem (mem_sup_left hj₁) (mem_sup_right hj₂)
    · have hle : J₀ ≤ (MulAut.conj (π x)).toMonoidHom.eqLocus
          (MulAut.conj (j₁ * j₂)).toMonoidHom := by
        rw [hJ₀]
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · change π x * y * (π x)⁻¹ = j₁ * j₂ * y * (j₁ * j₂)⁻¹
          rw [hx₁ y hy]
          have h1 : j₂ * y = y * j₂ := (hcomm y hy j₂ hj₂).symm
          calc j₁ * y * j₁⁻¹ = j₁ * (y * j₂) * j₂⁻¹ * j₁⁻¹ := by group
            _ = j₁ * (j₂ * y) * j₂⁻¹ * j₁⁻¹ := by rw [h1]
            _ = j₁ * j₂ * y * (j₁ * j₂)⁻¹ := by group
        · change π x * y * (π x)⁻¹ = j₁ * j₂ * y * (j₁ * j₂)⁻¹
          rw [hx₂ y hy]
          have hw : j₂ * y * j₂⁻¹ ∈ J₂ := J₂.mul_mem (J₂.mul_mem hj₂ hy) (J₂.inv_mem hj₂)
          have h1 : j₁ * (j₂ * y * j₂⁻¹) = j₂ * y * j₂⁻¹ * j₁ := hcomm j₁ hj₁ _ hw
          calc j₂ * y * j₂⁻¹ = j₁ * (j₂ * y * j₂⁻¹) * j₁⁻¹ := by rw [h1]; group
            _ = j₁ * j₂ * y * (j₁ * j₂)⁻¹ := by group
      exact fun y hy => hle hy
  have hJ₀n : J₀.Normal := hK₀n.map π (QuotientGroup.mk'_surjective C)
  have hAJ₀ : ∀ a : A, π a ∈ normalizer (J₀ : Set (H ⧸ C)) := fun a => by
    rw [normalizer_eq_top_iff.mpr hJ₀n]
    exact mem_top _
  set α : A →* MulAut J₀ :=
    J₀.normalizerMonoidHom.comp ((π.comp A.subtype).codRestrict _ hAJ₀) with hα
  have hαapp : ∀ (a : A) (y : J₀), ((α a y : J₀) : H ⧸ C) = π a * y * (π a)⁻¹ := fun _ _ => rfl
  have hαX : (X.subgroupOf A).map α ≠ ⊥ := by
    intro h0
    apply hJX
    rw [commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : α ⟨x, hXA hx⟩ ∈ (X.subgroupOf A).map α := ⟨_, mem_subgroupOf.mpr hx, rfl⟩
    rw [h0, mem_bot] at h1
    have h2 := congrArg (fun θ : MulAut J₀ => ((θ ⟨j, hj⟩ : J₀) : H ⧸ C)) h1
    simp only [MulAut.one_apply] at h2
    rw [hαapp] at h2
    calc π x * j = π x * j * (π x)⁻¹ * π x := by group
      _ = j * π x := by rw [show π x * j * (π x)⁻¹ = j from h2]
  have hrkα : 2 ≤ CFSG.pRank p ((X.subgroupOf A).map α) :=
    (SteinbergBT.irreducible_two_prime_residual_image_rank_dichotomy hp hp2
      (resQ A Q) (X.subgroupOf A) (resQ_le_resX Q) (isPGroup_resQ Q hQ2)
      (pow_eq_one_resBar Q hpow) (noPQuotient_resX hXA hX2) hW' (irreducible_resBar Q hXA hlat)
      α).1.resolve_left hαX
  have hαinner : (X.subgroupOf A).map α ≤ inner J₀ := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨j, hj, hjy⟩ := hinner0 (π a) ⟨a, mem_subgroupOf.mp ha, rfl⟩
    refine ⟨⟨j, hj⟩, ?_⟩
    ext y
    change j * (y : H ⧸ C) * j⁻¹ = π a * y * (π a)⁻¹
    exact (hjy y y.2).symm
  have hZ₀ : ¬ p ∣ Nat.card (center J₀) := by
    rw [hJ₀]
    exact not_dvd_card_center_sup hp hJc hZ hZ₂
  have hrkJ₀2 : 2 ≤ CFSG.pRank p J₀ := by
    rw [← pRank_inner_eq hp hZ₀]
    have h1 : CFSG.pRank p ((X.subgroupOf A).map α) ≤ CFSG.pRank p (inner J₀) := by
      have h2 := pRank_le_of_subgroup p hp.one_lt
        (((X.subgroupOf A).map α).subgroupOf (inner J₀))
      rwa [pRank_congr hp.one_lt (subgroupOfEquivOfLe hαinner)] at h2
    omega
  have hrkE : CFSG.pRank p (H ⧸ C) = CFSG.pRank p H :=
    pRank_quotient_of_isPGroup_two C hC hp hp2
  have hrkJ₀E : CFSG.pRank p J₀ ≤ CFSG.pRank p (H ⧸ C) := pRank_le_of_subgroup p hp.one_lt J₀
  have hrkJ₀ : CFSG.pRank p J₀ = 2 := by omega
  have hsat : CFSG.pRank p J₀ = CFSG.pRank p (H ⧸ C) := by omega
  obtain ⟨-, hinc⟩ :=
    SteinbergBT.rank_saturating_prime_centralizer_and_inner_containment hp J₀ hZ₀ hsat
  have := hK₀n
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_coreQuot_of_pow_mem Q hQ2 hpow
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p X))
  set P : Subgroup H := (P₀ : Subgroup X).map X.subtype with hP
  have hPX : P ≤ X := map_subtype_le _
  have hPp : IsPGroup p (P.map π) := (P₀.isPGroup'.map X.subtype).map π
  have hPJ : P.map π ≤ J₀ := by
    refine hinc (P.map π) hPp ?_ ?_
    · rw [normalizer_eq_top_iff.mpr hJ₀n]
      exact le_top
    · exact fun x hx => hinner0 x (map_mono hPX hx)
  have hPKC : P ≤ (K₁ ⊔ K₂) ⊔ C := by
    intro x hx
    have h1 : π x ∈ J₀ := hPJ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := h1
    have h2 : k⁻¹ * x ∈ C := by
      rw [← QuotientGroup.eq]
      exact hkx
    have h4 := mul_mem (mem_sup_left hk : k ∈ (K₁ ⊔ K₂) ⊔ C)
      (mem_sup_right h2 : k⁻¹ * x ∈ (K₁ ⊔ K₂) ⊔ C)
    rwa [mul_inv_cancel_left] at h4
  have hKCn : ((K₁ ⊔ K₂) ⊔ C).Normal := inferInstance
  have hXKC : X ≤ (K₁ ⊔ K₂) ⊔ C := by
    have h1 : X ≤ X ⊓ ((K₁ ⊔ K₂) ⊔ C) := by
      refine le_of_noPQuotient_two hX2 le_rfl inf_le_left (le_normalizer_inf_of_normal hKCn) ?_
      have hPN : (P₀ : Subgroup X) ≤ (X ⊓ ((K₁ ⊔ K₂) ⊔ C)).subgroupOf X := by
        intro y hy
        rw [mem_subgroupOf]
        exact ⟨y.2, hPKC ⟨y, hy, rfl⟩⟩
      obtain ⟨k, hk⟩ := index_dvd_two_pow_of_sylow_le hp2 hXp P₀ hPN
      exact ⟨k, hk⟩
    exact h1.trans inf_le_right
  have hXK₀ : X ≤ K₁ ⊔ K₂ := by
    refine le_of_noPQuotient_two hX2 hXKC le_sup_left ?_ ?_
    · rw [normalizer_eq_top_iff.mpr hK₀n]
      exact le_top
    · obtain ⟨k, hk⟩ := hC.exists_card_eq
      refine ⟨k, ?_⟩
      rw [sup_comm (K₁ ⊔ K₂) C,
        CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal C (K₁ ⊔ K₂), ← hk]
      exact relIndex_dvd_card (K₁ ⊔ K₂) C
  have hJ₁rk1 : 1 ≤ CFSG.pRank p J₁ := by
    by_contra hlt
    have h1 : ¬ p ∣ Nat.card J₁ := fun h => hlt (one_le_pRank_of_dvd hp h)
    have h2 : ¬ p ∣ Nat.card J₂ := fun h => hlt (by
      rw [← hrk₁₂]
      exact one_le_pRank_of_dvd hp h)
    have h3 : ¬ p ∣ Nat.card J₀ := by
      intro hdvd
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := J₀) p hdvd
      have hz' : (z : H ⧸ C) ∈ J₁ ⊔ J₂ := hJ₀ ▸ z.2
      obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := exists_mul_of_mem_sup hJc hz'
      have ho₁ : ¬ p ∣ orderOf j₁ := fun h => h1 (h.trans (by
        rw [← Subgroup.orderOf_mk j₁ hj₁]
        exact orderOf_dvd_natCard _))
      have ho₂ : ¬ p ∣ orderOf j₂ := fun h => h2 (h.trans (by
        rw [← Subgroup.orderOf_mk j₂ hj₂]
        exact orderOf_dvd_natCard _))
      have h4 : orderOf (j₁ * j₂) = p := by rw [hj, Subgroup.orderOf_coe, hz]
      exact not_dvd_orderOf_mul hp (hcomm j₁ hj₁ j₂ hj₂) ho₁ ho₂ (h4 ▸ dvd_refl p)
    exact h3 (prime_dvd_card_of_pRank_pos hp (by omega))
  have hJ₁rk : CFSG.pRank p J₁ ≤ 1 := by
    by_contra hlt
    obtain ⟨B₁, hB₁, hB₁c⟩ := SteinbergBM.exists_card_eq_pow_pRank (X := J₁) hp.one_lt
    obtain ⟨B₂, hB₂, hB₂c⟩ := SteinbergBM.exists_card_eq_pow_pRank (X := J₂) hp.one_lt
    have := hB₁
    have := hB₂
    set E₁ : Subgroup (H ⧸ C) := B₁.map J₁.subtype with hE₁
    set E₂ : Subgroup (H ⧸ C) := B₂.map J₂.subtype with hE₂
    have hE₁e : CFSG.IsElementaryAbelian p E₁ := CFSG.IsElementaryAbelian.map_subtype
    have hE₂e : CFSG.IsElementaryAbelian p E₂ := CFSG.IsElementaryAbelian.map_subtype
    have hE₂E₁ : E₂ ≤ centralizer (E₁ : Set (H ⧸ C)) := by
      rintro _ ⟨b, -, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨a, -, rfl⟩
      exact hcomm a a.2 b b.2
    have hdisj : E₁ ⊓ E₂ = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨a, haB, rfl⟩, hx₂⟩
      have hxJ₂ : ((a : J₁) : H ⧸ C) ∈ J₂ := map_subtype_le _ hx₂
      have haZ : a ∈ center J₁ := by
        rw [mem_center_iff]
        intro y
        apply Subtype.ext
        exact hcomm y y.2 _ hxJ₂
      have hapow : a ^ p = 1 := by
        have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (CFSG.IsElementaryAbelian.exponent_dvd_p p B₁) ⟨a, haB⟩
        have h2 := congrArg Subtype.val h1
        exact h2
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hapow) with h1 | h1
      · rw [orderOf_eq_one_iff] at h1
        rw [mem_bot, h1, map_one]
      · exfalso
        apply hZ
        have h2 : orderOf (⟨a, haZ⟩ : center J₁) = p := by rw [Subgroup.orderOf_mk, h1]
        exact h2 ▸ orderOf_dvd_natCard (⟨a, haZ⟩ : center J₁)
    have hcard : Nat.card (E₁ ⊔ E₂ : Subgroup (H ⧸ C)) =
        p ^ (CFSG.pRank p J₁ + CFSG.pRank p J₂) := by
      rw [SteinbergBM.card_sup_of_commute hE₂E₁ hdisj, hE₁, hE₂,
        card_map_of_injective J₁.subtype_injective, card_map_of_injective J₂.subtype_injective,
        hB₁c, hB₂c, pow_add]
    have hsupe : CFSG.IsElementaryAbelian p (E₁ ⊔ E₂ : Subgroup (H ⧸ C)) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer hE₂E₁
    have hle := SteinbergBS.le_pRank_of_card hp.one_lt hsupe hcard
    omega
  refine ⟨hXK₀, hK₀n, hinner0, hrkJ₀, by omega, by omega⟩

theorem stmtPairContainment_holds : StmtPairContainment :=
  fun _ _ _ _ hp hp2 hpH C _ hC _ _ hK₁ hne horb hex hJ₁ hZ hOD _ _ Q _ hXA hAQ hAX hQ2 hpow
      hX2 hdim hlat hJX =>
    derived_coprime_outer_two_component_orbit_forces_pair_containment hp hp2 hpH C hC hK₁ hne
      horb hex hJ₁ hZ hOD Q hXA hAQ hAX hQ2 hpow hX2 hdim hlat hJX

end CFSG.Quasithin.H13.NQRigid
