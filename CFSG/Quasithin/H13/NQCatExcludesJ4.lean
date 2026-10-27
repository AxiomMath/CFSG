module

public import CFSG.Quasithin.H13.NQTermNoncyclicAction
public import CFSG.Quasithin.H13.NQCatJ4Line

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped Pointwise

theorem map_mk_eq_top_of_isSylowOf {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X P : Subgroup G} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hP : IsSylowOf p P X) :
    (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
  obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
  have h1 := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
    (hXA.to_subgroup ⊤) le_top
  rw [h1, Sylow.coe_mapSurjective, hS₁]

theorem surjective_frattiniQuotient_of_isSylowOf {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {X P : Subgroup G} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hP : IsSylowOf p P X) :
    Function.Surjective (((QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 X))).comp (P.subgroupOf X).subtype) := by
  intro w
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈
      (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
    (map_mk_eq_top_of_isSylowOf hXA hP) ▸ mem_top _
  obtain ⟨y, hy, hyx⟩ := h1
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, coe_subtype, hyx]

theorem not_isCyclic_of_isSylowOf_of_card_eq_sq {G : Type} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {X P : Subgroup G} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hP : IsSylowOf p P X) : ¬ IsCyclic P := by
  intro hc
  have : IsCyclic (P.subgroupOf X) :=
    isCyclic_of_surjective (subgroupOfEquivOfLe hP.le).symm.toMonoidHom (MulEquiv.surjective _)
  have hWc : IsCyclic ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    isCyclic_of_surjective _ (surjective_frattiniQuotient_of_isSylowOf hXA hP)
  obtain ⟨-, -, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXA
  obtain ⟨w, hw⟩ := hWc.exists_generator
  have h1 : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ≤ p := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hw]
    exact orderOf_le_of_pow_eq_one hp.out.pos (hWpow w)
  rw [hW] at h1
  have h2 := hp.out.two_le
  nlinarith

theorem not_normalized_line
    {G : Type} [Group G] [Finite G] {T L M : Subgroup G}
    (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {P : Subgroup G} (hP : IsSylowOf p P X) (hPcard : Nat.card P = p ^ 2)
    {C : Subgroup G} (hCP : C ≤ P) (hC : Nat.card C = p)
    (hCn : ∀ n ∈ T, n ∈ normalizer (P : Set G) → ∀ c ∈ C, n * c * n⁻¹ ∈ C) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX : P ≤ X := hP.le
  have hLN : normalizer (L : Set G) ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have hTN : T ≤ normalizer (X : Set G) := (h.t_le.trans h.eq_normalizer.le).trans hLN
  have hLX : L ≤ normalizer (X : Set G) := le_normalizer.trans hLN
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, h.sylow.1, h.sylow.2⟩
  set AX := (CFSG.pCore 2 X).map X.subtype with hAXdef
  have hAX2 : IsPGroup 2 AX := CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : G) ∈ AX ↔ x ∈ CFSG.pCore 2 X := fun x =>
    mem_map_iff_mem (subtype_injective X)
  have hNAX : normalizer (X : Set G) ≤ normalizer (AX : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set G), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hAXT : AX ≤ T := by
    have h1 := hTtop.eq_of_le le_sup_left le_top
      (h.sylow.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
      (map_mk_eq_top_of_isSylowOf hXA hP) ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  set N := T ⊓ normalizer (P : Set G) with hN
  have hQdec : ∀ q ∈ T, ∃ a ∈ AX, a⁻¹ * q ∈ N := by
    intro q hq
    have hqP : IsSylowOf p (P.map (MulAut.conj q).toMonoidHom) X := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy)
      · rw [card_map_of_injective (MulAut.conj q).injective, hP.card_eq]
    obtain ⟨x, hx, hxP⟩ := SteinbergCC.exists_conj_eq_of_isSylowOf hP hqP
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have haA : x * y⁻¹ ∈ AX := by
      have h1 := hNA y (le_normalizer (hPX hy)) _ hya
      rwa [show y * (y⁻¹ * x) * y⁻¹ = x * y⁻¹ by group] at h1
    refine ⟨x * y⁻¹, haA, mem_inf.mpr ⟨mul_mem (inv_mem (hAXT haA)) hq,
      mem_normalizer_iff.mpr fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩⟩
    · have h1 : q * z * q⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom := by
        rw [hxP]
        exact ⟨z, hz, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : x * z' * x⁻¹ = q * z * q⁻¹ := hzz'
      have e : (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ = y * z' * y⁻¹ := by
        rw [show (x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹ =
          y * x⁻¹ * (q * z * q⁻¹) * x * y⁻¹ by group, ← hzz']
        group
      rw [e]
      exact mul_mem (mul_mem hy hz') (inv_mem hy)
    · have hu : y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y ∈ P :=
        mul_mem (mul_mem (inv_mem hy) hz) hy
      have h1 : x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ ∈
          P.map (MulAut.conj q).toMonoidHom := by
        rw [← hxP]
        exact ⟨_, hu, rfl⟩
      obtain ⟨z', hz', hzz'⟩ := h1
      have hzz' : q * z' * q⁻¹ =
          x * (y⁻¹ * ((x * y⁻¹)⁻¹ * q * z * ((x * y⁻¹)⁻¹ * q)⁻¹) * y) * x⁻¹ := hzz'
      have e : z = z' := by
        have h2 : q * z' * q⁻¹ = q * z * q⁻¹ := by rw [hzz']; group
        exact (mul_left_cancel (mul_right_cancel h2)).symm
      rw [e]
      exact hz'
  set π : X →* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 X)) with hπ
  have hconjmk : ∀ (g : G) (hg : g ∈ normalizer (X : Set G)) (x : X),
      normalizerFrattiniConj X ⟨g, hg⟩ (π x) = π (X.normalizerMonoidHom ⟨g, hg⟩ x) :=
    fun _ _ _ => rfl
  have hAtriv : ∀ (a : G) (ha : a ∈ AX) (haN : a ∈ normalizer (X : Set G)),
      normalizerFrattiniConj X ⟨a, haN⟩ = 1 := by
    intro a ha haN
    ext w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ v
    change normalizerFrattiniConj X ⟨a, haN⟩ (π x) = π x
    rw [hconjmk]
    rw [hπ, MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply (hmemA _).mp
    change (a * x * a⁻¹)⁻¹ * x ∈ AX
    have h1 := hNA (x : G)⁻¹ (le_normalizer (inv_mem x.2)) a⁻¹ (inv_mem ha)
    rw [inv_inv] at h1
    rw [show (a * (x : G) * a⁻¹)⁻¹ * x = a * ((x : G)⁻¹ * a⁻¹ * x) by group]
    exact mul_mem ha h1
  have hPXcard : Nat.card (P.subgroupOf X) = p ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPX).toEquiv, hPcard]
  have hπinj : Function.Injective (π.comp (P.subgroupOf X).subtype) :=
    ((surjective_frattiniQuotient_of_isSylowOf hXA hP).bijective_of_nat_card_le
      (by rw [hPXcard, hW])).1
  set Mline := (C.subgroupOf X).map π with hMline
  have : Group.IsPerfect L :=
    ⟨by rw [commutator_def]; exact (NQSetup.isCComponent_top_of_qtnq h).2.1⟩
  let ρL : L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hLX)
  have hTL : IsSylowOf 2 (T ⊓ L) L :=
    (hTtop.of_le h.t_le le_top).inf_of_le_normalizer h.l_le h.eq_normalizer.le
  obtain ⟨SL, hSL⟩ := hTL.exists_sylow_eq_subgroupOf
  obtain ⟨-, hWc, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXA
  have : IsMulCommutative ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := hWc
  have hρL : ρL ≠ 1 := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    intro h1
    apply hl1
    have h2 : ρL ⟨l, hlL⟩ = 1 := by rw [h1, MonoidHom.one_apply]
    have h3 : inclusion hLX ⟨(l : G), hlL⟩ = l := Subtype.ext rfl
    change (normalizerFrattiniConj X).comp (inclusion hLX) ⟨l, hlL⟩ = 1 at h2
    rwa [MonoidHom.comp_apply, h3] at h2
  have hMinv : ∀ s ∈ (SL : Subgroup L), ∀ w ∈ Mline, ρL s w ∈ Mline := by
    intro s hs w hw
    obtain ⟨c, hc, rfl⟩ := hw
    have hsT : (s : G) ∈ T := by
      have hs' : s ∈ (T ⊓ L).subgroupOf L := hSL ▸ hs
      exact (mem_inf.mp (mem_subgroupOf.mp hs')).1
    obtain ⟨a, ha, han⟩ := hQdec s hsT
    have haN : a ∈ normalizer (X : Set G) := hTN (hAXT ha)
    have hnN : a⁻¹ * (s : G) ∈ normalizer (X : Set G) := hTN (mem_inf.mp han).1
    have hsplit : (inclusion hLX s : normalizer (X : Set G)) =
        ⟨a, haN⟩ * ⟨a⁻¹ * (s : G), hnN⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, mul_inv_cancel_left]; rfl)
    change normalizerFrattiniConj X (inclusion hLX s) (π c) ∈ Mline
    rw [hsplit, map_mul, MulAut.mul_apply, hconjmk, hAtriv a ha haN, MulAut.one_apply]
    refine ⟨X.normalizerMonoidHom ⟨a⁻¹ * (s : G), hnN⟩ c, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    exact hCn _ (mem_inf.mp han).1 (mem_inf.mp han).2 _ (mem_subgroupOf.mp hc)
  rcases SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWpow hW ρL hρL SL Mline
      hMinv with hbot | htop
  ·
    have hC1 : 1 < Nat.card C := by
      rw [hC]
      exact hp.one_lt
    obtain ⟨c, hc1⟩ := (Subgroup.one_lt_card_iff_ne_bot C).mp hC1 |> fun hne =>
      (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have hcP : (c : G) ∈ P := hCP c.2
    have hmem : π ⟨c, hPX hcP⟩ ∈ Mline := ⟨⟨c, hPX hcP⟩, mem_subgroupOf.mpr c.2, rfl⟩
    rw [hbot, mem_bot] at hmem
    have h1 : (π.comp (P.subgroupOf X).subtype) ⟨⟨c, hPX hcP⟩, mem_subgroupOf.mpr hcP⟩ =
        (π.comp (P.subgroupOf X).subtype) 1 := by
      rw [map_one]
      exact hmem
    have h2 := congrArg (fun y : P.subgroupOf X => ((y : X) : G)) (hπinj h1)
    apply hc1
    exact Subtype.ext h2
  ·
    have h1 : Nat.card Mline ≤ Nat.card (C.subgroupOf X) :=
      Nat.card_le_card_of_surjective (π.subgroupMap (C.subgroupOf X))
        (π.subgroupMap_surjective (C.subgroupOf X))
    rw [htop, card_top, hW, Nat.card_congr (subgroupOfEquivOfLe (hCP.trans hPX)).toEquiv,
      hC] at h1
    have h2 := hp.two_le
    nlinarith

theorem exists_invariant_line_of_mulEquiv {S J' : Type*} [Group S] [Group J'] (ψ : S ≃* J')
    {A : Subgroup S} {C' : Subgroup J'} (hC'A : C' ≤ A.map ψ.toMonoidHom)
    (hC' : ∀ α : MulAut J', (A.map ψ.toMonoidHom).map α.toMonoidHom = A.map ψ.toMonoidHom →
      C'.map α.toMonoidHom = C') :
    C'.map ψ.symm.toMonoidHom ≤ A ∧ Nat.card (C'.map ψ.symm.toMonoidHom) = Nat.card C' ∧
      ∀ β : MulAut S, A.map β.toMonoidHom = A →
        (C'.map ψ.symm.toMonoidHom).map β.toMonoidHom = C'.map ψ.symm.toMonoidHom := by
  refine ⟨?_, card_map_of_injective ψ.symm.injective, fun β hβ => ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hC'A hc
    simpa using ha
  let α : MulAut J' := (ψ.symm.trans β).trans ψ
  have hα : ∀ x : S, α (ψ x) = ψ (β x) := fun x => by
    simp [α, MulEquiv.trans_apply]
  have hαs : ∀ y : J', ψ.symm (α y) = β (ψ.symm y) := fun y => by
    simp [α, MulEquiv.trans_apply]
  have hβA : ∀ a ∈ A, β a ∈ A := fun a ha => hβ ▸ ⟨a, ha, rfl⟩
  have hβA' : ∀ a ∈ A, ∃ a' ∈ A, β a' = a := fun a ha => by
    rw [← hβ] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact ⟨a', ha', rfl⟩
  have hαA : (A.map ψ.toMonoidHom).map α.toMonoidHom = A.map ψ.toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨β a, hβA a ha, (hα a).symm⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨a', ha', rfl⟩ := hβA' a ha
      exact ⟨ψ a', ⟨a', ha', rfl⟩, hα a'⟩
  have hαC := hC' α hαA
  apply le_antisymm
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have h1 : α c ∈ C' := hαC ▸ ⟨c, hc, rfl⟩
    exact ⟨α c, h1, hαs c⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [← hαC] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact ⟨ψ.symm c', ⟨c', hc', rfl⟩, (hαs c').symm⟩

theorem line_of_mulEquiv {S J' : Type*} [Group S] [Group J'] [Finite S] (ψ : S ≃* J') {p : ℕ}
    (hJ : ∀ A' : Subgroup J', IsPGroup p A' → ¬ IsCyclic A' → ∀ U' : Sylow 2 J',
      (A' : Set J') * ((U' : Subgroup J') : Set J') = ((U' : Subgroup J') : Set J') * A' →
      p = 11 ∧ Nat.card A' = 11 ^ 2 ∧ ∃ C' : Subgroup J', C' ≤ A' ∧ Nat.card C' = 11 ∧
        ∀ α : MulAut J', A'.map α.toMonoidHom = A' → C'.map α.toMonoidHom = C')
    (A : Subgroup S) (hA : IsPGroup p A) (hAc : ¬ IsCyclic A) (U : Sylow 2 S)
    (hAU : (A : Set S) * ((U : Subgroup S) : Set S) = ((U : Subgroup S) : Set S) * A) :
    p = 11 ∧ Nat.card A = 11 ^ 2 ∧ ∃ C : Subgroup S, C ≤ A ∧ Nat.card C = 11 ∧
      ∀ β : MulAut S, A.map β.toMonoidHom = A → C.map β.toMonoidHom = C := by
  have hψs : Function.Surjective ψ.toMonoidHom := ψ.surjective
  have hA'p : IsPGroup p (A.map ψ.toMonoidHom) := hA.map _
  have hA'c : ¬ IsCyclic (A.map ψ.toMonoidHom) := fun hc => hAc
    (isCyclic_of_surjective (A.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.toMonoidHom
      (MulEquiv.surjective _))
  have hU'coe : ((U.mapSurjective hψs : Sylow 2 J') : Subgroup J') =
      (U : Subgroup S).map ψ.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hA'U' : ((A.map ψ.toMonoidHom : Subgroup J') : Set J') *
      (((U.mapSurjective hψs : Sylow 2 J') : Subgroup J') : Set J') =
      (((U.mapSurjective hψs : Sylow 2 J') : Subgroup J') : Set J') *
        ((A.map ψ.toMonoidHom : Subgroup J') : Set J') := by
    rw [hU'coe, coe_map, coe_map, ← Set.image_mul, hAU, Set.image_mul]
  rcases hJ _ hA'p hA'c (U.mapSurjective hψs) hA'U' with ⟨hp11, hA'card, C', hC'A, hC'card, hC'inv⟩
  rcases exists_invariant_line_of_mulEquiv ψ hC'A hC'inv with ⟨h1, h2, h3⟩
  refine ⟨hp11, ?_, C'.map ψ.symm.toMonoidHom, h1, h2.trans hC'card, h3⟩
  rw [← hA'card]
  exact (card_map_of_injective ψ.injective).symm

theorem J4_line_of_mulEquiv
    {S : Type*} [Group S] [Finite S]
    (ψ₀ : S ≃* CFSG.Blueprint.NativeSporadic.J4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (A : Subgroup S) (hA : IsPGroup p A) (hAc : ¬ IsCyclic A) (U : Sylow 2 S)
    (hAU : (A : Set S) * ((U : Subgroup S) : Set S) = ((U : Subgroup S) : Set S) * A) :
    p = 11 ∧ Nat.card A = 11 ^ 2 ∧ ∃ C : Subgroup S, C ≤ A ∧ Nat.card C = 11 ∧
      ∀ β : MulAut S, A.map β.toMonoidHom = A → C.map β.toMonoidHom = C := by
  let ψ : S ≃* Sporadic.J4.J := ψ₀.trans (Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat)
  refine @line_of_mulEquiv S Sporadic.J4.J _ inferInstance _ ψ p
    (fun A' hA' hAc' U' hAU' => ?_) A hA hAc U hAU
  have hline := J4_noncyclic_prime_sylow_product_full_normalizer_preserves_line hp hp5 A' hA' hAc'
    U' hAU'
  rcases hline with ⟨hp11, -, hA'card, C', hC'A, hC'card, hC'inv, -⟩
  exact ⟨hp11, hA'card, C', hC'A, hC'card, hC'inv⟩

open CFSG.Quasithin.H13.NQTerm in
theorem original_characteristic_witness_excludes_normal_J4_quotient
    {G : Type} [Group G]
    [Finite G] {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    {Y K : Subgroup G} (hXTY : X ⊔ T ≤ Y) (hKY : K ≤ Y) (hKn : (K.subgroupOf Y).Normal)
    (hXK : X ≤ K) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) :
    IsEmpty ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) ≃*
      CFSG.Blueprint.NativeSporadic.J4) := by
  refine ⟨fun ψ₀ => ?_⟩
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  have hPX : P ≤ X := hP.le
  have hPK : P ≤ K := hPX.trans hXK
  have hnc :=
    original_characteristic_witness_normal_quotient_common_normalizer_action_is_noncyclic
      h hp hp5 hXL hXc hXA hW hLW hXTY hKY hKn hXK hZ P hP
  rcases hnc with ⟨hσinj, ⟨U', hU'⟩, hAU, -⟩
  set σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    with hσ
  set A := (P.subgroupOf K).map σ with hA
  have hrange : (σ.comp (P.subgroupOf K).subtype).range = A := by
    rw [MonoidHom.range_comp, range_subtype]
  let e : P.subgroupOf K ≃* A :=
    (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
  have hAp : IsPGroup p A := by
    have h1 : IsPGroup p (P.subgroupOf K) := by
      rw [← comap_subtype]
      exact hP.isPGroup.comap_subtype
    exact h1.map σ
  have hAnc : ¬ IsCyclic A := by
    intro hc
    apply not_isCyclic_of_isSylowOf_of_card_eq_sq hXA hW hP
    have : IsCyclic (P.subgroupOf K) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hPK).toMonoidHom
      (subgroupOfEquivOfLe hPK).surjective
  have hAU' : (A : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
      ((U' : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) :
        Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
      ((U' : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) :
        Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) * A := by
    rw [hU']
    exact hAU
  have hline := J4_line_of_mulEquiv ψ₀ hp hp5 A hAp hAnc U' hAU'
  rcases hline with ⟨hp11, hAcard, C, hCA, hCcard, hCinv⟩
  have hPcard : Nat.card P = p ^ 2 := by
    rw [hp11, ← hAcard, ← Nat.card_congr e.toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv]
  have hTY : T ≤ Y := le_sup_right.trans hXTY
  have hYK : Y ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKY).mp hKn
  have hTK : T ≤ normalizer (K : Set G) := hTY.trans hYK
  let τ : normalizer (K : Set G) →*
      MulAut ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
    (CFSG.SectionRank.Ccomm.autQuotient (center (K ⧸ CFSG.pCore 2 K))).comp
      ((CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 K)).comp K.normalizerMonoidHom)
  have hτ : ∀ (n : normalizer (K : Set G)) (k : K), τ n (σ k) = σ (K.normalizerMonoidHom n k) :=
    fun _ _ => rfl
  have hτA : ∀ n : normalizer (K : Set G), (n : G) ∈ normalizer (P : Set G) →
      A.map (τ n).toMonoidHom = A := by
    intro n hnP
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨K.normalizerMonoidHom n k, ?_, (hτ n k).symm⟩
      exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hnP k).mp (mem_subgroupOf.mp hk))
    · exact (Subgroup.card_map_of_injective (f := (τ n).toMonoidHom) (τ n).injective).symm.le
  set CP := ((C.comap σ) ⊓ P.subgroupOf K).map K.subtype with hCP
  have hCPP : CP ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_subgroupOf.mp (mem_inf.mp hk).2
  have hCPcard : Nat.card CP = p := by
    rw [hCP, card_map_of_injective K.subtype_injective, hp11, ← hCcard]
    let g : ((C.comap σ) ⊓ P.subgroupOf K : Subgroup K) → C :=
      fun k => ⟨σ k, (mem_inf.mp k.2).1⟩
    have hg : Function.Bijective g := by
      refine ⟨fun k₁ k₂ hk => ?_, fun c => ?_⟩
      · have h1 : σ (k₁ : K) = σ (k₂ : K) := congrArg Subtype.val hk
        have h2 : (⟨k₁, (mem_inf.mp k₁.2).2⟩ : P.subgroupOf K) = ⟨k₂, (mem_inf.mp k₂.2).2⟩ :=
          hσinj h1
        have h3 : (k₁ : K) = (k₂ : K) := congrArg (fun x : P.subgroupOf K => (x : K)) h2
        exact Subtype.ext h3
      · obtain ⟨y, hy, hyc⟩ := hCA c.2
        refine ⟨⟨y, mem_inf.mpr ⟨?_, hy⟩⟩, Subtype.ext hyc⟩
        rw [mem_comap, hyc]
        exact c.2
    exact Nat.card_congr (Equiv.ofBijective g hg)
  have hCPn : ∀ n ∈ T, n ∈ normalizer (P : Set G) → ∀ c ∈ CP, n * c * n⁻¹ ∈ CP := by
    intro n hnT hnP _ hc
    obtain ⟨k, hk, rfl⟩ := hc
    have hkC : σ k ∈ C := (mem_inf.mp hk).1
    have hkP : (k : G) ∈ P := mem_subgroupOf.mp (mem_inf.mp hk).2
    let nK : normalizer (K : Set G) := ⟨n, hTK hnT⟩
    have hCβ := hCinv (τ nK) (hτA nK hnP)
    refine ⟨K.normalizerMonoidHom nK k, mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [mem_comap, ← hτ nK k, ← hCβ]
      exact ⟨σ k, hkC, rfl⟩
    · exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hnP k).mp hkP)
  exact not_normalized_line h hp hp5 hXL hXc hXA hW hLW hP hPcard hCPP hCPcard hCPn

end CFSG.Quasithin.H13.NQCat
