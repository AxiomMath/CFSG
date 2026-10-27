module

import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_sup_le {A R L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) :
    A ⊔ R ⊔ L ≤ Subgroup.normalizer (L : Set G) :=
  sup_le (sup_le hAL hRL) Subgroup.le_normalizer

theorem mem_thetaComponents_subgroupOf_of_le_normalizer {L H : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLH : L ≤ H) (hHL : H ≤ Subgroup.normalizer (L : Set G)) :
    L.subgroupOf H ∈ thetaComponents 3 H := by
  set e := Subgroup.subgroupOfEquivOfLe hLH
  have hθ := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e.symm
  refine ⟨?_, ?_, ?_⟩
  · have : Group.IsPerfect L := hL.1
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · refine (⟨fun x hx h => ?_⟩ : (L.subgroupOf H).Normal).isSubnormal
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) _).mp hx
  · exact isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e.symm hθ) hL.2.2

omit [Finite G] in
theorem isSolvable_quotient_subgroupOf {A R L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hs : Group.IsSolvable (A ⊔ R : Subgroup G)) :
    haveI : (L.subgroupOf (A ⊔ R ⊔ L)).Normal := ⟨fun x hx h => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_sup_le hAL hRL h.2) _).mp hx⟩
    Group.IsSolvable ((A ⊔ R ⊔ L : Subgroup G) ⧸ L.subgroupOf (A ⊔ R ⊔ L)) := by
  set H := A ⊔ R ⊔ L
  have : (L.subgroupOf H).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_of_sup_le hAL hRL h.2) _).mp hx⟩
  have hARH : A ⊔ R ≤ H := le_sup_left
  let ι : (A ⊔ R : Subgroup G) →* H := Subgroup.inclusion hARH
  refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (L.subgroupOf H)).comp ι) ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : (x : G) ∈ ((A ⊔ R : Subgroup G) : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (A ⊔ R) L (sup_le hAL hRL)]
      exact x.2
    obtain ⟨y, hy, l, hl, hyl⟩ := hx
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    change (y : G)⁻¹ * x ∈ L
    rw [← hyl, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hl

theorem layer_quotient_eq_map {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : L ∈ thetaComponents 3 H) [hLn : L.Normal] (hs : Group.IsSolvable (H ⧸ L)) :
    layer (H ⧸ aschbacherSolvableCore 3 H) = L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))
    := by
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H)
  set L₂ := L.map f with hL₂
  have hL₂c : IsComponent L₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three hL
  have hL₂n : L₂.Normal := hLn.map f (QuotientGroup.mk'_surjective _)
  have hsolv : Group.IsSolvable ((H ⧸ aschbacherSolvableCore 3 H) ⧸ L₂) := by
    have hker : L ≤ ((QuotientGroup.mk' L₂).comp f).ker := by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_of_mem f hx
    refine Group.isSolvable_of_surjective (f := QuotientGroup.lift L _ hker) ?_
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective L₂ q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨(x : H ⧸ L), rfl⟩
  obtain ⟨-, -, -, -, hiff, -⟩ := perfect_residual_characterization
    (G := H ⧸ aschbacherSolvableCore 3 H)
  have hres : perfectResidual (H ⧸ aschbacherSolvableCore 3 H) ≤ L₂ := (hiff L₂).mp hsolv
  have hcomp : ∀ J : Subgroup (H ⧸ aschbacherSolvableCore 3 H), IsComponent J → J = L₂ := by
    intro J hJ
    have : Group.IsPerfect J := hJ.1.1
    have hJL : J ≤ L₂ :=
      ((perfect_residual_transport (MonoidHom.id _)).2.2 J hJ.1.1).trans hres
    rcases distinct_components_commute hJ hL₂c with h | h
    · exact h
    · exfalso
      have hJC : J ≤ Subgroup.centralizer (J : Set (H ⧸ aschbacherSolvableCore 3 H)) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hy) x (hJL hx)
        exact this.symm
      have hcomm : ∀ a b : J, a * b = b * a := fun a b => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hJC b.2) a a.2)
      have : Nontrivial J := isQuasisimple_nontrivial hJ.1
      exact Group.IsPerfect.not_isSolvable J (Group.isSolvable_of_comm hcomm)
  refine le_antisymm (sSup_le fun J hJ => (hcomp J hJ).le) (le_sSup hL₂c)

section Core

variable {H : Subgroup G}

omit [Finite G] in
theorem card_map_eq_of_inf_ker_eq_bot {X Y : Type*} [Group X] [Group Y] (φ : X →* Y)
    {U : Subgroup X} (hU : U ⊓ φ.ker = ⊥) : Nat.card (U.map φ) = Nat.card U := by
  refine (Nat.card_congr (Equiv.ofBijective (fun x : U => (⟨φ x, ⟨x, x.2, rfl⟩⟩ : U.map φ))
    ⟨fun x y hxy => Subtype.ext ?_, fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩)).symm
  have hxy' : φ (x : X) = φ (y : X) := congrArg Subtype.val hxy
  have hm : (x : X) * (y : X)⁻¹ ∈ U ⊓ φ.ker :=
    ⟨U.mul_mem x.2 (U.inv_mem y.2), show φ ((x : X) * (y : X)⁻¹) = 1 by
      rw [map_mul, map_inv, hxy', mul_inv_cancel]⟩
  rw [hU, Subgroup.mem_bot, mul_inv_eq_one] at hm
  exact hm

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian p A) :
    CFSG.Assembly.IsElemAbelian p (A.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hA H

theorem isE27_map_subgroupOf {A : Subgroup G} (hA : Late.IsE27 A) (hAH : A ≤ H) :
    Late.IsE27 ((A.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) := by
  have hAp : IsPGroup 3 (A.subgroupOf H) :=
    hA.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 H) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hinf : A.subgroupOf H ⊓ (QuotientGroup.mk' (aschbacherSolvableCore 3 H)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hAp hθ3
  refine ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
    (isElemAbelian_subgroupOf hA.1), ?_⟩
  rw [card_map_eq_of_inf_ker_eq_bot _ hinf,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hA.2]

theorem gamma_map_subgroupOf_le {A M : Subgroup G} (hA : Late.IsE27 A) (hAH : A ≤ H)
    (hM : gamma 2 A ≤ M) :
    gamma 2 ((A.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) ≤
      (M.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := by
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hf
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 H) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hAp : IsPGroup 3 (A.subgroupOf H) :=
    hA.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  rw [gamma_le_iff]
  intro B₂ hB₂ hB₂r
  set B' : Subgroup H := A.subgroupOf H ⊓ B₂.comap f with hB'
  have hB'map : B'.map f = B₂ := by
    refine le_antisymm (fun _ ⟨b, hb, hbe⟩ => hbe ▸ hb.2) fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := hB₂ hx
    exact ⟨a, ⟨ha, hx⟩, rfl⟩
  have hB'p : IsPGroup 3 B' := hAp.to_le inf_le_left
  have hN := map_normalizer_eq_of_not_dvd Nat.prime_three (aschbacherSolvableCore 3 H) hθ3 hB'p
  rw [← hB'map, ← hN]
  apply Subgroup.map_mono
  set B : Subgroup G := B'.map H.subtype with hBdef
  have hBA : B ≤ A := by
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hb.1
  have hBr : 2 ≤ CFSG.Open.pRank 3 B := by
    have hker : ¬ 3 ∣ Nat.card f.ker := by rwa [hf, QuotientGroup.ker_mk']
    calc 2 ≤ CFSG.Open.pRank 3 B₂ := hB₂r
      _ = CFSG.Open.pRank 3 (B'.map f) := by rw [hB'map]
      _ ≤ CFSG.Open.pRank 3 B' := pRank_map_le_of_not_dvd Nat.prime_three f hker B'
      _ ≤ CFSG.Open.pRank 3 B :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3 Nat.prime_three
          H.subtype H.subtype_injective B'
  have hNB : Subgroup.normalizer (B : Set G) ≤ M :=
    (normalizer_le_gamma hBA hBr).trans hM
  intro x hx
  refine Subgroup.mem_subgroupOf.mpr (hNB ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨_, (Subgroup.mem_normalizer_iff.mp hx b).mp hb, rfl⟩
  · rintro ⟨b, hb, hbe⟩
    have hyH : y ∈ H := by
      have : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x ∈ H := by
        rw [← hbe]
        exact H.mul_mem (H.mul_mem (H.inv_mem x.2) b.2) x.2
      simpa [mul_assoc] using this
    refine ⟨⟨y, hyH⟩, (Subgroup.mem_normalizer_iff.mp hx ⟨y, hyH⟩).mpr ?_, rfl⟩
    have : x * ⟨y, hyH⟩ * x⁻¹ = b := Subtype.ext (by simpa using hbe.symm)
    rwa [this]

theorem pRank_map_subgroupOf_eq {A M : Subgroup G} (hA : Late.IsE27 A) (hAH : A ≤ H)
    (hAM : A ≤ M) (hM3 : CFSG.Open.pRank 3 M = 3) :
    CFSG.Open.pRank 3 ((M.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)))
      = 3 := by
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hf
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    rw [hf, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  apply le_antisymm
  · calc CFSG.Open.pRank 3 ((M.subgroupOf H).map f) ≤ CFSG.Open.pRank 3 (M.subgroupOf H) :=
          pRank_map_le_of_not_dvd Nat.prime_three f hker _
      _ ≤ CFSG.Open.pRank 3 ((M.subgroupOf H).map H.subtype) :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3 Nat.prime_three
            H.subtype H.subtype_injective _
      _ ≤ CFSG.Open.pRank 3 M :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three
            (fun _ ⟨x, hx, hxe⟩ => hxe ▸ Subgroup.mem_subgroupOf.mp hx)
      _ = 3 := hM3
  · have hA2 := isE27_map_subgroupOf hA hAH
    calc 3 = CFSG.Open.pRank 3 ((A.subgroupOf H).map f) := hA2.pRank_eq.symm
      _ ≤ CFSG.Open.pRank 3 ((M.subgroupOf H).map f) :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three
            (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
              (hAM (Subgroup.mem_subgroupOf.mp hx)))

omit [Finite G] in
theorem map_subgroupOf_mem_invariantPiSubgroups {A R : Subgroup G} (hR3 : ¬ 3 ∣ Nat.card R)
    (hRH : R ≤ H) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    (R.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ∈
      invariantPiSubgroups ⊤ ((A.subgroupOf H).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)))
        (piCompl 3) := by
  set f := QuotientGroup.mk' (aschbacherSolvableCore 3 H)
  rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
  refine ⟨le_top, fun h => hR3 ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
    exact h.trans (Subgroup.card_map_dvd _ f)
  · refine (Subgroup.map_mono fun a ha => ?_).trans (Subgroup.le_normalizer_map f)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := Subgroup.mem_normalizer_iff.mp (hAR (Subgroup.mem_subgroupOf.mp ha)) y
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem mem_of_pow_mem_of_coprime {X : Type*} [Group X] {L : Subgroup X} {x : X} {n : ℕ}
    (hn : n.Coprime (orderOf x)) (hxn : x ^ n ∈ L) : x ∈ L := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hn
  rw [← hm]
  exact L.pow_mem hxn m

omit [Finite G] in
theorem mem_of_mem_sup_of_not_dvd {A L : Subgroup G} (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ A ⊔ L)
    (hx3 : ¬ 3 ∣ orderOf x) : x ∈ L := by
  set W := A ⊔ L with hW
  have hWL : W ≤ Subgroup.normalizer (L : Set G) := sup_le hAL Subgroup.le_normalizer
  have : (L.subgroupOf W).Normal := ⟨fun y hy w => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hWL w.2) _).mp hy⟩
  have hmul : ((A ⊔ L : Subgroup G) : Set G) = (A : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A L hAL
  have hsurj : Function.Surjective ((QuotientGroup.mk' (L.subgroupOf W)).comp
      (Subgroup.inclusion (le_sup_left : A ≤ W))) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : G) ∈ (A : Set G) * (L : Set G) := hmul ▸ w.2
      obtain ⟨a, ha, l, hl, hal⟩ := hw
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      change a⁻¹ * (w : G) ∈ L
      rw [← hal, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hl
  have hp : IsPGroup 3 (W ⧸ L.subgroupOf W) := hA.of_surjective _ hsurj
  obtain ⟨k, hk⟩ := hp (QuotientGroup.mk' (L.subgroupOf W) ⟨x, hx⟩)
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
  have hxL : x ^ 3 ^ k ∈ L := by simpa [Subgroup.mem_subgroupOf] using hk
  have hcop : (3 ^ k).Coprime (orderOf x) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx3)
  exact mem_of_pow_mem_of_coprime hcop hxL

theorem IsZ3L34OrHeisSL34.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsZ3L34OrHeisSL34 X) : IsZ3L34OrHeisSL34 Y := by
  rcases h with hf | ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.symm.trans f⟩
  · refine Or.inr ⟨U.map e.toMonoidHom, V.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_sup, hUV, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hcomm u hu v hv]
    · obtain ⟨hx, hc, hexp⟩ := hU
      set e' := U.equivMapOfInjective e.toMonoidHom e.injective
      exact ⟨PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv e' hx,
        by rw [← Nat.card_congr e'.toEquiv, hc], by rw [← Monoid.exponent_eq_of_mulEquiv e', hexp]⟩
    · exact ⟨(V.equivMapOfInjective _ e.injective).symm.trans eV⟩
    · rw [← Subgroup.map_inf_eq U V e.toMonoidHom e.injective,
        Subgroup.card_map_of_injective e.injective, hcard]

theorem commutator_mem_of_mem_aschbacherSolvableCore {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLH : L ≤ H) (hHL : H ≤ Subgroup.normalizer (L : Set G))
    {x : H} (hx : x ∈ aschbacherSolvableCore 3 H) {l : G} (hl : l ∈ L) :
    (x : G) * l * (x : G)⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have hL' := mem_thetaComponents_subgroupOf_of_le_normalizer hL hLH hHL
  set L' := L.subgroupOf H with hL'def
  have hLn : L'.Normal := ⟨fun y hy h => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) _).mp hy⟩
  set c : H := x * ⟨l, hLH hl⟩ * x⁻¹ * (⟨l, hLH hl⟩ : H)⁻¹ with hc
  have hcθ : c ∈ aschbacherSolvableCore 3 H := by
    have h1 : (⟨l, hLH hl⟩ : H) * x⁻¹ * (⟨l, hLH hl⟩ : H)⁻¹ ∈ aschbacherSolvableCore 3 H :=
      (inferInstance : (aschbacherSolvableCore 3 H).Normal).conj_mem _
        (Subgroup.inv_mem _ hx) _
    have : c = x * ((⟨l, hLH hl⟩ : H) * x⁻¹ * (⟨l, hLH hl⟩ : H)⁻¹) := by rw [hc]; group
    rw [this]
    exact Subgroup.mul_mem _ hx h1
  have hcL : c ∈ L' := by
    refine L'.mul_mem (hLn.conj_mem _ (Subgroup.mem_subgroupOf.mpr hl) x) (L'.inv_mem ?_)
    exact Subgroup.mem_subgroupOf.mpr hl
  have hint := solvable_prime_complement_core_subnormal_intersection Nat.prime_three
    hLn.isSubnormal (G := H)
  have hcθL : c ∈ inSubgroup (aschbacherSolvableCore 3) L' := by
    rw [hint]
    exact ⟨hcL, hcθ⟩
  obtain ⟨t, ht, hte⟩ := hcθL
  set e := Subgroup.subgroupOfEquivOfLe hLH
  have hmap := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  have het : e t ∈ aschbacherSolvableCore 3 L := hmap ▸ Subgroup.mem_map_of_mem _ ht
  refine ⟨e t, het, ?_⟩
  have hte' : ((t : L') : H) = c := hte
  change (((t : L') : H) : G) = _
  rw [hte', hc]
  simp

end Core

end CFSG.RankThree.PartTwo.Sec4
