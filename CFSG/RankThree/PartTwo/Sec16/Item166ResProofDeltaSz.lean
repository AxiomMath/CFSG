module

public import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofGen
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSz
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace ProofDeltaSz166

section Cores

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem map_pCore_le_pCore_of_isSubnormal {p : ℕ} {Z : Subgroup H} (hZ : Z.IsSubnormal) :
    (CFSG.pCore p Z).map Z.subtype ≤ CFSG.pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        obtain ⟨x, hx, hxl⟩ := hl
        have hyN : (y : H) ∈ Subgroup.normalizer (X : Set H) := hYN y.2
        let φ := Subgroup.normalizerMonoidHom X ⟨(y : H), hyN⟩
        have hfix : (CFSG.pCore p X).map φ.toMonoidHom = CFSG.pCore p X :=
          (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
        refine ⟨φ x, ?_, ?_⟩
        · rw [← hfix]
          exact Subgroup.mem_map_of_mem _ hx
        · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hxl]
          rfl
      · exact ((CFSG.pCore_isPGroup).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hZ with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => ?_⟩, (CFSG.pCore_isPGroup).map _⟩
    obtain ⟨x, hx, rfl⟩ := hl
    let φ := Subgroup.normalizerMonoidHom (⊤ : Subgroup H) ⟨g, by
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top g⟩
    have hfix : (CFSG.pCore p (⊤ : Subgroup H)).map φ.toMonoidHom = CFSG.pCore p _ :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
    refine ⟨φ x, ?_, ?_⟩
    · rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hx
    · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem map_pPrimeCore_le_pPrimeCore_of_isSubnormal {p : ℕ} [Fact p.Prime] {Z : Subgroup H}
    (hZ : Z.IsSubnormal) : (CFSG.pPrimeCore p Z).map Z.subtype ≤ CFSG.pPrimeCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pPrimeCore p X).map X.subtype ≤ (CFSG.pPrimeCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pPrimeCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pPrimeCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pPrimeCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        obtain ⟨x, hx, hxl⟩ := hl
        have hyN : (y : H) ∈ Subgroup.normalizer (X : Set H) := hYN y.2
        let φ := Subgroup.normalizerMonoidHom X ⟨(y : H), hyN⟩
        have hfix : (CFSG.pPrimeCore p X).map φ.toMonoidHom = CFSG.pPrimeCore p X :=
          (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
        refine ⟨φ x, ?_, ?_⟩
        · rw [← hfix]
          exact Subgroup.mem_map_of_mem _ hx
        · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hxl]
          rfl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc (CFSG.pPrimeCore p X).map X.subtype
        = (((CFSG.pPrimeCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pPrimeCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hZ with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => ?_⟩, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hl
      let φ := Subgroup.normalizerMonoidHom (⊤ : Subgroup H) ⟨g, by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top g⟩
      have hfix : (CFSG.pPrimeCore p (⊤ : Subgroup H)).map φ.toMonoidHom =
          CFSG.pPrimeCore p _ :=
        (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
      refine ⟨φ x, ?_, ?_⟩
      · rw [← hfix]
        exact Subgroup.mem_map_of_mem _ hx
      · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]
    · rw [Subgroup.card_map_of_injective (⊤ : Subgroup H).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem le_pPrimeCore_of_isSubnormal {p : ℕ} [Fact p.Prime] {Z : Subgroup H}
    (hZ : Z.IsSubnormal) (hcop : Nat.Coprime p (Nat.card Z)) : Z ≤ CFSG.pPrimeCore p H := by
  have htop : CFSG.pPrimeCore p Z = ⊤ :=
    le_antisymm le_top (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have h := map_pPrimeCore_le_pPrimeCore_of_isSubnormal (p := p) hZ
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

end Cores

section Components

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem mem_aschbacherSolvableCore_iff {K : Subgroup H} (hKs : K.IsSubnormal)
    (hθ : aschbacherSolvableCore 3 ↥K = CFSG.pCore 2 ↥K) (l : ↥K) :
    l ∈ aschbacherSolvableCore 3 ↥K ↔ QuotientGroup.mk' (CFSG.pCore 2 H) (l : H) = 1 := by
  rw [hθ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hl
    exact map_pCore_le_pCore_of_isSubnormal hKs ⟨l, hl, rfl⟩
  · intro hl
    have h2 : (CFSG.pCore 2 H).subgroupOf K ≤ CFSG.pCore 2 ↥K :=
      le_sSup ⟨Subgroup.normal_subgroupOf,
        CFSG.pCore_isPGroup.comap_of_injective K.subtype K.subtype_injective⟩
    exact h2 (Subgroup.mem_subgroupOf.mpr hl)

omit [Finite H] in
theorem isComponent_map_mk_pCore {K : Subgroup H} (hK : K ∈ thetaComponents 3 H)
    (hθ : aschbacherSolvableCore 3 ↥K = CFSG.pCore 2 ↥K) :
    IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 H))) ∧
      Nonempty ((↥K ⧸ aschbacherSolvableCore 3 ↥K) ≃*
        ↥(K.map (QuotientGroup.mk' (CFSG.pCore 2 H)))) := by
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map (QuotientGroup.mk' (CFSG.pCore 2 H)) K
    (aschbacherSolvableCore 3 ↥K) (mem_aschbacherSolvableCore_iff hK.2.1 hθ)
  exact ⟨⟨LocalCores.isQuasisimple_of_mulEquiv η hK.2.2,
    hK.2.1.map (QuotientGroup.mk'_surjective _)⟩, ⟨η⟩⟩

theorem eq_of_map_mk_pCore_eq {K₁ K₂ : Subgroup H} (h₁ : K₁ ∈ thetaComponents 3 H)
    (h₂ : K₂ ∈ thetaComponents 3 H)
    (h : K₁.map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      K₂.map (QuotientGroup.mk' (CFSG.pCore 2 H))) : K₁ = K₂ := by
  set N := CFSG.pCore 2 H with hNdef
  have hNΘ : N ≤ aschbacherSolvableCore 3 H :=
    (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.2.2.2.2 2
      Nat.prime_two (by norm_num)
  have hsup : K₁ ⊔ N = K₂ ⊔ N := by
    have := congrArg (Subgroup.comap (QuotientGroup.mk' N)) h
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  have hN0 : N.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hNΘ)
  have e : ∀ K : Subgroup H, K.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) =
      (K ⊔ N).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := fun K => by
    rw [Subgroup.map_sup, hN0, sup_bot_eq]
  exact (theta_component_quotient_correspondence Nat.prime_three).1.injOn h₁ h₂
    (show K₁.map _ = K₂.map _ by rw [e K₁, e K₂, hsup])

@[expose] noncomputable def quotAut (α : MulAut H) : MulAut (H ⧸ CFSG.pCore 2 H) :=
  QuotientGroup.congr (CFSG.pCore 2 H) (CFSG.pCore 2 H) α
    ((Subgroup.characteristic_iff_map_eq.mp inferInstance) α)

omit [Finite H] in
theorem map_map_mk_pCore (α : MulAut H) (J : Subgroup H) :
    (J.map α.toMonoidHom).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      (J.map (QuotientGroup.mk' (CFSG.pCore 2 H))).map (quotAut α).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

end Components

section Rank

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem eq_one_of_forall_commute {D : Subgroup Γ} [IsSimpleGroup ↥D]
    (hq : CFSG.IsQuasisimple ↥D) {x : Γ} (hx : x ∈ D) (hc : ∀ y ∈ D, x * y = y * x) : x = 1 := by
  have hZ : Subgroup.center ↥D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥D) with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, u, v, huv⟩ := hq
      have h1 : ∀ q : ↥D ⧸ Subgroup.center ↥D, q = 1 := fun q => by
        obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
        rw [QuotientGroup.eq_one_iff, h]
        exact Subgroup.mem_top d
      exact huv (by rw [h1 u, h1 v])
  have hmem : (⟨x, hx⟩ : ↥D) ∈ Subgroup.center ↥D := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem three_le_localRank_of_components {C : Subgroup Γ}
    (hC : IsComponent C) {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * a + 1)) (e : ↥C ≃* CFSG.Blueprint.suzukiGroup a F)
    (β : MulAut Γ) (h12 : C.map β.toMonoidHom ≠ C)
    (h13 : (C.map β.toMonoidHom).map β.toMonoidHom ≠ C)
    (h23 : (C.map β.toMonoidHom).map β.toMonoidHom ≠ C.map β.toMonoidHom) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ 3 ≤ CFSG.Assembly.RankThreeEven.localRank p Γ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₂ := C.map β.toMonoidHom with hC₂def
  set C₃ := C₂.map β.toMonoidHom with hC₃def
  have hcomp : ∀ D : Subgroup Γ, IsComponent D → IsComponent (D.map β.toMonoidHom) :=
    fun D hD => ⟨LocalCores.isQuasisimple_of_mulEquiv (D.equivMapOfInjective _ β.injective) hD.1,
      hD.2.map β.surjective⟩
  have hC₂ : IsComponent C₂ := hcomp C hC
  have hC₃ : IsComponent C₃ := hcomp C₂ hC₂
  have hcomm : ∀ {D₁ D₂ : Subgroup Γ}, IsComponent D₁ → IsComponent D₂ → D₁ ≠ D₂ →
      ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x := by
    intro D₁ D₂ h₁ h₂ hne x hx y hy
    rcases LocalCores.distinct_components_commute h₁ h₂ with h | h
    · exact absurd h hne
    · exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm
  have hsC : IsSimpleGroup ↥C := isSimpleGroup_of_suzukiModel
    (⟨rfl, a, ha, F, inferInstance, inferInstance, rfl, hF, ⟨e⟩⟩ :
      CFSG.Blueprint.SuzukiModel ↥C 2 (2 * a + 1))
  have hsimple : ∀ D : Subgroup Γ, IsSimpleGroup ↥D → IsSimpleGroup ↥(D.map β.toMonoidHom) :=
    fun D hD => by
      have := hD
      exact (D.equivMapOfInjective β.toMonoidHom β.injective).symm.isSimpleGroup
  have hsC₂ : IsSimpleGroup ↥C₂ := hsimple C hsC
  have hsC₃ : IsSimpleGroup ↥C₃ := hsimple C₂ hsC₂
  obtain ⟨p, hp, hp3, t, htp, htN, htfix⟩ := Steps166.exists_frobenius_pair (K := F) ha hF
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hp3, ?_⟩
  set Z0 := CFSG.LieType.Ree.suzukiZ0 a F with hZ0def
  have hZ0 : Z0 ≠ ⊥ := Steps166.suzukiZ0_ne_bot hF
  have ht1 : t ≠ 1 := by
    intro h1
    apply hZ0
    rw [eq_bot_iff]
    intro x hx
    rw [htfix x hx (by rw [h1, one_mul, inv_one, mul_one]), Subgroup.mem_bot]
  have hot : orderOf t = p := orderOf_eq_prime htp ht1
  set y₁ : Γ := ((e.symm t : ↥C) : Γ) with hy₁
  have hy₁C : y₁ ∈ C := (e.symm t).2
  have hoy₁ : orderOf y₁ = p := by rw [hy₁, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hot]
  set Zh : Subgroup Γ := (Z0.map e.symm.toMonoidHom).map C.subtype with hZh
  have hZhC : Zh ≤ C := Subgroup.map_subtype_le _
  have hZh2 : IsPGroup 2 Zh := by
    rintro ⟨z, hz⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨w, ⟨z₀, hz₀, rfl⟩, rfl⟩ := hz
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, ← map_pow, Steps166.suzukiZ0_sq hF hz₀, map_one, map_one]
  have hZh1 : Zh ≠ ⊥ := by
    rw [hZh, Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
    exact hZ0
  have hy₁N : y₁ ∈ Subgroup.normalizer (Zh : Set Γ) := by
    apply Sec3.mem_normalizer_of_forall_conj_mem
    rintro _ ⟨w, ⟨z₀, hz₀, rfl⟩, rfl⟩
    refine ⟨e.symm.toMonoidHom (t * z₀ * t⁻¹),
      ⟨_, (Subgroup.mem_normalizer_iff.mp htN z₀).mp hz₀, rfl⟩, ?_⟩
    simp [hy₁, map_mul, map_inv]
  set y₂ : Γ := β y₁ with hy₂
  set y₃ : Γ := β y₂ with hy₃
  have hy₂C : y₂ ∈ C₂ := ⟨y₁, hy₁C, rfl⟩
  have hy₃C : y₃ ∈ C₃ := ⟨y₂, hy₂C, rfl⟩
  have hoy₂ : orderOf y₂ = p := by rw [hy₂, MulEquiv.orderOf_eq, hoy₁]
  have hoy₃ : orderOf y₃ = p := by rw [hy₃, MulEquiv.orderOf_eq, hoy₂]
  have hcentN : ∀ {D : Subgroup Γ}, IsComponent D → D ≠ C → ∀ y ∈ D,
      y ∈ Subgroup.normalizer (Zh : Set Γ) := by
    intro D hD hne y hy
    apply Sec3.mem_normalizer_of_forall_conj_mem
    intro z hz
    rw [hcomm hD hC hne y hy z (hZhC hz), mul_inv_cancel_right]
    exact hz
  have hy₂N := hcentN hC₂ h12 y₂ hy₂C
  have hy₃N := hcentN hC₃ h13 y₃ hy₃C
  set P₁ := Subgroup.zpowers y₁ with hP₁
  set P₂ := Subgroup.zpowers y₂ with hP₂
  set P₃ := Subgroup.zpowers y₃ with hP₃
  have hP₁C : P₁ ≤ C := Subgroup.zpowers_le.mpr hy₁C
  have hP₂C : P₂ ≤ C₂ := Subgroup.zpowers_le.mpr hy₂C
  have hP₃C : P₃ ≤ C₃ := Subgroup.zpowers_le.mpr hy₃C
  have c23 : ∀ (m : ↥P₂) (n : ↥P₃), Commute (P₂.subtype m) (P₃.subtype n) := fun m n =>
    hcomm hC₂ hC₃ (Ne.symm h23) _ (hP₂C m.2) _ (hP₃C n.2)
  set f₂₃ := P₂.subtype.noncommCoprod P₃.subtype c23 with hf₂₃
  have c1 : ∀ (m : ↥P₁) (n : ↥P₂ × ↥P₃), Commute (P₁.subtype m) (f₂₃ n) := fun m n => by
    rw [hf₂₃, MonoidHom.noncommCoprod_apply]
    exact Commute.mul_right (hcomm hC hC₂ (Ne.symm h12) _ (hP₁C m.2) _ (hP₂C n.1.2))
      (hcomm hC hC₃ (Ne.symm h13) _ (hP₁C m.2) _ (hP₃C n.2.2))
  set f := P₁.subtype.noncommCoprod f₂₃ c1 with hf
  have hfapp : ∀ (u : ↥P₁) (v : ↥P₂) (w : ↥P₃), f (u, v, w) = (u : Γ) * ((v : Γ) * w) := by
    intro u v w
    rw [hf, MonoidHom.noncommCoprod_apply, hf₂₃, MonoidHom.noncommCoprod_apply]
    rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v, w⟩ huvw
    rw [hfapp] at huvw
    have hu : (u : Γ) = 1 := by
      have := hsC
      refine eq_one_of_forall_commute hC.1 (hP₁C u.2) fun y hy => ?_
      rw [eq_inv_of_mul_eq_one_left huvw]
      exact (Commute.mul_right (hcomm hC hC₂ (Ne.symm h12) y hy _ (hP₂C v.2))
        (hcomm hC hC₃ (Ne.symm h13) y hy _ (hP₃C w.2))).inv_right.symm
    have hvw : (v : Γ) * w = 1 := by rwa [hu, one_mul] at huvw
    have hv : (v : Γ) = 1 := by
      have := hsC₂
      refine eq_one_of_forall_commute hC₂.1 (hP₂C v.2) fun y hy => ?_
      rw [eq_inv_of_mul_eq_one_left hvw]
      exact (Commute.inv_right (hcomm hC₂ hC₃ (Ne.symm h23) y hy _ (hP₃C w.2))).symm
    have hw : (w : Γ) = 1 := by rwa [hv, one_mul] at hvw
    exact Prod.ext (Subtype.ext hu) (Prod.ext (Subtype.ext hv) (Subtype.ext hw))
  have hz : ∀ (g : Γ) (x y : ↥(Subgroup.zpowers g)), x * y = y * x := by
    intro g x y
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj, zpow_mul_comm]
  have hcommA : ∀ x y : ↥P₁ × (↥P₂ × ↥P₃), x * y = y * x := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨z₁, z₂, z₃⟩
    exact Prod.ext (hz _ x₁ z₁) (Prod.ext (hz _ x₂ z₂) (hz _ x₃ z₃))
  have hpz : ∀ g : Γ, orderOf g = p → ∀ x : ↥(Subgroup.zpowers g), x ^ p = 1 := by
    intro g hg x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← hg, pow_orderOf_eq_one, one_zpow, Subgroup.coe_one]
  have hpowA : ∀ x : ↥P₁ × (↥P₂ × ↥P₃), x ^ p = 1 := by
    rintro ⟨x₁, x₂, x₃⟩
    exact Prod.ext (hpz _ hoy₁ x₁) (Prod.ext (hpz _ hoy₂ x₂) (hpz _ hoy₃ x₃))
  have hcardA : Nat.card (↥P₁ × (↥P₂ × ↥P₃)) = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, Nat.card_zpowers, hoy₁,
      hoy₂, hoy₃]
    ring
  have hrange : f.range ≤ Subgroup.normalizer (Zh : Set Γ) := by
    rintro _ ⟨⟨u, v, w⟩, rfl⟩
    rw [hfapp]
    exact mul_mem (Subgroup.zpowers_le.mpr hy₁N u.2)
      (mul_mem (Subgroup.zpowers_le.mpr hy₂N v.2) (Subgroup.zpowers_le.mpr hy₃N w.2))
  exact (CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcommA hpowA hcardA f hfinj
    hrange).trans (CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt ⟨Zh, hZh1, hZh2, rfl⟩)

end Rank

section Normalizer

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_suzukiModel
    (hloc : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3)
    {X K : Subgroup G} (hK : K ∈ thetaComponentsIn X) {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n)
    (hθ : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K) {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G)) (ha3 : a ^ 3 = 1) :
    a ∈ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKX, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set K' := K.subgroupOf X with hK'def
  set e₀ : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX with he₀
  have hθ' : aschbacherSolvableCore 3 ↥K' = CFSG.pCore 2 ↥K' := by
    apply Subgroup.map_injective (f := e₀.toMonoidHom) e₀.injective
    rw [aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀, CFSG.pCore_map_iso 2 e₀, hθ]
  obtain ⟨-, a', ha', F, _, _, hn, hF, ⟨eS⟩⟩ := hSz
  rw [hn] at hF
  have e₁ : (↥K' ⧸ aschbacherSolvableCore 3 ↥K') ≃* (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    QuotientGroup.congr _ _ e₀ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀)
  obtain ⟨hC, ⟨η⟩⟩ := isComponent_map_mk_pCore hK' hθ'
  have eC : ↥(K'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ≃*
      CFSG.Blueprint.suzukiGroup a' F := η.symm.trans (e₁.trans eS)
  set α : MulAut ↥X := X.normalizerMonoidHom ⟨a, haX⟩ with hα
  have hα3 : ∀ x : ↥X, α (α (α x)) = x := by
    intro x
    have h1 : α ^ 3 = 1 := by
      rw [hα, ← map_pow]
      have : (⟨a, haX⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using ha3)
      rw [this, map_one]
    have h2 := congrArg (fun σ : MulAut ↥X => σ x) h1
    simpa [pow_succ, MulAut.mul_apply] using h2
  by_contra hna
  have hne : K'.map α.toMonoidHom ≠ K' := by
    intro heq
    apply hna
    apply Sec3.mem_normalizer_of_forall_conj_mem
    intro k hk
    have hkK' : (⟨k, hKX hk⟩ : ↥X) ∈ K' := Subgroup.mem_subgroupOf.mpr hk
    have h1 : α ⟨k, hKX hk⟩ ∈ K'.map α.toMonoidHom := Subgroup.mem_map_of_mem α.toMonoidHom hkK'
    rw [heq] at h1
    have h2 : ((α ⟨k, hKX hk⟩ : ↥X) : G) = a * k * a⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨a, haX⟩ ⟨k, hKX hk⟩
    rw [← h2]
    exact Subgroup.mem_subgroupOf.mp h1
  set K₂ := K'.map α.toMonoidHom with hK₂def
  set K₃ := K₂.map α.toMonoidHom with hK₃def
  have hmap3 : K₃.map α.toMonoidHom = K' := by
    rw [hK₃def, hK₂def, Subgroup.map_map, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id K']
    congr 1
    exact MonoidHom.ext fun x => hα3 x
  have hne32 : K₃ ≠ K₂ := fun h => hne (Subgroup.map_injective (f := α.toMonoidHom) α.injective h)
  have hne31 : K₃ ≠ K' := fun h => by
    apply hne
    have h1 : K₃.map α.toMonoidHom = K₂ := by rw [h]
    rw [hmap3] at h1
    exact h1.symm
  have hmem₂ : K₂ ∈ thetaComponents 3 ↥X := map_mulEquiv_mem_thetaComponents Nat.prime_three α hK'
  have hmem₃ : K₃ ∈ thetaComponents 3 ↥X :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three α hmem₂
  set β := quotAut α with hβ
  have hC₂ : (K'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map β.toMonoidHom =
      K₂.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := (map_map_mk_pCore α K').symm
  have hC₃ : ((K'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map β.toMonoidHom).map
      β.toMonoidHom = K₃.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
    rw [hC₂, ← map_map_mk_pCore α K₂]
  obtain ⟨p, hp, hp3, hle⟩ := three_le_localRank_of_components hC ha' hF eC β
    (by rw [hC₂]; exact fun h => hne (eq_of_map_mk_pCore_eq hmem₂ hK' h))
    (by rw [hC₃]; exact fun h => hne31 (eq_of_map_mk_pCore_eq hmem₃ hK' h))
    (by rw [hC₃, hC₂]; exact fun h => hne32 (eq_of_map_mk_pCore_eq hmem₃ hmem₂ h))
  have hN : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 ↥X) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le hp (by omega) (CFSG.pCore 2 ↥X) hN
  have h2 := localRank_subgroup_le hp X
  have h3 := hloc p hp hp3
  omega

end Normalizer

section Q

theorem le_sup_of_isPerfect {H : Type*} [Group H] {K C J : Subgroup H} (D : Subgroup H)
    (hK : Group.IsPerfect ↥K) (hKDC : K ≤ D ⊔ C) (hDK : D ≤ K) (hCK : C ≤ K) (hJK : J ≤ K)
    (hKJ : K ≤ Subgroup.normalizer (J : Set H)) (hDJ : ⁅D, K⁆ ≤ J) : K ≤ C ⊔ J := by
  set J' := J.subgroupOf K with hJ'
  have : J'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr hKJ
  set φ := QuotientGroup.mk' J' with hφ
  set Cb := (C.subgroupOf K).map φ with hCb
  have hDcen : (D.subgroupOf K).map φ ≤ Subgroup.center (↥K ⧸ J') := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective J' q
    have h1 : ⁅(d : H), (k : H)⁆ ∈ J :=
      hDJ (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hd) k.2)
    have h2 : ⁅d, k⁆ ∈ J' := Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)
    have h3 : ⁅φ d, φ k⁆ = 1 := by
      rw [← map_commutatorElement, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    exact (commutatorElement_eq_one_iff_commute.mp h3).symm
  have htop : ∀ q : ↥K ⧸ J', q ∈ Cb ⊔ Subgroup.center (↥K ⧸ J') := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective J' q
    have hk' : k ∈ D.subgroupOf K ⊔ C.subgroupOf K := by
      rw [← Subgroup.subgroupOf_sup hDK hCK]
      exact Subgroup.mem_subgroupOf.mpr (hKDC k.2)
    have := Subgroup.mem_map_of_mem φ hk'
    rw [Subgroup.map_sup] at this
    exact (sup_le (hDcen.trans le_sup_right) le_sup_left) this
  have key : ∀ u v w : ↥K ⧸ J', w ∈ Subgroup.center (↥K ⧸ J') →
      ⁅u * w, v⁆ = ⁅u, v⁆ ∧ ⁅u, v * w⁆ = ⁅u, v⁆ := by
    intro u v w hw
    have hwv : w * v = v * w := (Subgroup.mem_center_iff.mp hw v).symm
    have hwu : w * u⁻¹ = u⁻¹ * w := (Subgroup.mem_center_iff.mp hw u⁻¹).symm
    constructor
    · calc ⁅u * w, v⁆ = u * (w * v) * w⁻¹ * u⁻¹ * v⁻¹ := by rw [commutatorElement_def]; group
        _ = u * (v * w) * w⁻¹ * u⁻¹ * v⁻¹ := by rw [hwv]
        _ = ⁅u, v⁆ := by rw [commutatorElement_def]; group
    · calc ⁅u, v * w⁆ = u * v * (w * u⁻¹) * w⁻¹ * v⁻¹ := by rw [commutatorElement_def]; group
        _ = u * v * (u⁻¹ * w) * w⁻¹ * v⁻¹ := by rw [hwu]
        _ = ⁅u, v⁆ := by rw [commutatorElement_def]; group
  have hcomm : commutator (↥K ⧸ J') ≤ Cb := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (htop x)
    obtain ⟨c', hc', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (htop y)
    rw [(key _ _ z hz).1, (key _ _ z' hz').2, commutatorElement_def]
    exact Cb.mul_mem (Cb.mul_mem (Cb.mul_mem hc hc') (Cb.inv_mem hc)) (Cb.inv_mem hc')
  have := hK
  have hQ : Group.IsPerfect (↥K ⧸ J') :=
    Group.IsPerfect.ofSurjective (f := φ) (QuotientGroup.mk'_surjective J')
  intro k hk
  obtain ⟨c, hc, hcφ⟩ := hcomm (hQ.commutator_eq_top ▸ Subgroup.mem_top (φ ⟨k, hk⟩))
  have hJ : c⁻¹ * ⟨k, hk⟩ ∈ J' := by
    rw [← QuotientGroup.eq]
    simpa [hφ] using hcφ
  have hcH : (c : H) ∈ C := Subgroup.mem_subgroupOf.mp hc
  have hjH : ((c⁻¹ * ⟨k, hk⟩ : ↥K) : H) ∈ J := Subgroup.mem_subgroupOf.mp hJ
  have hk' : k = (c : H) * ((c⁻¹ * ⟨k, hk⟩ : ↥K) : H) := by simp
  rw [hk']
  exact Subgroup.mul_mem_sup hcH hjH

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem eq_delta_of_le_normalizer (hA : IsE27 A) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A)) {c : G}
    (hc : Subgroup.zpowers c ∈ omegaA A) {X : Subgroup G} (hX : X ∈ scriptY A)
    (hXΔ : X = delta A (lB A) X)
    (h147 : ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X))
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn X) (hK3 : ¬ 3 ∣ Nat.card K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) : K = delta A (lB A) K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKX, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hKO : K ≤ pPrimeCoreOf 3 X := by
    have hcop : Nat.Coprime 3 (Nat.card ↥(K.subgroupOf X)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3
    have h1 := le_pPrimeCore_of_isSubnormal (p := 3) hK'.2.1 hcop
    intro k hk
    exact ⟨⟨k, hKX hk⟩, h1 (Subgroup.mem_subgroupOf.mpr hk), rfl⟩
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.2
  have hOinv := Proof17Q0.pPrimeCoreOf_mem_invariantPiSubgroups hAX
  set I := delta A (lB A) (pPrimeCoreOf 3 X) with hI
  have hIQ : I ∈ scriptQ A (lB A) := delta_mem_scriptQ hA h146 hOinv
  have hXI : X ≤ Subgroup.normalizer (I : Set G) :=
    calc X = delta A (lB A) X := hXΔ
      _ ≤ _ := delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hOinv
          (le_normalizer_pPrimeCoreOf 3 X)
  have hD0 : deltaZero A (lB A) X = ⁅X, A⁆ := by
    have := (rank3II_14_5_lB hA hbot hAX).2.1
    rwa [← hXΔ] at this
  have hKA : ⁅K, A⁆ ≤ deltaZero A (lB A) X := hD0 ▸ Subgroup.commutator_mono hKX le_rfl
  have hKAK : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hAK
  have hDK : ⁅⁅K, A⁆, K⁆ ≤ K ⊓ I := by
    refine le_inf ?_ ((Subgroup.commutator_mono hKA hKO).trans h147)
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hKAK hx) hy) (K.inv_mem (hKAK hx))) (K.inv_mem hy)
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A K hA.isPGroup hK3 hAK
  have hle : K ≤ (K ⊓ Subgroup.centralizer (A : Set G)) ⊔ (K ⊓ I) :=
    le_sup_of_isPerfect ⁅K, A⁆ (isPerfect_of_mem_thetaComponentsIn hK) hfac.le hKAK inf_le_left
      inf_le_left (Late.le_normalizer_inf Subgroup.le_normalizer (hKX.trans hXI)) hDK
  have hK3' : IsPiSubgroup (piCompl 3) K := (isPiSubgroup_piCompl_iff Nat.prime_three K).mpr hK3
  have hAC : A ≤ Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1).trans Subgroup.le_normalizer
  have hCQ : K ⊓ Subgroup.centralizer (A : Set G) ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_of_le (Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 hc hK3' hAK)
      (inf_le_inf_left K ?_) (Late.le_normalizer_inf hAK hAC)
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (zpowers_mem_omegaA_iff.mp hc).1)
  have hJQ : K ⊓ I ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hIQ inf_le_right (Late.le_normalizer_inf hAK hIQ.1.2.2)
  exact le_antisymm (hle.trans (sup_le (le_delta hCQ inf_le_left) (le_delta hJQ inf_le_left)))
    (delta_le K)

end Q

end ProofDeltaSz166

theorem ProofDeltaSz166.deltaSz166_of {G : Type} [Group G]
    [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h142 : Concl142 A (lB A))
    (h147 : ∀ X ∈ scriptY A, X = delta A (lB A) X →
      ⁅deltaZero A (lB A) X, pPrimeCoreOf 3 X⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X)) :
    DeltaSz166 A := by
  intro X hX hXΔ K hK hSz hθ
  obtain ⟨n, hn⟩ := hSz
  have hA : IsE27 A := h.toSec14Std.isE27
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    ProofDeltaSz166.mem_normalizer_of_suzukiModel h.toTheoremFourHyp.localRank_lt hK hn hθ
      (hX.2 ha) (hA.1.2 a ha)
  exact ProofDeltaSz166.eq_delta_of_le_normalizer hA hbot h146 h142
    h.toSec13Data.zpowers_mem_omegaA hX hXΔ (h147 X hX hXΔ) hK
    (Steps166.not_three_dvd_card_of_suzukiModel hn) hAK

theorem step166DeltaSz_of_item1444 (h146 : Item146S14)
    (h1444 : Item1444S14) (hbot : Item145BotS17) (h142 : Concl142R) : Step166DeltaSz := by
  intro G _ _ A c L Y₀ h
  have hA : IsE27 A := h.toSec14Std.isE27
  have h146' := h146 G A c L h.toSec14Std
  refine ProofDeltaSz166.deltaSz166_of h h146' (hbot G A c L Y₀ h) (h142 G A c L h.toSec15R)
    fun X hX hXΔ => ?_
  have hOinv := Proof17Q0.pPrimeCoreOf_mem_invariantPiSubgroups hX.2
  have hXI : X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    calc X = delta A (lB A) X := hXΔ
      _ ≤ _ := delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146' hZ) hOinv
          (le_normalizer_pPrimeCoreOf 3 X)
  exact rank3II_14_7_reduction hA (h1444 G A c L h.toSec14Std) h146' hX.2
    ((pPrimeCoreOf_le 3 X).trans hXI)

theorem step166DeltaSzHJ_of (h : Step166DeltaSz) : Step166DeltaSzHJ :=
  fun G _ _ A c L Y₀ hs _ => h G A c L Y₀ hs

end CFSG.RankThree.PartTwo.Sec16
