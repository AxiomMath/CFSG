module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp

namespace OPlusEight

theorem ggFix_conj {R : Type} [Group R] (r : R) :
    ggFix (MulAut.conj r) = Subgroup.centralizer ({r} : Set R) := by
  ext x
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * r = r * x * r⁻¹ * r := by rw [h]
      _ = r * x := by group
  · intro h
    rw [← h]
    group

theorem isEndNode_iff_range {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (χ : A →* R) (hχinj : Function.Injective χ)
    (hχ : ∀ (a : A) (l : L'), ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹) (a : A) :
    GGIsEndNode A (a : MulAut L') ↔ TableBOrth.IsEndNode χ.range (χ a) := by
  have hc : ∀ (b : A) (l : L'), MulAut.conj (χ b) (ψ l) = ψ ((b : MulAut L') l) := by
    intro b l
    rw [MulAut.conj_apply, hχ]
  have hfix := ggFix_conj (χ a)
  have hmap := USixTwo.layer_map_eq hψ hker (hc a)
  have hone : (a : MulAut L') ≠ 1 ↔ χ a ≠ 1 := by
    constructor
    · intro h h1
      apply h
      have : a = 1 := hχinj (by rw [h1, map_one])
      rw [this]
      rfl
    · intro h h1
      apply h
      have : a = 1 := Subtype.ext h1
      rw [this, map_one]
  have hcentral : ∀ b : A, ((∀ j ∈ LargeEvenLayer (ggFix (a : MulAut L')), (b : MulAut L') j = j) ↔
      ∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({χ a} : Set R)), χ b * j = j * χ b) := by
    intro b
    rw [USixTwo.fix_layer_iff hψ hker (hc a) (hc b), hfix]
    refine forall₂_congr fun j _ => ?_
    rw [MulAut.conj_apply]
    constructor
    · intro h
      calc χ b * j = χ b * j * (χ b)⁻¹ * χ b := by group
        _ = j * χ b := by rw [h]
    · intro h
      rw [h]
      group
  have hzp : ∀ b : A, ((b : MulAut L') ∈ Subgroup.zpowers (a : MulAut L') ↔
      χ b ∈ Subgroup.zpowers (χ a)) := by
    intro b
    constructor
    · rintro ⟨k, hk⟩
      have hk' : (a : MulAut L') ^ k = (b : MulAut L') := hk
      have : a ^ k = b := Subtype.ext (by simpa using hk')
      exact ⟨k, by show χ a ^ k = χ b; rw [← map_zpow, this]⟩
    · rintro ⟨k, hk⟩
      have hk' : χ a ^ k = χ b := hk
      have : a ^ k = b := hχinj (by rw [map_zpow]; exact hk')
      refine ⟨k, ?_⟩
      show (a : MulAut L') ^ k = (b : MulAut L')
      simpa using congrArg Subtype.val this
  constructor
  · rintro ⟨haA, ha1, hcomp, hcent⟩
    refine ⟨⟨a, rfl⟩, hone.mp ha1, ?_, ?_⟩
    · have h := USixTwo.isComponentOf_layer_down hψ hker (hc a) hcomp
      rwa [hfix] at h
    · rintro _ ⟨b, rfl⟩
      exact (hcentral b).symm.trans ((hcent b b.2).trans (hzp b))
  · rintro ⟨-, ha1, hcomp, hcent⟩
    refine ⟨a.2, hone.mpr ha1, ?_, ?_⟩
    · have h : IsComponentOf (LargeEvenLayer (ggFix (MulAut.conj (χ a))))
          (ggFix (MulAut.conj (χ a))) := by
        rw [hfix]
        exact hcomp
      exact (USixTwo.layer_eq_commutator_comap hψ hker (hc a) h).2
    · intro b hb
      have h1 := hcentral ⟨b, hb⟩
      have h2 := hzp ⟨b, hb⟩
      have h3 := hcent (χ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
      exact (h1.trans h3).trans h2.symm

end OPlusEight

@[expose] def GGEndNodeRootEltAll (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    (∃ t, TableBOrth.IsEndNode A t) ∧
    ∀ t, TableBOrth.IsEndNode A t →
      ∃ U : Subgroup R, U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set R)) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)

theorem ggEndNodeRoot_of_eltAll {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥)
    (h : GGEndNodeRootEltAll p r R) : GGEndNodeRoot p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    have hφp : φ ^ p = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := hψ x
      rw [pow_apply_comp_eq hφ p l, hA.2 a a.2, MulAut.one_apply, MulAut.one_apply]
    obtain ⟨t, rfl⟩ := hI φ hφI hφp
    exact ⟨t, fun l => (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  set Ab := χ.range with hAb
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ Ab ≤ Subgroup.normalizer (U : Set R) := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    have := hAU a a.2 l hu
    rwa [hχ] at this
  obtain ⟨hexist, hall⟩ := h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) hUAb
  have hiff : ∀ a : A, GGIsEndNode A (a : MulAut L') ↔ TableBOrth.IsEndNode Ab (χ a) :=
    fun a => OPlusEight.isEndNode_iff_range hψ hker χ hχinj hχ a
  have hlift : ∀ a : A, GGIsEndNode A (a : MulAut L') →
      ∃ U : Subgroup L', U ≤ LargeEvenLayer (ggFix (a : MulAut L')) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U := by
    intro a ha
    obtain ⟨V, hVL, hV1, hV2, hAbV⟩ := hall (χ a) ((hiff a).mp ha)
    have hc : ∀ l, MulAut.conj (χ a) (ψ l) = ψ ((a : MulAut L') l) := fun l => by
      rw [MulAut.conj_apply, hχ]
    have hmap := USixTwo.layer_map_eq hψ hker hc
    rw [OPlusEight.ggFix_conj] at hmap
    have hVX : V ≤ (LargeEvenLayer (ggFix (a : MulAut L'))).map ψ := by
      rw [hmap]
      exact hVL
    have hAX : ∀ a' ∈ (A : Set (MulAut L')), ∀ x ∈ LargeEvenLayer (ggFix (a : MulAut L')),
        a' x ∈ LargeEvenLayer (ggFix (a : MulAut L')) := fun a' ha' x hx =>
      USixTwo.layer_invariant (TableB.IsElemAbelian.comm hA a.2 ha') x hx
    have hAV : ∀ a' ∈ (A : Set (MulAut L')), ∀ l, ψ l ∈ V → ψ (a' l) ∈ V := by
      intro a' ha' l hl
      rw [hχ ⟨a', ha'⟩]
      exact (Subgroup.mem_normalizer_iff.mp (hAbV ⟨⟨a', ha'⟩, rfl⟩) _).mp hl
    obtain ⟨P, hPX, hP1, hP2, hAP⟩ := exists_twoSubgroup_lift hker hV1 hV2 hVX hAX hAV
    exact ⟨P, hPX, hP1, hP2, fun a' ha' u hu => hAP a' ha' u hu⟩
  by_cases hns : ∃ a₁ : A, GGIsEndNode A (a₁ : MulAut L') ∧
      ¬ LargeEvenSmall (LargeEvenLayer (ggFix (a₁ : MulAut L')))
  · obtain ⟨a₁, hend, hn⟩ := hns
    obtain ⟨U, hUL, hU1, hU2, hUA⟩ := hlift a₁ hend
    exact ⟨(a₁ : MulAut L'), hend, fun _ _ => hn, U, hUL, hU1, hU2, hUA⟩
  · obtain ⟨t, ht⟩ := hexist
    obtain ⟨a₀, rfl⟩ := ht.1
    have hend := (hiff a₀).mpr ht
    obtain ⟨U, hUL, hU1, hU2, hUA⟩ := hlift a₀ hend
    refine ⟨(a₀ : MulAut L'), hend, ?_, U, hUL, hU1, hU2, hUA⟩
    rintro - ⟨a₁, hend₁, hn₁⟩
    exact absurd ⟨⟨a₁, hend₁.1⟩, hend₁, hn₁⟩ hns

theorem ggEndNodeIOne_of_eltAll {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥) (hC : GGCenterPrime p R)
    (h : GGEndNodeRootEltAll p r R) : GGEndNodeIOne p r R I :=
  ggEndNodeIOne_of_root_delta (ggEndNodeRoot_of_eltAll hI hZ h)
    (ggEndNodeIOneDelta_of_prime hI hC)

end CFSG.StandardType

end
