module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleAcross
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleEnd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleNegOne
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleFaithful

public section

namespace CFSG.StandardType

section Module

@[expose] def GGLinConnGen
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) : Prop :=
  ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ r ∈ S, GGLinRefl r) ∧
    (∀ r ∈ S, ∀ s ∈ S, Relation.EqvGen (fun a b => a ∈ S ∧ b ∈ S ∧ GGLinAdj a b) r s) ∧
    A = Subgroup.closure S

private lemma ggLinMove_neg_of_involution
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r : V ≃ₗ[ZMod p] V) (hr : r * r = 1) :
    ∀ x ∈ ggLinMove r, r x = -x := by
  rintro x ⟨v, rfl⟩
  have hr' : r.toLinearMap (r.toLinearMap v) = v := by
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hr
    simpa [LinearEquiv.mul_apply] using h
  change r.toLinearMap ((r.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) v) =
    -((r.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) v)
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hr']
  abel

theorem ggLin_bar_abstract
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) [Module.Finite (ZMod p) V] {I : Type*} [Nonempty I]
    (AX : I → Subgroup (V ≃ₗ[ZMod p] V)) (hX : ∀ X, GGLinConnGen (AX X))
    (AJ : Subgroup (V ≃ₗ[ZMod p] V)) (hJ : ∀ X, AJ ≤ AX X) (hJr : ∃ r ∈ AJ, GGLinRefl r)
    (hfix : ggLinFix ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) = ⊥)
    (hnotr : ∀ g ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g})) :
    (∀ W : Submodule (ZMod p) V, (∀ a ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)), ∀ w ∈ W, a w ∈ W) →
      W ≤ ggLinFix ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) ∨
        ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) ≤ W) ∧
    (∀ W : Submodule (ZMod p) V,
      W ≤ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)), ∀ w ∈ W, a w ∈ W) →
      W = ⊥ ∨ W = ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V))) ∧
    (∀ f : V →ₗ[ZMod p] V,
      LinearMap.range f ≤ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)),
        ∀ u ∈ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)),
          f (a u) = a (f u)) →
      ∃ c : ZMod p,
        ∀ u ∈ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)), f u = c • u) ∧
    (∀ a ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)), ∀ v : V,
      a v - v ∈ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V))) ∧
    (∀ g ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)),
      (∀ u ∈ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)), g u = u) →
        g = 1) ∧
    ((∃ ε ∈ (⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)), ε * ε = 1 ∧
        ∀ u ∈ ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)), ε u = -u) →
      ggLinCom ((⨆ X, AX X : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V)) = ⊤) := by
  classical
  have hX' : ∀ X : I, ∃ S : Set (V ≃ₗ[ZMod p] V),
      (∀ r ∈ S, GGLinRefl r) ∧
      (∀ r ∈ S, ∀ s ∈ S, Relation.EqvGen (fun a b => a ∈ S ∧ b ∈ S ∧ GGLinAdj a b) r s) ∧
      AX X = Subgroup.closure S := hX
  choose S hSrefl hSconn hSeq using hX'
  have hJ' : ∀ X, AJ ≤ Subgroup.closure (S X) := fun X => hSeq X ▸ hJ X
  let A : Subgroup (V ≃ₗ[ZMod p] V) := ⨆ X, AX X
  have hA : A = ⨆ X, AX X := rfl
  have hAeq : A = ⨆ X, Subgroup.closure (S X) := hA.trans (iSup_congr hSeq)
  obtain ⟨r, hrJ, hrrfl⟩ := hJr
  have hrr : r * r = 1 := hrrfl.1
  have hnt : Nontrivial (ggLinMove r) :=
    Module.nontrivial_of_finrank_eq_succ (R := ZMod p) (M := ggLinMove r) (n := 0) hrrfl.2
  obtain ⟨e, he0⟩ := exists_ne (0 : ggLinMove r)
  have he_mem : (e : V) ∈ ggLinMove r := e.2
  have he_ne : (e : V) ≠ 0 := by
    intro h
    exact he0 (Subtype.ext (by simpa using h))
  have hre : r (e : V) = -(e : V) := ggLinMove_neg_of_involution r hrr (e : V) he_mem
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hdvd)
  have he_move : r (e : V) ≠ (e : V) := by
    rw [hre]
    intro hneg
    have h2e : (2 : ZMod p) • (e : V) = 0 := by
      rw [two_smul]
      exact (neg_eq_iff_add_eq_zero).mp hneg
    exact (smul_ne_zero h2 he_ne) h2e
  have heAJ : (e : V) ∈ ggLinCom (AJ : Set (V ≃ₗ[ZMod p] V)) :=
    le_iSup₂ (f := fun a (_ : a ∈ (AJ : Set (V ≃ₗ[ZMod p] V))) => ggLinMove a) r hrJ he_mem
  have hJnt : ∃ a ∈ AJ, ∃ u ∈ ggLinCom (AJ : Set (V ≃ₗ[ZMod p] V)), a u ≠ u :=
    ⟨r, hrJ, (e : V), heAJ, he_move⟩
  have hprop : ∀ W : Submodule (ZMod p) V,
      (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      W ≤ ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) ∨
        ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) ≤ W := by
    intro W hW
    have hW' : ∀ a ∈ (⨆ X, Subgroup.closure (S X) : Subgroup (V ≃ₗ[ZMod p] V)),
        ∀ w ∈ W, a w ∈ W :=
      fun a ha w hw => hW a (hAeq.symm ▸ ha) w hw
    have hmain := ggLin_propagate_across S hSrefl hSconn AJ hJ' hJnt W hW'
    rw [hAeq]
    exact hmain
  have hirr : ∀ W : Submodule (ZMod p) V, W ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
    intro W hWU hWstab
    rcases hprop W hWstab with h | h
    · exact Or.inl (le_bot_iff.mp (h.trans (le_of_eq hfix)))
    · exact Or.inr (le_antisymm hWU h)
  have hend : ∀ f : V →ₗ[ZMod p] V, LinearMap.range f ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f u = c • u := by
    intro f hfrange hfcomm
    obtain ⟨X₀⟩ := (inferInstance : Nonempty I)
    have hrA : r ∈ A := by
      rw [hA]
      exact le_iSup (fun X => AX X) X₀ (hJ X₀ hrJ)
    exact ggLin_end_scalar hp2 A hprop hfix r hrA hrrfl f hfrange hfcomm
  have htriv : ∀ a ∈ A, ∀ v : V, a v - v ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
    intro a ha v
    exact le_iSup₂ (f := fun a (_ : a ∈ (A : Set (V ≃ₗ[ZMod p] V))) => ggLinMove a) a ha
      (LinearMap.mem_range_self (a.toLinearMap - LinearMap.id) v)
  have hfaith : ∀ g ∈ A, (∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), g u = u) → g = 1 := by
    intro g hg hgU
    exact ggLin_faithful_on_com A hnotr hirr hend htriv g hg hgU
  have hUstab : ∀ a ∈ A, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)),
      a u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
    intro a ha u hu
    have h := htriv a ha u
    have hauv : a u = u + (a u - u) := by abel
    rw [hauv]
    exact add_mem hu h
  have heps : (∃ ε ∈ A, ε * ε = 1 ∧
      ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), ε u = -u) →
      ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) = ⊤ := by
    rintro ⟨ε, hε, hεsq, hεneg⟩
    have hεinv : ε⁻¹ = ε := (eq_inv_of_mul_eq_one_left hεsq).symm
    have hεc : ∀ a ∈ A, a * ε = ε * a := by
      intro a ha
      have hgA : a * ε * a⁻¹ * ε⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem ha hε) (A.inv_mem ha)) (A.inv_mem hε)
      have hgU : ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)),
          (a * ε * a⁻¹ * ε⁻¹) u = u := by
        intro u hu
        have hainv : a⁻¹ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) :=
          hUstab a⁻¹ (A.inv_mem ha) u hu
        calc (a * ε * a⁻¹ * ε⁻¹) u
            = a (ε (a⁻¹ (ε u))) := by simp only [LinearEquiv.mul_apply, hεinv]
          _ = a (ε (a⁻¹ (-u))) := by rw [hεneg u hu]
          _ = a (ε (-(a⁻¹ u))) := by rw [map_neg]
          _ = a (-(ε (a⁻¹ u))) := by rw [map_neg]
          _ = a (-(-(a⁻¹ u))) := by rw [hεneg (a⁻¹ u) hainv]
          _ = a (a⁻¹ u) := by rw [neg_neg]
          _ = u := by rw [show a⁻¹ = a.symm from rfl, LinearEquiv.apply_symm_apply]
      have hg1 : a * ε * a⁻¹ * ε⁻¹ = 1 := hfaith _ hgA hgU
      have hmul : (a * ε) * (a⁻¹ * ε⁻¹) = 1 := by
        rw [← mul_assoc (a * ε) a⁻¹ ε⁻¹]
        exact hg1
      calc a * ε = (a⁻¹ * ε⁻¹)⁻¹ := (eq_inv_iff_mul_eq_one).mpr hmul
        _ = ε * a := by rw [mul_inv_rev, inv_inv, inv_inv]
    exact ggLin_eq_com_of_neg_one hp2 A hprop hfix ε hε hεsq hεc hεneg
  exact ⟨hprop, hirr, hend, htriv, hfaith, heps⟩

end Module

end CFSG.StandardType

end
