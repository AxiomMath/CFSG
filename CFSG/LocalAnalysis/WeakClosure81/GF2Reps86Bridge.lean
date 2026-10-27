module

public import CFSG.Milestones.ASVolI.I1
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.WeakClosure81.SevenTenEn
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (altAct altAct_mk evenWeightPerm_apply mem_evenWeightOnes_of_forall_eq
    exists_forall_eq_of_mem_evenWeightOnes)
open CFSG.RankThree.PartTwo (altHeart evenWeightOnes evenWeightPerm)
open CFSG.ASVolI.ChIJK (evenWeightRep constInEven symNaturalRep)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn StableUnder)

private theorem coe_evenWeightRep_apply (n : ℕ) (σ : Perm (Fin n))
    (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) (i : Fin n) :
    ((evenWeightRep n σ x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) : Fin n → ZMod 2) i =
      (x : Fin n → ZMod 2) (σ⁻¹ i) := by
  simp [CFSG.ASVolI.ChIJK.evenWeightRep, CFSG.ASVolI.ChIJK.permRepF2,
    Representation.subrepresentation, LinearMap.funLeft, Equiv.Perm.inv_def]

private theorem mem_constInEven_iff (n : ℕ) (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) :
    x ∈ constInEven n ↔ ∃ c : ZMod 2, ∀ i, (x : Fin n → ZMod 2) i = c := by
  have hx : x ∈ constInEven n ↔
      (x : Fin n → ZMod 2) ∈ Submodule.span (ZMod 2) {fun _ : Fin n => (1 : ZMod 2)} := Iff.rfl
  rw [hx, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun i => by rw [← hc]; simp⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, funext fun i => by simp [hc i]⟩

@[expose] def evenWeightAddEquiv (n : ℕ) :
    ↥(CFSG.ASVolI.ChIJK.evenWeight n) ≃+ ↥(CFSG.QuasithinUnique.evenWeight n) where
  toFun x := ⟨(x : Fin n → ZMod 2), x.2⟩
  invFun y := ⟨(y : Fin n → ZMod 2), y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem coe_evenWeightAddEquiv (n : ℕ) (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) :
    ((evenWeightAddEquiv n x : ↥(CFSG.QuasithinUnique.evenWeight n)) : Fin n → ZMod 2) =
      (x : Fin n → ZMod 2) :=
  rfl

theorem evenWeightAddEquiv_evenWeightRep (n : ℕ) (σ : Perm (Fin n))
    (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) :
    evenWeightAddEquiv n (evenWeightRep n σ x) = evenWeightPerm σ (evenWeightAddEquiv n x) :=
  Subtype.ext (funext fun i => by
    rw [evenWeightPerm_apply, coe_evenWeightAddEquiv, coe_evenWeightAddEquiv,
      coe_evenWeightRep_apply])

theorem evenWeightAddEquiv_mem_evenWeightOnes_iff (n : ℕ)
    (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) :
    evenWeightAddEquiv n x ∈ evenWeightOnes n ↔ x ∈ constInEven n := by
  rw [mem_constInEven_iff]
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_forall_eq_of_mem_evenWeightOnes hx
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact mem_evenWeightOnes_of_forall_eq (c := c) hc

@[expose] def natHeartAddEquiv (n : ℕ) :
    (↥(CFSG.ASVolI.ChIJK.evenWeight n) ⧸ constInEven n) ≃+ altHeart n :=
  QuotientAddGroup.congr (constInEven n).toAddSubgroup (evenWeightOnes n)
    (evenWeightAddEquiv n) (by
      ext y
      obtain ⟨x, rfl⟩ := (evenWeightAddEquiv n).surjective y
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨x', hx', hxx'⟩
        obtain rfl := (evenWeightAddEquiv n).injective hxx'
        exact (evenWeightAddEquiv_mem_evenWeightOnes_iff n x').2 hx'
      · intro hx
        exact ⟨x, (evenWeightAddEquiv_mem_evenWeightOnes_iff n x).1 hx, rfl⟩)

theorem natHeartAddEquiv_mk (n : ℕ) (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) :
    natHeartAddEquiv n (Submodule.Quotient.mk x) =
      (QuotientAddGroup.mk (evenWeightAddEquiv n x) : altHeart n) :=
  rfl

private theorem symNaturalRep_mk (n : ℕ) (σ : Perm (Fin n))
    (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)) :
    symNaturalRep n σ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (evenWeightRep n σ x) := by
  simp [CFSG.ASVolI.ChIJK.symNaturalRep, Representation.quotient]

theorem natHeartAddEquiv_symNaturalRep (n : ℕ) (σ : Perm (Fin n))
    (y : ↥(CFSG.ASVolI.ChIJK.evenWeight n) ⧸ constInEven n) :
    natHeartAddEquiv n (symNaturalRep n σ y) = altAct σ (natHeartAddEquiv n y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [symNaturalRep_mk, natHeartAddEquiv_mk, natHeartAddEquiv_mk, altAct_mk,
    evenWeightAddEquiv_evenWeightRep]

theorem natVia_top_of_equivariant {V : Type} [CommGroup V] [Finite V]
    [Module (ZMod 2) (Additive V)] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}
    (hn : 3 ≤ n) (hψs : Function.Surjective ψ) (hirr : IsIrrOn H ⊤ ⊥)
    (hfix : fixV (altPre ψ) = ⊥)
    (f : ↥(CFSG.ASVolI.ChIJK.evenWeight n) →ₗ[ZMod 2] Additive V)
    (hf : ∀ (h : ↥H) (x : ↥(CFSG.ASVolI.ChIJK.evenWeight n)),
      f (evenWeightRep n (ψ h) x) = Additive.ofMul ((h : MulAut V) (Additive.toMul (f x))))
    (hf0 : f ≠ 0) : NatVia ψ ⊤ := by
  have hker_le : LinearMap.ker f ≤ constInEven n := by
    by_contra hnle
    refine hf0 (LinearMap.ker_eq_top.1 (eq_top_of_not_le_constInEven hn _ ?_ hnle))
    intro σ x hx
    obtain ⟨h, rfl⟩ := hψs σ
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hf, hx]
    exact congrArg Additive.ofMul (map_one (h : MulAut V))
  have hconst_le : constInEven n ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨c, hc⟩ := (mem_constInEven_iff n x).1 hx
    rw [LinearMap.mem_ker]
    have hfx : Additive.toMul (f x) ∈ fixV (altPre ψ) := by
      intro g hg
      have hrep : evenWeightRep n (ψ ⟨g, altPre_le hg⟩) x = x :=
        Subtype.ext (funext fun i => by rw [coe_evenWeightRep_apply, hc, hc])
      have hg' := hf ⟨g, altPre_le hg⟩ x
      rw [hrep] at hg'
      exact (congrArg Additive.toMul hg').symm
    rw [hfix, Subgroup.mem_bot] at hfx
    exact Additive.toMul.injective hfx
  have hker : LinearMap.ker f = constInEven n := le_antisymm hker_le hconst_le
  have hsurj : Function.Surjective f := by
    obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (LinearMap.ext hcon)
    let J : Subgroup V :=
      { carrier := {u | ∃ x, f x = Additive.ofMul u}
        mul_mem' := by
          rintro a b ⟨x, hx⟩ ⟨y, hy⟩
          exact ⟨x + y, by rw [map_add, hx, hy]; rfl⟩
        one_mem' := ⟨0, by rw [map_zero]; rfl⟩
        inv_mem' := by
          rintro a ⟨x, hx⟩
          exact ⟨-x, by rw [map_neg, hx]; rfl⟩ }
    have hJ : ∀ u, u ∈ J ↔ ∃ x, f x = Additive.ofMul u := fun u => Iff.rfl
    have hstab : StableUnder H J := by
      intro g hg u hu
      obtain ⟨x, hx⟩ := (hJ u).1 hu
      refine (hJ _).2 ⟨evenWeightRep n (ψ ⟨g, hg⟩) x, ?_⟩
      rw [hf, hx]
      rfl
    rcases hirr.2.2.2 J hstab bot_le le_top with hbot | htop
    · exfalso
      have hmem : Additive.toMul (f x₀) ∈ J := (hJ _).2 ⟨x₀, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hx₀ (Additive.toMul.injective hmem)
    · intro z
      have hmem : Additive.toMul z ∈ J := htop ▸ Subgroup.mem_top _
      obtain ⟨x, hx⟩ := (hJ _).1 hmem
      exact ⟨x, hx⟩
  have hbij : Function.Bijective ((constInEven n).liftQ f hconst_le) := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hker_le
    · intro z
      obtain ⟨x, rfl⟩ := hsurj z
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  let e : (↥(CFSG.ASVolI.ChIJK.evenWeight n) ⧸ constInEven n) ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective ((constInEven n).liftQ f hconst_le) hbij
  have he_mk : ∀ x, e (Submodule.Quotient.mk x) = f x := fun _ => rfl
  have he_equiv : ∀ (h : ↥H) (y : ↥(CFSG.ASVolI.ChIJK.evenWeight n) ⧸ constInEven n),
      e (symNaturalRep n (ψ h) y) = Additive.ofMul ((h : MulAut V) (Additive.toMul (e y))) := by
    intro h y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [symNaturalRep_mk, he_mk, he_mk]
    exact hf h x
  let E : Additive V ≃+ altHeart n := e.symm.toAddEquiv.trans (natHeartAddEquiv n)
  let π : ↥(⊤ : Subgroup V) →* Multiplicative (altHeart n) :=
    { toFun := fun u => Multiplicative.ofAdd (E (Additive.ofMul (u : V)))
      map_one' := congrArg Multiplicative.ofAdd (map_zero E)
      map_mul' := fun a b => congrArg Multiplicative.ofAdd
        (map_add E (Additive.ofMul (a : V)) (Additive.ofMul (b : V))) }
  have hπinj : Function.Injective π := fun u v huv =>
    Subtype.ext (Additive.ofMul.injective (E.injective (Multiplicative.ofAdd.injective huv)))
  have hπsurj : Function.Surjective π := by
    intro y
    refine ⟨⟨Additive.toMul (E.symm (Multiplicative.toAdd y)), Subgroup.mem_top _⟩, ?_⟩
    show Multiplicative.ofAdd
      (E (Additive.ofMul (Additive.toMul (E.symm (Multiplicative.toAdd y))))) = y
    rw [ofMul_toMul, AddEquiv.apply_symm_apply, ofAdd_toAdd]
  unfold NatVia
  refine ⟨π, hπsurj, ?_, ?_⟩
  · rw [hfix, inf_bot_eq, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff π).2 hπinj
  · intro h u v hv
    have key : e.symm (Additive.ofMul (v : V)) =
        symNaturalRep n (ψ h) (e.symm (Additive.ofMul (u : V))) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, he_equiv, LinearEquiv.apply_symm_apply, hv]
      rfl
    show natHeartAddEquiv n (e.symm (Additive.ofMul (v : V))) =
      altAct (ψ h) (natHeartAddEquiv n (e.symm (Additive.ofMul (u : V))))
    rw [key, natHeartAddEquiv_symNaturalRep]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
