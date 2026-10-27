module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigFix
import CFSG.Milestones.ASVolI.I2BNWeakClosure
import CFSG.LocalAnalysis.SeitzReduction.F4PilotSylowUnique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

theorem k108big_conj_le {Gh : Type} [Group Gh] [Finite Gh] {X M U : Subgroup Gh}
    (hX : (Nat.card X).Prime) (hXM : X ≤ M)
    (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) (hUM : U ≤ M)
    (hXU : X ≤ Subgroup.normalizer (U : Set Gh)) {g : Gh}
    (hXg : X ≤ Subgroup.normalizer ((U.map (MulAut.conj g).toMonoidHom : Subgroup Gh) : Set Gh)) :
    U.map (MulAut.conj g).toMonoidHom ≤ M := by
  classical
  haveI : Fact (Nat.card X).Prime := ⟨hX⟩
  haveI : IsCyclic X := isCyclic_of_prime_card rfl
  obtain ⟨⟨t, htX⟩, ht⟩ := IsCyclic.exists_generator (α := ↥X)
  have hmem : ∀ x ∈ X, ∃ k : ℤ, t ^ k = x := fun x hx => by
    obtain ⟨k, hk⟩ := ht ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have huniq : ∀ y : Gh, y⁻¹ * t * y ∈ M → y ∈ M := fun y hy => hstar y fun x hx => by
    obtain ⟨k, rfl⟩ := hmem x hx
    have e : y⁻¹ * t ^ k * y = (y⁻¹ * t * y) ^ k := by
      simpa only [inv_inv] using (conj_zpow (a := y⁻¹) (b := t) (i := k)).symm
    rw [e]
    exact zpow_mem hy k
  have hXq : IsPGroup (Nat.card X) X := IsPGroup.of_card (n := 1) (by rw [pow_one])
  set R := Subgroup.normalizer (U : Set Gh) with hR
  have hconj : ∀ (K : Subgroup Gh) (a b : Gh), K.map (MulAut.conj (b * a)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom := fun K a b => by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hX'R : ∀ x ∈ X, g⁻¹ * x * g ∈ R := fun x hx => by
    have h1 : (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        U.map (MulAut.conj g).toMonoidHom := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hXg hx)
    have h2 : U.map (MulAut.conj (g⁻¹ * x * g)).toMonoidHom = U := by
      rw [hconj U g (g⁻¹ * x), hconj _ x g⁻¹, h1, ← hconj, inv_mul_cancel]
      ext y
      simp
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 h2
  obtain ⟨P, hXP⟩ := (hXq.comap_of_injective R.subtype Subtype.val_injective).exists_le_sylow
  obtain ⟨P', hX'P'⟩ := ((hXq.map (MulAut.conj g⁻¹).toMonoidHom).comap_of_injective R.subtype
    Subtype.val_injective).exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq (↥R) P' P
  set P₁ : Subgroup Gh := (P : Subgroup R).map R.subtype with hP₁
  have hXP₁ : X ≤ P₁ := fun x hx => ⟨⟨x, hXU hx⟩, hXP hx, rfl⟩
  have hP₁M : P₁ ≤ M := by
    haveI : Group.IsNilpotent P₁ := (P.isPGroup'.map R.subtype).isNilpotent
    exact CFSG.SeitzReduction.F4Pilot.le_of_isNilpotent_of_unique (hXM htX) huniq (hXP₁ htX)
  have hm : g * (r : Gh)⁻¹ ∈ M := by
    refine hstar _ fun x hx => ?_
    have hy : (⟨g⁻¹ * x * g, hX'R x hx⟩ : R) ∈ (P' : Subgroup R) :=
      hX'P' ⟨x, hx, by simp⟩
    have hy' : (MulAut.conj r) • (⟨g⁻¹ * x * g, hX'R x hx⟩ : R) ∈
        (MulAut.conj r) • (P' : Subgroup R) := Subgroup.smul_mem_pointwise_smul _ _ _ hy
    rw [← Sylow.pointwise_smul_def, ← Sylow.smul_def, hr] at hy'
    have : (g * (r : Gh)⁻¹)⁻¹ * x * (g * (r : Gh)⁻¹) =
        R.subtype ((MulAut.conj r) • (⟨g⁻¹ * x * g, hX'R x hx⟩ : R)) := by
      simp [MulAut.smul_def, mul_assoc]
    rw [this]
    exact hP₁M ⟨_, hy', rfl⟩
  have hrU : U.map (MulAut.conj (r : Gh)).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 r.2
  have hg : g = g * (r : Gh)⁻¹ * (r : Gh) := by group
  rw [hg, hconj U (r : Gh) (g * (r : Gh)⁻¹), hrU]
  rintro _ ⟨u, hu, rfl⟩
  exact M.mul_mem (M.mul_mem hm (hUM hu)) (M.inv_mem hm)

theorem k108big_le {Gh : Type} [Group Gh] [Finite Gh] (S : Subgroup Gh) [S.Normal]
    [IsSimpleGroup ↥S] {p : ℕ} [Fact p.Prime] {B N : Subgroup ↥S} [(cartan B N).Normal]
    {W : Set (WeylGroup B N)} (hBN : IsBNPair B N W) {U : Subgroup ↥S} (hUp : IsPGroup p U)
    (hU : U ≠ ⊥) (hUleB : U ≤ B) (hNU : Subgroup.normalizer (U : Set ↥S) = B)
    (hBUH : B ≤ U ⊔ (B ⊓ N)) {X M : Subgroup Gh} (hX : (Nat.card X).Prime)
    (hpX : p ≠ Nat.card X)
    (hXU : X ≤ Subgroup.normalizer ((U.map S.subtype : Subgroup Gh) : Set Gh))
    (hUM : U.map S.subtype ≤ M) (hXM : X ≤ M)
    (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) : S ≤ M := by
  classical
  haveI : Fact (Nat.card X).Prime := ⟨hX⟩
  obtain ⟨n₀, -, hmax⟩ := CFSG.ASVolI.burnsideI25b_exists_max (B := B) (N := N) W W
  have hmax' : ∀ w, wordLength W w ≤ wordLength W (n₀ : WeylGroup B N) := fun w =>
    hmax w (hBN.mem_closure w)
  let φ : ↥X →* MulAut ↥S := (MulAut.conjNormal (H := S)).comp X.subtype
  have hφapp : ∀ (a : ↥X) (y : ↥S), ((φ a y : ↥S) : Gh) = (a : Gh) * y * (a : Gh)⁻¹ :=
    fun a y => MulAut.conjNormal_apply _ _
  have hinj : Function.Injective S.subtype := Subtype.val_injective
  have hφmem : ∀ (a : ↥X) (y : ↥S), φ a y ∈ U ↔ y ∈ U := fun a y => by
    have e1 : φ a y ∈ U ↔ ((φ a y : ↥S) : Gh) ∈ U.map S.subtype :=
      (Subgroup.mem_map_iff_mem hinj).symm
    have e2 : y ∈ U ↔ (y : Gh) ∈ U.map S.subtype := (Subgroup.mem_map_iff_mem hinj).symm
    rw [e1, e2, hφapp]
    exact ((Subgroup.mem_normalizer_iff.1 (hXU a.2)) (y : Gh)).symm
  have hφU : ∀ a, U.map (φ a).toMonoidHom = U := fun a => by
    ext y
    rw [Subgroup.mem_map_equiv, ← hφmem a, MulEquiv.apply_symm_apply]
  have hφB : ∀ (a : ↥X) (y : ↥S), φ a y ∈ B ↔ y ∈ B := fun a y => by
    rw [← hNU]
    have h1 := Subgroup.map_equiv_normalizer_eq U (φ a)
    rw [hφU a] at h1
    constructor
    · intro h
      rw [← h1, Subgroup.mem_map_equiv] at h
      simpa using h
    · intro h
      rw [← h1]
      exact ⟨y, h, rfl⟩
  have hXq : IsPGroup (Nat.card X) ↥X := IsPGroup.of_card (n := 1) (by rw [pow_one])
  obtain ⟨g, hg, hfix⟩ :=
    k108big_exists_conj_fixed hBN hpX hUp hUleB hNU.ge hBUH hmax' hXq φ hφB hφU
  have htop := k108big_sup_conj_eq_top hBN hU hNU.ge hBUH hmax' hg
  have htrans : ∀ (K : Subgroup ↥S) (a : ↥X),
      (K.map S.subtype).map (MulAut.conj (a : Gh)).toMonoidHom =
        (K.map (φ a).toMonoidHom).map S.subtype := fun K a => by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hV : (U.map (MulAut.conj g).toMonoidHom).map S.subtype =
      (U.map S.subtype).map (MulAut.conj (g : Gh)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hXV : X ≤ Subgroup.normalizer
      (((U.map S.subtype).map (MulAut.conj (g : Gh)).toMonoidHom : Subgroup Gh) : Set Gh) := by
    intro a ha
    rw [← hV]
    refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
    have := htrans (U.map (MulAut.conj g).toMonoidHom) ⟨a, ha⟩
    rw [hfix ⟨a, ha⟩] at this
    exact this
  have hVM := k108big_conj_le hX hXM hstar hUM hXU hXV
  intro x hx
  have hxtop : (⟨x, hx⟩ : ↥S) ∈ U ⊔ U.map (MulAut.conj g).toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  have := Subgroup.mem_map_of_mem S.subtype hxtop
  rw [Subgroup.map_sup, hV] at this
  exact (sup_le hUM hVM) this

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
