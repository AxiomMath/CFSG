module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKFlipA
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKAstd
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k j : ℕ}
variable (D : StdData G T L I K m k (m + 1) j) (hj : 0 < j)

noncomputable def zE (t : Fin j → Fin (m + 1) → ZMod 2) : G :=
  Classical.choose (exists_coG_eq D t)

theorem zE_mem (t : Fin j → Fin (m + 1) → ZMod 2) : zE D t ∈ uZero I K :=
  (Classical.choose_spec (exists_coG_eq D t)).1

theorem coG_zE (t : Fin j → Fin (m + 1) → ZMod 2) : coG D (zE D t) = t :=
  (Classical.choose_spec (exists_coG_eq D t)).2

theorem zE_coG {z : G} (hz : z ∈ uZero I K) : zE D (coG D z) = z :=
  coG_injOn D (zE_mem D _) hz (coG_zE D _)

theorem zE_add (t t' : Fin j → Fin (m + 1) → ZMod 2) : zE D (t + t') = zE D t * zE D t' := by
  apply coG_injOn D (zE_mem D _) (Subgroup.mul_mem _ (zE_mem D t) (zE_mem D t'))
  rw [coG_zE, coG_mul D (zE_mem D t) (zE_mem D t'), coG_zE, coG_zE]

theorem zE_zero : zE D (0 : Fin j → Fin (m + 1) → ZMod 2) = 1 := by
  apply coG_injOn D (zE_mem D _) (one_mem _)
  rw [coG_zE, coG_one D]

theorem exists_wZ_eq (x : Fin j → ZMod 2) : ∃ u : G, u ∈ uZero I K ∧ wZ D u = x := by
  refine ⟨zE D (fun i => Pi.single (Fin.last m) (x i)), zE_mem D _, ?_⟩
  funext i
  simp [wZ, coG_zE]

variable {D} (F : RForm D)

@[expose] def wE : (Fin j → Fin (m + 1) → ZMod 2) →+ (Fin j → ZMod 2) :=
  AddMonoidHom.mk' (fun t i => t i (Fin.last m)) (fun _ _ => rfl)

theorem wE_surj : Function.Surjective (wE (j := j) (m := m)) := by
  intro x
  refine ⟨fun i => Pi.single (Fin.last m) (x i), ?_⟩
  funext i
  simp [wE]

theorem wE_zE (t : Fin j → Fin (m + 1) → ZMod 2) : wE t = wZ D (zE D t) := by
  funext i
  simp [wE, wZ, coG_zE]

theorem arOf_one (F : RForm D) : arOf D hj (1 : G) = 0 :=
  (arOf_eq_zero_iff D hj F (one_mem _)).mpr (fun z _ => by simp)

@[expose] noncomputable def AE (g : G) (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I) :
    (Fin j → Fin (m + 1) → ZMod 2) →+ ↥(astd m) where
  toFun t := ⟨arOf D hj (g⁻¹ * zE D t * g),
    (mem_astd _).mpr (arOf_spec D hj F (h1 _ (zE_mem D t))).1⟩
  map_zero' := by
    apply Subtype.ext
    show arOf D hj (g⁻¹ * zE D 0 * g) = 0
    rw [zE_zero, show g⁻¹ * (1 : G) * g = 1 by group, arOf_one hj F]
  map_add' := by
    intro t t'
    apply Subtype.ext
    show arOf D hj (g⁻¹ * zE D (t + t') * g) =
      arOf D hj (g⁻¹ * zE D t * g) + arOf D hj (g⁻¹ * zE D t' * g)
    rw [zE_add, show g⁻¹ * (zE D t * zE D t') * g = (g⁻¹ * zE D t * g) * (g⁻¹ * zE D t' * g) by
      group]
    exact arOf_mul D hj F (h1 _ (zE_mem D t)) (h1 _ (zE_mem D t'))

@[expose] noncomputable def AE' (g : G) (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) :
    (Fin j → Fin (m + 1) → ZMod 2) →+ ↥(astd m) where
  toFun t := ⟨arOf D hj (g * zE D t * g⁻¹),
    (mem_astd _).mpr (arOf_spec D hj F (h2 _ (zE_mem D t))).1⟩
  map_zero' := by
    apply Subtype.ext
    show arOf D hj (g * zE D 0 * g⁻¹) = 0
    rw [zE_zero, show g * (1 : G) * g⁻¹ = 1 by group, arOf_one hj F]
  map_add' := by
    intro t t'
    apply Subtype.ext
    show arOf D hj (g * zE D (t + t') * g⁻¹) =
      arOf D hj (g * zE D t * g⁻¹) + arOf D hj (g * zE D t' * g⁻¹)
    rw [zE_add, show g * (zE D t * zE D t') * g⁻¹ = (g * zE D t * g⁻¹) * (g * zE D t' * g⁻¹) by
      group]
    exact arOf_mul D hj F (h2 _ (zE_mem D t)) (h2 _ (zE_mem D t'))

theorem AE_apply (g : G) (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (t : Fin j → Fin (m + 1) → ZMod 2) :
    ((AE hj F g h1 t : ↥(astd m)) : Fin (m + 1) → ZMod 2) = arOf D hj (g⁻¹ * zE D t * g) := rfl

theorem AE'_apply (g : G) (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (t : Fin j → Fin (m + 1) → ZMod 2) :
    ((AE' hj F g h2 t : ↥(astd m)) : Fin (m + 1) → ZMod 2) = arOf D hj (g * zE D t * g⁻¹) := rfl

theorem exists_flip_equivs (F : RForm D) (hjm : j = m) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (hA : ∃ v ∈ uZero I K, arOf D hj (g⁻¹ * v * g) ≠ 0)
    (hA' : ∃ u ∈ uZero I K, arOf D hj (g * u * g⁻¹) ≠ 0) :
    ∃ ā ā' : (Fin j → ZMod 2) ≃+ ↥(astd m),
      (∀ v ∈ uZero I K, arOf D hj (g⁻¹ * v * g) = (ā (wZ D v) : Fin (m + 1) → ZMod 2)) ∧
      (∀ u ∈ uZero I K, arOf D hj (g * u * g⁻¹) = (ā' (wZ D u) : Fin (m + 1) → ZMod 2)) := by
  have hcardW : Nat.card (Fin j → ZMod 2) = Nat.card (astd m) := by
    rw [card_astd, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
      Nat.card_eq_fintype_card (α := Fin j), Fintype.card_fin, hjm]
  obtain ⟨ā, hā⟩ := exists_addEquiv_factor (wE (j := j) (m := m)) wE_surj (AE hj F g h1)
    (fun t => by
      rw [wE_zE (D := D), wZ_eq_zero_iff D hj F h1 h2 hA' (zE_mem D t)]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h) hcardW
  obtain ⟨ā', hā'⟩ := exists_addEquiv_factor (wE (j := j) (m := m)) wE_surj (AE' hj F g h2)
    (fun t => by
      rw [wE_zE (D := D), wZ_eq_zero_iff' D hj F h1 h2 hA (zE_mem D t)]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h) hcardW
  refine ⟨ā, ā', fun v hv => ?_, fun u hu => ?_⟩
  · have h := congrArg Subtype.val (hā (coG D v))
    rw [AE_apply hj F, wE_zE (D := D), zE_coG D hv] at h
    exact h
  · have h := congrArg Subtype.val (hā' (coG D u))
    rw [AE'_apply hj F, wE_zE (D := D), zE_coG D hu] at h
    exact h

structure FlipEq (D : StdData G T L I K m k (m + 1) j) (hj : 0 < j) (g : G) where
  ab : (Fin j → ZMod 2) ≃+ ↥(astd m)
  ab' : (Fin j → ZMod 2) ≃+ ↥(astd m)
  h1 : ∀ v ∈ uZero I K, arOf D hj (g⁻¹ * v * g) = (ab (wZ D v) : Fin (m + 1) → ZMod 2)
  h2 : ∀ u ∈ uZero I K, arOf D hj (g * u * g⁻¹) = (ab' (wZ D u) : Fin (m + 1) → ZMod 2)

theorem exists_pure_flip (F : RForm D) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) (E : FlipEq D hj g) (a₀ : ↥(astd m))
    (x : Fin j → ZMod 2) :
    ∃ c : G, c ∈ uZero I K ∧ coG D c = tens (a₀ : Fin (m + 1) → ZMod 2) x ∧
      g * c * g⁻¹ ∈ uZero I K ∧
      coG D (g * c * g⁻¹) = tens (E.ab' x : Fin (m + 1) → ZMod 2) (E.ab.symm a₀) := by
  obtain ⟨u, hu, hwu⟩ := exists_wZ_eq D x
  obtain ⟨v, hv, hwv⟩ := exists_wZ_eq D (E.ab.symm a₀)
  obtain ⟨⟨hcZ, hcc⟩, ⟨hcZ', hcc'⟩⟩ := flip_identity D hj F h1 h2 hu hv
  refine ⟨_, hcZ, ?_, hcZ', ?_⟩
  · rw [hcc, E.h1 v hv, hwv, hwu, E.ab.apply_symm_apply]
  · rw [hcc', E.h2 u hu, hwu, hwv]

end CFSG.Quasithin.H13.Ch4.NSB
