module

public import CFSG.LocalAnalysis.StandardType.GGWeylESystem
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggDepAThree_surv_weyl
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) {A : Subgroup (MulAut ↥Bs)}
    (gens : Set (V ≃ₗ[ZMod 3] V)) (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gens)
    (x : V) (s : Fin 6 → (V ≃ₗ[ZMod 3] V)) (w : Fin 72 → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i, s i ∈ Subgroup.closure gens)
    (hsr : ∀ i, ∃ (c : V) (f : Module.Dual (ZMod 3) V), f c = 2 ∧ ∀ v, s i v = v - f v • c)
    (hrel : ∀ i j, (s i * s j) ^ (CoxeterMatrix.E₆ i j) = 1)
    (hgen : ∀ g ∈ gens, g ∈ Subgroup.closure (Set.range s))
    (hw : ∀ k, w k ∈ Subgroup.closure gens) (hinj : Function.Injective fun k => w k x)
    (hstab : ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), H ≤ Subgroup.closure gens ∧
      (∀ g ∈ H, g x = x) ∧ 720 ≤ Nat.card H) :
    GGWeylReflectionGroup 3 A := by
  have hsA : ∀ i, s i ∈ A.map (ggLin (p := 3) ι) := fun i => by rw [hA]; exact hs i
  choose φ hφA hφ using fun i => Subgroup.mem_map.mp (hsA i)
  have hφLift : CoxeterMatrix.E₆.IsLiftable φ := by
    intro i j
    apply ggLin_injective (p := 3) ι
    rw [map_pow, map_mul, hφ i, hφ j, map_one]
    exact hrel i j
  have hrefl : ∀ i, GGIsReflection 3 (φ i) := by
    intro i
    obtain ⟨c, f, hfc, hform⟩ := hsr i
    refine ggIsReflection_of_eq_reflection (p := 3) (by norm_num) ι hfc ?_
    exact ggLin_eq_reflection ι hfc (fun v => by rw [hφ i]; exact hform v)
  have hmap_eq : (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι)
      = Subgroup.closure gens := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      change ggLin (p := 3) ι (φ i) ∈ Subgroup.closure gens
      rw [hφ i]
      exact hs i
    · rw [Subgroup.closure_le]
      intro g hg
      have hsub : Set.range s ⊆ ((Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) :
          Set (V ≃ₗ[ZMod 3] V)) := by
        rintro _ ⟨i, rfl⟩
        exact Subgroup.mem_map.mpr ⟨φ i, Subgroup.subset_closure ⟨i, rfl⟩, hφ i⟩
      exact (Subgroup.closure_le _).mpr hsub (hgen g hg)
  have hclosure : Subgroup.closure (Set.range φ) = A := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hφA i
    · intro a ha
      have hmem : ggLin (p := 3) ι a ∈
          (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
        rw [hmap_eq, ← hA]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hmem
      have hb_eq : b = a := ggLin_injective (p := 3) ι hba
      simpa [hb_eq] using hb
  have hcardA : Nat.card A = Nat.card ↥(Subgroup.closure gens) := by
    rw [← hA]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective A (ggLin (p := 3) ι) (ggLin_injective (p := 3) ι)).toEquiv
  haveI : Finite (Additive ↥Bs) := inferInstance
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  let G' : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure gens
  obtain ⟨H, hHle, hHfix, hHcard⟩ := hstab
  have horbit : 72 ≤ Nat.card (MulAction.orbit ↥G' x) := by
    let g : Fin 72 → MulAction.orbit ↥G' x := fun k =>
      ⟨w k x, MulAction.mem_orbit_iff.mpr ⟨⟨w k, hw k⟩, by
        rw [Subgroup.smul_def, LinearEquiv.smul_def]⟩⟩
    have hg : Function.Injective g := by
      intro a b hab
      have h1 : w a x = w b x := congrArg Subtype.val hab
      exact hinj h1
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  have hstab_card : 720 ≤ Nat.card ↥(MulAction.stabilizer ↥G' x) := by
    let f : ↥H → ↥(MulAction.stabilizer ↥G' x) := fun h =>
      ⟨⟨(h : V ≃ₗ[ZMod 3] V), hHle h.2⟩, by
        rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def]
        exact hHfix _ h.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (f a : ↥G') = (f b : ↥G') := congrArg Subtype.val hab
      exact Subtype.ext (congrArg (fun z : ↥G' => (z : V ≃ₗ[ZMod 3] V)) h1)
    exact le_trans hHcard (Nat.card_le_card_of_injective f hf)
  haveI : Fintype ↥G' := Fintype.ofFinite ↥G'
  haveI : Fintype (MulAction.orbit ↥G' x) := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer ↥G' x) := Fintype.ofFinite _
  have hos : Nat.card (MulAction.orbit ↥G' x) * Nat.card ↥(MulAction.stabilizer ↥G' x)
      = Nat.card ↥G' := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥G') (X := V) x
  have hcard_closure : 51840 ≤ Nat.card ↥(Subgroup.closure gens) := by
    calc
      51840 = 72 * 720 := by norm_num
      _ ≤ Nat.card (MulAction.orbit ↥G' x) * Nat.card ↥(MulAction.stabilizer ↥G' x) :=
        Nat.mul_le_mul horbit hstab_card
      _ = Nat.card ↥G' := hos
  have hcard : 51840 ≤ Nat.card ↥A := by
    rw [hcardA]
    exact hcard_closure
  exact ggWeylReflectionGroup_of_E6_system (p := 3) φ hφLift hrefl hclosure hcard

end CFSG.StandardType
