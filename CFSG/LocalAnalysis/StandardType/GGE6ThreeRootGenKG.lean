module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCoverTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenRefl
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenCoord
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenGen
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelE6Kernel
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG

public section

namespace CFSG.StandardType.E6ThreeRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem image_fix_excRefl_map_e6
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    {K : Type} [Field K] {g : ModGL .E6 K} {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) :
    (fun a : A => g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
        (Multiplicative.toAdd (κ a))) * g⁻¹) ''
      {a : A | ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) =
        Multiplicative.toAdd (κ a)} =
    ⇑(MulAut.conj g) ''
      ((fun x : Fin Tag.E6.rank → ZMod 3 => rootDiagUnit .E6
          (TableBExc.E6Three.zetaVec ζ hζ x)) ''
        {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧
          ∑ j, (γ j : ZMod 3) * x j = 0}) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [TwE6ThreeRootGen.image_fix_excRefl_toAdd (V := V) (γ := γ) (t := fun x =>
    g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) hVmem]
  have hfix : {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧
      ExcSplitRootGen.excRefl (p := 3) γ x = x} =
      {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧
        ∑ j, (γ j : ZMod 3) * x j = 0} := by
    ext x
    constructor
    · rintro ⟨hxV, hx⟩
      exact ⟨hxV, (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x).1 hx⟩
    · rintro ⟨hxV, hx⟩
      exact ⟨hxV, (ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hγ x).2 hx⟩
  have hfun : (fun x : Fin Tag.E6.rank → ZMod 3 =>
      g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) =
      ⇑(MulAut.conj g) ∘ fun x =>
        rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) := by
    funext x
    rw [Function.comp_apply, MulAut.conj_apply]
  rw [hfix, ← Set.image_comp, hfun]

private theorem comap_map_conj_centralizer_e6 {K : Type} [Field K]
    {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K) (D : Set (ModGL .E6 K)) :
    ((Subgroup.centralizer D).map (MulAut.conj g).toMonoidHom).comap
        (adjointGroup .E6 K).subtype =
      (((Subgroup.centralizer D).comap (adjointGroup .E6 K).subtype).map
        (MulAut.conj ⟨g, hg⟩).toMonoidHom) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_comap] at hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    have hzx' : (MulAut.conj g) z = (x : ModGL .E6 K) := hzx
    have hzC : z ∈ adjointGroup .E6 K := by
      have h : z = g⁻¹ * (x : ModGL .E6 K) * g := by
        rw [← hzx', MulAut.conj_apply]
        group
      rw [h]
      exact (adjointGroup .E6 K).mul_mem ((adjointGroup .E6 K).mul_mem
        ((adjointGroup .E6 K).inv_mem hg) x.2) hg
    refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, ?_⟩
    · exact hz
    · apply Subtype.ext
      exact hzx'
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩

theorem isComponentOf_excComp_map_conj_e6
    {K : Type} [Field K] {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    (hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)))
    (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ}) :
    IsComponentOf ((ExcSplitRootGen.excComp (K := K) i.1).map
        (MulAut.conj ⟨g, hg⟩).toMonoidHom)
      ((Subgroup.centralizer ((fun a : A => g * rootDiagUnit .E6
          (TableBExc.E6Three.zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹) ''
        {a : A | ExcSplitRootGen.excRefl (p := 3) i.1 (Multiplicative.toAdd (κ a)) =
          Multiplicative.toAdd (κ a)})).comap (adjointGroup .E6 K).subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hroot : ∀ β, IsRoot .E6 β → (∀ x ∈ V, ∑ j, (i.1 j : ZMod 3) * x j = 0 →
      ∑ j, (β j : ZMod 3) * x j = 0) → β = i.1 ∨ β = -i.1 :=
    fun β hβ h => TwE6ThreeRootGen.eq_or_eq_neg_of_forall_mem_sum_eq_zero hV i.2 hβ h
  have hcomp := isComponentOf_excComp_of_forall_mem (K := K) (p := 3)
    (by norm_num : (3 : ℕ) ≠ 2) hζo hζ (V := V) i.2 hroot
  have himg := image_fix_excRefl_map_e6 (g := g) (κ := κ) hVmem hζ i.2
  have hcen := CFSG.Fischer.centralizer_image_eq_map (MulAut.conj g)
    ((fun x : Fin Tag.E6.rank → ZMod 3 => rootDiagUnit .E6
      (TableBExc.E6Three.zetaVec ζ hζ x)) ''
      {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧ ∑ j, (i.1 j : ZMod 3) * x j = 0})
  have hcm := comap_map_conj_centralizer_e6 (g := g) hg
    ((fun x : Fin Tag.E6.rank → ZMod 3 => rootDiagUnit .E6
      (TableBExc.E6Three.zetaVec ζ hζ x)) ''
      {x : Fin Tag.E6.rank → ZMod 3 | x ∈ V ∧ ∑ j, (i.1 j : ZMod 3) * x j = 0})
  rw [himg, hcen]
  simp only [← MulEquiv.toMonoidHom_eq_coe]
  rw [hcm]
  have h := CFSG.StandardType.isComponentOf_map_mulEquiv' (MulAut.conj ⟨g, hg⟩) hcomp
  exact h

theorem dvd_card_excComp_map_conj_e6
    {K : Type} [Field K] {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ}) :
    3 ∣ Nat.card ((ExcSplitRootGen.excComp (K := K) i.1).map
      (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).toMonoidHom) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.card_map_of_injective
    (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).injective]
  refine ExcSplitRootGen.dvd_card_excComp (K := K) (p := 3) (by norm_num) hζo i.2 ?_
  intro β hβ h
  exact ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero (τ := .E6) (Or.inl rfl)
    (by norm_num) i.2 hβ h

private theorem iSup_excComp_map_conj_e6
    {K : Type} [Field K] {g : ModGL .E6 K} (hg : g ∈ adjointGroup .E6 K)
    (j : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ}) :
    (⨆ (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ})
        (_ : ExcSplitRootGen.excRefl (p := 3) i.1 ≠
          ExcSplitRootGen.excRefl (p := 3) j.1),
        (ExcSplitRootGen.excComp (K := K) i.1).map
          (MulAut.conj ⟨g, hg⟩).toMonoidHom) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen := ExcSplitRootGen.iSup_excComp_ne (K := K) (p := 3) (τ := .E6) (Or.inl rfl)
    (fun α hα t => ExcSplitRootGen.excRefl_eq_self_iff (p := 3) (by norm_num) hα t)
    (fun α β hα hβ h => ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero (τ := .E6)
      (Or.inl rfl) (by norm_num) hα hβ h) j
  have h1 : (⨆ (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ})
        (_ : ExcSplitRootGen.excRefl (p := 3) i.1 ≠
          ExcSplitRootGen.excRefl (p := 3) j.1),
        (ExcSplitRootGen.excComp (K := K) i.1).map
          (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).toMonoidHom) =
      (⨆ (i : {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ})
        (_ : ExcSplitRootGen.excRefl (p := 3) i.1 ≠
          ExcSplitRootGen.excRefl (p := 3) j.1),
        ExcSplitRootGen.excComp (K := K) i.1).map
          (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).toMonoidHom := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => (Subgroup.map_iSup
      (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).toMonoidHom
      (fun _ : ExcSplitRootGen.excRefl (p := 3) i.1 ≠
        ExcSplitRootGen.excRefl (p := 3) j.1 =>
        ExcSplitRootGen.excComp (K := K) i.1)).symm
  rw [h1, hgen]
  exact Subgroup.map_top_of_surjective _
    (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).surjective

theorem ggTorusRootGenAvoidKG_E6Three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcard]
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  let e := TableBExc.recipeEquiv .E6 K
  refine ggTorusRootGenAvoidKG_of_mulEquiv e
    (I' := (MulAut.congr e) '' TableBExc.RecipeID .E6 K)
    (fun φ hφ => ⟨φ, hφ, rfl⟩) ?_
  intro L' _ _ ψ hψ hker hperf A hA hAI h5 h3A hsc
  have hAH : ∀ a ∈ A, ∃ φ ∈ (TableBExc.E6Three.hatAut .E6 K).range,
      ∀ l, φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, ⟨φ₀, hφ₀, rfl⟩, hφ⟩ := hAI a ha
    exact ⟨MulAut.congr e φ₀, (E6ThreeModel.recipeID_iff_hatAut φ₀).1 hφ₀, hφ⟩
  let ψr : L' →* TableBExc.RecipeGroup .E6 K := e.symm.toMonoidHom.comp ψ
  have hψr : Function.Surjective ψr := e.symm.surjective.comp hψ
  have hkereq : ψr.ker = ψ.ker :=
    MonoidHom.ker_comp_of_injective ψ e.symm.toMonoidHom e.symm.injective
  have hcard : Nat.card ψ.ker ∣ 3 := by
    rw [← hkereq]
    exact TableBExc.E6Three.card_ker_dvd_three_e6 (n := (n : ℕ)) hn hK hψr
      (by rw [hkereq]; exact hker) hperf
  have hodd : ∀ z ∈ ψ.ker, Odd (orderOf z) := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ.ker hz).trans hcard
    rcases (Nat.dvd_prime Nat.prime_three).1 hz3 with h | h
    · rw [h]; exact ⟨0, rfl⟩
    · rw [h]; exact ⟨1, rfl⟩
  have hkerp : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ.ker hz).trans hcard
    exact orderOf_dvd_iff_pow_eq_one.1 hz3
  obtain ⟨g, κ, T, hg, hκinj, hκrange, hreal, hkerT_odd, hTA, hH, -⟩ :=
    exists_frame_torus_E (ζ := ζ) hζ hζo hψ hker hperf hcard hA hAH h5 hsc
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    TwE6ThreeRootGen.coordSet_eq_univ_or_hypE6 hκrange
  let ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot .E6 γ}
  haveI : Nonempty ι := ⟨⟨Pi.single 0 1, isRoot_single Tag.E6 0⟩⟩
  let s : ι → (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3 :=
    fun i => ExcSplitRootGen.excRefl (p := 3) i.1
  let τ : (Fin Tag.E6.rank → ZMod 3) → ModGL .E6 K :=
    fun x => g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹
  let r : ι → adjointGroup .E6 K :=
    fun i => ⟨g, hg⟩ * ExcSplitRootGen.excWeyl (K := K) i * ⟨g, hg⟩⁻¹
  let S : ι → Subgroup (adjointGroup .E6 K) :=
    fun i => (ExcSplitRootGen.excComp (K := K) i.1).map
      (MulAut.conj (⟨g, hg⟩ : adjointGroup .E6 K)).toMonoidHom
  refine ggTorusRootGenAvoid_of_coverTorus (p := 3) (k := Tag.E6.rank) (L' := L')
    (R := ↥(adjointGroup .E6 K)) (G := ModGL .E6 K)
    (ψ := ψ) (A := A) (Φ := κ) (τ := τ) (T := T) (ι := ι) (s := s) (r := r) (S := S)
    (ι₀ := (adjointGroup .E6 K).subtype)
    hψ hker hperf ?_ ?_ ?_ hκinj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  · exact hkerp
  · exact Subgroup.subtype_injective _
  · intro x y
    change g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ
        (x + y)) * g⁻¹ =
      (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) *
        (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ y) * g⁻¹)
    rw [ExcFrames.zetaVec_add (τ := Tag.E6) ζ hζ (x := x) (y := y), rootDiagUnit_mul]
    group
  · exact hreal
  · exact hTA
  · intro z hz
    exact hkerT_odd z hz (hodd z hz)
  · intro i x
    change (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹) *
        (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
        (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹)⁻¹ =
      g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
        (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹
    calc (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹) *
          (g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
          (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) * g⁻¹)⁻¹
        = g * ((ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K) *
            rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) *
            (ExcSplitRootGen.excWeyl (K := K) i : ModGL .E6 K)⁻¹) * g⁻¹ := by group
      _ = g * rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ
            (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹ := by
          rw [excWeyl_conj_rootDiagUnit (τ := Tag.E6) (K := K) (p := 3) hζ i x]
  · intro i a
    exact ExcSplitRootGen.excRefl_excRefl (τ := Tag.E6) (p := 3) i.2 _
  · intro i
    exact TwE6ThreeRootGen.card_fix_excRefl_toAdd_mul_three (κ := κ) hκinj hVmem hV i.2
  · intro i a
    exact hH _ (TwE6ThreeRootGen.excRefl_sub_mem_hypE6 _ _)
  · intro i
    refine Subgroup.mem_map.mpr ⟨ExcSplitRootGen.excWeyl (K := K) i,
      ExcSplitRootGen.excWeyl_mem_excComp i, ?_⟩
    rfl
  · intro i
    exact isComponentOf_excComp_map_conj_e6 (g := g) hg hζo hζ hVmem hV i
  · intro i
    exact dvd_card_excComp_map_conj_e6 (g := g) hg hζo i
  · intro j
    refine (iSup_congr fun i => iSup_congr_Prop
      (TwE6ThreeRootGen.exists_excRefl_toAdd_ne_iff (κ := κ) hVmem hV i.2 j.2)
        (fun _ => rfl)).trans ?_
    exact iSup_excComp_map_conj_e6 (g := g) hg j

end CFSG.StandardType.E6ThreeRootGen

end
