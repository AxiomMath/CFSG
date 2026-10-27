module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeD4Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma e6c3i_commutator_sup_central_le {G : Type*} [Group G] {J K : Subgroup G}
    (hK : K ≤ Subgroup.center G) : ⁅J ⊔ K, J ⊔ K⁆ ≤ ⁅J, J⁆ := by
  haveI : K.Normal := ⟨fun k hk g => by
    have h := Subgroup.mem_center_iff.mp (hK hk) g
    rw [h]
    simpa using hk⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨jx, hjx, kx, hkx, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := J) (t := K)).mp hx
  obtain ⟨jy, hjy, ky, hky, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := J) (t := K)).mp hy
  have hcx : ∀ z : G, kx * z * kx⁻¹ = z := by
    intro z
    rw [← Subgroup.mem_center_iff.mp (hK hkx) z]
    group
  have hcy : ∀ z : G, ky * z * ky⁻¹ = z := by
    intro z
    rw [← Subgroup.mem_center_iff.mp (hK hky) z]
    group
  convert Subgroup.commutator_mem_commutator hjx hjy using 1
  rw [commutatorElement_def, commutatorElement_def]
  rw [mul_inv_rev, mul_inv_rev]
  rw [show (jx * kx) * (jy * ky) * (kx⁻¹ * jx⁻¹) * (ky⁻¹ * jy⁻¹) =
      jx * (kx * (jy * ky) * kx⁻¹) * jx⁻¹ * ky⁻¹ * jy⁻¹ by group]
  rw [hcx]
  rw [show jx * (jy * ky) * jx⁻¹ * ky⁻¹ * jy⁻¹ =
      jx * jy * (ky * jx⁻¹ * ky⁻¹) * jy⁻¹ by group]
  rw [hcy]

private lemma e6c3i_excComp_map_le {K : Type} [Field K]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Kˣ} {i : KernelComponent χ}
    {c : Fin Tag.E6.rank → ℤ} (hc : c ∈ componentRoots χ i) :
    (ExcSplitRootGen.excComp (K := K) c).map (adjointGroup Tag.E6 K).subtype ≤
      componentRootSpan K χ i := by
  have hneg : -c ∈ componentRoots χ i :=
    (isRootComponent_componentRoots (χ := χ) i).neg_mem c hc
  have hc_le : rootSubgroup Tag.E6 K c ≤ componentRootSpan K χ i := by
    have := rootSubgroup_le_componentRootSpan (K := K) (χ := χ) ⟨c, hc.1⟩
    rwa [hc.2] at this
  have hneg_le : rootSubgroup Tag.E6 K (-c) ≤ componentRootSpan K χ i := by
    have := rootSubgroup_le_componentRootSpan (K := K) (χ := χ) ⟨-c, hneg.1⟩
    rwa [hneg.2] at this
  have hrootspan : rootSpan Tag.E6 K ({c, -c} : Set (Fin Tag.E6.rank → ℤ)) ≤
      componentRootSpan K χ i := by
    refine iSup₂_le fun α hα => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl
    · exact hc_le
    · exact hneg_le
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  change y ∈ (rootSpan Tag.E6 K ({c, -c} : Set (Fin Tag.E6.rank → ℤ))).subgroupOf
    (adjointGroup Tag.E6 K) at hy
  exact hrootspan (Subgroup.mem_subgroupOf.mp hy)

private lemma e6c3i_conj_subtype {K : Type} [Field K] (g : ModGL Tag.E6 K)
    (hg : g ∈ adjointGroup Tag.E6 K) (x : ↥(adjointGroup Tag.E6 K)) :
    (MulAut.conj g) ((adjointGroup Tag.E6 K).subtype x) =
      (adjointGroup Tag.E6 K).subtype
        ((MulEquiv.toMonoidHom (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K))) x) := by
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
    Subgroup.coe_subtype]

private theorem e6c3i_exists_refl_lift_mem
    {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hkerp : ∀ z ∈ ψ₀.ker, z ^ 3 = 1)
    {A : Subgroup (MulAut L')} {g : ModGL Tag.E6 K} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup L'} (hg : g ∈ adjointGroup Tag.E6 K) (hκinj : Function.Injective κ)
    (hκrange : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    (hreal : ∀ (a : A) (l : L'),
      ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹) *
          ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * g⁻¹)⁻¹)
    (hkerT : ψ₀.ker ≤ T) (hTA : ∀ a ∈ A, ∀ y ∈ T, a y = y)
    (hH : ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : A,
      MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt 3 A n ∧ GGIsReflection 3 (ggConjAut A hn) ∧
      n ∈ ⁅((ExcSplitRootGen.excComp (K := K) γ).map
            (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀,
          ((ExcSplitRootGen.excComp (K := K) γ).map
            (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀⁆ ∧
      ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hn a)) =
        ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) := by
  classical
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 K) = ⊥ :=
    center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  let V : Set (Fin Tag.E6.rank → ZMod 3) := {x | Multiplicative.ofAdd x ∈ κ.range}
  have hVmem : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V := fun _ => Iff.rfl
  have hV : V = Set.univ ∨ V = (NoOffRest.hypE6 : Set (Fin Tag.E6.rank → ZMod 3)) :=
    TwE6ThreeRootGen.coordSet_eq_univ_or_hypE6 hκrange
  let ι := {γ : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 γ}
  let s : ι → (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3 :=
    fun i => ExcSplitRootGen.excRefl (p := 3) i.1
  let τ : (Fin Tag.E6.rank → ZMod 3) → ModGL Tag.E6 K :=
    fun x => g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹
  let r : ι → adjointGroup Tag.E6 K :=
    fun i => ⟨g, hg⟩ * ExcSplitRootGen.excWeyl (K := K) i * ⟨g, hg⟩⁻¹
  let S : ι → Subgroup (adjointGroup Tag.E6 K) :=
    fun i => (ExcSplitRootGen.excComp (K := K) i.1).map
      (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom
  have hτ : ∀ x y : Fin Tag.E6.rank → ZMod 3, τ (x + y) = τ x * τ y := by
    intro x y
    change g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ (x + y)) *
        g⁻¹ =
      (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ x) * g⁻¹) *
        (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ y) * g⁻¹)
    rw [ExcFrames.zetaVec_add (τ := Tag.E6) ζ hζ (x := x) (y := y), rootDiagUnit_mul]
    group
  have hr : ∀ (i : ι) (x : Fin Tag.E6.rank → ZMod 3),
      (adjointGroup Tag.E6 K).subtype (r i) * τ x *
        ((adjointGroup Tag.E6 K).subtype (r i))⁻¹ = τ (s i x) := by
    intro i x
    change (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹) *
        (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
        (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹)⁻¹ =
      g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ
        (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹
    calc (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) * g⁻¹) *
          (g * (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) * g⁻¹)⁻¹
        = g * ((ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K) *
            rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ x) *
            (ExcSplitRootGen.excWeyl (K := K) i : ModGL Tag.E6 K)⁻¹) * g⁻¹ := by group
      _ = g * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ
            (ExcSplitRootGen.excRefl (p := 3) i.1 x)) * g⁻¹ := by
          rw [E6ThreeRootGen.excWeyl_conj_rootDiagUnit (τ := Tag.E6) (K := K) (p := 3) hζ i x]
  obtain ⟨J, n, hnN, hJdef, -, hnJ, -, hW, hR, hΦ, -, -⟩ :=
    exists_lift_of_coverTorus (p := 3) (k := Tag.E6.rank) (L' := L')
      (R := ↥(adjointGroup Tag.E6 K)) (G := ModGL Tag.E6 K)
      (ψ := ψ₀) (A := A) (Φ := κ) (τ := τ) (T := T) (ι := ι) (s := s) (r := r) (S := S)
      (ι₀ := (adjointGroup Tag.E6 K).subtype)
      hψ₀ hker hZ hkerp (Subgroup.subtype_injective _) hκinj hτ hreal hTA hkerT hr
      (fun i a => ExcSplitRootGen.excRefl_excRefl (τ := Tag.E6) (p := 3) i.2 _)
      (fun i => TwE6ThreeRootGen.card_fix_excRefl_toAdd_mul_three (κ := κ) hκinj hVmem hV i.2)
      (fun i a => hH _ (TwE6ThreeRootGen.excRefl_sub_mem_hypE6 i.1
        (Multiplicative.toAdd (κ a))))
      (fun i => Subgroup.mem_map.mpr ⟨ExcSplitRootGen.excWeyl (K := K) i,
        ExcSplitRootGen.excWeyl_mem_excComp i, rfl⟩)
      (fun i => E6ThreeRootGen.isComponentOf_excComp_map_conj_e6 (g := g) hg hζo hζ hVmem hV i)
      (fun i => E6ThreeRootGen.dvd_card_excComp_map_conj_e6 (g := g) hg hζo i)
  have hmem : n ⟨γ, hγ⟩ ∈
      ⁅((ExcSplitRootGen.excComp (K := K) γ).map
            (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀,
          ((ExcSplitRootGen.excComp (K := K) γ).map
            (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀⁆ := by
    rw [← hJdef ⟨γ, hγ⟩]
    exact hnJ ⟨γ, hγ⟩
  exact ⟨n ⟨γ, hγ⟩, hnN ⟨γ, hγ⟩, hW ⟨γ, hγ⟩, hR ⟨γ, hγ⟩, hmem, hΦ ⟨γ, hγ⟩⟩

theorem ggE6Three_frameClass_of_tb
    {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L'] {ψ₀ : L' →* ↥(adjointGroup Tag.E6 K)}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 ↥(adjointGroup Tag.E6 K)
      ((hatAut Tag.E6 K).range : Set (MulAut ↥(adjointGroup Tag.E6 K))) L' ψ₀ A) :
    ∃ κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3), GGE6ThreeFrameA A κ ∧
      ∀ (y : ↥A) (J : Subgroup L'), y ≠ 1 → IsComponentOf J (fixSubgroup (y : MulAut L')) →
        GGE6ThreeClassA A κ y J (∃ m : ℕ, 1 ≤ m ∧
          GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) := by
  classical
  obtain ⟨hψ, hker, hperf, hA, hAI, h5, -, hsc⟩ := id hTB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hK : 4 ≤ Nat.card K := by
    have h1 : orderOf ζ ≤ Nat.card Kˣ := orderOf_le_card
    rw [hζo, Nat.card_units] at h1
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hK2 : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKcard]
  let e := TableBExc.recipeEquiv .E6 K
  let ψr : L' →* TableBExc.RecipeGroup .E6 K := e.symm.toMonoidHom.comp ψ₀
  have hψr : Function.Surjective ψr := e.symm.surjective.comp hψ
  have hkereq : ψr.ker = ψ₀.ker :=
    MonoidHom.ker_comp_of_injective ψ₀ e.symm.toMonoidHom e.symm.injective
  have hcard : Nat.card ψ₀.ker ∣ 3 := by
    rw [← hkereq]
    exact TableBExc.E6Three.card_ker_dvd_three_e6 (n := (n : ℕ)) hn hK2 hψr
      (by rw [hkereq]; exact hker) hperf
  have hkerp : ∀ z ∈ ψ₀.ker, z ^ 3 = 1 := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ₀.ker hz).trans hcard
    exact orderOf_dvd_iff_pow_eq_one.1 hz3
  have hodd : ∀ z ∈ ψ₀.ker, Odd (orderOf z) := by
    intro z hz
    have hz3 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ₀.ker hz).trans hcard
    rcases (Nat.dvd_prime Nat.prime_three).1 hz3 with h | h
    · rw [h]; exact ⟨0, rfl⟩
    · rw [h]; exact ⟨1, rfl⟩
  obtain ⟨g, κ, T, hg, hκinj, hκrange, hreal, hoddker, hTA, hH, hnorm⟩ :=
    E6ThreeRootGen.exists_frame_torus_E (ζ := ζ) hζ hζo hψ hker hperf hcard hA hAI h5 hsc
  have hkerT : ψ₀.ker ≤ T := fun z hz => hoddker z hz (hodd z hz)
  have hlift : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ →
      ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        GGTorusWeylElt 3 A n ∧ GGIsReflection 3 (ggConjAut A hn) ∧
        ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hn a)) =
          ExcSplitRootGen.excRefl (p := 3) γ (Multiplicative.toAdd (κ a)) :=
    fun γ hγ => ggTBJ_e6Three_exists_refl_lift hζ hζo hψ hker hkerp hg hκinj hκrange hreal
      hkerT hTA hH hγ
  refine ⟨κ, ⟨hκinj, hκrange, hlift, hnorm⟩, ?_⟩
  intro y J hy hJ
  have hJopen : CFSG.Open.IsComponentOf J (fixSubgroup (y : MulAut L')) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ
  let ay : Fin Tag.E6.rank → Kˣ := zetaVec ζ hζ (Multiplicative.toAdd (κ y))
  let ψ₁ : L' →* ModGL Tag.E6 K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ((adjointGroup Tag.E6 K).subtype.comp ψ₀)
  have hker₁ : ψ₁.ker ≤ Subgroup.center L' := by
    rw [show ψ₁ = (MulAut.conj g⁻¹).toMonoidHom.comp
        ((adjointGroup Tag.E6 K).subtype.comp ψ₀) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g⁻¹).injective,
      MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]
    exact hker
  have hsub₁ : ((adjointGroup Tag.E6 K).subtype.comp ψ₀).range =
      adjointGroup Tag.E6 K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, Subgroup.map_top,
      Subgroup.range_subtype]
  have hrange₁ : ψ₁.range = adjointGroup Tag.E6 K := by
    rw [show ψ₁ = (MulAut.conj g⁻¹).toMonoidHom.comp
        ((adjointGroup Tag.E6 K).subtype.comp ψ₀) from rfl,
      MonoidHom.range_comp, hsub₁]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (Subgroup.inv_mem _ hg))
  have hay : ∀ i, ay i ^ 3 = 1 := by
    intro i
    change (zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ y)) i) ^ 3 = 1
    rw [zetaVec_apply, ← pow_mul, pow_mul', hζ, one_pow]
  have hconj : ∀ (a : A) (l : L'),
      ψ₁ ((a : MulAut L') l) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))) * ψ₁ l *
          (rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd (κ a))))⁻¹ := by
    intro a l
    have h₁ : ψ₁ ((a : MulAut L') l) =
        g⁻¹ * ((ψ₀ ((a : MulAut L') l) : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) * g := by
      dsimp only [ψ₁, MonoidHom.comp_apply]
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rfl
    have h₂ : ψ₁ l =
        g⁻¹ * ((ψ₀ l : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) * g := by
      dsimp only [ψ₁, MonoidHom.comp_apply]
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rfl
    rw [h₁, h₂, hreal a l]
    group
  obtain ⟨i, hi⟩ := ggTBJ_class_fix (p := 3) Nat.prime_three hK (ψ := ψ₁) hker₁ hrange₁
    ay hay (y : MulAut L') (hconj y) hJopen
  have hfixJ : ∀ a : A, (∀ γ ∈ componentRoots (rootCharHom ay) i,
      ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ a) j = 0) →
      ∀ j ∈ J, (a : MulAut L') j = j := fun a hκa =>
    ggTBJ_fix_of_kernel (ψ := ψ₁) hker₁ i hi
      (Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩)
      (zetaVec (τ := Tag.E6) ζ hζ (Multiplicative.toAdd (κ a)))
      (fun γ hγ => (TwE6FixedA2Type.rootChar_zetaVec_eq_one_iff_dotZ3 hζo hζ
        (Multiplicative.toAdd (κ a)) γ).2 (by exact hκa γ hγ))
      (a : MulAut L') (hconj a)
  refine ⟨K, inferInstance, ζ, hζ, hζo, i, hfixJ, ?_, ?_⟩
  ·
    intro c hc
    obtain ⟨n, hn, hW, hR, hmem, hΦ⟩ :=
      e6c3i_exists_refl_lift_mem hζ hζo hψ hker hkerp hg hκinj hκrange hreal hkerT hTA hH hc.1.1
    have hstep : (ExcSplitRootGen.excComp (K := K) c).map
        (adjointGroup Tag.E6 K).subtype ≤ componentRootSpan K (rootCharHom ay) i :=
      e6c3i_excComp_map_le (χ := rootCharHom ay) hc
    have hle : ((ExcSplitRootGen.excComp (K := K) c).map
        (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀ ≤
        J ⊔ ψ₁.ker := by
      intro l hl
      rw [Subgroup.mem_comap] at hl
      obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hl
      have hmap : (adjointGroup Tag.E6 K).subtype u ∈ componentRootSpan K (rootCharHom ay) i :=
        hstep ⟨u, hu, rfl⟩
      rw [← hi] at hmap
      obtain ⟨j, hj, hjψ⟩ := Subgroup.mem_map.mp hmap
      have hψ₁l : ψ₁ l = (adjointGroup Tag.E6 K).subtype u := by
        change (MulAut.conj g⁻¹)
          ((adjointGroup Tag.E6 K).subtype (ψ₀ l)) = (adjointGroup Tag.E6 K).subtype u
        rw [← hueq]
        rw [← e6c3i_conj_subtype g hg u]
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      have hker : j⁻¹ * l ∈ ψ₁.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hjψ, hψ₁l, inv_mul_cancel]
      exact (Subgroup.mem_sup_of_normal_right (s := J) (t := ψ₁.ker)).mpr
        ⟨j, hj, j⁻¹ * l, hker, by group⟩
    have hmemJ : n ∈ J := by
      have hcomm : ⁅((ExcSplitRootGen.excComp (K := K) c).map
          (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀,
          ((ExcSplitRootGen.excComp (K := K) c).map
          (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀⁆ ≤ J := by
        calc ⁅((ExcSplitRootGen.excComp (K := K) c).map
              (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀,
              ((ExcSplitRootGen.excComp (K := K) c).map
              (MulAut.conj (⟨g, hg⟩ : adjointGroup Tag.E6 K)).toMonoidHom).comap ψ₀⁆
            ≤ ⁅J ⊔ ψ₁.ker, J ⊔ ψ₁.ker⁆ := Subgroup.commutator_mono hle hle
          _ ≤ ⁅J, J⁆ := e6c3i_commutator_sup_central_le hker₁
          _ = J := Subgroup.isPerfect_iff.1 ⟨hJ.2.2.1⟩
      exact hcomm hmem
    refine ⟨n, hn, hmemJ, hW, ?_⟩
    intro a
    exact hΦ a
  ·
    intro hD4
    exact ggTBJE6Three_d4Label_of_class hζ hζo hker₁ hrange₁ (Multiplicative.toAdd (κ y))
      (y : MulAut L') (hconj y) hJ i hi hD4

end CFSG.StandardType

end
