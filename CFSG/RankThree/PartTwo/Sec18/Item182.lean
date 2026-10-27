module

public import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.RankThree.PartTwo.Sec18.Item181
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

@[expose] def Gap182ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ H ∈ scriptH A M, ∀ X : Subgroup G, H ≤ X → X ≠ ⊤ → ∀ K J : Subgroup G,
      K ∈ oTwoComponentsIn X → J ∈ oTwoComponentsIn X → ¬ K ≤ M →
      Nonempty (inSubgroup perfectResidual H ⧸
        CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) →
      ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J →
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
        Sec4.IsExtOf (J ⧸ CFSG.pCore 2 J) CFSG.Blueprint.NativeSporadic.M22
          (Multiplicative (ZMod 3))) →
      K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ scriptH A M ∧ J ∈ thetaComponentsIn X

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inSubgroup_pCore_eq_pCoreOf (p : ℕ) (K : Subgroup G) :
    inSubgroup (CFSG.pCore p) K = CFSG.Open.pCoreOf p K := by
  rw [inSubgroup]
  rfl

omit [Finite G] in
theorem le_normalizer_inSubgroup_perfectResidual (H : Subgroup G) :
    H ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) :=
  Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

omit [Finite G] in
theorem subgroupOf_mem_scriptH₀ {A M X H : Subgroup G} (hAX : A ≤ X) (hHX : H ≤ X)
    (hH : H ∈ scriptH A M) :
    H.subgroupOf X ∈ scriptH₀ (A.subgroupOf X) ((X ⊓ M).subgroupOf X) := by
  rw [← map_mem_scriptH₀_iff X.subtype X.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hHX, Subgroup.map_subgroupOf_eq_of_le hAX,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hinf : H ⊓ (X ⊓ M) = H ⊓ M := by rw [← inf_assoc, inf_eq_left.mpr hHX]
  rw [mem_scriptH₀_iff, hinf]
  exact (mem_scriptH_iff_mem_scriptH₀.mp hH).1

theorem isSolvable_sup_of_le_normalizer {A T : Subgroup G} (hA : IsMulCommutative A)
    (hT : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) :
    Group.IsSolvable (A ⊔ T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTn : (T.subgroupOf (A ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hAT Subgroup.le_normalizer)
  have hTs : Group.IsSolvable (T.subgroupOf (A ⊔ T)) := by
    have : Group.IsNilpotent (T.subgroupOf (A ⊔ T)) :=
      (hT.comap_subtype (K := A ⊔ T)).isNilpotent
    infer_instance
  have hAs : Group.IsSolvable A := by
    have : IsMulCommutative A := hA
    infer_instance
  have hq : Group.IsSolvable ((A ⊔ T : Subgroup G) ⧸ T.subgroupOf (A ⊔ T)) := by
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (T.subgroupOf (A ⊔ T))).comp
      (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ T))) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hx : (x : G) ∈ ((A : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A T hAT]
      exact x.2
    obtain ⟨a, ha, t, ht, hat⟩ := hx
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨t, (le_sup_right : T ≤ A ⊔ T) ht⟩, Subgroup.mem_subgroupOf.mpr ht, ?_⟩
    apply Subtype.ext
    simpa using hat
  exact Group.isSolvable_of_subgroup_quotient (T.subgroupOf (A ⊔ T))

omit [Finite G] in
theorem mem_oTwoComponentsIn_of_le {X Y K : Subgroup G} (hK : K ∈ oTwoComponentsIn X)
    (hKY : K ≤ Y) (hsn : (K.subgroupOf Y).IsSubnormal) : K ∈ oTwoComponentsIn Y := by
  obtain ⟨hKX, ⟨hp, -, hq⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  set e : K.subgroupOf X ≃* K.subgroupOf Y :=
    (Subgroup.subgroupOfEquivOfLe hKX).trans (Subgroup.subgroupOfEquivOfLe hKY).symm
  refine mem_oTwoComponentsIn_iff.mpr ⟨hKY, ?_, hsn, ?_⟩
  · exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)) hq

theorem mem_scriptH_of_eq_sup {A M H X K : Subgroup G} (h : Sec18Std G A M)
    (hH : H ∈ scriptH A M) (hHX : H ≤ X) (hX : X ≠ ⊤) (hK : K ∈ oTwoComponentsIn X)
    (hKL : K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K) :
    K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ scriptH A M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  set L := inSubgroup perfectResidual H with hLdef
  set T := CFSG.Open.pCoreOf 2 (H ⊓ M) with hTdef
  set R := CFSG.Open.pCoreOf 2 K with hRdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hTH : T ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hTM : T ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hLK : L ≤ K := by rw [hKL]; exact le_sup_left
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    mem_normalizer_of_eq_sup hK hKL (hHX hx) (hHL hx)
  have hHR : H ≤ Subgroup.normalizer (R : Set G) :=
    hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hRM : R ≤ M := le_of_le_normalizer_of_isPGroup_two h hR2 (hAH.trans hHR)
  set H₁ := K ⊔ A ⊔ T with hH₁def
  have hHeq : H = L ⊔ A ⊔ T := hH₀.1
  have hHH₁ : H ≤ H₁ := by
    rw [hHeq]
    exact sup_le (sup_le (hLK.trans (le_sup_left.trans le_sup_left)) (le_sup_right.trans
      le_sup_left)) le_sup_right
  have hH₁eq : H₁ = H ⊔ R := by
    apply le_antisymm
    · rw [hH₁def, hKL]
      exact sup_le (sup_le (sup_le (hLH.trans le_sup_left) le_sup_right)
        (hAH.trans le_sup_left)) (hTH.trans le_sup_left)
    · exact sup_le hHH₁ ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans
        (le_sup_left.trans le_sup_left))
  have hH₁X : H₁ ≤ X := by
    rw [hH₁eq]
    exact sup_le hHX ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKX)
  have hH₁K : H₁ ≤ Subgroup.normalizer (K : Set G) := by
    rw [hH₁eq]
    exact sup_le hHK ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer)
  have hKH₁ : K ≤ H₁ := le_sup_left.trans le_sup_left
  have hKn : (K.subgroupOf H₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH₁).mpr hH₁K
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    fun a ha => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
      ⟨hAH ha, sec18Std_le h ha⟩
  have hATs := isSolvable_sup_of_le_normalizer hA.1.1 hT2 hAT
  have hq : Group.IsSolvable (H₁ ⧸ K.subgroupOf H₁) := by
    refine Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (K.subgroupOf H₁)).comp
      (Subgroup.inclusion (show A ⊔ T ≤ H₁ from sup_le (le_sup_right.trans le_sup_left)
        le_sup_right))) ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hx : (x : G) ∈ ((K : Set G) * ((A ⊔ T : Subgroup G) : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K (A ⊔ T)
        (sup_le (hAH.trans hHK) (hTH.trans hHK)), show K ⊔ (A ⊔ T) = H₁ by
          rw [hH₁def, sup_assoc]]
      exact x.2
    obtain ⟨k, hk, y, hy, hky⟩ := hx
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨y⁻¹ * k * y, ?_⟩, ?_, ?_⟩
    · have hyH₁ : y ∈ H₁ := (show A ⊔ T ≤ H₁ from sup_le (le_sup_right.trans le_sup_left)
        le_sup_right) hy
      exact H₁.mul_mem (H₁.mul_mem (H₁.inv_mem hyH₁) (hKH₁ hk)) hyH₁
    · rw [Subgroup.mem_subgroupOf]
      have hyN : y⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        inv_mem ((sup_le (hAH.trans hHK) (hTH.trans hHK)) hy)
      have := (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
      simpa [mul_assoc] using this
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      rw [← hky]
      group
  have hres : inSubgroup perfectResidual H₁ = K :=
    le_antisymm (inSubgroup_perfectResidual_le_of_isSolvable hKH₁ hq)
      (le_inSubgroup_perfectResidual (commutator_eq_of_mem_oTwoComponentsIn hK) hKH₁)
  have hTR2 : IsPGroup 2 (T ⊔ R : Subgroup G) := hT2.to_sup_of_normal_right' hR2 (hTH.trans hHR)
  have hH₁M : H₁ ⊓ M ≤ Subgroup.normalizer ((T ⊔ R : Subgroup G) : Set G) := by
    intro x hx
    have hx' : x ∈ ((H : Set G) * (R : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H R hHR, ← hH₁eq]
      exact hx.1
    obtain ⟨y, hy, r, hr, rfl⟩ := hx'
    have hyM : y ∈ M := by
      have := M.mul_mem hx.2 (M.inv_mem (hRM hr))
      simpa using this
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.inf_normalizer_le_normalizer_sup T R
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hy, hyM⟩, hHR hy⟩
    · exact Subgroup.le_normalizer ((le_sup_right : R ≤ T ⊔ R) hr)
  have hTRle : T ⊔ R ≤ CFSG.Open.pCoreOf 2 (H₁ ⊓ M) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (sup_le (le_sup_right) (hKH₁.trans' (CFSG.LieType.BorelTits.pCoreOf_le 2 K)))
        (sup_le hTM hRM)) hH₁M hTR2
  have hTO : T ≤ CFSG.Open.pCoreOf 2 (H₁ ⊓ M) := le_sup_left.trans hTRle
  refine ⟨fun htop => hX (top_le_iff.mp (htop ▸ hH₁X)), ?_, ?_, ?_⟩
  ·
    rw [hres]
    apply le_antisymm
    · exact sup_le le_sup_left (hTO.trans le_sup_right)
    · exact sup_le le_sup_left ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  ·
    rw [hres]
    exact mem_oTwoComponentsIn_of_le hK hKH₁ hKn.isSubnormal
  ·
    intro heq
    apply hH₀.2.2
    refine le_antisymm (pCoreOf_le_pCoreOf_inf h hAH) ?_
    have h1 : T ≤ CFSG.Open.pCoreOf 2 H₁ := heq ▸ hTO
    have h2 : CFSG.Open.pCoreOf 2 H₁ ⊓ H ≤ CFSG.Open.pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁ (hHH₁ hx),
            Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁).to_le inf_le_left)
    exact (le_inf h1 hTH).trans h2

theorem rank3II_18_2_of (h444 : Sec4.Item4_44_3) (hgap : Gap182ii) : Item182 := by
  intro G _ _ A M h H hH X hHX hX
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAX : A ≤ X := hAH.trans hHX
  have hXM : X ⊓ M ≠ X := by
    intro heq
    apply inf_ne_of_mem_scriptH₀ hH₀
    exact inf_eq_left.mpr (hHX.trans (inf_eq_left.mp heq))
  have hctx := ctx444_subgroupOf h hAX hX hXM
  obtain ⟨K', hK', hK'M, hcase⟩ :=
    h444 X _ _ hctx (H.subgroupOf X) (subgroupOf_mem_scriptH₀ hAX hHX hH)
  set K := K'.map X.subtype with hKdef
  have hK : K ∈ oTwoComponentsIn X := ⟨K', hK', rfl⟩
  have hKM : ¬ K ≤ M := by
    intro hle
    apply hK'M
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hle (Subgroup.mem_map_of_mem X.subtype hx)⟩
  have hres : (inSubgroup perfectResidual (H.subgroupOf X)).map X.subtype =
      inSubgroup perfectResidual H := by
    rw [← inSubgroup_perfectResidual_map X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hHX]
  have hO2 : (inSubgroup (CFSG.pCore 2) K').map X.subtype = CFSG.Open.pCoreOf 2 K := by
    rw [inSubgroup_pCore_eq_pCoreOf, ← pCoreOf_map X.subtype X.subtype_injective]
  rcases hcase with hi | ⟨hL34, J', hJ', hLX, hK34, hJ⟩
  ·
    have hKL : K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K := by
      conv_lhs => rw [hKdef, hi]
      rw [Subgroup.map_sup, hres, hO2]
    exact ⟨K, hK, hKM, mem_scriptH_of_eq_sup h hH hHX hX hK hKL, Or.inl hKL⟩
  ·
    set J := J'.map X.subtype with hJdef
    have hJm : J ∈ oTwoComponentsIn X := ⟨J', hJ', rfl⟩
    have hiso : ∀ (Y : Type) [Group Y], ∀ W : Subgroup X,
        Nonempty (W ⧸ CFSG.pCore 2 W ≃* Y) →
          Nonempty ((W.map X.subtype : Subgroup G) ⧸ CFSG.pCore 2 (W.map X.subtype) ≃* Y) := by
      intro Y _ W ⟨φ⟩
      set e : W ≃* (W.map X.subtype : Subgroup G) := W.equivMapOfInjective _ X.subtype_injective
      exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).symm.trans φ⟩
    have hL34' : Nonempty (inSubgroup perfectResidual H ⧸
        CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) := by
      have := hiso _ _ hL34
      rwa [hres] at this
    have hK34' := hiso _ K' hK34
    have hLX' : ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J := by
      have h1 := congrArg (Subgroup.map X.subtype) hLX
      rwa [Subgroup.map_commutator, hres, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.map_sup] at h1
    have hJ'' : (∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
          Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
        Sec4.IsExtOf (J ⧸ CFSG.pCore 2 J) CFSG.Blueprint.NativeSporadic.M22
          (Multiplicative (ZMod 3)) := by
      rcases hJ with ⟨n, hn, hJn⟩ | ⟨N, hN, hNiso, hq⟩
      · exact Or.inl ⟨n, hn, hiso _ J' hJn⟩
      · right
        set e : J' ≃* J := J'.equivMapOfInjective _ X.subtype_injective
        set φ := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
        have hN' : (N.map φ.toMonoidHom).Normal := hN.map _ φ.surjective
        exact ⟨N.map φ.toMonoidHom, hN',
          ⟨(N.equivMapOfInjective _ φ.injective).symm.trans hNiso.some⟩,
          ⟨(QuotientGroup.congr N (N.map φ.toMonoidHom) φ rfl).symm.trans hq.some⟩⟩
    obtain ⟨hmem, hJL⟩ := hgap G A M h H hH X hHX hX K J hK hJm hKM hL34' hLX' hK34' hJ''
    exact ⟨K, hK, hKM, hmem, Or.inr ⟨hL34', J, hJL, hLX', hK34', hJ''⟩⟩

end CFSG.RankThree.PartTwo.Sec18
