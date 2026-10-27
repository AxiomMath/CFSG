module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryShortModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISpBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CentralCover
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU

public section
namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.RCKK1IIISU

@[expose] def FixedSUBlockAt {X : Type} [Group X] (K J : Subgroup X) : Prop :=
  ∃ (n : ℕ) (π : SUG n →* K),
    Function.Surjective π ∧ π.ker ≤ Subgroup.center (SUG n) ∧
    ∃ (S : Set (GL (Fin n) SUF)) (e : Matrix (Fin n) (Fin n) SUF)
      (J₀ : Subgroup (SUG n)),
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      IsPrimIdemIn (Algebra.adjoin SUF (Units.val '' S)) e ∧
      formAdj SUσ.toRingHom (antidiag n) e = e ∧
      blockDegree (Algebra.adjoin SUF (Units.val '' S)) e < 2 ∧
      IsComponentOf J₀
      ⁅glBlockCentralizer (SU SUσ n).subtype S e,
        glBlockCentralizer (SU SUσ n).subtype S e⁆ ∧
      J₀.map π = J.subgroupOf K

theorem k2At_of_actual_unitary_block_model
    {m n : ℕ} (hm : 4 ≤ m) (hn : 4 ≤ n)
    {J V : Subgroup (SUG n)} {r : SUG n}
    (η : J ≃* SUG m) (ι : SUG m →* SUG n) (hι : Function.Injective ι)
    (hComp : ∀ j : J, ι (η j) = (j : SUG n))
    (E : (Fin m → SUF) →ₗ[SUF] (Fin n → SUF)) (hE : Function.Injective E)
    (W : Submodule SUF (Fin n → SUF))
    (hAct : ∀ g x, natRep (SU SUσ n) (ι g) (E x) = E (natRep (SU SUσ m) g x))
    (hFix : ∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ W, z = E x + w)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r)
    (hRank : (mat SUσ m (η ⟨r, hFour.2.1 hFour.1⟩) - 1).rank = 2) :
    K2At (⊤ : Subgroup (SUG n)) V r := by
  have hrJ : r ∈ J := hFour.2.1 hFour.1
  have hFour' := fourAt_map_mulEquiv η hrJ hFour
  have hCore' := coreCommAt_map_mulEquiv η hrJ hCore
  have hR : ι (η ⟨r, hrJ⟩) = r := hComp ⟨r, hrJ⟩
  have hV : ((V.subgroupOf J).map η.toMonoidHom).map ι = V := by
    rw [Subgroup.map_map]
    have hHom : ι.comp η.toMonoidHom = J.subtype := by
      apply MonoidHom.ext
      intro j
      exact hComp j
    rw [hHom, Subgroup.map_subgroupOf_eq_of_le hFour.2.1]
  have hK2 := k2At_of_unitary_linear_embedding hm hn ι hι E hE W hAct hFix hSplit
    hFour' hCore' hRank
  rwa [hV, hR] at hK2

theorem injective_comp_unitary_linear_block_of_central_ker
    {Q : Type} [Group Q] {m n : ℕ} (hn : 4 ≤ n) (hmn : m < n)
    (π : SUG n →* Q) (hker : π.ker ≤ Subgroup.center (SUG n))
    (ι : SUG m →* SUG n) (hι : Function.Injective ι)
    (E : (Fin m → SUF) →ₗ[SUF] (Fin n → SUF))
    (W : Submodule SUF (Fin n → SUF))
    (hFix : ∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w)
    (hSplit : ∀ z, ∃ x, ∃ w ∈ W, z = E x + w) :
    Function.Injective (π.comp ι) := by
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective E := by
      intro z
      obtain ⟨x, w, hw, hz⟩ := hSplit z
      rw [h w hw, add_zero] at hz
      exact ⟨x, hz.symm⟩
    have hd := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hd
    omega
  intro a b hab
  have hzker : ι (a * b⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv]
    change π (ι a) * (π (ι b))⁻¹ = 1
    change π (ι a) = π (ι b) at hab
    rw [hab, mul_inv_cancel]
  obtain ⟨c, hc⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_scalar_of_mem_center_SU
    rckSU_suF_card (by omega : 3 ≤ n)
    (by rintro ⟨h3, _⟩; omega) (hker hzker)
  have hScalar (x : Fin n → SUF) :
      natRep (SU SUσ n) (ι (a * b⁻¹)) x = (c : SUF) • x := by
    rw [natRep_apply, hc, Matrix.GeneralLinearGroup.coe_scalar]
    funext i
    simp [Matrix.mulVec, Matrix.scalar_apply, Pi.smul_apply, smul_eq_mul]
  have hcw : (c : SUF) • w = w := (hScalar w).symm.trans (hFix (a * b⁻¹) w hw)
  have hzero : ((c : SUF) - 1) • w = 0 := by
    rw [sub_smul, one_smul, hcw, sub_self]
  have hc1 : c = 1 := Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hw0))
  have hz1 : ι (a * b⁻¹) = 1 := by
    apply Subtype.ext
    rw [hc, hc1, map_one]
    rfl
  exact mul_inv_eq_one.mp (hι (hz1.trans (map_one ι).symm))

section Certificates

theorem exists_unitary_linear_block_model_at_two
    {n : ℕ} (S : Set (GL (Fin n) SUF))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) SUF}
    (he : IsPrimIdemIn (Algebra.adjoin SUF (Units.val '' S)) e)
    (hadj : formAdj SUσ.toRingHom (antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin SUF (Units.val '' S)) e < 2)
    {J : Subgroup (SUG n)}
    (hJ : IsComponentOf J ⁅glBlockCentralizer (SU SUσ n).subtype S e,
      glBlockCentralizer (SU SUσ n).subtype S e⁆) :
    ∃ (m : ℕ) (η : J ≃* SUG m) (ι : SUG m →* SUG n)
      (E : (Fin m → SUF) →ₗ[SUF] (Fin n → SUF)) (W : Submodule SUF (Fin n → SUF)),
      4 ≤ m ∧ 4 ≤ n ∧ Function.Injective ι ∧ (∀ j : J, ι (η j) = (j : SUG n)) ∧
      Function.Injective E ∧
      (∀ g x, natRep (SU SUσ n) (ι g) (E x) = E (natRep (SU SUσ m) g x)) ∧
      (∀ g w, w ∈ W → natRep (SU SUσ n) (ι g) w = w) ∧
      (∀ z, ∃ x, ∃ w ∈ W, z = E x + w) := by
  obtain ⟨m, ι, E, W, hgood, hi, hrange, hE, hIso, hAct, hFix, hSplit, hOrth⟩ :=
    exists_linearBlockModel_selfDual_PSU n 0 S hS he hadj hdeg hJ
  have hm : 4 ≤ m := by
    rcases hgood with ⟨hm3, hne⟩ | ⟨_, h4⟩
    · have hne3 : m ≠ 3 := by
        intro h
        exact hne ⟨h, by norm_num⟩
      omega
    · norm_num at h4
  have hn : 4 ≤ n := by
    have h := LinearMap.finrank_le_finrank_of_injective hE
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    exact hm.trans h
  let ι' : SUG m →* SUG n := ι
  have hi' : Function.Injective ι' := by
    intro a b h
    exact hi h
  have hrange' : ι'.range = J := by
    exact hrange
  let ιJ : SUG m →* J := ι'.codRestrict J (by
    intro g
    rw [← hrange']
    exact ⟨g, rfl⟩)
  have hsurj : Function.Surjective ιJ := by
    intro j
    have hj : (j : SUG n) ∈ ι'.range := by rw [hrange']; exact j.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hj
    exact ⟨g, Subtype.ext hg⟩
  have hinj : Function.Injective ιJ := fun x y h => hi' (congrArg Subtype.val h)
  let η : J ≃* SUG m := (MulEquiv.ofBijective ιJ ⟨hinj, hsurj⟩).symm
  refine ⟨m, η, ι', E, W, hm, hn, hi', ?_, hE, ?_, ?_, hSplit⟩
  · intro j
    change (ιJ (η j) : SUG n) = (j : SUG n)
    exact congrArg Subtype.val
      ((MulEquiv.ofBijective ιJ ⟨hinj, hsurj⟩).apply_symm_apply j)
  · intro g x
    simpa only [ι', natRep_apply] using hAct g x
  · intro g w hw
    simpa only [ι', natRep_apply] using hFix g w hw

theorem k2At_of_shortAt_selfDual_su_block
    {n : ℕ} (S : Set (GL (Fin n) SUF))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) SUF}
    (he : IsPrimIdemIn (Algebra.adjoin SUF (Units.val '' S)) e)
    (hadj : formAdj SUσ.toRingHom (antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin SUF (Units.val '' S)) e < 2)
    {J V : Subgroup (SUG n)} {r : SUG n}
    (hJ : IsComponentOf J ⁅glBlockCentralizer (SU SUσ n).subtype S e,
      glBlockCentralizer (SU SUσ n).subtype S e⁆)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At (⊤ : Subgroup (SUG n)) V r := by
  obtain ⟨m, η, ι, E, W, hm, hn, hi, hComp, hE, hAct, hFix, hSplit⟩ :=
    exists_unitary_linear_block_model_at_two S hS he hadj hdeg hJ
  obtain ⟨rJ, hrJ, hPos⟩ := hShort
  have hr1 : rJ ≠ 1 := by
    intro h
    apply hFour.2.2.2.2.1
    rw [← hrJ, h]
    rfl
  have hr2 : rJ ^ 2 = 1 := by
    apply Subtype.ext
    change (rJ : SUG n) ^ 2 = 1
    rw [hrJ]
    exact hFour.2.2.1.2 r hFour.1
  have hRank := rckSURank_of_shortAt_model hm η hr1 hr2 hPos
  apply k2At_of_actual_unitary_block_model hm hn η ι hi hComp E hE W hAct hFix hSplit hFour hCore
  have hSub : (⟨r, hFour.2.1 hFour.1⟩ : J) = rJ := Subtype.ext hrJ.symm
  simpa only [hSub] using hRank

theorem k2At_of_fixedSUBlockAt
    {X : Type} [Group X] [Finite X] {K J V : Subgroup X} {r : X}
    (hBlock : FixedSUBlockAt K J) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  by_cases hKJ : K = J
  · subst K
    exact k2At_self_of_coreCommAt hFour.1 hCore
  obtain ⟨n, π, hπ, hker, S, e, J₀, hS, he, hadj, hdeg, hJ₀, hImage⟩ := hBlock
  obtain ⟨m, η₀, ι, E, W, hm, hn, hi, hComp, hE, hAct, hFix, hSplit⟩ :=
    exists_unitary_linear_block_model_at_two S hS he hadj hdeg hJ₀
  have hmn : m < n := by
    have hle := LinearMap.finrank_le_finrank_of_injective hE
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hle
    have hne : m ≠ n := by
      intro heq
      subst m
      have hsurj : Function.Surjective ι := Finite.surjective_of_injective hi
      have hJtop : J₀ = ⊤ := by
        apply le_antisymm le_top
        intro g _
        obtain ⟨a, ha⟩ := hsurj g
        have hmem : ι a ∈ J₀ := by
          rw [← η₀.apply_symm_apply a, hComp]
          exact (η₀.symm a).2
        rwa [ha] at hmem
      have hJk : J.subgroupOf K = ⊤ := by
        rw [← hImage, hJtop, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπ]
      have hKJle : K ≤ J := by
        intro x hx
        have hmem : (⟨x, hx⟩ : K) ∈ J.subgroupOf K := by
          rw [hJk]
          exact Subgroup.mem_top _
        exact hmem
      exact hKJ (le_antisymm hKJle hJK)
    omega
  have hπι := injective_comp_unitary_linear_block_of_central_ker hn hmn π hker
    ι hi E W hFix hSplit
  have hInjective : Function.Injective (π.comp J₀.subtype) := by
    intro a b hab
    apply η₀.injective
    apply hπι
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, hComp] using hab
  have hrJ : r ∈ J := hFour.2.1 hFour.1
  have hrK : r ∈ K := hJK hrJ
  have hodd : Odd (Nat.card π.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU SUσ hker
  let πJ : J₀ →* J.subgroupOf K := (π.comp J₀.subtype).codRestrict
    (J.subgroupOf K) (fun j => by
      rw [← hImage]
      exact Subgroup.mem_map_of_mem π j.2)
  have hπJinj : Function.Injective πJ := by
    intro a b h
    exact hInjective (congrArg Subtype.val h)
  have hπJsurj : Function.Surjective πJ := by
    intro j
    have hj : (j : K) ∈ J₀.map π := by rw [hImage]; exact j.2
    obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hj
    exact ⟨⟨a, ha⟩, Subtype.ext heq⟩
  let eJ : J₀ ≃* J := (MulEquiv.ofBijective πJ ⟨hπJinj, hπJsurj⟩).trans
    (Subgroup.subgroupOfEquivOfLe hJK)
  let ξ : J ≃* J₀ := eJ.symm
  have hπe (j : J₀) : (π (j : SUG n) : X) = (eJ j : X) := by
    rfl
  have hHom : (π.comp J₀.subtype).comp ξ.toMonoidHom = Subgroup.inclusion hJK := by
    apply MonoidHom.ext
    intro j
    apply Subtype.ext
    exact (hπe (ξ j)).trans (congrArg Subtype.val (eJ.apply_symm_apply j))
  let V₀ : Subgroup (SUG n) := ((V.subgroupOf J).map ξ.toMonoidHom).map J₀.subtype
  let r₀ : J₀ := ξ ⟨r, hrJ⟩
  have hFour₀ : FourAt J₀ V₀ (r₀ : SUG n) :=
    fourAt_map_subtype (fourAt_map_mulEquiv ξ hrJ hFour)
  have hCore₀ : CoreCommAt J₀ V₀ (r₀ : SUG n) :=
    coreCommAt_map_subtype (coreCommAt_map_mulEquiv ξ hrJ hCore)
  have hShort₀ : ShortAt J₀ (r₀ : SUG n) := by
    obtain ⟨rJ, hr, hPos⟩ := hShort
    have hr' : rJ = ⟨r, hrJ⟩ := Subtype.ext hr
    refine ⟨r₀, rfl, ?_⟩
    simpa only [hr'] using rckPosShort_map_mulEquiv ξ hPos
  have hK2₀ := k2At_of_shortAt_selfDual_su_block S hS he hadj hdeg hJ₀ hFour₀ hCore₀ hShort₀
  have hπr : π (r₀ : SUG n) = ⟨r, hrK⟩ := by
    exact congrArg (fun f : J →* K => f ⟨r, hrJ⟩) hHom
  have hπV : V₀.map π = V.subgroupOf K := by
    change (((V.subgroupOf J).map ξ.toMonoidHom).map J₀.subtype).map π = V.subgroupOf K
    rw [Subgroup.map_map, Subgroup.map_map, hHom]
    ext k
    constructor
    · rintro ⟨v, hv, heq⟩
      change (k : X) ∈ V
      rw [← heq]
      exact hv
    · intro hk
      exact ⟨⟨k, hFour.2.1 hk⟩, hk, Subtype.ext rfl⟩
  have hK2 := k2At_map_of_odd_central_ker π hπ hker hodd
    (hFour₀.2.2.1.2 (r₀ : SUG n) hFour₀.1) hK2₀
  rw [hπr, hπV] at hK2
  apply k2At_of_mulEquiv (MulEquiv.refl K) hrK (hFour.2.1.trans hJK)
  simpa [K2At] using hK2

end Certificates
end CFSG.StandardType.RCKC1
