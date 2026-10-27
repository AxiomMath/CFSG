module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatOutput
public import CFSG.Quasithin.Background.PushS3Setting
public import CFSG.Quasithin.Background.C118Partner
public import CFSG.Quasithin.MS93.PUEquiv
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.MS93.S51

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Campbell
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

section Weak

variable {H : Type*} [Group H] [Finite H] {k : Type*} [Field k] [Finite k] [CharP k 2]
variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem bsHyp (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H))
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowTwoOf (elemBaumannIn 2 R) (baumannOvergroup R) ∧
      (baumannOvergroup R).IsSubnormal ∧
      CharTwo (baumannOvergroup R) ∧
      baumannOvergroup R ⊔ R = ⊤ ∧
      (CFSG.pCore 2 (baumannOvergroup R)).map (baumannOvergroup R).subtype =
        CFSG.pCore 2 H ⊓ baumannOvergroup R ∧
      CFSG.pCore 2 H ⊓ baumannOvergroup R = CFSG.pCore 2 H ⊓ elemBaumannIn 2 R ∧
      (ρ.ker.subgroupOf (baumannOvergroup R)).map
          (QuotientGroup.mk' (CFSG.pCore 2 (baumannOvergroup R))) =
        frattini (baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R)) ∧
      (∃ e : ((baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R)) ⧸
            frattini (baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R))) ≃*
          Matrix.SpecialLinearGroup (Fin 2) k,
        ∀ x : baumannOvergroup R,
          slPerm k (e (QuotientGroup.mk (QuotientGroup.mk x))) =
            ((ρ (x : H) : Gamma k) : Equiv.Perm (Fin 2 → k))) := by
  classical
  have hVH := h.not_le_centralizer hJ
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hQn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  obtain ⟨hHLR, -, -, -, -, hfr, -⟩ :=
    minimal_parabolic_reduced_module_Frattini_kernel_production h.sylow h.nonnormal h.le_M h.M_lt
      h.M_max h.reduced hVH
  obtain ⟨ℓ, hsyl, -, -, -, hρH₀, -⟩ := h.Baumann_Sylow hJ
  have hRQ : R ⊓ ρ.ker = CFSG.pCore 2 H := h.inf_ker_eq hVH
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set S : Subgroup H := elemBaumannIn 2 R with hSdef
  set Q : Subgroup H := CFSG.pCore 2 H with hQdef
  set H₀ : Subgroup H := baumannOvergroup R with hH₀def
  have hρH₀' : H₀.map ρ = slGamma k := hρH₀
  have hSR : S ≤ R := elemBaumannIn_le 2 R
  have hLH₀ : L ≤ H₀ := le_sup_left
  have hSH₀ : S ≤ H₀ := le_sup_right
  have hQker : Q ≤ ρ.ker := fun x hx => (hRQ ▸ hx : x ∈ R ⊓ ρ.ker).2
  have hL2 : ∀ x : H ⧸ L, ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    intro x
    obtain ⟨h', rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := h') trivial
    exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hn⟩
  have h1 : IsSylowTwoOf S H₀ := hsyl
  have h2 : H₀.IsSubnormal := isSubnormal_of_pGroup_quotient L (hL2 : IsPGroup 2 (H ⧸ L)) hLH₀
  have h3 : CharTwo H₀ := hchar.of_isSubnormal le_top h2.subgroupOf
  have h4 : H₀ ⊔ R = ⊤ := by
    have : L ⊔ R ≤ H₀ ⊔ R := sup_le_sup_right hLH₀ R
    rw [hHLR] at this
    exact top_le_iff.mp this
  have hQ₀le : CFSG.Open.pCoreOf 2 H₀ ≤ ρ.ker :=
    le_ker_of_normal_isPGroup hρH₀'
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H₀)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H₀)
  have hQ₀S : CFSG.Open.pCoreOf 2 H₀ ≤ S := h1.pCoreOf_le
  have hSker : S ⊓ ρ.ker ≤ Q := fun x hx => hRQ ▸ (⟨hSR hx.1, hx.2⟩ : x ∈ R ⊓ ρ.ker)
  have hQ₀Q : CFSG.Open.pCoreOf 2 H₀ ≤ Q := fun x hx => hSker ⟨hQ₀S hx, hQ₀le hx⟩
  have hQH₀ : Q ⊓ H₀ ≤ CFSG.Open.pCoreOf 2 H₀ := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (Q ⊓ H₀) H₀
      inf_le_right ?_ ((CFSG.pCore_isPGroup (p := 2) (G := H)).to_le inf_le_left)
    refine (BlueprintB2.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxH⟩
      exact ⟨hQn.conj_mem x hxQ g, H₀.mul_mem (H₀.mul_mem hg hxH) (H₀.inv_mem hg)⟩
    · rintro ⟨hxQ, hxH⟩
      refine ⟨by simpa [mul_assoc] using hQn.conj_mem _ hxQ g⁻¹, ?_⟩
      simpa [mul_assoc] using H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hg) hxH) hg
  have hQ₀eq : CFSG.Open.pCoreOf 2 H₀ = Q ⊓ H₀ :=
    le_antisymm (le_inf hQ₀Q (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H₀)) hQH₀
  have hQSeq : Q ⊓ H₀ = Q ⊓ S :=
    le_antisymm (le_inf inf_le_left (hQH₀.trans hQ₀S)) (inf_le_inf_left Q hSH₀)
  have hQ₀map : (CFSG.pCore 2 ↥H₀).map H₀.subtype = Q ⊓ H₀ := by
    rw [← pCoreOf_eq 2 H₀]; exact hQ₀eq
  have hmem₀ : ∀ x : H₀, ρ (x : H) ∈ slGamma k := fun x =>
    hρH₀' ▸ Subgroup.mem_map_of_mem ρ x.2
  let ρ₀ : H₀ →* slGamma k := (ρ.comp H₀.subtype).codRestrict (slGamma k) hmem₀
  have hρ₀ : ∀ x : H₀, ((ρ₀ x : slGamma k) : Gamma k) = ρ (x : H) := fun x => rfl
  have hρ₀surj : Function.Surjective ρ₀ := by
    intro g
    have hg : (g : Gamma k) ∈ H₀.map ρ := by
      rw [hρH₀']
      exact g.2
    obtain ⟨x, hx, hxg⟩ := hg
    exact ⟨⟨x, hx⟩, Subtype.ext hxg⟩
  have hker₀ : ρ₀.ker = ρ.ker.subgroupOf H₀ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact congrArg (fun y : slGamma k => (y : Gamma k)) hx
    · intro hx
      exact Subtype.ext hx
  have hLp₀ : IsPGroup 2 (H₀ ⧸ L.subgroupOf H₀) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := exists_pow_mem_oddOrderSubgroup (H := (⊤ : Subgroup H)) (h := (y : H)) trivial
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hn)
  have hQ₁ : ∀ x : H₀, x ∈ CFSG.pCore 2 ↥H₀ ↔ (x : H) ∈ Q := by
    intro x
    have hiff : (x : H) ∈ (CFSG.pCore 2 ↥H₀).map H₀.subtype ↔ (x : H) ∈ Q ⊓ H₀ := by
      rw [hQ₀map]
    constructor
    · intro hx
      exact (hiff.mp ⟨x, hx, rfl⟩).1
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hiff.mpr ⟨hx, x.2⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
  have hQD : CFSG.pCore 2 ↥H₀ ≤ ρ₀.ker := by
    intro x hx
    rw [hker₀, Subgroup.mem_subgroupOf]
    exact hQker ((hQ₁ x).mp hx)
  have hNfr : ρ.ker.map (QuotientGroup.mk' Q) ≤ frattini (H ⧸ Q) := by
    rw [← hfr]
    exact Subgroup.map_mono h.ker_le_kerIn
  have hfrSub := frattini_image_in_odd_residual_quotient_sub L H₀ hLH₀ hL2 hNfr
    (CFSG.pCore 2 ↥H₀) hQ₁
  have hnormK : ((H₀ ⊓ ρ.ker).subgroupOf H₀).Normal := by
    have hK : (H₀ ⊓ ρ.ker).subgroupOf H₀ = ρ₀.ker := by
      rw [hker₀]
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hK]
    infer_instance
  have h1' : IsSylowIn 2 S H₀ := h1
  have hSylInf : IsSylowIn 2 (S ⊓ (H₀ ⊓ ρ.ker)) (H₀ ⊓ ρ.ker) :=
    h1'.inf_normal inf_le_left hnormK
  have hSylEq : S ⊓ (H₀ ⊓ ρ.ker) = Q ⊓ H₀ := by
    ext x
    constructor
    · rintro ⟨hxS, -, hxk⟩
      exact ⟨hSker ⟨hxS, hxk⟩, hSH₀ hxS⟩
    · rintro ⟨hxQ, hxH⟩
      have hxS : x ∈ S := (hQSeq ▸ (⟨hxQ, hxH⟩ : x ∈ Q ⊓ H₀) : x ∈ Q ⊓ S).2
      exact ⟨hxS, hxH, hQker hxQ⟩
  rw [hSylEq] at hSylInf
  have hQsyl : ¬ 2 ∣ ((CFSG.pCore 2 ↥H₀).subgroupOf ρ₀.ker).index := by
    have hmapker : ρ₀.ker.map H₀.subtype = H₀ ⊓ ρ.ker := by
      rw [hker₀]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, Subgroup.mem_subgroupOf.mp hy⟩
      · rintro ⟨hxH, hxk⟩
        exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxk, rfl⟩
    have := hSylInf.not_dvd_relIndex
    rw [← hQ₀map, ← hmapker,
      Subgroup.relIndex_map_map_of_injective _ _ H₀.subtype_injective] at this
    exact this
  obtain ⟨hfrat, e, he⟩ := action_kernel_is_frattini (p := 2) ρ₀ hρ₀surj (L.subgroupOf H₀)
    (CFSG.pCore 2 ↥H₀) hLp₀ hQD hQsyl (by rw [hker₀]; exact hfrSub) frattini_slGamma_eq_bot
  refine ⟨h1, h2, h3, h4, hQ₀map, hQSeq, ?_, ?_⟩
  · rw [← hker₀]
    exact hfrat
  · refine ⟨e.trans (slGammaEquiv k).symm, fun x => ?_⟩
    have hx := he x
    show slPerm k ((slGammaEquiv k).symm (e (QuotientGroup.mk (QuotientGroup.mk x)))) = _
    rw [hx]
    have hh := (slGammaEquiv k).apply_symm_apply (ρ₀ x)
    have := congrArg (fun y : slGamma k => ((y : Gamma k) : Equiv.Perm (Fin 2 → k))) hh
    rw [← slGammaEquiv_apply]
    exact this

theorem wholeCenter (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H))
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowTwoOf (elemBaumannIn 2 R) (baumannOvergroup R) ∧ CharTwo (baumannOvergroup R) ∧
      (baumannOvergroup R).map ρ = slGamma k ∧
      (ρ.ker.subgroupOf (baumannOvergroup R)).map
          (QuotientGroup.mk' (CFSG.pCore 2 (baumannOvergroup R))) =
        frattini (baumannOvergroup R ⧸ CFSG.pCore 2 (baumannOvergroup R)) ∧
      elemThompsonIn 2 (elemBaumannIn 2 R) = elemThompsonIn 2 R ∧
      IsSeed (h.actualSylow hJ) (h.actualRho hJ) (V.subgroupOf (baumannOvergroup R))
        (h.actualPsi hJ) ∧
      Ecore (baumannOvergroup R) = V.subgroupOf (baumannOvergroup R) ⊔
        (Ecore (baumannOvergroup R) ⊓ Subgroup.center (baumannOvergroup R)) ∧
      (∃ ψE : Ecore (baumannOvergroup R) →* Multiplicative (Fin 2 → k), Function.Surjective ψE ∧
        (∀ (g : baumannOvergroup R) (e e' : Ecore (baumannOvergroup R)),
          (e' : baumannOvergroup R) = g * e * g⁻¹ →
          Multiplicative.toAdd (ψE e') =
            (h.actualRho hJ g : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψE e))) ∧
        ψE.ker = (Ecore (baumannOvergroup R) ⊓ Subgroup.center (baumannOvergroup R)).subgroupOf
          (Ecore (baumannOvergroup R)) ∧
        ∀ (x : V.subgroupOf (baumannOvergroup R)) (e : Ecore (baumannOvergroup R)),
          (e : baumannOvergroup R) = x → ψE e = h.actualPsi hJ x) ∧
      (Kodd (baumannOvergroup R)).map (baumannOvergroup R).subtype =
        oddOrderSubgroup (⊤ : Subgroup H) ∧
      Vmod (baumannOvergroup R) =
        ⁅V.subgroupOf (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ := by
  classical
  have hVn : V.Normal := h.normal_V
  have hLn : (oddOrderSubgroup (⊤ : Subgroup H)).Normal := h.normal_L
  have hVH := h.not_le_centralizer hJ
  obtain ⟨hHLR, -, hQC, -, -, -, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production
    h.sylow h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  obtain ⟨h1, h2, h3, h4, hQ₀map, hQSeq, hfrat, -⟩ :=
    bsHyp h hchar hJ
  obtain ⟨ℓ, hsyl, -, hJρ, -, hρH₀, -, hcomm, -⟩ := h.Baumann_Sylow hJ
  have hRQ : R ⊓ ρ.ker = CFSG.pCore 2 H := h.inf_ker_eq hVH
  set L : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H) with hLdef
  set S : Subgroup H := elemBaumannIn 2 R with hSdef
  set Q : Subgroup H := CFSG.pCore 2 H with hQdef
  set H₀ : Subgroup H := baumannOvergroup R with hH₀def
  have hSR : S ≤ R := elemBaumannIn_le 2 R
  have hLH₀ : L ≤ H₀ := le_sup_left
  have hSH₀ : S ≤ H₀ := le_sup_right
  have hVH₀ : V ≤ H₀ := h.V_le_baumannOvergroup hJ
  have hQker : Q ≤ ρ.ker := fun x hx => (hRQ ▸ hx : x ∈ R ⊓ ρ.ker).2
  have hJS : elemThompsonIn 2 R ≤ S := elemThompsonIn_le_elemBaumannIn 2 R
  have hJeq : elemThompsonIn 2 S = elemThompsonIn 2 R := elemThompsonIn_eq_of_le 2 hJS hSR
  have hQ₁ : ∀ x : H₀, x ∈ CFSG.pCore 2 ↥H₀ ↔ (x : H) ∈ Q := by
    intro x
    have hiff : (x : H) ∈ (CFSG.pCore 2 ↥H₀).map H₀.subtype ↔ (x : H) ∈ Q ⊓ H₀ := by
      rw [hQ₀map]
    constructor
    · intro hx
      exact (hiff.mp ⟨x, hx, rfl⟩).1
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hiff.mpr ⟨hx, x.2⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by
    have := h.reduced.2.2.1.2 (v : H) v.2
    apply Subtype.ext
    simpa using this⟩
  have hVQ : V ≤ Q := le_sSup ⟨hVn, hV2⟩
  have hVE : V.subgroupOf H₀ ≤ Ecore H₀ := by
    intro x hx
    have hxV : (x : H) ∈ V := hx
    rw [Ecore, mem_centerTorsion_iff]
    refine ⟨(hQ₁ x).mpr (hVQ hxV), fun q hq => ?_, ?_⟩
    · have hqQ : (q : H) ∈ Q := (hQ₁ q).mp hq
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hQC hqQ) (x : H) hxV).symm
    · exact Subtype.ext (by simpa using h.reduced.2.2.1.2 (x : H) hxV)
  have hρH₀' : H₀.map ρ = slGamma k := hρH₀
  have hmem := h.rho_mem_baumannOvergroup hJ
  have hseed : IsSeed (h.actualSylow hJ) (h.actualRho hJ) (V.subgroupOf H₀) (h.actualPsi hJ) := by
    refine
      { card_k := card_eq_two_pow (k := k)
        surj := restrictSL_surjective ρ H₀ hmem hρH₀'
        core_le := ?_
        frattini_le := ?_
        normal := inferInstance
        le_E := hVE
        ψ_surj := h.φ_surj.comp (Subgroup.subgroupOfEquivOfLe hVH₀).surjective
        ψ_equiv := ?_
        ψ_ker := ?_
        not_le := ?_ }
    · rw [IsNatQuotSetting.ker_actualRho]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hQker ((hQ₁ x).mp hx))
    · rw [IsNatQuotSetting.ker_actualRho]
      exact hfrat.le
    · intro g x x' hx
      have := h.φ_equiv (g : H) ⟨((x : H₀) : H), x.2⟩ ⟨((x' : H₀) : H), x'.2⟩
        (congrArg Subtype.val hx)
      show Multiplicative.toAdd (φ ⟨((x' : H₀) : H), x'.2⟩) =
        (h.actualRho hJ g : Matrix (Fin 2) (Fin 2) k).mulVec
          (Multiplicative.toAdd (φ ⟨((x : H₀) : H), x.2⟩))
      rw [this]
      exact restrictSL_apply_smul ρ H₀ hmem g _
    · ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have hker : (⟨((x : H₀) : H), x.2⟩ : V) ∈ φ.ker := hx
        rw [h.φ_ker, Subgroup.mem_subgroupOf] at hker
        have hxE := h.inf_centralizer_le_elemCenterIn hJ ⟨x.2, hker⟩
        refine ⟨x.2, Subgroup.mem_center_iff.mpr ?_⟩
        have hLc : L ≤ Subgroup.centralizer ({((x : H₀) : H)} : Set H) := by
          intro l hl
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          exact (Subgroup.mem_centralizer_iff.mp hker l hl).symm
        have hSc : S ≤ Subgroup.centralizer ({((x : H₀) : H)} : Set H) := by
          intro s hs
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          exact (mem_elemBaumannIn_iff.mp hs).2 _ hxE
        have hH₀c : H₀ ≤ Subgroup.centralizer ({((x : H₀) : H)} : Set H) := sup_le hLc hSc
        intro g
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hH₀c g.2) _ rfl).symm)
      · intro hx
        have hxc := Subgroup.mem_center_iff.mp hx.2
        show φ ⟨((x : H₀) : H), x.2⟩ = 1
        have : (⟨((x : H₀) : H), x.2⟩ : V) ∈ φ.ker := by
          rw [h.φ_ker, Subgroup.mem_subgroupOf]
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          exact congrArg Subtype.val (hxc ⟨l, hLH₀ hl⟩)
        exact this
    · intro hle
      have hS₀ : ((h.actualSylow hJ : Sylow 2 ↥H₀) : Subgroup ↥H₀) = S.subgroupOf H₀ :=
        h.coe_actualSylow hJ
      rw [hS₀] at hle
      have hJmap : (thompsonJ (S.subgroupOf H₀)).map H₀.subtype = elemThompsonIn 2 R := by
        have hbridge : thompsonJ (S.subgroupOf H₀) = elemThompsonIn 2 (S.subgroupOf H₀) :=
          (elemThompson_map_subtype_eq_thompsonJ (S.subgroupOf H₀)).symm
        rw [hbridge, ← elemThompsonIn_map_of_injective 2 H₀.subtype H₀.subtype_injective,
          Subgroup.map_subgroupOf_eq_of_le hSH₀, hJeq]
      have hJQ : elemThompsonIn 2 R ≤ Q := by
        rw [← hJmap]
        intro y hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact ((hQ₁ z).mp (hle hz))
      have hbot : (elemThompsonIn 2 R).map ρ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact fun y hy => hQker (hJQ hy)
      rw [hJρ] at hbot
      have hcard := card_rootGamma (k := k) ℓ
      rw [hbot, Subgroup.card_bot] at hcard
      have : 1 < Nat.card k := Finite.one_lt_card
      omega
  obtain ⟨hEeq, ⟨ψE, hψEs, hψEq, hψEk, hψEx⟩, -⟩ :=
    hseed.natural_seed_exhausts_elementary_core_center
  have hKodd : (Kodd H₀).map H₀.subtype = L := by
    have hLclosure : L = Subgroup.closure {x : H | Nat.Coprime (orderOf x) 2} := by
      rw [hLdef, oddOrderSubgroup]
      congr 1
      ext x
      simp [Nat.coprime_two_right]
    have hset : (H₀.subtype '' {x : H₀ | x ∈ (⊤ : Subgroup H₀) ∧ (orderOf x).Coprime 2}) =
        {x : H | Nat.Coprime (orderOf x) 2} := by
      ext y
      constructor
      · rintro ⟨x, ⟨-, hx⟩, rfl⟩
        simpa [Subgroup.orderOf_coe] using hx
      · intro hy
        have hyL : y ∈ L := by
          rw [hLclosure]
          exact Subgroup.subset_closure hy
        refine ⟨⟨y, hLH₀ hyL⟩, ⟨trivial, ?_⟩, rfl⟩
        simpa [Subgroup.orderOf_coe] using hy
    unfold Kodd pPrimeGen
    rw [MonoidHom.map_closure, hset, ← hLclosure]
  have hVmod : Vmod H₀ = ⁅V.subgroupOf H₀, Kodd H₀⁆ := by
    apply le_antisymm
    · unfold Vmod
      rw [hEeq]
      refine commutator_sup_of_commute (fun x _ y hy => ?_) (fun y hy w _ => ?_)
      · exact (Subgroup.mem_center_iff.mp hy.2 x)
      · exact (Subgroup.mem_center_iff.mp hy.2 w).symm
    · exact Subgroup.commutator_mono hVE le_rfl
  refine ⟨h1, h3, hρH₀', hfrat, hJeq, hseed, hEeq, ⟨ψE, hψEs, hψEq, hψEk, ?_⟩, hKodd, hVmod⟩
  intro x e hex
  have := hψEx x
  rw [← this]
  congr 1
  exact Subtype.ext hex

theorem campbellOutput (h : IsNatQuotSetting R M V ρ φ)
    (hchar : CharTwo (⊤ : Subgroup H))
    (h10 : NoCharNormal (elemBaumannIn 2 R) (baumannOvergroup R))
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    IsSylowTwoOf (elemBaumannIn 2 R) (baumannOvergroup R) ∧ CharTwo (baumannOvergroup R) ∧
      (baumannOvergroup R).map ρ = slGamma k ∧
      Vmod (baumannOvergroup R) =
        ⁅V.subgroupOf (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ ∧
      (∃ α : (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) ≃*
            (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R),
        aimg ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)) α (Vmod (baumannOvergroup R)) ⊓
            CFSG.pCore 2 (baumannOvergroup R) =
          aimg ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)) α
            (Vmod (baumannOvergroup R) ⊓ Subgroup.centralizer
              (((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) :
                Subgroup (baumannOvergroup R)) : Set (baumannOvergroup R))) ∧
        (elemBaumannIn 2 R).subgroupOf (baumannOvergroup R) =
          CFSG.pCore 2 (baumannOvergroup R) ⊔
            aimg ((elemBaumannIn 2 R).subgroupOf (baumannOvergroup R)) α
              (Vmod (baumannOvergroup R))) ∧
      ⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ =
        Vmod (baumannOvergroup R) ∧
      Vmod (baumannOvergroup R) ≤ Ecore (baumannOvergroup R) ∧
      ∃ β : (⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
            Subgroup (baumannOvergroup R)) →* Multiplicative (Fin 2 → k),
        Function.Surjective β ∧
        β.ker = ((⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
              Subgroup (baumannOvergroup R)) ⊓ Subgroup.center (baumannOvergroup R)).subgroupOf
            (⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
              Subgroup (baumannOvergroup R)) ∧
        ∀ (g : baumannOvergroup R)
          (u u' : (⁅CFSG.pCore 2 (baumannOvergroup R), Kodd (baumannOvergroup R)⁆ :
            Subgroup (baumannOvergroup R))),
          (u' : baumannOvergroup R) = g * u * g⁻¹ →
            Multiplicative.toAdd (β u') =
              (h.actualRho hJ g : Matrix (Fin 2) (Fin 2) k).mulVec
                (Multiplicative.toAdd (β u)) := by
  classical
  obtain ⟨h1, h3, hρ, hfrat, hJeq, hseed, hEeq, hψE, hKodd, hVmod⟩ :=
    wholeCenter h hchar hJ
  obtain ⟨ψE, hE, hext⟩ := hseed.toEcore
  have hSG : elemBaumannIn 2 R ≤ baumannOvergroup R := le_sup_right
  have hcharG : ∀ N : Subgroup (baumannOvergroup R),
      N ≤ ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)) →
      (∀ γ : ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)) ≃*
          ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R)),
        aimg ((h.actualSylow hJ : Sylow 2 (baumannOvergroup R)) : Subgroup (baumannOvergroup R))
          γ N = N) → N.Normal → N = ⊥ := by
    intro N hNS hinv hNn
    by_contra hN0
    have hCchar := characteristic_map_subtype_of_aimg_invariant hSG
      (N := N) (by exact hinv)
    have hCS : N.map (baumannOvergroup R).subtype ≤ elemBaumannIn 2 R := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hNS hx)
    have hC0 : N.map (baumannOvergroup R).subtype ≠ ⊥ := fun hb =>
      hN0 ((Subgroup.map_eq_bot_iff_of_injective N (baumannOvergroup R).subtype_injective).mp hb)
    have key : ∀ g ∈ baumannOvergroup R, ∀ c ∈ N.map (baumannOvergroup R).subtype,
        g * c * g⁻¹ ∈ N.map (baumannOvergroup R).subtype := by
      rintro g hg _ ⟨y, hy, rfl⟩
      exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hNn.conj_mem y hy ⟨g, hg⟩, rfl⟩
    refine h10 _ hCS hC0 hCchar ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key g hg x, fun hx => by
      simpa [mul_assoc] using key g⁻¹ ((baumannOvergroup R).inv_mem hg) _ hx⟩
  obtain ⟨α, hα1, hα2⟩ := hE.characteristic_obstruction_produces_Sylow_supplement hcharG
  obtain ⟨hQK, hVE, β, hβs, hβk, hβe⟩ :=
    natural_center_Sylow_translate_produces_output hE.toIsNatBase α hα2
  refine ⟨h1, h3, hρ, hVmod, ⟨α, hα1, hα2⟩, hQK, hVE, β, hβs, hβk, ?_⟩
  intro g u u' hu
  exact hβe g u u' hu

end Weak

section Ambient

theorem baum_map_inj {T G' : Type*} [Group T] [Group G'] {f : T →* G'}
    (hf : Function.Injective f) (X : Subgroup T) : baum (X.map f) = (baum X).map f := by
  unfold baum
  rw [thompsonJ_map_of_injective' hf, MS93.PU.omegaOneCenterOf_map hf,
    map_inf_centralizer hf]

variable {G : Type*} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]

omit [Finite G] in
theorem noCharNormal_subgroupOf {B Y P : Subgroup G} (hBP : B ≤ P) (hYP : Y ≤ P)
    (hno : ∀ C : Subgroup G, C ≤ B → C ≠ ⊥ → (C.subgroupOf B).Characteristic →
      ¬ Y ≤ Subgroup.normalizer (C : Set G)) :
    NoCharNormal (B.subgroupOf P) (Y.subgroupOf P) := by
  intro C' hC'B hC'ne hC'char hn
  set C : Subgroup G := C'.map P.subtype with hC
  have hCB : C ≤ B := by
    have := Subgroup.map_mono (f := P.subtype) hC'B
    rwa [Subgroup.map_subgroupOf_eq_of_le hBP] at this
  have hCne : C ≠ ⊥ := fun hb =>
    hC'ne ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hb)
  have hchar : (C.subgroupOf B).Characteristic := by
    let e : ↥(B.subgroupOf P) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBP
    have h1 := Wreath.characteristic_map_mulEquiv e hC'char
    have h2 : (C'.subgroupOf (B.subgroupOf P)).map e.toMonoidHom = C.subgroupOf B := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨⟨⟨x, hBP x.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩, ?_, rfl⟩
        show (⟨(x : G), hBP x.2⟩ : ↥P) ∈ C'
        have : (⟨(x : G), hBP x.2⟩ : ↥P) = y := Subtype.ext hyx.symm
        rw [this]
        exact hy
    rw [← h2]
    exact h1
  have key : ∀ y ∈ Y, ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    rintro y hy _ ⟨c, hc, rfl⟩
    have hyY : (⟨y, hYP hy⟩ : ↥P) ∈ Y.subgroupOf P := Subgroup.mem_subgroupOf.mpr hy
    have h1 := (Subgroup.mem_normalizer_iff.1 (hn hyY) c).1 hc
    exact ⟨_, h1, rfl⟩
  refine hno C hCB hCne hchar fun y hy => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key y hy x, fun hx => by simpa [mul_assoc] using key y⁻¹ (Y.inv_mem hy) _ hx⟩

theorem push_up {S P Mx W : Subgroup G} (hSyl : IsSylowTwoOf S P)
    (hnn : ¬ (S.subgroupOf P).Normal) (hSM : S ≤ Mx) (hMP : ¬ P ≤ Mx)
    (hmax : ∀ Y : Subgroup G, S ≤ Y → Y < P → Y ≤ Mx)
    (hred : IsTwoReducedIn P W) (ϱ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) k)
    (hϱ : Function.Surjective ϱ) (ψ : ↥W →* Multiplicative (Fin 2 → k))
    (hψ : Function.Surjective ψ)
    (hψϱ : ∀ (p : ↥P) (v v' : ↥W), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ϱ p : Matrix (Fin 2) (Fin 2) k).mulVec (Multiplicative.toAdd (ψ v)))
    (hψker : ψ.ker = (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf W)
    (hchar : CharTwo P)
    (hnc : ∀ C : Subgroup G, C ≤ baum S → C ≠ ⊥ → (C.subgroupOf (baum S)).Characteristic →
      ¬ oddOrderSubgroup P ⊔ baum S ≤ Subgroup.normalizer (C : Set G))
    (hJ : ⁅thompsonJ S, W⁆ ≠ ⊥) {X : Subgroup G} (hX : X ≤ oddOrderSubgroup P ⊔ baum S)
    (hX2 : IsPGroup 2 X) (hXn : P ≤ Subgroup.normalizer (X : Set G)) :
    ⁅X, oddOrderSubgroup P⁆ ≤ W := by
  classical
  have hSP : S ≤ P := hSyl.1
  have hWP : W ≤ P := hred.1
  have hbS : baum S ≤ P := inf_le_left.trans hSP
  have hOP : oddOrderSubgroup P ≤ P := oddOrderSubgroup_le P
  have hYP : oddOrderSubgroup P ⊔ baum S ≤ P := sup_le hOP hbS
  have hXP : X ≤ P := hX.trans hYP
  obtain ⟨ϱ', φ, hset⟩ := F6.PushS3.natQuotSetting_of_module hSyl hnn hSM hMP hmax hred ϱ hϱ ψ
    hψ hψϱ hψker
  have hchar' := F6.PushS3.charTwo_top_of_charTwo hchar
  have hJ' : ⁅elemThompsonIn 2 (S.subgroupOf P), W.subgroupOf P⁆ ≠ ⊥ := by
    intro hbot
    apply hJ
    have h1 := congrArg (Subgroup.map P.subtype) hbot
    rw [Subgroup.map_commutator, Wreath.elemThompsonIn_subgroupOf_map_eq hSP,
      Subgroup.map_subgroupOf_eq_of_le hWP, Subgroup.map_bot] at h1
    exact h1
  have hodd : oddOrderSubgroup (⊤ : Subgroup ↥P) = (oddOrderSubgroup P).subgroupOf P := by
    rw [← Wreath.oddOrderSubgroup_top_map P]
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hbaum : elemBaumannIn 2 (S.subgroupOf P) = (baum S).subgroupOf P := by
    have h1 : elemBaumannIn 2 (S.subgroupOf P) = baum (S.subgroupOf P) :=
      elemBaumann_map_subtype_eq_baum (S.subgroupOf P)
    have h2 := baum_map_inj P.subtype_injective (S.subgroupOf P)
    rw [Subgroup.map_subgroupOf_eq_of_le hSP] at h2
    rw [h1, h2]
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hG₀ : baumannOvergroup (S.subgroupOf P) = (oddOrderSubgroup P ⊔ baum S).subgroupOf P := by
    rw [baumannOvergroup, hbaum, hodd, Subgroup.subgroupOf_sup hOP hbS]
  have h10 : NoCharNormal (elemBaumannIn 2 (S.subgroupOf P))
      (baumannOvergroup (S.subgroupOf P)) := by
    rw [hbaum, hG₀]
    exact noCharNormal_subgroupOf hbS hYP hnc
  obtain ⟨-, -, -, hVmod, -, hQK, -⟩ := campbellOutput hset hchar' h10 hJ'
  obtain ⟨-, -, -, -, -, -, -, -, hKodd, -⟩ := wholeCenter hset hchar' hJ'
  set G₀ := baumannOvergroup (S.subgroupOf P) with hG₀def
  have hXG₀ : X.subgroupOf P ≤ G₀ := by
    rw [hG₀]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hX (Subgroup.mem_subgroupOf.mp hx))
  set X₀ : Subgroup ↥G₀ := (X.subgroupOf P).subgroupOf G₀ with hX₀def
  have hX₀n : X₀.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hX₀def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hXn (((g : ↥P) : G) |> fun _ => (g : ↥P).2)) _).1 hx
    simpa using this
  have hX₀2 : IsPGroup 2 X₀ := by
    intro y
    obtain ⟨n, hn⟩ := hX2 ⟨(((y : ↥G₀) : ↥P) : G),
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp y.2)⟩
    refine ⟨n, ?_⟩
    have h1 : ((((y ^ 2 ^ n : ↥X₀) : ↥G₀) : ↥P) : G) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  have hX₀Q : X₀ ≤ CFSG.pCore 2 ↥G₀ := le_sSup ⟨hX₀n, hX₀2⟩
  have hWn : ((W.subgroupOf P).subgroupOf G₀).Normal := by
    have : (W.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWP).2 hred.2.1
    exact this.subgroupOf G₀
  have hcomm : ⁅X₀, Kodd ↥G₀⁆ ≤ (W.subgroupOf P).subgroupOf G₀ := by
    calc ⁅X₀, Kodd ↥G₀⁆ ≤ ⁅CFSG.pCore 2 ↥G₀, Kodd ↥G₀⁆ := Subgroup.commutator_mono hX₀Q le_rfl
      _ = Vmod ↥G₀ := hQK
      _ = ⁅(W.subgroupOf P).subgroupOf G₀, Kodd ↥G₀⁆ := hVmod
      _ ≤ _ := Subgroup.commutator_le_left _ _
  have hmap := Subgroup.map_mono (f := P.subtype) (Subgroup.map_mono (f := G₀.subtype) hcomm)
  rw [Subgroup.map_commutator, Subgroup.map_commutator, hKodd, hX₀def,
    Subgroup.map_subgroupOf_eq_of_le hXG₀, Subgroup.map_subgroupOf_eq_of_le hXP,
    Wreath.oddOrderSubgroup_top_map P] at hmap
  refine hmap.trans ?_
  rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  exact Subgroup.mem_subgroupOf.mp hz

end Ambient

end CFSG.Quasithin.MS93.S51
