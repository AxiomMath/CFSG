module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Comm
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModuleME
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UStd
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGLangRatComp
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6RGen
public import CFSG.Mathlib.GroupTheory.PrimePowerGeneratingRanges
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Orbit
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.SingleEdgePerfect
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem split_rootSL2_HSL_eq_coroot
    {L : Type} [Field L] {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (t : Lˣ) :
    rootSL2 Tag.E6 L γ (HSL t) = TwE6Coroot.coroot γ t := by
  have h2 : CFSG.LieType.Steinberg.Adjoint.iform γ γ = 2 :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := Tag.E6)
      (Or.inr (Or.inl rfl)) hγ
  refine CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hγ _ (fun δ _ => ?_) t
  rw [h2, Int.mul_ediv_cancel_left _ two_ne_zero]
  exact CFSG.SeitzReduction.F4Pilot.iform_eq_sum_mul_iform_single γ δ

theorem split_coroot_mem_rationalComponent
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hq : Odd (S.D.q - 1))
    (hnΓ : ∀ k : Fin Tag.E6.rank, weylElt Tag.E6 L k 1 ∈ S.Γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i)
    {s : Lˣ} (hmodel : rootSL2 Tag.E6 L γ (HSL s) ∈ S.D.model)
    (hs : s ^ (S.D.q - 1) = 1) :
    TwE6Coroot.coroot γ s ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hγr : IsRoot Tag.E6 γ := (isRootComponent_componentRoots i).isRoot γ hγ
  have hPW : pinnedWeyl Tag.E6 L γ ∈ S.Γ := by
    refine Subgroup.list_prod_mem _ ?_
    intro g hg
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hg)
    exact hnΓ (Tag.idx Tag.E6 k)
  have hW : rootSL2 Tag.E6 L γ WSL ∈ S.Γ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hweyl, -⟩ :=
      exceptional_Lang_root_rank_one_data Tag.E6 L γ
    have hWSL : rootWeylSL2 Tag.E6 L γ 1 = rootSL2 Tag.E6 L γ WSL := by
      show rootSL2 Tag.E6 L γ (nSL 1) = rootSL2 Tag.E6 L γ WSL
      rw [nSL_one]
    rw [← hWSL, hweyl]
    exact mul_mem (mul_mem hPW (hnΓ (pinnedData Tag.E6 γ).1)) (inv_mem hPW)
  rw [← split_rootSL2_HSL_eq_coroot hγr]
  exact CFSG.StandardType.LangRat.rootSL2_HSL_mem_rationalComponent_of_model_odd
    S i hγ hW hmodel hq hs

theorem eFrame_exists_coroot_in_component
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ≠ 0)
    {J : Subgroup (adjointGroup Tag.E6 K)}
    (hJ : IsComponentOf J (ggFix ((eFrame K ζ hζ).ad x))) :
    ∃ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α ∧
      ∀ s : Kˣ, ∃ u ∈ J, u ∈ (eFrame K ζ hζ).Tor ∧
        (u : ModGL Tag.E6 K) = TwE6Coroot.coroot α s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  let n : ℕ := f
  have hn : 0 < n := f.pos
  have hK : Nat.card K = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, hKf]
  have hperf : commutator ↥(adjointGroup Tag.E6 K) = ⊤ :=
    single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  have : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  obtain ⟨S, hSq, hSΓ, hSmodel⟩ := TableCRes.exists_stdSetup_E6 hK hperf
  have hT : ∀ a : Fin Tag.E6.rank → Kˣ,
      rootDiagUnit Tag.E6 (fun i => Units.map ι.toMonoidHom (a i)) ∈ S.D.torus := by
    intro a
    have hdiagT : rootDiagUnit Tag.E6 (fun i => Units.map ι.toMonoidHom (a i)) ∈
        torusGroup Tag.E6 L := rootDiagUnit_mem_torusGroup _
    have hdiagM : rootDiagUnit Tag.E6 (fun i => Units.map ι.toMonoidHom (a i)) ∈
        S.D.model := by
      rw [← baseChangeGL_rootDiagUnit (τ := Tag.E6) ι a]
      exact hSmodel _ (by
        rw [baseChangeGL_rootDiagUnit]
        exact (exceptional_Lang_adjoint_diagonal_lift Tag.E6 L _).1)
    exact CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mpr
      ⟨hdiagT, (LangDatum.mem_model S.D).mp hdiagM |>.2⟩
  have hnΓ : ∀ k : Fin Tag.E6.rank, weylElt Tag.E6 L k 1 ∈ S.Γ := by
    intro k
    rw [hSΓ, ← baseChangeGL_weylElt_one (τ := Tag.E6) ι k]
    exact Subgroup.mem_map_of_mem _ (weylElt_mem_adjointGroup (τ := Tag.E6) (K := K) k 1)
  let aL : Fin Tag.E6.rank → Lˣ := fun i => Units.map ι.toMonoidHom (zetaVec ζ hζ x i)
  let ιR : adjointGroup Tag.E6 K →* ModGL Tag.E6 L :=
    (baseChangeGL (τ := Tag.E6) ι).comp (adjointGroup Tag.E6 K).subtype
  have hιRinj : Function.Injective ιR :=
    (baseChangeGL_injective (τ := Tag.E6) (f := ι)).comp Subtype.val_injective
  have hbc_d : baseChangeGL (τ := Tag.E6) ι
      (rootDiagUnit Tag.E6 (zetaVec ζ hζ x)) = rootDiagUnit Tag.E6 aL :=
    baseChangeGL_rootDiagUnit (τ := Tag.E6) ι (zetaVec ζ hζ x)
  have hd1 : rootDiagUnit Tag.E6 (zetaVec ζ hζ x) ≠ 1 := by
    intro h
    apply hx
    have hz : zetaVec ζ hζ x = 1 := by
      apply rootDiagUnit_injective (τ := Tag.E6) (K := K)
      rw [h, rootDiagUnit_one]
    have h0 : zetaVec (τ := Tag.E6) ζ hζ (0 : Fin Tag.E6.rank → ZMod 3) = 1 := by
      funext i
      simp [zetaVec_apply]
    exact zetaVec_injective (τ := Tag.E6) hζo hζ (hz.trans h0.symm)
  have hap : ∀ i, aL i ^ 3 = 1 := by
    intro i
    show (Units.map ι.toMonoidHom (zetaVec ζ hζ x i)) ^ 3 = 1
    rw [← map_pow]
    have h3 : zetaVec ζ hζ x i ^ 3 = 1 := by
      rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [h3, map_one]
  have h1 : rootDiagUnit Tag.E6 aL ≠ 1 := by
    intro h
    apply hd1
    apply baseChangeGL_injective (τ := Tag.E6) (f := ι)
    rw [hbc_d, h, map_one]
  have hfixmap : (ggFix ((eFrame K ζ hζ).ad x)).map ιR =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 aL} := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hSΓ]
        exact Subgroup.mem_map_of_mem _ u.2
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        change (baseChangeGL (τ := Tag.E6) ι) (u : ModGL Tag.E6 K) *
            rootDiagUnit Tag.E6 aL =
          rootDiagUnit Tag.E6 aL * (baseChangeGL (τ := Tag.E6) ι) (u : ModGL Tag.E6 K)
        have hm : ((eFrame K ζ hζ).ad x u : ModGL Tag.E6 K) = (u : ModGL Tag.E6 K) :=
          congrArg Subtype.val hu
        change ((NoOffE6Three.diag3 ζ hζ (Multiplicative.ofAdd x) u : adjointGroup Tag.E6 K) :
          ModGL Tag.E6 K) = (u : ModGL Tag.E6 K) at hm
        rw [NoOffE6Three.diag3_apply] at hm
        have h2 : rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * (u : ModGL Tag.E6 K) =
            (u : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) := by
          have h3 := congrArg (fun z : ModGL Tag.E6 K =>
            z * rootDiagUnit Tag.E6 (zetaVec ζ hζ x)) hm
          simpa [mul_assoc] using h3
        rw [← hbc_d]
        simpa only [map_mul] using congrArg (baseChangeGL (τ := Tag.E6) ι) h2.symm
    · rintro ⟨hyΓ, hyC⟩
      rw [hSΓ] at hyΓ
      obtain ⟨u, huR, rfl⟩ := Subgroup.mem_map.mp hyΓ
      refine ⟨⟨u, huR⟩, ?_, rfl⟩
      have hcomm : (u : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) =
          rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * (u : ModGL Tag.E6 K) := by
        have hc := Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [← hbc_d] at hc
        apply baseChangeGL_injective (τ := Tag.E6) (f := ι)
        rw [map_mul, map_mul]
        exact hc
      apply Subtype.ext
      change ((NoOffE6Three.diag3 ζ hζ (Multiplicative.ofAdd x) ⟨u, huR⟩ :
        adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = (u : ModGL Tag.E6 K)
      rw [NoOffE6Three.diag3_apply]
      change rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * (u : ModGL Tag.E6 K) *
        (rootDiagUnit Tag.E6 (zetaVec ζ hζ x))⁻¹ = (u : ModGL Tag.E6 K)
      rw [← hcomm]
      group
  have hcomp : IsComponentOf (J.map ιR)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 aL}) := by
    have h := isComponentOf_map_of_injective ιR hιRinj hJ
    change IsComponentOf (J.map ιR) ((ggFix ((eFrame K ζ hζ).ad x)).map ιR) at h
    rw [hfixmap] at h
    exact h
  obtain ⟨i, -, hJeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2 S
      (by decide) Nat.prime_three
      (by
        have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
        have e : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
        rw [e, h2, zero_add]
        exact one_ne_zero)
      (hT (zetaVec ζ hζ x)) hap h1 (CFSG.Assembly.isComponentOf_iff_open.mp hcomp)
  obtain ⟨x0, hx0⟩ := Quot.exists_rep i
  rw [← hx0] at hJeq
  set α : Fin Tag.E6.rank → ℤ := (x0 : kernelRoots (rootCharHom aL)).1 with hαdef
  have hαroot : IsRoot Tag.E6 α := x0.2.1
  have hαmem : α ∈ componentRoots (rootCharHom aL) (⟦x0⟧ : KernelComponent (rootCharHom aL)) :=
    ⟨x0.2, rfl⟩
  have hoddq : Odd (S.D.q - 1) := by
    rw [hSq]
    have h2f : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
    refine ⟨2 ^ (n - 1) - 1, ?_⟩
    have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  refine ⟨α, hαroot, fun s => ?_⟩
  let sL : Lˣ := Units.map ι.toMonoidHom s
  have hsK : (s : K) ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (s : K) s.ne_zero
  have hsK' : s ^ (Nat.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hsK
  have hsL : sL ^ (S.D.q - 1) = 1 := by
    rw [hSq]
    show (Units.map ι.toMonoidHom s) ^ (2 ^ n - 1) = 1
    rw [← map_pow, ← hK, hsK', map_one]
  have hbc : baseChangeGL (τ := Tag.E6) ι (rootSL2 Tag.E6 K α (HSL s)) =
      rootSL2 Tag.E6 L α (HSL sL) := by
    rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field, map_HSL]
  have hmodelL : rootSL2 Tag.E6 L α (HSL sL) ∈ S.D.model := by
    rw [← hbc]
    exact hSmodel _ (by rw [hbc]; exact rootSL2_mem_adjointGroup (τ := Tag.E6) (k := L) α (HSL sL))
  have hcorL : TwE6Coroot.coroot α sL ∈
      rationalComponent S.ρ S.Γ (rootCharHom aL) (⟦x0⟧ : KernelComponent (rootCharHom aL)) :=
    split_coroot_mem_rationalComponent S hoddq hnΓ
      (⟦x0⟧ : KernelComponent (rootCharHom aL)) hαmem hmodelL hsL
  have hJmem : TwE6Coroot.coroot α sL ∈ J.map ιR := by
    rw [hJeq]
    exact hcorL
  obtain ⟨u, huJ, hu_eq⟩ := Subgroup.mem_map.mp hJmem
  have hbc_cor : baseChangeGL (τ := Tag.E6) ι (TwE6Coroot.coroot α s) =
      TwE6Coroot.coroot α sL := by
    show baseChangeGL (τ := Tag.E6) ι
        (rootDiagUnit Tag.E6 (CFSG.SeitzReduction.E6Pilot.corootTuple α s)) =
      rootDiagUnit Tag.E6 (CFSG.SeitzReduction.E6Pilot.corootTuple α sL)
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext k
    rw [CFSG.SeitzReduction.E6Pilot.corootTuple, CFSG.SeitzReduction.E6Pilot.corootTuple]
    exact map_zpow (Units.map ι.toMonoidHom) s _
  have huK : (u : ModGL Tag.E6 K) = TwE6Coroot.coroot α s := by
    apply baseChangeGL_injective (τ := Tag.E6) (f := ι)
    rw [hbc_cor]
    exact hu_eq
  have hcorAdj : TwE6Coroot.coroot α s ∈ adjointGroup Tag.E6 K := by
    rw [← split_rootSL2_HSL_eq_coroot hαroot s]
    exact rootSL2_mem_adjointGroup α (HSL s)
  let cK : adjointGroup Tag.E6 K := ⟨TwE6Coroot.coroot α s, hcorAdj⟩
  have hcKTor : cK ∈ (eFrame K ζ hζ).Tor := by
    show cK ∈ (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)
    rw [Subgroup.mem_subgroupOf]
    show TwE6Coroot.coroot α s ∈ torusGroup Tag.E6 K
    rw [← split_rootSL2_HSL_eq_coroot hαroot s]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_HSL_mem_torusGroup hαroot s
  refine ⟨cK, ?_, hcKTor, rfl⟩
  rw [show cK = u from Subtype.ext huK.symm]
  exact huJ


private theorem gen_contains_coroot_simple
    {K : Type} [Field K] [Finite K] [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    {J : Subgroup (adjointGroup Tag.E6 K)}
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hsupply : ∀ s : Kˣ, ∃ u ∈ J, u ∈ (eFrame K ζ hζ).Tor ∧
      (u : ModGL Tag.E6 K) = TwE6Coroot.coroot α s)
    (j : Fin 6) (t : Kˣ) (ht3 : ∃ a : ℕ, t ^ 3 ^ a = 1) :
    (eFrameCartanGen (K := K) hζ).d j t ∈ genSubgroup (eFrame K ζ hζ) J := by
  obtain ⟨w, hw⟩ := CFSG.StandardType.GGFinModel.G5.ggG5_orbit_simplyLaced (τ := Tag.E6)
    (Or.inl rfl) hα (IsRoot.basis (τ := Tag.E6) j)
  obtain ⟨ω₀, -, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  let ω : List (Fin 6) := ω₀
  have hw' : (coxeterSystem Tag.E6).wordProd ω • α = Pi.single j 1 := hw
  let m : adjointGroup Tag.E6 K := (ω.map (eFrame K ζ hζ).nb).prod
  have hm_mem : m ∈ Subgroup.closure (Set.range (eFrame K ζ hζ).nb) :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
      exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨u, huJ, huTor, hu_eq⟩ := hsupply t
  have hu3 : ∃ k : ℕ, u ^ 3 ^ k = 1 := by
    obtain ⟨a, ha⟩ := ht3
    exact ⟨a, Subtype.ext (by
      rw [Subgroup.coe_pow, hu_eq, coroot_pow_eq_one α t a ha, Subgroup.coe_one])⟩
  have hgen : m * u * m⁻¹ ∈ genSubgroup (eFrame K ζ hζ) J :=
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨hm_mem,
      ⟨u, ⟨huJ, huTor, hu3⟩, rfl⟩⟩⟩)
  have hconj : m * u * m⁻¹ = (eFrameCartanGen (K := K) hζ).d j t := by
    apply Subtype.ext
    have hmcoe : (m : ModGL Tag.E6 K) =
        (ω.map fun i => ((eFrame K ζ hζ).nb i : ModGL Tag.E6 K)).prod := by
      show (((ω.map (eFrame K ζ hζ).nb).prod : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = _
      rw [SubmonoidClass.coe_list_prod, List.map_map]
      rfl
    have hconjcoe : ((m * u * m⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        (m : ModGL Tag.E6 K) * (u : ModGL Tag.E6 K) * (m : ModGL Tag.E6 K)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hWeq : (ω.map fun i => ((eFrame K ζ hζ).nb i : ModGL Tag.E6 K)) =
        ω.map fun i => weylElt Tag.E6 K i 1 :=
      List.map_congr_left fun i _ => rfl
    rw [hconjcoe, hmcoe, hu_eq, hWeq]
    show (ω.map fun i => weylElt Tag.E6 K i 1).prod *
        rootDiagUnit Tag.E6 (CFSG.SeitzReduction.E6Pilot.corootTuple α t) *
        ((ω.map fun i => weylElt Tag.E6 K i 1).prod)⁻¹ = _
    rw [CFSG.SeitzReduction.E6Pilot.list_prod_weylElt_conj_corootTuple, hw']
    show rootDiagUnit Tag.E6 (CFSG.SeitzReduction.E6Pilot.corootTuple (Pi.single j 1) t) =
      (((eFrameCartanGen (K := K) hζ).d j t : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)
    rw [show (((eFrameCartanGen (K := K) hζ).d j t : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      torusElt Tag.E6 K j t from rfl]
    exact (torusElt_eq_coroot_single j t).symm
  rw [← hconj]
  exact hgen

theorem rGen_eFrame
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    GGE6ThreeRGen (eFrame K ζ hζ) := by
  intro x hx J hJ c hcT hc3
  change c ∈ genSubgroup (eFrame K ζ hζ) J
  obtain ⟨α, hα, hsupply⟩ := eFrame_exists_coroot_in_component hζo hζ hx hJ
  let G : CartanGen (eFrame K ζ hζ) Kˣ := eFrameCartanGen (K := K) hζ
  exact CFSG.GroupTheory.mem_subgroup_of_primePower_generating_ranges G.d
    (eFrame K ζ hζ).Tor (genSubgroup (eFrame K ζ hζ) J) G.tor_eq
    (fun y hy z hz => (eFrame_torus (K := K) hζ).1 y hy z hz)
    Nat.prime_three Nat.card_pos.ne' (fun s => pow_card_eq_one' (x := s))
    (fun j t ht => gen_contains_coroot_simple hζ hα hsupply j t ht) hcT hc3

end CFSG.StandardType.E6ThreeModel
