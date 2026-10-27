module

public import CFSG.LocalAnalysis.StandardType.ExcPos.PacketBasic
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6Base
public import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneInner
public import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneWeyl
public import CFSG.LocalAnalysis.StandardType.ExcPos.RankOneOrbit
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart14
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutCommon
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGFamTypeAFrames
import all CFSG.LocalAnalysis.StandardType.GGJ4dRankTwoBound

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.Chevalley
  CFSG.StandardType CFSG.StandardType.ClassicalPosition
open scoped MatrixGroups

theorem eq_one_of_fixes_central_image {X G : Type*} [Group X] [Group G]
    {J G₀ : Subgroup X} (hJG : J ≤ G₀) (η : G₀ →* G)
    (hker : η.ker ≤ Subgroup.center G₀) (hJ : Group.IsPerfect J) (a : MulAut J)
    (hfix : ∀ j : J, η (Subgroup.inclusion hJG (a j)) = η (Subgroup.inclusion hJG j)) :
    a = 1 := by
  refine CFSG.HardMathSupport.Solomon.Coordinator.mulAut_eq_one_of_central_perfect hJ a ?_
  intro j
  have hk : Subgroup.inclusion hJG (j⁻¹ * a j) ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, hfix j]
    exact inv_mul_cancel _
  have hc := hker hk
  rw [Subgroup.mem_center_iff]
  intro y
  have heq := Subgroup.mem_center_iff.mp hc (Subgroup.inclusion hJG y)
  apply Subtype.ext
  exact congrArg (fun z : G₀ => (z : X)) heq

theorem mem_D_of_centralizes_base_rootSpan
    {X : Type} [Group X] {τ : Tag} {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    (P : ExcBase τ f p G₀ B₁ D J x)
    (hJG : J ≤ G₀) (hJ : Group.IsPerfect J)
    (hBN : B₁ ≤ Subgroup.normalizer (J : Set X))
    (hBCD : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (b : B₁)
    (hb : P.Θ b ∈ Subgroup.centralizer
      (rootSpan τ (ExcOmega f) P.rootsJ : Set (ModGL τ (ExcOmega f)))) : (b : X) ∈ D := by
  let ι : J →* G₀ := Subgroup.inclusion hJG
  have hJimage : (P.η.comp ι).range ≤ rootSpan τ (ExcOmega f)
      (CFSG.StandardType.LieCore.ratOrbit P.ρ P.rootsJ) := by
    rintro y ⟨j, rfl⟩
    apply P.map_J_le
    exact ⟨ι j, j.2, rfl⟩
  have hfix : P.Δ.step (P.Θ b) = P.Θ b :=
    ((LangDatum.mem_model (D := P.Δ)).mp (P.Θ_mem b)).2
  have hc := CFSG.StandardType.F4ExplicitPos.OrbitKernel.mem_centralizer_of_mem_centralizer_rootSpan
    P.Δ P.ρ P.frob (fun γ hγ => hγ.1.1) hJimage hfix hb
  let a : MulAut J := J.normalizerMonoidHom ⟨b, hBN b.2⟩
  have ha : a = 1 := by
    apply eq_one_of_fixes_central_image hJG P.η P.ker_η hJ a
    intro j
    change P.η (ι (a j)) = P.η (ι j)
    have hact : P.η (ι (a j)) = P.Θ b * P.η (ι j) * (P.Θ b)⁻¹ :=
      P.η_conj b (ι j) (ι (a j)) (by
        simp only [ι, a, Subgroup.coe_inclusion, Subgroup.normalizerMonoidHom_apply_apply_coe])
    rw [hact]
    have hcomm := Subgroup.mem_centralizer_iff.mp hc (P.η (ι j)) ⟨j, rfl⟩
    rw [← hcomm]
    group
  have hbC : (b : X) ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun z : MulAut J => ((z ⟨y, hy⟩ : J) : X)) ha
    change (b : X) * y * (b : X)⁻¹ = y at h
    calc y * (b : X) = ((b : X) * y * (b : X)⁻¹) * (b : X) := by rw [h]
      _ = (b : X) * y := by group
  rw [← hBCD]
  exact ⟨b.2, hbC⟩

theorem mem_D_of_rootSL2_base_action_eq_one
    {X : Type} [Group X] {τ : Tag} {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    (P : ExcBase τ f p G₀ B₁ D J x)
    (hJG : J ≤ G₀) (hJ : Group.IsPerfect J)
    (hBN : B₁ ≤ Subgroup.normalizer (J : Set X))
    (hBCD : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpair : P.rootsJ = {γ, -γ})
    (a : B₁ →* SL(2, ExcOmega f))
    (hinner : ∀ (b : B₁) (A : SL(2, ExcOmega f)),
      P.Θ b * rootSL2 τ (ExcOmega f) γ A * (P.Θ b)⁻¹ =
        rootSL2 τ (ExcOmega f) γ (a b * A * (a b)⁻¹))
    (b : B₁) (hb : a b = 1) : (b : X) ∈ D := by
  apply mem_D_of_centralizes_base_rootSpan P hJG hJ hBN hBCD b
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hspan : rootSpan τ (ExcOmega f) P.rootsJ = (rootSL2 τ (ExcOmega f) γ).range := by
    rw [hpair, CFSG.LieType.HighestRoot.rootSpan_pair_eq, range_rootSL2_of_isRoot hγ]
  rw [hspan] at hy
  obtain ⟨A, rfl⟩ := hy
  have hact := hinner b A
  simp only [hb, one_mul, inv_one, mul_one] at hact
  calc rootSL2 τ (ExcOmega f) γ A * P.Θ b =
      (P.Θ b * rootSL2 τ (ExcOmega f) γ A * (P.Θ b)⁻¹) * P.Θ b := by rw [hact]
    _ = P.Θ b * rootSL2 τ (ExcOmega f) γ A := by group

theorem rankOne_action_impossible {X : Type} [Group X] [Finite X]
    {F : Type} [Field F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B D : Subgroup X} (hB : IsElemAbelian p B)
    (hB4 : p ^ 4 ≤ Nat.card B) (hD2 : Nat.card D = p ^ 2)
    (a : B →* SL(2, F)) (hker : ∀ b : B, a b = 1 → (b : X) ∈ D) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : (p : F) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have htop : IsElemAbelian p (⊤ : Subgroup B) := by
    simpa using hB.subgroupOf B
  have himage : IsElemAbelian p a.range := by
    simpa only [← MonoidHom.range_eq_map] using htop.map a
  haveI : Finite a.range :=
    Finite.of_surjective a.rangeRestrict (MonoidHom.rangeRestrict_surjective a)
  have hbound : Nat.card a.range ≤ p :=
    CFSG.LieType.SeitzGeneration.ExcHigh.card_le_of_isElemAbelian_specialLinear_two hpF himage
  let kD : a.ker → D := fun b => ⟨((b : B) : X), hker b b.2⟩
  have hkDi : Function.Injective kD := by
    intro b c h
    apply Subtype.ext
    apply Subtype.ext
    simpa only [kD] using congrArg (fun d : D => (d : X)) h
  have hk : Nat.card a.ker ≤ Nat.card D := Nat.card_le_card_of_injective kD hkDi
  have hB3 : Nat.card B ≤ p ^ 3 := by
    calc Nat.card B = Nat.card a.ker * Nat.card a.range :=
          (Subgroup.card_ker_mul_card_range a).symm
      _ ≤ Nat.card D * p := Nat.mul_le_mul hk hbound
      _ = p ^ 3 := by rw [hD2]; ring
  have hp34 : p ^ 3 < p ^ 4 := (Nat.pow_lt_pow_iff_right hp.one_lt).mpr (by decide)
  have hp43 : p ^ 4 ≤ p ^ 3 := hB4.trans hB3
  omega

theorem rankOne_base_impossible_of_inner
    {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n f p : ℕ} {ψ : (CFSG.StandardType.ggU t n f).K →* X}
    {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : CFSG.StandardType.ClassicalPosition.GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    (P : ExcBase (CFSG.StandardType.GGFinModel.langTag t) f p G₀ B₁ D J x)
    {γ : Fin (CFSG.StandardType.GGFinModel.langTag t).rank → ℤ}
    (hγ : IsRoot (CFSG.StandardType.GGFinModel.langTag t) γ) (hpair : P.rootsJ = {γ, -γ})
    (a : B₁ →* SL(2, ExcOmega f))
    (hinner : ∀ (b : B₁) (A : SL(2, ExcOmega f)),
      P.Θ b * rootSL2 (CFSG.StandardType.GGFinModel.langTag t) (ExcOmega f) γ A * (P.Θ b)⁻¹ =
        rootSL2 (CFSG.StandardType.GGFinModel.langTag t) (ExcOmega f) γ
          (a b * A * (a b)⁻¹)) : False := by
  obtain ⟨-, -, -, -, hp, hp2, -, -, hB, hB4, -, hD2, hBN, hBCD, hJcomp, -⟩ := hH
  have hJG : J ≤ G₀ := hJcomp.1.trans inf_le_left
  have hJ : Group.IsPerfect J := ⟨hJcomp.2.2.1⟩
  exact rankOne_action_impossible hp hp2 hB hB4 hD2 a
    (mem_D_of_rootSL2_base_action_eq_one P hJG hJ hBN hBCD hγ hpair a hinner)

theorem pair_of_compRank_lt_two
    {τ : Tag} (hτ : SimplyLacedTag τ) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i)
    (hsmall : compRank (componentRoots χ i) < 2) :
    ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ componentRoots χ i = {γ, -γ} := by
  have hpos := CFSG.StandardType.LangRat.one_le_compRank_of_nonempty
    (fun β hβ => hβ.1.1) ⟨α, hα⟩
  have hone : compRank (componentRoots χ i) = 1 := by omega
  exact CFSG.StandardType.TableCRes.fam_exists_pair_of_rank_one i
    (CFSG.StandardType.LangRat.j4d_rank_one_ncard hτ (isRootComponent_componentRoots i) hone)

theorem theta_mem_rootSpan_pair_sup_centralizer_of_base
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    (P : ExcBase (GGFinModel.langTag t) f p G₀ B₁ D J x)
    {γ : Fin (GGFinModel.langTag t).rank → ℤ} (hγ : IsRoot (GGFinModel.langTag t) γ)
    (hpair : P.rootsJ = {γ, -γ}) :
    ∀ b : B₁, P.Θ b ∈ rootSpan (GGFinModel.langTag t) (ExcOmega f) {γ, -γ} ⊔
      Subgroup.centralizer
        (rootSpan (GGFinModel.langTag t) (ExcOmega f) {γ, -γ} :
          Set (ModGL (GGFinModel.langTag t) (ExcOmega f))) := by
  obtain ⟨-, -, -, -, hp, hp2, -, -, hB, -, hDB, -, hBN, -, hJcomp, -⟩ := hH
  let τ := GGFinModel.langTag t
  let coords : Bool → Fin τ.rank → (ExcOmega f)ˣ :=
    fun b => if b then P.coord P.d else P.coord x
  have hkernel : kernelRoots P.chiD = familyKernel coords := by
    ext α
    change (IsRoot τ α ∧ P.chiD (Multiplicative.ofAdd α) = 1) ↔
      (IsRoot τ α ∧ ∀ b : Bool, rootChar (coords b) α = 1)
    simp [ExcBase.chiD, LieCore.jointChar, CFSG.LieType.AlgebraicGroups.rootCharHom,
      coords, Bool.forall_bool]
  have hperiod : P.ρ '' (P.ρ '' P.rootsJ) = P.rootsJ := by
    have hpos : 0 < P.b := by rcases P.b_eq_one_or_two with h | h <;> omega
    let S : Set ℕ := {s | 0 < s ∧
      (P.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' P.rootsJ = P.rootsJ}
    have hSpos : 0 < sInf S := by
      simpa only [S, ExcBase.b, componentOrbitLength] using hpos
    have hS := Nat.sInf_mem (Nat.nonempty_of_pos_sInf hSpos)
    have hbperiod :
        (P.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[P.b] '' P.rootsJ = P.rootsJ := by
      simpa only [S, ExcBase.b, componentOrbitLength] using hS.2
    rcases P.b_eq_one_or_two with hb | hb
    · have h1 : P.ρ '' P.rootsJ = P.rootsJ := by
        simpa only [hb, Function.iterate_one] using hbperiod
      rw [h1, h1]
    · rw [Set.image_image]
      simpa only [hb, Function.iterate_succ, Function.iterate_zero,
        Function.id_comp, Function.comp_def, id_eq] using hbperiod
  let K := (J.subgroupOf G₀).map P.η
  have hKmodel : K ≤ P.Δ.model := by
    rintro y ⟨u, hu, rfl⟩
    have hΓ : P.η u ∈ P.Δ.Γ := by rw [← P.range_η]; exact ⟨u, rfl⟩
    exact Subgroup.commutator_le_self _ hΓ
  have hKnoncomm : ∃ y ∈ K, ∃ z ∈ K, y * z ≠ z * y := by
    by_contra hcomm
    push Not at hcomm
    haveI : IsMulCommutative K := ⟨⟨fun u v => Subtype.ext (hcomm u u.2 v v.2)⟩⟩
    haveI : Group.IsPerfect K := ⟨P.attach_J.2.2.1⟩
    haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := P.attach_J.2.2.2
    haveI : Nontrivial K :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center K))
    exact Group.IsPerfect.not_isMulCommutative K inferInstance
  have hJG : J ≤ G₀ := hJcomp.1.trans inf_le_left
  let κ : J →* ModGL τ (ExcOmega f) := P.η.comp (Subgroup.inclusion hJG)
  have hKeq : K = κ.range := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨(u : X), hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨Subgroup.inclusion hJG u, u.2, rfl⟩
  intro b
  let β : MulAut J := J.normalizerMonoidHom ⟨b, hBN b.2⟩
  have hact : ∀ j : J, P.Θ b * κ j * (P.Θ b)⁻¹ = κ (β j) := by
    intro j
    exact (P.η_conj b (Subgroup.inclusion hJG j) (Subgroup.inclusion hJG (β j)) (by
      simp only [β, Subgroup.coe_inclusion, Subgroup.normalizerMonoidHom_apply_apply_coe])).symm
  have hNK : P.Θ b ∈ Subgroup.normalizer (K : Set (ModGL τ (ExcOmega f))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hKeq]
    refine le_antisymm ?_ ?_
    · rintro y ⟨z, ⟨j, rfl⟩, rfl⟩
      change P.Θ b * κ j * (P.Θ b)⁻¹ ∈ κ.range
      rw [hact j]
      exact ⟨β j, rfl⟩
    · rintro y ⟨j, rfl⟩
      refine ⟨κ (β.symm j), ⟨β.symm j, rfl⟩, ?_⟩
      change P.Θ b * κ (β.symm j) * (P.Θ b)⁻¹ = κ j
      simpa only [MulEquiv.apply_symm_apply] using hact (β.symm j)
  have hfix : P.Δ.step (P.Θ b) = P.Θ b :=
    ((LangDatum.mem_model (D := P.Δ)).mp (P.Θ_mem b)).2
  have htoral : ∀ e ∈ D, rootDiagUnit τ (P.coord e) * P.Θ b *
      (rootDiagUnit τ (P.coord e))⁻¹ = P.Θ b := by
    intro e he
    let eB : B₁ := ⟨e, hDB he⟩
    have hcomm := congrArg P.Θ (hB.1.is_comm.comm eB b)
    rw [map_mul, map_mul, P.Θ_eq_coord eB he] at hcomm
    change rootDiagUnit τ (P.coord e) * P.Θ b = P.Θ b * rootDiagUnit τ (P.coord e) at hcomm
    rw [hcomm]
    group
  have hfamily : P.Θ b ∈ familyCentralizer τ (ExcOmega f) coords := by
    refine mem_familyCentralizer.mpr ⟨
      ((LangDatum.mem_model (D := P.Δ)).mp (P.Θ_mem b)).1, ?_⟩
    intro q
    cases q
    · simpa only [coords, Bool.false_eq_true, ↓reduceIte] using htoral x P.x_mem
    · simpa only [coords, ↓reduceIte] using htoral P.d P.d_mem
  obtain ⟨w, hw, m, hm, hbm⟩ := familyCentralizer_le_mul τ (ExcOmega f) coords hfamily
  have hbp : b ^ p = 1 := Subtype.ext (hB.2 b b.2)
  have hConjp : (MulAut.conj (P.Θ b)) ^ p = 1 := by
    rw [← map_pow, ← map_pow, hbp, map_one, map_one]
  have hodd : Odd (orderOf (MulAut.conj (P.Θ b))) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hConjp)
  have hwγ : w • γ = γ ∨ w • γ = -γ :=
    root_eq_or_neg_of_fixed_family_bruhat coords P.chiD hkernel P.iJ hγ hpair
      P.Δ P.ρ P.frob P.mapsTo_rho_chiD hperiod K hKmodel P.map_J_le hKnoncomm
      hm hw hbm hfix hNK hodd
  have hmconn : m ∈ torusGroup τ (ExcOmega f) ⊔ rootSpan τ (ExcOmega f) (kernelRoots P.chiD) := by
    simpa only [familyGroup, hkernel] using hm
  have hmprod : m ∈ rootSpan τ (ExcOmega f) {γ, -γ} ⊔
      Subgroup.centralizer (rootSpan τ (ExcOmega f) {γ, -γ} : Set (ModGL τ (ExcOmega f))) := by
    have h := torus_sup_kernelRootSpan_le_component_sup_centralizer_of_pair P.chiD P.iJ hγ hpair hmconn
    have hspan : componentRootSpan (ExcOmega f) P.chiD P.iJ =
        rootSpan τ (ExcOmega f) {γ, -γ} := congrArg (rootSpan τ (ExcOmega f)) hpair
    simpa only [hspan] using h
  rw [hbm]
  exact mul_mem hmprod (canonicalRep_mem_sup_centralizer_rootSpan_pair_of_smul_eq hγ hwγ)

theorem excBase_rank_ge_two {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    (P : ExcBase (GGFinModel.langTag t) f p G₀ B₁ D J x) :
    2 ≤ compRank P.rootsJ := by
  by_contra hsmall
  have hτ : SimplyLacedTag (GGFinModel.langTag t) := by
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp [GGFinModel.langTag, SimplyLacedTag]
  have hlt : compRank P.rootsJ < 2 := Nat.lt_of_not_ge hsmall
  obtain ⟨α, hα⟩ := Quotient.exists_rep P.iJ
  have hαmem : (α : Fin (GGFinModel.langTag t).rank → ℤ) ∈ P.rootsJ := ⟨α.2, hα⟩
  obtain ⟨γ, hγ, hpair⟩ := pair_of_compRank_lt_two hτ P.iJ hαmem hlt
  obtain ⟨a, ha⟩ := exists_rootSL2_inner_hom hγ P.Θ
    (theta_mem_rootSpan_pair_sup_centralizer_of_base hH P hγ hpair)
  exact rankOne_base_impossible_of_inner hH P hγ hpair a ha

theorem excU3_holds : ExcU3 := by
  intro t ht X _ _ n f ψ p G₀ B₁ D J L x hH R Rm P
  exact excBase_rank_ge_two ht hH P.toBase

end CFSG.StandardType.LieKnownR2.ExcPos
