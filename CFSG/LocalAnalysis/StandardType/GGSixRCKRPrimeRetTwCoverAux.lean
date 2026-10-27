module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetTwStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetPin
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetComp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE6
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.Timmesfeld
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

private lemma rckTc_hom_eq_one_of_perfect {G A : Type*} [Group G] [Group A]
    (hG : Group.IsPerfect G) (f : G →* A)
    (hab : ∀ x y : G, f x * f y = f y * f x) : f = 1 := by
  have hle : _root_.commutator G ≤ f.ker := by
    change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab a b
  rw [hG.commutator_eq_top] at hle
  ext x
  exact MonoidHom.mem_ker.1 (hle (Subgroup.mem_top x))

theorem rckTc_pack
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} {i : KernelComponent (rootCharHom a)}
    {β : Fin 6 → Fin τ.rank → ℤ} (hβroot : ∀ b, IsRoot τ (β b))
    (hΨβ : componentRoots (rootCharHom a) i = rootsOfFam β Set.univ)
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    {h : ℕ} (hh : 0 < h) (hq : S.D.q = 2 ^ h)
    {p₁ : ℕ} (SK : LangSetup Tag.E6 GGL p₁) (hSKq : SK.D.q = 2 ^ h)
    (hSKΦ : SK.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h))
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    (hρ : ∀ γ ∈ rootsOfFam β Set.univ, SK.ρ (ι γ) = ι (S.ρ γ)) :
    ∃ (φ₀ : twistedE6Group 2 h →* ModGL τ GGL) (hφ₀mem : ∀ x, φ₀ x ∈ RetH τ β),
      (∀ x, θ ⟨φ₀ x, hφ₀mem x⟩ = SK.D.g0⁻¹ *
        (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) * SK.D.g0) ∧
      (∀ x, S.D.step (φ₀ x) = φ₀ x) ∧
      (∀ x, φ₀ x = 1 →
        x.1 ∈ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 (2 * h)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPkg : GGLangPkg SK.D (rckTw6_iota h) := rckTw6_langPkg SK h hh hSKΦ
  have hΓSK : SK.D.Γ = (show Subgroup (ModGL Tag.E6 GGL) from (rckTw6_iota h).range).map
      (MulAut.conj SK.D.g0⁻¹).toMonoidHom := rckTw6_Gamma SK h hSKΦ hPkg
  have hqSK : SK.D.q = S.D.q := by rw [hSKq, ← hq]
  have hstepgen := rckRet_theta_step_gen S SK hqSK hι hθ hρΨ hρ
  haveI hMperf : Group.IsPerfect (twistedE6Group 2 h) :=
    fixedGroup_isPerfect_of_four_le_card (frobQ 2 h) (frobQ_frobQ 2 h hh)
      (four_le_card_galoisField 2 h hh)
  obtain ⟨Ψc, hΨcpin, hΨcrange, hΨcker⟩ :=
    rckE6_pinCanon hτ hβroot hι (RingEquiv.refl (GaloisField 2 (2 * h)))
  let f : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * h))) →* ModGL τ GGL :=
    (baseChangeGL (τ := τ) (ggRatEmb (2 * h))).comp Ψc
  have hfr : f.range ≤ RetH τ β := by
    change ((baseChangeGL (τ := τ) (ggRatEmb (2 * h))).comp Ψc).range ≤ RetH τ β
    rw [MonoidHom.range_comp, hΨcrange]
    exact rckCu_map_le (ggRatEmb (2 * h)) (rootsOfFam β Set.univ)
  let f' : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * h))) →* ↥(RetH τ β) :=
    f.codRestrict _ fun u => hfr ⟨u, rfl⟩
  let A' : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * h))) →* ModGL Tag.E6 GGL :=
    (baseChangeGL (τ := Tag.E6) (ggRatEmb (2 * h))).comp
      (((adjointGroup Tag.E6 (GaloisField 2 (2 * h))).subtype).comp
        (e6Isogeny (GaloisField 2 (2 * h))))
  have hgen : ∀ (γ' : Fin Tag.E6.rank → ℤ), IsRoot Tag.E6 γ' → ∀ c : GaloisField 2 (2 * h),
      (θ.comp f') (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c) =
        A' (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c) := by
    intro γ' hγ' c
    have hL := rckRet_iota_L hι hγ'
    have hmemH : pinnedX τ GGL (∑ j : Fin 6, γ' j • β j) (ggRatEmb (2 * h) c) ∈
        RetH τ β :=
      (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ GGL γ)
        _ hL.1 le_rfl) (mem_rootSubgroup.2 ⟨ggRatEmb (2 * h) c, rfl⟩)
    have hfval : f (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c) =
        pinnedX τ GGL (∑ j : Fin 6, γ' j • β j) (ggRatEmb (2 * h) c) := by
      change baseChangeGL (τ := τ) (ggRatEmb (2 * h))
        (Ψc (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c)) = _
      rw [hΨcpin γ' hγ' c, baseChangeGL_pinnedX]
      rfl
    have hA'val : A' (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c) =
        pinnedX Tag.E6 GGL γ' (ggRatEmb (2 * h) c) := by
      change baseChangeGL (τ := Tag.E6) (ggRatEmb (2 * h))
        (((e6Isogeny (GaloisField 2 (2 * h))
          (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c) :
            ↥(adjointGroup Tag.E6 (GaloisField 2 (2 * h)))) :
          ModGL Tag.E6 (GaloisField 2 (2 * h)))) = _
      rw [CFSG.SeitzReduction.E6Pilot.coe_e6Isogeny_xm hγ' c, baseChangeGL_pinnedX]
    calc (θ.comp f') (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c)
        = θ ⟨pinnedX τ GGL (∑ j : Fin 6, γ' j • β j) (ggRatEmb (2 * h) c), hmemH⟩ := by
          apply congrArg θ
          apply Subtype.ext
          exact hfval
      _ = pinnedX Tag.E6 GGL (ι (∑ j : Fin 6, γ' j • β j)) (ggRatEmb (2 * h) c) :=
          hθ.1 _ hL.1 (ggRatEmb (2 * h) c) hmemH
      _ = pinnedX Tag.E6 GGL γ' (ggRatEmb (2 * h) c) := by rw [hL.2]
      _ = A' (e6Data_valid.xm (GaloisField 2 (2 * h)) γ' c) := hA'val.symm
  have hθf' : θ.comp f' = A' := by
    refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid
      (GaloisField 2 (2 * h))) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact hgen _ (IsRoot.basis i) c
    · exact hgen _ (IsRoot.neg (IsRoot.basis i)) c
  have hiota_psi : ∀ x : twistedE6Group 2 h,
      (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) = A' x.1 :=
    fun x => rfl
  have hzh : SK.D.g0⁻¹ ∈ adjointGroup Tag.E6 GGL := inv_mem SK.D.g0_mem
  have hzh_mem : SK.D.g0⁻¹ ∈ θ.range := by
    rw [hθ.2.1]
    exact hzh
  obtain ⟨zsub, hzsub⟩ := hzh_mem
  let z : ModGL τ GGL := zsub
  have hzmem : z ∈ RetH τ β := zsub.2
  have hθz : θ ⟨z, hzmem⟩ = SK.D.g0⁻¹ := hzsub
  let φ₀ : twistedE6Group 2 h →* ModGL τ GGL :=
    (MulAut.conj z).toMonoidHom.comp
      (f.comp (fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype)
  have hφ₀mem : ∀ x, φ₀ x ∈ RetH τ β := by
    intro x
    change z * f ((fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype x) * z⁻¹ ∈
      RetH τ β
    exact mul_mem (mul_mem hzmem (hfr ⟨_, rfl⟩)) (inv_mem hzmem)
  have hθφ₀ : ∀ x, θ ⟨φ₀ x, hφ₀mem x⟩ = SK.D.g0⁻¹ * A' x.1 * SK.D.g0 := by
    intro x
    have h1 : (⟨φ₀ x, hφ₀mem x⟩ : ↥(RetH τ β)) = zsub * f' x.1 * zsub⁻¹ := by
      apply Subtype.ext
      change z * f ((fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype x) * z⁻¹ =
        z * f x.1 * z⁻¹
      rfl
    rw [h1, map_mul, map_mul, map_inv, hzsub]
    have hθf'x : θ (f' x.1) = A' x.1 := DFunLike.congr_fun hθf' x.1
    rw [hθf'x, inv_inv]
  have hstepmem : ∀ x, S.D.step (φ₀ x) ∈ RetH τ β :=
    fun x => (hstepgen ⟨φ₀ x, hφ₀mem x⟩).1
  have hfixθ : ∀ x, SK.D.step (θ ⟨φ₀ x, hφ₀mem x⟩) = θ ⟨φ₀ x, hφ₀mem x⟩ := by
    intro x
    rw [hθφ₀ x]
    have hmemΓ : SK.D.g0⁻¹ * A' x.1 * SK.D.g0 ∈ SK.D.Γ := by
      rw [hΓSK]
      refine ⟨A' x.1, ?_, ?_⟩
      · rw [← hiota_psi x]
        exact ⟨rckTw6_psi h hh x, rfl⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact ((SK.D.mem_model).1 (LangSetup.Γ_le_model SK hmemΓ)).2
  let cfun : twistedE6Group 2 h → ↥(RetH τ β) := fun x =>
    ⟨(φ₀ x)⁻¹ * S.D.step (φ₀ x), mul_mem (inv_mem (hφ₀mem x)) (hstepmem x)⟩
  have hcker : ∀ x, cfun x ∈ θ.ker := by
    intro x
    rw [MonoidHom.mem_ker]
    change θ (⟨φ₀ x, hφ₀mem x⟩⁻¹ * ⟨S.D.step (φ₀ x), hstepmem x⟩) = 1
    rw [map_mul, map_inv, (hstepgen ⟨φ₀ x, hφ₀mem x⟩).2, hfixθ x, inv_mul_cancel]
  have hccenter : ∀ x, cfun x ∈ Subgroup.center ↥(RetH τ β) :=
    fun x => hθ.2.2.1 _ (hcker x)
  let cHom : twistedE6Group 2 h →* ↥(RetH τ β) :=
    { toFun := cfun
      map_one' := by
        apply Subtype.ext
        change (φ₀ 1)⁻¹ * S.D.step (φ₀ 1) = 1
        rw [map_one, map_one, inv_one, one_mul]
      map_mul' := fun x y => by
        apply Subtype.ext
        change (φ₀ (x * y))⁻¹ * S.D.step (φ₀ (x * y)) =
          ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) * ((φ₀ y)⁻¹ * S.D.step (φ₀ y))
        simp only [map_mul]
        have hcomm : (φ₀ y)⁻¹ * ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) =
            ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) * (φ₀ y)⁻¹ := by
          have h := Subgroup.mem_center_iff.1 (hccenter x)
            (⟨(φ₀ y)⁻¹, inv_mem (hφ₀mem y)⟩ : ↥(RetH τ β))
          exact congrArg Subtype.val h
        calc (φ₀ x * φ₀ y)⁻¹ * (S.D.step (φ₀ x) * S.D.step (φ₀ y))
            = (φ₀ y)⁻¹ * ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) * S.D.step (φ₀ y) := by group
          _ = ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) * (φ₀ y)⁻¹ * S.D.step (φ₀ y) := by rw [hcomm]
          _ = ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) * ((φ₀ y)⁻¹ * S.D.step (φ₀ y)) := by group }
  have hcHom_one : cHom = 1 := by
    apply rckTc_hom_eq_one_of_perfect hMperf
    intro x y
    exact (Subgroup.mem_center_iff.1 (hccenter x) (cHom y)).symm
  have hfix : ∀ x, S.D.step (φ₀ x) = φ₀ x := by
    intro x
    have h1 : (φ₀ x)⁻¹ * S.D.step (φ₀ x) = 1 := by
      have h := congrArg (fun g : ↥(RetH τ β) => (g : ModGL τ GGL))
        (DFunLike.congr_fun hcHom_one x)
      exact h
    calc S.D.step (φ₀ x) = φ₀ x * ((φ₀ x)⁻¹ * S.D.step (φ₀ x)) := by group
      _ = φ₀ x * 1 := by rw [h1]
      _ = φ₀ x := mul_one _
  have hθφ₀_iota : ∀ x, θ ⟨φ₀ x, hφ₀mem x⟩ = SK.D.g0⁻¹ *
      (show ModGL Tag.E6 GGL from rckTw6_iota h (rckTw6_psi h hh x)) * SK.D.g0 := by
    intro x
    rw [hθφ₀ x, ← hiota_psi x]
  have hkerΨ : ∀ x, φ₀ x = 1 →
      x.1 ∈ Subgroup.center ↥(e6Data_valid.minGroup (GaloisField 2 (2 * h))) := by
    intro x hx
    have hf1 : f x.1 = 1 := by
      have h2 : z * f x.1 * z⁻¹ = 1 := hx
      have h3 := congrArg (fun g => z⁻¹ * g * z) h2
      simpa [mul_assoc] using h3
    have hΨ1 : Ψc x.1 = 1 := by
      apply baseChangeGL_injective (ggRatEmb (2 * h))
      rw [map_one]
      exact hf1
    exact hΨcker (by rw [MonoidHom.mem_ker]; exact hΨ1)
  exact ⟨φ₀, hφ₀mem, hθφ₀_iota, hfix, hkerΨ⟩

end CFSG.StandardType.RCKRP

end
