module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigOModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigOY
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigA
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
import CFSG.LinearAlgebra.F2PlaneMaps

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LinearAlgebra.SteinbergBQ

theorem qtwoDB43_perfect_fixes_plane {G : Type} [Group G] {N J : Subgroup G} (hJN : J ≤ N)
    (hJ : ⁅J, J⁆ = J) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (σ : ↥N ≃* ↥(orthDerived Q))
    {V₀ : Submodule (ZMod 2) V} (hV₀dim : Module.finrank (ZMod 2) V₀ = 2)
    (hpres : ∀ n : ↥N, (n : G) ∈ J → ∀ x ∈ V₀,
      ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x ∈ V₀) :
    ∀ n : ↥N, (n : G) ∈ J → ∀ x ∈ V₀,
      ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x := by
  have hJsub : (J.subgroupOf N).map N.subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
    exact hJN
  have hcomm : ⁅J.subgroupOf N, J.subgroupOf N⁆ = J.subgroupOf N :=
    Subgroup.map_injective N.subtype_injective (by
      rw [Subgroup.map_commutator, hJsub, hJ])
  haveI : Group.IsPerfect ↥(J.subgroupOf N) := Subgroup.isPerfect_iff.mpr hcomm
  let ρ : ↥(J.subgroupOf N) →* (V ≃ₗ[ZMod 2] V) :=
    ((orthDerived Q).subtype.comp σ.toMonoidHom).comp (J.subgroupOf N).subtype
  have hst : ∀ g : ↥(J.subgroupOf N), ∀ w ∈ V₀, ρ g w ∈ V₀ := by
    intro g w hw
    have hgJ : (((J.subgroupOf N).subtype g : ↥N) : G) ∈ J := Subgroup.mem_subgroupOf.mp g.2
    have hle := hpres ((J.subgroupOf N).subtype g) hgJ w hw
    simpa [ρ, MonoidHom.comp_apply] using hle
  intro n hn x hx
  have h := CFSG.LinearAlgebra.apply_eq_self_of_isPerfect (W := V₀) hV₀dim ρ hst
    ⟨n, Subgroup.mem_subgroupOf.mpr hn⟩ x hx
  simpa [ρ, MonoidHom.comp_apply] using h

theorem qtwoDB43_plane_of_torus {m : ℕ} (hm : 6 ≤ m) {c : Fin m} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank (ZMod 2) V = 2 * m)
    (hplus : ¬ (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m))
    (τ : Multiplicative (DVec m) →* ↥(orthDerived Q))
    (hτker : ∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : ↥(orthDerived Q), ∀ v : DVec m,
      y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v))) :
    ∃ V₀ : Submodule (ZMod 2) V,
      (∀ x : V, x ∈ V₀ ↔ ∀ v : DVec m,
        ((τ (Multiplicative.ofAdd v) : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x) ∧
      Module.finrank (ZMod 2) V₀ = 2 ∧
      (∀ x ∈ V₀, (∀ y ∈ V₀, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (∀ v : DVec m, (∀ i, i ≠ c → v i ≠ 0) → ∀ x : V,
        ((τ (Multiplicative.ofAdd v) : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x → x ∈ V₀) ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType (Q.restrict (qtwoDB43_perp Q V₀)) ↔ Even (m - 1)) := by
  let τ₀ : Multiplicative (DVec m) →* (V ≃ₗ[ZMod 2] V) := (orthDerived Q).subtype.comp τ
  have hτO : τ₀.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨v, rfl⟩
    exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
      (Q := Q) (τ v).2
  have hτker' : ∀ v : DVec m, τ₀ (Multiplicative.ofAdd v) = 1 ↔
      ∀ i, i ≠ c → v i = 0 := by
    intro v
    have hiff : τ₀ (Multiplicative.ofAdd v) = 1 ↔ τ (Multiplicative.ofAdd v) = 1 := by
      constructor
      · intro h
        apply Subtype.ext
        simpa [τ₀] using h
      · intro h
        show τ₀ (Multiplicative.ofAdd v) = 1
        rw [show τ₀ (Multiplicative.ofAdd v) =
            ((τ (Multiplicative.ofAdd v) : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) from rfl]
        rw [h]
        rfl
    exact hiff.trans (hτker v)
  have hW' : ∀ w ∈ dEvenStab m (Pi.single c 1),
      ∃ n ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ v : DVec m,
        n * τ₀ (Multiplicative.ofAdd v) * n⁻¹ = τ₀ (Multiplicative.ofAdd (w v)) := by
    intro w hw
    obtain ⟨y, hy⟩ := hW w hw
    refine ⟨(y : V ≃ₗ[ZMod 2] V),
      CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Q) y.2, ?_⟩
    intro v
    have h := congrArg Subtype.val (hy v)
    simpa [τ₀] using h
  obtain ⟨hfin, hnd, hfix, htype⟩ := qtwoDB41_torus_weights hm hQ τ₀ hτO hτker' hW'
    (Or.inr ⟨hdim, hplus⟩)
  refine ⟨fixedSub τ₀.range, ?_, ?_, hnd, ?_, htype⟩
  · intro x
    rw [mem_fixedSub]
    constructor
    · intro h v
      exact h (τ₀ (Multiplicative.ofAdd v)) (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    · intro h μ hμ
      obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hμ
      simpa [τ₀] using h (Multiplicative.toAdd v)
  · omega
  · intro v hv x hx
    exact hfix v hv x (by simpa [τ₀] using hx)

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB43_case_orth_big_of (hRig : GGLabelRigidInput) (hm : 6 ≤ m) {N J₁ J₂ : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hinner : GGInnerDiagOn Bs N) (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hD : (Odd m ∧ lab = ⟨.D, m, 1⟩) ∨ (Even m ∧ lab = ⟨.twD, m, 1⟩))
    (hker_char : ∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔
      ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0)
    {Θ : ↥(dEvenStab m (Pi.single c 1)) →*
      ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range)}
    (hΘact : ∀ (w : ↥(dEvenStab m (Pi.single c 1))) (s : ↥Bs),
      (Θ w : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
        (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm
          ((w : DVec m ≃ₗ[ZMod 3] DVec m) (βL (Additive.ofMul s))))))
    (hJ₁N : J₁ ≤ N) (hJ₁perf : ⁅J₁, J₁⁆ = J₁) {s₁ : ↥Bs}
    (hs₁ : ∀ i, i ≠ c → βL (Additive.ofMul s₁) i ≠ 0) (hJ₁c : ∀ n ∈ J₁, (s₁ : G) * n = n * s₁)
    (hJ₂N : J₂ ≤ N) (hJ₂perf : ⁅J₂, J₂⁆ = J₂) {s₂ : ↥Bs}
    (hs₂ : ∀ i, i ≠ c → βL (Additive.ofMul s₂) i ≠ 0) (hJ₂c : ∀ n ∈ J₂, (s₂ : G) * n = n * s₂) :
    ∃ Y : Subgroup G, J₁ ≤ Y ∧ J₂ ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have htag : lab = ⟨.D, m, 1⟩ ∨ lab = ⟨.twD, m, 1⟩ := by
    rcases hD with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨V, i₁, i₂, i₃, Q, σ, τ, hQ, hdim, hpluslab, hker, hcompat, hweyl, hcomm⟩ :=
    qtwoDB43_model_of hRig hm hBs hSC hinner hBsN hΛ hlab htag hker_char hΘact
  have hplus' : ¬ (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even m) := by
    rcases hD with ⟨hodd, hlabD⟩ | ⟨heven, hlabT⟩
    · intro hiff
      exact (Nat.not_even_iff_odd.mpr hodd) (hiff.mp (hpluslab.mpr hlabD))
    · intro hiff
      have hDl : lab = ⟨.D, m, 1⟩ := hpluslab.mp (hiff.mpr heven)
      have htag' : lab.tag = LargeEvenLieTag.D := congrArg LargeEvenLabel.tag hDl
      rw [hlabT] at htag'
      exact absurd htag' (by intro h; cases h)
  obtain ⟨V₀, hV₀fix, hV₀dim, hV₀nd, hV₀all, hV₀type⟩ :=
    qtwoDB43_plane_of_torus hm hQ hdim hplus' τ hker hweyl
  let β : ↥Bs →* ↥(orthDerived Q) :=
    MonoidHom.mk' (fun s => τ (Multiplicative.ofAdd (βL (Additive.ofMul s)))) (by
      intro s t
      simp only [ofMul_mul, map_add, ofAdd_add, map_mul])
  have hcompat' : ∀ (s : ↥Bs) (n : ↥N),
      σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹ := by
    intro s n
    rw [hcompat s n]
    rfl
  have hV₀ : ∀ x : V, x ∈ V₀ ↔
      ∀ s : ↥Bs, ((β s : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x := by
    intro x
    rw [hV₀fix x]
    constructor
    · intro h s
      exact h (βL (Additive.ofMul s))
    · intro h v
      have hv : τ (Multiplicative.ofAdd v) = β (Additive.toMul (βL.symm v)) := by
        show τ (Multiplicative.ofAdd v) =
          τ (Multiplicative.ofAdd (βL (Additive.ofMul (Additive.toMul (βL.symm v)))))
        congr 1
        simp
      rw [hv]
      exact h _
  have hne : ∃ s : ↥Bs, β s ≠ 1 := by
    obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin m)
      (by rw [Fintype.card_fin]; omega) c
    refine ⟨Additive.toMul (βL.symm (Pi.single c' 1)), fun h => ?_⟩
    have hs : βL (Additive.ofMul (Additive.toMul (βL.symm (Pi.single c' 1)))) =
        Pi.single c' 1 := by simp
    have hτ : τ (Multiplicative.ofAdd (Pi.single c' 1)) = 1 := by
      simpa [β, hs] using h
    have hzero := (hker (Pi.single c' 1)).mp hτ c' hc'
    rw [Pi.single_eq_same] at hzero
    exact one_ne_zero hzero
  have hJ₁pres : ∀ n : ↥N, (n : G) ∈ J₁ → ∀ x ∈ V₀,
      ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x ∈ V₀ := by
    intro n hn x hx
    have hτ1x : ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₁))) : ↥(orthDerived Q)) :
        V ≃ₗ[ZMod 2] V) x = x := (hV₀fix x).mp hx (βL (Additive.ofMul s₁))
    have hcommV : ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) *
        ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₁))) : ↥(orthDerived Q)) :
          V ≃ₗ[ZMod 2] V) =
        ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₁))) : ↥(orthDerived Q)) :
          V ≃ₗ[ZMod 2] V) *
        ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) := by
      simpa using congrArg Subtype.val (hcomm s₁ n (hJ₁c n hn))
    have hfixσ : ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₁))) : ↥(orthDerived Q)) :
        V ≃ₗ[ZMod 2] V) (((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x) =
        ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x := by
      have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) hcommV
      simp only [LinearEquiv.mul_apply] at h
      rw [hτ1x] at h
      exact h.symm
    exact hV₀all (βL (Additive.ofMul s₁)) hs₁ _ hfixσ
  have hJ₁V₀ := qtwoDB43_perfect_fixes_plane hJ₁N hJ₁perf σ hV₀dim hJ₁pres
  have hJ₂pres : ∀ n : ↥N, (n : G) ∈ J₂ → ∀ x ∈ V₀,
      ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x ∈ V₀ := by
    intro n hn x hx
    have hτ2x : ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₂))) :
        ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x = x :=
      (hV₀fix x).mp hx (βL (Additive.ofMul s₂))
    have hcommV : ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) *
        ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₂))) :
          ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) =
        ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₂))) :
          ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) *
        ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) := by
      simpa using congrArg Subtype.val (hcomm s₂ n (hJ₂c n hn))
    have hfixσ : ((τ (Multiplicative.ofAdd (βL (Additive.ofMul s₂))) :
        ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V)
        (((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x) =
        ((σ n : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) x := by
      have h := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) hcommV
      simp only [LinearEquiv.mul_apply] at h
      rw [hτ2x] at h
      exact h.symm
    exact hV₀all (βL (Additive.ofMul s₂)) hs₂ _ hfixσ
  have hJ₂V₀ := qtwoDB43_perfect_fixes_plane hJ₂N hJ₂perf σ hV₀dim hJ₂pres
  exact qtwoDB43_orthY_of_plane hm hBs hSC hBsN hQ hdim σ β hcompat' hne hV₀
    hV₀dim hV₀nd hV₀type hJ₁N hJ₂N hJ₁perf hJ₂perf hJ₁V₀ hJ₂V₀


theorem qtwoDB43_case_orth_big (hRig : GGLabelRigidInput) (hm : 7 ≤ m)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (hD : (Odd m ∧ lab = ⟨.D, m, 1⟩) ∨ (Even m ∧ lab = ⟨.twD, m, 1⟩)) :
    ∃ Y : Subgroup G, qtwoDelJ ψ c ≤ Y ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ Y ∧
      ∃ Φ : OrthTorus.OrthFrameCore 3 Bs Y, Nat.card Φ.F = 2 ∧ Φ.r = m - 1 ∧
        Subgroup.center ↥Y = ⊥ := by
  have hstar : GGBstar 3 B Bs := hbase.p_eq ▸ hcfg.1.1.1.2.1
  have hinner : GGInnerDiagOn Bs N :=
    ggQTwoDUnit_innerDiag_N hcfg hm hbase hcoords hdel hb'B hN hJ₁ hJ₂
  have hBsN : Bs ≤ Subgroup.normalizer (N : Set G) := hinner.le_normalizer
  obtain ⟨Θ, -, hΘact⟩ := qtwoDB36_weyl_embed (by omega) hbase hcoords hdel hN hJ₁ hJ₂ hBsN
  have hJ₁perf : ⁅qtwoDelJ ψ c, qtwoDelJ ψ c⁆ = qtwoDelJ ψ c :=
    le_antisymm (Subgroup.commutator_le_self _) (qtwoDB16_J_perfect (by omega) hbase)
  have hJ₂perf : ⁅(qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom,
      (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom⁆ =
      (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, hJ₁perf]
  refine qtwoDB43_case_orth_big_of hRig (by omega) hstar.2.1 hstar.2.2.2 hinner hBsN hΛ hlab hD
    (qtwoDB36_gamma (by omega) hbase hcoords hdel hN hJ₁ hJ₂ hBsN).1 hΘact hJ₁ hJ₁perf
    (s₁ := ⟨x, hbase.x_mem⟩) ?_ (fun n hn => qtwoDB43_x_commute_J₁ hbase hn) hJ₂ hJ₂perf
    (s₂ := α ⟨x, hbase.x_mem⟩) ?_ (fun n hn => qtwoDB43_x_commute_J₂ hbase hdel hn)
  · intro i _
    rw [hcoords.x_coord hbase.x_mem]
    exact one_ne_zero
  · intro i _
    rw [hdel.sign ⟨x, hbase.x_mem⟩, hcoords.x_coord hbase.x_mem,
      show (fun _ : Fin m => (1 : ZMod 3)) = (1 : DVec m) from rfl, qtwoDB16_dSign_one_apply]
    split_ifs with h
    · show ((-1 : ZMod 3)) ≠ 0
      exact neg_ne_zero.mpr one_ne_zero
    · show ((1 : ZMod 3)) ≠ 0
      exact one_ne_zero

end CFSG.StandardType.QTwo

end
