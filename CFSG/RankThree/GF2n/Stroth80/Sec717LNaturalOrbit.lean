module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec717PairingCore
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec717L_naturalModule_of (hTyp : Sec717LTypingStatement) {G : Type} [Group G]
    [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZ0N : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {L : Subgroup G} (hL : Sec717L hc t Z0 L) (hLn : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L)
    [(Z0.subgroupOf L).Normal] (hXcomm : ∀ a b : ↥L ⧸ Z0.subgroupOf L, a * b = b * a)
    {K : Type} [Field K] [Finite K] (hKZ : Nat.card K = Nat.card Z)
    (φ₀ : ↥(Rt M (LB M Q B) t) →* GL (Fin 3 ⊕ Fin 3) K)
    (hφker : ∀ h, φ₀ h = 1 ↔ (h : G) ∈ hc.CN t) :
    letI : CommGroup (↥L ⧸ Z0.subgroupOf L) := sec717CommGroup hXcomm
    ∃ (η : ↥(Rt M (LB M Q B) t) →* Matrix.SpecialLinearGroup (Fin 4) K)
      (ψ : Additive (↥L ⧸ Z0.subgroupOf L) ≃+ (Fin 4 → K)),
      Function.Surjective η ∧ (∀ h, η h = 1 ↔ φ₀ h = 1) ∧
      ∀ (h : ↥(Rt M (LB M Q B) t)) (a : ↥L) (ha : (h : G) * a * (h : G)⁻¹ ∈ L),
        ψ (Additive.ofMul (QuotientGroup.mk ⟨(h : G) * a * (h : G)⁻¹, ha⟩)) =
          η h • ψ (Additive.ofMul (QuotientGroup.mk a)) := by
  classical
  letI : CommGroup (↥L ⧸ Z0.subgroupOf L) := sec717CommGroup hXcomm
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQL : Q ≤ L := hL.1
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLH : L ≤ H0 M Z := hL.2.1.trans (hNR.trans hRH)
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ₁, hφπ₁, hφker₁, -⟩ := exists_actionHom_H0 hc.hyp hM
  obtain ⟨φ, -, hφmk⟩ := exists_barAct hQH hHM φ₁ hφker₁
  have hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z))
      (x : G), x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x) := by
    intro y hy x hx
    have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hQH y).mp hy
    rw [hφmk y hy hyH]
    exact hφπ₁ ⟨(y : G), hyH⟩ x hx
  obtain ⟨η₁, hη₁s, hη₁k, θ₁, hθ₁s, hθ₁k, hθ₁e⟩ :=
    hTyp G M Q Z B hc n t hs hp3 Z0 hZ0 hZ0N hTI L hL hLn m γ M₀ hM φ hφπ
  haveI := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 m) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hM.card, hKZ]
  let σ : GaloisField 2 m ≃+* K := FiniteField.ringEquivOfCardEq hcard
  let π : ↥(Rt M (LB M Q B) t) →*
      ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) :=
    MonoidHom.codRestrict
      (MonoidHom.codRestrict ((QuotientGroup.mk' (Q.subgroupOf M)).comp
        (Subgroup.inclusion (hc.Rt_le_M t))) (bar M Q (H0 M Z)) fun x =>
          (mk_mem_bar_iff_sec4 hQH _).mpr (hRH x.2))
      _ fun x => Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr x.2)
  let lam : ↥L →* ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) :=
    MonoidHom.codRestrict
      (MonoidHom.codRestrict ((QuotientGroup.mk' (Q.subgroupOf M)).comp
        (Subgroup.inclusion (hLH.trans hHM))) (bar M Q (H0 M Z)) fun x =>
          (mk_mem_bar_iff_sec4 hQH _).mpr (hLH x.2))
      _ fun x => Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQL _).mpr x.2)
  have hπs : Function.Surjective π := by
    intro r
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M)
      ((r : ↥(bar M Q (H0 M Z))) : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp r.2)
    exact ⟨⟨(y : G), hyR⟩, Subtype.ext (Subtype.ext hy)⟩
  have hlams : Function.Surjective lam := by
    intro l
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M)
      ((l : ↥(bar M Q (H0 M Z))) : Mbar M Q)
    have hyL : (y : G) ∈ L :=
      (mk_mem_bar_iff_sec4 hQL y).mp (hy ▸ Subgroup.mem_subgroupOf.mp l.2)
    exact ⟨⟨(y : G), hyL⟩, Subtype.ext (Subtype.ext hy)⟩
  have hπN : ∀ x, ((π x : ↥(bar M Q (H0 M Z)))) ∈
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ↔ (x : G) ∈ hc.CN t := fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact mk_mem_bar_iff_sec4 hQN _
  have hlamV : ∀ a, ((lam a : ↥(bar M Q (H0 M Z)))) ∈
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ↔ (a : G) ∈ Z0 := fun a => by
    rw [Subgroup.mem_subgroupOf]
    exact mk_mem_bar_iff_sec4 hQZ0 _
  let η : ↥(Rt M (LB M Q B) t) →* Matrix.SpecialLinearGroup (Fin 4) K :=
    (Matrix.SpecialLinearGroup.map σ.toRingHom).comp (η₁.comp π)
  have hmapinj : ∀ A : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m),
      Matrix.SpecialLinearGroup.map σ.toRingHom A = 1 → A = 1 := by
    intro A hA
    ext i j
    have h1 := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 4) K => σ.symm (B i j)) hA
    simpa [Matrix.one_apply, apply_ite] using h1
  have hηs : Function.Surjective η := by
    intro A
    obtain ⟨r, hr⟩ := hη₁s (Matrix.SpecialLinearGroup.map σ.symm.toRingHom A)
    obtain ⟨x, rfl⟩ := hπs r
    refine ⟨x, ?_⟩
    ext i j
    change σ ((η₁ (π x) : Matrix (Fin 4) (Fin 4) (GaloisField 2 m)) i j) = A i j
    rw [hr]
    simp
  have hηk : ∀ h, η h = 1 ↔ φ₀ h = 1 := by
    intro h
    rw [hφker, ← hπN, ← hη₁k]
    constructor
    · exact hmapinj _
    · intro h1
      change Matrix.SpecialLinearGroup.map σ.toRingHom (η₁ (π h)) = 1
      rw [h1, map_one]
  let f : ↥L →* Multiplicative (Fin 4 → GaloisField 2 m) := θ₁.comp lam
  have hfs : Function.Surjective f := hθ₁s.comp hlams
  have hfker : f.ker = Z0.subgroupOf L := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, hθ₁k, hlamV]
  let e₁ : (↥L ⧸ Z0.subgroupOf L) ≃* Multiplicative (Fin 4 → GaloisField 2 m) :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)
  let σ' : Multiplicative (Fin 4 → GaloisField 2 m) ≃* Multiplicative (Fin 4 → K) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  let ψ : Additive (↥L ⧸ Z0.subgroupOf L) ≃+ (Fin 4 → K) :=
    MulEquiv.toAdditiveLeft (e₁.trans σ')
  have hψ : ∀ a : ↥L, ψ (Additive.ofMul (QuotientGroup.mk a)) =
      σ ∘ Multiplicative.toAdd (θ₁ (lam a)) := fun a => rfl
  refine ⟨η, ψ, hηs, hηk, fun h a ha => ?_⟩
  rw [hψ, hψ]
  have hconj : ((lam ⟨(h : G) * a * (h : G)⁻¹, ha⟩ : ↥(bar M Q (H0 M Z)))) =
      (π h : ↥(bar M Q (H0 M Z))) * lam a * (π h : ↥(bar M Q (H0 M Z)))⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    show QuotientGroup.mk' (Q.subgroupOf M) ⟨(h : G) * a * (h : G)⁻¹, _⟩ =
      QuotientGroup.mk' (Q.subgroupOf M) ⟨(h : G), _⟩ * QuotientGroup.mk' (Q.subgroupOf M)
        ⟨(a : G), _⟩ * (QuotientGroup.mk' (Q.subgroupOf M) ⟨(h : G), _⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [hθ₁e (π h) (lam a) _ hconj, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  funext i
  exact RingHom.map_mulVec (σ : GaloisField 2 m →+* K) _ _ i

end CFSG.RankThree.GF2n.Stroth80
