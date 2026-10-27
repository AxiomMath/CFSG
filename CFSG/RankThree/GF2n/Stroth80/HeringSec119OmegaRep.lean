module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec11OmegaAudit

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem exists_naturalRep_cmComm_of_irreducible
    (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (d : ℕ) (hd : Module.finrank K (cmComm M Q Z B K γ M₀ φ) = d)
    (hfaith : ∀ s : ↥(XbarPre M Q Z B),
      (∀ e ∈ cmComm M Q Z B K γ M₀ φ, φ ⟨s, XbarPre_le_H0 hc s.2⟩ e = e) → (s : G) ∈ Q)
    (hirr : ∀ U : Submodule K M₀.E, U ≤ cmComm M Q Z B K γ M₀ φ →
      (∀ s : ↥(XbarPre M Q Z B), ∀ u ∈ U, φ ⟨s, XbarPre_le_H0 hc s.2⟩ u ∈ U) →
        U = ⊥ ∨ U = cmComm M Q Z B K γ M₀ φ) :
    ∃ X : Subgroup (GL (Fin d) K),
      NaturalRep (ι := Fin d) K X (XbarPre M Q Z B) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) Z (Q) ∧
        ∀ W : Submodule K (Fin d → K),
          (∀ g ∈ X, ∀ w ∈ W, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w ∈ W) →
            W = ⊥ ∨ W = ⊤ := by
  classical
  let V : Subgroup G := Z ⊔ ⁅Q, XbarPre M Q Z B⁆
  have hZQ : Z ≤ Q := by
    rw [hc.hyp.hZ, cen_eq]
    exact inf_le_left
  have hVQ : V ≤ Q := sup_le hZQ (commutator_le_Q hc)
  let C : Submodule K M₀.E := cmComm M Q Z B K γ M₀ φ
  let b : Module.Basis (Fin d) K C := Module.finBasisOfFinrankEq K C hd
  let e : C ≃ₗ[K] (Fin d → K) := b.equivFun
  have hπV : ∀ v : ↥V, M₀.π (v : G) ∈ C := by
    let Kc : Subgroup G :=
      { carrier := {x | x ∈ Q ∧ M₀.π x ∈ C}
        one_mem' := ⟨Q.one_mem, by rw [pi_one]; exact C.zero_mem⟩
        mul_mem' := by
          rintro x y ⟨hxQ, hxπ⟩ ⟨hyQ, hyπ⟩
          exact ⟨Q.mul_mem hxQ hyQ, by
            rw [M₀.π_mul x hxQ y hyQ]
            exact C.add_mem hxπ hyπ⟩
        inv_mem' := by
          rintro x ⟨hxQ, hxπ⟩
          exact ⟨Q.inv_mem hxQ, by
            rw [pi_inv hxQ]
            exact C.neg_mem hxπ⟩ }
    have hZle : Z ≤ Kc := by
      intro z hz
      exact ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]
        exact C.zero_mem⟩
    have hCle : ⁅Q, XbarPre M Q Z B⁆ ≤ Kc := by
      intro x hx
      exact ⟨commutator_le_Q hc hx,
        (mem_cmComm_iff hc hD φ hφπ (M₀.π x)).mpr ⟨x, hx, rfl⟩⟩
    have hVle : V ≤ Kc := sup_le hZle hCle
    exact fun v => (hVle v.2).2
  let piC : ↥V → C := fun v => ⟨M₀.π (v : G), hπV v⟩
  let f : ↥V →* Multiplicative (Fin d → K) :=
    { toFun := fun v => Multiplicative.ofAdd (e (piC v))
      map_one' := by
        show Multiplicative.ofAdd (e (piC 1)) = 1
        have h : piC 1 = 0 := by
          apply Subtype.ext
          exact pi_one
        rw [h, map_zero]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (e (piC (a * b))) =
          Multiplicative.ofAdd (e (piC a)) * Multiplicative.ofAdd (e (piC b))
        have h : piC (a * b) = piC a + piC b := by
          apply Subtype.ext
          exact M₀.π_mul (a : G) (hVQ a.2) (b : G) (hVQ b.2)
        rw [h, map_add, ofAdd_add] }
  have hf_surj : Function.Surjective f := by
    intro y
    let x : C := e.symm (Multiplicative.toAdd y)
    obtain ⟨xg, hxg, hπxg⟩ :=
      (mem_cmComm_iff hc hD φ hφπ (x : M₀.E)).mp x.2
    have hxgV : xg ∈ V := Subgroup.mem_sup_right hxg
    refine ⟨⟨xg, hxgV⟩, ?_⟩
    show Multiplicative.ofAdd (e (piC ⟨xg, hxgV⟩)) = y
    have hpi : piC ⟨xg, hxgV⟩ = x := Subtype.ext hπxg
    rw [hpi]
    show Multiplicative.ofAdd (e x) = y
    have hx : e x = Multiplicative.toAdd y := by
      dsimp only [x]
      exact e.apply_symm_apply _
    rw [hx]
    exact ofAdd_toAdd y
  have hf_ker : f.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (e (piC v)) = 1 ↔ (v : G) ∈ Z
    rw [ofAdd_eq_one, ← map_zero e, e.injective.eq_iff]
    constructor
    · intro h
      have hπ : M₀.π (v : G) = 0 := by
        exact congrArg (fun x : C => (x : M₀.E)) h
      exact (M₀.π_ker (v : G) (hVQ v.2)).mp hπ
    · intro hv
      apply Subtype.ext
      show M₀.π (v : G) = 0
      exact (M₀.π_ker (v : G) (hZQ hv)).mpr hv
  have hZnorm : (Z.subgroupOf V).Normal := Z_subgroupOf_sup_comm_normal hc
  have := hZnorm
  let ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (Fin d → K) :=
    (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf_surj)
  have hψ_mk : ∀ x : ↥V, ψ (QuotientGroup.mk x) = f x := by
    intro x
    change (QuotientGroup.kerLift f) (QuotientGroup.mk x) = f x
    rfl
  let ssOf : ↥(XbarPre M Q Z B) → ↥(H0 M Z) := fun s => ⟨s, XbarPre_le_H0 hc s.2⟩
  let Ts : ↥(XbarPre M Q Z B) → (C ≃ₗ[K] C) := fun s =>
    LinearEquiv.ofBijective
      (((φ (ssOf s) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E).restrict (p := C) (q := C)
        (fun x hx => by
          have hx' : (φ (ssOf s)) x ∈ Submodule.map
              ((φ (ssOf s) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) C :=
            Submodule.mem_map.mpr ⟨x, hx, rfl⟩
          rwa [cmComm_invariant hc φ s] at hx'))
      ⟨fun x y hxy => by
        apply Subtype.ext
        exact (φ (ssOf s)).injective (Subtype.ext_iff.mp hxy),
       fun y => by
        have hy : (y : M₀.E) ∈ Submodule.map
            ((φ (ssOf s) : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) C := by
          rw [cmComm_invariant hc φ s]
          exact y.2
        obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let Ψ : ↥(XbarPre M Q Z B) →* (C ≃ₗ[K] C) :=
    { toFun := Ts
      map_one' := by
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        change (φ (ssOf 1)) (x : M₀.E) = (x : M₀.E)
        rw [show ssOf 1 = 1 from Subtype.ext rfl, map_one]
        rfl
      map_mul' := fun s t => by
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        change (φ (ssOf (s * t))) (x : M₀.E) =
          (φ (ssOf s)) ((φ (ssOf t)) (x : M₀.E))
        rw [show ssOf (s * t) = ssOf s * ssOf t from Subtype.ext rfl, map_mul,
          LinearEquiv.mul_apply] }
  let Φ : (C ≃ₗ[K] C) ≃* GL (Fin d) K :=
    (Matrix.GeneralLinearGroup.toLin' b |>.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K C)).symm
  let Φhom : ↥(XbarPre M Q Z B) →* GL (Fin d) K := Φ.toMonoidHom.comp Ψ
  have hΦ : ∀ (T : C ≃ₗ[K] C) (x : C),
      ((Φ T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ e x = e (T x) := by
    intro T x
    have hlin := Matrix.GeneralLinearGroup.toLin'_apply (b := b) (M := Φ T) (v := x)
    have hlt : (Matrix.GeneralLinearGroup.toLin' b (Φ T)).toLinearEquiv x = T x := by
      change (Matrix.GeneralLinearGroup.toLin' b
        ((Matrix.GeneralLinearGroup.toLin' b).symm
          ((LinearMap.GeneralLinearGroup.generalLinearEquiv K C).symm T))).toLinearEquiv x =
        T x
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hlt] at hlin
    have hx : e (T x) = ((Φ T : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) *ᵥ e x := by
      rw [hlin]
      have hsum : (Fintype.linearCombination K ⇑b) (↑(Φ T) *ᵥ ↑(b.repr x)) =
          b.equivFun.symm (↑(Φ T) *ᵥ ↑(b.repr x)) := by
        rw [Module.Basis.equivFun_symm_apply, Fintype.linearCombination_apply]
      rw [hsum, e.apply_symm_apply]
      rfl
    exact hx.symm
  have hΦker : Φhom.ker = Q.subgroupOf (XbarPre M Q Z B) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change Φ (Ψ s) = 1 ↔ (s : G) ∈ Q
    rw [← map_one Φ, Φ.injective.eq_iff]
    constructor
    · intro h
      apply hfaith s
      intro x hx
      have hxT : Ψ s ⟨x, hx⟩ = ⟨x, hx⟩ := by
        rw [h]
        rfl
      exact congrArg Subtype.val hxT
    · intro hs
      apply LinearEquiv.ext
      intro x
      apply Subtype.ext
      change (φ (ssOf s)) (x : M₀.E) = (x : M₀.E)
      rw [show φ (ssOf s) = 1 from (φker (ssOf s)).mpr hs]
      rfl
  have hirrX : ∀ W : Submodule K (Fin d → K),
      (∀ g ∈ Φhom.range, ∀ w ∈ W, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let U : Submodule K M₀.E := (W.comap (e : C →ₗ[K] (Fin d → K))).map C.subtype
    have hUC : U ≤ C := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have hUinv : ∀ s : ↥(XbarPre M Q Z B), ∀ u ∈ U, φ ⟨s, XbarPre_le_H0 hc s.2⟩ u ∈ U := by
      rintro s _ ⟨c, hcW, rfl⟩
      refine ⟨Ts s c, ?_, rfl⟩
      change e (Ts s c) ∈ W
      rw [← hΦ (Ts s) c]
      exact hW (Φhom s) ⟨s, rfl⟩ (e c) hcW
    rcases hirr U hUC hUinv with hU | hU
    · left
      refine (Submodule.eq_bot_iff W).mpr fun w hw => ?_
      have hmem : ((e.symm w : C) : M₀.E) ∈ U :=
        ⟨e.symm w, by simpa using hw, rfl⟩
      rw [hU, Submodule.mem_bot] at hmem
      have h0 : e.symm w = 0 := Subtype.ext hmem
      rw [← e.apply_symm_apply w, h0, map_zero]
    · right
      refine (Submodule.eq_top_iff').mpr fun w => ?_
      have hmem : ((e.symm w : C) : M₀.E) ∈ U := by
        rw [hU]
        exact (e.symm w).2
      obtain ⟨c, hcW, hc'⟩ := hmem
      have hceq : c = e.symm w := Subtype.ext hc'
      rw [hceq] at hcW
      simpa using hcW
  refine ⟨Φhom.range, ⟨Φhom, rfl, hΦker, ?_, ?_, ψ, ?_⟩, hirrX⟩
  · exact XbarPre_le_normalizer_sup_comm hc
  · exact hZnorm
  · intro s v w hw
    rw [hψ_mk w, hψ_mk v]
    have hwπ : M₀.π (w : G) = φ (ssOf s) (M₀.π (v : G)) := by
      rw [hw]
      exact hφπ (ssOf s) (v : G) (hVQ v.2)
    calc
      Multiplicative.toAdd (f w) = e (piC w) := rfl
      _ = e ((Ts s) (piC v)) := by
        rw [show piC w = Ts s (piC v) from Subtype.ext hwπ]
      _ = ((Φ (Ts s) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ e (piC v) :=
        (hΦ (Ts s) (piC v)).symm
      _ = ((Φhom s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
            Multiplicative.toAdd (f v) := rfl

end CFSG.RankThree.GF2n.Stroth80
