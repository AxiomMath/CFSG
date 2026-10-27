module

public import CFSG.RankThree.GF2n.Stroth80.CarterSec11OmegaAudit

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem exists_naturalRep_cmComm
    (hc : Ctx M Q Z B) {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (d : ℕ) (hd : Module.finrank K (cmComm M Q Z B K γ M₀ φ) = d)
    (hfaith : ∀ s : ↥(XbarPre M Q Z B),
      (∀ e ∈ cmComm M Q Z B K γ M₀ φ, φ ⟨s, XbarPre_le_H0 hc s.2⟩ e = e) → (s : G) ∈ Q) :
    ∃ X : Subgroup (GL (Fin d) K),
      NaturalRep (ι := Fin d) K X (XbarPre M Q Z B) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) Z (Q) := by
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
  haveI := hZnorm
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
  refine ⟨Φhom.range, Φhom, rfl, hΦker, ?_, ?_, ψ, ?_⟩
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

theorem cmComm_map_eq_self_of_mem_XbarH
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (h : ↥(XbarH M Q Z B)) :
    Submodule.map ((φ h.1 : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E)
      (cmComm M Q Z B K γ M₀ φ) = cmComm M Q Z B K γ M₀ φ := by
  have h' : (h.1 : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc h.1).mp h.2
  have hmap := cmComm_invariant hc φ ⟨(h.1 : G), h'⟩
  have hφ : (⟨(h.1 : G), XbarPre_le_H0 hc h'⟩ : ↥(H0 M Z)) = h.1 := Subtype.ext rfl
  rw [hφ] at hmap
  exact hmap

theorem exists_psu4_module_data {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (h8 : Module.finrank K (cmComm M Q Z B K γ M₀ φ) = 8)
    (hfaith : ∀ s : ↥(XbarPre M Q Z B),
      (∀ e ∈ cmComm M Q Z B K γ M₀ φ, φ ⟨s, XbarPre_le_H0 hc s.2⟩ e = e) → (s : G) ∈ Q) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = Nat.card Z ∧
      ∃ X : Subgroup (GL (Fin 8) K'),
        NaturalRep (ι := Fin 8) K' X (XbarPre M Q Z B) (Z ⊔ ⁅Q, XbarPre M Q Z B⁆) Z (Q) := by
  obtain ⟨X, hX⟩ := exists_naturalRep_cmComm hc hD φ hφπ φker 8 h8 hfaith
  exact ⟨K, inferInstance, inferInstance, hD.card, X, hX⟩

end CFSG.RankThree.GF2n.Stroth80
