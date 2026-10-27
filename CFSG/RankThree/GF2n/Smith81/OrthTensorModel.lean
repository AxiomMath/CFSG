module

public import CFSG.RankThree.GF2n.Smith81.OrthAct
public import CFSG.RankThree.GF2n.Smith81.OrthSetup
public import CFSG.RankThree.GF2n.Smith81.ELayer
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndClassical
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.RankThree.GF2n.Smith81

section PartA

open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Smith81 QuadraticMap

section Hyperbolic

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] [Finite K] {γ : G → K}

theorem orth_polar_eq_dotProduct_gram {ι : Type} [Fintype ι] [DecidableEq ι]
    (qU : QuadraticForm K (ι → K)) (u v : ι → K) :
    polar qU u v = u ⬝ᵥ (LinearMap.BilinForm.toMatrix' (polarBilin qU)).mulVec v := by
  have h := Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (polarBilin qU)) u v
  rw [Matrix.toBilin'_toMatrix'] at h
  simpa [QuadraticMap.polarBilin_apply_apply] using h

theorem orth_exists_gram_equiv {ι : Type} [Fintype ι] [DecidableEq ι] (qU : QuadraticForm K (ι → K))
    (hnd : ∀ u : ι → K, (∀ v : ι → K, polar qU u v = 0) → u = 0) :
    ∃ T : (ι → K) ≃ₗ[K] (ι → K), ∀ u y, polar qU u (T y) = u ⬝ᵥ y := by
  set J := LinearMap.BilinForm.toMatrix' (polarBilin qU) with hJ
  have hinj : Function.Injective (Matrix.mulVecLin J) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : J.mulVec v = 0 := hv
    refine hnd v fun u => ?_
    rw [polar_comm, orth_polar_eq_dotProduct_gram, ← hJ, hv', dotProduct_zero]
  let Jeq : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofInjectiveEndo (Matrix.mulVecLin J) hinj
  refine ⟨Jeq.symm, fun u y => ?_⟩
  rw [orth_polar_eq_dotProduct_gram, ← hJ]
  have h1 : J.mulVec (Jeq.symm y) = y := by
    have := Jeq.apply_symm_apply y
    rwa [show Jeq (Jeq.symm y) = J.mulVec (Jeq.symm y) from rfl] at this
  rw [h1]

end Hyperbolic

end PartA

section PartB

open QuadraticMap
open scoped Matrix commutatorElement

section TensorCore

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [AddCommGroup E] [Module K E]
  [Module.Finite K E] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure TensorCoreHyp (Qf : E → K) (B : E →ₗ[K] E →ₗ[K] K) (qU : QuadraticForm K (ι → K))
    (Ω : Subgroup ((ι → K) ≃ₗ[K] (ι → K))) (GX GA : Subgroup (E ≃ₗ[K] E))
    (ν : (ι → K) →ₗ[K] E) (ψ : E →ₗ[K] E) : Prop where
  qadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f
  nondegB : ∀ e, (∀ f, B e f = 0) → e = 0
  nondegU : ∀ u : ι → K, (∀ v, polar qU u v = 0) → u = 0
  omega_isom : ∀ o ∈ Ω, ∀ v, qU (o v) = qU v
  omega_comm : ∀ f : (ι → K) →ₗ[K] (ι → K), (∀ o ∈ Ω, ∀ u, f (o u) = o (f u)) →
    ∃ c : K, ∀ u, f u = c • u
  nu_inj : Function.Injective ν
  x_isom : ∀ x ∈ GX, ∀ e, Qf (x e) = Qf e
  a_isom : ∀ a ∈ GA, ∀ e, Qf (a e) = Qf e
  a_comm_x : ∀ a ∈ GA, ∀ x ∈ GX, a * x = x * a
  x_inv : ∀ x ∈ GX, ∃ o ∈ Ω, ∀ u, x (ν u) = ν (o u)
  x_surj : ∀ o ∈ Ω, ∃ x ∈ GX, ∀ u, x (ν u) = ν (o u)
  irr : ∀ S : Submodule K E, S ≤ LinearMap.range ν → (∀ x ∈ GX, ∀ v ∈ S, x v ∈ S) →
    S = ⊥ ∨ S = LinearMap.range ν
  psi_comm : ∀ x ∈ GX, ∀ e, x (ψ e) = ψ (x e)
  psi_range : LinearMap.range ψ = LinearMap.range ν
  psi_ker : LinearMap.ker ψ = LinearMap.range ν
  w_sing : ∀ u, Qf (ν u) = 0
  a_perfect : ⁅GA, GA⁆ = GA
  a_nonabelian : ∃ a ∈ GA, ∃ b ∈ GA, a * b ≠ b * a
  a_card : Nat.card GA = Nat.card K * (Nat.card K ^ 2 - 1)

theorem orthTensor_id_mul (g g' : Matrix (Fin 2) (Fin 2) K) (p : (ι → K) × (ι → K)) :
    orthTensor g (fun v => v) (orthTensor g' (fun v => v) p) =
      orthTensor (g * g') (fun v => v) p := by
  refine Prod.ext ?_ ?_
  · simp only [orthTensor, Matrix.mul_apply, Fin.sum_univ_two]
    module
  · simp only [orthTensor, Matrix.mul_apply, Fin.sum_univ_two]
    module

theorem orthTensor_id_one (p : (ι → K) × (ι → K)) :
    orthTensor (1 : Matrix (Fin 2) (Fin 2) K) (fun v => v) p = p := by
  ext <;> simp [orthTensor]

theorem orthTensor_id_inj {g g' : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ p : (ι → K) × (ι → K), orthTensor g (fun v => v) p = orthTensor g' (fun v => v) p) :
    g = g' := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have e1 : ∀ u : ι → K, u i₀ = 1 → g 0 0 = g' 0 0 ∧ g 1 0 = g' 1 0 := by
    intro u hu
    have := h (u, 0)
    simp only [orthTensor, smul_zero, add_zero, Prod.mk.injEq] at this
    obtain ⟨a, b⟩ := this
    have a' := congrFun a i₀
    have b' := congrFun b i₀
    simp [hu] at a' b'
    exact ⟨a', b'⟩
  have e2 : ∀ u : ι → K, u i₀ = 1 → g 0 1 = g' 0 1 ∧ g 1 1 = g' 1 1 := by
    intro u hu
    have := h (0, u)
    simp only [orthTensor, smul_zero, zero_add, Prod.mk.injEq] at this
    obtain ⟨a, b⟩ := this
    have a' := congrFun a i₀
    have b' := congrFun b i₀
    simp [hu] at a' b'
    exact ⟨a', b'⟩
  have hu : (Pi.single i₀ (1 : K) : ι → K) i₀ = 1 := by simp
  obtain ⟨h00, h10⟩ := e1 _ hu
  obtain ⟨h01, h11⟩ := e2 _ hu
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[expose] def TensorActsAs (φ : E ≃ₗ[K] (ι → K) × (ι → K)) (a : E ≃ₗ[K] E) (g : Matrix (Fin 2) (Fin 2) K) :
    Prop :=
  ∀ e, φ (a e) = orthTensor g (fun v => v) (φ e)

theorem TensorActsAs.mul {φ : E ≃ₗ[K] (ι → K) × (ι → K)} {a b : E ≃ₗ[K] E}
    {g g' : Matrix (Fin 2) (Fin 2) K} (ha : TensorActsAs φ a g) (hb : TensorActsAs φ b g') :
    TensorActsAs φ (a * b) (g * g') := by
  intro e
  rw [LinearEquiv.mul_apply, ha, hb, orthTensor_id_mul]

theorem TensorActsAs.one (φ : E ≃ₗ[K] (ι → K) × (ι → K)) : TensorActsAs φ 1 1 := by
  intro e
  rw [orthTensor_id_one]; rfl

theorem TensorActsAs.unique {φ : E ≃ₗ[K] (ι → K) × (ι → K)} {a : E ≃ₗ[K] E}
    {g g' : Matrix (Fin 2) (Fin 2) K} (ha : TensorActsAs φ a g) (ha' : TensorActsAs φ a g') : g = g' := by
  refine orthTensor_id_inj (ι := ι) fun p => ?_
  have h1 := ha (φ.symm p)
  have h2 := ha' (φ.symm p)
  rw [LinearEquiv.apply_symm_apply] at h1 h2
  rw [← h1, ← h2]

theorem TensorActsAs.mul_inv {φ : E ≃ₗ[K] (ι → K) × (ι → K)} {a : E ≃ₗ[K] E}
    {g g' : Matrix (Fin 2) (Fin 2) K} (ha : TensorActsAs φ a g) (ha' : TensorActsAs φ a⁻¹ g') :
    g * g' = 1 := by
  have := ha.mul ha'
  rw [mul_inv_cancel] at this
  exact this.unique (TensorActsAs.one φ)

@[expose] def OrthHasInvCompl (GX : Subgroup (E ≃ₗ[K] E)) (ν : (ι → K) →ₗ[K] E) : Prop :=
  ∃ W' : Submodule K E, IsCompl (LinearMap.range ν) W' ∧ ∀ x ∈ GX, ∀ v ∈ W', x v ∈ W'

namespace TensorCoreHyp

variable {Qf : E → K} {B : E →ₗ[K] E →ₗ[K] K} {qU : QuadraticForm K (ι → K)}
  {Ω : Subgroup ((ι → K) ≃ₗ[K] (ι → K))} {GX GA : Subgroup (E ≃ₗ[K] E)}
  {ν : (ι → K) →ₗ[K] E} {ψ : E →ₗ[K] E} (h : TensorCoreHyp Qf B qU Ω GX GA ν ψ)

include h

theorem B_eq (e f : E) : B e f = Qf (e + f) - Qf e - Qf f := by
  rw [h.qadd]; ring

theorem x_B {x : E ≃ₗ[K] E} (hx : x ∈ GX) (e f : E) : B (x e) (x f) = B e f := by
  rw [h.B_eq, h.B_eq e f, ← map_add, h.x_isom x hx, h.x_isom x hx, h.x_isom x hx]

theorem omega_polar {o : (ι → K) ≃ₗ[K] (ι → K)} (ho : o ∈ Ω) (u v : ι → K) :
    polar qU (o u) (o v) = polar qU u v := by
  simp only [QuadraticMap.polar, ← map_add, h.omega_isom o ho]

theorem scalar_on_W (f : E →ₗ[K] E) (hcomm : ∀ x ∈ GX, ∀ e, x (f e) = f (x e))
    (hW : ∀ u, f (ν u) ∈ LinearMap.range ν) : ∃ c : K, ∀ u, f (ν u) = c • ν u := by
  let e : (ι → K) ≃ₗ[K] LinearMap.range ν := LinearEquiv.ofInjective ν h.nu_inj
  have he : ∀ u, (e u : E) = ν u := fun u => rfl
  let f' : (ι → K) →ₗ[K] (ι → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.codRestrict (LinearMap.range ν) (f ∘ₗ ν) hW)
  have hf' : ∀ u, ν (f' u) = f (ν u) := by
    intro u
    have h1 : e (f' u) = ⟨f (ν u), hW u⟩ := by
      simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    simpa [he] using h2
  obtain ⟨c, hc⟩ := h.omega_comm f' (by
    intro o ho u
    obtain ⟨x, hx, hxo⟩ := h.x_surj o ho
    apply h.nu_inj
    rw [hf', ← hxo, ← hcomm x hx, ← hf', hxo])
  exact ⟨c, fun u => by rw [← hf', hc, map_smul]⟩

theorem finrank_E : Module.finrank K E = 2 * Module.finrank K (LinearMap.range ν) := by
  have := LinearMap.finrank_range_add_finrank_ker ψ
  rw [h.psi_range, h.psi_ker] at this
  omega

theorem range_inv {x : E ≃ₗ[K] E} (hx : x ∈ GX) {v : E} (hv : v ∈ LinearMap.range ν) :
    x v ∈ LinearMap.range ν := by
  obtain ⟨u, rfl⟩ := hv
  obtain ⟨o, -, ho⟩ := h.x_inv x hx
  exact ⟨_, (ho u).symm⟩

theorem quot_simple (T : Submodule K E) (hWT : LinearMap.range ν ≤ T)
    (hT : ∀ x ∈ GX, ∀ v ∈ T, x v ∈ T) : T = LinearMap.range ν ∨ T = ⊤ := by
  have hS : T.map ψ ≤ LinearMap.range ν := by
    rw [← h.psi_range]
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  have hSinv : ∀ x ∈ GX, ∀ v ∈ T.map ψ, x v ∈ T.map ψ := by
    rintro x hx _ ⟨t, ht, rfl⟩
    exact ⟨x t, hT x hx t ht, (h.psi_comm x hx t).symm⟩
  rcases h.irr _ hS hSinv with h0 | h1
  · left
    refine le_antisymm (fun t ht => ?_) hWT
    have : ψ t ∈ T.map ψ := ⟨t, ht, rfl⟩
    rw [h0] at this
    have : ψ t = 0 := this
    rw [← h.psi_ker]
    exact this
  · right
    rw [eq_top_iff]
    intro e _
    have : ψ e ∈ T.map ψ := by
      rw [h1, ← h.psi_range]
      exact ⟨e, rfl⟩
    obtain ⟨t, ht, hte⟩ := this
    have : e - t ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_sub, hte, sub_self]
    rw [h.psi_ker] at this
    have := T.add_mem (hWT this) ht
    simpa using this

theorem le_or_hasInvCompl (S : Submodule K E) (hS : ∀ x ∈ GX, ∀ v ∈ S, x v ∈ S)
    (hfr : Module.finrank K S ≤ Module.finrank K (LinearMap.range ν)) :
    S ≤ LinearMap.range ν ∨ OrthHasInvCompl GX ν := by
  have hT : ∀ x ∈ GX, ∀ v ∈ LinearMap.range ν ⊔ S, x v ∈ LinearMap.range ν ⊔ S := by
    intro x hx v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (h.range_inv hx ha) (hS x hx b hb)
  rcases h.quot_simple _ le_sup_left hT with h1 | h2
  · left
    rw [← h1]
    exact le_sup_right
  · have hI : ∀ x ∈ GX, ∀ v ∈ LinearMap.range ν ⊓ S, x v ∈ LinearMap.range ν ⊓ S :=
      fun x hx v hv => ⟨h.range_inv hx hv.1, hS x hx v hv.2⟩
    rcases h.irr _ inf_le_left hI with h3 | h4
    · right
      exact ⟨S, ⟨disjoint_iff.mpr h3, codisjoint_iff.mpr h2⟩, hS⟩
    · left
      have hle : LinearMap.range ν ≤ S := by
        rw [← h4]
        exact inf_le_right
      have := Submodule.eq_of_le_of_finrank_le hle hfr
      rw [this]

theorem endo_decomp (hns : ¬ OrthHasInvCompl GX ν) (f : E →ₗ[K] E)
    (hf : ∀ x ∈ GX, ∀ e, x (f e) = f (x e)) :
    ∃ c : K, (∀ u, f (ν u) = c • ν u) ∧
      (∀ e, f e - c • e ∈ LinearMap.range ν) := by
  have hW : ∀ u, f (ν u) ∈ LinearMap.range ν := by
    have hS : ∀ x ∈ GX, ∀ v ∈ (LinearMap.range ν).map f, x v ∈ (LinearMap.range ν).map f := by
      rintro x hx _ ⟨w, hw, rfl⟩
      exact ⟨x w, h.range_inv hx hw, (hf x hx w).symm⟩
    rcases h.le_or_hasInvCompl _ hS (Submodule.finrank_map_le f _) with h1 | h2
    · exact fun u => h1 ⟨ν u, ⟨u, rfl⟩, rfl⟩
    · exact absurd h2 hns
  obtain ⟨c, hc⟩ := h.scalar_on_W f hf hW
  refine ⟨c, hc, fun e => ?_⟩
  set g : E →ₗ[K] E := f - c • LinearMap.id with hg
  have hgx : ∀ x ∈ GX, ∀ e, x (g e) = g (x e) := by
    intro x hx e
    simp only [hg, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, hf x hx]
  have hgW : ∀ u, g (ν u) = 0 := by
    intro u
    simp [hg, hc]
  have hrange : LinearMap.range g ≤ LinearMap.range ν := by
    have hS : ∀ x ∈ GX, ∀ v ∈ LinearMap.range g, x v ∈ LinearMap.range g := by
      rintro x hx _ ⟨e, rfl⟩
      exact ⟨x e, (hgx x hx e).symm⟩
    have hfr : Module.finrank K (LinearMap.range g) ≤ Module.finrank K (LinearMap.range ν) := by
      have h1 := LinearMap.finrank_range_add_finrank_ker g
      have h2 : LinearMap.range ν ≤ LinearMap.ker g := fun w ⟨u, hu⟩ => by
        rw [LinearMap.mem_ker, ← hu, hgW]
      have h3 := Submodule.finrank_mono h2
      have h4 := h.finrank_E
      omega
    rcases h.le_or_hasInvCompl _ hS hfr with h1 | h2
    · exact h1
    · exact absurd h2 hns
  have : g e ∈ LinearMap.range ν := hrange ⟨e, rfl⟩
  simpa [hg] using this

theorem exists_hasInvCompl : OrthHasInvCompl GX ν := by
  by_contra hns
  obtain ⟨a, ha, b, hb, hab⟩ := h.a_nonabelian
  have hcomm : ∀ (f g : E →ₗ[K] E), (∀ x ∈ GX, ∀ e, x (f e) = f (x e)) →
      (∀ x ∈ GX, ∀ e, x (g e) = g (x e)) → ∀ e, f (g e) = g (f e) := by
    intro f g hf hg e
    obtain ⟨c, hc, hf₀⟩ := h.endo_decomp hns f hf
    obtain ⟨c', hc', hg₀⟩ := h.endo_decomp hns g hg
    have hfk : ∀ w ∈ LinearMap.range ν, f w = c • w := by
      rintro _ ⟨u, rfl⟩; exact hc u
    have hgk : ∀ w ∈ LinearMap.range ν, g w = c' • w := by
      rintro _ ⟨u, rfl⟩; exact hc' u
    obtain ⟨f₀, hf₀e⟩ : ∃ f₀, f₀ = f e - c • e := ⟨_, rfl⟩
    obtain ⟨g₀, hg₀e⟩ : ∃ g₀, g₀ = g e - c' • e := ⟨_, rfl⟩
    have hf₀W : f₀ ∈ LinearMap.range ν := hf₀e ▸ hf₀ e
    have hg₀W : g₀ ∈ LinearMap.range ν := hg₀e ▸ hg₀ e
    have hfe : f e = c • e + f₀ := by rw [hf₀e]; abel
    have hge : g e = c' • e + g₀ := by rw [hg₀e]; abel
    calc f (g e) = f (c' • e + g₀) := by rw [hge]
      _ = c' • (c • e + f₀) + c • g₀ := by rw [map_add, map_smul, hfe, hfk g₀ hg₀W]
      _ = c • (c' • e + g₀) + c' • f₀ := by
            simp only [smul_add, smul_smul]; rw [mul_comm c' c]; abel
      _ = c • g e + g f₀ := by rw [hgk f₀ hf₀W, hge]
      _ = g (c • e + f₀) := by rw [map_add, map_smul]
      _ = g (f e) := by rw [hfe]
  apply hab
  apply LinearEquiv.ext
  intro e
  have hax : ∀ x ∈ GX, ∀ e, x ((a : E →ₗ[K] E) e) = (a : E →ₗ[K] E) (x e) := by
    intro x hx e
    have := h.a_comm_x a ha x hx
    exact (congrArg (fun φ : E ≃ₗ[K] E => φ e) this).symm
  have hbx : ∀ x ∈ GX, ∀ e, x ((b : E →ₗ[K] E) e) = (b : E →ₗ[K] E) (x e) := by
    intro x hx e
    have := h.a_comm_x b hb x hx
    exact (congrArg (fun φ : E ≃ₗ[K] E => φ e) this).symm
  exact hcomm (a : E →ₗ[K] E) (b : E →ₗ[K] E) hax hbx e

theorem exists_nu' {W' : Submodule K E} (hc : IsCompl (LinearMap.range ν) W')
    (hinv : ∀ x ∈ GX, ∀ v ∈ W', x v ∈ W') :
    ∃ ν' : (ι → K) →ₗ[K] E, Function.Injective ν' ∧ LinearMap.range ν' = W' ∧
      (∀ u, ψ (ν' u) = ν u) ∧
      ∀ x ∈ GX, ∀ o : (ι → K) ≃ₗ[K] (ι → K), (∀ u, x (ν u) = ν (o u)) →
        ∀ u, x (ν' u) = ν' (o u) := by
  have hψW' : ∀ w ∈ W', ψ w ∈ LinearMap.range ν := by
    intro w _
    rw [← h.psi_range]
    exact ⟨w, rfl⟩
  let ψ' : W' →ₗ[K] LinearMap.range ν :=
    LinearMap.codRestrict (LinearMap.range ν) (ψ ∘ₗ W'.subtype) (fun w => hψW' w w.2)
  have hψ'inj : Function.Injective ψ' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ψ (w : E) = 0 := by
      have := congrArg Subtype.val hw
      exact this
    have h1 : (w : E) ∈ LinearMap.range ν := by
      rw [← h.psi_ker]
      exact h0
    have h2 : (w : E) ∈ LinearMap.range ν ⊓ W' := ⟨h1, w.2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  have hψ'surj : Function.Surjective ψ' := by
    intro z
    have hz : (z : E) ∈ LinearMap.range ψ := by rw [h.psi_range]; exact z.2
    obtain ⟨e, he⟩ := hz
    have : e ∈ LinearMap.range ν ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    have hψa : ψ a = 0 := by
      rw [← LinearMap.mem_ker, h.psi_ker]; exact ha
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    simp only [ψ', LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [map_add, hψa, zero_add] at he
    exact he
  let ψe : W' ≃ₗ[K] LinearMap.range ν := LinearEquiv.ofBijective ψ' ⟨hψ'inj, hψ'surj⟩
  let e : (ι → K) ≃ₗ[K] LinearMap.range ν := LinearEquiv.ofInjective ν h.nu_inj
  let ν' : (ι → K) →ₗ[K] E := W'.subtype ∘ₗ ψe.symm.toLinearMap ∘ₗ e.toLinearMap
  have hν'W : ∀ u, ν' u ∈ W' := fun u => (ψe.symm (e u)).2
  have hψν' : ∀ u, ψ (ν' u) = ν u := by
    intro u
    have h1 : ψe (ψe.symm (e u)) = e u := ψe.apply_symm_apply _
    have h2 : ψ ((ψe.symm (e u) : W') : E) = ν u := congrArg Subtype.val h1
    exact h2
  have hν'inj : Function.Injective ν' := by
    intro u v huv
    apply h.nu_inj
    rw [← hψν', ← hψν', huv]
  refine ⟨ν', hν'inj, ?_, hψν', ?_⟩
  · apply le_antisymm
    · rintro _ ⟨u, rfl⟩; exact hν'W u
    · intro w hw
      obtain ⟨u, hu⟩ := e.surjective (ψe ⟨w, hw⟩)
      refine ⟨u, ?_⟩
      have : ψe.symm (e u) = ⟨w, hw⟩ := by rw [hu]; exact ψe.symm_apply_apply _
      simp [ν', this]
  · intro x hx o hxo u
    have hxW' : x (ν' u) ∈ W' := hinv x hx _ (hν'W u)
    have hW'' : ν' (o u) ∈ W' := hν'W _
    have hdiff : x (ν' u) - ν' (o u) ∈ W' := W'.sub_mem hxW' hW''
    have hker : x (ν' u) - ν' (o u) ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_sub, ← h.psi_comm x hx, hψν', hψν', hxo, sub_self]
    rw [h.psi_ker] at hker
    have : x (ν' u) - ν' (o u) ∈ LinearMap.range ν ⊓ W' := ⟨hker, hdiff⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    exact sub_eq_zero.mp this

theorem B_nu_nu (u₁ u₂ : ι → K) : B (ν u₁) (ν u₂) = 0 := by
  rw [h.B_eq, ← map_add, h.w_sing, h.w_sing, h.w_sing]; ring

theorem exists_scalar {W' : Submodule K E} (hc : IsCompl (LinearMap.range ν) W')
    {ν' : (ι → K) →ₗ[K] E} (hν'r : LinearMap.range ν' = W')
    (hx' : ∀ x ∈ GX, ∀ o : (ι → K) ≃ₗ[K] (ι → K), (∀ u, x (ν u) = ν (o u)) →
        ∀ u, x (ν' u) = ν' (o u)) :
    ∃ c : K, c ≠ 0 ∧ ∀ u₁ u₂, B (ν u₁) (ν' u₂) = c * polar qU u₁ u₂ := by
  obtain ⟨T, hT⟩ := orth_exists_gram_equiv qU h.nondegU
  let y : (ι → K) →ₗ[K] (ι → K) :=
    LinearMap.pi fun i => (B (ν (Pi.single i 1))).comp ν'
  have hBy : ∀ u₁ u₂, B (ν u₁) (ν' u₂) = u₁ ⬝ᵥ y u₂ := by
    intro u₁ u₂
    have h1 : u₁ = ∑ i, u₁ i • (Pi.single i 1 : ι → K) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      dotProduct, y, LinearMap.pi_apply, LinearMap.comp_apply]
  let f : (ι → K) →ₗ[K] (ι → K) := T.toLinearMap ∘ₗ y
  have hf : ∀ u₁ u₂, polar qU u₁ (f u₂) = B (ν u₁) (ν' u₂) := by
    intro u₁ u₂
    rw [hBy]
    exact hT u₁ (y u₂)
  have hfcomm : ∀ o ∈ Ω, ∀ u, f (o u) = o (f u) := by
    intro o ho u₂
    obtain ⟨x, hx, hxo⟩ := h.x_surj o ho
    have hxo' := hx' x hx o hxo
    have hz : ∀ u₁, polar qU u₁ (f (o u₂)) = polar qU u₁ (o (f u₂)) := by
      intro u₁
      rw [hf]
      have e1 : ν u₁ = x (ν (o.symm u₁)) := by
        rw [hxo, LinearEquiv.apply_symm_apply]
      rw [e1, ← hxo' u₂, h.x_B hx, ← hf]
      have e2 := h.omega_polar ho (o.symm u₁) (f u₂)
      rw [LinearEquiv.apply_symm_apply] at e2
      exact e2.symm
    have : f (o u₂) - o (f u₂) = 0 := by
      refine h.nondegU _ fun v => ?_
      rw [polar_comm]
      have := hz v
      rw [QuadraticMap.polar_sub_right, this, sub_self]
    exact sub_eq_zero.mp this
  obtain ⟨c, hc'⟩ := h.omega_comm f hfcomm
  refine ⟨c, ?_, fun u₁ u₂ => ?_⟩
  · rintro rfl
    have hzero : ∀ u₁ u₂, B (ν u₁) (ν' u₂) = 0 := fun u₁ u₂ => by
      rw [← hf, hc']; simp
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have : ν (Pi.single i₀ 1) = 0 := by
      refine h.nondegB _ fun e => ?_
      have : e ∈ LinearMap.range ν ⊔ W' := by rw [hc.sup_eq_top]; trivial
      obtain ⟨a, ⟨ua, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp this
      rw [← hν'r] at hb
      obtain ⟨ub, rfl⟩ := hb
      rw [map_add, h.B_nu_nu, hzero, add_zero]
    have h1 : (Pi.single i₀ (1 : K) : ι → K) = 0 := h.nu_inj (by rw [this, map_zero])
    have h2 := congrFun h1 i₀
    simp at h2
  · rw [← hf, hc', QuadraticMap.polar_smul_right]; rfl

theorem exists_coordinates :
    ∃ (ν₂ : (ι → K) →ₗ[K] E) (φ : E ≃ₗ[K] (ι → K) × (ι → K)),
      (∀ u₁ u₂, φ.symm (u₁, u₂) = ν u₁ + ν₂ u₂) ∧
      (∀ u₁ u₂, B (ν u₁) (ν₂ u₂) = polar qU u₁ u₂) ∧
      (∀ x ∈ GX, ∀ o : (ι → K) ≃ₗ[K] (ι → K), (∀ u, x (ν u) = ν (o u)) →
        ∀ u, x (ν₂ u) = ν₂ (o u)) := by
  obtain ⟨W', hc, hinv⟩ := h.exists_hasInvCompl
  obtain ⟨ν', hν'inj, hν'r, -, hν'x⟩ := h.exists_nu' hc hinv
  obtain ⟨c, hc0, hcB⟩ := h.exists_scalar hc hν'r hν'x
  let ν₂ : (ι → K) →ₗ[K] E := c⁻¹ • ν'
  have hν₂ : ∀ u, ν₂ u = c⁻¹ • ν' u := fun u => rfl
  have hν₂inj : Function.Injective ν₂ := by
    intro u v huv
    apply hν'inj
    have := smul_right_injective E (inv_ne_zero hc0) (by simpa [hν₂] using huv)
    exact this
  have hν₂r : LinearMap.range ν₂ = W' := by
    rw [← hν'r]
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨c⁻¹ • u, by rw [map_smul, hν₂]⟩
    · rintro _ ⟨u, rfl⟩
      exact ⟨c • u, by rw [hν₂, map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  let Φ : ((ι → K) × (ι → K)) →ₗ[K] E := ν.coprod ν₂
  have hΦ : ∀ u₁ u₂, Φ (u₁, u₂) = ν u₁ + ν₂ u₂ := fun u₁ u₂ => LinearMap.coprod_apply _ _ _
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u₁, u₂⟩ hp
    have hp' : ν u₁ + ν₂ u₂ = 0 := by rw [← hΦ]; exact hp
    have h1 : ν u₁ ∈ LinearMap.range ν ⊓ W' := by
      refine ⟨⟨u₁, rfl⟩, ?_⟩
      rw [← hν₂r]
      refine ⟨-u₂, ?_⟩
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left hp').symm
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h1
    have h2 : ν₂ u₂ = 0 := by rw [h1, zero_add] at hp'; exact hp'
    have e1 : u₁ = 0 := h.nu_inj (by rw [h1, map_zero])
    have e2 : u₂ = 0 := hν₂inj (by rw [h2, map_zero])
    simp [e1, e2]
  have hΦsurj : Function.Surjective Φ := by
    intro e
    have : e ∈ LinearMap.range ν ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ⟨u₁, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    rw [← hν₂r] at hb
    obtain ⟨u₂, rfl⟩ := hb
    exact ⟨(u₁, u₂), hΦ u₁ u₂⟩
  let φe : ((ι → K) × (ι → K)) ≃ₗ[K] E := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  refine ⟨ν₂, φe.symm, fun u₁ u₂ => ?_, fun u₁ u₂ => ?_, fun x hx o hxo u => ?_⟩
  · rw [LinearEquiv.symm_symm]
    exact hΦ u₁ u₂
  · rw [hν₂, map_smul, hcB, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  · show x (c⁻¹ • ν' u) = c⁻¹ • ν' (o u)
    rw [map_smul, hν'x x hx o hxo u]

theorem exists_orthTensor_of_comm (F : (ι → K) × (ι → K) →ₗ[K] (ι → K) × (ι → K))
    (hF : ∀ o ∈ Ω, ∀ p : (ι → K) × (ι → K), F (o p.1, o p.2) = (o (F p).1, o (F p).2)) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, ∀ p, F p = orthTensor g (fun v => v) p := by
  let blk : ((ι → K) × (ι → K) →ₗ[K] (ι → K)) → ((ι → K) →ₗ[K] (ι → K) × (ι → K)) →
      ((ι → K) →ₗ[K] (ι → K)) := fun π L => π ∘ₗ F ∘ₗ L
  have hblk : ∀ (π : (ι → K) × (ι → K) →ₗ[K] (ι → K)) (L : (ι → K) →ₗ[K] (ι → K) × (ι → K)),
      (∀ o ∈ Ω, ∀ u, L (o u) = (o (L u).1, o (L u).2)) →
      (∀ o ∈ Ω, ∀ p : (ι → K) × (ι → K), π (o p.1, o p.2) = o (π p)) →
      ∃ c : K, ∀ u, π (F (L u)) = c • u := by
    intro π L hL hπ
    obtain ⟨c, hc⟩ := h.omega_comm (π ∘ₗ F ∘ₗ L) (by
      intro o ho u
      simp only [LinearMap.comp_apply]
      rw [hL o ho u, hF o ho, hπ o ho])
    exact ⟨c, fun u => hc u⟩
  have h1 := hblk (LinearMap.fst K _ _) (LinearMap.inl K _ _) (by
    intro o ho u; simp) (by intro o ho p; simp)
  have h2 := hblk (LinearMap.fst K _ _) (LinearMap.inr K _ _) (by
    intro o ho u; simp) (by intro o ho p; simp)
  have h3 := hblk (LinearMap.snd K _ _) (LinearMap.inl K _ _) (by
    intro o ho u; simp) (by intro o ho p; simp)
  have h4 := hblk (LinearMap.snd K _ _) (LinearMap.inr K _ _) (by
    intro o ho u; simp) (by intro o ho p; simp)
  obtain ⟨c00, hc00⟩ := h1
  obtain ⟨c01, hc01⟩ := h2
  obtain ⟨c10, hc10⟩ := h3
  obtain ⟨c11, hc11⟩ := h4
  refine ⟨!![c00, c01; c10, c11], fun p => ?_⟩
  have hp : p = (p.1, 0) + (0, p.2) := by simp
  have e1 : F p = F (p.1, 0) + F (0, p.2) := by rw [← map_add, ← hp]
  have f1 : (F (p.1, 0)).1 = c00 • p.1 := by simpa using hc00 p.1
  have f2 : (F (p.1, 0)).2 = c10 • p.1 := by simpa using hc10 p.1
  have f3 : (F (0, p.2)).1 = c01 • p.2 := by simpa using hc01 p.2
  have f4 : (F (0, p.2)).2 = c11 • p.2 := by simpa using hc11 p.2
  ext
  · rw [e1]; simp [orthTensor, f1, f3]
  · rw [e1]; simp [orthTensor, f2, f4]

theorem tensor_core :
    ∃ φ : E ≃ₗ[K] (ι → K) × (ι → K),
      (∀ e, Qf e = polar qU (φ e).1 (φ e).2) ∧ (∀ u, φ (ν u) = (u, 0)) ∧
      (∀ x ∈ GX, ∃ o ∈ Ω, ∀ e, φ (x e) = (o (φ e).1, o (φ e).2)) ∧
      (∀ o ∈ Ω, ∃ x ∈ GX, ∀ e, φ (x e) = (o (φ e).1, o (φ e).2)) ∧
      (∀ a ∈ GA, ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ TensorActsAs φ a g) ∧
      (∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ a ∈ GA, TensorActsAs φ a g) := by
  obtain ⟨ν₂, φ, hφ, hB, hν₂x⟩ := h.exists_coordinates
  have hφν : ∀ u, φ (ν u) = (u, 0) := by
    intro u
    have := hφ u 0
    rw [map_zero, add_zero] at this
    exact (φ.symm_apply_eq.mp this).symm
  have hφν₂ : ∀ u, φ (ν₂ u) = (0, u) := by
    intro u
    have := hφ 0 u
    rw [map_zero, zero_add] at this
    exact (φ.symm_apply_eq.mp this).symm
  have hdec : ∀ e, e = ν (φ e).1 + ν₂ (φ e).2 := by
    intro e
    have := hφ (φ e).1 (φ e).2
    rw [Prod.mk.eta, φ.symm_apply_apply] at this
    exact this
  have hXact : ∀ x ∈ GX, ∀ o : (ι → K) ≃ₗ[K] (ι → K), (∀ u, x (ν u) = ν (o u)) →
      ∀ e, φ (x e) = (o (φ e).1, o (φ e).2) := by
    intro x hx o hxo e
    have h2 := hν₂x x hx o hxo
    conv_lhs => rw [hdec e]
    rw [map_add, hxo, h2 (φ e).2]
    have := hφ (o (φ e).1) (o (φ e).2)
    exact ((φ.symm_apply_eq).mp this).symm
  have hAex : ∀ a ∈ GA, ∃ g, TensorActsAs φ a g := by
    intro a ha
    let F : (ι → K) × (ι → K) →ₗ[K] (ι → K) × (ι → K) :=
      φ.toLinearMap ∘ₗ a.toLinearMap ∘ₗ φ.symm.toLinearMap
    have hF : ∀ p, F p = φ (a (φ.symm p)) := fun p => rfl
    obtain ⟨g, hg⟩ := h.exists_orthTensor_of_comm F (by
      intro o ho p
      obtain ⟨x, hx, hxo⟩ := h.x_surj o ho
      have hxe := hXact x hx o hxo (φ.symm p)
      rw [LinearEquiv.apply_symm_apply] at hxe
      have hxae := hXact x hx o hxo (a (φ.symm p))
      rw [hF, ← hxe, LinearEquiv.symm_apply_apply]
      have hax : a (x (φ.symm p)) = x (a (φ.symm p)) :=
        congrArg (fun f : E ≃ₗ[K] E => f (φ.symm p)) (h.a_comm_x a ha x hx)
      rw [hax, hxae, hF])
    refine ⟨g, fun e => ?_⟩
    have := hg (φ e)
    rw [hF, LinearEquiv.symm_apply_apply] at this
    exact this
  let T : Subgroup (E ≃ₗ[K] E) :=
    { carrier := {a | a ∈ GA ∧ ∃ g : Matrix (Fin 2) (Fin 2) K, TensorActsAs φ a g ∧ g.det = 1}
      mul_mem' := by
        rintro a b ⟨ha, g, hg, hdg⟩ ⟨hb, g', hg', hdg'⟩
        exact ⟨GA.mul_mem ha hb, g * g', hg.mul hg', by rw [Matrix.det_mul, hdg, hdg', one_mul]⟩
      one_mem' := ⟨GA.one_mem, 1, TensorActsAs.one φ, Matrix.det_one⟩
      inv_mem' := by
        rintro a ⟨ha, g, hg, hdg⟩
        obtain ⟨g', hg'⟩ := hAex a⁻¹ (GA.inv_mem ha)
        refine ⟨GA.inv_mem ha, g', hg', ?_⟩
        have h1 := hg.mul_inv hg'
        have h2 := congrArg Matrix.det h1
        rw [Matrix.det_mul, hdg, one_mul, Matrix.det_one] at h2
        exact h2 }
  have hGAT : GA ≤ T := by
    rw [← h.a_perfect]
    refine (Subgroup.commutator_le).mpr fun x hx y hy => ?_
    obtain ⟨gx, hgx⟩ := hAex x hx
    obtain ⟨gy, hgy⟩ := hAex y hy
    obtain ⟨gx', hgx'⟩ := hAex x⁻¹ (GA.inv_mem hx)
    obtain ⟨gy', hgy'⟩ := hAex y⁻¹ (GA.inv_mem hy)
    have hcomm : TensorActsAs φ ⁅x, y⁆ (gx * gy * gx' * gy') := by
      rw [commutatorElement_def]
      exact ((hgx.mul hgy).mul hgx').mul hgy'
    refine ⟨?_, gx * gy * gx' * gy', hcomm, ?_⟩
    · rw [commutatorElement_def]
      exact GA.mul_mem (GA.mul_mem (GA.mul_mem hx hy) (GA.inv_mem hx)) (GA.inv_mem hy)
    · have e1 := congrArg Matrix.det (hgx.mul_inv hgx')
      have e2 := congrArg Matrix.det (hgy.mul_inv hgy')
      rw [Matrix.det_mul, Matrix.det_one] at e1 e2
      simp only [Matrix.det_mul]
      calc gx.det * gy.det * gx'.det * gy'.det = (gx.det * gx'.det) * (gy.det * gy'.det) := by ring
        _ = 1 := by rw [e1, e2, one_mul]
  have hex1 : ∀ a ∈ GA, ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ TensorActsAs φ a g := by
    intro a ha
    obtain ⟨-, g, hg, hd⟩ := hGAT ha
    exact ⟨g, hd, hg⟩
  have hsurj : ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ a ∈ GA, TensorActsAs φ a g := by
    classical
    let Ψ : GA → Matrix.SpecialLinearGroup (Fin 2) K := fun a =>
      ⟨Classical.choose (hex1 a a.2), (Classical.choose_spec (hex1 a a.2)).1⟩
    have hΨ : ∀ a : GA, TensorActsAs φ a (Ψ a : Matrix (Fin 2) (Fin 2) K) :=
      fun a => (Classical.choose_spec (hex1 a a.2)).2
    have hinj : Function.Injective Ψ := by
      intro a b hab
      apply Subtype.ext
      apply LinearEquiv.ext
      intro e
      have h1 := hΨ a e
      have h2 := hΨ b e
      rw [hab] at h1
      exact φ.injective (h1.trans h2.symm)
    have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ≤ Nat.card GA := by
      rw [h.a_card, ← CFSG.Open.StatedAPI.card_statedSL_two,
        CFSG.Open.StatedAPI.card_statedSL]
    have hbij := hinj.bijective_of_nat_card_le hcard
    intro g hg
    obtain ⟨a, ha⟩ := hbij.2 ⟨g, hg⟩
    refine ⟨a, a.2, ?_⟩
    have := hΨ a
    rw [ha] at this
    exact this
  have hsw : ∀ u, Qf (ν₂ u) = 0 := by
    intro u
    obtain ⟨a₀, ha₀, hact⟩ := hsurj !![0, 1; 1, 0] (by
      rw [Matrix.det_fin_two_of, zero_mul, zero_sub, mul_one]
      exact CharTwo.neg_eq (1 : K))
    have h1 := hact (ν₂ u)
    rw [hφν₂] at h1
    have h2 : φ (a₀ (ν₂ u)) = (u, 0) := by
      rw [h1]; simp [orthTensor]
    have h3 : a₀ (ν₂ u) = ν u := φ.injective (by rw [h2, hφν])
    rw [← h.a_isom a₀ ha₀, h3, h.w_sing]
  refine ⟨φ, fun e => ?_, hφν, ?_, ?_, hex1, hsurj⟩
  · conv_lhs => rw [hdec e]
    rw [h.qadd, h.w_sing, hsw, hB]; ring
  · intro x hx
    obtain ⟨o, ho, hxo⟩ := h.x_inv x hx
    exact ⟨o, ho, hXact x hx o hxo⟩
  · intro o ho
    obtain ⟨x, hx, hxo⟩ := h.x_surj o ho
    exact ⟨x, hx, hXact x hx o hxo⟩

end TensorCoreHyp

end TensorCore

end PartB

section PartC

open scoped Matrix commutatorElement
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section ProdSplit

variable {H A B : Type*} [Group H] [Group A] [Group B]

@[expose] def embProdFst (ψ : A × B →* H) : Subgroup H := (ψ.comp (MonoidHom.inl A B)).range

@[expose] def embProdSnd (ψ : A × B →* H) : Subgroup H := (ψ.comp (MonoidHom.inr A B)).range

theorem embProdFst_comm (ψ : A × B →* H) {a b : H} (ha : a ∈ embProdFst ψ) (hb : b ∈ embProdSnd ψ) :
    a * b = b * a := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem embProdFst_le_range (ψ : A × B →* H) : embProdFst ψ ≤ ψ.range := by
  rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩

theorem embProdSnd_le_range (ψ : A × B →* H) : embProdSnd ψ ≤ ψ.range := by
  rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩

theorem embProdFst_sup_prodSnd (ψ : A × B →* H) : embProdFst ψ ⊔ embProdSnd ψ = ψ.range := by
  refine le_antisymm (sup_le (embProdFst_le_range ψ) (embProdSnd_le_range ψ)) ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have : ψ (a, b) = ψ (a, 1) * ψ (1, b) := by rw [← map_mul]; simp
  rw [this]
  exact Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩

theorem embProdFst_normal (ψ : A × B →* H) {s : H} (hs : s ∈ ψ.range) {a : H}
    (ha : a ∈ embProdFst ψ) : s * a * s⁻¹ ∈ embProdFst ψ := by
  obtain ⟨⟨a₀, b₀⟩, rfl⟩ := hs
  obtain ⟨a', rfl⟩ := ha
  refine ⟨a₀ * a' * a₀⁻¹, ?_⟩
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

noncomputable def embProdFstEquiv (ψ : A × B →* H) (hψ : Function.Injective ψ) :
    A ≃* embProdFst ψ :=
  MonoidHom.ofInjective (f := ψ.comp (MonoidHom.inl A B)) (fun a b h => by
    have := hψ h
    exact congrArg Prod.fst this)

noncomputable def embProdSndEquiv (ψ : A × B →* H) (hψ : Function.Injective ψ) :
    B ≃* embProdSnd ψ :=
  MonoidHom.ofInjective (f := ψ.comp (MonoidHom.inr A B)) (fun a b h => by
    have := hψ h
    exact congrArg Prod.snd this)

end ProdSplit

section LinAct

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}

@[expose] noncomputable def orthLinAct (hS : IsTensorSetup hc n M₀ ρ b) :
    ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E) where
  toFun g := AddEquiv.toLinearEquiv (ρ g).toAdd (hS.lin g g.2)
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    show (ρ (1 : ↥(bar M Q (H0 M Z)))).toAdd v = v
    rw [Subgroup.coe_one, map_one]; rfl
  map_mul' g h := by
    refine LinearEquiv.ext fun v => ?_
    show (ρ (g * h : ↥(bar M Q (H0 M Z)))).toAdd v = (ρ g).toAdd ((ρ h).toAdd v)
    rw [Subgroup.coe_mul]
    exact act_mul_apply ρ g h v

theorem orthLinAct_apply (hS : IsTensorSetup hc n M₀ ρ b) (g : ↥(bar M Q (H0 M Z))) (e : M₀.E) :
    orthLinAct hS g e = (ρ g).toAdd e := rfl

theorem orth_exists_mk_of_mem_bar {S : Subgroup G} {ℓ : Mbar M Q} (hℓ : ℓ ∈ bar M Q S) :
    ∃ t : ↥M, (t : G) ∈ S ∧ (QuotientGroup.mk t : Mbar M Q) = ℓ := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hℓ
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

theorem orth_conj_of_mem_H0 {t : G} (ht : t ∈ H0 M Z) : ∀ z ∈ Z, t * z * t⁻¹ = z := by
  intro z hz
  have hm : t ∈ M ⊓ Subgroup.centralizer (Z : Set G) := ht
  have h1 := Subgroup.mem_centralizer_iff.mp hm.2 z hz
  rw [← h1]
  group

theorem orthLinAct_isom (hS : IsTensorSetup hc n M₀ ρ b) (g : ↥(bar M Q (H0 M Z))) (e : M₀.E) :
    M₀.Qf (orthLinAct hS g e) = M₀.Qf e := by
  obtain ⟨t, ht, hgt⟩ := orth_exists_mk_of_mem_bar g.2
  obtain ⟨T, hT1, hT2, -⟩ := hS.model.linear_of_centralizes t.2 (orth_conj_of_mem_H0 ht)
  have hρ : ∀ e, (ρ (QuotientGroup.mk t)).toAdd e = T e := fun e =>
    congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (t : G)) (S₁ := fun e => (ρ (QuotientGroup.mk t)).toAdd e)
      (S₂ := fun e => T e) (fun x hx => hS.conj t x hx) (fun x hx => hT1 x hx)) e
  rw [orthLinAct_apply, ← hgt, hρ, hT2]

theorem orthLinAct_injective (hS : IsTensorSetup hc n M₀ ρ b) : Function.Injective (orthLinAct hS) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨t, ht, hgt⟩ := orth_exists_mk_of_mem_bar g.2
  have h1 : (t : G) ∈ Q := by
    refine mem_Q_of_pi_conj_eq (M₀ := M₀) hc.hyp t.2 fun x hx => ?_
    rw [hS.conj t x hx]
    have := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f (M₀.π x)) hg
    simp only [orthLinAct_apply, LinearEquiv.coe_one, id_eq] at this
    rw [← hgt] at this
    exact this
  apply Subtype.ext
  show (g : Mbar M Q) = 1
  rw [← hgt]
  exact (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_subgroupOf.mpr h1)

end LinAct

end PartC

section PartD

open scoped Matrix
open CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Transport

variable {K K' : Type} [Field K] [Field K'] (θ : K ≃+* K') {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def thetaVec (v : ι → K) : ι → K' := fun i => θ (v i)

@[expose] def thetaGL : GL ι K ≃* GL ι K' :=
  Units.mapEquiv (θ.mapMatrix (m := ι)).toMulEquiv

theorem thetaGL_coe (A : GL ι K) : ((thetaGL θ A : GL ι K') : Matrix ι ι K') =
    (A : Matrix ι ι K).map θ := rfl

theorem thetaGL_mulVec (A : GL ι K) (v : ι → K) :
    ((thetaGL θ A : GL ι K') : Matrix ι ι K') *ᵥ thetaVec θ v = thetaVec θ ((A : Matrix ι ι K) *ᵥ v) := by
  funext i
  simp [thetaGL_coe, Matrix.mulVec, dotProduct, thetaVec, map_sum]

theorem thetaVec_add (u v : ι → K) : thetaVec θ (u + v) = thetaVec θ u + thetaVec θ v := by
  funext i; simp [thetaVec]

theorem thetaVec_smul (c : K) (v : ι → K) : thetaVec θ (c • v) = θ c • thetaVec θ v := by
  funext i; simp [thetaVec]

theorem thetaVec_zero : thetaVec θ (0 : ι → K) = 0 := by
  funext i; simp [thetaVec]

theorem thetaVec_surjective : Function.Surjective (thetaVec θ : (ι → K) → ι → K') := fun w =>
  ⟨fun i => θ.symm (w i), by funext i; simp [thetaVec]⟩

theorem thetaVec_injective : Function.Injective (thetaVec θ : (ι → K) → ι → K') := by
  intro u v h
  funext i
  exact θ.injective (congrFun h i)

@[expose] noncomputable def qTransport (qF : QuadraticForm K' (ι → K')) :
    QuadraticForm K (ι → K) where
  toFun v := θ.symm (qF (thetaVec θ v))
  toFun_smul a v := by
    simp only [thetaVec_smul, QuadraticMap.map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
  exists_companion' := by
    refine ⟨LinearMap.mk₂ K (fun x y => θ.symm (polar qF (thetaVec θ x) (thetaVec θ y)))
      (fun x₁ x₂ y => ?_) (fun c x y => ?_) (fun x y₁ y₂ => ?_) (fun c x y => ?_), fun x y => ?_⟩
    · simp only [thetaVec_add, polar_add_left, map_add]
    · simp only [thetaVec_smul, polar_smul_left, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    · simp only [thetaVec_add, polar_add_right, map_add]
    · simp only [thetaVec_smul, polar_smul_right, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    · simp only [thetaVec_add, LinearMap.mk₂_apply]
      rw [QuadraticMap.map_add qF (thetaVec θ x) (thetaVec θ y), map_add, map_add]

theorem qTransport_apply (qF : QuadraticForm K' (ι → K')) (v : ι → K) :
    qTransport θ qF v = θ.symm (qF (thetaVec θ v)) := rfl

theorem theta_qTransport (qF : QuadraticForm K' (ι → K')) (v : ι → K) :
    θ (qTransport θ qF v) = qF (thetaVec θ v) := by
  rw [qTransport_apply, RingEquiv.apply_symm_apply]

theorem theta_polar_qTransport (qF : QuadraticForm K' (ι → K')) (x y : ι → K) :
    θ (polar (qTransport θ qF) x y) = polar qF (thetaVec θ x) (thetaVec θ y) := by
  simp only [polar, map_sub, theta_qTransport, thetaVec_add]

theorem qTransport_nondeg (qF : QuadraticForm K' (ι → K'))
    (hnd : ∀ u : ι → K', (∀ v : ι → K', polar qF u v = 0) → u = 0) :
    ∀ u : ι → K, (∀ v : ι → K, polar (qTransport θ qF) u v = 0) → u = 0 := by
  intro u hu
  apply thetaVec_injective θ
  rw [thetaVec_zero]
  apply hnd
  intro w
  obtain ⟨v, rfl⟩ := thetaVec_surjective θ w
  rw [← theta_polar_qTransport, hu v, map_zero]

@[expose] noncomputable def thetaLin : ((ι → K) ≃ₗ[K] (ι → K)) ≃* GL ι K' :=
  (toLinEquiv ι K).symm.trans (thetaGL θ)

theorem thetaLin_mulVec (o : (ι → K) ≃ₗ[K] (ι → K)) (u : ι → K) :
    ((thetaLin θ o : GL ι K') : Matrix ι ι K') *ᵥ thetaVec θ u = thetaVec θ (o u) := by
  have h := toLinEquiv_apply ((toLinEquiv ι K).symm o) u
  rw [MulEquiv.apply_symm_apply] at h
  rw [thetaLin, MulEquiv.trans_apply, thetaGL_mulVec, h]

@[expose] noncomputable def omegaK (Xcl : Subgroup (GL ι K')) : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
  Xcl.comap (thetaLin θ).toMonoidHom

theorem mem_omegaK {Xcl : Subgroup (GL ι K')} {o : (ι → K) ≃ₗ[K] (ι → K)} :
    o ∈ omegaK θ Xcl ↔ thetaLin θ o ∈ Xcl := Iff.rfl

theorem omegaK_isom (qF : QuadraticForm K' (ι → K')) {Xcl : Subgroup (GL ι K')}
    (hX : ∀ A ∈ Xcl, ∀ v, qF ((A : Matrix ι ι K') *ᵥ v) = qF v)
    {o : (ι → K) ≃ₗ[K] (ι → K)} (ho : o ∈ omegaK θ Xcl) (v : ι → K) :
    qTransport θ qF (o v) = qTransport θ qF v := by
  have hA : thetaLin θ o ∈ Xcl := ho
  rw [qTransport_apply, qTransport_apply, ← thetaLin_mulVec, hX _ hA]

theorem omegaK_comm {Xcl : Subgroup (GL ι K')} (hX : CFSG.RankThree.GF2n.Stroth80.AddCommutantScalar Xcl)
    (f : (ι → K) →ₗ[K] (ι → K)) (hf : ∀ o ∈ omegaK θ Xcl, ∀ u, f (o u) = o (f u)) :
    ∃ c : K, ∀ u, f u = c • u := by
  let f' : (ι → K') →+ (ι → K') :=
    { toFun := fun y => thetaVec θ (f (thetaVec θ.symm y))
      map_zero' := by simp [thetaVec_zero]
      map_add' := fun y z => by
        rw [thetaVec_add θ.symm y z, map_add, thetaVec_add] }
  have hvv : ∀ u : ι → K, thetaVec θ.symm (thetaVec θ u) = u := fun u => by
    funext i; simp [thetaVec]
  have hvv' : ∀ y : ι → K', thetaVec θ (thetaVec θ.symm y) = y := fun y => by
    funext i; simp [thetaVec]
  obtain ⟨c', hc'⟩ := hX f' (by
    intro A hA y
    set o := (thetaLin θ).symm A with ho
    have hoA : o ∈ omegaK θ Xcl := by
      rw [mem_omegaK, ho, MulEquiv.apply_symm_apply]; exact hA
    have hy : y = thetaVec θ (thetaVec θ.symm y) := (hvv' y).symm
    show thetaVec θ (f (thetaVec θ.symm ((A : Matrix ι ι K') *ᵥ y))) =
      (A : Matrix ι ι K') *ᵥ thetaVec θ (f (thetaVec θ.symm y))
    have hA' : ((thetaLin θ o : GL ι K') : Matrix ι ι K') = (A : Matrix ι ι K') := by
      rw [ho, MulEquiv.apply_symm_apply]
    rw [hy, ← hA', thetaLin_mulVec, hvv, hvv, hf o hoA, thetaLin_mulVec])
  refine ⟨θ.symm c', fun u => ?_⟩
  apply thetaVec_injective θ
  have h1 := hc' (thetaVec θ u)
  show thetaVec θ (f u) = thetaVec θ (θ.symm c' • u)
  rw [thetaVec_smul, RingEquiv.apply_symm_apply, ← h1]
  show thetaVec θ (f u) = thetaVec θ (f (thetaVec θ.symm (thetaVec θ u)))
  rw [hvv]

theorem thetaVec_sub (u v : ι → K) : thetaVec θ (u - v) = thetaVec θ u - thetaVec θ v := by
  funext i; simp [thetaVec]

theorem thetaVec_eichler (qF : QuadraticForm K' (ι → K')) {a w : ι → K}
    (ha : qTransport θ qF a = 0) (hw : polar (qTransport θ qF) a w = 0) (u : ι → K) :
    thetaVec θ (eichler (qTransport θ qF) a w u) =
      eichler qF (thetaVec θ a) (thetaVec θ w) (thetaVec θ u) := by
  have ha' : qF (thetaVec θ a) = 0 := by rw [← theta_qTransport θ qF a, ha, map_zero]
  have hw' : polar qF (thetaVec θ a) (thetaVec θ w) = 0 := by
    rw [← theta_polar_qTransport θ qF a w, hw, map_zero]
  rw [eichler_apply ha hw, eichler_apply ha' hw']
  rw [thetaVec_sub, thetaVec_add, thetaVec_smul, thetaVec_smul]
  simp only [map_add, map_mul, theta_polar_qTransport, theta_qTransport]

theorem thetaLin_eichler (qF : QuadraticForm K' (ι → K')) {a w : ι → K}
    (ha : qTransport θ qF a = 0) (hw : polar (qTransport θ qF) a w = 0) :
    thetaLin θ (eichler (qTransport θ qF) a w) =
      (toLinEquiv ι K').symm (eichler qF (thetaVec θ a) (thetaVec θ w)) := by
  apply (toLinEquiv ι K').injective
  apply LinearEquiv.ext
  intro y
  obtain ⟨u, rfl⟩ := thetaVec_surjective θ y
  rw [toLinEquiv_apply, thetaLin_mulVec, MulEquiv.apply_symm_apply]
  exact thetaVec_eichler θ qF ha hw u

end Transport

end PartD

section PartE

section ClaimA

theorem orth_card_eq_ker_mul_range {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker]

variable {Γ A B Y : Type} [Group Γ] [Finite Γ] [Group A] [Group B] [Group Y]

noncomputable def embProjFst (ψ : A × B →* Γ) (hψ : Function.Injective ψ) (R : Subgroup Γ)
    (hRS : R ≤ ψ.range) : ↥R →* A :=
  (MonoidHom.fst A B).comp ((MonoidHom.ofInjective hψ).symm.toMonoidHom.comp
    (Subgroup.inclusion hRS))

theorem mem_ker_embProjFst (ψ : A × B →* Γ) (hψ : Function.Injective ψ) (R : Subgroup Γ)
    (hRS : R ≤ ψ.range) (r : ↥R) : r ∈ (embProjFst ψ hψ R hRS).ker ↔ (r : Γ) ∈ embProdSnd ψ := by
  constructor
  · intro h
    have h1 : ((MonoidHom.ofInjective hψ).symm (Subgroup.inclusion hRS r)).1 = 1 := h
    obtain ⟨⟨a, b⟩, hab⟩ : ∃ p : A × B, (MonoidHom.ofInjective hψ) p = Subgroup.inclusion hRS r :=
      ⟨(MonoidHom.ofInjective hψ).symm (Subgroup.inclusion hRS r), by simp⟩
    have h2 : (MonoidHom.ofInjective hψ).symm (Subgroup.inclusion hRS r) = (a, b) := by
      rw [← hab]; simp
    rw [h2] at h1
    simp only at h1
    subst h1
    refine ⟨b, ?_⟩
    have := congrArg Subtype.val hab
    exact this
  · rintro ⟨b, hb⟩
    have hab : (MonoidHom.ofInjective hψ) (1, b) = Subgroup.inclusion hRS r := by
      apply Subtype.ext
      exact hb
    have h2 : (MonoidHom.ofInjective hψ).symm (Subgroup.inclusion hRS r) = (1, b) := by
      rw [← hab]; simp
    show ((MonoidHom.ofInjective hψ).symm (Subgroup.inclusion hRS r)).1 = 1
    rw [h2]

theorem orthClaimA (ψ : A × B →* Γ) (hψ : Function.Injective ψ) (R N : Subgroup Γ)
    (hRS : R ≤ ψ.range) (hNR : N ≤ R) (π : ↥R →* Y) (hπs : Function.Surjective π)
    (hker : π.ker = N.subgroupOf R) [IsSimpleGroup Y]
    (hcardB : Nat.card B = Nat.card Y) (hbig : Nat.card A < Nat.card Y) :
    embProdSnd ψ ≤ R ∧ embProdSnd ψ ⊓ N = ⊥ ∧ ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ embProdSnd ψ, r = n * x := by
  classical
  haveI : Finite Y := Finite.of_surjective π hπs
  haveI : Finite A :=
    Finite.of_injective (fun a : A => ψ (a, 1)) (fun a b h => congrArg Prod.fst (hψ h))
  haveI : Finite B :=
    Finite.of_injective (fun b : B => ψ (1, b)) (fun a b h => congrArg Prod.snd (hψ h))
  set p := embProjFst ψ hψ R hRS with hp
  set D : Subgroup ↥R := (embProdSnd ψ).subgroupOf R with hD
  have hDp : D = p.ker := by
    ext r
    rw [mem_ker_embProjFst, Subgroup.mem_subgroupOf]
  have hDnorm : D.Normal := by
    rw [hDp]; infer_instance
  have hcardR : Nat.card ↥R = Nat.card D * Nat.card p.range := by
    rw [hDp]; exact orth_card_eq_ker_mul_range p
  have hcardR_le : Nat.card ↥R ≤ Nat.card D * Nat.card A := by
    rw [hcardR]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)
  have hcardR_π : Nat.card ↥R = Nat.card π.ker * Nat.card Y := by
    rw [orth_card_eq_ker_mul_range π, MonoidHom.range_eq_top.mpr hπs, Subgroup.card_top]
  have hD'normal : (D.map π).Normal := Subgroup.Normal.map hDnorm π hπs
  have hDB : Nat.card D ≤ Nat.card B := by
    have hinj : Function.Injective (fun d : D => (⟨(d : ↥R).1, Subgroup.mem_subgroupOf.mp d.2⟩ :
        embProdSnd ψ)) := by
      intro d e h
      have hh : ((d : ↥R) : Γ) = ((e : ↥R) : Γ) := congrArg (fun z : embProdSnd ψ => (z : Γ)) h
      exact Subtype.ext (Subtype.ext hh)
    calc Nat.card D ≤ Nat.card (embProdSnd ψ) := Nat.card_le_card_of_injective _ hinj
      _ = Nat.card B := (Nat.card_congr (embProdSndEquiv ψ hψ).toEquiv).symm
  rcases @Subgroup.Normal.eq_bot_or_eq_top Y _ _ (D.map π) hD'normal with h0 | h1
  · exfalso
    have hle : D ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp h0
    have h1 : Nat.card D ≤ Nat.card π.ker := Subgroup.card_le_of_le hle
    have hkpos : 0 < Nat.card π.ker := Nat.card_pos
    have h2 : Nat.card π.ker * Nat.card Y ≤ Nat.card π.ker * Nat.card A := by
      calc Nat.card π.ker * Nat.card Y = Nat.card ↥R := hcardR_π.symm
        _ ≤ Nat.card D * Nat.card A := hcardR_le
        _ ≤ Nat.card π.ker * Nat.card A := Nat.mul_le_mul_right _ h1
    have := Nat.le_of_mul_le_mul_left h2 hkpos
    omega
  · let πD : ↥D →* Y := π.comp D.subtype
    have hπD : Function.Surjective πD := by
      intro y
      have : y ∈ D.map π := by rw [h1]; trivial
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp this
      exact ⟨⟨d, hd⟩, rfl⟩
    have hYD : Nat.card Y ≤ Nat.card D := Nat.card_le_card_of_surjective _ hπD
    have hDeq : Nat.card D = Nat.card Y := le_antisymm (hcardB ▸ hDB) hYD
    have hbij : Function.Bijective πD := hπD.bijective_of_nat_card_le hDeq.le
    have hXR : embProdSnd ψ ≤ R := by
      have hbijD : Function.Bijective (fun d : D => (⟨(d : ↥R).1,
          Subgroup.mem_subgroupOf.mp d.2⟩ : embProdSnd ψ)) := by
        have hinj : Function.Injective (fun d : D => (⟨(d : ↥R).1,
            Subgroup.mem_subgroupOf.mp d.2⟩ : embProdSnd ψ)) := by
          intro d e h
          have hh : ((d : ↥R) : Γ) = ((e : ↥R) : Γ) := congrArg (fun z : embProdSnd ψ => (z : Γ)) h
          exact Subtype.ext (Subtype.ext hh)
        refine hinj.bijective_of_nat_card_le ?_
        have hc : Nat.card (embProdSnd ψ) = Nat.card D :=
          calc Nat.card (embProdSnd ψ) = Nat.card B :=
                (Nat.card_congr (embProdSndEquiv ψ hψ).toEquiv).symm
            _ = Nat.card Y := hcardB
            _ = Nat.card D := hDeq.symm
        exact hc.le
      intro x hx
      obtain ⟨d, hd⟩ := hbijD.2 ⟨x, hx⟩
      have hdx : ((d : ↥R) : Γ) = x := congrArg (fun z : embProdSnd ψ => (z : Γ)) hd
      rw [← hdx]
      exact (d : ↥R).2
    refine ⟨hXR, ?_, ?_⟩
    · rw [eq_bot_iff]
      rintro x ⟨hxX, hxN⟩
      have hxR : x ∈ R := hNR hxN
      have hxD : (⟨x, hxR⟩ : ↥R) ∈ D := Subgroup.mem_subgroupOf.mpr hxX
      have hxk : (⟨x, hxR⟩ : ↥R) ∈ π.ker := by
        rw [hker]; exact Subgroup.mem_subgroupOf.mpr hxN
      have h1 : πD ⟨⟨x, hxR⟩, hxD⟩ = πD 1 := by
        rw [map_one]; exact hxk
      have h2 := hbij.1 h1
      have h3 := congrArg (fun d : ↥D => ((d : ↥R) : Γ)) h2
      simpa using h3
    · intro r hr
      obtain ⟨d, hd⟩ := hπD (π ⟨r, hr⟩)
      have hdk : (⟨r, hr⟩ : ↥R) * ((d : ↥D) : ↥R)⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have : π (d : ↥R) = π ⟨r, hr⟩ := hd
        rw [this, mul_inv_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at hdk
      have hdX : (((d : ↥D) : ↥R) : Γ) ∈ embProdSnd ψ := Subgroup.mem_subgroupOf.mp d.2
      refine ⟨r * (((d : ↥D) : ↥R) : Γ)⁻¹, hdk, ((d : ↥D) : ↥R), hdX, by group⟩

end ClaimA

end PartE

section PartF

open scoped Matrix commutatorElement
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (eichler toLinEquiv)

section NuMap

variable {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E] (θ : K ≃+* F)
  {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule K E) (Ψ : ↥W ≃+ (ι → F))
  (hΨ : ∀ (c : K) (w : ↥W), Ψ (c • w) = θ c • Ψ w)

include hΨ

theorem orth_psi_symm_smul (c : K) (y : ι → F) : Ψ.symm (θ c • y) = c • Ψ.symm y := by
  apply Ψ.injective
  rw [AddEquiv.apply_symm_apply, hΨ, AddEquiv.apply_symm_apply]

@[expose] noncomputable def orthNuMap : (ι → K) →ₗ[K] E where
  toFun u := (Ψ.symm (thetaVec θ u) : E)
  map_add' u v := by
    show ((Ψ.symm (thetaVec θ (u + v)) : ↥W) : E) =
      ((Ψ.symm (thetaVec θ u) : ↥W) : E) + ((Ψ.symm (thetaVec θ v) : ↥W) : E)
    rw [thetaVec_add, map_add, Submodule.coe_add]
  map_smul' c u := by
    show ((Ψ.symm (thetaVec θ (c • u)) : ↥W) : E) = c • ((Ψ.symm (thetaVec θ u) : ↥W) : E)
    rw [thetaVec_smul, orth_psi_symm_smul θ W Ψ hΨ, Submodule.coe_smul]

theorem orthNuMap_apply (u : ι → K) : orthNuMap θ W Ψ hΨ u = (Ψ.symm (thetaVec θ u) : E) := rfl

theorem orthNuMap_mem (u : ι → K) : orthNuMap θ W Ψ hΨ u ∈ W := (Ψ.symm (thetaVec θ u)).2

theorem orthNuMap_injective : Function.Injective (orthNuMap θ W Ψ hΨ) := by
  intro u v h
  apply thetaVec_injective θ
  apply Ψ.symm.injective
  exact Subtype.ext h

theorem range_nuMap : LinearMap.range (orthNuMap θ W Ψ hΨ) = W := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩; exact orthNuMap_mem θ W Ψ hΨ u
  · intro w hw
    refine ⟨thetaVec θ.symm (Ψ ⟨w, hw⟩), ?_⟩
    have : thetaVec θ (thetaVec θ.symm (Ψ ⟨w, hw⟩)) = Ψ ⟨w, hw⟩ := by
      funext i; simp [thetaVec]
    rw [orthNuMap_apply, this, AddEquiv.symm_apply_apply]

end NuMap

section Glue

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_singular_of_transport [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {X : Subgroup (GL ι F)}
    (Ψ : ↥(hc.VtSub hS.model t) ≃+ (ι → F))
    (π : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL ι F) (hπr : π.range = X)
    (hπk : ∀ x : ↥(bar M Q (Rt M (LB M Q B) t)),
      π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t))
    (hΨπ : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
      Ψ ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS ht x x.2 w w.2⟩ =
        (π x : Matrix ι ι F) *ᵥ Ψ w)
    {qF : QuadraticForm F (ι → F)} (hsing : NatSingular hc t qF X) :
    ∀ w : ↥(hc.VtSub hS.model t), (w : M₀.E) ∈ M₀.img B → qF (Ψ w) = 0 := by
  classical
  intro w hw
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  haveI hZn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hx))
  have hπV : ∀ v : ↥(Vt M (LB M Q B) B Z t), M₀.π v ∈ hc.VtSub hS.model t := fun v =>
    M₀.pi_mem_img v.2 (hVQ v.2)
  let κ : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative ↥(hc.VtSub hS.model t) :=
    { toFun := fun v => Multiplicative.ofAdd ⟨M₀.π v, hπV v⟩
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext M₀.pi_one
      map_mul' := fun x y => by
        apply congrArg Multiplicative.ofAdd
        exact Subtype.ext (M₀.π_mul x (hVQ x.2) y (hVQ y.2)) }
  have hκsurj : Function.Surjective κ := by
    intro a
    obtain ⟨x, hxV, -, hx⟩ := a.toAdd.2
    exact ⟨⟨x, hxV⟩, by
      show Multiplicative.ofAdd (⟨M₀.π x, hπV ⟨x, hxV⟩⟩ : ↥(hc.VtSub hS.model t)) = a
      apply congrArg Multiplicative.ofAdd
      exact Subtype.ext hx⟩
  have hker : κ.ker = Z.subgroupOf (Vt M (LB M Q B) B Z t) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← M₀.π_ker _ (hVQ v.2)]
    constructor
    · intro h
      exact congrArg Subtype.val (Multiplicative.ofAdd.injective h)
    · intro h
      exact congrArg Multiplicative.ofAdd (Subtype.ext h)
  let e₁ : ↥(Vt M (LB M Q B) B Z t) ⧸ κ.ker ≃* Multiplicative ↥(hc.VtSub hS.model t) :=
    QuotientGroup.quotientKerEquivOfSurjective κ hκsurj
  let e₂ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      ↥(Vt M (LB M Q B) B Z t) ⧸ κ.ker := QuotientGroup.quotientMulEquivOfEq hker.symm
  let ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → F) := e₂.trans (e₁.trans (AddEquiv.toMultiplicative Ψ))
  have hψv : ∀ v : ↥(Vt M (LB M Q B) B Z t), secVec ψ v = Ψ ⟨M₀.π v, hπV v⟩ := fun v => rfl
  let ι₀ : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hmem : ∀ r : ↥(Rt M (LB M Q B) t), ι₀ r ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
    Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
  let f : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (Rt M (LB M Q B) t)) := ι₀.codRestrict _ hmem
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp y.2
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    refine ⟨⟨(r : G), hrR⟩, Subtype.ext ?_⟩
    show ι₀ ⟨(r : G), hrR⟩ = (y : Mbar M Q)
    rw [← hry]
    rfl
  let φ : ↥(Rt M (LB M Q B) t) →* GL ι F := π.comp f
  have hφr : φ.range = X := by
    rw [← hπr]
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨r, rfl⟩ := hfsurj y
      exact ⟨r, rfl⟩
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx, fun v hv =>
      hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  have hφk : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π (f r) = 1 ↔ (r : G) ∈ hc.CN t
    rw [hπk]
    constructor
    · rintro ⟨y, hy, hyr⟩
      have hyCN : (y : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hy
      have h1 : QuotientGroup.mk' (Q.subgroupOf M) y = ι₀ r := hyr
      have h2 := QuotientGroup.eq.mp h1
      have h3 : (y : G)⁻¹ * (r : G) ∈ Q := Subgroup.mem_subgroupOf.mp h2
      have e : (r : G) = (y : G) * ((y : G)⁻¹ * (r : G)) := by group
      rw [e]
      exact (hc.CN t).mul_mem hyCN (hQN h3)
    · intro h
      exact ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr h, rfl⟩
  have hequiv : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι F) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)) := by
    intro s v w hwv
    have hvQ : (v : G) ∈ Q := hVQ v.2
    have hconj := hS.conj ⟨(s : G), hRM s.2⟩ (v : G) hvQ
    have hfs : (f s : Mbar M Q) = QuotientGroup.mk ⟨(s : G), hRM s.2⟩ := rfl
    have key := hΨπ (f s) ⟨M₀.π (v : G), hπV v⟩
    have e : (⟨(ρ (f s : Mbar M Q)).toAdd (M₀.π (v : G)),
        hc.act_mem_VtSub hS ht (f s : Mbar M Q) (f s).2 (M₀.π (v : G)) (hπV v)⟩ :
          ↥(hc.VtSub hS.model t)) = ⟨M₀.π (w : G), hπV w⟩ := by
      apply Subtype.ext
      show (ρ (f s : Mbar M Q)).toAdd (M₀.π (v : G)) = M₀.π (w : G)
      rw [hfs, ← hconj, hwv]
    rw [e] at key
    exact key
  obtain ⟨e, he, heQ, hee⟩ := M₀.mem_img.mp hw
  have hwe : w = ⟨M₀.π e, hπV ⟨e, hBV he⟩⟩ := Subtype.ext hee.symm
  have := hsing φ hφr hφk ψ hequiv ⟨e, hBV he⟩ he
  rw [hwe]
  rw [hψv] at this
  exact this

theorem orth_tensor_glue [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (h34 : Stroth34Statement) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    (hVU : Vt M (LB M Q B) B Z t = Ut Q Z t)
    {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (qF : QuadraticForm F (ι → F)) (hFZ : Nat.card F = Nat.card Z) (hιn : Fintype.card ι = n)
    (hnd : ∀ u : ι → F, (∀ v, polar qF u v = 0) → u = 0)
    (hXiso : ∀ A ∈ StatedOmega ⇑qF, ∀ v, qF ((A : Matrix ι ι F) *ᵥ v) = qF v)
    (hscal : AddCommutantScalar (StatedOmega ⇑qF))
    (hEich : ∀ a' w' : ι → F, qF a' = 0 → polar qF a' w' = 0 →
      (toLinEquiv ι F).symm (eichler qF a' w') ∈ StatedOmega ⇑qF)
    (hsimple : IsSimpleGroup ↥(StatedOmega ⇑qF))
    (hbig : Nat.card Z * (Nat.card Z ^ 2 - 1) < Nat.card ↥(StatedOmega ⇑qF))
    (hnat : NaturalRep F (StatedOmega ⇑qF) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hc.CN t))
    (hsing : Stroth310RootStatement → NatSingular hc t qF (StatedOmega ⇑qF))
    {P₂ : ∀ (X : Type) [Group X], Prop}
    (hP₂ : ∀ (X : Type) [Group X], P₂ X → Nat.card X = Nat.card ↥(StatedOmega ⇑qF))
    (hprod : QuotSat (Lgen M (LB M Q B)) Q (IsProdOf (IsSLModel 2 (Nat.card Z)) P₂)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (θ : K ≃+* F) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ (qTransport θ qF) φ ∧
        (∀ s ∈ Lgen M (LB M Q B), ∃ (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) ≃ₗ[K] (ι → K)),
          g.det = 1 ∧ (∀ v, qTransport θ qF (o v) = qTransport θ qF v) ∧
            ActsAsTensor Q Z M₀ φ s g o) ∧
        (∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ s ∈ Lgen M (LB M Q B),
          ActsAsTensor Q Z M₀ φ s g id) ∧
        (∀ a w : ι → K, qTransport θ qF a = 0 → polar (qTransport θ qF) a w = 0 →
          ∃ s ∈ Lgen M (LB M Q B),
            ActsAsTensor Q Z M₀ φ s 1 (eichler (qTransport θ qF) a w)) ∧
        (∃ u : ι → K, u ≠ 0 ∧ (∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ s : K, φ e = s • (u, 0)) ∧
          (Stroth310RootStatement → qTransport θ qF u = 0)) := by
  classical
  obtain ⟨hN', A, B', _, _, hA, hB', ⟨e⟩⟩ := hprod
  haveI := hN'
  have hLM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.LB_le_M
  let e₃ : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃*
      ↥(bar M Q (Lgen M (LB M Q B))) :=
    (MonoidHom.ofInjective (quotIncl_injective (Q := Q) hLM)).trans
      (MulEquiv.subgroupCongr (quotIncl_range hLM))
  let eS : ↥(bar M Q (Lgen M (LB M Q B))) ≃* A × B' := e₃.symm.trans e
  let ψ₀ : A × B' →* Mbar M Q := (bar M Q (Lgen M (LB M Q B))).subtype.comp eS.symm.toMonoidHom
  have hψ₀ : Function.Injective ψ₀ := by
    intro a b h
    exact eS.symm.injective (Subtype.ext h)
  have hψ₀r : ψ₀.range = bar M Q (Lgen M (LB M Q B)) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (eS.symm p).2
    · intro hx
      exact ⟨eS ⟨x, hx⟩, by simp [ψ₀]⟩
  obtain ⟨K, hK, hKfin, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hw hn hno hgen
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  have h35 := (stroth_3_5 h34 hc hw hn hno hgen).2.1
  obtain ⟨θ, Ψ, π, hπr, hπk, hΨθ, hΨπ⟩ := hc.natural_transport hS ht hFZ hscal hnat
  have hRS : bar M Q (Rt M (LB M Q B) t) ≤ ψ₀.range := by
    rw [hψ₀r]; exact Ctx.bar_Rt_le_bar_Lgen t
  have hNR : bar M Q (hc.CN t) ≤ bar M Q (Rt M (LB M Q B) t) := hc.bar_CN_le_bar_Rt t
  let π' : ↥(bar M Q (Rt M (LB M Q B) t)) →* ↥(StatedOmega ⇑qF) :=
    π.codRestrict _ (fun x => by rw [← hπr]; exact ⟨x, rfl⟩)
  have hπ's : Function.Surjective π' := by
    intro y
    have : (y : GL ι F) ∈ π.range := by rw [hπr]; exact y.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  have hkerπ' : π'.ker = (bar M Q (hc.CN t)).subgroupOf (bar M Q (Rt M (LB M Q B) t)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hπk x]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  obtain ⟨F₂, hF₂, hF₂fin, hF₂card, ⟨eA⟩⟩ := hA
  have hcardA : Nat.card A = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
    rw [Nat.card_congr eA.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF₂card]
  haveI := hsimple
  obtain ⟨hXR, hXN, hRX⟩ := orthClaimA ψ₀ hψ₀ _ _ hRS hNR π' hπ's hkerπ'
    (hP₂ B' hB') (by rw [hcardA]; exact hbig)
  have hXH0 : embProdSnd ψ₀ ≤ bar M Q (H0 M Z) := by
    refine (embProdSnd_le_range ψ₀).trans ?_
    rw [hψ₀r]; exact hc.bar_Lgen_le_bar_H0
  have hAH0 : embProdFst ψ₀ ≤ bar M Q (H0 M Z) := by
    refine (embProdFst_le_range ψ₀).trans ?_
    rw [hψ₀r]; exact hc.bar_Lgen_le_bar_H0
  let incA : A →* ↥(bar M Q (H0 M Z)) :=
    (ψ₀.comp (MonoidHom.inl A B')).codRestrict _ (fun a => hAH0 ⟨a, rfl⟩)
  let incX : B' →* ↥(bar M Q (H0 M Z)) :=
    (ψ₀.comp (MonoidHom.inr A B')).codRestrict _ (fun b => hXH0 ⟨b, rfl⟩)
  let ΦA : A →* (M₀.E ≃ₗ[K] M₀.E) := (orthLinAct hS).comp incA
  let ΦX : B' →* (M₀.E ≃ₗ[K] M₀.E) := (orthLinAct hS).comp incX
  have hincA : ∀ a, ((incA a : ↥(bar M Q (H0 M Z))) : Mbar M Q) = ψ₀ (a, 1) := fun a => rfl
  have hincX : ∀ b, ((incX b : ↥(bar M Q (H0 M Z))) : Mbar M Q) = ψ₀ (1, b) := fun b => rfl
  have hincXR : ∀ b, ψ₀ (1, b) ∈ bar M Q (Rt M (LB M Q B) t) := fun b => hXR ⟨b, rfl⟩
  let W : Submodule K M₀.E := hc.VtSub hS.model t
  let ν : (ι → K) →ₗ[K] M₀.E := orthNuMap θ W Ψ hΨθ
  let Ω : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := omegaK θ (StatedOmega ⇑qF)
  have hAct : ∀ (g : ↥(bar M Q (H0 M Z)))
      (hgR : (g : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t)) (u : ι → K),
      orthLinAct hS g (ν u) = ν (((thetaLin θ).symm (π ⟨g, hgR⟩)) u) := by
    intro g hgR u
    set r : ↥(bar M Q (Rt M (LB M Q B) t)) := ⟨g, hgR⟩ with hr
    set o := (thetaLin θ).symm (π r) with ho
    have hmv : ((π r : GL ι F) : Matrix ι ι F) *ᵥ thetaVec θ u = thetaVec θ (o u) := by
      rw [← thetaLin_mulVec θ o u, ho, MulEquiv.apply_symm_apply]
    have key := hΨπ r (Ψ.symm (thetaVec θ u))
    rw [AddEquiv.apply_symm_apply, hmv] at key
    have key2 := congrArg (fun z : ↥W => (z : M₀.E)) (Ψ.symm_apply_eq.mpr key.symm)
    exact key2.symm
  have hXact : ∀ b : B', ∃ o ∈ Ω, ∀ u, ΦX b (ν u) = ν (o u) := by
    intro b
    refine ⟨(thetaLin θ).symm (π ⟨incX b, hincXR b⟩), ?_, hAct (incX b) (hincXR b)⟩
    rw [mem_omegaK, MulEquiv.apply_symm_apply, ← hπr]; exact ⟨_, rfl⟩
  have hXsurj : ∀ o ∈ Ω, ∃ b : B', ∀ u, ΦX b (ν u) = ν (o u) := by
    intro o ho
    have hA : thetaLin θ o ∈ π.range := by rw [hπr]; exact ho
    obtain ⟨r, hr⟩ := hA
    obtain ⟨n, hn, x, hx, hrnx⟩ := hRX r.1 r.2
    obtain ⟨b, rfl⟩ := hx
    have hxR := hincXR b
    have hπx : π ⟨ψ₀ (1, b), hxR⟩ = thetaLin θ o := by
      have h1 : r = ⟨n, hNR hn⟩ * ⟨ψ₀ (1, b), hxR⟩ := Subtype.ext hrnx
      have h2 : π ⟨n, hNR hn⟩ = 1 := (hπk _).mpr hn
      rw [← hr, h1, map_mul, h2, one_mul]
    refine ⟨b, fun u => ?_⟩
    rw [show ΦX b (ν u) = orthLinAct hS (incX b) (ν u) from rfl, hAct (incX b) hxR u]
    show ν (((thetaLin θ).symm (π ⟨ψ₀ (1, b), hxR⟩)) u) = ν (o u)
    rw [hπx, MulEquiv.symm_apply_apply]
  have hWr : LinearMap.range ν = W := range_nuMap θ W Ψ hΨθ
  have hirr : ∀ S : Submodule K M₀.E, S ≤ LinearMap.range ν →
      (∀ x ∈ ΦX.range, ∀ v ∈ S, x v ∈ S) → S = ⊥ ∨ S = LinearMap.range ν := by
    intro S hSle hSinv
    rw [hWr] at hSle ⊢
    refine hc.irred_VtSub hS h35 ht S hSle (fun x hx v hv => ?_)
    obtain ⟨n', hn', y, hy, hxny⟩ := hRX x hx
    obtain ⟨b, rfl⟩ := hy
    have h1 : (ρ x).toAdd v = (ρ n').toAdd ((ρ (ψ₀ (1, b))).toAdd v) := by
      rw [hxny]; exact act_mul_apply ρ n' _ v
    have h2 : (ρ (ψ₀ (1, b))).toAdd v ∈ S := hSinv (ΦX b) ⟨b, rfl⟩ v hv
    rw [h1, hc.act_CN hS ht n' hn' _ (hSle h2)]
    exact h2
  have htM : t ∈ M := hc.LB_le_M ht
  have htH : t ∈ H0 M Z := hc.LB_le_H0 ht
  let tb : ↥(bar M Q (H0 M Z)) :=
    ⟨QuotientGroup.mk ⟨t, htM⟩, ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr htH, rfl⟩⟩
  let τ : M₀.E ≃ₗ[K] M₀.E := orthLinAct hS tb
  obtain ⟨htQ1, htQ2⟩ := hc.conj_mem_Q_of_mem_M htM
  have hτπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = τ (M₀.π x) := fun x hx => hS.conj ⟨t, htM⟩ x hx
  have hττ : τ * τ = 1 := by
    have : tb * tb = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk ⟨t, htM⟩ * QuotientGroup.mk ⟨t, htM⟩ : Mbar M Q) = 1
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.mem_subgroupOf.mpr (by
          show t * t ∈ Q
          rw [← _root_.sq]; exact hc.sq_mem_Q_of_mem_LB ht))
    rw [← map_mul, this, map_one]
  have hWrange : ∀ e, e ∈ W ↔ e ∈ LinearMap.range ((τ : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro e
    have h1 : e ∈ W ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) := hc.mem_VtSub hS.model t
    rw [h1, hVU]
    exact mem_img_comm_zpowers_sup_iff M₀ hS.model.reg τ htQ1 htQ2 hτπ e
  have hQ0 : ∀ u, M₀.Qf (ν u) = 0 := fun u =>
    (M₀.isElemAbelian_iff hS.model.reg (hc.Vt_le_Q t)).mp (hc.Vt_isElemAbelian h35 ht htQ) _
      ((hc.mem_VtSub hS.model t).mp (orthNuMap_mem θ W Ψ hΨθ u))
  let ψ : M₀.E →ₗ[K] M₀.E := (τ : M₀.E →ₗ[K] M₀.E) - 1
  have hψe : ∀ e, ψ e = τ e - e := fun e => rfl
  have hψrange : LinearMap.range ψ = LinearMap.range ν := by
    rw [hWr]; ext e; exact (hWrange e).symm
  have hψcomm : ∀ x ∈ ΦX.range, ∀ e, x (ψ e) = ψ (x e) := by
    rintro _ ⟨b, rfl⟩ e
    have hcomm := hc.bar_Rt_comm (t := ⟨t, htM⟩) (ψ₀ (1, b)) (hincXR b)
    have hxt : ΦX b * τ = τ * ΦX b := by
      show orthLinAct hS (incX b) * orthLinAct hS tb = orthLinAct hS tb * orthLinAct hS (incX b)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    have h1 : ΦX b (τ e) = τ (ΦX b e) := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) hxt
    simp only [hψe, map_sub, h1]
  have hψψ : ∀ e, ψ (ψ e) = 0 := by
    intro e
    have h1 : τ (τ e) = e := congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f e) hττ
    have h2 : ∀ x : M₀.E, x + x = 0 := fun x => by
      rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
    simp only [hψe, map_sub, h1]
    have e1 : e - τ e - (τ e - e) = (e + e) - (τ e + τ e) := by abel
    rw [e1, h2, h2, sub_zero]
  have hKcard : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hcardKF : Nat.card K = Nat.card F := hS.card.trans hFZ.symm
  have hfinW : Module.finrank K W = n := by
    have h1 : Nat.card W = Nat.card (ι → F) := Nat.card_congr Ψ.toEquiv
    rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := K), ← hcardKF,
      Nat.card_eq_fintype_card (α := ι), hιn] at h1
    exact Nat.pow_right_injective hKcard h1
  have hkerψ : LinearMap.ker ψ = LinearMap.range ν := by
    have hle : LinearMap.range ν ≤ LinearMap.ker ψ := by
      rw [hWr]
      intro w hw
      obtain ⟨e, rfl⟩ := (hWrange w).mp hw
      exact hψψ e
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hψrange] at h1
    have h2 : Module.finrank K (LinearMap.range ν) = n := by rw [hWr]; exact hfinW
    have h3 := hS.dim
    omega
  have hq := statedSL_quasisimple_of_card 2 F₂ le_rfl (by rw [hF₂card]; exact hc.hyp.q4)
  haveI hSLperf : Group.IsPerfect ↥(StatedSL 2 F₂) := hq.1
  haveI hApf : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom)
    eA.symm.surjective
  have hAnonab : ∃ a b : A, a * b ≠ b * a := by
    obtain ⟨a', b', hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    have hne : a * b ≠ b * a := fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])
    exact ⟨eA.symm a, eA.symm b, fun h => hne (eA.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hincAinj : Function.Injective incA := by
    intro a b h
    have h' : ψ₀ (a, 1) = ψ₀ (b, 1) :=
      congrArg (fun z : ↥(bar M Q (H0 M Z)) => (z : Mbar M Q)) h
    exact congrArg Prod.fst (hψ₀ h')
  have hΦAinj : Function.Injective ΦA := (orthLinAct_injective hS).comp hincAinj
  have hcore : TensorCoreHyp M₀.Qf M₀.B (qTransport θ qF) Ω ΦX.range ΦA.range ν ψ :=
    { qadd := M₀.Qf_add
      nondegB := M₀.nondeg
      nondegU := qTransport_nondeg θ qF hnd
      omega_isom := fun o ho v => omegaK_isom θ qF hXiso ho v
      omega_comm := fun f hf => omegaK_comm θ hscal f hf
      nu_inj := orthNuMap_injective θ W Ψ hΨθ
      x_isom := by rintro _ ⟨b, rfl⟩ e; exact orthLinAct_isom hS _ e
      a_isom := by rintro _ ⟨a, rfl⟩ e; exact orthLinAct_isom hS _ e
      a_comm_x := by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        show orthLinAct hS (incA a) * orthLinAct hS (incX b) = orthLinAct hS (incX b) * orthLinAct hS (incA a)
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (embProdFst_comm ψ₀ ⟨a, rfl⟩ ⟨b, rfl⟩)
      x_inv := by rintro _ ⟨b, rfl⟩; exact hXact b
      x_surj := fun o ho => by
        obtain ⟨b, hb⟩ := hXsurj o ho
        exact ⟨ΦX b, ⟨b, rfl⟩, hb⟩
      irr := hirr
      psi_comm := hψcomm
      psi_range := hψrange
      psi_ker := hkerψ
      w_sing := hQ0
      a_perfect := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ΦA)
      a_nonabelian := by
        obtain ⟨a, b, hab⟩ := hAnonab
        exact ⟨ΦA a, ⟨a, rfl⟩, ΦA b, ⟨b, rfl⟩, fun h => hab (hΦAinj (by rw [map_mul, map_mul, h]))⟩
      a_card := by
        rw [Nat.card_congr (MonoidHom.ofInjective hΦAinj).toEquiv.symm, hcardA, hS.card] }
  obtain ⟨φ, hφQ, hφν, hφX1, hφX2, hφA1, hφA2⟩ := TensorCoreHyp.tensor_core hcore
  have hLH : Lgen M (LB M Q B) ≤ H0 M Z := hc.Lgen_le_H0_sec4x
  have hmkS : ∀ s : ↥M, (s : G) ∈ Lgen M (LB M Q B) → (QuotientGroup.mk s : Mbar M Q) ∈ ψ₀.range := by
    intro s hs
    rw [hψ₀r]; exact ⟨s, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  refine ⟨K, hK, hKfin, inferInstance, γ, M₀, hS.model, θ, φ,
    ⟨qTransport_nondeg θ qF hnd, hφQ⟩, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hsM : s ∈ M := hLM hs
    obtain ⟨⟨a, b⟩, hab⟩ := hmkS ⟨s, hsM⟩ hs
    obtain ⟨g, hgdet, hgA⟩ := hφA1 (ΦA a) ⟨a, rfl⟩
    obtain ⟨o, ho, hoX⟩ := hφX1 (ΦX b) ⟨b, rfl⟩
    refine ⟨g, o, hgdet, fun v => omegaK_isom θ qF hXiso ho v, fun x hx => ?_⟩
    have hconj := hS.conj ⟨s, hsM⟩ x hx
    have hsab : (QuotientGroup.mk ⟨s, hsM⟩ : Mbar M Q) = ψ₀ (a, 1) * ψ₀ (1, b) := by
      rw [← map_mul, ← hab]; simp
    rw [hconj, hsab]
    have e1 : (ρ (ψ₀ (a, 1) * ψ₀ (1, b))).toAdd (M₀.π x) = ΦA a (ΦX b (M₀.π x)) := by
      rw [act_mul_apply]; rfl
    rw [e1, hgA (ΦX b (M₀.π x)), hoX (M₀.π x)]
    rfl
  · intro g hg
    obtain ⟨_, ⟨a, rfl⟩, hga⟩ := hφA2 g hg
    have hmem : ψ₀ (a, 1) ∈ bar M Q (Lgen M (LB M Q B)) := by
      rw [← hψ₀r]; exact ⟨(a, 1), rfl⟩
    obtain ⟨s, hsL, hsa⟩ := orth_exists_mk_of_mem_bar hmem
    refine ⟨(s : G), hsL, fun x hx => ?_⟩
    have hconj := hS.conj s x hx
    rw [hconj, hsa]
    have e1 : (ρ (ψ₀ (a, 1))).toAdd (M₀.π x) = ΦA a (M₀.π x) := rfl
    rw [e1, hga (M₀.π x)]
    rfl
  · intro a w ha hw
    have ha' : qF (thetaVec θ a) = 0 := by rw [← theta_qTransport θ qF a, ha, map_zero]
    have hw' : polar qF (thetaVec θ a) (thetaVec θ w) = 0 := by
      rw [← theta_polar_qTransport θ qF a w, hw, map_zero]
    have hoΩ : eichler (qTransport θ qF) a w ∈ Ω := by
      rw [mem_omegaK, thetaLin_eichler θ qF ha hw]
      exact hEich _ _ ha' hw'
    obtain ⟨_, ⟨b, rfl⟩, hxb⟩ := hφX2 _ hoΩ
    have hmem : ψ₀ (1, b) ∈ bar M Q (Lgen M (LB M Q B)) := by
      rw [← hψ₀r]; exact ⟨(1, b), rfl⟩
    obtain ⟨s, hsL, hsa⟩ := orth_exists_mk_of_mem_bar hmem
    refine ⟨(s : G), hsL, fun x hx => ?_⟩
    have hconj := hS.conj s x hx
    rw [hconj, hsa]
    have e1 : (ρ (ψ₀ (1, b))).toAdd (M₀.π x) = ΦX b (M₀.π x) := rfl
    rw [e1, hxb (M₀.π x)]
    ext <;> simp [orthTensor]
  ·
    obtain ⟨b₁, hb₁0, -, hb₁line, -, -⟩ := hc.dictB hS.model
    have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
    have hb₁B : b₁ ∈ M₀.img B := (hb₁line b₁).mpr ⟨1, (one_smul K b₁).symm⟩
    have hb₁W : b₁ ∈ W := by
      obtain ⟨u, huB, huQ, hu⟩ := M₀.mem_img.mp hb₁B
      exact (hc.mem_VtSub hS.model t).mpr (M₀.mem_img.mpr ⟨u, hBV huB, huQ, hu⟩)
    obtain ⟨u₀, hu₀⟩ : b₁ ∈ LinearMap.range ν := by rw [hWr]; exact hb₁W
    have hu₀ne : u₀ ≠ 0 := by
      rintro rfl
      exact hb₁0 (by rw [← hu₀, map_zero])
    have hφb₁ : φ b₁ = (u₀, 0) := by rw [← hu₀]; exact hφν u₀
    refine ⟨u₀, hu₀ne, fun e => ?_, fun hRoot => ?_⟩
    · rw [hb₁line e]
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s, by rw [map_smul, hφb₁]⟩
      · rintro ⟨s, hs⟩
        refine ⟨s, φ.injective ?_⟩
        rw [map_smul, hφb₁]
        exact hs
    · have hs := orth_singular_of_transport hc hS ht Ψ π hπr hπk hΨπ (hsing hRoot)
        ⟨b₁, hb₁W⟩ hb₁B
      have hΨu : Ψ ⟨b₁, hb₁W⟩ = thetaVec θ u₀ := by
        have h1 : (Ψ.symm (thetaVec θ u₀) : M₀.E) = b₁ := hu₀
        have h2 : (⟨b₁, hb₁W⟩ : ↥W) = Ψ.symm (thetaVec θ u₀) := Subtype.ext h1.symm
        rw [h2, AddEquiv.apply_symm_apply]
      rw [hΨu] at hs
      apply θ.injective
      rw [theta_qTransport, map_zero]
      exact hs

end Glue

end PartF

section PartG

open scoped Matrix commutatorElement
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (eichler toLinEquiv)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

@[expose] def OrthBLine {G : Type} [Group G] {Q Z : Subgroup G}
    {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {ι : Type}
    (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)) (B : Subgroup G) : Prop :=
  ∃ (c : Fin 2 → K) (u : ι → K), c ≠ 0 ∧ u ≠ 0 ∧
    (∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ s : K, φ e = s • (c 0 • u, c 1 • u)) ∧
    (Stroth310RootStatement → qU u = 0)

theorem OrthBLine.of_pure {G : Type} [Group G] {Q Z : Subgroup G}
    {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type}
    {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} {B : Subgroup G}
    {u : ι → K} (hu : u ≠ 0) (hline : ∀ e : M₀.E, e ∈ M₀.img B ↔ ∃ s : K, φ e = s • (u, 0))
    (hsing : Stroth310RootStatement → qU u = 0) : OrthBLine M₀ qU φ B := by
  refine ⟨![1, 0], u, fun h => one_ne_zero (congrFun h 0), hu, fun e => ?_, hsing⟩
  simpa using hline e

section Plus

theorem card_statedOmega_plus_eq {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) :
    (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map hm,
    Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact CFSG.SeitzReduction.OmegaPilot.card_elementaryGroup_quadPlus_of_three_le hm

theorem card_statedSL_two_lt_omega_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) (hq : 4 ≤ Nat.card K) :
    Nat.card K * (Nat.card K ^ 2 - 1) < Nat.card ↥(StatedOmega (StatedQuadPlus m K)) := by
  have hQ : (4 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq
  have h1 : (Nat.card K : ℤ) ^ 3 ≤ (Nat.card K : ℤ) ^ (m * (m - 1)) :=
    pow_le_pow_right₀ (by omega) (by
      have : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
      omega)
  have h2 : (1 : ℤ) ≤ (Nat.card K : ℤ) ^ m - 1 := by
    have : (1 : ℤ) < (Nat.card K : ℤ) ^ m := one_lt_pow₀ (by omega) (by omega)
    omega
  have h3 : (1 : ℤ) ≤ ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    have : (0 : ℤ) < ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
      apply Finset.prod_pos
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have : (1 : ℤ) < (Nat.card K : ℤ) ^ (2 * i) := one_lt_pow₀ (by omega) (by omega)
      omega
    omega
  have h4 : (Nat.card K : ℤ) ^ (m * (m - 1)) ≤
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    have hp : (0 : ℤ) ≤ (Nat.card K : ℤ) ^ (m * (m - 1)) := by positivity
    calc (Nat.card K : ℤ) ^ (m * (m - 1)) = (Nat.card K : ℤ) ^ (m * (m - 1)) * 1 * 1 := by ring
      _ ≤ _ := by
        apply mul_le_mul (mul_le_mul le_rfl h2 (by norm_num) hp) h3 (by norm_num) (by positivity)
  have h5 : (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) < (Nat.card K : ℤ) ^ 3 := by nlinarith
  have := card_statedOmega_plus_eq (K := K) hm
  have h6 : ((Nat.card K * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) <
      (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) := by
    rw [this]
    have hsub : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub this]; ring
    push_cast [hsub]
    linarith
  exact_mod_cast h6

theorem smith24E2Plus_tensorB (h34 : Stroth34Statement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G} {m : ℕ}
    (hcfg : SmithOrthCfg M Q Z B) (ht : CtxD4 M Q Z B t) (hm : 3 ≤ m)
    (hE : CaseE2Plus M Q Z B t m) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hNat : OmegaPlusNat hcfg.ctx t m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) ∧
          OrthBLine M₀ qU φ B := by
  have hc : Ctx M Q Z B := hcfg.ctx
  haveI : (Q.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2
  have hw : Width Q Z (2 * m) := by
    unfold Width
    rw [hE.2.1]
    congr 1
    ring
  have hn : 2 < 2 * m := by omega
  have htLB : t ∈ LB M Q B := ht.2.1
  have htQ : t ∉ Q := ht.2.2.1
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  obtain ⟨K', hF', hFin', hK'card, hnat⟩ := hNat
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'card.trans hZ2)
  have hq4 : 4 ≤ Nat.card K' := by rw [hK'card]; exact hc.hyp.q4
  have hcoe : ⇑(quadPlus m K') = StatedQuadPlus m K' :=
    CFSG.LieType.Universal.Spin.coe_quadPlus m K'
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hVU := (stroth310Chi_of_34 h34 G M Q Z B hc (2 * m) t ⟨hw, hn, hno, hgen, htLB, htQ⟩
    (Or.inr ⟨K', hF', hFin', hK'card, Or.inl ⟨m, hm, hnat⟩⟩)).1
  have hnat' : NaturalRep (ι := Fin m ⊕ Fin m) K' (StatedOmega ⇑(quadPlus m K'))
      (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := by rw [hcoe]; exact hnat
  have hsing : Stroth310RootStatement →
      NatSingular hc t (quadPlus m K') (StatedOmega ⇑(quadPlus m K')) := by
    intro hRoot
    rw [hcoe]
    exact hc.natSingular_of h34 hRoot ⟨hw, hn, hno, hgen, htLB, htQ⟩
      (Or.inr ⟨K', hF', hFin', hK'card, Or.inl ⟨m, hm, hnat⟩⟩) hK'card (CFSG.ClassicalGroups.Orthogonal.ElemMatrixIso.plus hm)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K')
      (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega)
      (addCommutantScalar_statedOmegaPlus hm)
  have hres := orth_tensor_glue hc hw hn hno hgen h34 htLB htQ hVU
    (quadPlus m K') hK'card (by simp [Fintype.card_sum]; ring)
    (fun u hu => (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K').1 u
      (fun v => by simpa [QuadraticMap.polarBilin_apply_apply] using hu v))
    (fun A hA v => mem_statedOmega_preserves (Q := quadPlus m K') rfl hA v)
    (by rw [hcoe]; exact addCommutantScalar_statedOmegaPlus hm)
    (fun a' w' _ _ => by
      rw [hcoe, CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map hm]
      exact Subgroup.mem_map.mpr ⟨eichler (quadPlus m K') a' w',
        CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup _ a' w', rfl⟩)
    (by rw [hcoe]; exact (endg_omegaPlus_facts hq4 hm).1)
    (by rw [hcoe, ← hK'card]; exact card_statedSL_two_lt_omega_plus hm hq4)
    hnat' hsing
    (P₂ := IsOmegaPlus m (Nat.card Z)) (fun X _ ⟨K'', hK''f, hK''fin, hK''card, ⟨e⟩⟩ => by
      haveI : CharP K'' 2 := charP_two_of_card_eq_two_pow (hK''card.trans hZ2)
      have h1 := card_statedOmega_plus_eq (K := K'') hm
      have h2 := card_statedOmega_plus_eq (K := K') hm
      rw [hK''card] at h1
      rw [hK'card] at h2
      have h3 : (Nat.card ↥(StatedOmega (StatedQuadPlus m K'')) : ℤ) =
          (Nat.card ↥(StatedOmega (StatedQuadPlus m K')) : ℤ) := h1.trans h2.symm
      rw [Nat.card_congr e.toEquiv, hcoe]
      exact_mod_cast h3)
    hE.2.2.2.2
  obtain ⟨K, hK, hKfin, hKchar, γ, M₀, hM, θ, φ, hpre, hact, hsl, heich, u, hu0, hline, hsu⟩ := hres
  exact ⟨K, hK, hKfin, hKchar, γ, M₀, hM, Fin m ⊕ Fin m, inferInstance, inferInstance,
    qTransport θ (quadPlus m K'), φ, hpre, ⟨hact, hsl, heich⟩, OrthBLine.of_pure hu0 hline hsu⟩

end Plus

section Minus

theorem card_orth_three_minus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) =
      2 * Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ := by
  have hmin := CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus (K := K) (m := 3)
    (by norm_num) hirr
  obtain ⟨-, -, -, hidx, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (quadMinus 3 K b c) hmin.nondeg (Or.inr (by rw [hmin.finrank_eq]))
      (fun U hU => hmin.noTS U (by rw [hmin.finrank_eq] at hU; omega))
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hcard := ((⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c))).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  omega

theorem card_statedOmega_minus_eq {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | h4
  · rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le (n := 3)
        (by norm_num) hirr, Subgroup.card_map_of_injective (MulEquiv.injective _),
      ← CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
        (n := 3) (by norm_num) hirr]
    have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) : ℤ) =
        2 * (Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ : ℤ) := by
      exact_mod_cast card_orth_three_minus hirr
    have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (3 * (3 - 1)) * ((Nat.card K : ℤ) ^ 3 + 1) *
          ∏ i ∈ Finset.Icc 1 (3 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
      (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 2 hirr).2
    linarith
  · rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map h4 hirr,
      Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadMinus h4 hirr

theorem card_statedSL_two_lt_omega_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hq : 4 ≤ Nat.card K) :
    Nat.card K * (Nat.card K ^ 2 - 1) < Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) := by
  have hQ : (4 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast hq
  have h1 : (Nat.card K : ℤ) ^ 3 ≤ (Nat.card K : ℤ) ^ (m * (m - 1)) :=
    pow_le_pow_right₀ (by omega) (by
      have : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega)
      omega)
  have h2 : (1 : ℤ) ≤ (Nat.card K : ℤ) ^ m + 1 := by
    have : (0 : ℤ) ≤ (Nat.card K : ℤ) ^ m := by positivity
    omega
  have h3 : (1 : ℤ) ≤ ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    have : (0 : ℤ) < ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
      apply Finset.prod_pos
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have : (1 : ℤ) < (Nat.card K : ℤ) ^ (2 * i) := one_lt_pow₀ (by omega) (by omega)
      omega
    omega
  have h4 : (Nat.card K : ℤ) ^ (m * (m - 1)) ≤
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    have hp : (0 : ℤ) ≤ (Nat.card K : ℤ) ^ (m * (m - 1)) := by positivity
    calc (Nat.card K : ℤ) ^ (m * (m - 1)) = (Nat.card K : ℤ) ^ (m * (m - 1)) * 1 * 1 := by ring
      _ ≤ _ := by
        apply mul_le_mul (mul_le_mul le_rfl h2 (by norm_num) hp) h3 (by norm_num) (by positivity)
  have h5 : (Nat.card K : ℤ) * ((Nat.card K : ℤ) ^ 2 - 1) < (Nat.card K : ℤ) ^ 3 := by nlinarith
  have := card_statedOmega_minus_eq (K := K) hm hirr
  have h6 : ((Nat.card K * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) <
      (Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) : ℤ) := by
    rw [this]
    have hsub : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub this]; ring
    push_cast [hsub]
    linarith
  exact_mod_cast h6

theorem smith24E2Minus_tensorB (h34 : Stroth34Statement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G} {m : ℕ}
    (hcfg : SmithOrthCfg M Q Z B) (ht : CtxD4 M Q Z B t) (hm : 3 ≤ m)
    (hE : CaseE2Minus M Q Z B t m) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hNat : OmegaMinusNat hcfg.ctx t m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) ∧
          OrthBLine M₀ qU φ B := by
  have hc : Ctx M Q Z B := hcfg.ctx
  haveI : (Q.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2
  have hw : Width Q Z (2 * m) := by
    unfold Width
    rw [hE.2.1]
    congr 1
    ring
  have hn : 2 < 2 * m := by omega
  have htLB : t ∈ LB M Q B := ht.2.1
  have htQ : t ∉ Q := ht.2.2.1
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  obtain ⟨K', hF', hFin', hK'card, b, c, hirr, hnat⟩ := hNat
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'card.trans hZ2)
  have hq4 : 4 ≤ Nat.card K' := by rw [hK'card]; exact hc.hyp.q4
  have hcoe : ⇑(quadMinus m K' b c) = StatedQuadMinus m K' b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus m K' b c
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hVU := (stroth310Chi_of_34 h34 G M Q Z B hc (2 * m) t ⟨hw, hn, hno, hgen, htLB, htQ⟩
    (Or.inr ⟨K', hF', hFin', hK'card, Or.inr ⟨m, b, c, by omega, hirr, hnat⟩⟩)).1
  have hnat' : NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K'
      (StatedOmega ⇑(quadMinus m K' b c))
      (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := by rw [hcoe]; exact hnat
  have hsing : Stroth310RootStatement →
      NatSingular hc t (quadMinus m K' b c) (StatedOmega ⇑(quadMinus m K' b c)) := by
    intro hRoot
    rw [hcoe]
    exact hc.natSingular_of h34 hRoot ⟨hw, hn, hno, hgen, htLB, htQ⟩
      (Or.inr ⟨K', hF', hFin', hK'card, Or.inr ⟨m, b, c, by omega, hirr, hnat⟩⟩) hK'card
      (CFSG.ClassicalGroups.Orthogonal.ElemMatrixIso.minus (by omega) hirr)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K' hirr)
      (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]
        omega)
      (addCommutantScalar_statedOmegaMinus (by omega) hirr)
  have hres := orth_tensor_glue hc hw hn hno hgen h34 htLB htQ hVU
    (quadMinus m K' b c) hK'card (by simp [Fintype.card_sum]; omega)
    (fun u hu => (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K' hirr).1 u
      (fun v => by simpa [QuadraticMap.polarBilin_apply_apply] using hu v))
    (fun A hA v => mem_statedOmega_preserves (Q := quadMinus m K' b c) rfl hA v)
    (by rw [hcoe]; exact addCommutantScalar_statedOmegaMinus (by omega) hirr)
    (fun a' w' _ _ => by
      rw [hcoe, CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le
        (by omega) hirr]
      exact Subgroup.mem_map.mpr ⟨eichler (quadMinus m K' b c) a' w',
        CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup _ a' w', rfl⟩)
    (by rw [hcoe]; exact (endg_omegaMinus_facts hq4 (by omega) hirr).1)
    (by rw [hcoe, ← hK'card]; exact card_statedSL_two_lt_omega_minus hm hirr hq4)
    hnat' hsing
    (P₂ := IsOmegaMinus m (Nat.card Z))
    (fun X _ ⟨K'', hK''f, hK''fin, hK''card, b'', c'', hirr'', ⟨e⟩⟩ => by
      haveI : CharP K'' 2 := charP_two_of_card_eq_two_pow (hK''card.trans hZ2)
      have h1 := card_statedOmega_minus_eq (K := K'') hm hirr''
      have h2 := card_statedOmega_minus_eq (K := K') hm hirr
      rw [hK''card] at h1
      rw [hK'card] at h2
      have h3 : (Nat.card ↥(StatedOmega (StatedQuadMinus m K'' b'' c'')) : ℤ) =
          (Nat.card ↥(StatedOmega (StatedQuadMinus m K' b c)) : ℤ) := h1.trans h2.symm
      rw [Nat.card_congr e.toEquiv, hcoe]
      exact_mod_cast h3)
    hE.2.2.2.2
  obtain ⟨K, hK, hKfin, hKchar, γ, M₀, hM, θ, φ, hpre, hact, hsl, heich, u, hu0, hline, hsu⟩ := hres
  exact ⟨K, hK, hKfin, hKchar, γ, M₀, hM, Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, inferInstance,
    inferInstance, qTransport θ (quadMinus m K' b c), φ, hpre, ⟨hact, hsl, heich⟩,
    OrthBLine.of_pure hu0 hline hsu⟩

end Minus

end PartG

end CFSG.RankThree.GF2n.Smith81
