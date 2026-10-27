module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispUC
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrB
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigOQuad

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
open CFSG.RankThree.Classical2 (orthDerived)

section Transfer

variable {G : Type} [Group G] {Bs N : Subgroup G} {Ω : Type} [Group Ω]

theorem qtwoDB43_beta_eq_one_iff (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (hΩ : Subgroup.center Ω = ⊥) (σ : ↥N ≃* Ω) (β : ↥Bs →* Ω)
    (hcompat : ∀ (s : ↥Bs) (n : ↥N), σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹)
    (s : ↥Bs) : β s = 1 ↔ ggGamma N hBsN s = 1 := by
  constructor
  · intro hβ
    refine MulEquiv.ext fun n => ?_
    apply σ.injective
    rw [hcompat s n, hβ, MulAut.one_apply]
    simp
  · intro hγ
    have hcenter : β s ∈ Subgroup.center Ω := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := hcompat s (σ.symm z)
      rw [hγ, MulAut.one_apply, σ.apply_symm_apply] at hz
      exact (mul_inv_eq_iff_eq_mul.mp hz.symm).symm
    rw [hΩ] at hcenter
    simpa using hcenter

theorem qtwoDB43_commute_of_commute (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (σ : ↥N ≃* Ω) (β : ↥Bs →* Ω)
    (hcompat : ∀ (s : ↥Bs) (n : ↥N), σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹)
    (s : ↥Bs) (n : ↥N) (h : (s : G) * (n : G) = (n : G) * (s : G)) :
    σ n * β s = β s * σ n := by
  have hγ : ggGamma N hBsN s n = n := by
    apply Subtype.ext
    rw [ggGamma_coe, h]
    group
  have hz := hcompat s n
  rw [hγ] at hz
  exact (mul_inv_eq_iff_eq_mul.mp hz.symm).symm

theorem qtwoDB43_exists_tau {m : ℕ} (β : ↥Bs →* Ω) (βL : Additive ↥Bs ≃+ DVec m) :
    ∃ τ : Multiplicative (DVec m) →* Ω,
      ∀ s : ↥Bs, τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) = β s := by
  refine ⟨{ toFun := fun v => β (Additive.toMul (βL.symm (Multiplicative.toAdd v)))
            map_one' := by simp
            map_mul' := by
              intro a b
              simp only [toAdd_mul, map_add, toMul_add, map_mul] }, ?_⟩
  intro s
  simp

theorem qtwoDB43_weyl_realize {m : ℕ} (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (hΩ : Subgroup.center Ω = ⊥) (σ : ↥N ≃* Ω) (β : ↥Bs →* Ω)
    (hcompat : ∀ (s : ↥Bs) (n : ↥N), σ (ggGamma N hBsN s n) = β s * σ n * (β s)⁻¹)
    (βL : Additive ↥Bs ≃+ DVec m) (w : DVec m ≃ₗ[ZMod 3] DVec m)
    (φ : ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range))
    (hφ : ∀ s : ↥Bs, (φ : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
      (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm (w (βL (Additive.ofMul s)))))) :
    ∃ y : Ω, ∀ s : ↥Bs,
      y * β s * y⁻¹ = β (Additive.toMul (βL.symm (w (βL (Additive.ofMul s))))) := by
  obtain ⟨g₀, hg₀H, -, hg₀act⟩ := mem_ggAutomizer_iff.mp φ.2
  obtain ⟨n₀, hn₀⟩ := MonoidHom.mem_range.mp hg₀H
  rw [← hn₀] at hg₀act
  refine ⟨σ n₀, ?_⟩
  intro s
  let s' : ↥Bs := Additive.toMul (βL.symm (w (βL (Additive.ofMul s))))
  have hs' : βL (Additive.ofMul s') = w (βL (Additive.ofMul s)) := by
    simp [s']
  have hact : (ggGamma N hBsN s' : MulAut ↥N) =
      (MulAut.conj n₀) * (ggGamma N hBsN s) * (MulAut.conj n₀)⁻¹ := by
    have h1 := hg₀act ((ggGamma N hBsN).rangeRestrict s)
    rw [hφ s] at h1
    simpa only [MonoidHom.coe_rangeRestrict] using h1
  have hcomp : ∀ u : ↥N, σ (((MulAut.conj n₀) * (ggGamma N hBsN s) *
        (MulAut.conj n₀)⁻¹) u) =
      (σ n₀ * β s * (σ n₀)⁻¹) * σ u * (σ n₀ * β s * (σ n₀)⁻¹)⁻¹ := by
    intro u
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, hcompat s (n₀⁻¹ * u * n₀)]
    rw [map_mul, map_mul, map_inv]
    group
  have key : ∀ z : Ω, β s' * z * (β s')⁻¹ =
      (σ n₀ * β s * (σ n₀)⁻¹) * z * (σ n₀ * β s * (σ n₀)⁻¹)⁻¹ := by
    intro z
    have hcong := congrArg (fun f : MulAut ↥N => σ (f (σ.symm z))) hact
    rw [hcompat s' (σ.symm z), σ.apply_symm_apply, hcomp (σ.symm z),
      σ.apply_symm_apply] at hcong
    exact hcong
  have hcenter : (σ n₀ * β s * (σ n₀)⁻¹)⁻¹ * β s' ∈ Subgroup.center Ω := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h2 : β s' * z = (σ n₀ * β s * (σ n₀)⁻¹) * z * (σ n₀ * β s * (σ n₀)⁻¹)⁻¹ * β s' := by
      have h3 := congrArg (fun t => t * β s') (key z)
      simpa [mul_assoc] using h3
    have h4 : ((σ n₀ * β s * (σ n₀)⁻¹)⁻¹ * β s') * z =
        z * ((σ n₀ * β s * (σ n₀)⁻¹)⁻¹ * β s') := by
      rw [mul_assoc, h2]
      group
    exact h4.symm
  have h1 : (σ n₀ * β s * (σ n₀)⁻¹)⁻¹ * β s' = 1 := by
    have hc := hcenter
    rw [hΩ] at hc
    simpa using hc
  have hfin : β s' = σ n₀ * β s * (σ n₀)⁻¹ := by
    have hc := congrArg (fun t => (σ n₀ * β s * (σ n₀)⁻¹) * t) h1
    simpa [mul_assoc] using hc
  rw [← hs']
  simp only [AddEquiv.symm_apply_apply, toMul_ofMul]
  exact hfin.symm

end Transfer

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB43_x_commute_J₁ (hbase : QTwoUnitBase p B Bs x L ψ ε) {n : G}
    (hn : n ∈ qtwoDelJ ψ c) : x * n = n * x := by
  obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.mp hn
  have hnL : n ∈ L := by
    rw [← hbase.range]
    exact ⟨y, hyn⟩
  have hx : x ∈ Subgroup.centralizer (L : Set G) := by
    have : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hbase.cent]
      exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp this).2
  exact (Subgroup.mem_centralizer_iff.mp hx n hnL).symm

theorem qtwoDB43_x_commute_J₂ (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hdel : QTwoUnitDel Bs βL a b c α g b') {n : G}
    (hn : n ∈ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom) :
    ((α ⟨x, hbase.x_mem⟩ : ↥Bs) : G) * n = n * ((α ⟨x, hbase.x_mem⟩ : ↥Bs) : G) := by
  obtain ⟨j, hj, hjn⟩ := Subgroup.mem_map.mp hn
  have hj' : (MulAut.conj g) j = n := hjn
  rw [MulAut.conj_apply] at hj'
  have hxj : x * j = j * x := qtwoDB43_x_commute_J₁ hbase hj
  rw [hdel.conj ⟨x, hbase.x_mem⟩, ← hj']
  calc
    g * x * g⁻¹ * (g * j * g⁻¹) = g * (x * j) * g⁻¹ := by group
    _ = g * (j * x) * g⁻¹ := by rw [hxj]
    _ = g * j * g⁻¹ * (g * x * g⁻¹) := by group

theorem qtwoDB43_model_of (hRig : GGLabelRigidInput) (hm : 6 ≤ m) {N : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hinner : GGInnerDiagOn Bs N) (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (↥N ⧸ Subgroup.center ↥N))
    (htag : lab = ⟨.D, m, 1⟩ ∨ lab = ⟨.twD, m, 1⟩)
    (hker_char : ∀ s : ↥Bs, ggGamma N hBsN s = 1 ↔
      ∀ k : Fin m, k ≠ c → βL (Additive.ofMul s) k = 0)
    {Θ : ↥(dEvenStab m (Pi.single c 1)) →*
      ↥(ggAutomizer (MulAut.conj : ↥N →* MulAut ↥N).range (ggGamma N hBsN).range)}
    (hΘact : ∀ (w : ↥(dEvenStab m (Pi.single c 1))) (s : ↥Bs),
      (Θ w : MulAut ↥(ggGamma N hBsN).range) ((ggGamma N hBsN).rangeRestrict s) =
        (ggGamma N hBsN).rangeRestrict (Additive.toMul (βL.symm
          ((w : DVec m ≃ₗ[ZMod 3] DVec m) (βL (Additive.ofMul s)))))) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : FiniteDimensional (ZMod 2) V)
      (Q : QuadraticForm (ZMod 2) V) (σ : ↥N ≃* ↥(orthDerived Q))
      (τ : Multiplicative (DVec m) →* ↥(orthDerived Q)),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank (ZMod 2) V = 2 * m ∧
      (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ lab = ⟨.D, m, 1⟩) ∧
      (∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0) ∧
      (∀ (s : ↥Bs) (n : ↥N), σ (ggGamma N hBsN s n) =
        τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * σ n *
          (τ (Multiplicative.ofAdd (βL (Additive.ofMul s))))⁻¹) ∧
      (∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : ↥(orthDerived Q), ∀ v : DVec m,
        y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v))) ∧
      (∀ (s : ↥Bs) (n : ↥N), (s : G) * n = n * s →
        σ n * τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) =
          τ (Multiplicative.ofAdd (βL (Additive.ofMul s))) * σ n) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨V, i₁, i₂, i₃, Q, σ, β, hQ, hdim, hplus, hZ, hcompat⟩ :=
    qtwoDB43_quad hRig hm hinner hBs hSC hBsN hΛ hlab htag
  obtain ⟨τ, hτ⟩ := qtwoDB43_exists_tau β βL
  refine ⟨V, i₁, i₂, i₃, Q, σ, τ, hQ, hdim, hplus, ?_, ?_, ?_, ?_⟩
  · intro v
    let s : ↥Bs := Additive.toMul (βL.symm v)
    have hs : βL (Additive.ofMul s) = v := by simp [s]
    rw [← hs, hτ s]
    exact (qtwoDB43_beta_eq_one_iff hBsN hZ σ β hcompat s).trans (hker_char s)
  · intro s n
    rw [hcompat s n, ← hτ s]
  · intro w hw
    obtain ⟨y, hy⟩ := qtwoDB43_weyl_realize hBsN hZ σ β hcompat βL
      (w : DVec m ≃ₗ[ZMod 3] DVec m) (Θ ⟨w, hw⟩) (hΘact ⟨w, hw⟩)
    refine ⟨y, ?_⟩
    intro v
    let s : ↥Bs := Additive.toMul (βL.symm v)
    have hs : βL (Additive.ofMul s) = v := by simp [s]
    have hy' := hy s
    rw [hs] at hy'
    have hβs : τ (Multiplicative.ofAdd v) = β s := by rw [← hs, hτ s]
    have hβwv : τ (Multiplicative.ofAdd ((w : DVec m ≃ₗ[ZMod 3] DVec m) v)) =
        β (Additive.toMul (βL.symm ((w : DVec m ≃ₗ[ZMod 3] DVec m) v))) := by
      rw [← hτ (Additive.toMul (βL.symm ((w : DVec m ≃ₗ[ZMod 3] DVec m) v)))]
      congr 1
      simp
    rw [hβs, hβwv]
    exact hy'
  · intro s n hsn
    rw [hτ s]
    exact qtwoDB43_commute_of_commute hBsN σ β hcompat s n hsn

end CFSG.StandardType.QTwo

end
