module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatPairing
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem commutator_conj_expand (r y τ : G) :
    ⁅r * y * r⁻¹, τ⁆ = r * ((⁅y, ⁅r⁻¹, τ⁆⁆ * ⁅⁅r⁻¹, τ⁆, ⁅y, τ⁆⁆) * ⁅y, τ⁆) * r⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem conj_mul_of_conj_eq {r z a : G} (hz : r * z * r⁻¹ = z) :
    r * (z * a) * r⁻¹ = z * (r * a * r⁻¹) := by
  calc r * (z * a) * r⁻¹ = (r * z * r⁻¹) * (r * a * r⁻¹) := by group
    _ = z * (r * a * r⁻¹) := by rw [hz]

theorem exists_scalar_of_equivariant {Q V Z R : Subgroup G} {t : G}
    (D : NatCommData Q V Z R t) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    {X : Subgroup (GL ι K)} (hX : AddCommutantScalar X) (φ : ↥R →* GL ι K)
    (hφ : φ.range = X)
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hVR : R ≤ Subgroup.normalizer (V : Set G))
    (c : ↥Q → (ι → K)) (hadd : ∀ y y' : ↥Q, c (y * y') = c y + c y')
    (hW : ∀ y : ↥Q, ⁅(y : G), t⁆ ∈ Z → c y = 0)
    (hequiv : ∀ (r : ↥R) (y : ↥Q),
      c ⟨(r : G) * y * (r : G)⁻¹, D.R_normQ r r.2 y y.2⟩ = (φ r : Matrix ι ι K) *ᵥ c y) :
    ∃ κ : K, ∀ y : ↥Q, c y = κ • kapVec D ψ y := by
  obtain ⟨g, hgdef⟩ : ∃ g : (ι → K) → (ι → K),
      ∀ x : ι → K, g x = c (Classical.choose (exists_kapVec D ψ x)) :=
    ⟨fun x => c (Classical.choose (exists_kapVec D ψ x)), fun x => rfl⟩
  have hkey : ∀ y y₀ : ↥Q, kapVec D ψ y₀ = kapVec D ψ y → c y₀ = c y := by
    intro y y₀ hy₀
    have hq : kapVec D ψ (y * y₀⁻¹) = 0 := by
      rw [kapVec_mul, kapVec_inv, hy₀, add_neg_cancel]
    have hqZ : ⁅((y * y₀⁻¹ : ↥Q) : G), t⁆ ∈ Z := (secVec_eq_zero_iff ψ _).mp hq
    have h1 : c (y * y₀⁻¹ * y₀) = c (y * y₀⁻¹) + c y₀ := hadd _ _
    rw [inv_mul_cancel_right, hW (y * y₀⁻¹) hqZ, zero_add] at h1
    exact h1.symm
  have hg : ∀ y : ↥Q, g (kapVec D ψ y) = c y := by
    intro y
    rw [hgdef]
    exact hkey y _ (Classical.choose_spec (exists_kapVec D ψ (kapVec D ψ y)))
  have hgadd : ∀ x₁ x₂ : ι → K, g (x₁ + x₂) = g x₁ + g x₂ := by
    intro x₁ x₂
    obtain ⟨y₁, rfl⟩ := exists_kapVec D ψ x₁
    obtain ⟨y₂, rfl⟩ := exists_kapVec D ψ x₂
    rw [← kapVec_mul D ψ, hg, hg, hg, hadd]
  obtain ⟨ε, hεg⟩ : ∃ ε : (ι → K) →+ (ι → K), ∀ x, ε x = g x :=
    ⟨AddMonoidHom.mk' g hgadd, fun x => rfl⟩
  have hε : ∀ y : ↥Q, ε (kapVec D ψ y) = c y := fun y => (hεg _).trans (hg y)
  have hcomm : ∀ A ∈ X, ∀ v : ι → K,
      ε ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ ε v := by
    intro A hA v
    rw [← hφ] at hA
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hA
    obtain ⟨y, rfl⟩ := exists_kapVec D ψ v
    rw [← kapVec_conj D ψ hψ hVR r y, hε, hε, hequiv]
  obtain ⟨κ, hκ⟩ := hX ε hcomm
  exact ⟨κ, fun y => (hε y).symm.trans (hκ _)⟩

theorem NatCommData.secVec_comm_mul {Q V Z R : Subgroup G} {t : G} (D : NatCommData Q V Z R t)
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [(Z.subgroupOf V).Normal]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) {τ : G}
    (hτ : ∀ y ∈ Q, ⁅y, τ⁆ ∈ V) (y y' : ↥Q) :
    secVec ψ ⟨⁅((y * y' : ↥Q) : G), τ⁆, hτ _ (y * y').2⟩ =
      secVec ψ ⟨⁅(y : G), τ⁆, hτ _ y.2⟩ + secVec ψ ⟨⁅(y' : G), τ⁆, hτ _ y'.2⟩ := by
  have hv' : ⁅(y' : G), τ⁆ ∈ V := hτ _ y'.2
  have hv : ⁅(y : G), τ⁆ ∈ V := hτ _ y.2
  have hz : ⁅(y : G), ⁅(y' : G), τ⁆⁆ ∈ Z := D.comm_Z y y.2 _ (D.VQ hv')
  have e : (⟨⁅((y * y' : ↥Q) : G), τ⁆, hτ _ (y * y').2⟩ : ↥V) =
      ⟨⁅(y : G), ⁅(y' : G), τ⁆⁆, D.ZV hz⟩ * ⟨⁅(y' : G), τ⁆, hv'⟩ * ⟨⁅(y : G), τ⁆, hv⟩ := by
    apply Subtype.ext
    show ⁅(y : G) * (y' : G), τ⁆ = ⁅(y : G), ⁅(y' : G), τ⁆⁆ * ⁅(y' : G), τ⁆ * ⁅(y : G), τ⁆
    simp only [commutatorElement_def]
    group
  rw [e, secVec_mul, secVec_mul, (secVec_eq_zero_iff ψ ⟨_, D.ZV hz⟩).mpr hz, zero_add,
    add_comm]

theorem NatCommData.secVec_comm_conj {Q V Z R : Subgroup G} {t : G} (D : NatCommData Q V Z R t)
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [(Z.subgroupOf V).Normal]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) {φ : ↥R →* GL ι K}
    (hψ : ∀ (s : ↥R) (v w : ↥V), (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {τ : G} (hτ : ∀ y ∈ Q, ⁅y, τ⁆ ∈ V) (hRτ : ∀ r ∈ R, ⁅r, τ⁆ ∈ Q) (r : ↥R) (y : ↥Q) :
    secVec ψ ⟨⁅(r : G) * y * (r : G)⁻¹, τ⁆, hτ _ (D.R_normQ r r.2 y y.2)⟩ =
      (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨⁅(y : G), τ⁆, hτ _ y.2⟩ := by
  have hv : ⁅(y : G), τ⁆ ∈ V := hτ _ y.2
  have hq : ⁅(r : G)⁻¹, τ⁆ ∈ Q := hRτ _ (R.inv_mem r.2)
  have hz1 : ⁅(y : G), ⁅(r : G)⁻¹, τ⁆⁆ ∈ Z := D.comm_Z y y.2 _ hq
  have hz2 : ⁅⁅(r : G)⁻¹, τ⁆, ⁅(y : G), τ⁆⁆ ∈ Z := D.comm_Z _ hq _ (D.VQ hv)
  obtain ⟨zz, hzz, hmain⟩ : ∃ zz ∈ Z, ⁅(r : G) * y * (r : G)⁻¹, τ⁆ =
      zz * ((r : G) * ⁅(y : G), τ⁆ * (r : G)⁻¹) :=
    ⟨_, Z.mul_mem hz1 hz2, (commutator_conj_expand (r : G) (y : G) τ).trans
      (conj_mul_of_conj_eq (a := ⁅(y : G), τ⁆) (D.R_centZ r r.2 _ (Z.mul_mem hz1 hz2)))⟩
  have hwV : (r : G) * ⁅(y : G), τ⁆ * (r : G)⁻¹ ∈ V := by
    have e : (r : G) * ⁅(y : G), τ⁆ * (r : G)⁻¹ = zz⁻¹ * ⁅(r : G) * y * (r : G)⁻¹, τ⁆ := by
      rw [hmain, inv_mul_cancel_left]
    rw [e]
    exact V.mul_mem (D.ZV (Z.inv_mem hzz)) (hτ _ (D.R_normQ r r.2 y y.2))
  obtain ⟨w, hw⟩ : ∃ w : ↥V, (w : G) = (r : G) * ⁅(y : G), τ⁆ * (r : G)⁻¹ :=
    ⟨⟨_, hwV⟩, rfl⟩
  have h1 : secVec ψ w = (φ r : Matrix ι ι K) *ᵥ secVec ψ ⟨⁅(y : G), τ⁆, hv⟩ :=
    hψ r ⟨⁅(y : G), τ⁆, hv⟩ w hw
  have h2 : secVec ψ ⟨⁅(r : G) * y * (r : G)⁻¹, τ⁆, hτ _ (D.R_normQ r r.2 y y.2)⟩ =
      secVec ψ w := by
    rw [secVec_eq_iff, hw]
    show ⁅(r : G) * y * (r : G)⁻¹, τ⁆ * ((r : G) * ⁅(y : G), τ⁆ * (r : G)⁻¹)⁻¹ ∈ Z
    rw [hmain, mul_inv_cancel_right]
    exact hzz
  exact h2.trans h1

theorem NatCommData.secVec_comm_mul_right {Q V Z R : Subgroup G} {t : G}
    (D : NatCommData Q V Z R t) {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [(Z.subgroupOf V).Normal] (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))
    {τ τ' : G} (hτ : ∀ y ∈ Q, ⁅y, τ⁆ ∈ V) (hτ' : ∀ y ∈ Q, ⁅y, τ'⁆ ∈ V)
    (hττ' : ∀ y ∈ Q, ⁅y, τ * τ'⁆ ∈ V) (hτN : ∀ v ∈ V, ⁅τ, v⁆ ∈ Z) (y : ↥Q) :
    secVec ψ ⟨⁅(y : G), τ * τ'⁆, hττ' _ y.2⟩ =
      secVec ψ ⟨⁅(y : G), τ⁆, hτ _ y.2⟩ + secVec ψ ⟨⁅(y : G), τ'⁆, hτ' _ y.2⟩ := by
  have hv : ⁅(y : G), τ'⁆ ∈ V := hτ' _ y.2
  have hz : ⁅τ, ⁅(y : G), τ'⁆⁆ ∈ Z := hτN _ hv
  have hw : ⁅(y : G), τ⁆ ∈ V := hτ _ y.2
  have e : (⟨⁅(y : G), τ * τ'⁆, hττ' _ y.2⟩ : ↥V) =
      ⟨⁅(y : G), τ⁆, hw⟩ * ⟨⁅τ, ⁅(y : G), τ'⁆⁆, D.ZV hz⟩ * ⟨⁅(y : G), τ'⁆, hv⟩ := by
    apply Subtype.ext
    show ⁅(y : G), τ * τ'⁆ = ⁅(y : G), τ⁆ * ⁅τ, ⁅(y : G), τ'⁆⁆ * ⁅(y : G), τ'⁆
    simp only [commutatorElement_def]
    group
  rw [e, secVec_mul, secVec_mul, (secVec_eq_zero_iff ψ ⟨_, D.ZV hz⟩).mpr hz, add_zero]

end CFSG.RankThree.GF2n.Stroth80

end
