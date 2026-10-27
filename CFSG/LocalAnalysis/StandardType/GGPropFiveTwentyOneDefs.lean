module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGPresentationReduce
public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

section Special

variable {G : Type*} [Group G] {ι : Type*} (M : CoxeterMatrix ι) (Bs : Subgroup G)

@[expose] def GGSpecialInvolutions (A : Subgroup (MulAut ↥Bs)) (f : M.Group ≃* ↥A) (t : ι → G) :
    Prop :=
  M.IsLiftable t ∧ ∀ i, t i ∈ Subgroup.normalizer (Bs : Set G) ∧
    ∀ b : ↥Bs, (((f (M.simple i) : ↥A) : MulAut ↥Bs) b : G) = t i * b * (t i)⁻¹

variable {M Bs} {A : Subgroup (MulAut ↥Bs)} {f : M.Group ≃* ↥A} {t : ι → G}

@[expose] noncomputable def ggSpecialLift (h : GGSpecialInvolutions M Bs A f t) : M.Group →* G :=
  M.toCoxeterSystem.lift ⟨t, h.1⟩

theorem ggSpecialLift_simple (h : GGSpecialInvolutions M Bs A f t) (i : ι) :
    ggSpecialLift h (M.simple i) = t i :=
  M.toCoxeterSystem.lift_apply_simple h.1 i

theorem ggSpecialLift_spec (h : GGSpecialInvolutions M Bs A f t) (w : M.Group) :
    ggSpecialLift h w ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, (((f w : ↥A) : MulAut ↥Bs) b : G) =
        ggSpecialLift h w * b * (ggSpecialLift h w)⁻¹ := by
  induction w using M.toCoxeterSystem.simple_induction_left with
  | one =>
    refine ⟨by rw [map_one]; exact one_mem _, fun b => ?_⟩
    simp only [map_one, OneMemClass.coe_one, MulAut.one_apply, one_mul, inv_one, mul_one]
  | mul_simple_left w i ih =>
    obtain ⟨hN, hact⟩ := ih
    obtain ⟨hNi, hacti⟩ := h.2 i
    have hs : M.toCoxeterSystem.simple i = M.simple i := rfl
    rw [hs] at *
    refine ⟨by rw [map_mul, ggSpecialLift_simple]; exact mul_mem hNi hN, fun b => ?_⟩
    have hf : ((f (M.simple i * w) : ↥A) : MulAut ↥Bs) =
        ((f (M.simple i) : ↥A) : MulAut ↥Bs) * ((f w : ↥A) : MulAut ↥Bs) := by
      rw [map_mul]
      rfl
    rw [hf, MulAut.mul_apply, hacti, hact, map_mul, ggSpecialLift_simple]
    group

theorem ggSpecialLift_injective (h : GGSpecialInvolutions M Bs A f t) :
    Function.Injective (ggSpecialLift h) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  apply f.injective
  rw [map_one]
  apply Subtype.ext
  refine MulEquiv.ext fun b => Subtype.ext ?_
  have key := (ggSpecialLift_spec h w).2 b
  rw [hw, one_mul, inv_one, mul_one] at key
  rw [key]
  rfl

theorem ggSpecialLift_range_le (h : GGSpecialInvolutions M Bs A f t) {H : Subgroup G}
    (hH : ∀ i, t i ∈ H) : (ggSpecialLift h).range ≤ H := by
  rintro _ ⟨w, rfl⟩
  induction w using M.toCoxeterSystem.simple_induction_left with
  | one => rw [map_one]; exact one_mem H
  | mul_simple_left w i ih =>
    rw [map_mul]
    exact mul_mem (by rw [show M.toCoxeterSystem.simple i = M.simple i from rfl,
      ggSpecialLift_simple]; exact hH i) ih

theorem ggSpecialLift_range_le_normalizer (h : GGSpecialInvolutions M Bs A f t) :
    (ggSpecialLift h).range ≤ Subgroup.normalizer (Bs : Set G) := by
  rintro _ ⟨w, rfl⟩
  exact (ggSpecialLift_spec h w).1

end Special

theorem forall_range_ofInjective {W X : Type*} [Group W] [Group X] {ρ : W →* X}
    (hρ : Function.Injective ρ) {P : X → W → Prop} (h : ∀ w, P (ρ w) w) (r : ρ.range) :
    P r ((MonoidHom.ofInjective hρ).symm r) := by
  have e : (r : X) = ρ ((MonoidHom.ofInjective hρ).symm r) := by
    rw [← MonoidHom.ofInjective_apply hρ, MulEquiv.apply_symm_apply]
  rw [e]
  exact h _

section Closure

variable {X : Type*} [Group X] {U : Type*} [Group U] {Δ : UniversalRootDatum U} {ι : Type*}
  {S : ι → Set (Fin Δ.rank → ℤ)} {φ : ∀ k, ggSub Δ (S k) →* X} {R : Subgroup X}

theorem range_le_ggClosure (k : ι) : (φ k).range ≤ ggClosure Δ S φ R := by
  intro g hg
  refine Subgroup.mem_iSup_of_mem (1 : R) (Subgroup.mem_iSup_of_mem k ⟨g, hg, ?_⟩)
  simp

theorem ggClosure_le {H : Subgroup X} (hφ : ∀ k, (φ k).range ≤ H) (hR : R ≤ H) :
    ggClosure Δ S φ R ≤ H := by
  refine iSup_le fun r => iSup_le fun k => ?_
  rintro _ ⟨g, hg, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact mul_mem (mul_mem (hR r.2) (hφ k hg)) (inv_mem (hR r.2))

variable {G : Type} [Group G] [Finite G]

theorem ggG0_le_of {p : ℕ} {B : Subgroup G} {x : G} {L D J I : Subgroup G} (hL : L ≤ I)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → K ≤ I) : ggG0 p B x L D J ≤ I :=
  sup_le hL (iSup_le fun y => iSup_le fun K => iSup_le fun h => hK y K h)

theorem ggClosure_eq_ggG0 {φ : ∀ k, ggSub Δ (S k) →* G} {R : Subgroup G} {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G} (hφ : ∀ k, (φ k).range ≤ ggG0 p B x L D J)
    (hR : R ≤ ggG0 p B x L D J) (hL : L ≤ ggClosure Δ S φ R)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → K ≤ ggClosure Δ S φ R) :
    ggClosure Δ S φ R = ggG0 p B x L D J :=
  le_antisymm (ggClosure_le hφ hR) (ggG0_le_of hL hK)

end Closure

section Injective

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U) {X : Type*} [Group X] {ι : Type*}
  (S : ι → Set (Fin Δ.rank → ℤ)) (φ : ∀ k, ggSub Δ (S k) →* X) (ν : GGWeyl Δ →* U)
  (ρ : GGWeyl Δ →* X)

@[expose] def GGActsLikeHom : Prop :=
  ∀ (v : GGWeyl Δ) (k l : ι), ∀ α ∈ S k, weylAction Δ.isFiniteType v α ∈ S l →
    ∀ z ∈ Δ.rootGroup α, ρ v * ggExt (φ k) z * (ρ v)⁻¹ = ggExt (φ l) (ν v * z * (ν v)⁻¹)

@[expose] def GGWeylInRHom : Prop :=
  ∀ (k : ι) (v : GGWeyl Δ) (j : Fin Δ.rank), weylAction Δ.isFiniteType v (Pi.single j 1) ∈ S k →
    ggExt (φ k) (ν (v * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple j * v⁻¹)) =
      ρ (v * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple j * v⁻¹)

variable {Δ S φ ν ρ}

theorem coe_ofInjective_symm (hρ : Function.Injective ρ) (r : ρ.range) :
    (r : X) = ρ ((MonoidHom.ofInjective hρ).symm r) := by
  rw [← MonoidHom.ofInjective_apply hρ, MulEquiv.apply_symm_apply]

theorem ggActsLike_ofInjective (hρ : Function.Injective ρ) (hC : GGActsLikeHom Δ S φ ν ρ) :
    GGActsLike Δ S φ ν ρ.range (MonoidHom.ofInjective hρ).symm.toMonoidHom := by
  intro r k l α hα hαl z hz
  rw [coe_ofInjective_symm hρ r]
  exact hC _ k l α hα hαl z hz

theorem ggActsLikeHom_of_actsLike (hρ : Function.Injective ρ)
    (hC : GGActsLike Δ S φ ν ρ.range (MonoidHom.ofInjective hρ).symm.toMonoidHom) :
    GGActsLikeHom Δ S φ ν ρ := by
  intro v k l α hα hαl z hz
  have h1 : (MonoidHom.ofInjective hρ).symm.toMonoidHom (MonoidHom.ofInjective hρ v) = v :=
    (MonoidHom.ofInjective hρ).symm_apply_apply v
  have h2 : ((MonoidHom.ofInjective hρ v : ρ.range) : X) = ρ v := MonoidHom.ofInjective_apply hρ
  have h := hC (MonoidHom.ofInjective hρ v) k l α hα (by rw [h1]; exact hαl) z hz
  rw [h1, h2] at h
  exact h

theorem ggWeylInR_ofInjective (hρ : Function.Injective ρ) (hW : GGWeylInRHom Δ S φ ν ρ) :
    GGWeylInR Δ S φ ν ρ.range (MonoidHom.ofInjective hρ).symm.toMonoidHom := by
  intro k v j hj
  refine ⟨MonoidHom.ofInjective hρ
    (v * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple j * v⁻¹), ?_, ?_⟩
  · rw [MonoidHom.ofInjective_apply hρ, hW k v j hj]
  · exact (MonoidHom.ofInjective hρ).symm_apply_apply _

theorem ggExt_comp_eq_of_closure {k : ι} {T : Set (GGWeyl Δ)}
    (hWk : ∀ v ∈ Subgroup.closure T, ν v ∈ ggSub Δ (S k))
    (hgen : ∀ t ∈ T, ggExt (φ k) (ν t) = ρ t) :
    ∀ v ∈ Subgroup.closure T, ggExt (φ k) (ν v) = ρ v := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem t ht => exact hgen t ht
  | one => rw [map_one, map_one, ggExt_one]
  | mul a b ha hb iha ihb =>
    rw [map_mul, map_mul, ggExt_mul (φ k) (hWk a ha) (hWk b hb), iha, ihb]
  | inv a ha iha => rw [map_inv, map_inv, ggExt_inv (φ k) (hWk a ha), iha]

theorem ggWeylInRHom_of_local (Wk : ι → Subgroup (GGWeyl Δ))
    (hρk : ∀ k, ∀ v ∈ Wk k, ggExt (φ k) (ν v) = ρ v)
    (hrefl : ∀ (k : ι) (w : GGWeyl Δ) (j : Fin Δ.rank),
      weylAction Δ.isFiniteType w (Pi.single j 1) ∈ S k →
        w * (coxeterMatrix Δ.isFiniteType).toCoxeterSystem.simple j * w⁻¹ ∈ Wk k) :
    GGWeylInRHom Δ S φ ν ρ :=
  fun k v j hj => hρk k _ (hrefl k v j hj)

theorem ggActsLikeHom_of_local (hν : GGStandardCopy Δ ν) (hρ : Function.Injective ρ)
    (hS : ∀ k, S k ⊆ Δ.roots)
    (hagree : ∀ k l, ∀ α ∈ S k, α ∈ S l → ∀ z ∈ Δ.rootGroup α, ggExt (φ k) z = ggExt (φ l) z)
    (Wk : ι → Subgroup (GGWeyl Δ)) (hWk : ∀ k, ∀ v ∈ Wk k, ν v ∈ ggSub Δ (S k))
    (hρk : ∀ k, ∀ v ∈ Wk k, ggExt (φ k) (ν v) = ρ v)
    (htrans : ∀ (w : GGWeyl Δ) (k l : ι), ∀ α ∈ S k, weylAction Δ.isFiniteType w α ∈ S l →
      ∃ α' ∈ S k, α' ∈ S l ∧ ∃ v₁ ∈ Wk k, ∃ v₂ ∈ Wk l, weylAction Δ.isFiniteType v₁ α = α' ∧
        weylAction Δ.isFiniteType v₂ α' = weylAction Δ.isFiniteType w α)
    (hcent : ∀ (w : GGWeyl Δ) (k : ι), ∀ α ∈ S k, weylAction Δ.isFiniteType w α = α →
      ∀ z ∈ Δ.rootGroup α, ρ w * ggExt (φ k) z * (ρ w)⁻¹ = ggExt (φ k) z) :
    GGActsLikeHom Δ S φ ν ρ := by
  refine ggActsLikeHom_of_actsLike hρ (ggActsLike_of_transitive hν.1 hS hagree ?_ ?_ hν.2)
  · intro r k l α hα hαl
    obtain ⟨α', hα'k, hα'l, v₁, hv₁, v₂, hv₂, h₁, h₂⟩ := htrans _ k l α hα hαl
    refine ⟨α', v₁, v₂, MonoidHom.ofInjective hρ v₁, MonoidHom.ofInjective hρ v₂, hα'k, hα'l, h₁,
      h₂, hWk k v₁ hv₁, ?_, (MonoidHom.ofInjective hρ).symm_apply_apply v₁, hWk l v₂ hv₂, ?_,
      (MonoidHom.ofInjective hρ).symm_apply_apply v₂⟩
    · rw [MonoidHom.ofInjective_apply hρ, hρk k v₁ hv₁]
    · rw [MonoidHom.ofInjective_apply hρ, hρk l v₂ hv₂]
  · intro r k α hα hfix z hz
    rw [coe_ofInjective_symm hρ r]
    exact hcent _ k α hα hfix z hz

end Injective

section Data

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFivePres (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) : Prop :=
  (StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧ 2 ≤ (ggU t n f).D.rank) ∧
  ∃ (ν : GGWeyl (ggU t n f).D →* (ggU t n f).K) (ι : Type)
    (S : ι → Set (Fin (ggU t n f).D.rank → ℤ)) (φ : ∀ k, ggSub (ggU t n f).D (S k) →* G)
    (ρ : GGWeyl (ggU t n f).D →* G),
    GGWeylLift (ggU t n f).D ν ∧ (∀ k, S k ⊆ (ggU t n f).D.roots) ∧ Function.Injective ρ ∧
    GGActsLikeHom (ggU t n f).D S φ ν ρ ∧ GGWeylInRHom (ggU t n f).D S φ ν ρ ∧
    GGOrbit (ggU t n f).D S ∧
    (∃ k, ∃ γ ∈ S k, ∃ z ∈ (ggU t n f).D.rootGroup γ, ggExt (φ k) z ≠ 1) ∧
    (∀ k, (φ k).range ≤ ggG0 p B x L D J) ∧ ρ.range ≤ ggG0 p B x L D J ∧
    L ≤ ggClosure (ggU t n f).D S φ ρ.range ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → K ≤ ggClosure (ggU t n f).D S φ ρ.range

@[expose] def GGSecFiveLocal (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) : Prop :=
  (StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧ 2 ≤ (ggU t n f).D.rank) ∧
  ∃ (ν : GGWeyl (ggU t n f).D →* (ggU t n f).K) (ι : Type)
    (S : ι → Set (Fin (ggU t n f).D.rank → ℤ)) (φ : ∀ k, ggSub (ggU t n f).D (S k) →* G)
    (ρ : GGWeyl (ggU t n f).D →* G) (Wk : ι → Subgroup (GGWeyl (ggU t n f).D)),
    GGStandardCopy (ggU t n f).D ν ∧ (∀ k, S k ⊆ (ggU t n f).D.roots) ∧ Function.Injective ρ ∧
    (∀ k l, ∀ α ∈ S k, α ∈ S l → ∀ z ∈ (ggU t n f).D.rootGroup α,
      ggExt (φ k) z = ggExt (φ l) z) ∧
    (∀ k, ∀ v ∈ Wk k, ν v ∈ ggSub (ggU t n f).D (S k)) ∧
    (∀ k, ∀ v ∈ Wk k, ggExt (φ k) (ν v) = ρ v) ∧
    (∀ (k : ι) (w : GGWeyl (ggU t n f).D) (j : Fin (ggU t n f).D.rank),
      weylAction (ggU t n f).D.isFiniteType w (Pi.single j 1) ∈ S k →
        w * (coxeterMatrix (ggU t n f).D.isFiniteType).toCoxeterSystem.simple j * w⁻¹ ∈ Wk k) ∧
    (∀ (w : GGWeyl (ggU t n f).D) (k l : ι), ∀ α ∈ S k,
      weylAction (ggU t n f).D.isFiniteType w α ∈ S l →
        ∃ α' ∈ S k, α' ∈ S l ∧ ∃ v₁ ∈ Wk k, ∃ v₂ ∈ Wk l,
          weylAction (ggU t n f).D.isFiniteType v₁ α = α' ∧
          weylAction (ggU t n f).D.isFiniteType v₂ α' =
            weylAction (ggU t n f).D.isFiniteType w α) ∧
    (∀ (w : GGWeyl (ggU t n f).D) (k : ι), ∀ α ∈ S k,
      weylAction (ggU t n f).D.isFiniteType w α = α → ∀ z ∈ (ggU t n f).D.rootGroup α,
        ρ w * ggExt (φ k) z * (ρ w)⁻¹ = ggExt (φ k) z) ∧
    GGOrbit (ggU t n f).D S ∧
    (∃ k, ∃ γ ∈ S k, ∃ z ∈ (ggU t n f).D.rootGroup γ, ggExt (φ k) z ≠ 1) ∧
    (∀ k, (φ k).range ≤ ggG0 p B x L D J) ∧ ρ.range ≤ ggG0 p B x L D J ∧
    L ≤ ggClosure (ggU t n f).D S φ ρ.range ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → K ≤ ggClosure (ggU t n f).D S φ ρ.range

theorem ggSecFivePres_of_local {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} (h : GGSecFiveLocal p B x L D J t n f) :
    GGSecFivePres p B x L D J t n f := by
  obtain ⟨hty, ν, ι, S, φ, ρ, Wk, hν, hS, hρ, hagree, hWk, hρk, hrefl, htrans, hcent, horb, hnt,
    hφG, hρG, hL, hK⟩ := h
  exact ⟨hty, ν, ι, S, φ, ρ, hν.1, hS, hρ,
    ggActsLikeHom_of_local hν hρ hS hagree Wk hWk hρk htrans hcent,
    ggWeylInRHom_of_local Wk hρk hrefl, horb, hnt, hφG, hρG, hL, hK⟩

end Data

section Presentation

variable {G : Type} [Group G] [Finite G]

theorem ggPresentsG0_of_secFivePres {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} (h : GGSecFivePres p B x L D J t n f) :
    ∃ ψ : (ggU t n f).K →* G, GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ := by
  obtain ⟨⟨hadm, hrank, hrk⟩, ν, ι, S, φ, ρ, hν, hS, hρ, hC, hW, horb, hnt, hφG, hρG, hL, hK⟩ :=
    h
  obtain ⟨ψ, hψ, -⟩ := ggPresentsG0_of_presentation t n f hadm hrank hrk hν hS φ
    (MonoidHom.ofInjective hρ).symm.surjective (ggActsLike_ofInjective hρ hC)
    (ggWeylInR_ofInjective hρ hW) horb hnt (ggClosure_eq_ggG0 hφG hρG hL hK)
  exact ⟨ψ, hψ⟩

end Presentation

end CFSG.StandardType
