module

public import CFSG.LocalAnalysis.StandardType.GGPresentation

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

variable {U : Type*} [Group U] {D : UniversalRootDatum U}
  {X : Type*} [Group X] {ι : Type*} {S : ι → Set (Fin D.rank → ℤ)}
  {φ : ∀ k, ggSub D (S k) →* X} {ν : GGWeyl D →* U} {R : Subgroup X} {δ : R →* GGWeyl D}

theorem ggExt_one {H : Subgroup U} (ψ : H →* X) : ggExt ψ 1 = 1 := by
  rw [ggExt_of_mem ψ (one_mem H)]
  exact map_one ψ

theorem ggExt_inv {H : Subgroup U} (ψ : H →* X) {u : U} (hu : u ∈ H) :
    ggExt ψ u⁻¹ = (ggExt ψ u)⁻¹ := by
  rw [ggExt_of_mem ψ hu, ggExt_of_mem ψ (inv_mem hu), ← map_inv]
  rfl

variable (D S φ ν δ) in
@[expose] def GGGood (k l : ι) (α : Fin D.rank → ℤ) (c : R) : Prop :=
  ∀ z ∈ D.rootGroup α,
    (c : X) * ggExt (φ k) z * (c : X)⁻¹ = ggExt (φ l) (ν (δ c) * z * (ν (δ c))⁻¹)

theorem ggGood_one_of_agree {k l : ι} {α : Fin D.rank → ℤ}
    (h : ∀ z ∈ D.rootGroup α, ggExt (φ k) z = ggExt (φ l) z) : GGGood D S φ ν δ k l α 1 := by
  intro z hz
  simp only [map_one, OneMemClass.coe_one, one_mul, inv_one, mul_one]
  exact h z hz

theorem ggGood_weyl {k : ι} {α : Fin D.rank → ℤ} (hα : α ∈ S k) {v : GGWeyl D}
    (hv : ν v ∈ ggSub D (S k)) {c : R} (hc : (c : X) = ggExt (φ k) (ν v)) (hcδ : δ c = v) :
    GGGood D S φ ν δ k k α c := by
  intro z hz
  have hz' : z ∈ ggSub D (S k) := rootGroup_le_ggSub hα hz
  rw [hcδ, hc, ggExt_mul (φ k) (mul_mem hv hz') (inv_mem hv), ggExt_mul (φ k) hv hz',
    ggExt_inv (φ k) hv]

theorem ggGood_of_centralize {k : ι} {α : Fin D.rank → ℤ} {r : R}
    (hr : ∀ z ∈ D.rootGroup α, (r : X) * ggExt (φ k) z * (r : X)⁻¹ = ggExt (φ k) z)
    (hν : ∀ z ∈ D.rootGroup α, ν (δ r) * z * (ν (δ r))⁻¹ = z) : GGGood D S φ ν δ k k α r := by
  intro z hz
  rw [hr z hz, hν z hz]

theorem ggGood_comp (hν : GGWeylLift D ν) {k l m : ι} {α : Fin D.rank → ℤ} (hα : α ∈ D.roots)
    {c c' : R} (h1 : GGGood D S φ ν δ k l α c)
    (h2 : GGGood D S φ ν δ l m (weylAction D.isFiniteType (δ c) α) c') :
    GGGood D S φ ν δ k m α (c' * c) := by
  intro z hz
  have hz' := hν.conj_mem (δ c) α hα z hz
  have e := h2 _ hz'
  rw [← h1 z hz] at e
  have hconj : ν (δ c') * (ν (δ c) * z * (ν (δ c))⁻¹) * (ν (δ c'))⁻¹ =
      ν (δ (c' * c)) * z * (ν (δ (c' * c)))⁻¹ := by
    simp only [map_mul, mul_inv_rev]
    group
  rw [hconj] at e
  rw [← e]
  simp only [Subgroup.coe_mul, mul_inv_rev]
  group

theorem ggActsLike_of_good (hν : GGWeylLift D ν) (hS : ∀ k, S k ⊆ D.roots)
    (hone : ∀ (r : R) (k l : ι), ∀ α ∈ S k, weylAction D.isFiniteType (δ r) α ∈ S l →
      ∃ c : R, weylAction D.isFiniteType (δ c) α = weylAction D.isFiniteType (δ r) α ∧
        GGGood D S φ ν δ k l α c)
    (hstab : ∀ (r : R) (k : ι), ∀ α ∈ S k, weylAction D.isFiniteType (δ r) α = α →
      GGGood D S φ ν δ k k α r) :
    GGActsLike D S φ ν R δ := by
  intro r k l α hα hαl z hz
  obtain ⟨c, hcα, hgood⟩ := hone r k l α hα hαl
  have hfix : weylAction D.isFiniteType (δ (c⁻¹ * r)) α = α := by
    rw [map_mul, map_inv, weylAction_mul_apply, ← hcα, weylAction_inv_apply_apply]
  have h1 := hstab (c⁻¹ * r) k α hα hfix
  have h2 : GGGood D S φ ν δ k l (weylAction D.isFiniteType (δ (c⁻¹ * r)) α) c := by
    rw [hfix]
    exact hgood
  have h3 := ggGood_comp hν (hS k hα) h1 h2
  rw [mul_inv_cancel_left] at h3
  exact h3 z hz

theorem ggActsLike_of_transitive (hν : GGWeylLift D ν) (hS : ∀ k, S k ⊆ D.roots)
    (hagree : ∀ k l, ∀ α ∈ S k, α ∈ S l → ∀ z ∈ D.rootGroup α, ggExt (φ k) z = ggExt (φ l) z)
    (htrans : ∀ (r : R) (k l : ι), ∀ α ∈ S k, weylAction D.isFiniteType (δ r) α ∈ S l →
      ∃ (α' : Fin D.rank → ℤ) (v₁ v₂ : GGWeyl D) (c₁ c₂ : R), α' ∈ S k ∧ α' ∈ S l ∧
        weylAction D.isFiniteType v₁ α = α' ∧
        weylAction D.isFiniteType v₂ α' = weylAction D.isFiniteType (δ r) α ∧
        ν v₁ ∈ ggSub D (S k) ∧ (c₁ : X) = ggExt (φ k) (ν v₁) ∧ δ c₁ = v₁ ∧
        ν v₂ ∈ ggSub D (S l) ∧ (c₂ : X) = ggExt (φ l) (ν v₂) ∧ δ c₂ = v₂)
    (hcent : ∀ (r : R) (k : ι), ∀ α ∈ S k, weylAction D.isFiniteType (δ r) α = α →
      ∀ z ∈ D.rootGroup α, (r : X) * ggExt (φ k) z * (r : X)⁻¹ = ggExt (φ k) z)
    (hνfix : ∀ (w : GGWeyl D), ∀ α ∈ D.roots, weylAction D.isFiniteType w α = α →
      ∀ z ∈ D.rootGroup α, ν w * z * (ν w)⁻¹ = z) :
    GGActsLike D S φ ν R δ := by
  refine ggActsLike_of_good hν hS (fun r k l α hα hαl => ?_)
    (fun r k α hα hfix => ggGood_of_centralize (hcent r k α hα hfix)
      (hνfix (δ r) α (hS k hα) hfix))
  obtain ⟨α', v₁, v₂, c₁, c₂, hα'k, hα'l, h₁, h₂, hv₁, hc₁, hcδ₁, hv₂, hc₂, hcδ₂⟩ :=
    htrans r k l α hα hαl
  have g1 : GGGood D S φ ν δ k k α c₁ := ggGood_weyl hα hv₁ hc₁ hcδ₁
  have g2 : GGGood D S φ ν δ k l α' 1 := ggGood_one_of_agree (hagree k l α' hα'k hα'l)
  have g3 : GGGood D S φ ν δ l l α' c₂ := ggGood_weyl hα'l hv₂ hc₂ hcδ₂
  have hα'root : α' ∈ D.roots := hS k hα'k
  have g12 : GGGood D S φ ν δ k l α (1 * c₁) := by
    refine ggGood_comp hν (hS k hα) g1 ?_
    rw [hcδ₁, h₁]
    exact g2
  have g123 : GGGood D S φ ν δ k l α (c₂ * (1 * c₁)) := by
    refine ggGood_comp hν (hS k hα) g12 ?_
    rw [one_mul, hcδ₁, h₁]
    exact g3
  refine ⟨c₂ * (1 * c₁), ?_, g123⟩
  rw [one_mul, map_mul, hcδ₁, hcδ₂, weylAction_mul_apply, h₁, h₂]

variable (D) in
@[expose] def ggSuppLattice (J : Finset (Fin D.rank)) : AddSubgroup (Fin D.rank → ℤ) where
  carrier := {v | ∀ i ∉ J, v i = 0}
  add_mem' {a b} ha hb i hi := by
    simp only [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' i _ := rfl
  neg_mem' {a} ha i hi := by
    simp only [Pi.neg_apply, ha i hi, neg_zero]

theorem mem_ggSupp_iff {J : Finset (Fin D.rank)} {γ : Fin D.rank → ℤ} :
    γ ∈ ggSupp D J ↔ γ ∈ D.roots ∧ γ ∈ ggSuppLattice D J :=
  Iff.rfl

theorem eq_sum_single_of_supp {J : Finset (Fin D.rank)} {γ : Fin D.rank → ℤ}
    (hγ : ∀ i ∉ J, γ i = 0) : γ = ∑ j ∈ J, γ j • (Pi.single j 1 : Fin D.rank → ℤ) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq]
  by_cases hi : i ∈ J
  · simp [hi]
  · simp [hi, hγ i hi]

theorem ggOrbit_of_pairs (M : ι → AddSubgroup (Fin D.rank → ℤ))
    (hM : ∀ k, ∀ γ ∈ D.roots, γ ∈ M k → γ ∈ S k)
    (hpair : ∀ J : Finset (Fin D.rank), J.card ≤ 2 → ∃ (w : GGWeyl D) (k : ι), ∀ j ∈ J,
      weylAction D.isFiniteType w (Pi.single j 1) ∈ M k) :
    GGOrbit D S := by
  intro J hJ
  obtain ⟨w, k, hw⟩ := hpair J hJ
  refine ⟨w, k, fun γ hγ => hM k _ ((ggIsCTRootSystem D).smul_mem w γ hγ.1) ?_⟩
  rw [eq_sum_single_of_supp hγ.2, map_sum]
  exact AddSubgroup.sum_mem _ fun j hj => by
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (hw j hj) _

theorem ggWeylLift_mem_of_closure {T : Set (GGWeyl D)} {S' : Set (Fin D.rank → ℤ)}
    (hT : ∀ t ∈ T, ν t ∈ ggSub D S') {v : GGWeyl D} (hv : v ∈ Subgroup.closure T) :
    ν v ∈ ggSub D S' :=
  (Subgroup.closure_le ((ggSub D S').comap ν)).mpr hT hv

theorem exists_mem_R_of_closure {k : ι} {T : Set (GGWeyl D)}
    (hWk : ∀ v ∈ Subgroup.closure T, ν v ∈ ggSub D (S k))
    (hgen : ∀ t ∈ T, ∃ c : R, (c : X) = ggExt (φ k) (ν t) ∧ δ c = t) :
    ∀ v ∈ Subgroup.closure T, ∃ c : R, (c : X) = ggExt (φ k) (ν v) ∧ δ c = v := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem t ht => exact hgen t ht
  | one => exact ⟨1, by rw [map_one, ggExt_one]; rfl, map_one δ⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨c₁, h₁, hδ₁⟩ := iha
    obtain ⟨c₂, h₂, hδ₂⟩ := ihb
    refine ⟨c₁ * c₂, ?_, by rw [map_mul, hδ₁, hδ₂]⟩
    rw [Subgroup.coe_mul, h₁, h₂, map_mul, ggExt_mul (φ k) (hWk a ha) (hWk b hb)]
  | inv a ha iha =>
    obtain ⟨c, h, hδc⟩ := iha
    refine ⟨c⁻¹, ?_, by rw [map_inv, hδc]⟩
    rw [Subgroup.coe_inv, h, map_inv, ggExt_inv (φ k) (hWk a ha)]

theorem ggWeylInR_of_subgroup (Wk : ι → Subgroup (GGWeyl D))
    (hWk : ∀ k, ∀ v ∈ Wk k, ν v ∈ ggSub D (S k)) (T : ι → Set (GGWeyl D))
    (hT : ∀ k, Subgroup.closure (T k) = Wk k)
    (hgen : ∀ k, ∀ t ∈ T k, ∃ c : R, (c : X) = ggExt (φ k) (ν t) ∧ δ c = t)
    (hrefl : ∀ (k : ι) (w : GGWeyl D) (j : Fin D.rank),
      weylAction D.isFiniteType w (Pi.single j 1) ∈ S k →
        w * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j * w⁻¹ ∈ Wk k) :
    GGWeylInR D S φ ν R δ := by
  intro k w j hj
  have h := exists_mem_R_of_closure (k := k) (T := T k) (fun v hv => hWk k v (hT k ▸ hv))
    (hgen k)
  exact h _ ((hT k).symm ▸ hrefl k w j hj)

end CFSG.StandardType
