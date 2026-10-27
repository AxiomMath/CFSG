module

public import CFSG.Quasithin.Vol2.KGNatReal
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

section Faithful

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (GL ι K)} {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥Γ →* ↥H} {f : W → (ι → K)}

theorem IsCoord.injective_nat (hf : IsCoord (linModelNat Γ) H Z π f) : Function.Injective π := by
  intro γ γ' h
  have hlin : ∀ x, ((γ : GL ι K) : Matrix ι ι K) *ᵥ x = ((γ' : GL ι K) : Matrix ι ι K) *ᵥ x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    have h1 : f (((π γ : ↥H) : MulAut W) w) = f (((π γ' : ↥H) : MulAut W) w) := by rw [h]
    exact (linModelNat_lin Γ γ (f w)).symm.trans ((hf.act γ w).symm.trans
      (h1.trans ((hf.act γ' w).trans (linModelNat_lin Γ γ' (f w)))))
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hlin x)

end Faithful

section Pullback

variable {G X : Type*} [Group G] [Group X] {H P : Subgroup X}

theorem isPGroup_comap (ρ : G →* ↥H) (hρ : Function.Injective ρ) (hP : IsPGroup 2 P) :
    IsPGroup 2 ((P.subgroupOf H).comap ρ) :=
  (hP.comap_of_injective H.subtype H.subtype_injective).comap_of_injective ρ hρ

theorem index_comap (ρ : G →* ↥H) (hρ : Function.Surjective ρ) :
    ((P.subgroupOf H).comap ρ).index = (P.subgroupOf H).index :=
  Subgroup.index_comap_of_surjective _ hρ

end Pullback

section SL3

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

@[expose] noncomputable def rho3 (π : ↥(StatedSL 3 K) →* ↥H) :
    Matrix.SpecialLinearGroup (Fin 3) K →* ↥H :=
  π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom

omit [Finite K] in
theorem rho3_bijective (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) :
    Function.Bijective (rho3 π) :=
  ⟨hf.injective_nat.comp (specialLinearGroupEquivStatedSL 3 K).injective,
    hf.onto.comp (specialLinearGroupEquivStatedSL 3 K).surjective⟩

omit [Finite K] in
theorem IsCoord.act3 (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (A : Matrix.SpecialLinearGroup (Fin 3) K) (w : W) :
    f (((rho3 π A : ↥H) : MulAut W) w) = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ f w :=
  (hf.act _ w).trans (linModelNat_lin _ _ _)

theorem exists_sylow_eq_conj_Usl {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) {P : Subgroup (MulAut W)}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPH, hP2, hPi⟩ := hP
  obtain ⟨hinj, hsurj⟩ := rho3_bijective hf
  have hQ2 := isPGroup_comap (rho3 π) hinj hP2
  have hQi : ¬ 2 ∣ ((P.subgroupOf H).comap (rho3 π)).index := by
    rw [index_comap (rho3 π) hsurj]
    exact hPi
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow
    (IsPGroup.toSylow (isPGroup_Usl hK) (not_dvd_index_Usl hK hn)) (hQ2.toSylow hQi)
  refine ⟨g, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := hsurj ⟨x, hPH hx⟩
    have hAQ : A ∈ (P.subgroupOf H).comap (rho3 π) := by
      rw [Subgroup.mem_comap, hA, Subgroup.mem_subgroupOf]
      exact hx
    rw [← IsPGroup.toSylow_coe hQ2 hQi, ← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hAQ
    refine ⟨g⁻¹ * A * g, hAQ, ?_⟩
    rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]
  · rintro ⟨u, hu, rfl⟩
    have hmem : g * u * g⁻¹ ∈ (P.subgroupOf H).comap (rho3 π) := by
      rw [← IsPGroup.toSylow_coe hQ2 hQi, ← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hmem
    exact hmem

end SL3

end CFSG.Quasithin.Vol2.KGNat
