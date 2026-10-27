module

public import CFSG.Quasithin.Background.FFC9C
public import CFSG.Quasithin.Background.FFC7E

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H
open scoped Matrix

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem isFFStarOffender_map_congrHom (e : V ≃* W) {X A : Subgroup (MulAut V)}
    (h : IsFFStarOffender X A) :
    IsFFStarOffender (X.map (congrHom e)) (A.map (congrHom e)) :=
  isFFStarOffender_map_congr_equiv e h

end Transport

namespace SumNat

theorem exists_model_iso {W : Type} [CommGroup W] {K : Subgroup (MulAut W)} {F : Type} [Field F]
    [Finite F] {I : Fin 2 → Subgroup W} {π : ↥(StatedSL 3 F) →* ↥K}
    (hind : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 F)).RealizesVia K (I i) ⊥ π) :
    ∃ Φ : W ≃* PM F, K.map (congrHom Φ) = natImage F := by
  classical
  have hmap : ∀ i, ∃ f : ↥(I i) →* Multiplicative (Fin 3 → F), Function.Surjective f ∧
      (∀ u : ↥(I i), f u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W)) ∧
      ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(I i)) (hu : ((π γ : ↥K) : MulAut W) u ∈ I i),
        f ⟨_, hu⟩ = natAct (StatedSL 3 F) γ (f u) := fun i => exists_natMap (hreal i)
  choose f hfs hfk hfe using hmap
  have hfi : ∀ i, Function.Injective (f i) := fun i => by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk i u).1 hu))
  let e : ∀ i, ↥(I i) ≃* Multiplicative (Fin 3 → F) := fun i =>
    MulEquiv.ofBijective (f i) ⟨hfi i, hfs i⟩
  let u : ∀ _ : Fin 2, (Fin 3 → F) → W := fun i x =>
    (((e i).symm (Multiplicative.ofAdd x) : ↥(I i)) : W)
  have hu_mem : ∀ i x, u i x ∈ I i := fun i x => ((e i).symm (Multiplicative.ofAdd x)).2
  have hu_add : ∀ i x y, u i (x + y) = u i x * u i y := by
    intro i x y
    simp only [u, ofAdd_add, map_mul, Subgroup.coe_mul]
  have hu_zero : ∀ i, u i 0 = 1 := by
    intro i
    simp [u]
  have hu_inj : ∀ i x, u i x = 1 → x = 0 := by
    intro i x hx
    have h1 : (e i).symm (Multiplicative.ofAdd x) = 1 := Subtype.ext hx
    have h2 := congrArg (e i) h1
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    exact h2
  have hu_e : ∀ i (x : ↥(I i)), u i (Multiplicative.toAdd (e i x)) = x := fun i x => by
    simp [u]
  have hu_eq : ∀ i (γ : ↥(StatedSL 3 F)) x, ((π γ : ↥K) : MulAut W) (u i x) =
      u i (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
    intro i γ x
    have hmem : ((π γ : ↥K) : MulAut W) (u i x) ∈ I i :=
      (hreal i).2.2.2.1 (π γ) _ (((e i).symm (Multiplicative.ofAdd x)).2)
    have h1 := hfe i γ ((e i).symm (Multiplicative.ofAdd x)) hmem
    have h2 : f i ((e i).symm (Multiplicative.ofAdd x)) = Multiplicative.ofAdd x :=
      (e i).apply_symm_apply _
    rw [h2] at h1
    have h3 : (e i) ⟨_, hmem⟩ = Multiplicative.ofAdd
        (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := h1
    have h4 : (⟨_, hmem⟩ : ↥(I i)) = (e i).symm (Multiplicative.ofAdd
        (((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) := by
      rw [← h3, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h4
  let Θ : PM F →* W :=
    { toFun := fun v => u 0 (Multiplicative.toAdd v 0) * u 1 (Multiplicative.toAdd v 1)
      map_one' := by simp [hu_zero]
      map_mul' := fun x y => by
        simp only [toAdd_mul, Pi.add_apply, hu_add]
        exact mul_mul_mul_comm _ _ _ _ }
  have hΘ : ∀ v, Θ v = u 0 (Multiplicative.toAdd v 0) * u 1 (Multiplicative.toAdd v 1) :=
    fun v => rfl
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [hΘ] at hv
    have h0 : u 0 (Multiplicative.toAdd v 0) ∈ I 0 ⊓ I 1 := by
      refine ⟨hu_mem 0 _, ?_⟩
      have : u 0 (Multiplicative.toAdd v 0) = (u 1 (Multiplicative.toAdd v 1))⁻¹ :=
        eq_inv_of_mul_eq_one_left hv
      rw [this]
      exact (I 1).inv_mem (hu_mem 1 _)
    rw [hind] at h0
    have h0' : u 0 (Multiplicative.toAdd v 0) = 1 := Subgroup.mem_bot.1 h0
    have h1' : u 1 (Multiplicative.toAdd v 1) = 1 := by
      rw [h0', one_mul] at hv
      exact hv
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hu_inj 0 _ h0'
    · exact hu_inj 1 _ h1'
  have hsurj : Function.Surjective Θ := by
    intro w
    have hw : w ∈ I 0 ⊔ I 1 := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hw
    refine ⟨Multiplicative.ofAdd ![Multiplicative.toAdd (e 0 ⟨y, hy⟩),
      Multiplicative.toAdd (e 1 ⟨z, hz⟩)], ?_⟩
    rw [hΘ]
    have h0 := hu_e 0 ⟨y, hy⟩
    have h1 := hu_e 1 ⟨z, hz⟩
    simp only [toAdd_ofAdd, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h0, h1]
  let Φ : W ≃* PM F := (MulEquiv.ofBijective Θ ⟨hinj, hsurj⟩).symm
  have hΦΘ : ∀ v, Φ (Θ v) = v := fun v =>
    (MulEquiv.ofBijective Θ ⟨hinj, hsurj⟩).symm_apply_apply v
  have hΘeq : ∀ (γ : ↥(StatedSL 3 F)) (v : PM F),
      ((π γ : ↥K) : MulAut W) (Θ v) = Θ (diagAut (γ : GL (Fin 3) F) v) := by
    intro γ v
    rw [hΘ, hΘ, map_mul, hu_eq, hu_eq]
    rfl
  have hcongr : ∀ γ : ↥(StatedSL 3 F),
      congrHom Φ ((π γ : ↥K) : MulAut W) = diagAut (γ : GL (Fin 3) F) := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply]
    show Φ (((π γ : ↥K) : MulAut W) (Θ x)) = _
    rw [hΘeq, hΦΘ]
  have hπsurj : Function.Surjective π := (hreal 0).1
  refine ⟨Φ, ?_⟩
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨γ, hγ⟩ := hπsurj ⟨k, hk⟩
    refine ⟨γ, ?_⟩
    have hk' : ((π γ : ↥K) : MulAut W) = k := congrArg Subtype.val hγ
    show diagAut (γ : GL (Fin 3) F) = congrHom Φ k
    rw [← hk', hcongr]
  · rintro ⟨γ, rfl⟩
    exact ⟨((π γ : ↥K) : MulAut W), (π γ).2, hcongr γ⟩

end SumNat

open SumNat in
theorem b510SumNat_of : B510SumNat := by
  intro W _ _ H K hKH hnorm hnat A hA
  obtain ⟨m, F, hFfield, hFfin, hodd, hcard, I, π, hZ, hind, hsup, hreal⟩ := hnat
  have : CharP F 2 := charP_two_of_card_pow hcard
  have hind2 : I 0 ⊓ I 1 = ⊥ := by
    have h := hind 0
    have h1 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
      refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le 1 (by decide) le_rfl)
      have : j = 1 := by
        fin_cases j
        · exact absurd rfl hj
        · rfl
      rw [this]
    rw [h1, bot_sup_eq] at h
    exact h
  have hsup2 : I 0 ⊔ I 1 = ⊤ := by
    have h1 : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [← h1, ← bot_sup_eq (⨆ i : Fin 2, I i)]
    exact hsup
  obtain ⟨Φ, hKimg⟩ := exists_model_iso hind2 hsup2 hreal
  have hHN : H ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hnorm h hh k hk
    · intro hk
      have h1 := hnorm h⁻¹ (H.inv_mem hh) _ hk
      have e : h⁻¹ * (h * k * h⁻¹) * h⁻¹⁻¹ = k := by group
      rwa [e] at h1
  have hXN : H.map (congrHom Φ) ≤ Subgroup.normalizer (natImage F : Set (MulAut (PM F))) := by
    rw [← hKimg]
    have h1 : (Subgroup.normalizer (K : Set (MulAut W))).map (congrHom Φ) =
        Subgroup.normalizer ((K.map (congrHom Φ) : Subgroup (MulAut (PM F))) :
          Set (MulAut (PM F))) := Subgroup.map_equiv_normalizer_eq K (MulAut.congr Φ)
    rw [← h1]
    exact Subgroup.map_mono hHN
  have hA' := isFFStarOffender_map_congrHom Φ hA
  have hle := core hodd hcard hXN hA'
  rw [← hKimg] at hle
  exact (map_congrHom_le_iff Φ).1 hle

end FFC

end CFSG.Quasithin
