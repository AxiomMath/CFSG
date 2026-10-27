module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalarsPlusTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.RankThree.GF2n.Stroth80
open scoped Matrix

theorem s16e_omc_centralizer_hom_units {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] {H : Subgroup (MulAut W)}
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥H}
    (hscal : AddCommutantScalar Γ) (hπ : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    ∃ f : ↥(Subgroup.centralizer (H : Set (MulAut W))) →* Kˣ, Function.Injective f := by
  classical
  have R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β₀, hβs₀, hβk₀, hβe₀⟩ := R.exists_β
  let β : W →* Multiplicative (ι → K) := β₀.comp (Subgroup.topEquiv.symm.toMonoidHom)
  have hβs : Function.Surjective β := hβs₀.comp Subgroup.topEquiv.symm.surjective
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : ((⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) :=
      (hβk₀ ⟨w, Subgroup.mem_top w⟩).1 hw
    exact Subgroup.mem_bot.1 h1
  have hβe : ∀ (γ : ↥Γ) (w : W),
      β (((π γ : ↥H) : MulAut W) w) = natAct Γ γ (β w) :=
    fun γ w => hβe₀ γ ⟨w, Subgroup.mem_top w⟩ (Subgroup.mem_top _)
  let eβ : W ≃* Multiplicative (ι → K) := MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  have heβ : ∀ w, eβ w = β w := fun _ => rfl
  let g : MulAut W → ((ι → K) →+ (ι → K)) := fun c =>
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (eβ (c (eβ.symm (Multiplicative.ofAdd v)))))
      (fun a b => by simp [ofAdd_add, map_mul])
  have hg : ∀ (c : MulAut W) (v : ι → K),
      g c v = Multiplicative.toAdd (eβ (c (eβ.symm (Multiplicative.ofAdd v)))) := fun _ _ => rfl
  have hg_mul : ∀ (c c' : MulAut W) (v : ι → K), g (c * c') v = g c (g c' v) := by
    intro c c' v
    rw [hg, hg, hg]
    simp
  have hg_one : ∀ v, g 1 v = v := by
    intro v
    rw [hg]
    simp
  have hg_comm : ∀ c ∈ Subgroup.centralizer (H : Set (MulAut W)), ∀ A ∈ Γ, ∀ v : ι → K,
      g c ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ g c v := by
    intro c hc A hA v
    let γ : ↥Γ := ⟨A, hA⟩
    have hcπ : ∀ w : W, c (((π γ : ↥H) : MulAut W) w) = ((π γ : ↥H) : MulAut W) (c w) := by
      intro w
      have := Subgroup.mem_centralizer_iff.1 hc (π γ : MulAut W) (π γ).2
      exact (congrArg (fun m : MulAut W => m w) this).symm
    set w := eβ.symm (Multiplicative.ofAdd v) with hw
    have h1 : eβ (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd ((A : Matrix ι ι K) *ᵥ v) := by
      rw [heβ, hβe, ← heβ, hw, MulEquiv.apply_symm_apply]
      rfl
    have h2 : eβ.symm (Multiplicative.ofAdd ((A : Matrix ι ι K) *ᵥ v)) =
        ((π γ : ↥H) : MulAut W) w := by
      rw [← h1]; simp
    rw [hg, h2, hcπ, heβ, hβe, ← heβ]
    rfl
  have hex : ∀ c : ↥(Subgroup.centralizer (H : Set (MulAut W))), ∃ a : K, ∀ v, g c v = a • v :=
    fun c => hscal (g c) (hg_comm c c.2)
  choose a ha using hex
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hsmul : ∀ x y : K, (∀ v : ι → K, x • v = y • v) → x = y := by
    intro x y h
    have := congrFun (h (Pi.single i 1)) i
    simpa using this
  have ha_one : a 1 = 1 := by
    apply hsmul
    intro v
    rw [← ha, one_smul]
    exact hg_one v
  have ha_mul : ∀ c c' : ↥(Subgroup.centralizer (H : Set (MulAut W))), a (c * c') = a c * a c' := by
    intro c c'
    apply hsmul
    intro v
    rw [← ha, mul_smul, ← ha c' v, ← ha c, ← hg_mul]
    rfl
  let lam : ↥(Subgroup.centralizer (H : Set (MulAut W))) →* K :=
    { toFun := a
      map_one' := ha_one
      map_mul' := ha_mul }
  refine ⟨lam.toHomUnits, ?_⟩
  rw [injective_iff_map_eq_one]
  intro c hc
  have hc1 : a c = 1 := by
    have h : lam c = 1 := by
      have := congrArg Units.val hc
      simpa using this
    exact h
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have h2 : g c (Multiplicative.toAdd (eβ w)) = Multiplicative.toAdd (eβ w) := by
    rw [ha, hc1, one_smul]
  rw [hg] at h2
  simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h2
  have h3 := Multiplicative.toAdd.injective h2
  have h4 := eβ.injective h3
  simpa using h4

private theorem s16e_omc_exists_ne_zero_ne_one {K : Type} [Field K] [Finite K]
    (h : Nat.card K = 4) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  haveI := Fintype.ofFinite K
  have h2 : 2 < Fintype.card K := by rw [← Nat.card_eq_fintype_card, h]; norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h2
  by_contra hcon
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := fun x => by
    by_cases h0 : x = 0
    · exact Or.inl h0
    · exact Or.inr (by_contra fun h1 => hcon ⟨x, h0, h1⟩)
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> rcases h01 c with rfl | rfl <;>
    simp_all

theorem s16e_omc_centralizer_embeds_units {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : NatOmegaPlus H (⊤ : Subgroup W) ⊥ 4 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ f : ↥(Subgroup.centralizer (H : Set (MulAut W))) →* Kˣ, Function.Injective f := by
  obtain ⟨-, K, hKf, hKfin, hK, π, hπ⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  exact ⟨K, hKf, hKfin, hK4, s16e_omc_centralizer_hom_units
    (addCommutantScalar_statedOmegaPlus_two (s16e_omc_exists_ne_zero_ne_one hK4)) hπ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
