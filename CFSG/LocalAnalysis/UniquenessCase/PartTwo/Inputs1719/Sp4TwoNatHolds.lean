module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatTorus
public import CFSG.ClassicalGroups.Symplectic.Sp4LagrangianParabolic
public import CFSG.Quasithin.Background.RealizesFaithful
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.C48PfFourModPfNat
public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Matrix Subgroup CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.ClassicalGroups.Symplectic.Sp4

private theorem conj_apply_eq_iff {W : Type} [CommGroup W] (h s : MulAut W) (w : W) :
    MulAut.conj h s w = w ↔ s (h⁻¹ w) = h⁻¹ w := by
  constructor <;> intro hw
  · simpa [MulAut.mul_apply] using congrArg (fun z => h⁻¹ z) hw
  · rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, hw, MulAut.apply_inv_self]

theorem isSylowIn_exists_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q H : Subgroup G} (hP : IsSylowIn p P H) (hQ : IsSylowIn p Q H) :
    ∃ h ∈ H, Q = P.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨h, hh, hQP⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hP hQ
  refine ⟨h, hh, Subgroup.ext fun x => ?_⟩
  rw [hQP, mem_map]
  constructor
  · exact fun hx => ⟨h⁻¹ * x * h, hx, by simp [mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

theorem sumOfNatVia_two {W : Type} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)}
    {π : D.Gam →* ↥H} (hsum : SumOfNatVia D H ⊤ ⊥ 2 π) :
    ∃ I₀ I₁ : Subgroup W, I₀ ⊓ I₁ = ⊥ ∧ I₀ ⊔ I₁ = ⊤ ∧
      D.RealizesVia H I₀ ⊥ π ∧ D.RealizesVia H I₁ ⊥ π := by
  obtain ⟨I, -, hind, hsup, hreal⟩ := hsum
  have h1 : I 1 ≤ ⨆ (j : Fin 2) (_ : j ≠ 0), I j := le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl
  refine ⟨I 0, I 1, le_antisymm ((inf_le_inf_left _ (le_sup_of_le_right h1)).trans (hind 0))
    bot_le, ?_, hreal 0, hreal 1⟩
  rw [← hsup, bot_sup_eq]
  exact le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1))
    (iSup_le fun i => by fin_cases i <;> simp)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem two_le_of_card_eq_two_pow {f r : ℕ} (hK : Nat.card K = 2 ^ f) (hr : r.Prime)
    (hrd : r ∣ 2 ^ f - 1) : 2 ≤ f := by
  rcases Nat.lt_or_ge f 2 with hf | hf
  · interval_cases f
    · rw [pow_zero] at hK
      exact absurd hK Finite.one_lt_card.ne'
    · rw [pow_one] at hrd
      exact absurd (Nat.dvd_one.mp hrd) hr.ne_one
  · exact hf

theorem unipotent_isSylowIn :
    IsSylowIn 2 (unipotent (r := 2) K) (⊤ : Subgroup (StatedSp 2 K)) := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  have hPcoe : (P : Subgroup (StatedSp 2 K)) = unipotent 2 K := hP
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hPcoe]; exact P.isPGroup'
  · rw [← hPcoe]
    simpa using Sylow.not_dvd_index P

theorem isL2_lam_zero_range (f : ℕ) (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    IsL2 ↥((lam (0 : Fin 2) : SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range) f :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (MonoidHom.ofInjective (CFSG.ComponentClassification.Burgoyne.Sp.lam_injective 0))
    (uc22p22d_isL2_of_statedSL hf2 hK (specialLinearGroupEquivStatedSL 2 K))

theorem isL2_leviConjHom_range (f : ℕ) (hK : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    IsL2 ↥(leviConjHom (K := K)).range f :=
  CFSG.Blueprint.LieModel.of_mulEquiv (MonoidHom.ofInjective leviConjHom_injective)
    (uc22p22d_isL2_of_statedSL hf2 hK (specialLinearGroupEquivStatedSL 2 K))

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
  {π : ↥(StatedSp 2 K) →* ↥H}

theorem isSylowIn_unipotent_map (hπi : Function.Injective π) (hπs : Function.Surjective π) :
    IsSylowIn 2 ((unipotent 2 K).map (H.subtype.comp π)) H := by
  refine isSylowIn_of_card_eq (by rintro _ ⟨u, -, rfl⟩; exact (π u).2) ?_
  rw [card_map_of_injective (fun _ _ hxy => hπi (Subtype.ext hxy)), unipotent_isSylowIn.card_eq,
    card_top, Nat.card_congr (MulEquiv.ofBijective π ⟨hπi, hπs⟩).toEquiv]

theorem natSummand_fix {I : Subgroup W}
    (hR : (FFModel.nat (StatedSp 2 K)).RealizesVia H I ⊥ π) {a : W} (ha : a ∈ I)
    (haU : ∀ u ∈ unipotent 2 K, ((π u : ↥H) : MulAut W) a = a) (g : StatedSp 2 K) :
    (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) 1 →
      ((π g : ↥H) : MulAut W) a = a) ∧
    (a ≠ 1 → ((π g : ↥H) : MulAut W) a = a →
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) 1) := by
  obtain ⟨β, -, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hR
  have hβi : Function.Injective β := (injective_iff_map_eq_one β).mpr fun u hu =>
    Subtype.ext (mem_bot.mp ((hβk u).mp hu))
  set v : Fin 2 ⊕ Fin 2 → K := Multiplicative.toAdd (β ⟨a, ha⟩) with hvdef
  have key : ∀ γ : StatedSp 2 K, ((π γ : ↥H) : MulAut W) a = a ↔
      ((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v := by
    intro γ
    have he : β ⟨((π γ : ↥H) : MulAut W) a, hR.2.2.2.1 (π γ) a ha⟩ = Multiplicative.ofAdd
        (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) :=
      hβe γ ⟨a, ha⟩ (hR.2.2.2.1 (π γ) a ha)
    constructor
    · intro hγa
      rw [show (⟨((π γ : ↥H) : MulAut W) a, hR.2.2.2.1 (π γ) a ha⟩ : ↥I) = ⟨a, ha⟩ from
        Subtype.ext hγa] at he
      exact (congrArg Multiplicative.toAdd he).symm
    · intro hγv
      have h2 : β ⟨((π γ : ↥H) : MulAut W) a, hR.2.2.2.1 (π γ) a ha⟩ = β ⟨a, ha⟩ :=
        he.trans (congrArg Multiplicative.ofAdd hγv)
      exact congrArg Subtype.val (hβi h2)
  have hv := unipotent_fixed_eq_smul v fun u hu => (key u).mp (haU u hu)
  refine ⟨fun hg => (key g).mpr (by rw [hv, mulVec_smul, hg]), fun ha1 hga => ?_⟩
  have hc : v (Sum.inl 0) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hv
    exact ha1 (mem_bot.mp ((hβk ⟨a, ha⟩).mp
      (Multiplicative.toAdd.injective (hv.trans toAdd_one.symm))))
  have h := (key g).mp hga
  rw [hv, mulVec_smul] at h
  exact smul_right_injective _ hc h

variable {I₀ I₁ : Subgroup W} (hdisj : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤)
  (hR₀ : (FFModel.nat (StatedSp 2 K)).RealizesVia H I₀ ⊥ π)
  (hR₁ : (FFModel.nat (StatedSp 2 K)).RealizesVia H I₁ ⊥ π)
include hdisj hsup hR₀ hR₁

theorem fixU_components {y : W} (hy : y ∈ fixV ((unipotent 2 K).map (H.subtype.comp π))) :
    ∃ a ∈ I₀, ∃ b ∈ I₁, a * b = y ∧
      (∀ u ∈ unipotent 2 K, ((π u : ↥H) : MulAut W) a = a) ∧
      ∀ u ∈ unipotent 2 K, ((π u : ↥H) : MulAut W) b = b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp (by rw [hsup]; exact mem_top y : y ∈ I₀ ⊔ I₁)
  have hU := fun u (hu : u ∈ unipotent 2 K) => C48Pf.FMod.fixed_of_mul_fixed hdisj
    (hR₀.2.2.2.1 (π u)) (hR₁.2.2.2.1 (π u)) ha hb (mem_fixV.mp hy _ (mem_map_of_mem _ hu))
  exact ⟨a, ha, b, hb, rfl, fun u hu => (hU u hu).1, fun u hu => (hU u hu).2⟩

theorem fix_of_mulVec_e1 {g : StatedSp 2 K}
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) 1) :
    ∀ w ∈ fixV ((unipotent 2 K).map (H.subtype.comp π)), ((π g : ↥H) : MulAut W) w = w := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl, haU, hbU⟩ := fixU_components hdisj hsup hR₀ hR₁ hw
  rw [map_mul, (natSummand_fix hR₀ ha haU g).1 hg, (natSummand_fix hR₁ hb hbU g).1 hg]

theorem mulVec_e1_of_fix {g : StatedSp 2 K} {y : W}
    (hy : y ∈ fixV ((unipotent 2 K).map (H.subtype.comp π))) (hy1 : y ≠ 1)
    (hgy : ((π g : ↥H) : MulAut W) y = y) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) 1 := by
  obtain ⟨a, ha, b, hb, rfl, haU, hbU⟩ := fixU_components hdisj hsup hR₀ hR₁ hy
  obtain ⟨hga, hgb⟩ :=
    C48Pf.FMod.fixed_of_mul_fixed hdisj (hR₀.2.2.2.1 (π g)) (hR₁.2.2.2.1 (π g)) ha hb hgy
  by_cases ha1 : a = 1
  · subst ha1
    exact (natSummand_fix hR₁ hb hbU g).2 (by simpa using hy1) hgb
  · exact (natSummand_fix hR₀ ha haU g).2 ha1 hga

omit hdisj hsup hR₀ hR₁

theorem pointTorus_exists {S : Subgroup (MulAut W)} {f r : ℕ} (hKcard : Nat.card K = 2 ^ f)
    (hsum : SumOfNatVia (FFModel.nat (StatedSp 2 K)) H ⊤ ⊥ 2 π)
    (hSyl : IsSylowIn 2 S H) (hr : r.Prime) (hrd : r ∣ 2 ^ f - 1) :
    ∃ b ∈ H, ∃ x ∈ H, ∃ Y : Subgroup (MulAut W),
      b ∈ normalizer (S : Set (MulAut W)) ∧ orderOf b = r ∧
        (∀ w ∈ fixV S, b w = w) ∧ (∀ w ∈ fixV S, x w = w) ∧
        x * b * x⁻¹ = b⁻¹ ∧
        Y ≤ H ⊓ centralizer ({b} : Set (MulAut W)) ∧ IsL2 ↥Y f := by
  have hf2 := two_le_of_card_eq_two_pow hKcard hr hrd
  obtain ⟨I₀, I₁, hdisj, hsup, hR₀, hR₁⟩ := sumOfNatVia_two hsum
  have hπi := FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful _) hR₀
  obtain ⟨h, hhH, hSconj⟩ := isSylowIn_exists_conj (isSylowIn_unipotent_map hπi hR₀.1) hSyl
  set φ : StatedSp 2 K →* MulAut W := (MulAut.conj h).toMonoidHom.comp (H.subtype.comp π)
  have hφi : Function.Injective φ :=
    (MulAut.conj h).injective.comp (H.subtype_injective.comp hπi)
  have hφH : ∀ g, φ g ∈ H := fun g => H.mul_mem (H.mul_mem hhH (π g).2) (H.inv_mem hhH)
  have hS : S = (unipotent 2 K).map φ := by rw [hSconj, Subgroup.map_map]
  have hfix : ∀ g : StatedSp 2 K,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single (Sum.inl 0) (1 : K) = Pi.single (Sum.inl 0) 1 → ∀ w ∈ fixV S, φ g w = w := by
    intro g hg w hw
    rw [hSconj] at hw
    exact (conj_apply_eq_iff h ((π g : ↥H) : MulAut W) w).mpr
      (fix_of_mulVec_e1 hdisj hsup hR₀ hR₁ hg _ (ConjTransport.mem_fixV_map_conj_iff.mp hw))
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units, hKcard])
  refine ⟨φ (torusHom (Pi.mulSingle 1 β)), hφH _, φ (lam 1 sl2W), hφH _,
    (lam (0 : Fin 2) : SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range.map φ, ?_, ?_,
    hfix _ (torusHom_mulVec_e1 β), hfix _ lam_sl2W_mulVec_e1, ?_, ?_, ?_⟩
  · rw [hS]
    exact le_normalizer_map φ (mem_map_of_mem φ (torusHom_mem_normalizer_unipotent _))
  · rw [orderOf_injective φ hφi, orderOf_torusHom_mulSingle, hβ]
  · simpa only [map_mul, map_inv] using congrArg φ (sl2W_conj_torusHom β)
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨hφH _, mem_centralizer_singleton_iff.mpr
      ((commute_lam_torusHom_mulSingle (by decide) g β).map φ)⟩
  · exact CFSG.Blueprint.LieModel.of_mulEquiv (equivMapOfInjective _ φ hφi)
      (isL2_lam_zero_range f hKcard hf2)

theorem lineParabolic_exists {S : Subgroup (MulAut W)} {f r : ℕ} (hKcard : Nat.card K = 2 ^ f)
    (hsum : SumOfNatVia (FFModel.nat (StatedSp 2 K)) H ⊤ ⊥ 2 π)
    (hSyl : IsSylowIn 2 S H) (hr : r.Prime) (hrd : r ∣ 2 ^ f - 1) :
    ∃ P Q : Subgroup (MulAut W), P ≤ H ∧ S ≤ P ∧ Q ≤ S ∧
      P ≤ normalizer (Q : Set (MulAut W)) ∧ Q.relIndex S ≤ 2 ^ f ∧
      (∀ y ∈ fixV S, y ≠ 1 → ∀ g ∈ P, Odd (orderOf g) → g y = y → g = 1) ∧
      ∃ b ∈ P, ∃ x ∈ P, ∃ Y : Subgroup (MulAut W),
        b ∈ normalizer (S : Set (MulAut W)) ∧ orderOf b = r ∧
        x * b * x⁻¹ = b⁻¹ ∧
        Y ≤ H ⊓ centralizer ({b} : Set (MulAut W)) ∧ IsL2 ↥Y f := by
  have hf2 := two_le_of_card_eq_two_pow hKcard hr hrd
  obtain ⟨I₀, I₁, hdisj, hsup, hR₀, hR₁⟩ := sumOfNatVia_two hsum
  have hπi := FFModel.RealizesVia.injective_of_faithful_on (FFModel.nat_faithful _) hR₀
  obtain ⟨h, hhH, hSconj⟩ := isSylowIn_exists_conj (isSylowIn_unipotent_map hπi hR₀.1) hSyl
  set φ : StatedSp 2 K →* MulAut W := (MulAut.conj h).toMonoidHom.comp (H.subtype.comp π)
  have hφi : Function.Injective φ :=
    (MulAut.conj h).injective.comp (H.subtype_injective.comp hπi)
  have hφH : ∀ g, φ g ∈ H := fun g => H.mul_mem (H.mul_mem hhH (π g).2) (H.inv_mem hhH)
  have hS : S = (unipotent 2 K).map φ := by rw [hSconj, Subgroup.map_map]
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units, hKcard])
  refine ⟨(lagrangianParabolicSL (K := K)).map φ, (SymplecticFour.radical K).map φ,
    ?_, ?_, ?_, ?_, ?_, ?_, φ (lagrangianTorus β), mem_map_of_mem _ (lagrangianTorus_mem β),
    φ lagrangianWeyl, mem_map_of_mem _ lagrangianWeyl_mem,
    (leviConjHom (K := K)).range.map φ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact hφH g
  · rw [hS]
    exact map_mono unipotent_le_lagrangianParabolicSL
  · rw [hS]
    exact map_mono SymplecticFour.radical_le_unipotent
  · rintro _ ⟨g, hg, rfl⟩
    exact le_normalizer_map φ (mem_map_of_mem φ (lagrangianParabolicSL_le_normalizer_radical hg))
  · rw [hS, relIndex_map_map_of_injective _ _ hφi, radical_relIndex_unipotent, hKcard]
  · rintro y hy hy1 _ ⟨g, hg, rfl⟩ hodd hgy
    rw [hSconj] at hy
    have hgU := mem_unipotent_of_mulVec_e1 hg (mulVec_e1_of_fix hdisj hsup hR₀ hR₁
      (ConjTransport.mem_fixV_map_conj_iff.mp hy) (by simpa using hy1)
      ((conj_apply_eq_iff h ((π g : ↥H) : MulAut W) y).mp hgy))
    obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow unipotent_isSylowIn.isPGroup
      (⟨g, hgU⟩ : ↥(unipotent 2 K))
    have h2k : orderOf (φ g) = 2 ^ k := by
      rw [orderOf_injective φ hφi, ← Subgroup.orderOf_mk g hgU, hk]
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at h2k
    · rw [h2k] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, k.succ_ne_zero⟩))
  · rw [hS]
    exact le_normalizer_map φ (mem_map_of_mem φ (lagrangianTorus_mem_normalizer_unipotent β))
  · rw [orderOf_injective φ hφi, orderOf_lagrangianTorus, hβ]
  · simpa only [map_mul, map_inv] using congrArg φ (lagrangianWeyl_conj_lagrangianTorus β)
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hy
    exact ⟨hφH _, mem_centralizer_singleton_iff.mpr
      ((leviConjHom_commute_lagrangianTorus β A).map φ)⟩
  · exact CFSG.Blueprint.LieModel.of_mulEquiv (equivMapOfInjective _ φ hφi)
      (isL2_leviConjHom_range f hKcard hf2)

theorem k_Sp4TwoNat_pointTorus_holds :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H S : Subgroup (MulAut W)) (f r : ℕ), Sp4TwoNatData H f → IsSylowIn 2 S H →
        r.Prime → r ∣ 2 ^ f - 1 →
          ∃ b ∈ H, ∃ x ∈ H, ∃ Y : Subgroup (MulAut W),
            b ∈ normalizer (S : Set (MulAut W)) ∧ orderOf b = r ∧
              (∀ w ∈ fixV S, b w = w) ∧ (∀ w ∈ fixV S, x w = w) ∧
              x * b * x⁻¹ = b⁻¹ ∧
              Y ≤ H ⊓ centralizer ({b} : Set (MulAut W)) ∧ IsL2 ↥Y f := by
  intro W _ _ _ H S f r hD hSyl hr hrd
  obtain ⟨-, K, _, _, π, hKcard, hsum⟩ := hD
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  exact pointTorus_exists hKcard hsum hSyl hr hrd

theorem k_Sp4TwoNat_lineParabolic_holds :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H S : Subgroup (MulAut W)) (f r : ℕ), Sp4TwoNatData H f → IsSylowIn 2 S H →
        r.Prime → r ∣ 2 ^ f - 1 →
          ∃ P Q : Subgroup (MulAut W), P ≤ H ∧ S ≤ P ∧ Q ≤ S ∧
            P ≤ normalizer (Q : Set (MulAut W)) ∧ Q.relIndex S ≤ 2 ^ f ∧
            (∀ y ∈ fixV S, y ≠ 1 → ∀ g ∈ P, Odd (orderOf g) → g y = y → g = 1) ∧
            ∃ b ∈ P, ∃ x ∈ P, ∃ Y : Subgroup (MulAut W),
              b ∈ normalizer (S : Set (MulAut W)) ∧ orderOf b = r ∧
              x * b * x⁻¹ = b⁻¹ ∧
              Y ≤ H ⊓ centralizer ({b} : Set (MulAut W)) ∧ IsL2 ↥Y f := by
  intro W _ _ _ H S f r hD hSyl hr hrd
  obtain ⟨-, K, _, _, π, hKcard, hsum⟩ := hD
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  exact lineParabolic_exists hKcard hsum hSyl hr hrd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
