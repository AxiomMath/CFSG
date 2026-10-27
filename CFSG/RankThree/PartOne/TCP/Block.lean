module

public import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.RankThree.PartOne.TCP

open CFSG.GroupTheory.WeirSylow Module

@[expose] def blockDim (e : ℕ) : ℕ := if Even e then e else 2 * e

theorem dvd_pow_sub_one_of_orderOf {p q : ℕ} (hp : p.Prime) (hq : 0 < q) :
    p ∣ q ^ orderOf (q : ZMod p) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((q : ZMod p)) ^ orderOf (q : ZMod p) = 1 := pow_orderOf_eq_one _
  have hq1 : 1 ≤ q ^ orderOf (q : ZMod p) := Nat.one_le_pow _ _ hq
  rw [← (Nat.modEq_iff_dvd' hq1), ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact h1.symm

theorem orderOf_natCast_pos {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    0 < orderOf (q : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hq : (q : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one hq⟩)

theorem exists_block (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F) :
    ∃ S : FormSpace F F, IsSymplecticSpace S ∧
      finrank F S.V = blockDim (orderOf (Nat.card F : ZMod p)) ∧ ∃ c : S.isom, orderOf c = p ∧
        (¬ Even (orderOf (Nat.card F : ZMod p)) →
          ∃ W : Submodule F S.V, W ≠ ⊥ ∧ (∀ v ∈ W, ∀ w ∈ W, S.F v w = 0) ∧
            ∀ w ∈ W, (c : S.V ≃ₗ[F] S.V) w ∈ W) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  set q := Nat.card F with hqdef
  set e := orderOf (q : ZMod p) with hedef
  have hq : 1 < q := Finite.one_lt_card
  have he : 0 < e := orderOf_natCast_pos hp hpF
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  let L := FiniteField.Extension F (ringChar F) e
  have hLcard : Nat.card L = q ^ e := by
    rw [FiniteField.natCard_extension]
  have hLdim : finrank F L = e := FiniteField.finrank_extension F _ e
  have hpdvd : p ∣ q ^ e - 1 := dvd_pow_sub_one_of_orderOf hp (by omega)
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := p) (by rw [hLcard]; exact hpdvd)
  obtain ⟨lam, hlam⟩ := exists_ne_zero_dual (K := F) L
  by_cases hev : Even e
  ·
    obtain ⟨f, hf⟩ := hev
    have hfe : e = 2 * f := by omega
    have hf0 : 0 < f := by omega
    have hnd : ¬ p ∣ q ^ f - 1 := by
      intro h
      have h' : (p : ℤ) ∣ (q : ℤ) ^ f - 1 := by
        have := Int.natCast_dvd_natCast.2 h
        rwa [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one] at this
      rw [dvd_pow_sub_one_iff, ordMod_natCast, ← hedef] at h'
      exact absurd (Nat.le_of_dvd hf0 h') (by omega)
    have hdvd : p ∣ q ^ f + 1 := by
      have hfac : (q ^ f - 1) * (q ^ f + 1) = q ^ e - 1 := by
        have h1 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
        have h2 : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
        zify [h1, h2]
        rw [hfe, pow_mul']
        ring
      have : p ∣ (q ^ f - 1) * (q ^ f + 1) := by rw [hfac]; exact hpdvd
      exact ((Nat.Prime.dvd_mul hp).mp this).resolve_left hnd
    let σ : L ≃ₐ[F] L := FiniteField.frobeniusAlgEquivOfAlgebraic F L ^ f
    have hσσ : ∀ x, σ (σ x) = x := frob_pow_frob_pow (by rw [hLdim, hfe])
    have hζσ : (ζ : L) * σ ζ = 1 := by
      rw [frob_pow_apply, ← pow_succ', hcardF]
      have : ζ ^ (q ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hdvd)
      have h' := congrArg Units.val this
      rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
    let Fix : Submodule F L := LinearMap.ker ((σ : L →ₗ[F] L) - LinearMap.id)
    have hFix : Fix < ⊤ := by
      obtain ⟨x, hx⟩ := exists_pow_ne_self (K := F) (L := L) hf0 (by rw [hLdim]; omega)
      refine lt_top_iff_ne_top.2 fun htop => hx ?_
      have hmem : x ∈ Fix := htop ▸ Submodule.mem_top
      have : σ x - x = 0 := hmem
      rw [← frob_pow_apply]
      exact sub_eq_zero.1 this
    obtain ⟨mu, hmu, hFixmu⟩ := Submodule.exists_le_ker_of_lt_top Fix hFix
    have hmu0 : ∀ z, σ z = z → mu z = 0 := fun z hz =>
      hFixmu (show σ z - z = 0 from sub_eq_zero.2 hz)
    have halt := twistSympForm_isAlt hσσ hmu0
    let S₀ : FormSpace F F := ⟨L, fun x y => twistSympForm mu σ x y⟩
    have hS₀ : IsSymplecticSpace S₀ :=
      ⟨twistSympForm mu σ, fun _ _ => rfl, halt, twistSympForm_nondegenerate hmu hσσ halt⟩
    have hmem : DistribMulAction.toModuleAut F L ζ ∈ S₀.isom := fun x y =>
      toModuleAut_mem_twist mu σ hζσ x y
    refine ⟨S₀, hS₀, ?_, ⟨DistribMulAction.toModuleAut F L ζ, hmem⟩, ?_, fun h => absurd ⟨f, hf⟩ h⟩
    · change finrank F L = blockDim e
      rw [hLdim, blockDim, ite_eq_left_iff.mpr (fun h => absurd ⟨f, hf⟩ h)]
    · rw [Subgroup.orderOf_mk, orderOf_toModuleAut, hζ]
  ·
    let S₀ : FormSpace F F := ⟨L × L, fun v w => hypSympForm lam v w⟩
    have hS₀ : IsSymplecticSpace S₀ :=
      ⟨hypSympForm lam, fun _ _ => rfl, hypSympForm_isAlt lam, hypSympForm_nondegenerate hlam⟩
    have hmem : prodUnitsHom F L ζ ∈ S₀.isom := fun v w => prodUnitsHom_mem_isometry lam ζ v w
    refine ⟨S₀, hS₀, ?_, ⟨prodUnitsHom F L ζ, hmem⟩, ?_, fun _ => ?_⟩
    · change finrank F (L × L) = blockDim e
      rw [Module.finrank_prod, hLdim, blockDim, ite_eq_right_iff.mpr (fun h => absurd h hev)]
      ring
    · rw [Subgroup.orderOf_mk, orderOf_injective _ (prodUnitsHom_injective F L), hζ]
    · refine ⟨Submodule.prod ⊤ ⊥, ?_, ?_, ?_⟩
      · intro h
        have h1 : ((1 : L), (0 : L)) ∈ (Submodule.prod ⊤ ⊥ : Submodule F (L × L)) :=
          ⟨Submodule.mem_top, Submodule.mem_bot F |>.2 rfl⟩
        rw [h] at h1
        have := (Submodule.mem_bot F).1 h1
        exact one_ne_zero (congrArg Prod.fst this)
      · rintro v ⟨-, hv⟩ w ⟨-, hw⟩
        have hv' : v.2 = 0 := (Submodule.mem_bot F).1 hv
        have hw' : w.2 = 0 := (Submodule.mem_bot F).1 hw
        change hypSympForm lam v w = 0
        rw [hypSympForm_apply, hv', hw']
        simp
      · intro w hw
        refine ⟨Submodule.mem_top, ?_⟩
        have hw' : w.2 = 0 := (Submodule.mem_bot F).1 hw.2
        have : (prodUnitsHom F L ζ w).2 = 0 := by
          rw [prodUnitsHom_apply]
          simp [hw']
        exact (Submodule.mem_bot F).2 this

end CFSG.RankThree.PartOne.TCP
