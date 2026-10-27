module

public import CFSG.Quasithin.Background.G8Dihedral
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Faithful
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G]

theorem a1_5 {X A : Subgroup G} (hX : Odd (Nat.card X)) (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hfaith : A ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    {n : ℕ} (hcard : Nat.card A = 2 ^ n) :
    ∃ (Hs : Fin n → Subgroup G) (p : Fin n → ℕ), IsDihedralFamily Hs p ∧ A ≤ ⨆ i, Hs i ∧
      (⨆ i, Hs i) ≤ X ⊔ A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hA1 : A = ⊥ := Subgroup.card_eq_one.mp (by simpa using hcard)
    refine ⟨fun i => i.elim0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, iSupIndep_subsingleton _⟩, ?_, ?_⟩
    · simp [hA1]
    · simp
  ·
    classical
    have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard X hX
    have hAnorm : Subgroup.Normalizes A X := ⟨hAX⟩
    have hfaithX : FaithfulSMul A X := by
      refine ⟨fun {a b} hab => ?_⟩
      obtain ⟨a', ha'⟩ := a
      obtain ⟨b', hb'⟩ := b
      have h1 : ∀ x : X, a' * (x : G) * a'⁻¹ = b' * (x : G) * b'⁻¹ := fun x => by
        have := congrArg (fun y : X => (y : G)) (hab x)
        simpa using this
      have hc : b'⁻¹ * a' ∈ A ⊓ Subgroup.centralizer (X : Set G) := by
        refine ⟨A.mul_mem (A.inv_mem hb') ha', ?_⟩
        show b'⁻¹ * a' ∈ Subgroup.centralizer (X : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have := h1 ⟨x, hx⟩
        calc x * (b'⁻¹ * a') = b'⁻¹ * (b' * x * b'⁻¹) * a' := by group
          _ = b'⁻¹ * (a' * x * a'⁻¹) * a' := by rw [← this]
          _ = (b'⁻¹ * a') * x := by group
      rw [hfaith, Subgroup.mem_bot] at hc
      have : a' = b' := by
        have := congrArg (fun y => b' * y) hc
        simpa using this
      exact Subtype.ext this
    have hcop : Nat.Coprime (Nat.card A) (Nat.card X) := by
      rw [hcard]; exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hX)
    have hfaithF : FaithfulSMul A (CFSG.fittingSubgroup X) :=
      CFSG.faithful_on_fitting_of_coprime hsolv hcop
    set F : Subgroup G := (CFSG.fittingSubgroup X).map X.subtype with hF
    have hFX : F ≤ X := Subgroup.map_subtype_le _
    have hFn : Group.IsNilpotent F := by
      have : Group.IsNilpotent (CFSG.fittingSubgroup X) := inferInstance
      exact (Group.isNilpotent_congr
        (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective)).mp this
    have hFodd : Odd (Nat.card F) := hX.of_dvd_nat (Subgroup.card_dvd_of_le hFX)
    have hAF : A ≤ Subgroup.normalizer (F : Set G) :=
      hAX.trans (normalizer_le_normalizer_map_of_characteristic (CFSG.fittingSubgroup X))
    have hFfaith : A ⊓ Subgroup.centralizer (F : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro a ⟨haA, haC⟩
      have hone : (⟨a, haA⟩ : A) = 1 := by
        refine (faithfulSMul_iff.mp hfaithF) _ fun x => ?_
        apply Subtype.ext
        apply Subtype.ext
        have hxF : ((x : X) : G) ∈ F := ⟨x, x.2, rfl⟩
        have hc := Subgroup.mem_centralizer_iff.mp haC _ hxF
        show a * ((x : X) : G) * a⁻¹ = ((x : X) : G)
        calc a * ((x : X) : G) * a⁻¹ = ((x : X) : G) * a * a⁻¹ := by rw [← hc]
          _ = ((x : X) : G) := by group
      have := congrArg Subtype.val hone
      simpa using this
    have hApg : IsPGroup 2 A := isPGroup_of_isElemAbelian hA
    have hFne : F ≠ ⊥ := by
      intro h
      rw [h] at hFfaith
      have hA1 : A = ⊥ := by
        rw [← hFfaith]
        symm
        rw [inf_eq_left]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Subgroup.mem_bot.mp hy]
        simp
      rw [hA1, Subgroup.card_bot] at hcard
      have : 2 ^ n ≥ 2 := by
        calc 2 ^ n ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn
          _ = 2 := by norm_num
      omega
    obtain ⟨Hs, p, hfam, hAle, hle, -⟩ :=
      g8_6 (X := F) (P := A) (A := A) ⟨hA, le_rfl, hApg, hAF, hFn, hFodd, hFne⟩ hn hcard hFfaith
    exact ⟨Hs, p, hfam, hAle, hle.trans (sup_le_sup hFX le_rfl)⟩

end CFSG.Quasithin
