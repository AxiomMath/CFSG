module

public import CFSG.Quasithin.EmptyFaithful.SzPS8L28
public import CFSG.Quasithin.Vol2.Ch1Five
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace SzPS8

section Sl2

open L28

theorem center_sl2_f8 : Subgroup.center SL(2, F8) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h2 := sub_pow_char (p := 2) r 1
  rw [hr, one_pow, sub_self] at h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h2)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem not_isMulCommutative_sl2_f8 : ¬ IsMulCommutative SL(2, F8) := by
  intro hc
  have hcard : 1 < Nat.card SL(2, F8) := by rw [card_sl2_f8]; norm_num
  have hnt : Nontrivial SL(2, F8) := Finite.one_lt_card_iff_nontrivial.mp hcard
  have hc' : Subgroup.center SL(2, F8) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact Subgroup.mem_center_iff.mpr fun h => hc.is_comm.comm h g
  rw [center_sl2_f8] at hc'
  exact bot_ne_top hc'

noncomputable def slEquivPsl2_f8 : SL(2, F8) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F8 :=
  (QuotientGroup.quotientBot (G := SL(2, F8))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq center_sl2_f8.symm)

theorem nonempty_statedProj_of_sl2_f8 {X : Type} [Group X] (e : X ≃* SL(2, F8)) :
    Nonempty (X ≃* StatedProj (StatedSL 2 F8)) :=
  ⟨e.trans (slEquivPsl2_f8.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F8))⟩

theorem fusionIsBenderGroup_of_sl2_f8 {X : Type} [Group X] (e : X ≃* SL(2, F8)) :
    fusionIsBenderGroup X :=
  Or.inl ⟨3, by norm_num, ⟨e.trans slEquivPsl2_f8⟩⟩

end Sl2

section Types

theorem card_sl2_finiteField {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have hq1 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

variable {Q S : Type} [Group Q] [Group S]

theorem ker_eq_center_of_quasisimple (hq : CFSG.IsQuasisimple Q) (hS : IsSimpleGroup S)
    (hSnc : ¬ IsMulCommutative S) (ψ : Q →* S) (hψ : Function.Surjective ψ) :
    ψ.ker = Subgroup.center Q := by
  have hSnt : Nontrivial S := hS.toNontrivial
  have hcS : Subgroup.center S = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      apply hSnc
      refine ⟨⟨fun a b => ?_⟩⟩
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  have hZ : Subgroup.center Q ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : ψ z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨x, rfl⟩ := hψ s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    rw [hcS, Subgroup.mem_bot] at this
    exact this
  refine le_antisymm ?_ hZ
  rcases hq.2.1.eq_bot_or_eq_top_of_normal
    ((ψ.ker).map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈
        (ψ.ker).map (QuotientGroup.mk' (Subgroup.center Q)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · exfalso
    have hall : ∀ x, x ∈ ψ.ker := by
      intro x
      have : QuotientGroup.mk' (Subgroup.center Q) x ∈
          (ψ.ker).map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [h]
        trivial
      obtain ⟨n, hn, hnx⟩ := this
      have h1 : n⁻¹ * x ∈ Subgroup.center Q := by
        rw [← QuotientGroup.eq]
        simpa using hnx
      have := ψ.ker.mul_mem hn (hZ h1)
      simpa using this
    have hone : ∀ s : S, s = 1 := by
      intro s
      obtain ⟨x, rfl⟩ := hψ s
      exact MonoidHom.mem_ker.mp (hall x)
    obtain ⟨a, b, hab⟩ := exists_pair_ne S
    exact hab ((hone a).trans (hone b).symm)

open L28 in
theorem not_isMulCommutative_of_sl2_f8 (e : S ≃* SL(2, F8)) : ¬ IsMulCommutative S := fun h =>
  not_isMulCommutative_sl2_f8 ⟨⟨fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.is_comm.comm _ _⟩⟩

open L28 in
theorem isPGroup_ker_of_quasisimple {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hS : IsSimpleGroup S) (e : S ≃* SL(2, F8)) (φ : X →* S) (hφ : Function.Surjective φ) :
    IsPGroup 2 φ.ker := by
  have hSnc := not_isMulCommutative_of_sl2_f8 e
  have hker := ker_eq_center_of_quasisimple hq hS hSnc φ hφ
  have : Group.IsPerfect X := hq.1
  obtain ⟨e'⟩ := nonempty_statedProj_of_sl2_f8
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e)
  exact isPGroup_two_of_mulEquiv_stated_psl_two_even (K := F8) φ.ker hker.le (n := 3)
    (by norm_num) (GaloisField.card 2 3 (by norm_num)) e'

open L28 in
theorem false_of_case34 {X : Type} [Group X] [Finite X] (h34 : A36Case3 X ∨ A36Case4 X)
    (hS : IsSimpleGroup S) (e : S ≃* SL(2, F8)) (φ : X →* S) (hφ : Function.Surjective φ) :
    False := by
  obtain ⟨r, hr, h5, χ₀, hχ₀, hker⟩ := exists_sl2_surjection_of_case34 h34
  have hSnc := not_isMulCommutative_of_sl2_f8 e
  have hF : CFSG.fittingSubgroup X ≤ φ.ker := by
    set F := CFSG.fittingSubgroup X with hFdef
    have hFn : (F.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    have hnil : Group.IsNilpotent ↥(F.map φ) :=
      Group.nilpotent_of_surjective (φ.subgroupMap F) (φ.subgroupMap_surjective F)
    rcases hS.eq_bot_or_eq_top_of_normal (F.map φ) with h | h
    · intro x hx
      have : φ x ∈ F.map φ := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hsolv : Group.IsSolvable ↥(F.map φ) := inferInstance
      rw [h] at hsolv
      have hs : Group.IsSolvable S :=
        Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := S)).toMonoidHom)
          (Subgroup.topEquiv (G := S)).surjective
      exact hSnc ⟨⟨fun a b => (IsSimpleGroup.comm_iff_isSolvable.mpr hs) a b⟩⟩
  have hle : χ₀.ker ≤ φ.ker := hker ▸ hF
  let ξ : SL(2, ZMod r) →* S := χ₀.liftOfSurjective hχ₀ ⟨φ, hle⟩
  have hξχ : ∀ x, ξ (χ₀ x) = φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hle⟩ x
  have hξ : Function.Surjective ξ := fun s => by
    obtain ⟨x, rfl⟩ := hφ s
    exact ⟨χ₀ x, hξχ x⟩
  have hqs : CFSG.IsQuasisimple SL(2, ZMod r) := A36B.isQuasisimple_sl2 hr h5
  have hkerξ := ker_eq_center_of_quasisimple hqs hS hSnc ξ hξ
  have hr2 : r ≠ 2 := by omega
  have hcardK : Nat.card ξ.ker = 2 := by
    rw [hkerξ]
    exact A36B.card_center_sl2 hr hr2
  have hcardS : Nat.card S = 504 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_sl2_f8
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ξ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ξ hξ).toEquiv, hcardK,
    hcardS] at h1
  have : Fact r.Prime := ⟨hr⟩
  have h2 : Nat.card SL(2, ZMod r) = r * (r ^ 2 - 1) := by
    rw [card_sl2_finiteField, Nat.card_zmod]
  rw [h2] at h1
  have hlt : r < 12 := by
    by_contra hge
    push Not at hge
    have h144 : 144 ≤ r ^ 2 := by nlinarith
    have h4 : 12 * 143 ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul hge (by omega)
    rw [h1] at h4
    norm_num at h4
  interval_cases r <;> omega

open L28 in
theorem isPGroup_ker_of_a36_lift {Lg X : Type} [Group Lg] [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X ∨ A36Case3 X ∨ A36Case4 X) (hS : IsSimpleGroup S)
    (e : S ≃* SL(2, F8)) (ψ : Lg →* X) (hψ : Function.Surjective ψ) (hψ2 : IsPGroup 2 ψ.ker)
    (χ : Lg →* S) (hχ : Function.Surjective χ) (hle : ψ.ker ≤ χ.ker) : IsPGroup 2 χ.ker := by
  let φ : X →* S := ψ.liftOfSurjective hψ ⟨χ, hle⟩
  have hφψ : ∀ x, φ (ψ x) = χ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hle⟩ x
  have hφ : Function.Surjective φ := fun s => by
    obtain ⟨x, rfl⟩ := hχ s
    exact ⟨ψ x, hφψ x⟩
  have hker : IsPGroup 2 φ.ker := by
    rcases hX with hq | h34
    · exact isPGroup_ker_of_quasisimple hq hS e φ hφ
    · rcases h34 with h3 | h4
      · exact (false_of_case34 (Or.inl h3) hS e φ hφ).elim
      · exact (false_of_case34 (Or.inr h4) hS e φ hφ).elim
  intro ⟨x, hx⟩
  have hx' : φ (ψ x) = 1 := by rw [hφψ]; exact hx
  obtain ⟨k, hk⟩ := hker ⟨ψ x, hx'⟩
  have hk' : (ψ x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hmem : x ^ 2 ^ k ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hk'
  obtain ⟨j, hj⟩ := hψ2 ⟨x ^ 2 ^ k, hmem⟩
  refine ⟨k + j, Subtype.ext ?_⟩
  have hj' : (x ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  simpa [pow_add, pow_mul] using hj'

end Types

end SzPS8

end CFSG.Quasithin
