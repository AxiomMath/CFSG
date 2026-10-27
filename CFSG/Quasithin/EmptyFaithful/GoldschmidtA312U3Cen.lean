module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Dick

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem card_perfect_of_le_centralizer_K (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ 2) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {t : H ⧸ Subgroup.center H} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (L : Subgroup (H ⧸ Subgroup.center H)) [Group.IsPerfect L] (hL : L ≠ ⊥)
    (hLt : ∀ x ∈ L, x * t = t * x) :
    Nat.card L = 120 ∨ Nat.card L = 40 ∨ Nat.card L = p * (p ^ 2 - 1) ∨
      Nat.card L = p ^ 2 * (p ^ 4 - 1) := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_sq hp2 hK
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  obtain ⟨t', rfl, ht'2⟩ := exists_lift_pow_eq_one le_rfl hZ3 (by norm_num : Nat.Coprime 2 3)
    t ht2
  have ht'1 : (t' : GL (Fin 3) K) ≠ 1 := fun h =>
    ht1 (by rw [show t' = 1 from Subtype.ext h, QuotientGroup.mk_one])
  set M := L.comap (QuotientGroup.mk' (Subgroup.center H)) with hM
  set D := ⁅M, M⁆ with hD
  have hDp : Group.IsPerfect D := isPerfect_commutator_comap le_rfl L
  have hDL : D.map (QuotientGroup.mk' (Subgroup.center H)) = L := map_commutator_comap L
  have hDM : D ≤ M := Subgroup.commutator_le_self M
  have hcomm : ∀ y ∈ D, y * t' = t' * y := by
    intro y hy
    have hyL : ((y : H) : H ⧸ Subgroup.center H) ∈ L := hDM hy
    have := commute_of_commute_mk le_rfl hZ3 (by norm_num : Nat.Coprime 2 3) ht'2
      (hLt _ hyL).symm
    exact this.symm
  set X := D.map H.subtype with hX
  have hXc : ∀ x ∈ X, x * (t' : GL (Fin 3) K) = t' * x := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcomm y hy)
  have hXdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨y, -, rfl⟩
    exact hdet _ y.2
  obtain ⟨ρ, hρ, -⟩ := exists_injective_gl2_of_commute h2
    (by rw [← Subgroup.coe_mul, ← sq, ht'2, Subgroup.coe_one]) ht'1 (hdet _ t'.2) X hXc hXdet
  have eDX : D ≃* X := D.equivMapOfInjective H.subtype H.subtype_injective
  have hXp : Group.IsPerfect X := Group.IsPerfect.map _
  obtain ⟨P, ⟨eXP⟩⟩ := exists_sl2_copy_of_perfect ρ hρ
  have hPp : Group.IsPerfect P := Group.IsPerfect.ofSurjective (f := eXP.toMonoidHom)
    eXP.surjective
  have hDne : D ≠ ⊥ := by
    intro h
    apply hL
    rw [← hDL, h, Subgroup.map_bot]
  have hPne : P ≠ ⊥ := by
    intro h
    apply hDne
    have : Subsingleton P := by rw [h]; infer_instance
    have : Subsingleton D := (eDX.trans eXP).toEquiv.subsingleton
    exact Subgroup.eq_bot_of_subsingleton D
  have hcardDP : Nat.card D = Nat.card P := Nat.card_congr (eDX.trans eXP).toEquiv
  set k : D →* H ⧸ Subgroup.center H := (QuotientGroup.mk' (Subgroup.center H)).comp D.subtype
  have hkrange : k.range = L := by
    rw [← hDL, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardL : Nat.card D = Nat.card L * Nat.card k.ker := by
    rw [← hkrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange k).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hker : ∀ d ∈ k.ker, (d : H) ∈ Subgroup.center H := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    exact (QuotientGroup.eq_one_iff _).mp hd
  have hkerZ : Nat.card k.ker ∣ 3 := by
    have hsub : Nat.card k.ker ∣ Nat.card (Subgroup.center H) := by
      let φ : k.ker →* Subgroup.center H :=
        { toFun := fun d => ⟨((d : D) : H), hker d d.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hφ : Function.Injective φ := by
        intro a b hab
        have h' : ((φ a : Subgroup.center H) : H) = ((φ b : Subgroup.center H) : H) := by
          rw [hab]
        exact Subtype.ext (Subtype.ext h')
      rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact Nat.dvd_trans hsub hZ
  have hkc : k.ker ≤ Subgroup.center D := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker d hd) (y : H)
  rcases perfect_sl2_mulEquiv hp2 hK P hPne with h5 | ⟨m, hm0, hm2, ⟨em⟩⟩
  · obtain ⟨e5⟩ := h5
    have h120 : Nat.card P = 120 := by
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      rw [Nat.card_congr e5.toEquiv, card_sl2_field (F := ZMod 5), Nat.card_zmod]
      norm_num
    rw [hcardDP, h120] at hcardL
    rcases (Nat.dvd_prime Nat.prime_three).mp hkerZ with h | h
    · left; rw [h, mul_one] at hcardL; exact hcardL.symm
    · right; left; rw [h] at hcardL; omega
  · have h2GF : (2 : GaloisField p m) ≠ 0 := by
      intro h
      have hc : ringChar (GaloisField p m) = p := ringChar.eq (GaloisField p m) p
      have : ((2 : ℕ) : GaloisField p m) = 0 := by exact_mod_cast h
      rw [ringChar.spec, hc] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hZD : Nat.card (Subgroup.center D) = 2 := by
      have e : D ≃* SL(2, GaloisField p m) := (eDX.trans eXP).trans em
      rw [← natCard_center_sl2 h2GF]
      exact Nat.card_congr ((Subgroup.centerCongr e).toEquiv)
    have hker2 : Nat.card k.ker ∣ 2 := by
      have := Subgroup.card_dvd_of_le hkc
      rwa [hZD] at this
    have hker1 : Nat.card k.ker = 1 := by
      have := Nat.dvd_gcd hker2 hkerZ
      simpa using this
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hcardP : Nat.card P = p ^ m * ((p ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr em.toEquiv, card_sl2_field, hGF]
    rw [hcardDP, hcardP, hker1, mul_one] at hcardL
    have hm12 : m = 1 ∨ m = 2 := by
      have := Nat.le_of_dvd (by norm_num) hm2
      omega
    right; right
    rcases hm12 with rfl | rfl
    · left
      rw [pow_one] at hcardL
      exact hcardL.symm
    · right
      rw [show (p ^ 2) ^ 2 = p ^ 4 by ring] at hcardL
      exact hcardL.symm

end CFSG.Quasithin.A312U3
