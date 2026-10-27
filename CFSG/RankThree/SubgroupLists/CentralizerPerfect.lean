module

public import CFSG.RankThree.SubgroupLists.QuasisimpleRankTwo
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.RankThree.SubgroupLists.CentralThreeLift

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix
open scoped MatrixGroups

theorem card_sl2_field {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by
      rcases Nat.lt_or_ge q 2 with h | h
      · have : 2 ≤ q := by
          have := Fintype.one_lt_card (α := F)
          rw [← Nat.card_eq_fintype_card] at this
          omega
        omega
      · omega)]

theorem exists_sl2_copy_of_perfect {K : Type*} [Field K] {X : Type*} [Group X]
    [Group.IsPerfect X] (ρ : X →* GL (Fin 2) K) (hρ : Function.Injective ρ) :
    ∃ P : Subgroup SL(2, K), Nonempty (X ≃* P) := by
  classical
  have hdet : ∀ x : X, ((ρ x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    intro x
    have h := (MonoidHom.mem_ker (f := Matrix.GeneralLinearGroup.det.comp ρ)).mp
      (Abelianization.commutator_subset_ker _ (Group.IsPerfect.mem_commutator (g := x)))
    have := congrArg Units.val h
    simpa using this
  let σ : X →* SL(2, K) :=
    { toFun := fun x => ⟨(ρ x : Matrix (Fin 2) (Fin 2) K), hdet x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        change ((ρ (x * y) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          ((ρ x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((ρ y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        rw [map_mul, Units.val_mul] }
  have hσ : Function.Injective σ := by
    intro x y h
    apply hρ
    apply Units.ext
    exact congrArg Subtype.val h
  exact ⟨σ.range, ⟨MonoidHom.ofInjective hσ⟩⟩

theorem card_perfect_of_le_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {t : H ⧸ Subgroup.center H} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (L : Subgroup (H ⧸ Subgroup.center H)) [Group.IsPerfect L] (hL : L ≠ ⊥)
    (hLt : ∀ x ∈ L, x * t = t * x) :
    Nat.card L = 120 ∨ Nat.card L = 40 ∨ Nat.card L = p * (p ^ 2 - 1) := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  obtain ⟨t', rfl, ht'2⟩ := exists_lift_pow_eq_one le_rfl hZ3 (by norm_num : Nat.Coprime 2 3)
    t ht2
  have ht'1 : (t' : GL (Fin 3) (ZMod p)) ≠ 1 := fun h =>
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
  have hXc : ∀ x ∈ X, x * (t' : GL (Fin 3) (ZMod p)) = t' * x := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hcomm y hy)
  have hXdet : ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
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
  rcases perfect_sl2_mulEquiv hp2 (by rw [Nat.card_zmod, pow_one] : Nat.card (ZMod p) = p ^ 1) P
      hPne with h5 | ⟨m, hm0, hm1, ⟨em⟩⟩
  · obtain ⟨e5⟩ := h5
    have h120 : Nat.card P = 120 := by
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      rw [Nat.card_congr e5.toEquiv, card_sl2_field (F := ZMod 5), Nat.card_zmod]
      norm_num
    rw [hcardDP, h120] at hcardL
    rcases (Nat.dvd_prime Nat.prime_three).mp hkerZ with h | h
    · left; rw [h, mul_one] at hcardL; exact hcardL.symm
    · right; left; rw [h] at hcardL; omega
  · have hm : m = 1 := Nat.dvd_one.mp hm1
    subst hm
    have hGF : Nat.card (GaloisField p 1) = p := by
      rw [GaloisField.card p 1 one_ne_zero, pow_one]
    have hcardP : Nat.card P = p * (p ^ 2 - 1) := by
      rw [Nat.card_congr em.toEquiv, card_sl2_field, hGF]
    have hkc : k.ker ≤ Subgroup.center D := by
      intro d hd
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (hker d hd) (y : H)
    have h2GF : (2 : GaloisField p 1) ≠ 0 := by
      intro h
      have hc : ringChar (GaloisField p 1) = p := ringChar.eq (GaloisField p 1) p
      have : ((2 : ℕ) : GaloisField p 1) = 0 := by exact_mod_cast h
      rw [ringChar.spec, hc] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hZD : Nat.card (Subgroup.center D) = 2 := by
      have e : D ≃* SL(2, GaloisField p 1) := (eDX.trans eXP).trans em
      rw [← natCard_center_sl2 h2GF]
      exact Nat.card_congr ((Subgroup.centerCongr e).toEquiv)
    have hker2 : Nat.card k.ker ∣ 2 := by
      have := Subgroup.card_dvd_of_le hkc
      rwa [hZD] at this
    have hker1 : Nat.card k.ker = 1 := by
      have := Nat.dvd_gcd hker2 hkerZ
      simpa using this
    right; right
    rw [hcardDP, hcardP, hker1, mul_one] at hcardL
    exact hcardL.symm

end CFSG.RankThree.SubgroupLists
