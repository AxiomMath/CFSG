module

public import CFSG.RankThree.SubgroupLists.UnitaryThreeFour

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K]

theorem commute_of_centralize_four_group_K (h2 : (2 : K) ≠ 0) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {a b x y : H ⧸ Subgroup.center H}
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (habc : a * b = b * a) (hxa : x * a = a * x) (hxb : x * b = b * x) (hya : y * a = a * y)
    (hyb : y * b = b * y) : x * y = y * x := by
  classical
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hc2 : Nat.Coprime 2 3 := by norm_num
  obtain ⟨a', rfl, ha'2⟩ := exists_lift_pow_eq_one le_rfl hZ3 hc2 a ha2
  obtain ⟨b', rfl, hb'2⟩ := exists_lift_pow_eq_one le_rfl hZ3 hc2 b hb2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hb'a : b' * a' = a' * b' := (commute_of_commute_mk le_rfl hZ3 hc2 ha'2 habc).symm
  have hx'a : x' * a' = a' * x' := (commute_of_commute_mk le_rfl hZ3 hc2 ha'2 hxa.symm).symm
  have hy'a : y' * a' = a' * y' := (commute_of_commute_mk le_rfl hZ3 hc2 ha'2 hya.symm).symm
  have hx'b : x' * b' = b' * x' := (commute_of_commute_mk le_rfl hZ3 hc2 hb'2 hxb.symm).symm
  have hy'b : y' * b' = b' * y' := (commute_of_commute_mk le_rfl hZ3 hc2 hb'2 hyb.symm).symm
  set C := (Subgroup.centralizer ({a'} : Set H)).map H.subtype with hC
  have hCc : ∀ g ∈ C, g * (a' : GL (Fin 3) K) = a' * g := by
    rintro _ ⟨g, hg, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact congrArg Subtype.val this
  have hCdet : ∀ g ∈ C, (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨g, -, rfl⟩
    exact hdet _ g.2
  have ha'1 : (a' : GL (Fin 3) K) ≠ 1 := fun h =>
    ha1 (by rw [show a' = 1 from Subtype.ext h, QuotientGroup.mk_one])
  obtain ⟨ρ, hρ, hρa⟩ := exists_injective_gl2_of_commute h2
    (by rw [← Subgroup.coe_mul, ← sq, ha'2, Subgroup.coe_one]) ha'1 (hdet _ a'.2) C hCc hCdet
  have hmem : ∀ g : H, g * a' = a' * g → (g : GL (Fin 3) K) ∈ C := fun g hg =>
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg, rfl⟩
  set A : C := ⟨a', hmem a' rfl⟩
  set B : C := ⟨b', hmem b' hb'a⟩
  set X : C := ⟨x', hmem x' hx'a⟩
  set Y : C := ⟨y', hmem y' hy'a⟩
  have hAm : ρ A = -1 := hρa A rfl
  set s := ((ρ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have hBB : B * B = 1 := Subtype.ext (by
    change ((b' : GL (Fin 3) K)) * b' = 1
    rw [← Subgroup.coe_mul, ← sq, hb'2, Subgroup.coe_one])
  have hs : s * s = 1 := by
    change ((ρ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ B : GL _ _) = 1
    rw [← Units.val_mul, ← map_mul, hBB, map_one, Units.val_one]
  have hs1 : s ≠ 1 := by
    intro h
    have hB1 : ρ B = 1 := Units.ext h
    rw [← map_one ρ] at hB1
    have hB : B = 1 := hρ hB1
    apply hb1
    have hb'1 : b' = 1 := Subtype.ext (by simpa [B] using congrArg Subtype.val hB)
    rw [hb'1, QuotientGroup.mk_one]
  have hsn : s ≠ -1 := by
    intro h
    have hBA : ρ B = ρ A := by
      rw [hAm]
      exact Units.ext (by rw [Units.val_neg, Units.val_one]; exact h)
    have hBA' : B = A := hρ hBA
    apply hab
    have : b' = a' := Subtype.ext (by simpa [A, B] using congrArg Subtype.val hBA')
    rw [this]
  have hcomm : ∀ U : C, U * B = B * U →
      ((ρ U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * s =
        s * ((ρ U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro U hU
    change ((ρ U : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ B : GL _ _) =
      ((ρ B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ U : GL _ _)
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hU]
  have hXB : X * B = B * X := Subtype.ext (by
    change (x' : GL (Fin 3) K) * b' = b' * x'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hx'b])
  have hYB : Y * B = B * Y := Subtype.ext (by
    change (y' : GL (Fin 3) K) * b' = b' * y'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hy'b])
  have hXY := fin_two_commute_of_commute_involution h2 hs hs1 hsn (hcomm X hXB) (hcomm Y hYB)
  have hρXY : ρ (X * Y) = ρ (Y * X) := by
    rw [map_mul, map_mul]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hXY])
  have hXY' := congrArg Subtype.val (hρ hρXY)
  have hxy : x' * y' = y' * x' := Subtype.ext hXY'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem false_of_psu34_K (h2 : (2 : K) ≠ 0) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {K' : Type} [Field K'] [Finite K']
    (hK : Nat.card K' = (2 ^ 2) ^ 2)
    (e : (H ⧸ Subgroup.center H) ≃* StatedProj (StatedSU 3 (2 ^ 2) K')) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K' 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two
    (by rw [hK, ← pow_mul])
  obtain ⟨a, b, x, y, ha2, hb2, ha1, hb1, hab, habc, hxa, hxb, hya, hyb, hxy⟩ :=
    exists_four_group_witness_psu34 hK
  apply hxy
  have := commute_of_centralize_four_group_K h2 hdet hZ (a := e.symm a) (b := e.symm b)
    (x := e.symm x) (y := e.symm y) (by rw [← map_pow, ha2, map_one])
    (by rw [← map_pow, hb2, map_one]) (fun h => ha1 (e.symm.injective (by rw [h, map_one])))
    (fun h => hb1 (e.symm.injective (by rw [h, map_one]))) (fun h => hab (e.symm.injective h))
    (by rw [← map_mul, ← map_mul, habc]) (by rw [← map_mul, ← map_mul, hxa])
    (by rw [← map_mul, ← map_mul, hxb]) (by rw [← map_mul, ← map_mul, hya])
    (by rw [← map_mul, ← map_mul, hyb])
  apply e.symm.injective
  rw [map_mul, map_mul, this]

end CFSG.Quasithin.A312U3
