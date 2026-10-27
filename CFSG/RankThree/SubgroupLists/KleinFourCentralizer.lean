module

public import CFSG.RankThree.SubgroupLists.QuasisimpleRankTwo
public import CFSG.RankThree.SubgroupLists.CentralThreeLift

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K]

theorem fin_two_commute_of_commute_involution (h2 : (2 : K) ≠ 0)
    {s x y : Matrix (Fin 2) (Fin 2) K}
    (hs : s * s = 1) (hs1 : s ≠ 1) (hsn : s ≠ -1) (hx : x * s = s * x) (hy : y * s = s * y) :
    x * y = y * x := by
  have key : ∀ z : Matrix (Fin 2) (Fin 2) K, z * s = s * z →
      ∃ μ ν : K, z = μ • 1 + ν • s := by
    intro z hz
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : K, s = !![a, b; c, d] := ⟨_, _, _, _, s.eta_fin_two⟩
    obtain ⟨z₁, z₂, z₃, z₄, rfl⟩ : ∃ z₁ z₂ z₃ z₄ : K, z = !![z₁, z₂; z₃, z₄] :=
      ⟨_, _, _, _, z.eta_fin_two⟩
    have hn : ∀ p q r t : K, -!![p, q; r, t] = !![-p, -q; -r, -t] := by
      intro p q r t
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    simp only [Matrix.mul_fin_two, Matrix.one_fin_two, hn] at hs hz hs1 hsn
    rw [← Matrix.ext_iff] at hs
    simp [Fin.forall_fin_two] at hs hz hs1 hsn
    obtain ⟨⟨s00, s01⟩, s10, s11⟩ := hs
    obtain ⟨⟨c00, c01⟩, c10, -⟩ := hz
    have hsq : ∀ w : K, w * w = 1 → w = 1 ∨ w = -1 := fun w hw => mul_self_eq_one_iff.mp hw
    have had : a + d = 0 := by
      by_contra hne
      have hb : b = 0 := by
        have : b * (a + d) = 0 := by linear_combination s01
        exact (mul_eq_zero.mp this).resolve_right hne
      have hc : c = 0 := by
        have : c * (a + d) = 0 := by linear_combination s10
        exact (mul_eq_zero.mp this).resolve_right hne
      subst hb hc
      rcases hsq a (by linear_combination s00) with ha | ha <;>
        rcases hsq d (by linear_combination s11) with hd | hd
      · exact hs1 ha rfl rfl hd
      · exact hne (by rw [ha, hd]; ring)
      · exact hne (by rw [ha, hd]; ring)
      · exact hsn ha rfl rfl hd
    have hd : d = -a := by linear_combination had
    subst hd
    have e1 : b * (z₁ - z₄) = 2 * a * z₂ := by linear_combination c01
    have e2 : c * (z₁ - z₄) = 2 * a * z₃ := by linear_combination -c10
    have e3 : c * z₂ = b * z₃ := by linear_combination c00
    obtain ⟨ν, hν1, hν2, hν3⟩ : ∃ ν : K, z₁ - z₄ = ν * (2 * a) ∧ z₂ = ν * b ∧ z₃ = ν * c := by
      by_cases ha0 : a = 0
      · subst ha0
        have hbc : b * c = 1 := by linear_combination s00
        have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hbc
        have hc0 : c ≠ 0 := right_ne_zero_of_mul_eq_one hbc
        refine ⟨z₂ / b, ?_, by field_simp, ?_⟩
        · simp only [mul_zero]
          have : b * (z₁ - z₄) = 0 := by linear_combination e1
          have := (mul_eq_zero.mp this).resolve_left hb0
          linear_combination this
        · field_simp
          linear_combination -e3
      · have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha0
        refine ⟨(z₁ - z₄) / (2 * a), by field_simp, ?_, ?_⟩
        · field_simp
          linear_combination -e1
        · field_simp
          linear_combination -e2
    refine ⟨(z₁ + z₄) / 2, ν, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    · linear_combination hν1
    · linear_combination hν2
    · linear_combination hν3
    · linear_combination -hν1
  obtain ⟨μ₁, ν₁, rfl⟩ := key x hx
  obtain ⟨μ₂, ν₂, rfl⟩ := key y hy
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, hs]
  module

theorem commute_of_centralize_four_group {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) {a b x y : H ⧸ Subgroup.center H}
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (habc : a * b = b * a) (hxa : x * a = a * x) (hxb : x * b = b * x) (hya : y * a = a * y)
    (hyb : y * b = b * y) : x * y = y * x := by
  classical
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
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
  have hCc : ∀ g ∈ C, g * (a' : GL (Fin 3) (ZMod p)) = a' * g := by
    rintro _ ⟨g, hg, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact congrArg Subtype.val this
  have hCdet : ∀ g ∈ C, (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
    rintro _ ⟨g, -, rfl⟩
    exact hdet _ g.2
  have ha'1 : (a' : GL (Fin 3) (ZMod p)) ≠ 1 := fun h =>
    ha1 (by rw [show a' = 1 from Subtype.ext h, QuotientGroup.mk_one])
  obtain ⟨ρ, hρ, hρa⟩ := exists_injective_gl2_of_commute h2
    (by rw [← Subgroup.coe_mul, ← sq, ha'2, Subgroup.coe_one]) ha'1 (hdet _ a'.2) C hCc hCdet
  have hmem : ∀ g : H, g * a' = a' * g → (g : GL (Fin 3) (ZMod p)) ∈ C := fun g hg =>
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg, rfl⟩
  set A : C := ⟨a', hmem a' rfl⟩
  set B : C := ⟨b', hmem b' hb'a⟩
  set X : C := ⟨x', hmem x' hx'a⟩
  set Y : C := ⟨y', hmem y' hy'a⟩
  have hAm : ρ A = -1 := hρa A rfl
  set s := ((ρ B : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
  have hBB : B * B = 1 := Subtype.ext (by
    change ((b' : GL (Fin 3) (ZMod p))) * b' = 1
    rw [← Subgroup.coe_mul, ← sq, hb'2, Subgroup.coe_one])
  have hs : s * s = 1 := by
    change ((ρ B : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * (ρ B : GL _ _) = 1
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
      ((ρ U : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * s =
        s * ((ρ U : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    intro U hU
    change ((ρ U : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * (ρ B : GL _ _) =
      ((ρ B : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) * (ρ U : GL _ _)
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hU]
  have hXB : X * B = B * X := Subtype.ext (by
    change (x' : GL (Fin 3) (ZMod p)) * b' = b' * x'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hx'b])
  have hYB : Y * B = B * Y := Subtype.ext (by
    change (y' : GL (Fin 3) (ZMod p)) * b' = b' * y'
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hy'b])
  have hXY := fin_two_commute_of_commute_involution h2 hs hs1 hsn (hcomm X hXB) (hcomm Y hYB)
  have hρXY : ρ (X * Y) = ρ (Y * X) := by
    rw [map_mul, map_mul]
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hXY])
  have hXY' := congrArg Subtype.val (hρ hρXY)
  have hxy : x' * y' = y' * x' := Subtype.ext hXY'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

end CFSG.RankThree.SubgroupLists
