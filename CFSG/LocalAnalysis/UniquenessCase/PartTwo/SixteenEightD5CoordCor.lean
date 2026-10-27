module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Coord
public import CFSG.Quasithin.Background.B1Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private theorem s16e_d5_coord_pow_three (x : Multiplicative (Fin 4 → ZMod 3)) : x ^ 3 = 1 := by
  refine Multiplicative.ext (funext fun i => ?_)
  rw [toAdd_pow]
  show (3 : ℕ) • (x.toAdd i) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private def s16e_d5_fixSub (S : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | ∀ z ∈ S, g z = z}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g h hg hh z hz
    rw [MulAut.mul_apply, hh z hz, hg z hz]
  inv_mem' := by
    intro g hg z hz
    refine g.injective ?_
    simpa [hg z hz]

private theorem s16e_d5_coord_off {κ : ↥(Subgroup.centralizer (L : Set (MulAut W))) →*
      Multiplicative (Fin 4 → ZMod 3)}
    (hinj : Function.Injective κ)
    (hκ0 : ∀ (g : ↥(Subgroup.centralizer (L : Set (MulAut W)))) (i : Fin 4),
      Multiplicative.toAdd (κ g) i = 0 ↔ ∀ z ∈ Z i, (g : MulAut W) z = z)
    {a : MulAut W} (ha : a ∈ Subgroup.centralizer (L : Set (MulAut W))) {i : Fin 4}
    (hai : ∀ k, k ≠ i → ∀ z ∈ Z k, a z = z) (ha1 : a ≠ 1) :
    (∀ k, k ≠ i → Multiplicative.toAdd (κ ⟨a, ha⟩) k = 0) ∧
      Multiplicative.toAdd (κ ⟨a, ha⟩) i ≠ 0 := by
  have h0 : ∀ k, k ≠ i → Multiplicative.toAdd (κ ⟨a, ha⟩) k = 0 := by
    intro k hk
    exact (hκ0 ⟨a, ha⟩ k).2 (hai k hk)
  refine ⟨h0, ?_⟩
  intro hi
  have hzero : κ ⟨a, ha⟩ = 1 := by
    refine Multiplicative.ext (funext fun k => ?_)
    by_cases hk : k = i
    · subst hk
      simpa using hi
    · simpa using h0 k hk
  have hx1 : (⟨a, ha⟩ : ↥(Subgroup.centralizer (L : Set (MulAut W)))) = 1 :=
    hinj (by rw [hzero, map_one])
  exact ha1 (by simpa using congrArg Subtype.val hx1)

theorem s16e_d5_cent_pow_three (hfr : s16e_d5_Frame L K Z) {g : MulAut W}
    (hg : g ∈ Subgroup.centralizer (L : Set (MulAut W))) : g ^ 3 = 1 := by
  obtain ⟨κ, hinj, -, -⟩ := s16e_d5_coord hfr
  have h3 : (⟨g, hg⟩ : ↥(Subgroup.centralizer (L : Set (MulAut W)))) ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact s16e_d5_coord_pow_three (κ ⟨g, hg⟩)
  simpa using congrArg Subtype.val h3

theorem s16e_d5_cent_comm (hfr : s16e_d5_Frame L K Z) {g h : MulAut W}
    (hg : g ∈ Subgroup.centralizer (L : Set (MulAut W)))
    (hh : h ∈ Subgroup.centralizer (L : Set (MulAut W))) : g * h = h * g := by
  obtain ⟨κ, hinj, -, -⟩ := s16e_d5_coord hfr
  have hgh : (⟨g, hg⟩ : ↥(Subgroup.centralizer (L : Set (MulAut W)))) * ⟨h, hh⟩ =
      ⟨h, hh⟩ * ⟨g, hg⟩ := by
    apply hinj
    rw [map_mul, map_mul]
    exact mul_comm _ _
  simpa using congrArg Subtype.val hgh

theorem s16e_d5_card_cent_dvd (hfr : s16e_d5_Frame L K Z) :
    Nat.card ↥(Subgroup.centralizer (L : Set (MulAut W))) ∣ 81 := by
  obtain ⟨κ, hinj, -, -⟩ := s16e_d5_coord hfr
  have hdvd := Subgroup.card_dvd_of_injective κ hinj
  have h81 : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 81 := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card]
  rwa [h81] at hdvd

theorem s16e_d5_L_le_cent (hfr : s16e_d5_Frame L K Z) :
    L ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact hfr.comm_L y hy x hx

theorem s16e_d5_cent_stable (hfr : s16e_d5_Frame L K Z) {g : MulAut W}
    (hg : g ∈ Subgroup.centralizer (L : Set (MulAut W))) (i : Fin 4) {z : W} (hz : z ∈ Z i) :
    g z ∈ Z i := by
  have hzK : z ∈ fixV (K i) := by rwa [← hfr.Z_eq i]
  rw [hfr.Z_eq i]
  refine mem_fixV.mpr fun k hk => ?_
  have hkg : k * g = g * k :=
    (Subgroup.mem_centralizer_iff.mp hg) k (hfr.K_le i hk)
  calc k (g z) = (k * g) z := rfl
    _ = (g * k) z := by rw [hkg]
    _ = g (k z) := rfl
    _ = g z := by rw [(mem_fixV.mp hzK) k hk]

theorem s16e_d5_cent_fix (hfr : s16e_d5_Frame L K Z) {a : MulAut W}
    (ha : a ∈ Subgroup.centralizer (L : Set (MulAut W))) {i : Fin 4}
    (hai : ∀ k, k ≠ i → ∀ z ∈ Z k, a z = z) (ha1 : a ≠ 1) {z : W} (hz : z ∈ Z i) (haz : a z = z) :
    z = 1 := by
  obtain ⟨κ, hinj, hκ0, hκ1⟩ := s16e_d5_coord hfr
  exact hκ1 ⟨a, ha⟩ i (s16e_d5_coord_off (a := a) hinj hκ0 ha hai ha1).2 z hz haz

theorem s16e_d5_orderOf_cent (hfr : s16e_d5_Frame L K Z) {a : MulAut W}
    (ha : a ∈ Subgroup.centralizer (L : Set (MulAut W))) (ha1 : a ≠ 1) : orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (s16e_d5_cent_pow_three hfr ha) ha1

theorem s16e_d5_commSub_zpowers (hfr : s16e_d5_Frame L K Z) {a : MulAut W}
    (ha : a ∈ Subgroup.centralizer (L : Set (MulAut W))) {i : Fin 4}
    (hai : ∀ k, k ≠ i → ∀ z ∈ Z k, a z = z) (ha1 : a ≠ 1) :
    commSub ⊤ (Subgroup.zpowers a) = Z i := by
  let Y : Subgroup (MulAut W) := Subgroup.zpowers a
  have hleC : Y ≤ Subgroup.centralizer (L : Set (MulAut W)) := Subgroup.zpowers_le.mpr ha
  have hYcard : Nat.card ↥Y = 3 := by
    rw [Nat.card_zpowers, s16e_d5_orderOf_cent hfr ha ha1]
  have hYodd : Odd (Nat.card ↥Y) := ⟨1, by rw [hYcard]; norm_num⟩
  have hfix : ∀ k, k ≠ i → ∀ y ∈ Y, ∀ z ∈ Z k, y z = z := by
    intro k hk y hy
    exact (Subgroup.zpowers_le.mpr (show a ∈ s16e_d5_fixSub (Z k) from hai k hk)) hy
  have hstab : ∀ y ∈ Y, ∀ z ∈ Z i, y z ∈ Z i := by
    intro y hy z hz
    exact s16e_d5_cent_stable hfr (hleC hy) i hz
  have hcomm_le : commSub ⊤ Y ≤ Z i := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨y, hy, w, -, rfl⟩
    have hw : w ∈ ⨆ k, Z k := by rw [hfr.Z_top]; exact Subgroup.mem_top w
    refine Subgroup.iSup_induction Z (C := fun w => y w * w⁻¹ ∈ Z i) hw ?_ ?_ ?_
    · intro k z hz
      by_cases hk : k = i
      · rw [hk] at hz
        exact (Z i).mul_mem (hstab y hy z hz) ((Z i).inv_mem hz)
      · rw [hfix k hk y hy z hz]
        simpa using (Z i).one_mem
    · simpa using (Z i).one_mem
    · intro x₁ x₂ hx₁ hx₂
      have heq : y (x₁ * x₂) * (x₁ * x₂)⁻¹ = (y x₁ * x₁⁻¹) * (y x₂ * x₂⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [heq]
      exact (Z i).mul_mem hx₁ hx₂
  have hM : ∀ y ∈ Y, ∀ m ∈ Z i, y m ∈ Z i := hstab
  have hdecomp := (B1.coprime_decomp hfr.sq_W hYodd (M := Z i) hM).1
  have hinf : Z i ⊓ fixV Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzZ, hzfix⟩ := Subgroup.mem_inf.mp hz
    exact s16e_d5_cent_fix hfr ha hai ha1 hzZ ((mem_fixV.mp hzfix) a (Subgroup.mem_zpowers a))
  rw [hinf, bot_sup_eq] at hdecomp
  refine le_antisymm hcomm_le ?_
  rw [← hdecomp]
  exact commSub_mono le_top le_rfl

theorem s16e_d5_line (hfr : s16e_d5_Frame L K Z) {a b : MulAut W}
    (ha : a ∈ Subgroup.centralizer (L : Set (MulAut W)))
    (hb : b ∈ Subgroup.centralizer (L : Set (MulAut W))) {i : Fin 4}
    (hai : ∀ k, k ≠ i → ∀ z ∈ Z k, a z = z) (hbi : ∀ k, k ≠ i → ∀ z ∈ Z k, b z = z)
    (ha1 : a ≠ 1) : b ∈ Subgroup.zpowers a := by
  obtain ⟨κ, hinj, hκ0, hκ1⟩ := s16e_d5_coord hfr
  have ha0 : ∀ k, k ≠ i → Multiplicative.toAdd (κ ⟨a, ha⟩) k = 0 :=
    (s16e_d5_coord_off (a := a) hinj hκ0 ha hai ha1).1
  have hai_nz : Multiplicative.toAdd (κ ⟨a, ha⟩) i ≠ 0 :=
    (s16e_d5_coord_off (a := a) hinj hκ0 ha hai ha1).2
  have hb0 : ∀ k, k ≠ i → Multiplicative.toAdd (κ ⟨b, hb⟩) k = 0 := by
    intro k hk
    exact (hκ0 ⟨b, hb⟩ k).2 (hbi k hk)
  set u : ZMod 3 := Multiplicative.toAdd (κ ⟨a, ha⟩) i with hu
  set v : ZMod 3 := Multiplicative.toAdd (κ ⟨b, hb⟩) i with hv
  have hu0 : u ≠ 0 := hai_nz
  set n : ℕ := (v * u⁻¹).val with hn
  have hnv : (n : ZMod 3) * u = v := by
    rw [hn, ZMod.natCast_zmod_val]
    rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  have hxy : (⟨a, ha⟩ : ↥(Subgroup.centralizer (L : Set (MulAut W)))) ^ n = ⟨b, hb⟩ := by
    apply hinj
    refine Multiplicative.ext (funext fun k => ?_)
    rw [map_pow, toAdd_pow]
    by_cases hk : k = i
    · rw [hk]
      show n • (Multiplicative.toAdd (κ ⟨a, ha⟩) i) =
        Multiplicative.toAdd (κ ⟨b, hb⟩) i
      rw [← hu, ← hv, nsmul_eq_mul, hnv]
    · rw [hb0 k hk]
      simp [ha0 k hk]
  have hab : a ^ n = b := by simpa using congrArg Subtype.val hxy
  rw [← hab]
  exact Subgroup.npow_mem_zpowers a n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
