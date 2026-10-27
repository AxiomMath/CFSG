module

public import CFSG.Quasithin.MS93.S38EFFHyp
public import CFSG.Quasithin.MS93.S32Types
public import CFSG.Quasithin.MS93.SkTypes
public import CFSG.Quasithin.MS93.S6Bridge
public import CFSG.Quasithin.MS93.MSPBasic

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

section Orders

theorem odd_two_pow_sub_one' {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have he : Even (2 ^ m) := Nat.even_pow.2 ⟨even_two, by omega⟩
  obtain ⟨r, hr⟩ := he
  exact ⟨r - 1, by omega⟩

theorem two_pow_mul_odd_eq' {x y u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ x * u = 2 ^ y * v) : x = y ∧ u = v := by
  have key : ∀ {x y u v : ℕ}, Odd u → Odd v → 2 ^ x * u = 2 ^ y * v → x ≤ y → x = y ∧ u = v := by
    intro x y u v hu _ h hxy
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [pow_add, mul_assoc] at h
    have h' : u = 2 ^ d * v := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [h']
    · exfalso
      rw [h'] at hu
      have : Even (2 ^ d * v) := (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right v
      exact Nat.not_even_iff_odd.2 hu this
  rcases le_total x y with hxy | hyx
  · exact key hu hv h hxy
  · obtain ⟨h1, h2⟩ := key hv hu h.symm hyx
    exact ⟨h1.symm, h2.symm⟩

theorem ordA_two_ne_ordBC_two {n k : ℕ} (hk : 2 ≤ k) : ordA 2 (2 ^ n) ≠ ordBC 2 (2 ^ k) := by
  intro h
  have hg : Nat.gcd 3 (2 ^ n - 1) ∣ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.mul_left (Dvd.dvd.mul_right
      (by simpa using Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2) _) _)
  have hc : Nat.gcd 3 (2 ^ n - 1) = 1 ∨ Nat.gcd 3 (2 ^ n - 1) = 3 := by
    have := Nat.gcd_dvd_left 3 (2 ^ n - 1)
    have h3 : (3 : ℕ).Prime := Nat.prime_three
    rcases (Nat.dvd_prime h3).1 this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  apply card_sl3_ne_card_sp4 (n := n) hk hc
  rw [ordA_two_eq, ordBC_two_two_pow (by omega)] at h
  rw [← h, Nat.mul_div_cancel' hg]
  ring

theorem ordG2_ne_ordBC_two {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ordG2 (2 ^ n) ≠ ordBC 2 (2 ^ k) := by
  intro h
  rw [ordBC_two_two_pow hk] at h
  unfold ordG2 at h
  simp only [← pow_mul] at h
  have hA : Odd ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) :=
    (odd_two_pow_sub_one' (by omega)).mul (odd_two_pow_sub_one' (by omega))
  have hB : Odd ((2 ^ (k * 2) - 1) * (2 ^ (k * 4) - 1)) :=
    (odd_two_pow_sub_one' (by omega)).mul (odd_two_pow_sub_one' (by omega))
  have h' : 2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) =
      2 ^ (k * 4) * ((2 ^ (k * 2) - 1) * (2 ^ (k * 4) - 1)) := by
    rw [← h]
    ring
  obtain ⟨hnk, huv⟩ := two_pow_mul_odd_eq' hA hB h'
  obtain ⟨m, rfl, rfl⟩ : ∃ m, n = 2 * m ∧ k = 3 * m := ⟨n / 2, by omega, by omega⟩
  have e1 : 2 * m * 6 = 3 * m * 4 := by ring
  rw [e1] at huv
  have hW : 0 < 2 ^ (3 * m * 4) - 1 := by
    have : 2 ≤ 2 ^ (3 * m * 4) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (3 * m * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have huv' : 2 ^ (2 * m * 2) - 1 = 2 ^ (3 * m * 2) - 1 := by
    apply Nat.eq_of_mul_eq_mul_left hW
    rw [mul_comm (2 ^ (3 * m * 4) - 1) (2 ^ (3 * m * 2) - 1), ← huv]
  have hlt : 2 ^ (2 * m * 2) < 2 ^ (3 * m * 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ 2 ^ (2 * m * 2) := Nat.one_le_two_pow
  omega

theorem eq_of_ordBC_two_eq {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (h : ordBC 2 (2 ^ n) = ordBC 2 (2 ^ k)) : n = k := by
  obtain ⟨r, hr, hrn⟩ := two_part_ordBC_two hn
  obtain ⟨s, hs, hsk⟩ := two_part_ordBC_two hk
  have := (two_pow_mul_odd_eq' hr hs (hrn.symm.trans (h.trans hsk))).1
  omega

end Orders

section Lstar

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_ne_one_sp4 (F : Type) [Field F] : ∃ g : ↥(StatedSp 2 F), g ≠ 1 := by
  set x : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1 with hx
  have hx0 : x ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp [hx] at this
  refine ⟨MSP.transv x 1, fun h1 => ?_⟩
  have := MSP.transv_injective hx0 (h1.trans (MSP.transv_zero x).symm)
  exact one_ne_zero this

theorem card_lstar_of_sp4 (h : PUHyp M T L) {F : Type} [Field F] [Finite F] {k : ℕ}
    (hF : Nat.card F = 2 ^ k) (hk : 2 ≤ k) {α : ↥L →* ↥(StatedSp 2 F)}
    (hα : Function.Surjective α) (hO : CFSG.pCore 2 ↥L ≤ α.ker) :
    Nat.card (S32.Lstar L) = ordBC 2 (2 ^ k) := by
  set αbar : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(StatedSp 2 F) := QuotientGroup.lift _ α hO
  have hαbar : Function.Surjective αbar := by
    intro x
    obtain ⟨y, rfl⟩ := hα x
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hne : ∃ y, αbar y ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne_one_sp4 F
    obtain ⟨y, hy⟩ := hαbar g
    exact ⟨y, hy ▸ hg⟩
  have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple hαbar
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple hne)
  rw [Nat.card_congr e.toEquiv]
  exact card_quot_of_equiv_statedSp hF hk (MulEquiv.refl _)

theorem card_lstar_of_alt (h : PUHyp M T L) {α : ↥L →* alternatingGroup (Fin 6)}
    (hα : Function.Surjective α) (hO : CFSG.pCore 2 ↥L ≤ α.ker) :
    Nat.card (S32.Lstar L) = 360 := by
  set αbar : ↥L ⧸ CFSG.pCore 2 ↥L →* alternatingGroup (Fin 6) := QuotientGroup.lift _ α hO
  have hαbar : Function.Surjective αbar := by
    intro x
    obtain ⟨y, rfl⟩ := hα x
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hne : ∃ y, αbar y ≠ 1 := by
    obtain ⟨y, hy⟩ := hαbar ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    refine ⟨y, fun h1 => ?_⟩
    rw [h1] at hy
    have := congrArg (fun σ : alternatingGroup (Fin 6) => (σ : Equiv.Perm (Fin 6)) 0) hy
    exact absurd this (by decide)
  have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple hαbar
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple hne)
  rw [Nat.card_congr e.toEquiv]
  exact card_quot_of_equiv_alt6 (MulEquiv.refl _)

theorem card_lstar_of_isSp4DerSec (h : PUHyp M T L) {k : ℕ}
    (hsp : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k) :
    (k = 1 ∧ Nat.card (S32.Lstar L) = 360) ∨
      (2 ≤ k ∧ Nat.card (S32.Lstar L) = ordBC 2 (2 ^ k)) := by
  rcases hsp with ⟨hk1, N, hN⟩ | ⟨hk2, F, iF, fF, α, hcard, hαs, hnat⟩
  · refine Or.inl ⟨hk1, ?_⟩
    obtain ⟨hLU, α₀, hα₀, -, β₀, hβ₀, -, hβ₀e⟩ := hN
    refine card_lstar_of_alt h hα₀ fun y hy => ?_
    rw [MonoidHom.mem_ker]
    have hfix : ∀ u : ↥(Uq M T L), ((y : G) * u * (y : G)⁻¹) = u := fun u =>
      commute_of_mem_pCore h.L_le h.le_normalizer hy (h.Uq_le_Xq u.2)
    have hmat : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 2,
        (((S6B.thetaTwo (α₀ y : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
          GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ w =
          w := by
      intro w
      obtain ⟨m, hm⟩ := S6B.crdHom_bijective.2 (Multiplicative.ofAdd w)
      obtain ⟨u, hu⟩ := hβ₀ m
      have h1 := S6B.crdHom_conj hβ₀e y u u (hfix u).symm
      rw [hu, hm] at h1
      exact h1.symm
    have hθ : S6B.thetaTwo (α₀ y : Equiv.Perm (Fin 6)) = 1 := by
      apply Subtype.ext
      apply Units.ext
      refine Matrix.ext_iff_mulVec.mpr fun v => ?_
      rw [hmat v]
      simp
    have hσ : (α₀ y : Equiv.Perm (Fin 6)) = 1 := by
      rw [← map_one S6B.thetaTwo] at hθ
      exact S6B.thetaTwo.injective hθ
    exact Subtype.ext hσ
  · refine Or.inr ⟨hk2, ?_⟩
    have : Finite F := Finite.of_fintype F
    refine card_lstar_of_sp4 h (by rw [Nat.card_eq_fintype_card, hcard]) hk2 hαs fun y hy => ?_
    rw [MonoidHom.mem_ker]
    exact eq_one_of_isSumOfNaturalModulesVia hnat
      (fun v hv => commute_of_mem_pCore h.L_le h.le_normalizer hy (h.Uq_le_Xq hv))

theorem card_quot_center_imL {F : Type} [CommGroup F] {ρ : ↥M →* MulAut F}
    (hρ : S38E.IsIrrRep L ρ) (h : PUHyp M T L) :
    Nat.card (↥(S38E.IsIrrRep.imL L ρ) ⧸ Subgroup.center ↥(S38E.IsIrrRep.imL L ρ)) =
      Nat.card (S32.Lstar L) :=
  (Nat.card_congr (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple
    (hρ.quotHom_surjective h) (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      h.quasisimple (hρ.quotHom_ne_one h))).toEquiv).symm

end Lstar

end CFSG.Quasithin.MS93.S36E
