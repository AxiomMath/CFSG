module

public import CFSG.Quasithin.Vol2.Ch11SecAKA7
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.KGNatPointT

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat

namespace EK1

variable {W : Type*} [CommGroup W]

theorem conj_mem_pCoreOf_of_comm {X : Subgroup (MulAut W)} {h : MulAut W}
    (hc : ∀ k ∈ X, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 X) :
    ∀ r ∈ pCoreOf 2 X, h * r * h⁻¹ ∈ pCoreOf 2 X := by
  intro r hr
  have h1 := (pCoreOf 2 X).mul_mem (hc r (Subgroup.map_subtype_le _ hr)) hr
  rwa [inv_mul_cancel_right] at h1

theorem mem_stabW_bot (h : MulAut W) : h ∈ SecA.stabW (⊥ : Subgroup W) :=
  SecA.mem_stabW.mpr fun z => ⟨fun hz => bot_maps h z hz, fun hz => by
    have h1 := bot_maps h⁻¹ _ hz
    rwa [MulAut.inv_apply_self] at h1⟩

theorem mem_stabW_of_comm [Finite W] {H : Subgroup (MulAut W)} {U : Subgroup W}
    (hfix : SecA.RadicalFixes H ⊥ U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ (⊥ : Subgroup W))
    {h : MulAut W} (hc : ∀ k ∈ perfectCore (H ⊓ SecA.stabW U),
      h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ SecA.stabW U))) :
    h ∈ SecA.stabW U :=
  KA.mem_stabW_of_conj hfix hpt (mem_stabW_bot h) (conj_mem_pCoreOf_of_comm hc)

theorem eq_one_of_sq {F : Type*} [Field F] [CharP F 2] {r : F} (h : r ^ 2 = 1) : r = 1 := by
  rcases sq_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

theorem eq_one_of_mem_center {F : Type*} [Field F] [CharP F 2]
    {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  rw [Fintype.card_fin] at hr
  rw [eq_one_of_sq hr, map_one] at hrA
  exact Subtype.ext hrA.symm

theorem exists_pow_eq_one_of_levi {G : Type*} [Group G] {L : Subgroup G} {F : Type*} [Field F]
    [CharP F 2] (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) {h : G}
    (hh : h ∈ L) (hc : ∀ k ∈ L, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 L) : ∃ a : ℕ, h ^ 2 ^ a = 1 := by
  set x : ↥L := ⟨h, hh⟩ with hxdef
  have hcen : e (x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro C
    obtain ⟨y, rfl⟩ := e.surjective C
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥L :=
      (KA.mem_pCoreOf_iff' L (x * y * x⁻¹ * y⁻¹)).mp (hc y y.2)
    have h2 := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) _).mpr h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    rw [← map_mul, ← map_mul, h2]
  have hx1 : (x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := (MulEquiv.map_eq_one_iff e).mp
    (eq_one_of_mem_center hcen)
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    ⟨x, (QuotientGroup.eq_one_iff _).mp hx1⟩
  refine ⟨a, ?_⟩
  have h1 := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) ha
  simpa [hxdef] using h1

theorem eq_one_of_pow_coprime {K : Type*} [Field K] [Finite K] {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (hm0 : m ≠ 0) (hmc : Nat.Coprime m (2 ^ n - 1)) {x : K}
    (hx : x ^ m = 1) : x = 1 := by
  have := Fintype.ofFinite K
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hx
    exact zero_ne_one hx
  have h1 : x ^ (2 ^ n - 1) = 1 := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one x hx0
  exact (pow_eq_one_iff_of_coprime hmc).mp ⟨hx, h1⟩

theorem eq_one_of_odd_of_two_pow {G : Type*} [Group G] {x : G} {m a : ℕ} (hm : Odd m)
    (h1 : x ^ m = 1) (h2 : x ^ 2 ^ a = 1) : x = 1 :=
  (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm))).mp
    ⟨h1, h2⟩

end EK1

end CFSG.Quasithin.Vol2.Ch11.SecE
