module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofStatements
public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
import CFSG.RankThree.PartTwo.Sec21.Item228InspProofRefl
import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)

@[expose] def Insp228SL3NonComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Fam228SL3 A φ X → Item228OneConcl A ψ X → Insp228NonComm A φ ψ

namespace Item228InspProof

variable {G : Type} [Group G]

theorem card_le_nine_of_le_SL3 {X H : Subgroup G} {m : ℕ} (e : X ≃* SL3 m) (hHX : H ≤ X)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hexp : ∀ x ∈ H, x ^ 3 = 1) :
    Nat.card H ≤ 9 := by
  set F := GaloisField 2 m
  set ι : X →* GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL.comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
    exact h'
  set E : Subgroup (GL (Fin 3) F) := (H.subgroupOf X).map ι with hEdef
  have hcard : Nat.card E = Nat.card H := by
    rw [hEdef, Subgroup.card_map_of_injective hι]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv
  have : Finite E := Finite.of_injective (fun x : E => (x : GL (Fin 3) F)) Subtype.val_injective
  have h3 : ((3 : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F 2]
    norm_num
  have hb := CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_gl Nat.prime_three h3 (by simp) E
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ hx _ hy))
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hexp _ hx)
      rw [this, map_one])
    (by
      rintro _ ⟨x, -, rfl⟩
      exact (e x).2)
  rw [hcard] at hb
  simpa using hb

theorem three_dvd_two_pow_sub_one_of_even {m : ℕ} (hme : Even m) : 3 ∣ 2 ^ m - 1 := by
  obtain ⟨k, rfl⟩ := hme
  rw [← two_mul, pow_mul]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 k

theorem exists_central_SL3 {m : ℕ} (hm0 : 0 < m) (hme : Even m) :
    ∃ z : SL3 m, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ g : SL3 m, g * z = z * g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField 2 m
  have hF : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact three_dvd_two_pow_sub_one_of_even hme
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    norm_num at hu
  set ω : F := (u : F) with hω
  have hω3 : ω ^ 3 = 1 := by rw [hω, ← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hω1 : ω ≠ 1 := fun h => hu1 (Units.ext h)
  have hmem : ∃ r : F, r ^ Fintype.card (Fin 3) = 1 ∧ Matrix.scalar (Fin 3) r =
      Matrix.scalar (Fin 3) ω := ⟨ω, by simpa using hω3, rfl⟩
  have hdet : (Matrix.scalar (Fin 3) ω).det = 1 := by simp [hω3]
  set z : SL3 m := ⟨Matrix.scalar (Fin 3) ω, hdet⟩ with hz
  have hzc : z ∈ Subgroup.center (SL3 m) := Matrix.SpecialLinearGroup.mem_center_iff.mpr hmem
  refine ⟨z, ?_, ?_, fun g => ((Subgroup.mem_center_iff.mp hzc) g)⟩
  · intro h
    have h' := congrArg (fun g : SL3 m => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [hz] at h'
    exact hω1 h'
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow]
    simp [hz, Matrix.diagonal_pow, Pi.pow_def, hω3]

theorem mulComm_ne_of_SL3 [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3) (hK : KOfWellDefined A)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : ψ ≠ φ) {X : Subgroup G}
    (hKX : kOf A φ ≤ X) (hJX : kOf A ψ ≤ X) {m : ℕ} (hm0 : 0 < m) (hme : Even m)
    (e : X ≃* SL3 m) : ψ * φ ≠ φ * ψ := by
  intro hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hne' : φ ≠ ψ := fun h => hne h.symm
  have hφr := hφ.1
  have hψr := hψ.1
  have hφφ := apply_apply_of_orderOf_eq_two hφr.1
  have hψψ := apply_apply_of_orderOf_eq_two hψr.1
  have h₁ : commOf ψ ≤ fixedSubgroupOf φ :=
    commOf_le_fixedSubgroupOf_of_commute hAc hA3 hφr hψr hc hne'
  have h₂ : commOf φ ≤ fixedSubgroupOf ψ :=
    commOf_le_fixedSubgroupOf_of_commute hAc hA3 hψr hφr hc.symm hne
  have hinf : commOf φ ⊓ commOf ψ = ⊥ := inf_commOf_eq_bot_of_commute hAc hA3 hφr hψr hc hne'
  obtain ⟨z, hz1, hz3, hzc⟩ := exists_central_SL3 hm0 hme
  set z₀ : G := ((e.symm z : X) : G) with hz₀def
  have hz₀X : z₀ ∈ X := (e.symm z).2
  have hz₀c : ∀ x ∈ X, x * z₀ = z₀ * x := by
    intro x hx
    have h := congrArg (fun g => ((e.symm g : X) : G)) (hzc (e ⟨x, hx⟩))
    simpa [map_mul] using h
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    apply hz1
    have h' : e.symm z = 1 := Subtype.ext h
    rw [← map_one e.symm] at h'
    exact e.symm.injective h'
  have hz₀3 : z₀ ^ 3 = 1 := by
    rw [hz₀def, ← Subgroup.coe_pow, ← map_pow, hz3, map_one, Subgroup.coe_one]
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  obtain ⟨i, hiK, -, hi⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hψ
  set C : Subgroup A := commOf φ ⊔ commOf ψ with hCdef
  have hCX : C.map A.subtype ≤ X := by
    rw [hCdef, Subgroup.map_sup]
    exact sup_le ((map_commOf_le_kOf h222 hpair hK hφ).trans hKX)
      ((map_commOf_le_kOf h222 hpair hK hψ).trans hJX)
  have hnormal : (commOf φ).Normal :=
    ⟨fun n hn g => by rw [hAc g n, mul_inv_cancel_right]; exact hn⟩
  have hψφ : ¬ commOf ψ ≤ commOf φ := by
    intro hle
    have : commOf ψ = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact le_inf hle le_rfl
    have h3 := hψr.2
    rw [this, Subgroup.card_bot] at h3
    omega
  have hlt : commOf φ < C := lt_of_le_of_ne le_sup_left fun h => hψφ (h ▸ le_sup_right)
  have hC9 : 9 ≤ Nat.card C := by
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [hφr.2] at h1
    have hdvd : Nat.card C ∣ 3 ^ 3 := hA27 ▸ Subgroup.card_subgroup_dvd_card C
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hkeq] at h1 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> norm_num at h1
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hz₀C : z₀ ∉ C.map A.subtype := by
    rintro ⟨a, haC, ha⟩
    have hfixφ : φ a = a := by
      rw [← hj]
      apply Subtype.ext
      rw [wConj_apply]
      change (j : G) * a * (j : G)⁻¹ = a
      rw [Subgroup.coe_subtype] at ha
      rw [ha, hz₀c j (hKX hjK), mul_inv_cancel_right]
    have hfixψ : ψ a = a := by
      rw [← hi]
      apply Subtype.ext
      rw [wConj_apply]
      change (i : G) * a * (i : G)⁻¹ = a
      rw [Subgroup.coe_subtype] at ha
      rw [ha, hz₀c i (hJX hiK), mul_inv_cancel_right]
    obtain ⟨u, hu, v, hv, rfl⟩ := (Subgroup.mem_sup_of_normal_left).mp haC
    have hφu : φ u = u⁻¹ := inv_of_mem_commOf hAc hφφ hu
    have hφv : φ v = v := (mem_fixedSubgroupOf φ v).mp (h₁ hv)
    have hψu : ψ u = u := (mem_fixedSubgroupOf ψ u).mp (h₂ hu)
    have hψv : ψ v = v⁻¹ := inv_of_mem_commOf hAc hψψ hv
    rw [map_mul, hφu, hφv] at hfixφ
    rw [map_mul, hψu, hψv] at hfixψ
    have hu1 : u = 1 := eq_one_of_eq_inv hA3 (mul_right_cancel hfixφ).symm
    have hv1 : v = 1 := eq_one_of_eq_inv hA3 (mul_left_cancel hfixψ).symm
    apply hz₀1
    rw [← ha, hu1, hv1, mul_one]
    rfl
  set H : Subgroup G := C.map A.subtype ⊔ Subgroup.zpowers z₀ with hHdef
  have hHX : H ≤ X := sup_le hCX (Subgroup.zpowers_le.mpr hz₀X)
  obtain ⟨hHc, hHe⟩ := sup_commute_pow_three (H₁ := C.map A.subtype)
    (H₂ := Subgroup.zpowers z₀)
    (by
      rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
      exact congrArg Subtype.val (hAc a b))
    (by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm])
    (by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxX := hCX hx
      exact (Commute.zpow_right (hz₀c x hxX) k))
    (by
      rintro _ ⟨a, -, rfl⟩
      exact hAe.2 _ a.2)
    (by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz₀3, one_zpow])
  have hupper := card_le_nine_of_le_SL3 e hHX hHc hHe
  have hlt' : C.map A.subtype < H :=
    lt_of_le_of_ne le_sup_left fun h => hz₀C (h ▸ Subgroup.mem_sup_right
      (Subgroup.mem_zpowers z₀))
  have h1 := Subgroup.card_lt_of_lt hlt'
  rw [Subgroup.card_map_of_injective A.subtype_injective] at h1
  omega

theorem insp228SL3_of (h222 : Item222) (hKW : KOfWellDefinedAll)
    (hNC : Insp228SL3NonComm) : Insp228SL3 := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam hψX
  refine ⟨fun hc => ?_, hNC G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hfam hψX⟩
  obtain ⟨m, hm0, hme, -, ⟨e⟩⟩ := hfam
  exact (mulComm_ne_of_SL3 h222 hpair hA27 (hKW G A E U c L hpair) hφ hψ hne hKX hJX hm0 hme
    e hc).elim

end Item228InspProof

end CFSG.RankThree.PartTwo.Sec21
