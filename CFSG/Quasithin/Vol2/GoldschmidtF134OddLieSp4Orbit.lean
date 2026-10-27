module

public import CFSG.Quasithin.Vol2.F134LieSp4Borel

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher SymplecticFour Submodule
open CFSG.Quasithin.F134.Sp4

variable {K : Type} [Field K]

local notation "M[" g "]" => Units.val (Subtype.val g)

theorem not_dvd_pow_of_dvd_pred {p a q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : p ∣ q - 1) : ¬ q + 1 ∣ p ^ a := by
  intro h
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 h
  rcases b with _ | b
  · rw [pow_zero] at hb
    omega
  · have h1 : p ∣ q + 1 := hb ▸ dvd_pow_self p (Nat.succ_ne_zero b)
    have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h1 hpq
    rw [show q + 1 - (q - 1) = 2 by omega] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem le_stabilizer_one_of_le_stabilizer_two_of_dvd [Finite K] {P : Subgroup (StatedSp 2 K)}
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPU : ∀ u ∈ unipotent 2 K, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ unipotent 2 K, u * x = y * s)
    (hPF : P ≤ stabilizer 2 K (flag 2 K 2)) (hPa : Nat.card P = p ^ a)
    (hq : p ∣ Nat.card K - 1) : P ≤ stabilizer 2 K (flag 2 K 1) := by
  set e := (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) with he
  have he0 : e ≠ 0 := single_inl_zero_ne_zero
  have heF : e ∈ flag 2 K 2 := by
    rw [mem_flag_two_iff]
    simp [he]
  suffices hfix : ∀ y ∈ P, M[y] *ᵥ e ∈ flag 2 K 1 by
    intro y hy
    refine mem_stabilizer_of_mulVec_mem' fun v hv => ?_
    rw [eq_smul_e1_of_mem_flag_one hv, mulVec_smul]
    exact Submodule.smul_mem _ _ (hfix y hy)
  by_contra hne
  obtain ⟨y₀, hy₀, hv₀⟩ := not_forall₂.mp hne
  set v := M[y₀] *ᵥ e with hv
  have hvF : v ∈ flag 2 K 2 := mulVec_mem_of_mem_stabilizer (hPF hy₀) heF
  obtain ⟨hv0, hv1⟩ := mem_flag_two_iff.mp hvF
  have hvl : v (Sum.inl 1) ≠ 0 := fun h => hv₀ (mem_flag_one_iff.mpr ⟨hv0, hv1, h⟩)
  set p₀ := SpPoint.ofVec e he0
  have hsmul : ∀ y : P, y • p₀ = SpPoint.ofVec (M[(y : StatedSp 2 K)] *ᵥ e)
      (fun h => he0 (spAct_injective (y : StatedSp 2 K) (h.trans (map_zero _).symm))) :=
    fun y => smul_ofVec (y : StatedSp 2 K) e he0
  have horbit : MulAction.orbit P p₀ = {M : SpPoint 2 K | M.line ≤ flag 2 K 2} := by
    ext Mp
    constructor
    · rintro ⟨y, rfl⟩
      change (y • p₀).line ≤ flag 2 K 2
      rw [hsmul y, line_ofVec, span_le, Set.singleton_subset_iff]
      exact mulVec_mem_of_mem_stabilizer (hPF y.2) heF
    · intro hM
      obtain ⟨w, hw, rfl⟩ := Mp.exists_ofVec
      have hwF : w ∈ flag 2 K 2 := by
        apply hM
        rw [line_ofVec]
        exact mem_span_singleton_self w
      obtain ⟨hw0, hw1⟩ := mem_flag_two_iff.mp hwF
      by_cases hwl : w (Sum.inl 1) = 0
      · have hw' : w = w (Sum.inl 0) • e := eq_smul_e1_of_mem_flag_one
          (mem_flag_one_iff.mpr ⟨hw0, hw1, hwl⟩)
        have hc : w (Sum.inl 0) ≠ 0 := fun h => hw (by rw [hw', h, zero_smul])
        refine ⟨1, ?_⟩
        change (1 : P) • p₀ = _
        rw [one_smul]
        exact (ofVec_smul_eq he0 hc (hw' ▸ hw)).symm.trans (by congr 1; exact hw'.symm)
      · set a := w (Sum.inl 0) / w (Sum.inl 1) - v (Sum.inl 0) / v (Sum.inl 1)
        obtain ⟨y, hy, hyv⟩ := exists_mulVec_e1 hPU (lam_mem_unipotent a) hy₀
        set c := v (Sum.inl 1) / w (Sum.inl 1)
        have hc : c ≠ 0 := div_ne_zero hvl hwl
        have hlam : M[lam a] *ᵥ v = c • w := by
          rw [lam_mulVec_of_mem_flag_two a hvF]
          ext i
          rcases i with i | i <;> fin_cases i <;> simp [c, a, hw0, hw1]
          · field_simp
            ring
          · field_simp
        refine ⟨⟨y, hy⟩, ?_⟩
        change (⟨y, hy⟩ : P) • p₀ = _
        rw [hsmul]
        have hcw : c • w ≠ 0 := smul_ne_zero hc hw
        refine (SpPoint.ext ?_).trans (ofVec_smul_eq hw hc hcw)
        rw [line_ofVec, line_ofVec]
        congr 1
        rw [Set.singleton_eq_singleton_iff]
        change M[y] *ᵥ e = c • w
        rw [hyv, ← hlam]
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hpts : Nat.card {M : SpPoint 2 K // M.line ≤ flag 2 K 2} = Nat.card K + 1 := by
    have h := card_pointsLe_mul (flag 2 K 2)
    rw [finrank_flag (by norm_num)] at h
    have h2 := Nat.sq_sub_sq (Nat.card K) 1
    rw [one_pow] at h2
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h
  have hcardO : Nat.card (MulAction.orbit P p₀) = Nat.card K + 1 := by
    rw [horbit]
    exact hpts
  have hdvd : Nat.card (MulAction.orbit P p₀) ∣ Nat.card P := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  rw [hcardO, hPa] at hdvd
  exact not_dvd_pow_of_dvd_pred hp hp2 hK1 hq hdvd

end CFSG.Quasithin.H13.NQCore.Psp4
