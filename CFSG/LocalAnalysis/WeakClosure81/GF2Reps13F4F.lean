module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4B
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4FAux1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundB
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s134b_three_summands (hW : ∀ w : W, w ^ 2 = 1) {K K' : Subgroup (MulAut W)}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hL3 : UC22.IsL3 ↥K 1) (hL3' : UC22.IsL3 ↥K' 1)
    {R : Subgroup W} (hcard : Nat.card ↥R = 2 ^ 9) (hirr : IsIrrOn (K ⊔ K') R ⊥)
    (hKnt : ¬ ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r = r)
    (hK'nt : ¬ ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r = r) :
    ∃ I : Fin 3 → Subgroup W, (∀ i, BinaryNaturalSL K (I i) ⊥ 3 1) ∧
      (∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ ⊥) ∧ (⊥ ⊔ ⨆ i, I i) = R ∧
      ∀ i, CFSG.Quasithin.H.Pair.IsoMod K (I 0) (I i) := by
  have hRK : R ⊓ fixV K = ⊥ := f4f_inf_fixV_eq_bot hKK' hirr hKnt
  have hRK' : R ⊓ fixV K' = ⊥ := by
    refine f4f_inf_fixV_eq_bot (A := K') (B := K) (fun a ha b hb => (hKK' b hb a ha).symm) ?_ hK'nt
    rwa [sup_comm]
  have hKR : StableUnder K R :=
    fun a ha r hr => hirr.2.1 a (Subgroup.mem_sup_left ha) r hr
  have hK'R : StableUnder K' R :=
    fun b hb r hr => hirr.2.1 b (Subgroup.mem_sup_right hb) r hr
  have hKperf : ⁅K, K⁆ = K := s134b_perfect_of_isL3 hL3
  have hK'perf : ⁅K', K'⁆ = K' := s134b_perfect_of_isL3 hL3'
  obtain ⟨M₀, hM₀leR, hM₀stab, hM₀ne, hM₀irr, hM₀min⟩ := f4f_exists_minimal hirr.1.ne' hKR
  have hM₀inf : M₀ ⊓ fixV K = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hM₀leR le_rfl).trans (le_of_eq hRK))
  have hM₀nt : ∃ k ∈ K, ∃ u ∈ M₀, (k : MulAut W) u * u⁻¹ ∉ (⊥ : Subgroup W) := by
    by_contra h
    apply hM₀ne
    apply le_bot_iff.mp
    have hfix : M₀ ≤ fixV K := by
      intro u hu
      rw [mem_fixV]
      intro k hk
      by_contra hne
      exact h ⟨k, hk, u, hu, by
        intro hmem
        exact hne (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem))⟩
    exact (le_inf le_rfl hfix).trans (le_of_eq hM₀inf)
  have hM₀card_ge : 8 ≤ Nat.card ↥M₀ := by
    by_cases hle : Nat.card ↥M₀ ≤ 8
    · have hle' : Nat.card (Sec M₀ ⊥) ≤ 8 := by rw [f4f_card_sec_bot M₀]; exact hle
      have h8 := s134b_perfect_sec_card hW hKperf (I := M₀) (C := ⊥) bot_le hM₀stab
        (f4f_stableUnder_bot K) hM₀nt hle'
      rw [f4f_card_sec_bot M₀] at h8
      omega
    · have h8 : 8 < Nat.card ↥M₀ := not_le.1 hle
      omega
  have hrk3le : 3 ≤ rk ↥M₀ := by
    have h8 : (8 : ℕ) ≤ 2 ^ rk ↥M₀ := by
      rw [← card_eq_two_pow hW M₀]
      exact hM₀card_ge
    have h23 : (2 : ℕ) ^ 3 ≤ 2 ^ rk ↥M₀ := by norm_num; exact h8
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h23
  have h9 : rk ↥R = 9 := by
    have h2 : 2 ^ 9 = 2 ^ rk ↥R := by
      rw [← hcard]
      exact card_eq_two_pow hW R
    exact ((Nat.pow_right_injective (by norm_num : 2 ≤ 2)) h2).symm
  have hS_eq : (⨆ k : K', M₀.map (k : MulAut W).toMonoidHom) = R :=
    f4f_iSup_translates_eq hKK' hirr hM₀leR hM₀stab hM₀ne
  have hex₁ : ∃ k ∈ K', M₀.map k.toMonoidHom ≠ M₀ := by
    by_contra h
    have halleq : ∀ k ∈ K', M₀.map k.toMonoidHom = M₀ := by
      intro k hk
      by_contra hne
      exact h ⟨k, hk, hne⟩
    have hK'stab : StableUnder K' M₀ := by
      intro k hk u hu
      have hmem : k u ∈ M₀.map k.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rwa [halleq k hk] at hmem
    have hLstab : StableUnder (K ⊔ K') M₀ := f4f_stableUnder_sup hM₀stab hK'stab
    have hM₀eqR : M₀ = R := by
      rcases hirr.2.2.2 M₀ hLstab bot_le hM₀leR with h' | h'
      · exact absurd h' hM₀ne
      · exact h'
    have hcomm : ⁅K, K'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hKK' x hx y hy).symm
    have hrK : R ⊓ fixV K = ⊥ := by rw [← hM₀eqR]; exact hM₀inf
    have hirrK : IsIrrOn K R (R ⊓ fixV K) := by rw [hrK, ← hM₀eqR]; exact hM₀irr
    have hschur := s13_schur_perfect (fun w => by rw [← sq]; exact hW w) K K' hcomm hK'perf
      R hKR hK'R hirrK
    have hbot : commSub R K' = ⊥ := le_bot_iff.mp (hschur.trans (le_of_eq hrK))
    have hfix : R ≤ fixV K' := commSub_eq_bot_iff.mp hbot
    exact hK'nt (fun k hk r hr => mem_fixV.mp (hfix hr) k hk)
  obtain ⟨k₁, hk₁K', hk₁ne⟩ := hex₁
  have hI1irr : IsIrrOn K (M₀.map k₁.toMonoidHom) ⊥ := f4f_map_irr hKK' hM₀irr hk₁K'
  have hI1leR : M₀.map k₁.toMonoidHom ≤ R := f4f_map_le_of_stable hK'R hM₀leR hk₁K'
  have hI0infI1 : M₀ ⊓ M₀.map k₁.toMonoidHom = ⊥ :=
    f4f_inf_eq_bot_of_irr hM₀irr hI1irr hk₁ne.symm
      (Subgroup.card_map_of_injective k₁.injective).symm
  have hJ₁le : M₀ ⊔ M₀.map k₁.toMonoidHom ≤ R := sup_le hM₀leR hI1leR
  have hJ₁rk : rk ↥(M₀ ⊔ M₀.map k₁.toMonoidHom) = 2 * rk ↥M₀ := by
    rw [f4f_rk_sup_of_inf_bot hI0infI1, f4f_rk_map, two_mul]
  have hJ₁ne : M₀ ⊔ M₀.map k₁.toMonoidHom ≠ R := by
    intro hJeq
    have h29 : 2 * rk ↥M₀ = 9 := by
      rw [hJeq, h9] at hJ₁rk
      omega
    omega
  have hex₂ : ∃ k ∈ K', ¬ M₀.map k.toMonoidHom ≤ M₀ ⊔ M₀.map k₁.toMonoidHom := by
    by_contra h
    have hle : (⨆ k : K', M₀.map (k : MulAut W).toMonoidHom) ≤
        M₀ ⊔ M₀.map k₁.toMonoidHom := by
      refine iSup_le fun k : K' => ?_
      by_contra hk
      exact h ⟨(k : MulAut W), k.2, hk⟩
    exact hJ₁ne (le_antisymm hJ₁le (hS_eq ▸ hle))
  obtain ⟨k₂, hk₂K', hk₂⟩ := hex₂
  have hI2irr : IsIrrOn K (M₀.map k₂.toMonoidHom) ⊥ := f4f_map_irr hKK' hM₀irr hk₂K'
  have hI2leR : M₀.map k₂.toMonoidHom ≤ R := f4f_map_le_of_stable hK'R hM₀leR hk₂K'
  have hJ₁stab : StableUnder K (M₀ ⊔ M₀.map k₁.toMonoidHom) :=
    stableUnder_sup hM₀stab hI1irr.2.1
  have hI2infJ₁ : (M₀.map k₂.toMonoidHom) ⊓ (M₀ ⊔ M₀.map k₁.toMonoidHom) = ⊥ := by
    rcases hI2irr.2.2.2 ((M₀.map k₂.toMonoidHom) ⊓ (M₀ ⊔ M₀.map k₁.toMonoidHom))
        (stableUnder_inf hI2irr.2.1 hJ₁stab) bot_le inf_le_left with h | h
    · exact h
    · exfalso
      exact hk₂ (h ▸ inf_le_right)
  have hk₂ne : M₀.map k₂.toMonoidHom ≠ M₀ := by
    intro heq
    apply hk₂
    calc M₀.map k₂.toMonoidHom = M₀ := heq
      _ ≤ M₀ ⊔ M₀.map k₁.toMonoidHom := le_sup_left
  have hk₂ne' : M₀.map k₂.toMonoidHom ≠ M₀.map k₁.toMonoidHom := by
    intro heq
    apply hk₂
    calc M₀.map k₂.toMonoidHom = M₀.map k₁.toMonoidHom := heq
      _ ≤ M₀ ⊔ M₀.map k₁.toMonoidHom := le_sup_right
  have hI0infI2 : M₀ ⊓ M₀.map k₂.toMonoidHom = ⊥ :=
    f4f_inf_eq_bot_of_irr hM₀irr hI2irr hk₂ne.symm
      (Subgroup.card_map_of_injective k₂.injective).symm
  have hcard12 : Nat.card ↥(M₀.map k₁.toMonoidHom) = Nat.card ↥(M₀.map k₂.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective k₁.injective, Subgroup.card_map_of_injective k₂.injective]
  have hI1infI2 : (M₀.map k₁.toMonoidHom) ⊓ (M₀.map k₂.toMonoidHom) = ⊥ :=
    f4f_inf_eq_bot_of_irr hI1irr hI2irr hk₂ne'.symm hcard12
  have hJ₂le : M₀ ⊔ M₀.map k₁.toMonoidHom ⊔ M₀.map k₂.toMonoidHom ≤ R :=
    sup_le hJ₁le hI2leR
  have hJ₂rk : rk ↥(M₀ ⊔ M₀.map k₁.toMonoidHom ⊔ M₀.map k₂.toMonoidHom) = 3 * rk ↥M₀ := by
    rw [f4f_rk_sup_of_inf_bot (A := M₀ ⊔ M₀.map k₁.toMonoidHom)
        (B := M₀.map k₂.toMonoidHom) (by rw [inf_comm]; exact hI2infJ₁),
      hJ₁rk, f4f_rk_map]
    ring
  have hJ₂eq : M₀ ⊔ M₀.map k₁.toMonoidHom ⊔ M₀.map k₂.toMonoidHom = R := by
    refine eq_of_le_of_rk_le hW hJ₂le ?_
    rw [hJ₂rk, h9]
    omega
  have hr_eq : rk ↥M₀ = 3 := by
    have h39 : 3 * rk ↥M₀ = 9 := by
      rw [← hJ₂rk, hJ₂eq, h9]
    omega
  let I : Fin 3 → Subgroup W := ![M₀, M₀.map k₁.toMonoidHom, M₀.map k₂.toMonoidHom]
  have hI0 : I 0 = M₀ := rfl
  have hI1 : I 1 = M₀.map k₁.toMonoidHom := rfl
  have hI2 : I 2 = M₀.map k₂.toMonoidHom := rfl
  have hI012 : I 0 ⊔ I 1 ⊔ I 2 = R := by
    change M₀ ⊔ M₀.map k₁.toMonoidHom ⊔ M₀.map k₂.toMonoidHom = R
    exact hJ₂eq
  have hI120 : I 1 ⊔ I 2 ⊔ I 0 = R := by rw [← hI012]; ac_rfl
  have hI201 : I 2 ⊔ I 0 ⊔ I 1 = R := by rw [← hI012]; ac_rfl
  have h01 : I 0 ⊓ I 1 = ⊥ := by rw [hI0, hI1]; exact hI0infI1
  have h02 : I 0 ⊓ I 2 = ⊥ := by rw [hI0, hI2]; exact hI0infI2
  have h12 : I 1 ⊓ I 2 = ⊥ := by rw [hI1, hI2]; exact hI1infI2
  have hrkI0 : rk ↥(I 0) = 3 := by rw [hI0]; exact hr_eq
  have hrkI1 : rk ↥(I 1) = 3 := by rw [hI1, f4f_rk_map k₁ M₀]; exact hr_eq
  have hrkI2 : rk ↥(I 2) = 3 := by rw [hI2, f4f_rk_map k₂ M₀]; exact hr_eq
  have hcard_sec0 : Nat.card (Sec (I 0) ⊥) = 8 := by
    rw [f4f_card_sec_bot, hI0, card_eq_two_pow hW M₀, hr_eq]; norm_num
  have hcard_sec1 : Nat.card (Sec (I 1) ⊥) = 8 := by
    rw [f4f_card_sec_bot, hI1, card_eq_two_pow hW (M₀.map k₁.toMonoidHom),
      f4f_rk_map k₁ M₀, hr_eq]; norm_num
  have hcard_sec2 : Nat.card (Sec (I 2) ⊥) = 8 := by
    rw [f4f_card_sec_bot, hI2, card_eq_two_pow hW (M₀.map k₂.toMonoidHom),
      f4f_rk_map k₂ M₀, hr_eq]; norm_num
  have hntI1 : ∃ k ∈ K, ∃ u ∈ I 1, (k : MulAut W) u * u⁻¹ ∉ (⊥ : Subgroup W) := by
    rw [hI1]; exact f4f_map_nt hKK' hk₁K' hM₀nt
  have hntI2 : ∃ k ∈ K, ∃ u ∈ I 2, (k : MulAut W) u * u⁻¹ ∉ (⊥ : Subgroup W) := by
    rw [hI2]; exact f4f_map_nt hKK' hk₂K' hM₀nt
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change BinaryNaturalSL K M₀ ⊥ 3 1
      exact s134b_natural_of_card_eight hW hL3 bot_le hM₀stab (f4f_stableUnder_bot K)
        hcard_sec0 hM₀nt
    · change BinaryNaturalSL K (M₀.map k₁.toMonoidHom) ⊥ 3 1
      exact s134b_natural_of_card_eight hW hL3 bot_le hI1irr.2.1 (f4f_stableUnder_bot K)
        hcard_sec1 hntI1
    · change BinaryNaturalSL K (M₀.map k₂.toMonoidHom) ⊥ 3 1
      exact s134b_natural_of_card_eight hW hL3 bot_le hI2irr.2.1 (f4f_stableUnder_bot K)
        hcard_sec2 hntI2
  · intro i
    fin_cases i <;> dsimp only
    · have hle : (⨆ (j : Fin 3) (_ : j ≠ (0 : Fin 3)), I j) ≤ I 1 ⊔ I 2 := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact (hj rfl).elim
        · exact le_sup_left
        · exact le_sup_right
      rw [bot_sup_eq]
      exact le_trans (inf_le_inf le_rfl hle)
        (f4f_indep_of hW h01 h02 h12 hrkI0 hrkI1 hrkI2 hI012 h9)
    · have hle : (⨆ (j : Fin 3) (_ : j ≠ (1 : Fin 3)), I j) ≤ I 2 ⊔ I 0 := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact le_sup_right
        · exact (hj rfl).elim
        · exact le_sup_left
      rw [bot_sup_eq]
      exact le_trans (inf_le_inf le_rfl hle)
        (f4f_indep_of hW h12 (by rw [inf_comm]; exact h01) (by rw [inf_comm]; exact h02)
          hrkI1 hrkI2 hrkI0 hI120 h9)
    · have hle : (⨆ (j : Fin 3) (_ : j ≠ (2 : Fin 3)), I j) ≤ I 0 ⊔ I 1 := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact le_sup_left
        · exact le_sup_right
        · exact (hj rfl).elim
      rw [bot_sup_eq]
      exact le_trans (inf_le_inf le_rfl hle)
        (f4f_indep_of hW (by rw [inf_comm]; exact h02) (by rw [inf_comm]; exact h12) h01
          hrkI2 hrkI0 hrkI1 hI201 h9)
  · rw [bot_sup_eq]
    have hIeq : (⨆ i : Fin 3, I i) = I 0 ⊔ I 1 ⊔ I 2 := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        fin_cases i
        · exact le_trans le_sup_left le_sup_left
        · exact le_trans le_sup_right le_sup_left
        · exact le_sup_right
      · refine sup_le (sup_le (le_iSup I 0) (le_iSup I 1)) (le_iSup I 2)
    rw [hIeq, hI012]
  · intro i
    fin_cases i
    · change CFSG.Quasithin.H.Pair.IsoMod K M₀ M₀
      refine ⟨MulEquiv.refl M₀, ?_⟩
      intro l hl w hw
      rfl
    · change CFSG.Quasithin.H.Pair.IsoMod K M₀ (M₀.map k₁.toMonoidHom)
      refine ⟨MulEquiv.subgroupMap k₁ M₀, ?_⟩
      intro l hl w hw
      change k₁ (l w) = l (k₁ w)
      exact (congrArg (fun f : MulAut W => f w) (hKK' l hl k₁ hk₁K')).symm
    · change CFSG.Quasithin.H.Pair.IsoMod K M₀ (M₀.map k₂.toMonoidHom)
      refine ⟨MulEquiv.subgroupMap k₂ M₀, ?_⟩
      intro l hl w hw
      change k₂ (l w) = l (k₂ w)
      exact (congrArg (fun f : MulAut W => f w) (hKK' l hl k₂ hk₂K')).symm

end CFSG.LocalAnalysis.WeakClosure81
