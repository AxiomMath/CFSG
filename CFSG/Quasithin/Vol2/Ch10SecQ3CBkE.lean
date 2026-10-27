module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkC
public import CFSG.Quasithin.Vol2.Ch10SecANatCoord
public import CFSG.Quasithin.Vol2.Ch10SecEBlockA5
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem odd_four_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (4 ^ n - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
    ((by decide : Even 4).pow_of_ne_zero (by omega)) odd_one

theorem ker_eq_pCore [Finite G] {X : Subgroup G} {F F' : Type} [Field F] [Fintype F] [Field F']
    [Finite F'] {j n : ℕ} (hj : 2 ≤ j) (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ j)
    (hF' : Nat.card F' = 2 ^ n) (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαs : Function.Surjective α)
    (e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F') :
    α.ker = CFSG.pCore 2 ↥X ∧ j = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : Nat.card F = 2 ^ j := by rw [Nat.card_eq_fintype_card, hF]
  have hcard := SecA.card_SL_two_pow hF2
  have h16 : 16 ≤ 4 ^ j := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hle : CFSG.pCore 2 ↥X ≤ α.ker := by
    have := Ch11.SecA.isSimpleGroup_SL2 (K := F) hj hF2
    have : ((CFSG.pCore 2 ↥X).map α).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥X)).map α hαs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥X).map α) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h2 : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) F) := by
        have := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map α
        rw [h] at this
        exact this.of_equiv Subgroup.topEquiv
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      rw [hcard] at hk
      have hdvd : 4 ^ j - 1 ∣ 2 ^ k := ⟨2 ^ j, by rw [← hk, mul_comm]⟩
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [pow_zero] at hi
        omega
      · exact (odd_four_pow_sub_one (by omega)).not_two_dvd_nat (hi ▸ dvd_pow_self 2 hi0.ne')
  have hge : α.ker ≤ CFSG.pCore 2 ↥X := by
    have := Ch11.SecA.isSimpleGroup_SL2 (K := F') hn hF'
    have : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := e.isSimpleGroup
    have : (α.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).Normal :=
      (MonoidHom.normal_ker α).map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (α.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) with h | h
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    · exfalso
      have htop : α.ker = ⊤ := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨y, hy, hyx⟩ : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈
            α.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := h ▸ Subgroup.mem_top _
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
        have := α.ker.mul_mem hy (hle hyx)
        rwa [mul_inv_cancel_left] at this
      obtain ⟨x, hx⟩ := hαs ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
      have h1 : α x = 1 := (htop ▸ Subgroup.mem_top x : x ∈ α.ker)
      rw [h1] at hx
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F) 0 1) hx
      simp at this
  have hker : α.ker = CFSG.pCore 2 ↥X := le_antisymm hge hle
  refine ⟨hker, ?_⟩
  have hX1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv, hcard,
    hker] at hX1
  have hX2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF'] at hX2
  have hpos : 0 < Nat.card (CFSG.pCore 2 ↥X) := Nat.card_pos
  have heq : 2 ^ j * (4 ^ j - 1) = 2 ^ n * (4 ^ n - 1) :=
    Nat.eq_of_mul_eq_mul_right hpos (hX1.symm.trans hX2)
  exact eq_of_two_pow_mul_odd (odd_four_pow_sub_one (by omega))
    (odd_four_pow_sub_one (by omega)) heq

section L

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem natData_L (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Ch10.Hyp10 G T L I)
    (h1 : Ch10.Case10_1_1One T L I n) (hCV : fsuCVM T L I = ⊥) :
    NatData L (fsuUL T L I) n := by
  obtain ⟨hab, F, _, _, _, hn, hF, ⟨c⟩⟩ := SecA.exists_natCoord hyp h1
  have := Fintype.ofFinite F
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator hLV Subgroup.le_normalizer
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hel := SecA.isElemAbelian_fsuVM hyp
  obtain ⟨K', _, _, hK', ⟨e⟩⟩ := h1.2.1
  set α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F :=
    c.eρ.symm.toMonoidHom.comp (SecA.autOnHomOf hLU) with hα
  have hαs : Function.Surjective α := c.eρ.symm.surjective.comp (SecA.autOnHomOf_surjective hLU)
  have hαk : α.ker = CFSG.pCore 2 ↥L :=
    (ker_eq_pCore hn hn (by rw [← Nat.card_eq_fintype_card, hF]) hK' α hαs e).1
  refine ⟨SecE.fsuUL_le_pCoreOf_L hyp, fun u hu => ?_, fun u hu => ?_, hLU, F, inferInstance,
    inferInstance, by rw [← Nat.card_eq_fintype_card, hF], α, hαs, hαk, c.β, ⟨?_, c.surj⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' := SecE.pCoreOf_L_le_centralizer h37 h38 h3228 hyp (Or.inl ⟨n, h1⟩) hq
    exact (Subgroup.mem_centralizer_iff.mp hq' u (hUV hu)).symm
  · have := hel.2 u (hUV hu)
    simpa using this
  · rw [injective_iff_map_eq_one]
    intro w hw
    have hw' := (c.ker w).mp hw
    have hmem : (w : G) ∈ fsuCVM T L I := ⟨hUV w.2, hw'⟩
    rw [hCV, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  · intro ℓ u v huv
    have h1 := c.equivariant (α ℓ) u
    have h2 : ((c.eρ (α ℓ) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) u = v := by
      have : c.eρ (α ℓ) = SecA.autOnHomOf hLU ℓ := by
        rw [hα, MonoidHom.comp_apply]
        exact c.eρ.apply_symm_apply _
      rw [this]
      apply Subtype.ext
      rw [SecA.autOnHomOf_apply, huv]
      rfl
    rw [h2] at h1
    rw [h1, toAdd_ofAdd]

end L

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
