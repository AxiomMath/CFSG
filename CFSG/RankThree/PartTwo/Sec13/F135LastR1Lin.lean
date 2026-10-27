module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofGL

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG
open scoped MatrixGroups

theorem r1a_top_of_comm {Y : Type*} [Group Y] (O N : Subgroup Y) [O.Normal]
    (hperf : Group.IsPerfect (Y ⧸ O)) (hON : O ≤ N)
    (hcomm : ∀ a b : Y, @Bracket.bracket Y Y commutatorElement a b ∈ N) :
    N = ⊤ := by
  have hC : ⁅(⊤ : Subgroup (Y ⧸ O)), (⊤ : Subgroup (Y ⧸ O))⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.mp hperf
  have hmap : Subgroup.map (QuotientGroup.mk' O) ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O),
      hC]
  have hCN : ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  rw [eq_top_iff]
  intro y _
  have hy : QuotientGroup.mk' O y ∈
      Subgroup.map (QuotientGroup.mk' O) ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hcy
  have hco : c⁻¹ * y ∈ O := (QuotientGroup.eq (s := O)).mp hcy
  have hprod := N.mul_mem (hCN hc) (hON hco)
  rwa [mul_inv_cancel_left] at hprod

theorem r1a_comm_of_gen {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal] (g : Y)
    (h : ∀ a : Y, ∃ n ∈ N, ∃ i : ℤ, a = n * g ^ i) :
    ∀ a b : Y, @Bracket.bracket Y Y commutatorElement a b ∈ N := by
  have key : ∀ a : Y, ∃ i : ℤ, QuotientGroup.mk' N a = QuotientGroup.mk' N g ^ i := by
    intro a
    obtain ⟨n, hn, i, rfl⟩ := h a
    refine ⟨i, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff n).mpr hn
    rw [map_mul, map_zpow, hn1, one_mul]
  intro a b
  obtain ⟨i, hi⟩ := key a
  obtain ⟨j, hj⟩ := key b
  have hc : QuotientGroup.mk' N (@Bracket.bracket Y Y commutatorElement a b) = 1 := by
    rw [map_commutatorElement, hi, hj, commutatorElement_eq_one_iff_mul_comm]
    exact ((Commute.refl (QuotientGroup.mk' N g)).zpow_zpow i j).eq
  rw [QuotientGroup.mk'_apply] at hc
  exact (QuotientGroup.eq_one_iff _).mp hc

theorem r1_ker_le {Y : Type*} [Group Y] [Finite Y] (O : Subgroup Y) [O.Normal]
    (hOodd : Odd (Nat.card O)) (hperf : Group.IsPerfect (Y ⧸ O)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (ρ : Y →* Module.End (ZMod p) W) {z : Y} (hz : ∀ w, ρ z w = -w) (hW : ∃ w : W, w ≠ 0)
    {T : Type*} [Group T] [IsSimpleGroup T] (ψ : Y →* T) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.zpowers z ⊔ O) :
    ∀ y, (∀ w, ρ y w = w) → ψ y = 1 := by
  intro y hy
  by_contra hne
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup Y, K = ρ.toHomUnits.ker := ⟨_, rfl⟩
  have hKmem : ∀ k : Y, k ∈ K ↔ ρ k = 1 := by
    intro k
    rw [hKdef, MonoidHom.mem_ker]
    constructor
    · intro h
      simpa [MonoidHom.coe_toHomUnits] using congrArg Units.val h
    · intro h
      ext
      simp [MonoidHom.coe_toHomUnits, h]
  have hKn : K.Normal := by
    rw [hKdef]
    exact MonoidHom.normal_ker _
  have hψK : (K.map ψ).Normal := hKn.map ψ hψ
  have hyK : y ∈ K := (hKmem y).mpr (by ext w; simp [hy w])
  have htop : K.map ψ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map ψ) with h | h
    · exfalso
      apply hne
      have hmem : ψ y ∈ K.map ψ := Subgroup.mem_map_of_mem ψ hyK
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    · exact h
  have hsplit : ∀ a : Y, ∃ k ∈ K, ∃ s ∈ ψ.ker, a = k * s := by
    intro a
    have hmem : ψ a ∈ K.map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.mp hmem
    refine ⟨k, hk, k⁻¹ * a, ?_, (mul_inv_cancel_left k a).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hka, inv_mul_cancel]
  have hOn : O.Normal := inferInstance
  have hdec : ∀ a : Y, ∃ n ∈ K ⊔ O, ∃ i : ℤ, a = n * z ^ i := by
    intro a
    obtain ⟨k, hk, s, hs, rfl⟩ := hsplit a
    obtain ⟨h, hh, o, ho, hho⟩ := Subgroup.mem_sup_of_normal_right.mp (hker hs)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    subst hho
    refine ⟨k * (z ^ i * o * (z ^ i)⁻¹), ?_, i, ?_⟩
    · exact Subgroup.mul_mem_sup hk (hOn.conj_mem o ho (z ^ i))
    · group
  have hcomm : ∀ a b : Y, @Bracket.bracket Y Y commutatorElement a b ∈ K ⊔ O :=
    r1a_comm_of_gen (K ⊔ O) z hdec
  have htopN : K ⊔ O = ⊤ := r1a_top_of_comm O (K ⊔ O) hperf le_sup_right hcomm
  have hzN : z ∈ K ⊔ O := by
    rw [htopN]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, o, ho, hko⟩ := Subgroup.mem_sup_of_normal_left.mp hzN
  have hkone : ρ k = 1 := (hKmem k).mp hk
  have hρz : ρ z = ρ o := by
    rw [← hko, map_mul, hkone, one_mul]
  have hρo : ∀ w, ρ o w = -w := fun w => by
    rw [← hρz]
    exact hz w
  have hpow : o ^ Nat.card O = 1 := by
    have h1 : (⟨o, ho⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    exact h2
  have hρo' : ρ o = -1 := LinearMap.ext fun w => by simp [hρo w]
  have hodd : (ρ o) ^ Nat.card O = 1 := by
    rw [← map_pow, hpow, map_one]
  rw [hρo', Odd.neg_one_pow hOodd] at hodd
  obtain ⟨w, hw0⟩ := hW
  have hneg : -w = w := by
    simpa using congrArg (fun f : Module.End (ZMod p) W => f w) hodd
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
  have h2w : (2 : ZMod p) • w = 0 := by
    rw [two_smul]
    calc w + w = -w + w := by rw [hneg]
      _ = 0 := neg_add_cancel w
  apply hw0
  calc w = (2 : ZMod p)⁻¹ • (2 : ZMod p) • w := (inv_smul_smul₀ h2 w).symm
    _ = 0 := by rw [h2w, smul_zero]

theorem r1_dim_ge_four {Y : Type*} [Group Y] [Finite Y] (O : Subgroup Y)
    [O.Normal] (hOodd : Odd (Nat.card O)) (hperf : Group.IsPerfect (Y ⧸ O)) {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (ρ : Y →* Module.End (ZMod p) W) {z : Y} (hz : ∀ w, ρ z w = -w) (hW : ∃ w : W, w ≠ 0)
    {T : Type*} [Group T] [Finite T] (hT : AltTarget T) (ψ : Y →* T) (hψ : Function.Surjective ψ)
    (hker : ∀ y, (∀ w, ρ y w = w) → ψ y = 1) : 4 ≤ Module.finrank (ZMod p) W := by
  by_contra hlt
  rw [not_le] at hlt
  rcases Nat.lt_or_ge (Module.finrank (ZMod p) W) 3 with h2 | h3
  · have hle : Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) W) ≤ 2 := by
      rw [finrank_top]
      omega
    exact false_of_rep_one hp5 ρ ⊤ hle (fun _ _ _ => Submodule.mem_top) hT ψ hψ
      (fun y hy => hker y (fun w => hy w Submodule.mem_top))
  · have h3' : Module.finrank (ZMod p) W = 3 := by omega
    obtain ⟨χ, hχdef⟩ : ∃ χ : Y →* (ZMod p)ˣ,
        χ = (Units.map (LinearMap.det : Module.End (ZMod p) W →* ZMod p)).comp ρ.toHomUnits :=
      ⟨_, rfl⟩
    have hχval : ∀ y, ((χ y : (ZMod p)ˣ) : ZMod p) = LinearMap.det (ρ y) := by
      intro y
      subst hχdef
      rfl
    have hρz : ρ z = -1 := LinearMap.ext fun w => by simp [hz w]
    have hdet : LinearMap.det (ρ z) = -1 := by
      have hsm : (-1 : Module.End (ZMod p) W) = (-1 : ZMod p) • (1 : Module.End (ZMod p) W) := by
        apply LinearMap.ext
        intro w
        first
          | exact (neg_one_smul (R := ZMod p) w).symm
          | (simp [neg_one_smul]; done)
          | (simp [neg_smul, one_smul]; done)
      rw [hρz, hsm, LinearMap.det_smul, h3', Module.End.one_eq_id, LinearMap.det_id, mul_one]
      exact Odd.neg_one_pow ⟨1, rfl⟩
    have hcomm : ∀ a b : Y, @Bracket.bracket Y Y commutatorElement a b ∈ χ.ker ⊔ O := by
      intro a b
      apply Subgroup.mem_sup_left
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have htop : χ.ker ⊔ O = ⊤ := r1a_top_of_comm O (χ.ker ⊔ O) hperf le_sup_right hcomm
    have hzN : z ∈ χ.ker ⊔ O := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, o, ho, hko⟩ := Subgroup.mem_sup_of_normal_left.mp hzN
    have hkχ : χ k = 1 := MonoidHom.mem_ker.mp hk
    have hχo : χ o = χ z := by
      rw [← hko, map_mul, hkχ, one_mul]
    have hpow : o ^ Nat.card O = 1 := by
      have h1 : (⟨o, ho⟩ : O) ^ Nat.card O = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      exact h2
    have hcoe : ((χ o : (ZMod p)ˣ) : ZMod p) = -1 := by
      rw [hχo, hχval, hdet]
    have hodd : χ (o ^ Nat.card O) = 1 := by
      rw [hpow, map_one]
    have hodd' := congrArg Units.val hodd
    have hneg1 : (-1 : ZMod p) ^ Nat.card O = -1 := Odd.neg_one_pow hOodd
    rw [map_pow, Units.val_pow_eq_pow_val, hcoe, hneg1, Units.val_one] at hodd'
    have h2' : (1 : ZMod p) + 1 = 0 := neg_eq_iff_add_eq_zero.mp hodd'
    have h2 : (2 : ZMod p) = 0 := by
      rw [← one_add_one_eq_two]
      exact h2'
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp (by exact_mod_cast h2)
    have hle2 := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem r1p_not_seven_dvd_GL [Fact (Nat.Prime 5)] (d : ℕ) (hd : d ≤ 4) :
    ¬ 7 ∣ Nat.card (GL (Fin d) (ZMod 5)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> decide

theorem r1p_card_units_end [Fact (Nat.Prime 5)] (W : Type*) [AddCommGroup W]
    [Module (ZMod 5) W] [FiniteDimensional (ZMod 5) W] :
    Nat.card (Module.End (ZMod 5) W)ˣ = Nat.card (GL (Fin (Module.finrank (ZMod 5) W)) (ZMod 5)) :=
  Nat.card_congr
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasis (ZMod 5) W)).toMulEquiv).toEquiv

theorem r1_not_five [Fact (Nat.Prime 5)] {Y : Type*} [Group Y] [Finite Y] {W : Type*} [AddCommGroup W]
    [Module (ZMod 5) W] [FiniteDimensional (ZMod 5) W] (hW : Module.finrank (ZMod 5) W ≤ 4)
    (ρ : Y →* Module.End (ZMod 5) W) {T : Type*} [Group T] [Finite T] (h7 : 7 ∣ Nat.card T)
    (ψ : Y →* T) (hψ : Function.Surjective ψ) (hker : ∀ y, (∀ w, ρ y w = w) → ψ y = 1) :
    False := by
  have hle : ρ.toHomUnits.ker ≤ ψ.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : ρ y = 1 := by
      have h := congrArg Units.val hy
      rw [MonoidHom.coe_toHomUnits, Units.val_one] at h
      exact h
    apply hker
    intro w
    rw [h1, Module.End.one_apply]
  have h1 : ψ.ker.index ∣ ρ.toHomUnits.ker.index := Subgroup.index_dvd_of_le hle
  have h2 : ψ.ker.index = Nat.card T := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top]
  have h3 : ρ.toHomUnits.ker.index ∣ Nat.card (Module.End (ZMod 5) W)ˣ := by
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card T ∣ Nat.card (Module.End (ZMod 5) W)ˣ := by
    rw [← h2]
    exact dvd_trans h1 h3
  have h5 : 7 ∣ Nat.card (GL (Fin (Module.finrank (ZMod 5) W)) (ZMod 5)) := by
    rw [← r1p_card_units_end W]
    exact dvd_trans h7 h4
  exact r1p_not_seven_dvd_GL _ hW h5

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
