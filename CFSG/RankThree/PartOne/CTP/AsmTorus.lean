module

public import CFSG.RankThree.PartOne.CTP.AsmDefs
public import CFSG.RankThree.PartOne.CTP.ModelFacts

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.RankThree.PartOne CFSG.RankThree
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem card_mul_relIndex {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  unfold Subgroup.relIndex
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.card_mul_index _

theorem exists_perm_34 {u v : Fin 5} (h : u ≠ v) :
    ∃ σ : Equiv.Perm (Fin 5), σ 3 = u ∧ σ 4 = v :=
  (by decide : ∀ u v : Fin 5, u ≠ v → ∃ σ : Equiv.Perm (Fin 5), σ 3 = u ∧ σ 4 = v) u v h

section Torus

variable {L B K : Subgroup G} {f₀ : ℕ} {b : G} (F : LFam L B f₀ b K)

theorem J_inf_centralizer {u v : Fin 5} (huv : u ≠ v) :
    F.J u v ⊓ Subgroup.centralizer (F.J u v : Set G) = ⊥ := by
  have hc := psl2_model_center_eq_bot (F.J_model u v huv)
  rw [eq_bot_iff]
  intro x hx
  have hx1 : (⟨x, hx.1⟩ : ↥(F.J u v)) ∈ Subgroup.center ↥(F.J u v) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp hx.2 g g.2))
  rw [hc] at hx1
  have := congrArg Subtype.val (Subgroup.mem_bot.mp hx1)
  simpa using this

theorem line_not_le_R {u v : Fin 5} (huv : u ≠ v) :
    ¬ (B ⊓ F.J u v ≤ B ⊓ Subgroup.centralizer (F.J u v : Set G)) := by
  intro h
  have hbot : B ⊓ F.J u v = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have := (J_inf_centralizer F huv)
    have hx' : x ∈ F.J u v ⊓ Subgroup.centralizer (F.J u v : Set G) :=
      ⟨hx.2, (h hx).2⟩
    rw [this] at hx'
    exact hx'
  have h5 := F.line_card u v huv
  rw [hbot, Subgroup.card_bot] at h5
  omega

theorem R_eq_BK (σ : Equiv.Perm (Fin 5)) :
    B ⊓ Subgroup.centralizer (F.J (σ 3) (σ 4) : Set G) = B ⊓ Ksg F σ := by
  have hu : σ 3 ≠ σ 4 := σ.injective.ne (by decide)
  have hKc : Ksg F σ ≤ Subgroup.centralizer (F.J (σ 3) (σ 4) : Set G) := by
    have e2 : Ksg F σ = F.J (σ 0) (σ 1) ⊔ F.J (σ 1) (σ 2) := by
      have := congrArg (conjBy (F.W σ)) F.K_eq
      rw [conjBy_sup, conjBy_J, conjBy_J] at this
      exact this
    rw [e2]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact F.disj (σ 0) (σ 1) (σ 3) (σ 4) (σ.injective.ne (by decide))
        (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
        (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) hx
    · exact F.disj (σ 1) (σ 2) (σ 3) (σ 4) (σ.injective.ne (by decide))
        (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
        (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) hx
  have hle : B ⊓ Ksg F σ ≤ B ⊓ Subgroup.centralizer (F.J (σ 3) (σ 4) : Set G) :=
    inf_le_inf_left B hKc
  have hcardK : Nat.card ↥(B ⊓ Ksg F σ) = 25 := by
    have : B ⊓ Ksg F σ = conjBy (F.W σ) (B ⊓ K) := by
      unfold Ksg
      rw [conjBy_inf, Equivariance.conjBy_eq_of_mem_normalizer (F.W_B σ)]
    rw [this, card_conjBy, F.BK_card]
  have hne : B ⊓ Subgroup.centralizer (F.J (σ 3) (σ 4) : Set G) ≠ B := by
    intro h
    apply line_not_le_R F hu
    rw [h]
    exact inf_le_left
  have hBfin : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [F.B_card]; norm_num)
  set R := B ⊓ Subgroup.centralizer (F.J (σ 3) (σ 4) : Set G) with hR
  have hRB : R ≤ B := inf_le_left
  have hdvd1 : 25 ∣ Nat.card R := hcardK ▸ Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card R ∣ 125 := by
    have := Subgroup.card_dvd_of_le hRB
    rwa [F.B_card] at this
  have hlt : Nat.card R < 125 := by
    have hle125 : Nat.card R ≤ 125 := Nat.le_of_dvd (by norm_num) hdvd2
    refine lt_of_le_of_ne hle125 fun h125 => hne ?_
    refine Subgroup.eq_of_le_of_card_ge hRB ?_
    rw [h125, F.B_card]
    norm_num
  have hRfin : Finite ↥R := Finite.of_injective (Subgroup.inclusion hRB)
    (Subgroup.inclusion_injective hRB)
  have hcard25 : Nat.card R = 25 := by
    obtain ⟨k, hk⟩ := hdvd1
    have hpos : 0 < Nat.card R := Nat.card_pos
    have hk0 : 0 < k := by omega
    have hk5 : k < 5 := by omega
    interval_cases k
    · omega
    · rw [hk] at hdvd2
      norm_num at hdvd2
    · rw [hk] at hdvd2
      norm_num at hdvd2
    · rw [hk] at hdvd2
      norm_num at hdvd2
  symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard25, hcardK])

theorem card_R {u v : Fin 5} (huv : u ≠ v) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (F.J u v : Set G)) = 25 := by
  obtain ⟨σ, h3, h4⟩ := exists_perm_34 huv
  rw [← h3, ← h4, R_eq_BK F σ]
  have : B ⊓ Ksg F σ = conjBy (F.W σ) (B ⊓ K) := by
    unfold Ksg
    rw [conjBy_inf, Equivariance.conjBy_eq_of_mem_normalizer (F.W_B σ)]
  rw [this, card_conjBy, F.BK_card]

theorem R_sup_line {u v : Fin 5} (huv : u ≠ v) :
    (B ⊓ Subgroup.centralizer (F.J u v : Set G)) ⊔ (B ⊓ F.J u v) = B := by
  set R := B ⊓ Subgroup.centralizer (F.J u v : Set G) with hR
  have hBfin : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [F.B_card]; norm_num)
  have hsup : R ⊔ (B ⊓ F.J u v) ≤ B := sup_le inf_le_left inf_le_left
  have hne : ¬ (B ⊓ F.J u v ≤ R) := line_not_le_R F huv
  have hlt : R ≠ R ⊔ (B ⊓ F.J u v) := fun h => hne (h ▸ le_sup_right)
  have hcardR : Nat.card R = 25 := card_R F huv
  have hSfin : Finite ↥(R ⊔ (B ⊓ F.J u v)) := Finite.of_injective (Subgroup.inclusion hsup)
    (Subgroup.inclusion_injective hsup)
  have hdvd : 25 ∣ Nat.card ↥(R ⊔ (B ⊓ F.J u v)) :=
    hcardR ▸ Subgroup.card_dvd_of_le (le_sup_left : R ≤ R ⊔ (B ⊓ F.J u v))
  have hdvd2 : Nat.card ↥(R ⊔ (B ⊓ F.J u v)) ∣ 125 := by
    have := Subgroup.card_dvd_of_le hsup
    rwa [F.B_card] at this
  have hpos : 0 < Nat.card ↥(R ⊔ (B ⊓ F.J u v)) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by omega
  have hk5 : k ≤ 5 := by
    have := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  have hcard : Nat.card ↥(R ⊔ (B ⊓ F.J u v)) = 125 := by
    interval_cases k
    · exfalso
      apply hlt
      exact Subgroup.eq_of_le_of_card_ge (le_sup_left : R ≤ R ⊔ (B ⊓ F.J u v)) (by omega)
    · rw [hk] at hdvd2
      norm_num at hdvd2
    · rw [hk] at hdvd2
      norm_num at hdvd2
    · rw [hk] at hdvd2
      norm_num at hdvd2
    · omega
  exact Subgroup.eq_of_le_of_card_ge hsup (by rw [hcard, F.B_card]; norm_num)

theorem relIndex_R {u v : Fin 5} (huv : u ≠ v) :
    (B ⊓ Subgroup.centralizer (F.J u v : Set G)).relIndex B = 5 := by
  have h := card_mul_relIndex (inf_le_left : B ⊓ Subgroup.centralizer (F.J u v : Set G) ≤ B)
  rw [card_R F huv, F.B_card] at h
  omega

theorem relIndex_R_inf {u v u' v' : Fin 5} (huv : u ≠ v) (huv' : u' ≠ v')
    (hne : B ⊓ Subgroup.centralizer (F.J u v : Set G) ≠
      B ⊓ Subgroup.centralizer (F.J u' v' : Set G)) :
    (B ⊓ Subgroup.centralizer (F.J u v : Set G) ⊓
      (B ⊓ Subgroup.centralizer (F.J u' v' : Set G))).relIndex B = 25 := by
  set R := B ⊓ Subgroup.centralizer (F.J u v : Set G) with hR
  set R' := B ⊓ Subgroup.centralizer (F.J u' v' : Set G) with hR'
  have hBfin : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [F.B_card]; norm_num)
  have hRB : R ≤ B := inf_le_left
  have hcR : Nat.card R = 25 := card_R F huv
  have hcR' : Nat.card R' = 25 := card_R F huv'
  have hrel : (R ⊓ R').relIndex B ≤ 25 := by
    have h1 := Subgroup.relIndex_inf_le (H := R) (K := R') (L := B)
    rw [relIndex_R F huv, relIndex_R F huv'] at h1
    exact h1
  have hIB : R ⊓ R' ≤ B := inf_le_left.trans hRB
  have hmul := card_mul_relIndex hIB
  rw [F.B_card] at hmul
  have hRfin : Finite ↥R := Finite.of_injective (Subgroup.inclusion hRB)
    (Subgroup.inclusion_injective hRB)
  have hRB' : R' ≤ B := inf_le_left
  have hR'fin : Finite ↥R' := Finite.of_injective (Subgroup.inclusion hRB')
    (Subgroup.inclusion_injective hRB')
  have hcdvd : Nat.card ↥(R ⊓ R') ∣ 25 := hcR ▸ Subgroup.card_dvd_of_le inf_le_left
  have hge5 : 5 ≤ Nat.card ↥(R ⊓ R') := by
    by_contra h
    have h' := not_le.mp h
    have := Nat.mul_le_mul (Nat.le_of_lt_succ h') hrel
    omega
  have hne25 : Nat.card ↥(R ⊓ R') ≠ 25 := by
    intro h25
    apply hne
    have h1 : R ⊓ R' = R := Subgroup.eq_of_le_of_card_ge (inf_le_left : R ⊓ R' ≤ R)
      (by rw [h25, hcR])
    have h2 : R ⊓ R' = R' := Subgroup.eq_of_le_of_card_ge (inf_le_right : R ⊓ R' ≤ R')
      (by rw [h25, hcR'])
    exact h1.symm.trans h2
  have hcard5 : Nat.card ↥(R ⊓ R') = 5 := by
    have h52 : Nat.card ↥(R ⊓ R') ∣ 5 ^ 2 := by
      rw [show (5 : ℕ) ^ 2 = 25 by norm_num]
      exact hcdvd
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp h52
    interval_cases m
    · exfalso
      rw [hm'] at hge5
      norm_num at hge5
    · rw [hm']
      norm_num
    · exfalso
      rw [hm'] at hne25
      exact hne25 (by norm_num)
  rw [hcard5] at hmul
  omega

end Torus

end CFSG.RankThree.PartOne.CTP
