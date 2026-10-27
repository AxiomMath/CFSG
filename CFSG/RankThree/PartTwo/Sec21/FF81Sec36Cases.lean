module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81T0
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofCoprime
import CFSG.RankThree.PartTwo.Sec18.Item188Abs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S36

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}

theorem t₀_comm (ht₀L : t₀ ∈ CenS L) {l : G} (hl : l ∈ L) : l * t₀ = t₀ * l :=
  Subgroup.mem_centralizer_iff.mp ht₀L l hl

theorem t₀_mul_self (ht₀ : orderOf t₀ = 2) : t₀ * t₀ = 1 := by
  rw [← pow_two, ← ht₀]; exact pow_orderOf_eq_one t₀

theorem zpowers_normal_of_le_cen {U : Subgroup G} (hU : U ≤ Cen t₀) :
    ∀ u ∈ U, ∀ w ∈ Subgroup.zpowers t₀, u * w * u⁻¹ ∈ Subgroup.zpowers t₀ := fun u hu w hw =>
  (Subgroup.mem_normalizer_iff.mp
    (mem_nor_zpowers (Subgroup.mem_centralizer_singleton_iff.mp (hU hu))) w).mp hw

theorem t₀_mem_cenS_hyp (hB : FF81Basis b L B b₁ b₂ b₃) (ht₀L : t₀ ∈ CenS L) (i : Fin 13) :
    t₀ ∈ CenS (hyp b₁ b₂ b₃ i) :=
  Subgroup.centralizer_le ((hyp_le i).trans hB.B₁_le) ht₀L

theorem t₀_comm_ε3 (hB : FF81Basis b L B b₁ b₂ b₃) (ht₀L : t₀ ∈ CenS L)
    (x : Fin 3 → ZMod 3) : t₀ * ε3 b₁ b₂ b₃ x = ε3 b₁ b₂ b₃ x * t₀ :=
  (t₀_comm ht₀L (hB.B₁_le (ε3_mem x))).symm

theorem sl3_t₀ (hKF2 : KF_Sp6SL3) (hKF3 : KF_SL32Fix) (hB : FF81Basis b L B b₁ b₂ b₃)
    (ht₀ : orderOf t₀ = 2) (ht₀L : t₀ ∈ CenS L) {U : Subgroup G} (hU : IsPGroup 2 U)
    (ht₀U : t₀ ∈ U) (hUt : U ≤ Cen t₀) (hUL : L ≤ Nor U) {eU eUy : ℕ}
    (hcU : Nat.card U = 2 ^ eU) (hcUy : Nat.card ↥(U ⊓ Cen (b₁ * b₂)) = 2 ^ eUy) :
    eU + 4 ≤ 1 + 4 * eUy := by
  have hzy : Subgroup.zpowers t₀ ⊓ Cen (b₁ * b₂) = Subgroup.zpowers t₀ :=
    inf_eq_left.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (t₀_comm ht₀L (L.mul_mem hB.hb₁ hB.hb₂)).symm))
  have h := sl3_exp hKF2 hKF3 hB hU (Subgroup.zpowers_le.mpr ht₀U) (zpowers_normal_of_le_cen hUt)
    hUL (fun l hl => mem_nor_zpowers (t₀_comm ht₀L hl)) hcU
    (by rw [card_zpowers_t₀ ht₀, pow_one]) hcUy (by rw [hzy, card_zpowers_t₀ ht₀, pow_one])
  omega

theorem card_two_or_eight (hB : FF81Basis b L B b₁ b₂ b₃) {X : Subgroup G} (hXp : IsPGroup 2 X)
    (hXN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor X)
    (hXB : Nat.card ↥(X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) = 2) (i : Fin 13)
    (h8 : Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 8) :
    Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ∨ Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 8 := by
  have hE := card_hyp_modEq hB hXN i
  obtain ⟨n, hn⟩ := card_eq_two_pow (hXp.to_le (inf_le_left : X ⊓ CenS (hyp b₁ b₂ b₃ i) ≤ X))
  rw [hn, hXB] at hE
  have hodd := two_pow_odd_of_modEq hE
  rw [hn] at h8 ⊢
  have := pow_le_two_pow (n := 3) h8
  rcases (by omega : n = 1 ∨ n = 3) with rfl | rfl
  · left; rfl
  · right; rfl

theorem case33 (hKF : KF_Sp6RefS) (hKF2 : KF_Sp6SL3)
    (hKF3 : KF_SL32Fix) (hB : FF81Basis b L B b₁ b₂ b₃) (hbad : CaseBad b B)
    (ht₀ : orderOf t₀ = 2) (ht₀L : t₀ ∈ CenS L) (ht₀b : t₀ * b * t₀⁻¹ = b⁻¹)
    (hT' : ⁅Op 2 (Cen t₀), Op 2 (Cen t₀)⁆ ≤ Subgroup.zpowers t₀)
    (h2 : ∀ i, hypW i = 2 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ 3)
    (h3 : ∀ i, hypW i = 3 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ 3) :
    False := by
  set T := Op 2 (Cen t₀) with hT
  have hTp : IsPGroup 2 T := op_two_isPGroup t₀
  have hTt : T ≤ Cen t₀ := op_two_le t₀
  have ht₀T : t₀ ∈ T := mem_op_two_self ht₀
  have hTL : L ≤ Nor T := (le_cen_of_cenS ht₀L).trans cen_le_nor_op_two
  have hB₁N : Subgroup.closure {b₁, b₂, b₃} ≤ Nor T := hB.B₁_le.trans hTL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTB, -, -, -⟩ :=
    exps_of_le hKF hB hbad ht₀ ht₀L ht₀b hTL ht₀T le_rfl
  set Z := T ⊓ CenS T with hZ
  have hZT : Z ≤ T := inf_le_left
  have ht₀Z : t₀ ∈ Z := ⟨ht₀T, Subgroup.mem_centralizer_iff.mpr fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp (hTt hu)⟩
  have hZL : L ≤ Nor Z := fun l hl => mem_nor_inf (hTL hl) (mem_nor_cenS_of_mem_nor (hTL hl))
  obtain ⟨αZ, γZ, eZ, eZy, hαZ, hγZ, heZ, heZy, hcZ, hcZy, -, -, h2Z, h3Z⟩ :=
    exps_of_le hKF hB hbad ht₀ ht₀L ht₀b hZL ht₀Z hZT
  have hγZ1 : γZ = 1 := by
    rcases hγZ with h | h
    · exact h
    exfalso
    obtain ⟨u, hu, v, hv, huv⟩ :=
      ((local_bound hKF hB hbad ht₀ ht₀L ht₀b 11).2.2 rfl).2 (by rw [h3 11 rfl]; norm_num)
    have heq : Z ⊓ CenS (hyp b₁ b₂ b₃ 11) = T ⊓ CenS (hyp b₁ b₂ b₃ 11) :=
      Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hZT) (by rw [h3 11 rfl, h3Z 11 rfl, h])
    have hu' : u ∈ Z ⊓ CenS (hyp b₁ b₂ b₃ 11) := by rw [heq]; exact hu
    exact huv (Subgroup.mem_centralizer_iff.mp hu'.1.2 v hv.1).symm
  have hsZ := sl3_t₀ hKF2 hKF3 hB ht₀ ht₀L (hTp.to_le hZT) ht₀Z (hZT.trans hTt) hZL hcZ hcZy
  have hαZ1 : αZ = 1 := by omega
  set Q₀ := T ⊓ CenS (hyp b₁ b₂ b₃ 4) with hQ₀
  obtain ⟨-, hQab, -⟩ := (local_bound hKF hB hbad ht₀ ht₀L ht₀b 4).2.1 rfl
  have hle : ∀ i, T ⊓ CenS (hyp b₁ b₂ b₃ i) ≤ T ⊓ CenS Q₀ := by
    intro i u hu
    refine ⟨hu.1, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    by_cases hi : i = 4
    · subst hi; exact hQab v hv u hu
    · exact (comm_of_hyp_ne hB hTp hTt hB₁N (t₀_mul_self ht₀) hT' hTB.le hi hu hv).symm
  have hXN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor (T ⊓ CenS Q₀) := fun β hβ =>
    mem_nor_inf (hB₁N hβ) (mem_nor_cenS_of_mem_nor (mem_nor_inf_cenS_hyp hB hβ (hB₁N hβ) 4))
  have hXT := eq_of_cen_hyp_le hB hTp inf_le_left hXN hB₁N hle
  have hQZ : Q₀ ≤ Z ⊓ CenS (hyp b₁ b₂ b₃ 4) := by
    intro q hq
    refine ⟨⟨hq.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, hq.2⟩
    have ht' : t ∈ T ⊓ CenS Q₀ := by rw [hXT]; exact ht
    exact (Subgroup.mem_centralizer_iff.mp ht'.2 q hq).symm
  have := Subgroup.card_le_of_le hQZ
  rw [h2 4 rfl, h2Z 4 rfl, hαZ1] at this
  norm_num at this

theorem case13 (hKF : KF_Sp6RefS) (hB : FF81Basis b L B b₁ b₂ b₃)
    (hbad : CaseBad b B) (ht₀ : orderOf t₀ = 2) (ht₀L : t₀ ∈ CenS L) (ht₀b : t₀ * b * t₀⁻¹ = b⁻¹)
    (hT' : ⁅Op 2 (Cen t₀), Op 2 (Cen t₀)⁆ ≤ Subgroup.zpowers t₀)
    (h2 : ∀ i, hypW i = 2 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ 1)
    (h3 : ∀ i, hypW i = 3 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 ^ 3)
    (hcy : Nat.card ↥(Op 2 (Cen t₀) ⊓ Cen (b₁ * b₂)) = 2 ^ 5) : False := by
  set T := Op 2 (Cen t₀) with hT
  have hTp : IsPGroup 2 T := op_two_isPGroup t₀
  have hTt : T ≤ Cen t₀ := op_two_le t₀
  have ht₀T : t₀ ∈ T := mem_op_two_self ht₀
  have hTL : L ≤ Nor T := (le_cen_of_cenS ht₀L).trans cen_le_nor_op_two
  have hB₁N : Subgroup.closure {b₁, b₂, b₃} ≤ Nor T := hB.B₁_le.trans hTL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hTB, h1, -, -⟩ :=
    exps_of_le hKF hB hbad ht₀ ht₀L ht₀b hTL ht₀T le_rfl
  obtain ⟨hTc, hTs⟩ := coprime_solvable_of_two hTp
  have h2' : ∀ i, hypW i = 2 → T ⊓ CenS (hyp b₁ b₂ b₃ i) = Subgroup.zpowers t₀ := fun i h =>
    eq_zpowers_of_card ht₀ ⟨ht₀T, t₀_mem_cenS_hyp hB ht₀L i⟩ (by rw [h2 i h]; norm_num)
  have hcT : ∀ i, Nat.card ↥(T ⊓ CenS (hyp b₁ b₂ b₃ i)) = if hypW i = 3 then 8 else 2 := by
    intro i
    have hw : hypW i = 1 ∨ hypW i = 2 ∨ hypW i = 3 := by
      have := (by decide : ∀ j : Fin 13, hypW j = 1 ∨ hypW j = 2 ∨ hypW j = 3) i; exact this
    rcases hw with h | h | h
    · rw [h1 i h, card_zpowers_t₀ ht₀, if_neg (by omega)]
    · rw [h2' i h, card_zpowers_t₀ ht₀, if_neg (by omega)]
    · rw [h3 i h, if_pos h]; norm_num
  have hTB2 : Nat.card ↥(T ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) = 2 := by
    rw [hTB, card_zpowers_t₀ ht₀]
  obtain ⟨S₂, hS₂p, hS₂8, hS₂C, hS₂N⟩ := ((local_bound hKF hB hbad ht₀ ht₀L ht₀b 4).2.1 rfl).2.2
  have hS₂t : ∀ σ ∈ S₂, σ ∈ Cen t₀ := fun σ h => (hS₂C h).2
  have hS₂T : ∀ σ ∈ S₂, σ ∈ Nor T := fun σ h => cen_le_nor_op_two (hS₂t σ h)
  have hcomm4 : ∀ σ ∈ S₂, ∀ z, dot (hypF 4) z = 0 → ε3 b₁ b₂ b₃ z * σ = σ * ε3 b₁ b₂ b₃ z :=
    fun σ hσ z hz => Subgroup.mem_centralizer_iff.mp (hS₂C hσ).1 _ ((hB.mem_hyp 4 z).2 hz)
  have ht₀S : ∀ σ ∈ S₂, t₀ * σ = σ * t₀ := fun σ h =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hS₂t σ h)).symm
  have ht₀S' : t₀ ∈ CenS S₂ := Subgroup.mem_centralizer_iff.mpr fun σ h => (ht₀S σ h).symm
  set y : Fin 3 → ZMod 3 := ![1, 1, 0] with hy
  have hβy : ∀ β ∈ Subgroup.closure {b₁, b₂, b₃}, β * ε3 b₁ b₂ b₃ y = ε3 b₁ b₂ b₃ y * β :=
    fun β hβ => hB.B₁_comm hβ (ε3_mem y)
  have hcyT : Nat.card ↥(T ⊓ Cen (ε3 b₁ b₂ b₃ y)) = 2 ^ 5 := by rw [hy, ε3_y]; exact hcy
  have hviaZ : ∀ k : Fin 13, ∀ z : Fin 3 → ZMod 3, hypW k = 3 → dot (hypF k) z = 0 →
      dot (hypF 4) z = 0 → dot (hypF k) y ≠ 0 → z ≠ 0 →
      (∏ i ∈ Finset.univ.filter (fun i => dot (hypF i) z = 0),
        (if hypW i = 3 then 8 else 2)) = 64 →
      T ⊓ CenS (hyp b₁ b₂ b₃ k) ≤ CenS S₂ := by
    intro k z hk hzk hz4 hyk hz0 hprod
    have hzk' := (hB.mem_hyp k z).2 hzk
    have hW := card_cen_mul_pow_three hB hB₁N hTc hTs hz0
    rw [hTB2, Finset.prod_congr rfl fun i _ => hcT i, hprod] at hW
    have hYz : T ⊓ CenS (hyp b₁ b₂ b₃ k) = T ⊓ Cen (ε3 b₁ b₂ b₃ z) :=
      Subgroup.eq_of_le_of_card_ge
        (inf_le_inf_left _ fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hu _ hzk').symm)
        (by rw [h3 k hk]; omega)
    refine le_cenS_of_axb (Y := T ⊓ CenS (hyp b₁ b₂ b₃ k)) (S := S₂) (x := ε3 b₁ b₂ b₃ y)
      (hTp.to_le inf_le_left) (by rw [h3 k hk]; norm_num) hS₂p ?_ (hB.orderOf_ε3 (by decide))
      (mem_nor_inf_cenS_hyp hB (ε3_mem _) (hB₁N (ε3_mem _)) k)
      (fun σ hσ => hcomm4 σ hσ _ (by decide)) ht₀ ⟨ht₀T, t₀_mem_cenS_hyp hB ht₀L k⟩ ht₀S
      (t₀_comm_ε3 hB ht₀L y) (by rw [inf_cenS_hyp_inf_cen hB T k hyk, hTB])
    rw [hYz]
    exact fun σ hσ => mem_nor_inf (hS₂T σ hσ) (mem_nor_cen (hcomm4 σ hσ z hz4).symm)
  have hT9 := hviaZ 9 ![1, 1, 1] rfl (by decide) (by decide) (by decide) (by decide) (by decide)
  have hT10 := hviaZ 10 ![1, 1, 2] rfl (by decide) (by decide) (by decide) (by decide)
    (by decide)
  set e₃ : Fin 3 → ZMod 3 := ![0, 0, 1] with he₃
  have hb₃ord : orderOf (ε3 b₁ b₂ b₃ e₃) = 3 := hB.orderOf_ε3 (by decide)
  have hb₃S : ∀ σ ∈ S₂, ε3 b₁ b₂ b₃ e₃ * σ = σ * ε3 b₁ b₂ b₃ e₃ := fun σ hσ =>
    hcomm4 σ hσ _ (by decide)
  set P := T ⊓ Cen (ε3 b₁ b₂ b₃ y) with hP
  have hPp : IsPGroup 2 P := hTp.to_le inf_le_left
  have hS₂P : S₂ ≤ Nor P := fun σ hσ =>
    mem_nor_inf (hS₂T σ hσ) (mem_nor_cen (hcomm4 σ hσ y (by decide)).symm)
  have hb₃P : ε3 b₁ b₂ b₃ e₃ ∈ Nor P :=
    mem_nor_inf (hB₁N (ε3_mem _)) (mem_nor_cen (hβy _ (ε3_mem _)))
  have hP4 : P ⊓ Cen (ε3 b₁ b₂ b₃ e₃) ≤ Subgroup.zpowers t₀ := by
    rw [← h2' 4 rfl]
    rintro u ⟨⟨huT, huy⟩, hub⟩
    refine ⟨huT, ?_⟩
    show u ∈ CenS (Subgroup.closure {ε3 b₁ b₂ b₃ y, ε3 b₁ b₂ b₃ e₃})
    exact mem_cenS_pair.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp huy,
      Subgroup.mem_centralizer_singleton_iff.mp hub⟩
  set Q := P ⊓ CenS S₂ with hQ
  have ht₀Q : t₀ ∈ Q := ⟨⟨ht₀T, Subgroup.mem_centralizer_singleton_iff.mpr
    (t₀_comm_ε3 hB ht₀L y)⟩, ht₀S'⟩
  have hQb₃ : ¬ Q ≤ Cen (ε3 b₁ b₂ b₃ e₃) := by
    intro hle
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers (ε3 b₁ b₂ b₃ e₃))) 2 := by
      rw [Nat.card_zpowers, hb₃ord]; norm_num
    have hRB : ⁅Subgroup.zpowers (ε3 b₁ b₂ b₃ e₃), S₂⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_iff.mpr fun s hs => (hb₃S s hs).symm)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPb := CFSG.RankThree.PartTwo.Sec18.Item188Proof.centralizes_of_thompson_AxB
      (p := 2) (P := P) (R := Subgroup.zpowers (ε3 b₁ b₂ b₃ e₃)) (B := S₂) hPp hcop hS₂p
      (Subgroup.zpowers_le.mpr hb₃P) hS₂P hRB (by
        intro d hd
        have : d ∈ Cen (ε3 b₁ b₂ b₃ e₃) := hle hd
        rw [← cenS_zpowers] at this
        exact this)
    rw [← CenS, cenS_zpowers] at hPb
    have h := Subgroup.card_le_of_le ((le_inf le_rfl hPb).trans hP4)
    rw [hcyT, card_zpowers_t₀ ht₀] at h
    norm_num at h
  have hQ4 : 4 ≤ Nat.card Q := by
    obtain ⟨n, hn⟩ := card_eq_two_pow (hPp.to_le (inf_le_left : Q ≤ P))
    rw [hn]
    by_contra hlt
    have hn1 : n ≤ 1 := by
      by_contra h
      exact hlt (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega))
    have hQz := eq_zpowers_of_card ht₀ ht₀Q (by
      rw [hn]; calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
        _ = 2 := by norm_num)
    exact hQb₃ (hQz.le.trans (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (t₀_comm_ε3 hB ht₀L e₃))))
  have hQN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor Q := fun β hβ =>
    mem_nor_inf (mem_nor_inf (hB₁N hβ) (mem_nor_cen (hβy β hβ)))
      (mem_nor_cenS_of_mem_nor (hS₂N hβ))
  have hQT : Q ≤ T := inf_le_left.trans inf_le_left
  have hQp : IsPGroup 2 Q := hTp.to_le hQT
  obtain ⟨hQc, hQs⟩ := coprime_solvable_of_two hQp
  have hsmall : ∀ X : Subgroup G, X ≤ T → t₀ ∈ X → ∀ i, hypW i ≠ 3 →
      Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) = 2 := by
    intro X hXT ht₀X i hi
    refine le_antisymm ?_ ?_
    · have := Subgroup.card_le_of_le (inf_le_inf_right (CenS (hyp b₁ b₂ b₃ i)) hXT)
      rw [hcT i, if_neg hi] at this; exact this
    · rw [← card_zpowers_t₀ ht₀]
      exact Subgroup.card_le_of_le (zpowers_le_inf_cenS ht₀L ht₀X ((hyp_le i).trans hB.B₁_le))
  have hBX : ∀ X : Subgroup G, X ≤ T → t₀ ∈ X →
      Nat.card ↥(X ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) = 2 := by
    intro X hXT ht₀X
    refine le_antisymm ?_ ?_
    · have := Subgroup.card_le_of_le
        (inf_le_inf_right (CenS (Subgroup.closure {b₁, b₂, b₃})) hXT)
      rwa [hTB2] at this
    · rw [← card_zpowers_t₀ ht₀]
      exact Subgroup.card_le_of_le (zpowers_le_inf_cenS ht₀L ht₀X hB.B₁_le)
  have hle8 : ∀ X : Subgroup G, X ≤ T → ∀ i, hypW i = 3 →
      Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 8 := by
    intro X hXT i hi
    have := Subgroup.card_le_of_le (inf_le_inf_right (CenS (hyp b₁ b₂ b₃ i)) hXT)
    rwa [hcT i, if_pos hi] at this
  have hQW := card_cen_mul_pow_three hB hQN hQc hQs (x := y) (by decide)
  rw [inf_eq_left.mpr (inf_le_left.trans inf_le_right : Q ≤ Cen (ε3 b₁ b₂ b₃ y)),
    hBX Q hQT ht₀Q, hy, filter_y, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, hsmall Q hQT ht₀Q 2 (by decide),
    hsmall Q hQT ht₀Q 4 (by decide)] at hQW
  have hQ11 := card_two_or_eight hB hQp hQN (hBX Q hQT ht₀Q) 11 (hle8 Q hQT 11 rfl)
  have hQ12 := card_two_or_eight hB hQp hQN (hBX Q hQT ht₀Q) 12 (hle8 Q hQT 12 rfl)
  have hTQ : ∀ k : Fin 13, hypW k = 3 → Nat.card ↥(Q ⊓ CenS (hyp b₁ b₂ b₃ k)) = 8 →
      T ⊓ CenS (hyp b₁ b₂ b₃ k) ≤ CenS S₂ := by
    intro k hk h8
    have heq : Q ⊓ CenS (hyp b₁ b₂ b₃ k) = T ⊓ CenS (hyp b₁ b₂ b₃ k) :=
      Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hQT) (by rw [h8, h3 k hk]; norm_num)
    rw [← heq]
    exact inf_le_left.trans inf_le_right
  have hother : ∀ k m : Fin 13, (k = 11 ∧ m = 12) ∨ (k = 12 ∧ m = 11) →
      T ⊓ CenS (hyp b₁ b₂ b₃ k) ≤ CenS S₂ → T ⊓ CenS (hyp b₁ b₂ b₃ m) ≤ CenS S₂ := by
    intro k m hkm hk
    have hf : hypW k = 3 ∧ hypW m = 3 ∧ k ≠ m ∧ dot (hypF k) y = 0 ∧ dot (hypF m) y = 0 ∧
        dot (hypF m) e₃ ≠ 0 := by
      rcases hkm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    obtain ⟨hk3, hm3, hkm', hky, hmy, hme⟩ := hf
    set Tk := T ⊓ CenS (hyp b₁ b₂ b₃ k) with hTk
    set Tm := T ⊓ CenS (hyp b₁ b₂ b₃ m) with hTm
    set X := P ⊓ CenS Tk with hX
    have hXT : X ≤ T := inf_le_left.trans inf_le_left
    have ht₀X : t₀ ∈ X := ⟨⟨ht₀T, Subgroup.mem_centralizer_singleton_iff.mpr
      (t₀_comm_ε3 hB ht₀L y)⟩, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        Subgroup.mem_centralizer_singleton_iff.mp (hTt hu.1)⟩
    have hTmX : Tm ≤ X := by
      intro u hu
      refine ⟨⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hu.2 _ ((hB.mem_hyp m y).2 hmy)).symm⟩,
        Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      exact comm_of_hyp_ne hB hTp hTt hB₁N (t₀_mul_self ht₀) hT' hTB.le hkm' hv hu
    have hXN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor X := fun β hβ =>
      mem_nor_inf (mem_nor_inf (hB₁N hβ) (mem_nor_cen (hβy β hβ)))
        (mem_nor_cenS_of_mem_nor (mem_nor_inf_cenS_hyp hB hβ (hB₁N hβ) k))
    have hXp : IsPGroup 2 X := hTp.to_le hXT
    obtain ⟨hXc, hXs⟩ := coprime_solvable_of_two hXp
    have hXk : Nat.card ↥(X ⊓ CenS (hyp b₁ b₂ b₃ k)) = 2 := by
      rcases card_two_or_eight hB hXp hXN (hBX X hXT ht₀X) k (hle8 X hXT k hk3) with h | h
      · exact h
      exfalso
      obtain ⟨u, hu, v, hv, huv⟩ :=
        ((local_bound hKF hB hbad ht₀ ht₀L ht₀b k).2.2 hk3).2 (by rw [h3 k hk3]; norm_num)
      have heq : X ⊓ CenS (hyp b₁ b₂ b₃ k) = Tk :=
        Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hXT) (by rw [h, hTk, h3 k hk3]; norm_num)
      have hu' : u ∈ X ⊓ CenS (hyp b₁ b₂ b₃ k) := by rw [heq]; exact hu
      exact huv (Subgroup.mem_centralizer_iff.mp hu'.1.2 v hv).symm
    have hXW := card_cen_mul_pow_three hB hXN hXc hXs (x := y) (by decide)
    rw [inf_eq_left.mpr (inf_le_left.trans inf_le_right : X ≤ Cen (ε3 b₁ b₂ b₃ y)),
      hBX X hXT ht₀X, hy, filter_y] at hXW
    have hXm := hle8 X hXT m hm3
    have hX8 : Nat.card X ≤ 8 := by
      rcases hkm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
          Finset.prod_insert (by decide), Finset.prod_singleton, hsmall X hXT ht₀X 2 (by decide),
          hsmall X hXT ht₀X 4 (by decide), hXk] at hXW
        nlinarith
      · rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
          Finset.prod_insert (by decide), Finset.prod_singleton, hsmall X hXT ht₀X 2 (by decide),
          hsmall X hXT ht₀X 4 (by decide), hXk] at hXW
        nlinarith
    have hXTm : Tm = X := Subgroup.eq_of_le_of_card_ge hTmX (by rw [hTm, h3 m hm3]; norm_num; exact hX8)
    have hS₂m : S₂ ≤ Nor Tm := by
      rw [hXTm]
      exact fun σ hσ => mem_nor_inf (hS₂P hσ) (mem_nor_cenS fun h hh =>
        (Subgroup.mem_centralizer_iff.mp (hk hh) σ hσ))
    exact le_cenS_of_axb (Y := Tm) (S := S₂) (x := ε3 b₁ b₂ b₃ e₃) (hTp.to_le inf_le_left)
      (by rw [hTm, h3 m hm3]; norm_num) hS₂p hS₂m hb₃ord
      (mem_nor_inf_cenS_hyp hB (ε3_mem _) (hB₁N (ε3_mem _)) m) hb₃S ht₀
      ⟨ht₀T, t₀_mem_cenS_hyp hB ht₀L m⟩ ht₀S (t₀_comm_ε3 hB ht₀L e₃)
      (by rw [hTm, inf_cenS_hyp_inf_cen hB T m hme, hTB])
  have hT1112 : T ⊓ CenS (hyp b₁ b₂ b₃ 11) ≤ CenS S₂ ∧ T ⊓ CenS (hyp b₁ b₂ b₃ 12) ≤ CenS S₂ := by
    rcases hQ11 with h11 | h11
    · rcases hQ12 with h12 | h12
      · exfalso
        have hQW' : Nat.card Q * 2 ^ 3 = 2 * (2 * (2 * 2)) := by rw [h11, h12] at hQW; exact hQW
        norm_num at hQW'; omega
      · have := hTQ 12 rfl h12
        exact ⟨hother 12 11 (Or.inr ⟨rfl, rfl⟩) this, this⟩
    · have := hTQ 11 rfl h11
      exact ⟨this, hother 11 12 (Or.inl ⟨rfl, rfl⟩) this⟩
  have hle : ∀ i, T ⊓ CenS (hyp b₁ b₂ b₃ i) ≤ T ⊓ CenS S₂ := by
    intro i
    refine le_inf inf_le_left ?_
    by_cases hi : hypW i = 3
    · have : i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by
        revert hi; revert i; decide
      rcases this with rfl | rfl | rfl | rfl
      · exact hT9
      · exact hT10
      · exact hT1112.1
      · exact hT1112.2
    · have hz : T ⊓ CenS (hyp b₁ b₂ b₃ i) = Subgroup.zpowers t₀ :=
        eq_zpowers_of_card ht₀ ⟨ht₀T, t₀_mem_cenS_hyp hB ht₀L i⟩ (by rw [hcT i, if_neg hi])
      rw [hz]
      exact Subgroup.zpowers_le.mpr ht₀S'
  have hXN : Subgroup.closure {b₁, b₂, b₃} ≤ Nor (T ⊓ CenS S₂) := fun β hβ =>
    mem_nor_inf (hB₁N hβ) (mem_nor_cenS_of_mem_nor (hS₂N hβ))
  have hXT := eq_of_cen_hyp_le hB hTp inf_le_left hXN hB₁N hle
  have hS₂T' : S₂ ≤ T ⊓ CenS (hyp b₁ b₂ b₃ 4) := by
    intro σ hσ
    refine ⟨hB.mem_op_two_of_comm ht₀ (hS₂t σ hσ) fun u hu => ?_, (hS₂C hσ).1⟩
    have hu' : u ∈ T ⊓ CenS S₂ := by rw [hXT]; exact hu
    exact Subgroup.mem_centralizer_iff.mp hu'.2 σ hσ
  have := Subgroup.card_le_of_le hS₂T'
  rw [hS₂8, h2 4 rfl] at this
  norm_num at this

theorem ff81_3_6_of (hKF : KF_Sp6RefS) (hKF2 : KF_Sp6SL3)
    (hKF3 : KF_SL32Fix) (hB : FF81Basis b L B b₁ b₂ b₃) (hbad : CaseBad b B) : False := by
  obtain ⟨t₀, ht₀, ht₀L, ht₀b⟩ := ff81_t0 G b L B b₁ b₂ b₃ hB hB.cenOdd
  set T := Op 2 (Cen t₀) with hT
  have hTp : IsPGroup 2 T := op_two_isPGroup t₀
  have hTt : T ≤ Cen t₀ := op_two_le t₀
  have ht₀T : t₀ ∈ T := mem_op_two_self ht₀
  have hTL : L ≤ Nor T := (le_cen_of_cenS ht₀L).trans cen_le_nor_op_two
  obtain ⟨α, γ, e₀, ey, hα, hγ, he₀, hey, hc₀, hcy, -, -, h2, h3⟩ :=
    exps_of_le hKF hB hbad ht₀ ht₀L ht₀b hTL ht₀T le_rfl
  have hbot := sl3_exp hKF2 hKF3 hB hTp bot_le
    (fun u _ w hw => by rw [Subgroup.mem_bot] at hw ⊢; rw [hw, mul_one, mul_inv_cancel]) hTL
    (fun _ _ => Subgroup.mem_normalizer_fintype fun w hw => by
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hw ⊢; rw [hw, mul_one, mul_inv_cancel])
    hc₀ (by rw [Subgroup.card_bot, pow_zero]) hcy (by rw [bot_inf_eq, Subgroup.card_bot, pow_zero])
  have h11 : ¬ (α = 1 ∧ γ = 1) := by
    rintro ⟨rfl, rfl⟩
    have hTz : T = Subgroup.zpowers t₀ :=
      eq_zpowers_of_card ht₀ ht₀T (by rw [hc₀, show e₀ = 1 by omega]; norm_num)
    have hb₁T : b₁ ∈ T := hB.mem_op_two_of_comm ht₀ (le_cen_of_cenS ht₀L hB.hb₁) fun u hu => by
      rw [← hT, hTz] at hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_right (t₀_comm ht₀L hB.hb₁) k).eq
    have hord : orderOf b₁ = 3 := by
      have := hB.orderOf_ε3 (x := ![1, 0, 0]) (by decide)
      rwa [ε3_b₁] at this
    have hdvd := Subgroup.orderOf_dvd_natCard T hb₁T
    rw [hord, hc₀, show e₀ = 1 by omega] at hdvd
    norm_num at hdvd
  have hγ3 : γ = 3 := by omega
  set W := ⁅T, T⁆ ⊔ Subgroup.zpowers t₀ with hW
  have hTT : ⁅T, T⁆ ≤ T := Subgroup.commutator_le.mpr fun a ha c hc => by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem ha hc) (T.inv_mem ha)) (T.inv_mem hc)
  have hWT : W ≤ T := sup_le hTT (Subgroup.zpowers_le.mpr ht₀T)
  have ht₀W : t₀ ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have hWL : L ≤ Nor W := fun l hl =>
    mem_nor_sup (mem_nor_commutator (hTL hl)) (mem_nor_zpowers (t₀_comm ht₀L hl))
  have hWn : ∀ u ∈ T, ∀ w ∈ W, u * w * u⁻¹ ∈ W := fun u hu w hw => by
    have hc : u * w * u⁻¹ * w⁻¹ ∈ W := Subgroup.mem_sup_left (by
      rw [← commutatorElement_def]; exact Subgroup.commutator_mem_commutator hu (hWT hw))
    have := W.mul_mem hc hw
    rwa [inv_mul_cancel_right] at this
  obtain ⟨αW, γW, eW, eWy, hαW, hγW, heW, heWy, hcW, hcWy, -, -, h2W, h3W⟩ :=
    exps_of_le hKF hB hbad ht₀ ht₀L ht₀b hWL ht₀W hWT
  have hαle : αW ≤ α := by
    have := Subgroup.card_le_of_le (inf_le_inf_right (CenS (hyp b₁ b₂ b₃ 4)) hWT)
    rw [h2W 4 rfl, h2 4 rfl] at this
    exact pow_le_two_pow this
  have hγle : γW ≤ γ := by
    have := Subgroup.card_le_of_le (inf_le_inf_right (CenS (hyp b₁ b₂ b₃ 11)) hWT)
    rw [h3W 11 rfl, h3 11 rfl] at this
    exact pow_le_two_pow this
  have hne : ¬ (αW = α ∧ γW = γ) := by
    rintro ⟨hαe, hγe⟩
    have heq : W = T := Subgroup.eq_of_le_of_card_ge hWT (by
      rw [hcW, hc₀, show eW = e₀ by omega])
    have hle : T ≤ Subgroup.zpowers t₀ :=
      CFSG.RankThree.PartTwo.Sec17.Proof171Steps.le_of_le_sup_commutator_of_isPGroup
        Nat.prime_two hTp (Subgroup.zpowers_le.mpr ht₀T)
        (heq.symm.trans (hW.trans (sup_comm _ _))).le
    have := Subgroup.card_le_of_le hle
    rw [hc₀, card_zpowers_t₀ ht₀] at this
    have := pow_le_two_pow (e := e₀) (n := 1) (by rw [pow_one]; exact this)
    omega
  have hsW := sl3_t₀ hKF2 hKF3 hB ht₀ ht₀L (hTp.to_le hWT) ht₀W (hWT.trans hTt) hWL hcW hcWy
  have hsTW := sl3_exp hKF2 hKF3 hB hTp hWT hWn hTL hWL hc₀ hcW hcy hcWy
  have hW1 : eW = 1 := by omega
  have hWz : W = Subgroup.zpowers t₀ :=
    eq_zpowers_of_card ht₀ ht₀W (by rw [hcW, hW1]; norm_num)
  have hT' : ⁅T, T⁆ ≤ Subgroup.zpowers t₀ := le_sup_left.trans hWz.le
  rcases hα with rfl | rfl
  · exact case13 hKF hB hbad ht₀ ht₀L ht₀b hT' h2 (hγ3 ▸ h3)
      (by rw [hcy, show ey = 5 by omega])
  · exact case33 hKF hKF2 hKF3 hB hbad ht₀ ht₀L ht₀b hT' h2 (hγ3 ▸ h3)

end S36

theorem ff81_3_6 (hKF : KF_Sp6RefS) (hKF2 : KF_Sp6SL3)
    (hKF3 : KF_SL32Fix) : FF81_3_6 :=
  fun _ _ _ _ _ _ _ _ _ hB hbad => S36.ff81_3_6_of hKF hKF2 hKF3 hB hbad

end CFSG.RankThree.PartTwo.Sec21.FF81
