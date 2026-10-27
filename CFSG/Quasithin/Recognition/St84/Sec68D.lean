module

public import CFSG.Quasithin.Recognition.St84.Sec68C

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

@[expose] def X0 : Subgroup G := X.Z 4 ⊔ X.Z (-4)

private theorem Z_one_le_Gi_neg_two_two_four (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s) (hodd : Odd s)
    (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.Z 1 ≤ X.Gi (-2) ∧ X.Z 1 ≤ X.Gi 2 ∧ X.Z 1 ≤ X.Gi 4 := by
  have hb := X.Z_one_b_facts hc (Or.inl hn0) hs hodd h5 hX hGT hreg
  have hm2 : X.Z 1 ≤ X.Gi (-2) := fun z hz => (Subgroup.mem_inf.mp (hb.1 hz)).1
  have h4 : X.Z 1 ≤ X.Gi 4 := fun z hz => (Subgroup.mem_inf.mp (hb.1 hz)).2
  have h2 : X.Z 1 ≤ X.Gi 2 := fun z hz =>
    X.mem_Gi_of_between (hm2 hz) (h4 hz) (by omega) (by omega)
  exact ⟨hm2, h2, h4⟩

private theorem Z_one_le_Q_neg_one (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.Z 1 ≤ X.Q (-1) :=
  X.Z_le_Q_of_le_Gi 1 (-2) (-1)
    (X.Z_one_le_Gi_neg_two_two_four hc hn0 hs hodd h5 hX hGT hreg).1
    (Or.inr ⟨by norm_num, by norm_num⟩)

private theorem V0_le_A (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.V0 ≤ X.A := by
  rw [X.V0_eq_Z_one_sup_Z_neg_one hc hn0 hs hodd h5 hX
    hGT hreg]
  exact sup_le (le_inf (X.Z_le_Q 1) (X.Z_one_le_Q_neg_one hc hn0 hs hodd h5 hX hGT hreg))
    (le_inf (X.Z_neg_one_le_Q_one hc hn0 hs hodd h5 hX hGT hreg) (X.Z_le_Q (-1)))

private theorem X0_le_L (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.X0 ≤ X.L 0 := by
  rw [X.L_zero_eq_Z_four_sup hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
  exact le_sup_left

theorem commutator_A_X0_le (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ⁅X.A, X.X0⁆ ≤ X.V0 := by
  have hNV : X.X0 ≤ Subgroup.normalizer (X.V0 : Set G) :=
    (X.X0_le_L hc hn0 hs hodd h5 hX hGT hreg).trans
      ((X.L_le_Gi 0).trans (X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg))
  have hV0 : X.V0 = X.Z 1 ⊔ X.Z (-1) :=
    X.V0_eq_Z_one_sup_Z_neg_one hc hn0 hs hodd h5 hX hGT hreg
  have h4 : ⁅X.A, X.Z 4⁆ ≤ X.V0 :=
    (X.commutator_A_Z_four_le hc hn0 hs hodd h5 hX hGT hreg).trans (by
      rw [hV0]; exact le_sup_left)
  have hm4 : ⁅X.A, X.Z (-4)⁆ ≤ X.V0 :=
    (X.commutator_A_Z_neg_four_le hc hn0 hs hodd h5 hX hGT hreg).trans (by
      rw [hV0]; exact le_sup_right)
  have h4N : X.Z 4 ≤ Subgroup.normalizer (X.V0 : Set G) := fun z hz =>
    hNV (Subgroup.mem_sup_left hz)
  have hm4N : X.Z (-4) ≤ Subgroup.normalizer (X.V0 : Set G) := fun z hz =>
    hNV (Subgroup.mem_sup_right hz)
  have h := CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
    (X.Z 4) (X.Z (-4)) X.A X.V0 ((Subgroup.commutator_comm _ _).trans_le h4)
    ((Subgroup.commutator_comm _ _).trans_le hm4) h4N hm4N
  rw [Subgroup.commutator_comm]
  simpa [Setup.X0] using h

private def Cmod : Subgroup G := relCent (X.L 0) X.V0 X.A

private theorem mem_Cmod (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {g : G} :
    g ∈ X.Cmod ↔ g ∈ X.L 0 ∧ ∀ a ∈ X.A, ⁅g, a⁆ ∈ X.V0 :=
  mem_relCent ((X.L_le_Gi 0).trans (X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg))

private theorem X0_le_Cmod (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.X0 ≤ X.Cmod := by
  intro z hz
  rw [mem_Cmod X hc hn0 hs hodd h5 hX hGT hreg]
  refine ⟨X.X0_le_L hc hn0 hs hodd h5 hX hGT hreg hz, fun a ha => ?_⟩
  have h := (Subgroup.commutator_le.mp
    (X.commutator_A_X0_le hc hn0 hs hodd h5 hX hGT hreg)) a ha z hz
  rw [← commutatorElement_inv a z]
  exact X.V0.inv_mem h

private theorem conj_mem_Cmod (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {x y : G} (hx : x ∈ X.L 0)
    (hy : y ∈ X.Cmod) : x⁻¹ * y * x ∈ X.Cmod := by
  rw [mem_Cmod X hc hn0 hs hodd h5 hX hGT hreg] at hy ⊢
  obtain ⟨hyL, hyA⟩ := hy
  have hxG : x ∈ X.Gi 0 := X.L_le_Gi 0 hx
  have hxn : x ∈ Subgroup.normalizer (X.A : Set G) :=
    X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg hxG
  refine ⟨(X.L 0).mul_mem ((X.L 0).mul_mem ((X.L 0).inv_mem hx) hyL) hx, ?_⟩
  intro a ha
  have ha' : x * a * x⁻¹ ∈ X.A := (Subgroup.mem_normalizer_iff.mp hxn a).mp ha
  have h1 : ⁅y, x * a * x⁻¹⁆ ∈ X.V0 := hyA _ ha'
  have hxN : x⁻¹ ∈ Subgroup.normalizer (X.V0 : Set G) :=
    (X.L_le_Gi 0).trans (X.Gi_zero_le_normalizer_V0 hc hn0 hs hodd h5 hX hGT hreg)
      (Subgroup.inv_mem _ hx)
  have h2 : x⁻¹ * ⁅y, x * a * x⁻¹⁆ * x ∈ X.V0 := by
    simpa using (Subgroup.mem_normalizer_iff.mp hxN _).mp h1
  have hid : ⁅x⁻¹ * y * x, a⁆ = x⁻¹ * ⁅y, x * a * x⁻¹⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [hid]
  exact h2

private theorem odd_card_Ki_zero : Odd (Nat.card ↥(X.Ki 0)) :=
  X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : X.Ki 0 ≤ X.K))

private theorem odd_orderOf_of_mem_Ki_zero {k : G} (hk : k ∈ X.Ki 0) :
    Odd (orderOf k) :=
  X.odd_card_Ki_zero.of_dvd_nat (Subgroup.orderOf_dvd_natCard (X.Ki 0) hk)

private theorem commutator_D_Ki_zero_eq_bot : ⁅X.D, X.Ki 0⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right

private theorem mul_pow_mul_pow_inv_mem_Cmod (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ)))
    {c q : G} (hcC : c ∈ X.Cmod) (hqL : q ∈ X.L 0) (j : ℕ) :
    (c * q) ^ j * (q ^ j)⁻¹ ∈ X.Cmod := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hqj : (q ^ j)⁻¹ ∈ X.L 0 := (X.L 0).inv_mem ((X.L 0).pow_mem hqL j)
    have hconj : q ^ j * c * (q ^ j)⁻¹ ∈ X.Cmod := by
      have h := X.conj_mem_Cmod hc hn0 hs hodd h5 hX hGT hreg hqj hcC
      simpa using h
    have hstep : (c * q) ^ (j + 1) * (q ^ (j + 1))⁻¹ =
        ((c * q) ^ j * (q ^ j)⁻¹) * (q ^ j * c * (q ^ j)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [hstep]
    exact X.Cmod.mul_mem ih hconj

theorem Ki_zero_centralizes_mod (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    ∀ k ∈ X.Ki 0, ∀ a ∈ X.A, ⁅a, k⁆ ∈ X.V0 := by
  have hX0C : X.X0 ≤ X.Cmod := X.X0_le_Cmod hc hn0 hs hodd h5 hX hGT hreg
  have hCL : X.Cmod ≤ X.L 0 := fun g hg => hg.1
  have hQL : X.Q 0 ≤ X.L 0 := fun q hq =>
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 0)) (X.Q_le_Gi 0) hq
  have hL0X : X.L 0 = X.X0 ⊔ X.Q 0 := by
    rw [X.L_zero_eq_Z_four_sup hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
    rfl
  have hL0 : X.L 0 = X.Cmod ⊔ X.Q 0 := by
    refine le_antisymm (by rw [hL0X]; exact sup_le (hX0C.trans le_sup_left) le_sup_right)
      (sup_le hCL hQL)
  have hQnorm : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hcoe : ((X.Cmod ⊔ X.Q 0 : Subgroup G) : Set G) =
      (X.Cmod : Set G) * (X.Q 0 : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X.Cmod (X.Q 0) (hCL.trans hQnorm)
  intro k hk a ha
  have hkL : k ∈ X.L 0 := hk.2
  have hk_mul : k ∈ (X.Cmod : Set G) * (X.Q 0 : Set G) := by
    rw [← hcoe, ← hL0]
    exact hkL
  obtain ⟨c, hcC, q, hqQ, hcq⟩ := hk_mul
  have hqL : q ∈ X.L 0 := hQL hqQ
  have hkmem : (c * q) ^ orderOf k * (q ^ orderOf k)⁻¹ ∈ X.Cmod :=
    X.mul_pow_mul_pow_inv_mem_Cmod hc hn0 hs hodd h5 hX hGT hreg hcC hqL (orderOf k)
  have hkpow : (c * q) ^ orderOf k = 1 := by
    rw [← hcq, pow_orderOf_eq_one]
  have hqjC : q ^ orderOf k ∈ X.Cmod := by
    have hinv : (q ^ orderOf k)⁻¹ ∈ X.Cmod := by
      simpa [hkpow] using hkmem
    simpa using X.Cmod.inv_mem hinv
  obtain ⟨mq, hmq⟩ := pCoreOf_isPGroup' (X.Gi 0) ⟨q, hqQ⟩
  have hq2 : q ^ (2 ^ mq) = 1 := by simpa using congrArg Subtype.val hmq
  have hoddk : Odd (orderOf k) := X.odd_orderOf_of_mem_Ki_zero hk
  have hcop : Nat.Coprime (orderOf k) (2 ^ mq) := hoddk.coprime_two_right.pow_right mq
  have hqC : q ∈ X.Cmod :=
    CFSG.Quasithin.E1.mem_of_pow_mem_of_coprime hcop hqjC
      (by rw [hq2]; exact X.Cmod.one_mem)
  have hkC : k ∈ X.Cmod := by
    rw [← hcq]
    exact X.Cmod.mul_mem hcC hqC
  have hmem : ⁅k, a⁆ ∈ X.V0 :=
    (mem_Cmod X hc hn0 hs hodd h5 hX hGT hreg).mp hkC |>.2 a ha
  rw [← commutatorElement_inv k a]
  exact X.V0.inv_mem hmem

theorem A_eq_D_sup_V0 (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.A = X.D ⊔ X.V0 := by
  have hDA : X.D ≤ X.A := X.D_le_A hc hn0 hs hodd h5 hX hGT hreg
  have hVA : X.V0 ≤ X.A := X.V0_le_A hc hn0 hs hodd h5 hX hGT hreg
  refine le_antisymm ?_ (sup_le hDA hVA)
  haveI hAfin : Finite ↥X.A := finite_of_le_stabilizer X.hyp (H := X.A)
    (X.A_le_Q_zero.trans (X.Q_le_Gi 0))
  have hKi_le : X.Ki 0 ≤ X.K := inf_le_left
  haveI hKfin : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 0) (hKi_le.trans (X.K_le_Gi 0))
  have hKA : X.Ki 0 ≤ Subgroup.normalizer (X.A : Set G) :=
    (hKi_le.trans (X.K_le_Gi 0)).trans (X.Gi_zero_le_normalizer_A hc hn0 hs hodd h5 hX hGT hreg)
  letI : MulDistribMulAction ↥(X.Ki 0) ↥X.A :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (X.Ki 0) X.A hKA
  have hA2 : IsPGroup 2 ↥X.A := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnil : Group.IsNilpotent ↥X.A := hA2.isNilpotent
  have hsolv : Group.IsSolvable ↥X.A := IsNilpotent.to_isSolvable
  obtain ⟨na, hna⟩ := hA2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(X.Ki 0)) (Nat.card ↥X.A) := by
    rw [hna]
    exact X.odd_card_Ki_zero.coprime_two_right.pow_right na
  have htop := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := ↥X.A) (A := ↥(X.Ki 0)) hsolv hcop
  have hcomm : Subgroup.map X.A.subtype
      (commutatorAction (A := ↥(X.Ki 0)) (G := ↥X.A)) = ⁅X.A, X.Ki 0⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator X.A (X.Ki 0) hKA
  have hfix : fixedPointSubgroup (↥(X.Ki 0)) (↥X.A) =
      (subgroupCentralizerIn X.A (X.Ki 0)).subgroupOf X.A :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn X.A (X.Ki 0) hKA
  haveI : (commutatorAction (A := ↥(X.Ki 0)) (G := ↥X.A)).Normal :=
    (commutatorAction_normal_and_invariant (A := ↥(X.Ki 0)) (G := ↥X.A)).1
  have hcomm_le : ⁅X.A, X.Ki 0⁆ ≤ X.V0 := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    exact X.Ki_zero_centralizes_mod hc hn0 hs hodd h5 hX hGT hreg k hk a ha
  intro x hx
  let xA : ↥X.A := ⟨x, hx⟩
  have hxTop : xA ∈ commutatorAction (A := ↥(X.Ki 0)) (G := ↥X.A) ⊔
      fixedPointSubgroup (↥(X.Ki 0)) (↥X.A) := by
    rw [sup_comm, htop]
    exact Subgroup.mem_top xA
  obtain ⟨k, hk, c, hcPt, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp hxTop
  have hkV : (k : G) ∈ X.V0 := by
    have hkmap : (k : G) ∈ Subgroup.map X.A.subtype
        (commutatorAction (A := ↥(X.Ki 0)) (G := ↥X.A)) :=
      Subgroup.mem_map_of_mem _ hk
    rw [hcomm] at hkmap
    exact hcomm_le hkmap
  have hcD : (c : G) ∈ X.D := by
    rw [hfix] at hcPt
    have hc' : (c : G) ∈ subgroupCentralizerIn X.A (X.Ki 0) := Subgroup.mem_subgroupOf.mp hcPt
    rw [subgroupCentralizerIn] at hc'
    exact Subgroup.mem_inf.mpr
      ⟨X.A_le_Q_zero hc'.1, hc'.2⟩
  have hx_eq : (k : G) * (c : G) = x := by
    have h := congrArg Subtype.val hkc
    simpa using h
  have hmem : (k : G) * (c : G) ∈ X.D ⊔ X.V0 := by
    rw [sup_comm]
    exact Subgroup.mul_mem_sup hkV hcD
  rwa [hx_eq] at hmem

theorem K_le_normalizer_D : X.K ≤ Subgroup.normalizer (X.D : Set G) :=
  (le_inf ((X.K_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
    (CFSG.Quasithin.B6.le_normalizer_centralizer (X.K_le_normalizer_Ki 0))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem commutator_Ki_zero_Z_zero_eq_bot (hc : CharTwoStab (V := V) (G := G))
    (hn0 : 2 ≤ X.n 0) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Even (Nat.card X.GT)) : ⁅X.Ki 0, X.Z 0⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro k hk z hz
  have hZ0 : X.Z 0 = centerOf (X.L 0) :=
    X.Z_zero_eq_centerOf_L_zero hc (Or.inl hn0) hs hodd h5 hX hGT
  have hkL : k ∈ X.L 0 := hk.2
  have hc' : z ∈ Subgroup.centralizer (X.L 0 : Set G) := by
    rw [hZ0] at hz
    exact hz.2
  have h := Subgroup.mem_centralizer_iff.mp hc' k hkL
  rw [Subgroup.mem_bot, commutatorElement_def]
  calc k * z * k⁻¹ * z⁻¹ = (k * z) * k⁻¹ * z⁻¹ := by group
    _ = (z * k) * k⁻¹ * z⁻¹ := by rw [h]
    _ = 1 := by group

private theorem centralizer_E_le_ZM (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT)) :
    ∀ e ∈ X.E X.QT 0, (∀ k ∈ X.Ki 0, ⁅e, k⁆ = 1) → e ∈ X.ZM := by
  intro e heE heC
  have hK0Lst : X.Ki 0 ≤ X.Lst X.QT 0 := X.Ki_zero_le_Lst hGT hs hodd h5 hX hn0
  obtain ⟨k, hk, hk1⟩ :=
    (X.Ki 0).bot_or_exists_ne_one.resolve_left (X.torus_ne_bot 0 hn0)
  have hkL : k ∈ X.Lst X.QT 0 := hK0Lst hk
  have hkE : k ∉ X.E X.QT 0 := by
    intro hkE
    have hkQ : k ∈ X.Q 0 := hkE.1
    have hkS : k ∈ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0 hkQ
    have : k ∈ X.K ⊓ X.edgeSylow 0 := ⟨hk.1, hkS⟩
    rw [X.K_inf_edgeSylow 0] at this
    exact hk1 (Subgroup.mem_bot.mp this)
  have hoddk : Odd (orderOf k) := X.odd_orderOf_of_mem_Ki_zero hk
  have hcomm : ⁅e, k⁆ ∈ X.ZM := by
    rw [heC k hk]
    exact (X.ZM).one_mem
  exact (X.natQuot_M hGT hs hodd h5 hX).fpf k hkL hoddk hkE e heE hcomm

private theorem Ki_zero_fixes_neighbors (j : ℤ)
    {P : Subgroup G} (hsup : P ⊔ X.Q j = X.edgeSylow (j - 1))
    (hPN : P ≤ Subgroup.normalizer (X.Q j : Set G))
    (hP : ⁅P, X.Ki 0⁆ ≤ X.Q j) :
    ∀ k ∈ X.Ki 0, ∀ w : V, Γ.Adj (X.vert j) w → k • w = w := by
  intro k hk w hw
  have hcommQj : ⁅X.Q j, X.Ki 0⁆ ≤ X.Q j :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp fun x hx =>
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi j) (X.K_le_Gi j hx.1)
  have hcomm : ⁅X.edgeSylow (j - 1), X.Ki 0⁆ ≤ X.Q j := by
    rw [← hsup]
    exact CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      P (X.Q j) (X.Ki 0) (X.Q j) hP hcommQj hPN Subgroup.le_normalizer
  exact X.fixes_neighbors_of_centralizes_edgeSylow_gen j (X.K_le_Gi (j - 1) hk.1)
    (X.K_le_Gi j hk.1) (X.odd_orderOf_of_mem_Ki_zero hk)
    (fun x hx => by
      rw [← commutatorElement_inv]
      exact (X.Q j).inv_mem (Subgroup.commutator_le.mp hcomm x hx k hk)) w hw

private theorem exists_centralizing_conj_Z_three {k : G}
    (hL2C : X.L 2 = (X.L 2 ⊓ Subgroup.centralizer ({k} : Set G)) ⊔ X.Q 2) :
    ∃ c ∈ X.L 2 ⊓ Subgroup.centralizer ({k} : Set G), X.Z 3 = conjSub c (X.Z 1) := by
  obtain ⟨g, hgL, hg13⟩ : ∃ g ∈ X.L 2, g • X.vert 1 = X.vert 3 :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 2)).trans (X.vert 1) (X.vert 3)
      (X.adj 1).symm (X.adj 2)
  have hZg : X.Z 3 = conjSub g (X.Z 1) := (X.Z_conj hg13).symm
  have hQL2 : X.Q 2 ≤ X.L 2 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 2)) (X.Q_le_Gi 2)
  have hQ2n : (X.Q 2).subgroupOf (X.L 2) |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := X.Q 2) (K := X.L 2) hQL2).mpr
      ((X.L_le_Gi 2).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)))
  have htop : (⊤ : Subgroup ↥(X.L 2)) =
      (X.L 2 ⊓ Subgroup.centralizer ({k} : Set G)).subgroupOf (X.L 2) ⊔
        (X.Q 2).subgroupOf (X.L 2) := by
    rw [← Subgroup.subgroupOf_sup inf_le_left hQL2, ← hL2C, Subgroup.subgroupOf_self]
  obtain ⟨c, hcC, q, hqQ, hgq⟩ :=
    (Subgroup.mem_sup_of_normal_right
      (s := (X.L 2 ⊓ Subgroup.centralizer ({k} : Set G)).subgroupOf (X.L 2))
      (t := (X.Q 2).subgroupOf (X.L 2)) (x := ⟨g, hgL⟩)).mp
      (by rw [← htop]; exact Subgroup.mem_top _)
  have hcG : (c : G) ∈ X.L 2 := (Subgroup.mem_subgroupOf.mp hcC).1
  have hcentC : (c : G) ∈ Subgroup.centralizer ({k} : Set G) :=
    (Subgroup.mem_subgroupOf.mp hcC).2
  have hqG : (q : G) ∈ X.Q 2 := Subgroup.mem_subgroupOf.mp hqQ
  have hcg : g = (c : G) * (q : G) := (congrArg Subtype.val hgq).symm
  have hqZ1 : conjSub (q : G) (X.Z 1) = X.Z 1 :=
    X.Z_normal 1 (q : G) ((X.Q_le_Gi_adj 2 hqG).1)
  refine ⟨(c : G), ⟨hcG, hcentC⟩, ?_⟩
  rw [hZg, hcg, conjSub_mul, hqZ1]

private theorem commutator_V2_mem_Z_two (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk : k ∈ X.Ki 0)
    (hL2C : X.L 2 = (X.L 2 ⊓ Subgroup.centralizer ({k} : Set G)) ⊔ X.Q 2) :
    ∀ x ∈ X.V2, ⁅x, k⁆ ∈ X.Z 2 := by
  have hZ2Nk : k ∈ Subgroup.normalizer (X.Z 2 : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub k (X.Z 2) = X.Z 2
    exact X.Z_normal 2 k (X.K_le_Gi 2 hk.1)
  have hZ2k : ∀ z ∈ X.Z 2, ⁅z, k⁆ ∈ X.Z 2 := by
    intro z hz
    have hconj : k * z⁻¹ * k⁻¹ ∈ X.Z 2 :=
      (Subgroup.mem_normalizer_iff.mp hZ2Nk z⁻¹).mp ((X.Z 2).inv_mem hz)
    have hz' : z * (k * z⁻¹ * k⁻¹) ∈ X.Z 2 := (X.Z 2).mul_mem hz hconj
    rwa [show z * (k * z⁻¹ * k⁻¹) = ⁅z, k⁆ by rw [commutatorElement_def]; group] at hz'
  have hZ0k : ∀ z ∈ X.Z 0, ⁅z, k⁆ = 1 := by
    intro z hz
    have hZ0eq : X.Z 0 = centerOf (X.L 0) :=
      X.Z_zero_eq_centerOf_L_zero hc (Or.inl hn0) hs hodd h5 hX hGT
    have hcent : z ∈ Subgroup.centralizer (X.L 0 : Set G) := by rw [hZ0eq] at hz; exact hz.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hcent k hk.2
    rw [commutatorElement_def]
    calc z * k * z⁻¹ * k⁻¹ = (k * z) * z⁻¹ * k⁻¹ := by rw [← hcomm]
      _ = 1 := by group
  let H : Subgroup G :=
    { carrier := {x : G | x ∈ X.Gi 2 ∧ ⁅x, k⁆ ∈ X.Z 2}
      one_mem' := ⟨(X.Gi 2).one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxG, hx⟩ ⟨hyG, hy⟩
        refine ⟨(X.Gi 2).mul_mem hxG hyG, ?_⟩
        have hxy : ⁅x * y, k⁆ = x * ⁅y, k⁆ * x⁻¹ * ⁅x, k⁆ := by
          rw [commutatorElement_def]; group
        rw [hxy]
        have hconj : x * ⁅y, k⁆ * x⁻¹ ∈ X.Z 2 := by
          have hZN := X.Z_normal 2 x hxG
          rw [← hZN]
          refine Subgroup.mem_map.mpr ⟨⁅y, k⁆, hy, ?_⟩
          change (MulAut.conj x) ⁅y, k⁆ = x * ⁅y, k⁆ * x⁻¹
          rw [MulAut.conj_apply]
        exact (X.Z 2).mul_mem hconj hx
      inv_mem' := by
        rintro x ⟨hxG, hx⟩
        refine ⟨(X.Gi 2).inv_mem hxG, ?_⟩
        have hx' : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * x := by
          rw [commutatorElement_def]; group
        rw [hx']
        have hZN := X.Z_normal 2 x⁻¹ ((X.Gi 2).inv_mem hxG)
        rw [← hZN]
        refine Subgroup.mem_map.mpr ⟨⁅x, k⁆⁻¹, (X.Z 2).inv_mem hx, ?_⟩
        change (MulAut.conj x⁻¹) ⁅x, k⁆⁻¹ = x⁻¹ * ⁅x, k⁆⁻¹ * x
        rw [MulAut.conj_apply, inv_inv] }
  have hZ1H : X.Z 1 ≤ H := by
    have hZ1 : X.Z 1 = X.Z 0 ⊔ X.Z 2 :=
      X.Z_one_eq_Z_zero_sup_Z_two hc (Or.inl hn0) hs hodd h5 hX hGT hreg
    rw [hZ1]
    refine sup_le ?_ ?_
    · intro z hz
      refine ⟨?_, ?_⟩
      · have hb := X.Z_zero_le_Gi_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg hz
        exact X.mem_Gi_of_between hb.2 hb.1 (by omega) (by omega)
      · rw [hZ0k z hz]
        exact (X.Z 2).one_mem
    · intro z hz
      exact ⟨X.Z_le_Gi 2 hz, hZ2k z hz⟩
  have hZ3H : X.Z 3 ≤ H := by
    obtain ⟨c, hcC, hZ3c⟩ := X.exists_centralizing_conj_Z_three hL2C
    have hcG : c ∈ X.L 2 := hcC.1
    have hcentC : c ∈ Subgroup.centralizer ({k} : Set G) := hcC.2
    have hcK : k * c = c * k :=
      Subgroup.mem_centralizer_iff.mp hcentC k (Set.mem_singleton k)
    have hmem : ∀ y : G, y ∈ X.Z 3 ↔ ∃ z ∈ X.Z 1, y = c * z * c⁻¹ := by
      intro y
      rw [hZ3c]
      constructor
      · intro hy
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        refine ⟨z, hz, ?_⟩
        change (MulAut.conj c) z = c * z * c⁻¹
        rw [MulAut.conj_apply]
      · rintro ⟨z, hz, rfl⟩
        refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
        change (MulAut.conj c) z = c * z * c⁻¹
        rw [MulAut.conj_apply]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (hmem y).mp hy
    refine ⟨?_, ?_⟩
    · exact (X.Gi 2).mul_mem ((X.Gi 2).mul_mem (X.L_le_Gi 2 hcG)
        ((X.Z_one_le_Gi_neg_two_two_four hc hn0 hs hodd h5 hX hGT hreg).2.1 hz))
        ((X.Gi 2).inv_mem (X.L_le_Gi 2 hcG))
    · have hZk : ⁅z, k⁆ ∈ X.Z 2 := (hZ1H hz).2
      have hconj : c * ⁅z, k⁆ * c⁻¹ ∈ X.Z 2 := by
        have hZN := X.Z_normal 2 c (X.L_le_Gi 2 hcG)
        rw [← hZN]
        refine Subgroup.mem_map.mpr ⟨⁅z, k⁆, hZk, ?_⟩
        change (MulAut.conj c) ⁅z, k⁆ = c * ⁅z, k⁆ * c⁻¹
        rw [MulAut.conj_apply]
      have hkey : ⁅c * z * c⁻¹, k⁆ = c * ⁅z, k⁆ * c⁻¹ := by
        have hmap := map_commutatorElement (f := (MulAut.conj c).toMonoidHom) z k
        have hck : (MulEquiv.toMonoidHom (MulAut.conj c)) k = k := by
          change (MulAut.conj c) k = k
          rw [MulAut.conj_apply, ← hcK]
          group
        rw [hck] at hmap
        have hcz : (MulEquiv.toMonoidHom (MulAut.conj c)) z = c * z * c⁻¹ := by
          change (MulAut.conj c) z = c * z * c⁻¹
          rw [MulAut.conj_apply]
        rw [hcz] at hmap
        exact hmap.symm
      rw [hkey]
      exact hconj
  have hV2H : X.V2 ≤ H := by
    rw [X.V2_eq_Z_one_sup_Z_three hc hn0 hs hodd h5 hX hGT hreg]
    exact sup_le hZ1H hZ3H
  exact fun x hx => (hV2H hx).2

private theorem commutator_S_mem_Q_zero (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) {k : G} (hk : k ∈ X.Ki 0)
    (hV2k : ∀ x ∈ X.V2, ⁅x, k⁆ ∈ X.Z 2) : ∀ x ∈ X.S, ⁅k, x⁆ ∈ X.Q 0 := by
  have hZ2Q0 : X.Z 2 ≤ X.Q 0 := by
    have hZ2le : X.Z 2 ≤ X.Z 1 := by
      rw [X.Z_one_eq_Z_zero_sup_Z_two hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
      exact le_sup_right
    exact hZ2le.trans (X.Z_one_le_Q_zero hc (Or.inl hn0) hs hodd h5 hX hGT hreg)
  have hZ4G0 : X.Z 4 ≤ X.Gi 0 :=
    ((show X.Z 4 ≤ X.X0 from le_sup_left).trans
      (X.X0_le_L hc hn0 hs hodd h5 hX hGT hreg)).trans (X.L_le_Gi 0)
  have hZ4N : X.Z 4 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hZ4G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hkQ0N : k ∈ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.K_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))) hk.1
  intro x hx
  have hS : X.S = X.Q 0 ⊔ X.Z 4 := by
    rw [← X.Z_four_sup_Q_zero hc (Or.inl hn0) hs hodd h5 hX hGT hreg, sup_comm]
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (H := X.Q 0) (K := X.Z 4)
      hZ4N).mp (by rw [← hS]; exact hx)
  have h1 : ⁅k, a * b⁆ = (k * a * k⁻¹) * (k * b * k⁻¹ * b⁻¹) * a⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h1]
  have hka : k * a * k⁻¹ ∈ X.Q 0 := (Subgroup.mem_normalizer_iff.mp hkQ0N a).mp ha
  have hkb : k * b * k⁻¹ * b⁻¹ ∈ X.Q 0 := by
    have h2 : k * b * k⁻¹ * b⁻¹ = ⁅k, b⁆ := by rw [commutatorElement_def]
    rw [h2, ← commutatorElement_inv]
    exact hZ2Q0 ((X.Z 2).inv_mem
      (hV2k b (X.Z_four_le_V2 hc hn0 hs hodd h5 hX hGT hreg hb)))
  exact (X.Q 0).mul_mem ((X.Q 0).mul_mem hka hkb) ((X.Q 0).inv_mem ha)

private theorem false_of_commutator_S_le_Q_zero (hn0 : 2 ≤ X.n 0) {k : G} (hk : k ∈ X.Ki 0)
    (hk1 : k ≠ 1) (hcommS : ∀ x ∈ X.S, ⁅k, x⁆ ∈ X.Q 0) : False := by
  have hoddk : Odd (orderOf k) := X.odd_orderOf_of_mem_Ki_zero hk
  have hrevS : X.reverse.edgeSylow (-1) = X.S := by
    show pCoreOf 2 (X.reverse.Gi (-1) ⊓ X.reverse.Gi (-1 + 1)) = X.S
    rw [X.reverse_Gi, X.reverse_Gi,
      show (-(-1 + 1) : ℤ) = 0 by norm_num, neg_neg, inf_comm]
  have hfix0 : ∀ w : V, Γ.Adj (X.vert 0) w → k • w = w := by
    intro w hw
    refine X.reverse.fixes_neighbors_of_centralizes_edgeSylow_gen 0 ?_ ?_ hoddk ?_ w hw
    · rw [X.reverse_Gi]; simpa using X.K_le_Gi 1 hk.1
    · rw [X.reverse_Gi]; simpa using X.K_le_Gi 0 hk.1
    · intro x hx
      have hx' : x ∈ X.S := by simpa [hrevS] using hx
      rw [X.reverse_Q]
      simpa using hcommS x hx'
  have hval : 5 ≤ Nat.card (Γ.neighborSet (X.vert 0)) := by
    have h := (X.hyp.valency (X.vert 0)).2
    have hpow : 2 ^ 2 ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
    norm_num at hpow
    calc 5 ≤ 2 ^ X.n 0 + 1 := by omega
      _ = Nat.card (Γ.neighborSet (X.vert 0)) := h.symm
  have hne : X.vert 1 ≠ X.vert (-1) := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hsub : Γ.neighborSet (X.vert 0) ⊆ ({X.vert 1, X.vert (-1)} : Set V) := by
    intro a ha
    have hfixa : k • a = a := hfix0 a ha
    have hmem := (X.torus_fixed 0 hn0 hk hk1 a ha).mp hfixa
    rcases hmem with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hle : (Γ.neighborSet (X.vert 0)).ncard ≤ 2 := by
    have h2 : ({X.vert 1, X.vert (-1)} : Set V).ncard = 2 := Set.ncard_pair hne
    rw [← h2]
    exact Set.ncard_le_ncard hsub
  rw [show (Γ.neighborSet (X.vert 0)).ncard = Nat.card (Γ.neighborSet (X.vert 0)) from rfl]
    at hle
  omega

theorem D_le_Q_two (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.D ≤ X.Q 2 := by
  by_contra hnot
  have hDA : X.D ≤ X.A := X.D_le_A hc hn0 hs hodd h5 hX hGT hreg
  have hDQ1 : X.D ≤ X.Q 1 := hDA.trans inf_le_left
  have hDedge : X.D ≤ X.edgeSylow 1 := hDQ1.trans (X.Q_le_edgeSylow_left 1)
  have hsup : X.D ⊔ X.Q 2 = X.edgeSylow 1 :=
    X.sup_Q_eq_edgeSylow_of_gen 1 (inf_le_left.trans X.K_le_normalizer_D) hDedge hnot
  have hDG2 : X.D ≤ X.Gi 2 := hDQ1.trans ((X.Q_le_Gi_adj 1).trans inf_le_right)
  have hcommD : ⁅X.D, X.Ki 0⁆ ≤ X.Q 2 := X.commutator_D_Ki_zero_eq_bot.trans_le bot_le
  have hfix2 : ∀ k ∈ X.Ki 0, ∀ w : V, Γ.Adj (X.vert 2) w → k • w = w :=
    X.Ki_zero_fixes_neighbors 2 hsup
      (hDG2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))) hcommD
  have hKi_le12 : X.Ki 0 ≤ X.Gi 1 ⊓ X.Gi 2 :=
    le_inf (inf_le_left.trans (X.K_le_Gi 1)) (inf_le_left.trans (X.K_le_Gi 2))
  obtain ⟨k, hk, hk1⟩ :=
    (X.Ki 0).bot_or_exists_ne_one.resolve_left (X.torus_ne_bot 0 hn0)
  have hoddk : Odd (orderOf k) := X.odd_orderOf_of_mem_Ki_zero hk
  have hfix2k : ∀ w : V, Γ.Adj (X.vert 2) w → k • w = w := hfix2 k hk
  have hL2C : X.L 2 = (X.L 2 ⊓ Subgroup.centralizer ({k} : Set G)) ⊔ X.Q 2 :=
    X.L_eq_centralizer_sup_Q 2 (hKi_le12 hk).1 (hKi_le12 hk).2 hoddk hfix2k
  have hV2k : ∀ x ∈ X.V2, ⁅x, k⁆ ∈ X.Z 2 :=
    X.commutator_V2_mem_Z_two hc hn0 hs hodd h5 hX hGT hreg hk hL2C
  have hcommS : ∀ x ∈ X.S, ⁅k, x⁆ ∈ X.Q 0 :=
    X.commutator_S_mem_Q_zero hc hn0 hs hodd h5 hX hGT hreg hk hV2k
  exact X.false_of_commutator_S_le_Q_zero hn0 hk hk1 hcommS

private theorem normalizer_Ki_zero_transitive (j : ℤ)
    (hfix : ∀ k ∈ X.Ki 0, ∀ w : V, Γ.Adj (X.vert j) w → k • w = w) :
    ∀ a b : V, Γ.Adj (X.vert j) a → Γ.Adj (X.vert j) b →
      ∃ g ∈ Subgroup.normalizer (X.Ki 0 : Set G) ⊓ X.Gi j, g • a = b := by
  have hoddKi : Odd (Nat.card ↥(X.Ki 0)) := X.odd_card_Ki_zero
  have hcommL : ⁅X.Ki 0, X.L j⁆ ≤ X.Q j := by
    rw [Subgroup.commutator_le]
    intro k hk l hl
    exact X.commutator_mem_Q_of_fixes_neighbors j (X.K_le_Gi j hk.1) (hfix k hk) l hl
  exact X.normalizer_transitive_of_commutator_le_Q j hoddKi
    (fun k hk => X.K_le_Gi j hk.1)
    (by rw [Subgroup.commutator_comm]; exact hcommL)

theorem D_le_Q_three (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.D ≤ X.Q 3 := by
  by_contra hnot
  have hD2 : X.D ≤ X.Q 2 := X.D_le_Q_two hc hn0 hs hodd h5 hX hGT hreg
  have hD3 : X.D ≤ X.edgeSylow 2 := hD2.trans (X.Q_le_edgeSylow_left 2)
  have hsup : X.D ⊔ X.Q 3 = X.edgeSylow 2 :=
    X.sup_Q_eq_edgeSylow_of_gen 2 (inf_le_left.trans X.K_le_normalizer_D) hD3 hnot
  have hDG3 : X.D ≤ X.Gi 3 := fun d hd => (X.Q_le_Gi_adj 2 (hD2 hd)).2
  have hcommD : ⁅X.D, X.Ki 0⁆ ≤ X.Q 3 := X.commutator_D_Ki_zero_eq_bot.trans_le bot_le
  have hfix3 : ∀ k ∈ X.Ki 0, ∀ w : V, Γ.Adj (X.vert 3) w → k • w = w :=
    X.Ki_zero_fixes_neighbors 3 hsup
      (hDG3.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 3))) hcommD
  have htrans3 := X.normalizer_Ki_zero_transitive 3 hfix3
  have hZ0G4 : X.Z 0 ≤ X.Gi 4 :=
    fun z hz => (X.Z_zero_le_Gi_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg hz).1
  have hZ0N : X.Z 0 ≤ Subgroup.normalizer (X.Q 4 : Set G) :=
    hZ0G4.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4))
  have hcommZ0 : ⁅X.Z 0, X.Ki 0⁆ ≤ X.Q 4 := by
    rw [Subgroup.commutator_comm,
      X.commutator_Ki_zero_Z_zero_eq_bot hc hn0 hs hodd h5 hX hGT]
    exact bot_le
  have hsup4 : X.Z 0 ⊔ X.Q 4 = X.edgeSylow 3 :=
    X.Z_zero_sup_Q_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg
  have hfix4 : ∀ k ∈ X.Ki 0, ∀ w : V, Γ.Adj (X.vert 4) w → k • w = w :=
    X.Ki_zero_fixes_neighbors 4 hsup4 hZ0N hcommZ0
  have htrans4 := X.normalizer_Ki_zero_transitive 4 hfix4
  have hKi_le34 : X.Ki 0 ≤ X.Gi 3 ⊓ X.Gi 4 :=
    le_inf (inf_le_left.trans (X.K_le_Gi 3)) (inf_le_left.trans (X.K_le_Gi 4))
  have hbot : X.Ki 0 = ⊥ :=
    eq_bot_of_normalizer_trans X.hyp (X.adj 3) hKi_le34 htrans3 htrans4
  exact X.torus_ne_bot 0 hn0 hbot

private theorem D_eq_Z0_sup_inf (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.D = X.Z 0 ⊔ (X.D ⊓ X.Q 4) := by
  have hZ0L : X.Z 0 = centerOf (X.L 0) :=
    X.Z_zero_eq_centerOf_L_zero hc (Or.inl hn0) hs hodd h5 hX hGT
  have hZ0D : X.Z 0 ≤ X.D := by
    refine le_inf (X.Z_le_Q 0) ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hz' : z ∈ Subgroup.centralizer (X.L 0 : Set G) := by
      rw [hZ0L] at hz
      exact hz.2
    exact Subgroup.mem_centralizer_iff.mp hz' y hy.2
  have hZ0G4 : X.Z 0 ≤ X.Gi 4 :=
    fun z hz => (X.Z_zero_le_Gi_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg hz).1
  have hZ0NQ4 : X.Z 0 ≤ Subgroup.normalizer (X.Q 4 : Set G) :=
    hZ0G4.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 4))
  have hD3 : X.D ≤ X.Q 3 := X.D_le_Q_three hc hn0 hs hodd h5 hX hGT hreg
  have hD_le : X.D ≤ X.Z 0 ⊔ X.Q 4 := by
    have h := hD3.trans (X.Q_le_edgeSylow_left 3)
    rwa [← X.Z_zero_sup_Q_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg] at h
  refine le_antisymm ?_ (sup_le hZ0D inf_le_left)
  intro x hx
  have hxsup : x ∈ X.Q 4 ⊔ X.Z 0 := by
    rw [sup_comm]
    exact hD_le hx
  obtain ⟨q, hq, z, hz, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (H := X.Q 4) (K := X.Z 0)
      hZ0NQ4).mp hxsup
  have hqD : q ∈ X.D := by
    have hzD : z⁻¹ ∈ X.D := X.D.inv_mem (hZ0D hz)
    simpa using X.D.mul_mem hx hzD
  rw [sup_comm]
  exact Subgroup.mul_mem_sup (S := X.D ⊓ X.Q 4) (T := X.Z 0)
    (Subgroup.mem_inf.mpr ⟨hqD, hq⟩) hz

private theorem QT_le_D (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.QT ≤ X.D := by
  have hQTCK : X.QT ≤ Subgroup.centralizer (X.K : Set G) := by
    rw [X.QT_eq_inf_centralizer_K hc hn0 hs hodd h5 hX hGT hreg]
    exact inf_le_right
  refine le_inf (X.QT_le_Q 0) ?_
  intro q hq
  have hqK : q ∈ Subgroup.centralizer (X.K : Set G) := hQTCK hq
  rw [Subgroup.mem_centralizer_iff] at hqK ⊢
  intro y hy
  exact hqK y hy.1

private theorem ZM_inf_Q_four_eq_QT (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.ZM ⊓ X.Q 4 = X.QT := by
  have hZ0NQT : X.Z 0 ≤ Subgroup.normalizer (X.QT : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer (X.QT : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun q hq =>
        Subgroup.mem_centralizer_iff.mp (X.Z_le_center 0 hz).2 q (X.QT_le_Q 0 hq))
  have hZ0Q4 : X.Z 0 ⊓ X.Q 4 = ⊥ :=
    X.Z_zero_inf_Q_four hc (Or.inl hn0) hs hodd h5 hX hGT hreg
  rw [X.ZM_eq_Z_zero_sup_QT hc (Or.inl hn0) hs hodd h5 hX hGT hreg]
  refine le_antisymm ?_ (le_inf le_sup_right (X.QT_le_Q 4))
  intro y hy
  have hysup : y ∈ X.QT ⊔ X.Z 0 := by
    rw [sup_comm]
    exact hy.1
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes (H := X.QT) (K := X.Z 0)
      hZ0NQT).mp hysup
  have hbQ4 : b ∈ X.Q 4 := by
    have haQ4 : a⁻¹ ∈ X.Q 4 := (X.Q 4).inv_mem (X.QT_le_Q 4 ha)
    simpa using (X.Q 4).mul_mem haQ4 hy.2
  have hbBot : b ∈ (⊥ : Subgroup G) := by
    rw [← hZ0Q4]
    exact ⟨hb, hbQ4⟩
  rw [Subgroup.mem_bot] at hbBot
  rw [hbBot, mul_one]
  exact ha

private theorem D_inf_Q_four_eq_QT (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) :
    X.D ⊓ X.Q 4 = X.QT := by
  have hQTD : X.QT ≤ X.D := X.QT_le_D hc hn0 hs hodd h5 hX hGT hreg
  have hQD4 : X.QT ≤ X.D ⊓ X.Q 4 := le_inf hQTD (X.QT_le_Q 4)
  by_contra hne
  let P : Subgroup G := X.D ⊓ X.Q 4
  have hPQ0 : P ≤ X.Q 0 := fun x hx => hx.1.1
  haveI hPfin : Finite ↥P :=
    finite_of_le_stabilizer X.hyp (H := P) (hPQ0.trans (X.Q_le_Gi 0))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥P := (pCoreOf_isPGroup' (X.Gi 0)).to_le hPQ0
  let U : Subgroup ↥P := X.QT.subgroupOf P
  have hU : U < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    intro hple
    exact hne (le_antisymm hple hQD4)
  have hltN : U < Subgroup.normalizer (U : Set ↥P) := by
    haveI : Finite ↥(⊤ : Subgroup ↥P) :=
      Finite.of_equiv ↥P (Subgroup.topEquiv (G := ↥P)).symm
    have htop2 : IsPGroup 2 (⊤ : Subgroup ↥P) :=
      hP2.of_equiv (Subgroup.topEquiv (G := ↥P)).symm
    have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) (P := ⊤) (S := U)
      htop2 hU
    simpa using h
  obtain ⟨x, hxN, hxU⟩ := SetLike.exists_of_lt hltN
  have hnP : (x : G) ∈ P := x.2
  have hnQD : (x : G) ∈ X.D := hnP.1
  have hnQ0 : (x : G) ∈ X.Q 0 := hnQD.1
  have hnQ4 : (x : G) ∈ X.Q 4 := hnP.2
  have hnN : (x : G) ∈ Subgroup.normalizer (X.QT : Set G) := by
    have hEq := Subgroup.subgroupOf_normalizer_eq (H := X.QT) (N := P) hQD4
    have hx' : x ∈ (Subgroup.normalizer (X.QT : Set G)).subgroupOf P := by
      rw [hEq]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hx'
  have hnE : (x : G) ∈ X.E X.QT 0 := ⟨hnQ0, hnN⟩
  have hnC : ∀ k ∈ X.Ki 0, ⁅(x : G), k⁆ = 1 := fun k hk => by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_iff.mp hnQD.2 k hk).symm
  have hnZM : (x : G) ∈ X.ZM :=
    X.centralizer_E_le_ZM hn0 hs hodd h5 hX hGT (x : G) hnE hnC
  have hmeet : X.ZM ⊓ X.Q 4 = X.QT :=
    X.ZM_inf_Q_four_eq_QT hc hn0 hs hodd h5 hX hGT hreg
  have hnQT : (x : G) ∈ X.QT := by
    have hmem : (x : G) ∈ X.ZM ⊓ X.Q 4 := ⟨hnZM, hnQ4⟩
    rwa [hmeet] at hmem
  exact hxU hnQT

theorem D_eq (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.D = X.Z 0 ⊔ X.QT := by
  rw [X.D_eq_Z0_sup_inf hc hn0 hs hodd h5 hX hGT hreg,
    X.D_inf_Q_four_eq_QT hc hn0 hs hodd h5 hX hGT hreg]

theorem A_eq_E (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : X.A = X.E X.QT 0 := by
  have hA : X.A = X.D ⊔ X.V0 := X.A_eq_D_sup_V0 hc hn0 hs hodd h5 hX hGT hreg
  have hD : X.D = X.Z 0 ⊔ X.QT := X.D_eq hc hn0 hs hodd h5 hX hGT hreg
  have hE : X.E X.QT 0 = X.V0 ⊔ X.QT :=
    X.E_eq_V0_sup_QT hc hn0 hs hodd h5 hX hGT hreg
  have hZV : X.Z 0 ≤ X.V0 := by
    have h := X.Z_zero_sup_Z_two_le hc (Or.inl hn0) hs hodd h5 hX hGT hreg
    have hV : X.V0 = X.Z 1 ⊔ X.Z (-1) :=
      X.V0_eq_Z_one_sup_Z_neg_one hc hn0 hs hodd h5 hX hGT hreg
    rw [hV]
    exact (le_sup_left.trans h).trans le_sup_left
  rw [hA, hD, hE]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ le_sup_left
    exact sup_le (hZV.trans le_sup_left) le_sup_right
  · refine sup_le le_sup_right ?_
    exact (le_sup_right : X.QT ≤ X.Z 0 ⊔ X.QT).trans le_sup_left

theorem isElemAbelian_A (hc : CharTwoStab (V := V) (G := G)) (hn0 : 2 ≤ X.n 0)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Even (Nat.card X.GT))
    {m : ℕ} (hreg : X.IsMaxReg 0 (2 * (m : ℤ))) : IsElemAbelian 2 X.A := by
  rw [X.A_eq_E hc hn0 hs hodd h5 hX hGT hreg]
  exact X.isElemAbelian_E_QT hGT hs hodd h5 hX

end Setup

end CFSG.Quasithin.St84
