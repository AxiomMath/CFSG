module

public import CFSG.GroupTheory.DedekindNormalizer
public import CFSG.Quasithin.Recognition.St84.Sec67A

import CFSG.Quasithin.Recognition.St84.Gen.Sec6TorusCent

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

@[expose] def VA : Subgroup G := X.Vone ⊓ X.Q 0

@[expose] def VB : Subgroup G := X.VnegOne ⊓ X.Q 0

@[expose] def Ktwo : Subgroup G := conjSub X.τ (X.Ki 0)

@[expose] def R : Subgroup G := (X.Ki 0 ⊔ X.Ktwo) ⊓ X.Ki 1

theorem K_le_normalizer_Ki (i : ℤ) : X.K ≤ Subgroup.normalizer (X.Ki i : Set G) :=
  CFSG.Quasithin.F1.le_normalizer_inf_of_le ((X.K_le_Gi i).trans
    (le_normalizer_oTwoPrime (X.Gi i)))

theorem Ki_zero_inf_one_eq_bot (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) : X.Ki 0 ⊓ X.Ki 1 = ⊥ := by
  have hQT : X.QT ≠ ⊥ := X.QT_ne_bot hGT
  have hQ1 : X.Q 1 ≠ ⊥ := by
    intro h
    exact hQT (le_bot_iff.mp ((X.QT_le_Q 1).trans (le_of_eq h)))
  have hZ1 : X.Z 1 ≠ ⊥ := X.Z_ne_bot_of 1 hQ1
  have hZ1le : X.Z 1 ≤ X.Z 0 := by
    rw [X.Z_zero_eq_Z_one_sup_Z_neg_one hb hc hGT hs hodd h5 hX]
    exact le_sup_left
  have hZ1eq : X.Z 1 = centerOf (X.L 1) :=
    X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX
  have hfpf := X.natQuot_Z_zero hb hc hGT hs hodd h5 hX
  rw [eq_bot_iff]
  intro k hk
  obtain ⟨hk0, hk1⟩ := Subgroup.mem_inf.mp hk
  by_contra hkne
  have hkK : k ∈ X.K := hk0.1
  have hkL0 : k ∈ X.L 0 := hk0.2
  have hkL1 : k ∈ X.L 1 := hk1.2
  have hkOdd : Odd (orderOf k) :=
    X.odd_card_K.of_dvd_nat (Subgroup.orderOf_dvd_natCard X.K hkK)
  have hkZ : k ∉ X.Z 0 := by
    intro hkZ
    haveI : Finite ↥(X.Z 0) :=
      finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Gi 0)
    have hZ0pg : IsPGroup 2 (X.Z 0) :=
      (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ0pg
    have hdvd : orderOf k ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard (X.Z 0) hkZ
    have hcop : Nat.Coprime (orderOf k) (2 ^ n) :=
      Nat.Coprime.pow_right n
        (Nat.prime_two.coprime_iff_not_dvd.mpr hkOdd.not_two_dvd_nat).symm
    have hone : orderOf k = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    exact hkne (orderOf_eq_one_iff.mp hone)
  obtain ⟨⟨e, heZ1⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  have heZ0 : e ∈ X.Z 0 := hZ1le heZ1
  have hec : e ∈ centerOf (X.L 1) := hZ1eq ▸ heZ1
  have hcomm : ⁅e, k⁆ ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hec.2 k hkL1).symm
  have hebot : e ∈ (⊥ : Subgroup G) := hfpf.fpf k hkL0 hkOdd hkZ e heZ0 hcomm
  exact he1 (Subtype.ext (Subgroup.mem_bot.mp hebot))

theorem commutator_Ki_zero_Ki_one_eq_bot (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.Ki 0, X.Ki 1⁆ = ⊥ := by
  have hle : ⁅X.Ki 0, X.Ki 1⁆ ≤ X.Ki 0 ⊓ X.Ki 1 :=
    le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((inf_le_left : X.Ki 1 ≤ X.K).trans (X.K_le_normalizer_Ki 0)))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((inf_le_left : X.Ki 0 ≤ X.K).trans (X.K_le_normalizer_Ki 1)))
  have hbot : X.Ki 0 ⊓ X.Ki 1 = ⊥ :=
    X.Ki_zero_inf_one_eq_bot hb hc hGT hs hodd h5 hX
  rw [hbot] at hle
  exact le_bot_iff.mp hle

private theorem K_mul_comm (hbZ : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) {a b : G}
    (ha : a ∈ X.K) (hb : b ∈ X.K) : a * b = b * a := by
  have hcross : ∀ x ∈ X.Ki 0, ∀ y ∈ X.Ki 1, x * y = y * x :=
    fun x hx y hy => by
      have hmem : ⁅x, y⁆ ∈ (⊥ : Subgroup G) := by
        have hbot := X.commutator_Ki_zero_Ki_one_eq_bot hbZ hc hGT hs hodd h5 hX
        rw [← hbot]
        exact Subgroup.commutator_mem_commutator hx hy
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
  have hclosure : (X.K : Set G) =
      (Subgroup.closure ((X.Ki 0 : Set G) ∪ (X.Ki 1 : Set G)) : Set G) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    exact congrArg (fun H : Subgroup G => (H : Set G)) X.K_eq_sup
  have hK0C : X.Ki 0 ≤ Subgroup.centralizer (X.K : Set G) := by
    intro x hx
    rw [hclosure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with hy | hy
    · exact (X.Ki_mul_comm_gen 0 hx hy).symm
    · exact (hcross x hx y hy).symm
  have hK1C : X.Ki 1 ≤ Subgroup.centralizer (X.K : Set G) := by
    intro x hx
    rw [hclosure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with hy | hy
    · exact hcross y hy x hx
    · exact (X.Ki_mul_comm_gen 1 hx hy).symm
  have hKC : X.K ≤ Subgroup.centralizer (X.K : Set G) := by
    calc X.K = X.Ki 0 ⊔ X.Ki 1 := X.K_eq_sup
      _ ≤ Subgroup.centralizer (X.K : Set G) := sup_le hK0C hK1C
  haveI : IsMulCommutative X.K := Subgroup.le_centralizer_iff_isMulCommutative.mp hKC
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥X.K) ⟨b, hb⟩)

private theorem Ktwo_eq_Ki_two : X.Ktwo = X.Ki 2 := by
  have hτK : conjSub X.τ X.K = X.K :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer X.τ_norm
  have hτL : conjSub X.τ (X.L 0) = X.L 2 := by
    simpa using (X.L_add 1 0).symm
  change conjSub X.τ (X.K ⊓ X.L 0) = X.K ⊓ X.L 2
  rw [conjSub_inf, hτK, hτL]

private theorem Ki_inf_Q {i : ℤ} (hQ : X.Q i ≤ X.S) : X.Ki i ⊓ X.Q i = ⊥ := by
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨hxKi, hxQ⟩ := Subgroup.mem_inf.mp hx
  exact Subgroup.mem_bot.mp (by
    rw [← X.K_inf]
    exact Subgroup.mem_inf.mpr ⟨hxKi.1, hQ hxQ⟩)

private theorem exists_unique_fixed_neighbor_of_two_element {t : G}
    (ht : t ∈ X.normGi X.QT 1) (ht02 : t • X.vert 0 = X.vert 2)
    (htpow : ∃ m : ℕ, t ^ 2 ^ m = 1) :
    ∃ ω : V, Γ.Adj (X.vert 1) ω ∧ t • ω = ω ∧ ω ≠ X.vert 0 ∧ ω ≠ X.vert 2 ∧
      ∀ y : V, Γ.Adj (X.vert 1) y → t • y = y → y = ω := by
  have htG1 : t ∈ X.Gi 1 := (Subgroup.mem_inf.mp ht).2
  have htL1 : t ∈ X.L 1 := by
    obtain ⟨m, hm⟩ := htpow
    exact le_oTwoPrime_of_isPGroup (isPGroup_zpowers_of_pow_two hm)
      (Subgroup.zpowers_le.mpr htG1) (Subgroup.mem_zpowers t)
  have htQ : t ∉ X.Q 1 := by
    intro htQ
    have hfix0 : t • X.vert 0 = X.vert 0 :=
      (X.hyp.isLocL2_oTwoPrime (X.vert 1)).Q_fixes_neighbors X.hyp.adj_smul
        (X.hyp.finite_stab (X.vert 1)) (X.hyp.valency (X.vert 1)).2
        (X.hyp.valency (X.vert 1)).1 (X.vert 0) (by simpa using (X.adj 0).symm) t htQ
    have h20 : X.vert 2 = X.vert 0 := ht02.symm.trans hfix0
    exact (by norm_num : (2 : ℤ) ≠ 0) (X.vert_injective h20)
  have hP2 : IsPGroup 2 ((Subgroup.zpowers t).subgroupOf (X.L 1)) :=
    (isPGroup_zpowers_of_pow_two htpow.choose_spec).comap_subtype
  obtain ⟨S, hSle⟩ := hP2.exists_le_sylow
  have hxS : (⟨t, htL1⟩ : ↥(X.L 1)) ∈ (S : Subgroup ↥(X.L 1)) :=
    hSle (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers t))
  have hxQ : ((⟨t, htL1⟩ : ↥(X.L 1)) : G) ∉
      pCoreOf 2 (MulAction.stabilizer G (X.vert 1)) := by
    simpa [Setup.Q, Setup.Gi] using htQ
  obtain ⟨ω, ⟨hωadj, hωfix⟩, huniq⟩ :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 1)).fixes_unique_of_mem_sylow_not_pcore
      X.hyp.adj_smul (X.hyp.finite_stab (X.vert 1))
      (X.hyp.valency (X.vert 1)).2 (X.hyp.valency (X.vert 1)).1 S hxS hxQ
  have hω0 : ω ≠ X.vert 0 := by
    intro h
    have h20 : X.vert 2 = X.vert 0 := by
      rw [← ht02, ← h]
      exact hωfix
    exact (by norm_num : (2 : ℤ) ≠ 0) (X.vert_injective h20)
  have hω2 : ω ≠ X.vert 2 := by
    intro h
    have h20 : X.vert 2 = X.vert 0 := by
      have h1 : t • X.vert 2 = t • X.vert 0 := by
        rw [← h, hωfix, ht02, h]
      exact smul_left_cancel t h1
    exact (by norm_num : (2 : ℤ) ≠ 0) (X.vert_injective h20)
  exact ⟨ω, hωadj, hωfix, hω0, hω2, fun y hy hyfix => huniq y ⟨hy, hyfix⟩⟩

private theorem Ki_zero_fixes_of_centralizes
    (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) {t : G}
    (ht : t ∈ X.normGi X.QT 1) (ht02 : t • X.vert 0 = X.vert 2)
    (htpow : ∃ m : ℕ, t ^ 2 ^ m = 1) (hcent : ∀ k ∈ X.Ki 0, ⁅k, t⁆ = 1) :
    ∀ k ∈ X.Ki 0, ∀ w : V, Γ.Adj (X.vert 1) w → k • w = w := by
  have hK : ∀ a ∈ X.K, ∀ b ∈ X.K, a * b = b * a :=
    fun a ha b hb' => X.K_mul_comm hb hc hGT hs hodd h5 hX ha hb'
  obtain ⟨ω, hωadj, hωfix, hω0, hω2, huniq⟩ :=
    X.exists_unique_fixed_neighbor_of_two_element ht ht02 htpow
  intro k hk w hw
  obtain ⟨c, hcKi, hc⟩ := X.exists_Ki_smul_eq_of_mem_K hK 1 hk.1
  have hkG1 : k ∈ X.Gi 1 := X.K_le_Gi 1 hk.1
  have hkω : k • ω = ω := by
    have hfix : t • (k • ω) = k • ω := by
      have hkt : k * t = t * k := by
        have h := hcent k hk
        rwa [commutatorElement_eq_one_iff_mul_comm] at h
      calc t • (k • ω) = (t * k) • ω := by rw [mul_smul]
        _ = (k * t) • ω := by rw [hkt]
        _ = k • (t • ω) := by rw [mul_smul]
        _ = k • ω := by rw [hωfix]
    have hkfix1 : k • X.vert 1 = X.vert 1 := MulAction.mem_stabilizer_iff.mp hkG1
    have hadj : Γ.Adj (X.vert 1) (k • ω) := by
      rw [← hkfix1]
      exact (X.hyp.adj_smul k (X.vert 1) ω).mpr hωadj
    exact huniq (k • ω) hadj hfix
  have hcω : c • ω = ω := (hc ω hωadj).trans hkω
  have hc1 : c = 1 := by
    by_contra hcne
    haveI : Finite ↥(X.Ki 1) :=
      finite_of_le_stabilizer X.hyp (H := X.Ki 1) (inf_le_left.trans (X.K_le_Gi 1))
    have hne : X.Ki 1 ≠ ⊥ := by
      intro hbot
      have hcbot : c ∈ (⊥ : Subgroup G) := hbot ▸ hcKi
      exact hcne (Subgroup.mem_bot.mp hcbot)
    have hcard : 1 < Nat.card ↥(X.Ki 1) :=
      (Subgroup.one_lt_card_iff_ne_bot (X.Ki 1)).mpr hne
    rw [X.card_Ki 1] at hcard
    have hn1 : 2 ≤ X.n 1 := by
      have hle : 1 ≤ X.n 1 := (X.hyp.valency (X.vert 1)).1
      by_contra h
      have hlt : X.n 1 < 2 := Nat.lt_of_not_ge h
      have h1 : X.n 1 = 1 := by omega
      rw [h1] at hcard
      norm_num at hcard
    have hcase := (X.torus_fixed 1 hn1 hcKi hcne ω hωadj).mp hcω
    rcases hcase with h | h
    · rw [show (1 : ℤ) - 1 = 0 by norm_num] at h
      exact hω0 h
    · rw [show (1 : ℤ) + 1 = 2 by norm_num] at h
      exact hω2 h
  calc k • w = c • w := (hc w hw).symm
    _ = w := by rw [hc1, one_smul]

private theorem exists_pow_two_of_sq_mem_skP {t : G} (ht2 : t ^ 2 ∈ X.skP X.QT) :
    ∃ m : ℕ, t ^ 2 ^ m = 1 := by
  have hP : IsPGroup 2 (X.skP X.QT) := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hP (⟨t ^ 2, ht2⟩ : ↥(X.skP X.QT))
  refine ⟨k + 1, ?_⟩
  have hk' : (t ^ 2) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by ring, pow_mul]
  exact hk'

theorem commutator_Ki_zero_L_one_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) {t : G}
    (ht : t ∈ X.normGi X.QT 1) (ht02 : t • X.vert 0 = X.vert 2)
    (ht2 : t ^ 2 ∈ X.skP X.QT) (hK0 : ∀ k ∈ X.Ki 0, ⁅k, t⁆ = 1) :
    ⁅X.Ki 0, X.L 1⁆ ≤ X.Q 1 := by
  have htpow : ∃ m : ℕ, t ^ 2 ^ m = 1 := X.exists_pow_two_of_sq_mem_skP ht2
  rw [Subgroup.commutator_le]
  intro k hk l hl
  exact X.commutator_mem_Q_of_fixes_neighbors 1 (X.K_le_Gi 1 hk.1)
    (X.Ki_zero_fixes_of_centralizes hb hc hGT hs hodd h5 hX ht ht02 htpow hK0 k hk) l hl

private theorem conjSub_Vone_le_VnegOne {y : G} (hyG0 : y ∈ X.Gi 0)
    (hy : y • X.vert 1 = X.vert (-1)) : conjSub y X.Vone ≤ X.VnegOne := by
  unfold Setup.Vone Setup.VnegOne
  rw [conjSub_iSup]
  apply iSup_le
  intro g
  rw [conjSub_iSup]
  apply iSup_le
  intro hg
  have hyG : conjSub y (X.Gi 1) = X.Gi (-1) := by
    rw [← stabilizer_smul_eq_conjSub y (X.vert 1), hy]
  have hygy : y * g * y⁻¹ ∈ X.Gi (-1) := by
    rw [← hyG]
    exact mem_conjSub.mpr (by
      rw [show y⁻¹ * (y * g * y⁻¹) * y = g by group]
      exact hg)
  have hconj : conjSub y (conjSub g (X.Z 0)) = conjSub (y * g * y⁻¹) (X.Z 0) := by
    rw [← conjSub_mul]
    have h2 : conjSub (y * g) (X.Z 0) =
        conjSub (y * g * y⁻¹) (conjSub y (X.Z 0)) := by
      rw [← conjSub_mul, show (y * g * y⁻¹) * y = y * g by group]
    rw [h2, X.Z_normal 0 y hyG0]
  rw [hconj]
  exact le_iSup₂_of_le (y * g * y⁻¹) hygy le_rfl

private theorem Ki_zero_commutator_Q_zero_le_of_L1
    (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hK0L1 : ⁅X.Ki 0, X.L 1⁆ ≤ X.Q 1) :
    ⁅X.Ki 0, X.Q 0⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
  have hSGi1 : X.S ≤ X.Gi 1 :=
    (le_sup_right.trans (le_of_eq (X.K_sup_edgeSylow 0))).trans inf_le_right
  have hAnorm : X.Gi 0 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.Q_one_inf_neg_one_normal hb hc hGT hs hodd h5 hX
  have hKL1 : ⁅X.Ki 0, X.L 1⁆ ≤ X.Q 1 := hK0L1
  have hKB : ⁅X.Ki 0, X.VB⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
    apply le_inf
    · refine (Subgroup.commutator_mono le_rfl ?_).trans hKL1
      intro x hx
      have hxE : x ∈ X.edgeSylow 0 := by
        rw [X.edgeSylow_zero]
        exact X.Q_le_edgeSylow_left 0 hx.2
      have hE1 : X.edgeSylow 0 ≤ X.Gi 1 := by
        rw [X.edgeSylow_zero]
        exact hSGi1
      exact le_oTwoPrime_of_isPGroup (X.isPGroup_edgeSylow 0) hE1 hxE
    · exact (Subgroup.commutator_mono le_rfl
        (inf_le_left.trans (X.VnegOne_le_Q_neg_one
          hb hGT hs hodd h5 hX))).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.mp
          ((inf_le_left.trans (X.K_le_Gi (-1))).trans
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))))
  obtain ⟨y, hyL0Ki, hy_move⟩ := X.exists_normalizer_Ki_move
  have hyL0 : y ∈ X.L 0 := hyL0Ki.1
  have hyG0 : y ∈ X.Gi 0 := X.L_le_Gi 0 hyL0
  have hconjK : conjSub y (X.Ki 0) = X.Ki 0 :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer hyL0Ki.2
  have hconjQ : conjSub y (X.Q 0) = X.Q 0 :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hyG0)
  have hconjV : conjSub y X.Vone ≤ X.VnegOne := X.conjSub_Vone_le_VnegOne hyG0 hy_move
  have hKB' : ⁅X.Ki 0, conjSub y X.VA⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
    have hVA : conjSub y X.VA ≤ X.VB := by
      rw [Setup.VA, Setup.VB, conjSub_inf, hconjQ]
      exact inf_le_inf hconjV le_rfl
    exact (Subgroup.commutator_mono le_rfl hVA).trans hKB
  have hKA : ⁅X.Ki 0, X.VA⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
    have h1 : conjSub y ⁅X.Ki 0, X.VA⁆ = ⁅X.Ki 0, conjSub y X.VA⁆ := by
      rw [(conjSub_commutator y (X.Ki 0) X.VA).symm, hconjK]
    have h2 : conjSub y ⁅X.Ki 0, X.VA⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
      rw [h1]
      exact hKB'
    have h3 : ⁅X.Ki 0, X.VA⁆ = conjSub y⁻¹ (conjSub y ⁅X.Ki 0, X.VA⁆) := by
      rw [conjSub_conjSub_inv]
    rw [h3]
    have hAconj_inv : conjSub y⁻¹ (X.Q 1 ⊓ X.Q (-1)) = X.Q 1 ⊓ X.Q (-1) :=
      CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
        (hAnorm ((X.Gi 0).inv_mem hyG0))
    refine (conjSub_mono y⁻¹ h2).trans ?_
    rw [hAconj_inv]
  have hKA' : ⁅X.Ki 0, (X.Q 1 ⊓ X.Q (-1))⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (((inf_le_left : X.Ki 0 ≤ X.K).trans (X.K_le_Gi 0)).trans hAnorm)
  have hQsup := X.Q_zero_eq_sup hb hc hGT hs hodd h5 hX
  have hA'Q0 : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 := by
    rw [hQsup]
    exact le_sup_of_le_right le_rfl
  have hcl : X.VA ⊔ X.VB ⊔ (X.Q 1 ⊓ X.Q (-1)) =
      Subgroup.closure ((X.VA : Set G) ∪ (X.VB : Set G) ∪
        ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_union,
      Subgroup.closure_eq, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hQsup]
  change ⁅X.Ki 0, X.VA ⊔ X.VB ⊔ (X.Q 1 ⊓ X.Q (-1))⁆ ≤ X.Q 1 ⊓ X.Q (-1)
  rw [hcl]
  refine CFSG.Quasithin.D14.commutator_le_closure ?_ ?_
  · rw [← hcl]
    exact (sup_le (sup_le (show X.VA ≤ X.Q 0 from inf_le_right)
      (show X.VB ≤ X.Q 0 from inf_le_right)) hA'Q0).trans
      ((X.Q_le_Gi 0).trans hAnorm)
  rintro k hk s ((hs | hs) | hs)
  · exact hKA (Subgroup.commutator_mem_commutator hk hs)
  · exact hKB (Subgroup.commutator_mem_commutator hk hs)
  · exact hKA' (Subgroup.commutator_mem_commutator hk hs)

private theorem map_subgroupOf_ne_bot_of_Ki_zero_le
    (hN : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0)) (hn0 : 2 ≤ X.n 0)
    {N : Subgroup G} (hK0N : X.Ki 0 ≤ N) :
    (N.subgroupOf (X.L 0)).map hN.phi ≠ ⊥ := by
  have hpow : 4 ≤ 2 ^ X.n 0 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
  haveI : Finite ↥(X.Ki 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Ki 0) (inf_le_left.trans (X.K_le_Gi 0))
  have hcard : 1 < Nat.card ↥(X.Ki 0) := by
    rw [X.card_Ki 0]
    omega
  have hne : X.Ki 0 ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot (X.Ki 0)).mp hcard
  intro hbot
  obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hmemRL : hN.phi ⟨k, hk.2⟩ ∈ (N.subgroupOf (X.L 0)).map hN.phi :=
    Subgroup.mem_map_of_mem hN.phi
      (show (⟨k, hk.2⟩ : ↥(X.L 0)) ∈ N.subgroupOf (X.L 0) from hK0N hk)
  have hphi_ne : hN.phi ⟨k, hk.2⟩ ≠ 1 := by
    intro h1
    have hkQ : k ∈ X.Q 0 := by
      have := (hN.phi_ker ⟨k, hk.2⟩).mp h1
      simpa [Setup.Q, Setup.Gi] using this
    have hbot0 : X.Ki 0 ⊓ X.Q 0 = ⊥ := X.Ki_inf_Q (X.Q_le_edgeSylow_left 0)
    have hmem : k ∈ X.Ki 0 ⊓ X.Q 0 := ⟨hk, hkQ⟩
    rw [hbot0, Subgroup.mem_bot] at hmem
    exact hk1' hmem
  have hmem : hN.phi ⟨k, hk.2⟩ ∈
      (⊥ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 (X.n 0)))) := by
    rw [← hbot]
    exact hmemRL
  exact hphi_ne (Subgroup.mem_bot.mp hmem)

private theorem exists_mem_Q_zero_mul_of_Ki_zero_le (hn0 : 2 ≤ X.n 0)
    {N : Subgroup G} (hK0N : X.Ki 0 ≤ N) (hNL0 : N ≤ X.L 0)
    (hNnorm : X.L 0 ≤ Subgroup.normalizer (N : Set G)) :
    ∀ l ∈ X.L 0, ∃ u ∈ X.Q 0, ∃ r ∈ N, u * r = l := by
  let P := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0))
  have hN : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  let φ : ↥(X.L 0) →* P := hN.phi
  let RL : Subgroup P := (N.subgroupOf (X.L 0)).map φ
  have hcardF : 4 ≤ Nat.card (GaloisField 2 (X.n 0)) := by
    rw [GaloisField.card (p := 2) (n := X.n 0) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) hn0
  haveI : IsSimpleGroup P := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  have hRLnormal : RL.Normal := by
    haveI : (N.subgroupOf (X.L 0)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNnorm
    exact Subgroup.Normal.map (inferInstance : (N.subgroupOf (X.L 0)).Normal) φ
      hN.phi_surjective
  have hRLne : RL ≠ ⊥ := by
    show (N.subgroupOf (X.L 0)).map hN.phi ≠ ⊥
    exact X.map_subgroupOf_ne_bot_of_Ki_zero_le hN hn0 hK0N
  have hRLtop : RL = ⊤ := by
    haveI := hRLnormal
    rcases Subgroup.Normal.eq_bot_or_eq_top RL with h | h
    · exact absurd h hRLne
    · exact h
  intro l hl
  have hmemRL : φ ⟨l, hl⟩ ∈ RL := by
    rw [hRLtop]
    exact Subgroup.mem_top _
  obtain ⟨r, hr, hrr⟩ := Subgroup.mem_map.mp hmemRL
  have hrR : (r : G) ∈ N := hr
  refine ⟨l * (r : G)⁻¹, ?_, (r : G), hrR, by group⟩
  have hrL0 : (r : G) ∈ X.L 0 := hNL0 hrR
  have huL0 : l * (r : G)⁻¹ ∈ X.L 0 :=
    (X.L 0).mul_mem hl ((X.L 0).inv_mem hrL0)
  have hρu : φ ⟨l * (r : G)⁻¹, huL0⟩ = 1 := by
    have hsub : (⟨l * (r : G)⁻¹, huL0⟩ : ↥(X.L 0)) = ⟨l, hl⟩ * r⁻¹ :=
      Subtype.ext (by simp)
    rw [hsub, map_mul, map_inv, hrr, mul_inv_cancel]
  have hker := (hN.phi_ker ⟨l * (r : G)⁻¹, huL0⟩).mp hρu
  simpa [Setup.Q, Setup.Gi] using hker

theorem commutator_Q_zero_L_zero_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) (hK0L1 : ⁅X.Ki 0, X.L 1⁆ ≤ X.Q 1) :
    ⁅X.Q 0, X.L 0⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
  have hAnorm : X.Gi 0 ≤ Subgroup.normalizer ((X.Q 1 ⊓ X.Q (-1) : Subgroup G) : Set G) :=
    X.Q_one_inf_neg_one_normal hb hc hGT hs hodd h5 hX
  have hKQ : ⁅X.Ki 0, X.Q 0⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    X.Ki_zero_commutator_Q_zero_le_of_L1 hb hc hGT hs hodd h5 hX hK0L1
  have hQQ : ⁅X.Q 0, X.Q 0⁆ ≤ X.Q 1 ⊓ X.Q (-1) :=
    (X.isElemSec_Q_one_inf_Q_neg_one hb hc hGT hs hodd h5 hX).2.1
  let gen : Set G := {x | ∃ l ∈ X.L 0, ∃ k ∈ X.Ki 0, x = l * k * l⁻¹}
  let N : Subgroup G := Subgroup.closure gen
  have hK0N : X.Ki 0 ≤ N := by
    intro k hk
    exact Subgroup.subset_closure ⟨1, (X.L 0).one_mem, k, hk, by simp⟩
  have hNL0 : N ≤ X.L 0 := by
    rw [Subgroup.closure_le]
    rintro x ⟨l, hl, k, hk, rfl⟩
    exact (X.L 0).mul_mem ((X.L 0).mul_mem hl hk.2) ((X.L 0).inv_mem hl)
  have hNnorm : X.L 0 ≤ Subgroup.normalizer (N : Set G) := by
    intro l₀ hl₀
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub l₀ N = N
    have hgen : (fun x => l₀ * x * l₀⁻¹) '' gen = gen := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases hy with ⟨l, hl, k, hk, rfl⟩
        exact ⟨l₀ * l, (X.L 0).mul_mem hl₀ hl, k, hk, by group⟩
      · rintro ⟨l, hl, k, hk, rfl⟩
        exact ⟨(l₀⁻¹ * l) * k * (l₀⁻¹ * l)⁻¹,
          ⟨l₀⁻¹ * l, (X.L 0).mul_mem ((X.L 0).inv_mem hl₀) hl, k, hk, rfl⟩, by group⟩
    rw [conjSub_closure, hgen]
  have hNcomm : ⁅N, X.Q 0⁆ ≤ X.Q 1 ⊓ X.Q (-1) := by
    refine CFSG.Quasithin.D14.commutator_closure_le
      (hNL0.trans ((X.L_le_Gi 0).trans hAnorm)) ?_
    rintro _ ⟨l, hl, k, hk, rfl⟩ q hq
    have hlG0 : l ∈ X.Gi 0 := X.L_le_Gi 0 hl
    have hq' : l⁻¹ * q * l ∈ X.Q 0 := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
          ((X.Gi 0).inv_mem hlG0)) q).mp hq
    have hkq : ⁅k, l⁻¹ * q * l⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
      hKQ (Subgroup.commutator_mem_commutator hk hq')
    have heq : ⁅l * k * l⁻¹, q⁆ = l * ⁅k, l⁻¹ * q * l⁆ * l⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [heq]
    simpa using (Subgroup.mem_normalizer_iff.mp (hAnorm hlG0)
      ⁅k, l⁻¹ * q * l⁆).mp hkq
  have hdecomp := X.exists_mem_Q_zero_mul_of_Ki_zero_le hn0 hK0N hNL0 hNnorm
  rw [Subgroup.commutator_le]
  intro q hq l hl
  obtain ⟨u, huQ, r, hrN, hur⟩ := hdecomp l hl
  have hrq : ⁅r, q⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
    hNcomm (Subgroup.commutator_mem_commutator hrN hq)
  have hqr : ⁅q, r⁆ ∈ X.Q 1 ⊓ X.Q (-1) := by
    rw [show ⁅q, r⁆ = (⁅r, q⁆)⁻¹ by simp only [commutatorElement_def]; group]
    exact (X.Q 1 ⊓ X.Q (-1)).inv_mem hrq
  have hconj : u * ⁅q, r⁆ * u⁻¹ ∈ X.Q 1 ⊓ X.Q (-1) := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hAnorm (X.Q_le_Gi 0 huQ)) ⁅q, r⁆).mp hqr
  have hlu : ⁅q, u⁆ ∈ X.Q 1 ⊓ X.Q (-1) :=
    hQQ (Subgroup.commutator_mem_commutator hq huQ)
  have heq : ⁅q, l⁆ = ⁅q, u⁆ * (u * ⁅q, r⁆ * u⁻¹) := by
    rw [← hur]
    simp only [commutatorElement_def]; group
  rw [heq]
  exact (X.Q 1 ⊓ X.Q (-1)).mul_mem hlu hconj

private theorem false_of_centralizes_Ki_zero
    (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) {t : G} (ht : t ∈ X.normGi X.QT 1)
    (ht2 : t ^ 2 ∈ X.skP X.QT) (ht02 : t • X.vert 0 = X.vert 2)
    (hcent : ∀ k ∈ X.Ki 0, ⁅k, t⁆ = 1) : False := by
  let A := X.Q 1 ⊓ X.Q (-1)
  let H := X.Q 0 ⊓ X.Q (-1)
  have hK0L1 : ⁅X.Ki 0, X.L 1⁆ ≤ X.Q 1 :=
    X.commutator_Ki_zero_L_one_le hb hc hGT hs hodd h5 hX ht ht02 ht2 hcent
  have hQL : ⁅X.Q 0, X.L 0⁆ ≤ A :=
    X.commutator_Q_zero_L_zero_le hb hc hGT hs hodd h5 hX hn0 hK0L1
  have hQQ : ⁅X.Q 0, X.Q 0⁆ ≤ A :=
    (X.isElemSec_Q_one_inf_Q_neg_one hb hc hGT hs hodd h5 hX).2.1
  have hQsup := X.Q_zero_eq_sup hb hc hGT hs hodd h5 hX
  have hAQ0 : A ≤ X.Q 0 := by
    rw [hQsup]
    exact le_sup_of_le_right le_rfl
  have hAH : A ≤ H := le_inf hAQ0 inf_le_right
  have hQ1L0 : X.Q 1 ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1))
      ((X.Q_le_Gi_adj 1).trans inf_le_left)
  have h1 : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      (((Subgroup.commutator_mono inf_le_left inf_le_left).trans hQQ).trans hAH)
  have h2 : X.Q 1 ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((((Subgroup.commutator_mono hQ1L0 inf_le_left).trans
        (Subgroup.commutator_comm _ _).le).trans hQL).trans hAH)
  exact (X.not_normal_Q_zero_inf_one hc hs h5)
    ⟨h1, h2⟩

theorem commutator_K_t_le_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    {t : G} (ht : t ∈ X.normGi X.QT 1)
    (htK : t ∈ Subgroup.normalizer (X.K : Set G)) :
    ∀ k ∈ X.K, ⁅k, t⁆ ∈ X.Ki 1 := by
  intro k hk
  have htG1 : t ∈ X.Gi 1 := (Subgroup.mem_inf.mp ht).2
  have hG : X.Gi 1 = X.L 1 ⊔ X.K := X.Gi_eq_L_sup_K 1
  have hKL : X.K ≤ Subgroup.normalizer (X.L 1 : Set G) :=
    X.K_le_Gi 1 |>.trans (le_normalizer_oTwoPrime (X.Gi 1))
  have ht' : t ∈ X.K ⊔ X.L 1 := by
    rw [sup_comm, ← hG]
    exact htG1
  obtain ⟨c, hcK, l, hl, hcl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hKL).mp ht'
  have hck : c * k = k * c := X.K_mul_comm hb hc hGT hs hodd h5 hX hcK hk
  have hktL1 : ⁅k, t⁆ ∈ X.L 1 := by
    have hkG1 : k ∈ X.Gi 1 := X.K_le_Gi 1 hk
    have hkL : k * l * k⁻¹ ∈ X.L 1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoPrime (X.Gi 1) hkG1) l).mp hl
    have hu : k * l * k⁻¹ * l⁻¹ ∈ X.L 1 := (X.L 1).mul_mem hkL ((X.L 1).inv_mem hl)
    have hcG1 : c ∈ X.Gi 1 := X.K_le_Gi 1 hcK
    have hconj : c * (k * l * k⁻¹ * l⁻¹) * c⁻¹ ∈ X.L 1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoPrime (X.Gi 1) hcG1)
        (k * l * k⁻¹ * l⁻¹)).mp hu
    have heq : ⁅k, t⁆ = c * (k * l * k⁻¹ * l⁻¹) * c⁻¹ := by
      rw [hcl]
      calc k * (c * l) * k⁻¹ * (c * l)⁻¹
          = (k * c) * l * k⁻¹ * (l⁻¹ * c⁻¹) := by group
        _ = (c * k) * l * k⁻¹ * (l⁻¹ * c⁻¹) := by rw [hck]
        _ = c * (k * l * k⁻¹ * l⁻¹) * c⁻¹ := by group
    rw [heq]
    exact hconj
  have hktK : ⁅k, t⁆ ∈ X.K := by
    have hconj : t * k⁻¹ * t⁻¹ ∈ X.K :=
      (Subgroup.mem_normalizer_iff.mp htK k⁻¹).mp ((X.K).inv_mem hk)
    have heq : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact (X.K).mul_mem hk hconj
  exact Subgroup.mem_inf.mpr ⟨hktK, hktL1⟩

theorem exists_commutator_Ki_zero_t_ne_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) {t : G} (ht : t ∈ X.normGi X.QT 1)
    (ht02 : t • X.vert 0 = X.vert 2)
    (ht2 : t ^ 2 ∈ X.skP X.QT) :
    ∃ k ∈ X.Ki 0, ⁅k, t⁆ ≠ 1 := by
  by_contra hcon
  have hcent : ∀ k ∈ X.Ki 0, ⁅k, t⁆ = 1 := by
    intro k hk
    by_contra hne
    exact hcon ⟨k, hk, hne⟩
  exact X.false_of_centralizes_Ki_zero hb hc hGT hs hodd h5 hX hn0
    ht ht2 ht02 hcent

theorem Ki_zero_le_Lst (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s) (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) : X.Ki 0 ≤ X.Lst X.QT 0 := by
  have hU : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  have hP : ¬ X.skP X.QT ≤ X.Q 0 ∨ 2 ≤ X.n 0 := Or.inr hn0
  have hL0 : X.L 0 = X.Lst X.QT 0 ⊔ X.Q 0 := X.L_eq_Lst_sup_Q hU hP
  have hLstQ0 : X.Lst X.QT 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (oTwoPrime_le (X.normGi X.QT 0)).trans
      ((X.normGi_le_Gi X.QT 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have hELst : X.E X.QT 0 ≤ X.Lst X.QT 0 := by
    rw [X.E_eq_pCoreOf hU]
    exact le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.normGi X.QT 0))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.normGi X.QT 0))
  have hK0M : X.Ki 0 ≤ X.normGi X.QT 0 :=
    le_inf ((inf_le_left : X.Ki 0 ≤ X.K).trans X.K_le_normalizer_QT)
      ((inf_le_left : X.Ki 0 ≤ X.K).trans (X.K_le_Gi 0))
  intro z hz
  have hzL : z ∈ X.L 0 := (inf_le_right : X.Ki 0 ≤ X.L 0) hz
  have hzM : z ∈ X.normGi X.QT 0 := hK0M hz
  have hLM : X.L 0 ⊓ X.normGi X.QT 0 = X.Lst X.QT 0 := by
    rw [hL0, inf_comm,
      CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer (S := X.Lst X.QT 0)
        (U := X.normGi X.QT 0)
        (T := X.Q 0) (oTwoPrime_le _) hLstQ0]
    rw [inf_comm (X.normGi X.QT 0) (X.Q 0), ← X.E_eq_Q_inf_normGi X.QT 0, sup_eq_left.mpr hELst]
  exact hLM ▸ Subgroup.mem_inf.mpr ⟨hzL, hzM⟩

private theorem commutator_Ki_zero_QT_eq_bot (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) : ⁅X.Ki 0, X.QT⁆ = ⊥ := by
  have hKL : X.Ki 0 ≤ X.Lst X.QT 0 := X.Ki_zero_le_Lst hGT hs hodd h5 hX hn0
  have hcomm : ⁅X.QT, X.Lst X.QT 0⁆ = ⊥ :=
    X.commutator_QT_Lst_eq_bot hGT hs hodd h5 hX
  have h : ⁅X.Ki 0, X.QT⁆ ≤ ⁅X.QT, X.Lst X.QT 0⁆ :=
    (Subgroup.commutator_mono hKL le_rfl).trans (Subgroup.commutator_comm _ _).le
  rw [hcomm] at h
  exact le_bot_iff.mp h

private theorem commutator_Ktwo_QT_eq_bot (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) : ⁅X.Ktwo, X.QT⁆ = ⊥ := by
  have h0 : ⁅X.Ki 0, X.QT⁆ = ⊥ :=
    X.commutator_Ki_zero_QT_eq_bot hGT hs hodd h5 hX hn0
  have hτQ : conjSub X.τ X.QT = X.QT :=
    CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer X.tau_mem_normalizer_QT
  have h : ⁅X.Ktwo, X.QT⁆ = conjSub X.τ ⁅X.Ki 0, X.QT⁆ := by
    rw [← conjSub_commutator X.τ (X.Ki 0) X.QT, hτQ]
    rfl
  rw [h0, conjSub_bot] at h
  exact h

theorem R_ne_bot (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) : X.R ≠ ⊥ := by
  have hU : X.IsSK X.QT := X.isSK_QT hGT hs hodd h5 hX
  obtain ⟨t, ht, ht02, -, ht2⟩ := IsSK.exists_t X hU
  have htM : t ∈ X.normGi X.QT 1 := (Subgroup.mem_inf.mp ht).1
  have htK : t ∈ Subgroup.normalizer (X.K : Set G) := (Subgroup.mem_inf.mp ht).2
  obtain ⟨k, hk0, hkt⟩ :=
    X.exists_commutator_Ki_zero_t_ne_one hb hc hGT hs hodd h5 hX hn0 htM ht02 ht2
  have hktKi1 : ⁅k, t⁆ ∈ X.Ki 1 :=
    X.commutator_K_t_le_one hb hc hGT hs hodd h5 hX htM htK k hk0.1
  have htKi2 : conjSub t (X.Ki 0) = X.Ktwo := by
    rw [X.Ktwo_eq_Ki_two]
    have hK : conjSub t X.K = X.K :=
      CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer htK
    have hG : conjSub t (X.Gi 0) = X.Gi 2 := by
      rw [← stabilizer_smul_eq_conjSub t (X.vert 0), ht02]
    have hL : conjSub t (X.L 0) = X.L 2 := by
      change conjSub t (oTwoPrime (X.Gi 0)) = oTwoPrime (X.Gi 2)
      rw [conjSub_oTwoPrime, hG]
    change conjSub t (X.K ⊓ X.L 0) = X.K ⊓ X.L 2
    rw [conjSub_inf, hK, hL]
  have hktK02 : ⁅k, t⁆ ∈ X.Ki 0 ⊔ X.Ktwo := by
    have hconj : t * k⁻¹ * t⁻¹ ∈ X.Ktwo := by
      rw [← htKi2]
      exact mul_mem_conjSub ((X.Ki 0).inv_mem hk0)
    have heq : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hk0 hconj
  intro hRbot
  have hmemR : ⁅k, t⁆ ∈ X.R := by
    change ⁅k, t⁆ ∈ (X.Ki 0 ⊔ X.Ktwo) ⊓ X.Ki 1
    exact Subgroup.mem_inf.mpr ⟨hktK02, hktKi1⟩
  rw [hRbot, Subgroup.mem_bot] at hmemR
  exact hkt hmemR

theorem commutator_R_QT_eq_bot (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s)
    (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) : ⁅X.R, X.QT⁆ = ⊥ := by
  have hK0 := X.commutator_Ki_zero_QT_eq_bot hGT hs hodd h5 hX hn0
  have hK2 := X.commutator_Ktwo_QT_eq_bot hGT hs hodd h5 hX hn0
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((inf_le_left : X.R ≤ X.Ki 0 ⊔ X.Ktwo).trans
      (sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK0)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK2)))

theorem commutator_R_Z_one_eq_bot (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) : ⁅X.R, X.Z 1⁆ = ⊥ := by
  have hRle : X.R ≤ X.Ki 1 := inf_le_right
  have hRL : X.R ≤ X.L 1 := hRle.trans (inf_le_right : X.Ki 1 ≤ X.L 1)
  have hZ : X.Z 1 = centerOf (X.L 1) :=
    X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro r hr z hz
  have hzcent : z ∈ Subgroup.centralizer (X.L 1 : Set G) := by
    rw [hZ] at hz
    exact hz.2
  have hcomm : r * z = z * r := Subgroup.mem_centralizer_iff.mp hzcent r (hRL hr)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm

theorem commutator_commutator_VA_R_QT_eq_bot (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) :
    ⁅⁅X.VA, X.R⁆, X.QT⁆ = ⊥ := by
  have hRQ : ⁅X.R, X.QT⁆ = ⊥ :=
    X.commutator_R_QT_eq_bot hGT hs hodd h5 hX hn0
  have hRZ : ⁅X.R, X.Z 1⁆ = ⊥ :=
    X.commutator_R_Z_one_eq_bot hb hc hGT hs hodd h5 hX
  have hVone : X.VA ≤ X.Vone := inf_le_left
  have hQT1 : X.QT ≤ X.Q 1 := X.QT_le_Q 1
  have hQVA : ⁅X.QT, X.VA⁆ ≤ X.Z 1 := by
    calc ⁅X.QT, X.VA⁆ ≤ ⁅X.Q 1, X.Vone⁆ :=
          Subgroup.commutator_mono hQT1 hVone
      _ = ⁅X.Vone, X.Q 1⁆ := Subgroup.commutator_comm _ _
      _ = X.Z 1 := X.commutator_Vone_Q_one hb hc hGT hs hodd h5 hX
  have h1 : ⁅⁅X.R, X.QT⁆, X.VA⁆ = ⊥ := by
    rw [hRQ]
    exact Subgroup.commutator_bot_left (H₁ := X.VA)
  have h2 : ⁅⁅X.QT, X.VA⁆, X.R⁆ = ⊥ := by
    have h : ⁅⁅X.QT, X.VA⁆, X.R⁆ ≤ ⁅X.R, X.Z 1⁆ :=
      (Subgroup.commutator_mono hQVA le_rfl).trans (Subgroup.commutator_comm _ _).le
    rw [hRZ] at h
    exact le_bot_iff.mp h
  exact Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := X.VA) (H₂ := X.R)
    (H₃ := X.QT) h1 h2

private theorem commutator_L_le_Q_of_commutator_edgeSylow_le (j : ℤ)
    {H : Subgroup G} (hHK : H ≤ X.K) (hSH : ⁅X.edgeSylow j, H⁆ ≤ X.Q j) :
    ⁅X.L j, H⁆ ≤ X.Q j := by
  have hrev : X.reverse.edgeSylow (-j - 1) = X.edgeSylow j := by
    show pCoreOf 2 (X.reverse.Gi (-j - 1) ⊓ X.reverse.Gi (-j - 1 + 1)) = X.edgeSylow j
    rw [X.reverse_Gi, X.reverse_Gi, show -(-j - 1) = j + 1 by ring,
      show -(-j - 1 + 1) = j by ring, inf_comm]
  rw [Subgroup.commutator_le]
  intro l hl h hh
  have hhK : h ∈ X.K := hHK hh
  have hfix : ∀ w : V, Γ.Adj (X.vert j) w → h • w = w := by
    have := X.reverse.fixes_neighbors_of_centralizes_edgeSylow_gen (-j)
      (k := h) (by rw [X.reverse_Gi]; exact X.K_le_Gi _ hhK)
      (by rw [X.reverse_Gi]; exact X.K_le_Gi _ hhK)
      (X.odd_card_K.of_dvd_nat (Subgroup.orderOf_dvd_natCard X.K hhK)) (fun x hx => by
        rw [hrev] at hx
        rw [X.reverse_Q, neg_neg, ← commutatorElement_inv]
        exact (X.Q j).inv_mem (hSH (Subgroup.commutator_mem_commutator hx hh)))
    simpa using this
  rw [← commutatorElement_inv]
  exact (X.Q j).inv_mem
    (X.commutator_mem_Q_of_fixes_neighbors j (X.K_le_Gi j hhK) hfix l hl)

private theorem K_le_normalizer_VA : X.K ≤ Subgroup.normalizer (X.VA : Set G) :=
  CFSG.Quasithin.F7.le_normalizer_inf
    ((X.K_le_Gi 1).trans X.Gi_one_le_normalizer_Vone)
    ((X.K_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))

private theorem R_le_K : X.R ≤ X.K :=
  inf_le_right.trans (inf_le_left : X.Ki 1 ≤ X.K)

private theorem E_le_Q_neg_one (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.E X.QT 0 ≤ X.Q (-1) := by
  refine le_pCoreOf_of_isPGroup_fixes_two X.hyp ?_ ?_ (by simpa using (X.adj (-2)).symm)
    (by simpa using X.adj (-1)) ?_ ?_ ?_
  · exact (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  · intro e he
    exact X.mem_Gi_of_between (m := -2) (r := 0) (k := -1)
      (X.E_QT_le_Gi_two hGT hs hodd h5 hX he).2
      (X.Q_le_Gi 0 he.1) (by norm_num) (by norm_num)
  · intro h
    have := X.vert_injective h
    norm_num at this
  · intro e he
    exact MulAction.mem_stabilizer_iff.mp
      ((X.E_QT_le_Gi_two hGT hs hodd h5 hX he).2)
  · intro e he
    exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 0 he.1)

private theorem edgeSylow_neg_one_eq_sup_VA (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    X.edgeSylow (-1) = X.Q (-1) ⊔ X.VA := by
  have hVneg : X.VnegOne ≤ X.Q (-1) :=
    X.VnegOne_le_Q_neg_one hb hGT hs hodd h5 hX
  have hS : X.edgeSylow (-1) = X.Q (-1) ⊔ X.Q 0 := by
    have h := X.sup_Q_eq_edgeSylow hc (-1)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
    exact h.symm
  rw [hS, X.Q_zero_eq_sup hb hc hGT hs hodd h5 hX]
  change X.Q (-1) ⊔ ((X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔
    (X.Q 1 ⊓ X.Q (-1))) = X.Q (-1) ⊔ (X.Vone ⊓ X.Q 0)
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    refine sup_le ?_ ?_
    · refine sup_le (le_sup_of_le_right le_rfl) ?_
      exact le_sup_of_le_left ((inf_le_left : X.VnegOne ⊓ X.Q 0 ≤ X.VnegOne).trans hVneg)
    · exact le_sup_of_le_left inf_le_right
  · exact sup_le le_sup_left ((le_sup_left.trans le_sup_left).trans le_sup_right)

theorem commutator_L_neg_one_R_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : 2 ≤ X.n 0) : ⁅X.L (-1), X.R⁆ ≤ X.Q (-1) := by
  have hAR : ⁅X.VA, X.R⁆ ≤ X.Q (-1) := by
    have hVA_le : ⁅X.VA, X.R⁆ ≤ X.VA :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        (X.R_le_K.trans X.K_le_normalizer_VA)
    have hcent : ⁅X.VA, X.R⁆ ≤ Subgroup.centralizer (X.QT : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (X.commutator_commutator_VA_R_QT_eq_bot hb hc hGT hs hodd h5 hX hn0)
    have hE : ⁅X.VA, X.R⁆ ≤ X.E X.QT 0 :=
      le_inf (hVA_le.trans inf_le_right)
        (hcent.trans (Subgroup.centralizer_le_normalizer (X.QT : Set G)))
    exact hE.trans (X.E_le_Q_neg_one hGT hs hodd h5 hX)
  have hQR : ⁅X.Q (-1), X.R⁆ ≤ X.Q (-1) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((X.R_le_K.trans (X.K_le_Gi (-1))).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1))))
  have hQ0G : X.Q 0 ≤ X.Gi (-1) := fun x hx => MulAction.mem_stabilizer_iff.mpr
    (X.Q_fixes_neighbors_vert 0 (X.vert (-1)) (by simpa using (X.adj (-1)).symm) x hx)
  have hVAn : X.VA ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (inf_le_right : X.VA ≤ X.Q 0).trans
      (hQ0G.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1))))
  have hS_eq : X.edgeSylow (-1) = X.Q (-1) ⊔ X.VA :=
    X.edgeSylow_neg_one_eq_sup_VA hb hc hGT hs hodd h5 hX
  have hSR : ⁅X.edgeSylow (-1), X.R⁆ ≤ X.Q (-1) := by
    rw [hS_eq, sup_comm]
    exact CFSG.Quasithin.D14.commutator_sup_le_of hVAn hVAn hQR hAR
  exact X.commutator_L_le_Q_of_commutator_edgeSylow_le (-1) X.R_le_K hSR

theorem commutator_L_neg_two_R_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.L (-2), X.R⁆ ≤ X.Q (-2) := by
  have hZ1Gm2 : X.Z 1 ≤ X.Gi (-2) := fun z hz =>
    (X.Z_one_le_Gi hb hc hGT hs hodd h5 hX hz).1
  have hZ1G1 : X.Z 1 ≤ X.Gi 1 := X.Z_le_Gi 1
  have hZ1Gm1 : X.Z 1 ≤ X.Gi (-1) := by
    intro z hz
    exact X.mem_Gi_of_between (m := -2) (r := 1) (k := -1)
      (hZ1Gm2 hz) (hZ1G1 hz) (by norm_num) (by norm_num)
  have hZ1G0 : X.Z 1 ≤ X.Gi 0 := by
    intro z hz
    exact X.mem_Gi_of_between (m := -2) (r := 1) (k := 0)
      (hZ1Gm2 hz) (hZ1G1 hz) (by norm_num) (by norm_num)
  have hnotGm3 : ¬ X.Z 1 ≤ X.Gi (-3) := by
    intro hle
    have hfix : X.Z 1 ≤ MulAction.stabilizer G (X.vert (-3)) := by rwa [← Setup.Gi]
    have hd4 : Γ.dist (X.vert 1) (X.vert (-3)) = 4 := by
      rw [SimpleGraph.dist_comm]
      have hh := Line.dist_eq X.hyp.isTree X.line (i := (-3 : ℤ)) (j := 1) (by norm_num)
      simpa using hh
    have hfix5 : X.Z 1 ≤ MulAction.stabilizer G (X.vert 5) := by
      refine X.Z_fixes_of_dist 1 hs (by omega) hd4 hfix (X.vert 5) ?_
      rw [Line.dist_eq X.hyp.isTree X.line (i := (1 : ℤ)) (j := 5) (by norm_num)]
      norm_num
    exact X.Z_one_not_le_Gi_five hb hc hGT hs hodd h5 hX
      (by rwa [← Setup.Gi] at hfix5)
  have hZ1Qm1 : X.Z 1 ≤ X.Q (-1) := by
    refine le_pCoreOf_of_isPGroup_fixes_two X.hyp ?_ hZ1Gm1
      (by simpa using (X.adj (-2)).symm) (by simpa using X.adj (-1)) ?_ ?_ ?_
    · exact (pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1)
    · intro h
      have := X.vert_injective h
      norm_num at this
    · intro z hz
      exact MulAction.mem_stabilizer_iff.mp (hZ1Gm2 hz)
    · intro z hz
      exact MulAction.mem_stabilizer_iff.mp (hZ1G0 hz)
  have hZ1S : X.Z 1 ≤ X.edgeSylow (-2) :=
    hZ1Qm1.trans (X.Q_le_edgeSylow_right (-1))
  have hZ1notQm2 : ¬ X.Z 1 ≤ X.Q (-2) := by
    intro hle
    apply hnotGm3
    intro z hz
    exact MulAction.mem_stabilizer_iff.mpr
      (X.Q_fixes_neighbors_vert (-2) (X.vert (-3)) (by simpa using (X.adj (-3)).symm)
        z (hle hz))
  have hKnormZ1 : X.K ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [conjSub] using X.Z_normal 1 k (X.K_le_Gi 1 hk)
  have hS_eq : X.Z 1 ⊔ X.Q (-2) = X.edgeSylow (-2) :=
    X.sup_Q_eq_edgeSylow_of_left_gen (-2) (inf_le_left.trans hKnormZ1) hZ1S hZ1notQm2
  have hZ1N : X.Z 1 ≤ Subgroup.normalizer (X.Q (-2) : Set G) :=
    hZ1Gm2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-2)))
  have hQR2 : ⁅X.Q (-2), X.R⁆ ≤ X.Q (-2) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((X.R_le_K.trans (X.K_le_Gi (-2))).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-2))))
  have hZR : ⁅X.Z 1, X.R⁆ ≤ X.Q (-2) := by
    rw [Subgroup.commutator_comm, X.commutator_R_Z_one_eq_bot hb hc hGT hs hodd h5 hX]
    exact bot_le
  have hSR : ⁅X.edgeSylow (-2), X.R⁆ ≤ X.Q (-2) := by
    rw [← hS_eq]
    exact CFSG.Quasithin.D14.commutator_sup_le_of hZ1N hZ1N hQR2 hZR
  exact X.commutator_L_le_Q_of_commutator_edgeSylow_le (-2) X.R_le_K hSR

theorem false_of_two_le_n_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hn0 : 2 ≤ X.n 0) : False := by
  have hoddR : Odd (Nat.card ↥(X.R)) :=
    X.odd_card_K.of_dvd_nat (Subgroup.card_dvd_of_le X.R_le_K)
  have hRGi : X.R ≤ X.Gi (-2) ⊓ X.Gi (-1) :=
    le_inf ((inf_le_right.trans (inf_le_left : X.Ki 1 ≤ X.K)).trans (X.K_le_Gi (-2)))
      ((inf_le_right.trans (inf_le_left : X.Ki 1 ≤ X.K)).trans (X.K_le_Gi (-1)))
  have hRbot : X.R = ⊥ :=
    X.eq_bot_of_commutator_le_Q (X.adj (-2)) hoddR hRGi
      (X.commutator_L_neg_two_R_le hb hc hGT hs hodd h5 hX)
      (X.commutator_L_neg_one_R_le hb hc hGT hs hodd h5 hX hn0)
  exact X.R_ne_bot hb hc hGT hs hodd h5 hX hn0 hRbot

end Setup

end CFSG.Quasithin.St84
