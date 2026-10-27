module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType

theorem ggHalf_card_ge_of_orbit {G X : Type} [Group G] [MulAction G X] [Finite G]
    (H T : Subgroup G) (x : X) (k : ℕ) (h : Fin k → G) (hH : ∀ i, h i ∈ H)
    (hinj : Function.Injective fun i => h i • x) (hT : T ≤ H) (hfix : ∀ t ∈ T, t • x = x)
    (s : ℕ) (hs : s ≤ Nat.card T) : k * s ≤ Nat.card H := by
  classical
  haveI hfinOrbit : Finite (MulAction.orbit H x) :=
    (Set.finite_range (fun g : H => g • x)).to_subtype
  have hcard : Nat.card H = (MulAction.orbit H x).ncard * Nat.card (MulAction.stabilizer H x) := by
    have h := (MulAction.stabilizer H x).card_mul_index
    rw [MulAction.index_stabilizer] at h
    rw [← h, mul_comm]
  have hk : k ≤ (MulAction.orbit H x).ncard := by
    have hinj' : Function.Injective
        (fun i : Fin k => (⟨h i • x, ⟨⟨h i, hH i⟩, rfl⟩⟩ : MulAction.orbit H x)) := by
      intro i j hij
      exact hinj (congrArg Subtype.val hij)
    have h1 : Nat.card (Fin k) ≤ Nat.card (MulAction.orbit H x) :=
      Nat.card_le_card_of_injective _ hinj'
    simpa using h1
  have hs' : s ≤ Nat.card (MulAction.stabilizer H x) := by
    have hle : Nat.card T ≤ Nat.card (MulAction.stabilizer H x) := by
      apply Nat.card_le_card_of_injective
        (fun t : T => (⟨⟨t.1, hT t.2⟩, hfix t.1 t.2⟩ : MulAction.stabilizer H x))
      intro t u htu
      exact Subtype.ext (congrArg (fun z : ↥(MulAction.stabilizer H x) => ((z : H) : G)) htu)
    exact le_trans hs hle
  calc k * s ≤ (MulAction.orbit H x).ncard * Nat.card (MulAction.stabilizer H x) :=
        Nat.mul_le_mul hk hs'
    _ = Nat.card H := hcard.symm

theorem ggHalf_card_ge_semidirect {G : Type} [Group G] [Finite G] (J : Subgroup G) (c d : G)
    (hc3 : orderOf c = 3) (hcJ : ∀ j ∈ J, c * j = j * c) (hcnot : c ∉ J)
    (hd : d * c * d⁻¹ = c⁻¹) :
    6 * Nat.card J ≤ Nat.card ↥(Subgroup.closure ((J : Set G) ∪ {c, d})) := by
  classical
  set Z : Subgroup G := Subgroup.zpowers c with hZdef
  set K : Subgroup G := Subgroup.closure ((J : Set G) ∪ {c}) with hKdef
  set T : Subgroup G := Subgroup.closure ((J : Set G) ∪ {c, d}) with hTdef
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers, hc3]
  have hJK : J ≤ K := by
    intro j hj
    exact Subgroup.subset_closure (Or.inl hj)
  have hZK : Z ≤ K := by
    rw [hZdef, Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hZne : J ⊓ Z ≠ Z := by
    intro hEq
    have hcZ : c ∈ Z := by
      rw [hZdef, Subgroup.mem_zpowers_iff]
      exact ⟨1, by simp⟩
    have hcInf : c ∈ J ⊓ Z := by
      rw [hEq]
      exact hcZ
    exact hcnot (Subgroup.mem_inf.1 hcInf).1
  have hbot : J ⊓ Z = ⊥ := by
    have hdvd : Nat.card ↥(J ⊓ Z) ∣ Nat.card Z := by
      have h := Subgroup.card_subgroup_dvd_card ((J ⊓ Z).subgroupOf Z)
      have hc : Nat.card ↥((J ⊓ Z).subgroupOf Z) = Nat.card ↥(J ⊓ Z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : J ⊓ Z ≤ Z)).toEquiv
      rw [← hc]
      exact h
    have hne3 : Nat.card ↥(J ⊓ Z) ≠ 3 := by
      intro h3
      apply hZne
      apply Subgroup.eq_of_le_of_card_ge (H := J ⊓ Z) (K := Z) inf_le_right
      rw [hZcard, h3]
    have hcard1 : Nat.card ↥(J ⊓ Z) = 1 := by
      have hdvd3 : Nat.card ↥(J ⊓ Z) ∣ 3 := by simpa [hZcard] using hdvd
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd3 with h1 | h3
      · exact h1
      · exact absurd h3 hne3
    exact Subgroup.eq_bot_of_card_eq _ hcard1
  have hcent : K ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hKdef, Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer ({c} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rcases hx with hxJ | hxc
    · exact hcJ x hxJ
    · rw [Set.mem_singleton_iff] at hxc
      subst x
      rfl
  have hdK : d ∉ K := by
    intro hdmem
    have hcomm : c * d = d * c :=
      (Subgroup.mem_centralizer_iff.mp (hcent hdmem)) c (Set.mem_singleton c)
    have hcinv : c⁻¹ = c := by
      calc c⁻¹ = d * c * d⁻¹ := hd.symm
        _ = c * d * d⁻¹ := by rw [← hcomm]
        _ = c := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hc2 : c ^ 2 = 1 := by
      have hmul : c * c = 1 := inv_eq_iff_mul_eq_one.mp hcinv
      simpa [pow_two] using hmul
    have hdiv : orderOf c ∣ 2 := (orderOf_dvd_iff_pow_eq_one).2 hc2
    rw [hc3] at hdiv
    have hle : 3 ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hKT : K ≤ T := by
    rw [hKdef, hTdef]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hdT : d ∈ T := by
    rw [hTdef]
    exact Subgroup.subset_closure (by simp)
  have hKTne : K.subgroupOf T ≠ ⊤ := by
    intro htop
    have hmem : (⟨d, hdT⟩ : T) ∈ K.subgroupOf T := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hdK hmem
  have hidx : 1 < (K.subgroupOf T).index := Subgroup.one_lt_index_of_ne_top hKTne
  have hcardKT : Nat.card ↥(K.subgroupOf T) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
  have hcardT : Nat.card T = Nat.card K * (K.subgroupOf T).index := by
    have h := Subgroup.card_mul_index (K.subgroupOf T)
    rw [hcardKT] at h
    exact h.symm
  have h2 : 2 * Nat.card K ≤ Nat.card T := by
    calc 2 * Nat.card K = Nat.card K * 2 := by ring
      _ ≤ Nat.card K * (K.subgroupOf T).index :=
          Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hidx)
      _ = Nat.card T := hcardT.symm
  have hprod : Nat.card ((↥J) × (↥Z)) = Nat.card ↥J * Nat.card ↥Z :=
    Nat.card_prod _ _
  have hinj : Function.Injective
      (fun p : (↥J) × (↥Z) => (⟨(p.1 : G) * (p.2 : G),
        Subgroup.mul_mem K (hJK p.1.2) (hZK p.2.2)⟩ : K)) := by
    rintro ⟨j1, z1⟩ ⟨j2, z2⟩ heq
    have heq' : (j1 : G) * (z1 : G) = (j2 : G) * (z2 : G) := congrArg Subtype.val heq
    have hmem : (j2 : G)⁻¹ * (j1 : G) = (z2 : G) * (z1 : G)⁻¹ := by
      calc (j2 : G)⁻¹ * (j1 : G)
          = (j2 : G)⁻¹ * ((j1 : G) * (z1 : G)) * (z1 : G)⁻¹ := by simp [mul_assoc]
        _ = (j2 : G)⁻¹ * ((j2 : G) * (z2 : G)) * (z1 : G)⁻¹ := by rw [heq']
        _ = (z2 : G) * (z1 : G)⁻¹ := by simp [mul_assoc]
    have hJ : (j2 : G)⁻¹ * (j1 : G) ∈ J :=
      Subgroup.mul_mem J (Subgroup.inv_mem J j2.2) j1.2
    have hZ : (z2 : G) * (z1 : G)⁻¹ ∈ Z :=
      Subgroup.mul_mem Z z2.2 (Subgroup.inv_mem Z z1.2)
    have hone : (j2 : G)⁻¹ * (j1 : G) = 1 := by
      have hmemZ : (j2 : G)⁻¹ * (j1 : G) ∈ Z := by rw [hmem]; exact hZ
      have hmemInf : (j2 : G)⁻¹ * (j1 : G) ∈ J ⊓ Z := Subgroup.mem_inf.2 ⟨hJ, hmemZ⟩
      rw [hbot] at hmemInf
      simpa using hmemInf
    have honeZ : (z2 : G) * (z1 : G)⁻¹ = 1 := by
      have hmemJ : (z2 : G) * (z1 : G)⁻¹ ∈ J := by rw [← hmem]; exact hJ
      have hmemInf : (z2 : G) * (z1 : G)⁻¹ ∈ J ⊓ Z := Subgroup.mem_inf.2 ⟨hmemJ, hZ⟩
      rw [hbot] at hmemInf
      simpa using hmemInf
    have h1 : (j1 : G) = (j2 : G) := by
      calc (j1 : G) = (j2 : G) * ((j2 : G)⁻¹ * (j1 : G)) := by
              rw [← mul_assoc, mul_inv_cancel, one_mul]
        _ = (j2 : G) * 1 := by rw [hone]
        _ = (j2 : G) := mul_one _
    have h2 : (z1 : G) = (z2 : G) := by
      have hz := mul_eq_one_iff_eq_inv.mp honeZ
      simpa using hz.symm
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hlower : 3 * Nat.card J ≤ Nat.card K := by
    have hcardle : Nat.card ((↥J) × (↥Z)) ≤ Nat.card K :=
      Nat.card_le_card_of_injective _ hinj
    simpa [hprod, hZcard, Nat.mul_comm] using hcardle
  calc 6 * Nat.card J = 2 * (3 * Nat.card J) := by ring
    _ ≤ 2 * Nat.card K := Nat.mul_le_mul_left 2 hlower
    _ ≤ Nat.card T := h2

theorem ggHalf_perfect_of_commutators {G : Type} [Group G] (a b : G)
    (hP : a ∈ ⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆ ∧
      b ∈ ⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆) :
    ⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆ = Subgroup.closure {a, b} := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  have hsub : ({a, b} : Set G) ⊆
      (⁅Subgroup.closure {a, b}, Subgroup.closure {a, b}⁆ : Subgroup G) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hP.1
    · exact hP.2
  exact (Subgroup.closure_le _).2 hsub

end CFSG.StandardType

end
