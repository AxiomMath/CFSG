module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G9
public import CFSG.Quasithin.Vol2.Ch10SecC9S5g
public import CFSG.Quasithin.Vol2.Ch10SecD211A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_pCoreOf_of_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) {l : G}
    (hl : l ∈ L) (hlC : l ∈ Subgroup.centralizer (fsuUL T L I : Set G)) : l ∈ pCoreOf 2 L := by
  have hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    SecA.isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuUL T L I : Set G) :=
    (pCoreOf_L_le_centralizer hyp h1011).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1V))
  exact inf_centralizer_le_pCoreOf hsimp hOC (le_normalizer_fsuUL T L I)
    (commutator_fsuUL_eq hyp) (SecA.commutator_fsuVM_ne_bot hyp.fsu) ⟨hl, hlC⟩

theorem eq_one_of_odd_of_centralizer
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (hyp : Hyp10 G T L I) {l : G} (hl : l ∈ L)
    (hlC : l ∈ Subgroup.centralizer (fsuUL T L I : Set G)) {n : ℕ} (hn : l ^ n = 1)
    (hodd : Odd n) : l = 1 := by
  obtain ⟨m, hm⟩ := exists_two_pow_of_mem_pCoreOf
    (mem_pCoreOf_of_centralizer h37 h38 h1011 hyp hl hlC)
  exact eq_one_of_two_pow hm hn hodd

omit [Finite G] in
theorem conjAct_eq_one_iff' (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem exists_three_comm_of_case3 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) {v : G} (hv : v ∈ fsuUL T L I) :
    ∃ l ∈ L, orderOf l = 3 ∧ l * v = v * l := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcomm, hnat⟩ := h3
  obtain ⟨D⟩ := hnat.toL3Coord
  set u : ↥(⊤ : Subgroup ↥(fsuUL T L I)) := ⟨⟨v, hv⟩, trivial⟩ with hu
  set a := Multiplicative.toAdd (D.β u) with ha
  obtain ⟨γ, hγa, hγ3, hγ1⟩ : ∃ γ : L3.Γ, L3.act γ a = a ∧ γ ^ 3 = 1 ∧ γ ≠ 1 := by
    by_cases h0 : a = 0
    · obtain ⟨γ, -, hγ3, hγ1⟩ := SecD.L3.exists_order_three_fix (Pi.single 0 1) (by decide)
      exact ⟨γ, by rw [h0]; exact L3.act_zero γ, hγ3, hγ1⟩
    · exact SecD.L3.exists_order_three_fix a h0
  have hγpow : ∀ n : ℕ, L3.act (γ ^ n) a = a := fun n => by
    induction n with
    | zero => exact L3.act_one a
    | succ n ih => rw [pow_succ, L3.act_mul, hγa, ih]
  obtain ⟨⟨l₀, hl₀N⟩, hl₀L, hl₀σ⟩ := D.rho_mem γ
  have hl₀L' : l₀ ∈ L := Subgroup.mem_subgroupOf.mp hl₀L
  obtain ⟨e, m, hm3, hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos l₀).ne' 3 (by norm_num)
  set l := l₀ ^ m with hl
  have hlL : l ∈ L := L.pow_mem hl₀L' m
  have hlN : l ∈ Subgroup.normalizer (fsuUL T L I : Set G) := (Subgroup.normalizer _).pow_mem hl₀N m
  have hlσ : conjAct (fsuUL T L I) ⟨l, hlN⟩ = D.rho (γ ^ m) := by
    have e1 : (⟨l, hlN⟩ : ↥(Subgroup.normalizer (fsuUL T L I : Set G))) = ⟨l₀, hl₀N⟩ ^ m :=
      Subtype.ext (by simp [hl])
    rw [e1, map_pow, hl₀σ, map_pow]
  have hl3e : l ^ 3 ^ e = 1 := by
    rw [hl, ← pow_mul, mul_comm, ← hme, pow_orderOf_eq_one]
  have hγm1 : γ ^ m ≠ 1 := by
    intro h
    have h1 : orderOf γ ∣ m := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime hγ3 hγ1] at h1
    exact hm3 h1
  have hl3C : l ^ 3 ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    have hN3 := (Subgroup.normalizer (fsuUL T L I : Set G)).pow_mem hlN 3
    have h1 : conjAct (fsuUL T L I) ⟨l ^ 3, hN3⟩ = 1 := by
      have e1 : (⟨l ^ 3, hN3⟩ : ↥(Subgroup.normalizer (fsuUL T L I : Set G))) = ⟨l, hlN⟩ ^ 3 :=
        Subtype.ext (by simp)
      rw [e1, map_pow, hlσ, ← map_pow, ← pow_mul, mul_comm, pow_mul, hγ3, one_pow, map_one]
    exact (conjAct_eq_one_iff' _ _).mp h1
  have hl3 : l ^ 3 = 1 := eq_one_of_odd_of_centralizer h37 h38 h1011 hyp (L.pow_mem hlL 3) hl3C
    (n := 3 ^ e) (by rw [← pow_mul, mul_comm, pow_mul, hl3e, one_pow]) (Odd.pow (by decide))
  have hl1 : l ≠ 1 := by
    intro h
    apply hγm1
    apply D.rho_injective
    rw [← hlσ, map_one, conjAct_eq_one_iff']
    show l ∈ Subgroup.centralizer (fsuUL T L I : Set G)
    rw [h]
    exact Subgroup.one_mem _
  refine ⟨l, hlL, orderOf_eq_prime hl3 hl1, ?_⟩
  clear_value l
  have hlv : l * v * l⁻¹ ∈ fsuUL T L I := (Subgroup.mem_normalizer_iff.mp hlN v).mp hv
  have hβ : D.β ⟨⟨l * v * l⁻¹, hlv⟩, trivial⟩ = D.β u := by
    have h1 := D.β_rho (γ ^ m) (⟨v, hv⟩ : ↥(fsuUL T L I)) trivial trivial
    have e1 : D.rho (γ ^ m) ⟨v, hv⟩ = ⟨l * v * l⁻¹, hlv⟩ := by
      rw [← hlσ]
      exact Subtype.ext (coe_conjAct_apply _ _ _)
    rw [show Multiplicative.toAdd (D.β ⟨⟨v, hv⟩, trivial⟩) = a from rfl, hγpow m, e1] at h1
    rw [h1, ha, ofAdd_toAdd]
  have hcV : (⟨⟨l * v * l⁻¹, hlv⟩, trivial⟩ * u⁻¹ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
      ⟨⟨l * v * l⁻¹ * v⁻¹, (fsuUL T L I).mul_mem hlv ((fsuUL T L I).inv_mem hv)⟩, trivial⟩ := rfl
  have hc0 := (D.ker_β _).mp (by rw [map_mul, map_inv, hβ]; exact mul_inv_cancel _ :
    D.β (⟨⟨l * v * l⁻¹, hlv⟩, trivial⟩ * u⁻¹) = 1)
  rw [hcV] at hc0
  set c := l * v * l⁻¹ * v⁻¹ with hc
  have hcC : c ∈ Subgroup.centralizer (fsuL0 T L : Set G) := Subgroup.mem_subgroupOf.mp hc0
  have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcC l (SecA.le_fsuL0 T L hlL)
  have hcl' : l * c * l⁻¹ = c := by rw [hcl]; group
  have hcV1 : c ∈ fsuUL T L I := (fsuUL T L I).mul_mem hlv ((fsuUL T L I).inv_mem hv)
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hc2 : c * c = 1 := by
    rw [← pow_two]
    exact (SecA.isElemAbelian_fsuVM hyp).2 c (commutator_le_left_of_le_normalizer hLN hcV1)
  have key : l * v * l⁻¹ = c * v := by rw [hc]; group
  have key2 : l * (l * v * l⁻¹) * l⁻¹ = v := by
    calc l * (l * v * l⁻¹) * l⁻¹ = l * (c * v) * l⁻¹ := by rw [key]
      _ = (l * c * l⁻¹) * (l * v * l⁻¹) := by group
      _ = c * (c * v) := by rw [hcl', key]
      _ = v := by rw [← mul_assoc, hc2, one_mul]
  have hl3' : l * l * l = 1 := by rw [← hl3, pow_succ, pow_two]
  have key3 : v = c * v := by
    calc v = (l * l * l) * v * (l * l * l)⁻¹ := by rw [hl3']; group
      _ = l * (l * (l * v * l⁻¹) * l⁻¹) * l⁻¹ := by group
      _ = c * v := by rw [key2, key]
  have hc1 : c = 1 := by
    have := congrArg (fun x => x * v⁻¹) key3
    simpa using this.symm
  have key4 : l * v * l⁻¹ = v := by rw [key, hc1, one_mul]
  calc l * v = l * v * l⁻¹ * l := by group
    _ = v * l := by rw [key4]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
