module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.Quasithin.Vol2.KGFact1296Red
public import CFSG.Quasithin.Vol2.KGFact1297Rank
public import CFSG.Quasithin.Vol2.KGFactH91B

public section

namespace CFSG.Quasithin.H13.KG1297

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.SLnTwo

variable {n : ℕ}

section Lattice

variable {K : Type*} [Field K]

theorem flagStabilizer_inf (I J : Set ℕ) :
    flagStabilizer n K I ⊓ flagStabilizer n K J = flagStabilizer n K (I ∪ J) := by
  ext g
  rw [Subgroup.mem_inf, mem_flagStabilizer, mem_flagStabilizer, mem_flagStabilizer]
  constructor
  · rintro ⟨h1, h2⟩ i (hi | hi)
    · exact h1 i hi
    · exact h2 i hi
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩

theorem flagStabilizer_anti {I J : Set ℕ} (h : I ⊆ J) :
    flagStabilizer n K J ≤ flagStabilizer n K I :=
  fun _ hg => mem_flagStabilizer.2 fun i hi => mem_flagStabilizer.1 hg i (h hi)

theorem subset_of_flagStabilizer_le {I J : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (h : flagStabilizer n K J ≤ flagStabilizer n K I) : I ⊆ J := by
  intro i hi
  by_contra hJ
  obtain ⟨h1, h2⟩ := hI i hi
  have hr := ((subflag_stabilizer_generation (K := K) (n := n) J).2.2 i h1 h2).2 hJ
  exact ((subflag_stabilizer_generation (K := K) (n := n) I).2.2 i h1 h2).1 (h hr) hi

theorem flagStabilizer_sup (I J : Set ℕ) :
    flagStabilizer n K I ⊔ flagStabilizer n K J = flagStabilizer n K (I ∩ J) := by
  refine le_antisymm (sup_le (flagStabilizer_anti Set.inter_subset_left)
    (flagStabilizer_anti Set.inter_subset_right)) ?_
  rw [(subflag_stabilizer_generation (K := K) (n := n) (I ∩ J)).1, Subgroup.closure_le]
  rintro g (hg | ⟨j, hj, hjn, hjIJ, rfl⟩)
  · exact Subgroup.mem_sup_left (upperTriangular_le_flagStabilizer I hg)
  · rw [Set.mem_inter_iff, not_and_or] at hjIJ
    rcases hjIJ with hjI | hjJ
    · exact Subgroup.mem_sup_left
        (((subflag_stabilizer_generation (K := K) (n := n) I).2.2 j hj hjn).2 hjI)
    · exact Subgroup.mem_sup_right
        (((subflag_stabilizer_generation (K := K) (n := n) J).2.2 j hj hjn).2 hjJ)

end Lattice

theorem exists_eq_flagStabilizer {Y : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hU : unitriangular n (ZMod 2) ≤ Y) :
    ∃ J : Set ℕ, (∀ i ∈ J, 1 ≤ i ∧ i < n) ∧ Y = flagStabilizer n (ZMod 2) J := by
  have hU' : upperTriangular n (ZMod 2) ≤ Y := by
    rw [BinaryParabolic.upperTriangular_eq_unitriangular]
    exact hU
  refine ⟨borelOvergroupCuts Y, fun i hi => ?_, (borel_overgroups Y hU').1⟩
  obtain ⟨hi1, hin, -⟩ := hi
  exact ⟨hi1, hin⟩

theorem exists_block_dvd (hn : 1 ≤ n) {J : Set ℕ} {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ flagStabilizer n (ZMod 2) J) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpx : orderOf x = p) :
    ∃ a m : ℕ, a + m ≤ n ∧ (a = 0 ∨ a ∈ J) ∧ (a + m = n ∨ a + m ∈ J) ∧
      (∀ c ∈ J, ¬ (a < c ∧ c < a + m)) ∧ p ∣ Nat.card (GL (Fin m) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hxp : (⟨x, hx⟩ : ↥(flagStabilizer n (ZMod 2) J)) ^ p = 1 := by
    rw [← hpx, ← Subgroup.orderOf_mk x hx]
    exact pow_orderOf_eq_one _
  have hU : x ∈ unitriangular n (ZMod 2) := by
    refine mem_unitriangular_of_blocks hx fun a m h ha hb hno => ?_
    have hm : ¬ p ∣ Nat.card (GL (Fin m) (ZMod 2)) := fun hd => hcon ⟨a, m, h, ha, hb, hno, hd⟩
    set φ := blkMon (flagStabilizer n (ZMod 2) J) a m h (blockLeft_of_cut m ha)
      (blockRight_of_cut hb) with hφ
    set u := φ.toHomUnits ⟨x, hx⟩ with hu
    have hup : u ^ p = 1 := by
      rw [hu, ← map_pow, hxp, map_one]
    have hu1 : orderOf u = 1 := by
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hup) with h1 | hpu
      · exact h1
      · exfalso
        apply hm
        rw [← hpu]
        exact orderOf_dvd_natCard u
    rw [orderOf_eq_one_iff] at hu1
    have := congrArg Units.val hu1
    rw [hu, MonoidHom.coe_toHomUnits, Units.val_one] at this
    exact this
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 (isPGroup_unitriangular_charTwo (K := ZMod 2) hn))
    ⟨x, hU⟩
  rw [Subgroup.orderOf_mk, hpx] at hj
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ j by rw [hj])
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem card_GL_small {m : ℕ} (hm : m ≤ 3) :
    Nat.card (GL (Fin m) (ZMod 2)) = [1, 1, 6, 168].getD m 0 := by
  rw [card_GL_eq, Nat.card_zmod]
  interval_cases m <;> decide

theorem orderOf_ne_of_small (hn : 1 ≤ n) {J : Set ℕ} {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsmall : ∀ a m : ℕ, a + m ≤ n → (a = 0 ∨ a ∈ J) → (a + m = n ∨ a + m ∈ J) →
      (∀ c ∈ J, ¬ (a < c ∧ c < a + m)) → m ≤ k)
    (hGL : ∀ m, m ≤ k → ¬ p ∣ Nat.card (GL (Fin m) (ZMod 2)))
    {x : SpecialLinearGroup (Fin n) (ZMod 2)} (hx : x ∈ flagStabilizer n (ZMod 2) J) :
    orderOf x ≠ p := by
  intro hpx
  obtain ⟨a, m, h, ha, hb, hno, hd⟩ := exists_block_dvd hn hx hp hp2 hpx
  exact hGL m (hsmall a m h ha hb hno) hd

theorem lowTv_mem {J : Set ℕ} {i j : Fin n} (hij : (i : ℕ) = j + 1) (hJ : (i : ℕ) ∉ J) :
    SpecialLinearGroup.transvection (show i ≠ j from fun h => by rw [h] at hij; omega)
      (1 : ZMod 2) ∈ flagStabilizer n (ZMod 2) J := by
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply,
    Matrix.one_apply]
  have hkl : k ≠ l := fun h => by rw [h] at hk; omega
  rw [ite_eq_right hkl]
  split_ifs with h
  · exfalso
    obtain ⟨rfl, rfl⟩ := h
    have : c = (i : ℕ) := by omega
    exact hJ (this ▸ hc)
  · rfl

theorem not_noE9 {M : Type*} [Group M] {Y : Subgroup M} {a b : M} (ha : a ∈ Y) (hb : b ∈ Y)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hba1 : b ≠ a) (hba2 : b ≠ a ^ 2) : ¬ NoE9 Y := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (h a ha b hb ha3 hb3 hab ha1)
  have hk' : a ^ k = a ^ (k % 3) := zpow_eq_zpow_emod' k ha3
  have hr : 0 ≤ k % 3 ∧ k % 3 < 3 := ⟨Int.emod_nonneg k (by norm_num), Int.emod_lt_of_pos k
    (by norm_num)⟩
  rw [hk'] at hk
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk
    exact hb1 hk.symm
  · rw [h1, zpow_one] at hk
    exact hba1 hk.symm
  · rw [h2, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hk
    exact hba2 hk.symm

theorem modO2_flag {J : Set ℕ} {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ J)
    (hb : a + m = n ∨ a + m ∈ J) (hno : ∀ c ∈ J, ¬ (a < c ∧ c < a + m)) (hm : 3 ≤ m)
    (hother : ∀ a' m' : ℕ, a' + m' ≤ n → (a' = 0 ∨ a' ∈ J) → (a' + m' = n ∨ a' + m' ∈ J) →
      (∀ c ∈ J, ¬ (a' < c ∧ c < a' + m')) → (a' = a ∧ m' = m) ∨ m' ≤ 1) :
    Nonempty (ModO2 (flagStabilizer n (ZMod 2) J) ≃* SpecialLinearGroup (Fin m) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  set H := flagStabilizer n (ZMod 2) J with hH
  set β := blkSLTwo hK H a m h (blockLeft_of_cut m ha) (blockRight_of_cut hb) with hβ
  have hβs : Function.Surjective β := by
    intro A
    obtain ⟨x, hx⟩ := bigBlockHom_surjective (K := ZMod 2) (n := n) hK h hm ha hb hno A
    refine ⟨⟨x.1, CFSG.Quasithin.perfectCore_le _ x.2⟩, Subtype.ext ?_⟩
    have h1 := congrArg (fun B : SpecialLinearGroup (Fin m) (ZMod 2) =>
      (B : Matrix (Fin m) (Fin m) (ZMod 2))) hx
    rw [bigBlockHom_coe] at h1
    exact h1
  have hkerU : ∀ x : ↥H, β x = 1 → (x : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
      unitriangular n (ZMod 2) := by
    intro x hx
    refine mem_unitriangular_of_blocks x.2 fun a' m' h' ha' hb' hno' => ?_
    rcases hother a' m' h' ha' hb' hno' with ⟨rfl, rfl⟩ | hm'
    · exact congrArg Subtype.val hx
    · interval_cases m'
      · exact blkAt_zero a' h' _
      · exact blkAt_one_eq_one hK H a' h' (blockLeft_of_cut 1 ha') (blockRight_of_cut hb') x
  have hker2 : IsPGroup 2 β.ker :=
    isPGroup_ker_of_unitriangular (by omega) β fun x hx => hkerU x hx
  have hpc : CFSG.pCore 2 ↥H = β.ker := by
    apply le_antisymm
    · intro x hx
      set N := (CFSG.pCore 2 ↥H).map β with hN
      have hNn : N.Normal := Subgroup.Normal.map CFSG.pCore_normal β hβs
      have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup.map β
      have hbot := CFSG.Quasithin.H13.KGH91.NatCoord.eq_bot_of_normal_isPGroup hm hN2
      have hmem : β x ∈ N := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    · exact KG1296.le_pCore_of_normal (MonoidHom.normal_ker β) hker2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans
    (QuotientGroup.quotientKerEquivOfSurjective β hβs)⟩

end CFSG.Quasithin.H13.KG1297
