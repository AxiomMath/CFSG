module

public import CFSG.Quasithin.Background.FFC4Three
public import CFSG.Quasithin.Background.A3FactsClassical
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix

theorem ThreeRank2.of_pRank {X : Type*} [Group X] [Finite X]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : ThreeRank2 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (Nat.prime_three.one_lt) (⊤ : Subgroup X)
  have h9 : 9 ≤ Nat.card E := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) := Nat.pow_le_pow_right (by norm_num) h
  have hnb : 1 < Nat.card E := by omega
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
    rw [this, Subgroup.card_bot] at hnb
    omega
  have hx3 : x ^ 3 = 1 := hE.2 x hx
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers x := hcon
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord] at this
    omega
  refine ⟨x, y, hx1, hx3, hE.2 y hy, ?_, hyx⟩
  have := hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem ThreeRank2.pRank_two_le {X : Type*} [Group X] [Finite X] (h : ThreeRank2 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := h
  refine A3Facts.two_le_pRank_of_gens hx3 hy3 hxy hx1 fun n hn => hyx ?_
  rw [← hn]
  exact Subgroup.npow_mem_zpowers x n


theorem exists_npow_of_mem_zpowers_of_cube {G : Type*} [Group G] {x y : G} (hx3 : x ^ 3 = 1)
    (h : y ∈ Subgroup.zpowers x) : ∃ n : ℕ, x ^ n = y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  refine ⟨(k % 3).toNat, ?_⟩
  rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
  have h3 : x ^ (3 : ℤ) = 1 := by simpa using hx3
  conv_rhs => rw [← Int.emod_add_mul_ediv k 3, _root_.zpow_add, _root_.zpow_mul, h3, _root_.one_zpow, mul_one]

section Rot

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem rotGL_ne_one {i j : ι} (hij : i ≠ j) : rotGL (K := K) i j ≠ 1 := by
  intro h
  have h1 := rotMatrix_mulVec_left (K := K) i j
  have h2 : (rotGL (K := K) i j : Matrix ι ι K) = 1 := by rw [h]; rfl
  rw [coe_rotGL] at h2
  rw [h2, one_mulVec] at h1
  have := congrFun h1 j
  simp [hij.symm] at this

theorem threeRank2_of_rot {H : Subgroup (GL ι K)} {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hx : rotGL (K := K) i j ∈ H)
    (hy : rotGL (K := K) k l ∈ H) : ThreeRank2 ↥H := by
  refine ⟨⟨rotGL i j, hx⟩, ⟨rotGL k l, hy⟩, fun h => rotGL_ne_one hij (congrArg Subtype.val h),
    Subtype.ext (rotGL_pow_three _ _), Subtype.ext (rotGL_pow_three _ _),
    Subtype.ext (rotGL_commute hik hil hjk hjl).eq, fun hmem => ?_⟩
  obtain ⟨n, hn⟩ := exists_npow_of_mem_zpowers_of_cube
    (Subtype.ext (rotGL_pow_three (K := K) i j) : (⟨rotGL i j, hx⟩ : ↥H) ^ 3 = 1) hmem
  have h1 : ((rotGL (K := K) i j ^ n : GL ι K) : Matrix ι ι K) *ᵥ Pi.single k 1 = Pi.single k 1 :=
    rotGL_pow_mulVec_of_ne hik.symm hjk.symm n
  have h2 := rotMatrix_mulVec_left (K := K) k l
  have h3 : (rotGL (K := K) k l : GL ι K) = rotGL i j ^ n := by
    have := congrArg Subtype.val hn
    simpa using this.symm
  have h4 : ((rotGL (K := K) k l : GL ι K) : Matrix ι ι K) *ᵥ Pi.single k 1 = Pi.single k 1 := by
    rw [h3]; exact h1
  rw [coe_rotGL, h2] at h4
  have := congrFun h4 l
  simp [hkl.symm] at this

theorem threeRank2_statedSL {n : ℕ} (hn : 4 ≤ n) : ThreeRank2 ↥(StatedSL n K) := by
  have he := (Fin.castLE_injective hn).comp (finSumFinEquiv (m := 2) (n := 2)).injective
  set e : Fin 2 ⊕ Fin 2 → Fin n := Fin.castLE hn ∘ finSumFinEquiv with hedef
  have hne : ∀ a b : Fin 2 ⊕ Fin 2, a ≠ b → e a ≠ e b := fun _ _ h => he.ne h
  exact threeRank2_of_rot (hne (.inl 0) (.inr 0) (by decide)) (hne (.inl 1) (.inr 1) (by decide))
    (hne (.inl 0) (.inl 1) (by decide)) (hne (.inl 0) (.inr 1) (by decide))
    (hne (.inr 0) (.inl 1) (by decide)) (hne (.inr 0) (.inr 1) (by decide))
    (Subgroup.subset_closure (det_rotMatrix _ _)) (Subgroup.subset_closure (det_rotMatrix _ _))


theorem threeRank2_statedSL_three {ζ : Kˣ} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    ThreeRank2 ↥(StatedSL 3 K) := by
  set a : Fin 3 → Kˣ := ![ζ, ζ⁻¹, 1] with ha
  set b : Fin 3 → Kˣ := ![1, ζ, ζ⁻¹] with hb
  have hpa : ∏ i, a i = 1 := by simp [ha, Fin.prod_univ_three]
  have hpb : ∏ i, b i = 1 := by simp [hb, Fin.prod_univ_three]
  have hcube : ∀ d : Fin 3 → Kˣ, (∀ i, d i ^ 3 = 1) → d ^ 3 = 1 := fun d hd => by
    funext i
    simpa using hd i
  have ha3 : a ^ 3 = 1 := hcube a fun i => by fin_cases i <;> simp [ha, inv_pow, hζ3]
  have hb3 : b ^ 3 = 1 := hcube b fun i => by fin_cases i <;> simp [hb, inv_pow, hζ3]
  have hx3 : (⟨torusDiag a, torusDiag_mem_SL hpa⟩ : ↥(StatedSL 3 K)) ^ 3 = 1 := by
    apply Subtype.ext
    show torusDiag a ^ 3 = 1
    rw [← map_pow, ha3, map_one]
  refine ⟨⟨torusDiag a, torusDiag_mem_SL hpa⟩, ⟨torusDiag b, torusDiag_mem_SL hpb⟩, ?_, hx3, ?_, ?_, ?_⟩
  · intro h
    have h' : torusDiag a = torusDiag (1 : Fin 3 → Kˣ) := by
      have := congrArg Subtype.val h
      simpa using this
    have := congrFun (torusDiag_injective h') 0
    exact hζ1 (by simpa [ha] using this)
  · apply Subtype.ext
    show torusDiag b ^ 3 = 1
    rw [← map_pow, hb3, map_one]
  · apply Subtype.ext
    exact ((Commute.all a b).map torusDiag).eq
  · intro hmem
    obtain ⟨n, hn⟩ := exists_npow_of_mem_zpowers_of_cube hx3 hmem
    have hn' : torusDiag (a ^ n) = torusDiag b := by
      rw [map_pow]
      have := congrArg Subtype.val hn
      simpa using this
    have h0 := congrFun (torusDiag_injective hn') 0
    have h1 := congrFun (torusDiag_injective hn') 1
    simp [ha, hb] at h0 h1
    apply hζ1
    rw [← h1, h0]
    simp


theorem rotMatrix_symplectic (k : Fin 2) :
    (rotMatrix (K := K) (Sum.inl k) (Sum.inr k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0 * rotMatrix (Sum.inl k) (Sum.inr k) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, rotMatrix, rotCol, Matrix.fromBlocks,
      Pi.single_apply]

theorem threeRank2_statedSp : ThreeRank2 ↥(StatedSp 2 K) :=
  threeRank2_of_rot (i := Sum.inl 0) (j := Sum.inr 0) (k := Sum.inl 1) (l := Sum.inr 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (Subgroup.subset_closure (rotMatrix_symplectic 0))
    (Subgroup.subset_closure (rotMatrix_symplectic 1))

end Rot


theorem threeRank2_alt {n : ℕ} (hn : 6 ≤ n) : ThreeRank2 ↥(alternatingGroup (Fin n)) :=
  ThreeRank2.of_pRank (A3Facts.two_le_pRank_alternating hn)

theorem threeRank2_perm {n : ℕ} (hn : 6 ≤ n) : ThreeRank2 (Equiv.Perm (Fin n)) :=
  (threeRank2_alt hn).of_injective (alternatingGroup (Fin n)).subtype
    (alternatingGroup (Fin n)).subtype_injective

theorem ThreeRank2.of_surjective_pgroup_ker {X S : Type*} [Group X] [Group S] [Finite X] [Finite S]
    (φ : X →* S) (hφ : Function.Surjective φ) (hker : IsPGroup 3 φ.ker) (hS : ThreeRank2 S) :
    ThreeRank2 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (Nat.prime_three.one_lt) (⊤ : Subgroup S)
  have hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := hS.pRank_two_le
  have h9 : 9 ≤ Nat.card E := by
    rw [hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup S) := Nat.pow_le_pow_right (by norm_num) hr
  set P : Subgroup X := E.comap φ with hP
  have hPp : IsPGroup 3 ↥P := by
    intro g
    have h1 : (φ (g : X)) ^ 3 = 1 := hE.2 _ g.2
    have h2 : (g : X) ^ 3 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow]; exact h1
    obtain ⟨j, hj⟩ := hker ⟨(g : X) ^ 3, h2⟩
    refine ⟨j + 1, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_succ', pow_mul]
    exact this
  have hnc : ¬ IsCyclic ↥P := by
    intro hcyc
    let ψ : ↥P →* ↥E := (φ.comp P.subtype).codRestrict E (fun g => g.2)
    have hψ : Function.Surjective ψ := by
      intro e
      obtain ⟨g, hg⟩ := hφ (e : S)
      exact ⟨⟨g, by rw [hP, Subgroup.mem_comap, hg]; exact e.2⟩, Subtype.ext hg⟩
    have hEc : IsCyclic ↥E := isCyclic_of_surjective ψ hψ
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
    have hg3 : g ^ 3 = 1 := Subtype.ext (hE.2 g g.2)
    have h1 : Nat.card ↥E ∣ 3 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one hg3
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  exact ThreeRank2.of_pRank (A3Facts.two_le_pRank_of_not_isCyclic (by norm_num) hPp hnc)

theorem threeRank2_hat {X : Type} [Group X] [Finite X] (h : IsHat X ↥(alternatingGroup (Fin 6))) :
    ThreeRank2 X := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (QuotientGroup.mk' (Subgroup.center X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  exact ThreeRank2.of_surjective_pgroup_ker (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) hp ((threeRank2_alt (by norm_num)).of_mulEquiv e.symm)

end FFC

end CFSG.Quasithin
