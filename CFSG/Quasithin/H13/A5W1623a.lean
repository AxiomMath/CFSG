module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2A

public section

namespace CFSG.Quasithin.H13.Ln2P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {n : ℕ}

theorem card_zmod_two : Nat.card (ZMod 2) = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem eq_conj_of_slConjugation (A : GL (Fin n) (ZMod 2))
    (hU : ∀ u ∈ unitriangular n (ZMod 2),
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A u ∈
        unitriangular n (ZMod 2)) :
    ∃ u ∈ unitriangular n (ZMod 2), ∀ g,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A g =
        u * g * u⁻¹ := by
  have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 :=
    eq_one_of_ne_zero _ ((isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  set g₀ : SpecialLinearGroup (Fin n) (ZMod 2) := ⟨A, hdet⟩ with hg₀
  have hinv : ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((g₀⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [Matrix.coe_units_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, hdet]
    simp [hg₀]
  have hφg : ∀ g, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n
      (ZMod 2) A g = g₀ * g * g₀⁻¹ := by
    intro g
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hinv]
    rfl
  have hN : g₀ ∈ Subgroup.normalizer
      (unitriangular n (ZMod 2) : Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    have hle : (unitriangular n (ZMod 2)).map (MulAut.conj g₀).toMonoidHom ≤
        unitriangular n (ZMod 2) := by
      rintro _ ⟨u, hu, rfl⟩
      show g₀ * u * g₀⁻¹ ∈ unitriangular n (ZMod 2)
      rw [← hφg]
      exact hU u hu
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective]
  rw [normalizer_unitriangular, upperTriangular_eq_unitriangular] at hN
  exact ⟨g₀, hN, hφg⟩

theorem ringEquiv_zmod_two_eq_one (σ : ZMod 2 ≃+* ZMod 2) : σ = 1 :=
  RingEquiv.ext fun c => by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl <;> simp

theorem graphAut_ne_conj (hn : 3 ≤ n) {u : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hu : u ∈ unitriangular n (ZMod 2)) :
    ¬ ∀ g, graphAut n g = u * g * u⁻¹ := by
  intro h
  have hr := reflection_mem_parabolic (n := n) (j := n - 1) (by omega) (by omega)
  have hU := unitriangular_le_flagStabilizer (n := n) (Set.Icc 1 (n - 1) \ {n - 1}) hu
  have hmem := (flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {n - 1})).mul_mem
    ((flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {n - 1})).mul_mem hU hr)
    ((flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {n - 1})).inv_mem hU)
  rw [← h, graphAut_apply, graphFun_reflection (by omega) (by omega)] at hmem
  have h1 := eq_of_reflection_mem_parabolic (by omega) (by omega) hmem
  omega

theorem mulAut_cases (hn : 3 ≤ n) (ψ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)))
    (hU : ∀ u ∈ unitriangular n (ZMod 2), ψ u ∈ unitriangular n (ZMod 2)) :
    (∃ u ∈ unitriangular n (ZMod 2), ∀ g, ψ g = u * g * u⁻¹) ∨
      ∃ u ∈ unitriangular n (ZMod 2), ∀ g, ψ g = graphAut n (u * g * u⁻¹) := by
  obtain ⟨A, σ, ε, hε, hψ⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn ψ
  rw [ringEquiv_zmod_two_eq_one σ, map_one, mul_one] at hψ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hψ
    subst hψ
    exact Or.inl (eq_conj_of_slConjugation A hU)
  · rw [pow_one] at hψ
    set ψ' : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) := graphAut n * ψ with hψ'
    have hU' : ∀ u ∈ unitriangular n (ZMod 2), ψ' u ∈ unitriangular n (ZMod 2) := fun u hu =>
      graphFun_mem_unitriangular (hU u hu)
    obtain ⟨A', σ', ε', hε', hψ'e⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn ψ'
    rw [ringEquiv_zmod_two_eq_one σ', map_one, mul_one] at hψ'e
    rcases (by omega : ε' = 0 ∨ ε' = 1) with rfl | rfl
    · rw [pow_zero, mul_one] at hψ'e
      rw [hψ'e] at hU'
      obtain ⟨u, hu, hcu⟩ := eq_conj_of_slConjugation A' hU'
      refine Or.inr ⟨u, hu, fun g => ?_⟩
      have h1 : ψ' g = u * g * u⁻¹ := by rw [hψ'e]; exact hcu g
      rw [← h1, hψ', MulAut.mul_apply, graphAut_apply, graphAut_apply, graphFun_graphFun]
    · exfalso
      rw [pow_one] at hψ'e
      have hγ : graphAut n =
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n (ZMod 2)
            (A' * A⁻¹) := by
        have h1 : graphAut n = ψ' * ψ⁻¹ := by rw [hψ', mul_inv_cancel_right]
        rw [h1, hψ'e, hψ, map_mul, map_inv]
        group
      have hUγ : ∀ u ∈ unitriangular n (ZMod 2),
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n (ZMod 2)
            (A' * A⁻¹) u ∈ unitriangular n (ZMod 2) := fun u hu => by
        rw [← hγ]
        exact graphFun_mem_unitriangular hu
      obtain ⟨u, hu, hcu⟩ := eq_conj_of_slConjugation _ hUγ
      exact graphAut_ne_conj hn hu fun g => by rw [hγ]; exact hcu g

theorem graphAut_not_map_stab_one (hn : 3 ≤ n) :
    ¬ ∀ g ∈ flagStabilizer n (ZMod 2) {1}, graphAut n g ∈ flagStabilizer n (ZMod 2) {1} := by
  intro h
  have hr : reflection n (ZMod 2) (n - 1) (by omega) (by omega) ∈
      flagStabilizer n (ZMod 2) {1} :=
    ((subflag_stabilizer_generation (K := ZMod 2) (n := n) {1}).2.2 (n - 1) (by omega)
      (by omega)).mpr (by simp only [Set.mem_singleton_iff]; omega)
  have h1 := h _ hr
  rw [graphAut_apply, graphFun_reflection (by omega) (by omega)] at h1
  exact ((subflag_stabilizer_generation (K := ZMod 2) (n := n) {1}).2.2 (n - (n - 1)) (by omega)
    (by omega)).mp h1 (by simp only [Set.mem_singleton_iff]; omega)

theorem card_sup_dvd_mul {G : Type*} [Group G] (N I : Subgroup G)
    (hI : I ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2

theorem card_sl3_two : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [card_SL_eq (by norm_num), card_zmod_two]
  decide

theorem pCore_sl3_two : CFSG.pCore 2 (SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    sl_isSimple_of_card_two card_zmod_two le_rfl
  have : (CFSG.pCore 2 (SpecialLinearGroup (Fin 3) (ZMod 2))).Normal := CFSG.pCore_normal
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 (SpecialLinearGroup (Fin 3) (ZMod 2)))
    with h | h
  · exact h
  · exfalso
    have hp := CFSG.pCore_isPGroup (p := 2) (G := SpecialLinearGroup (Fin 3) (ZMod 2))
    rw [h] at hp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hp.of_equiv Subgroup.topEquiv)
    rw [card_sl3_two] at hk
    have h8 : k < 8 := by
      by_contra hk8
      have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> omega

theorem exists_block {m j : ℕ} (hm : 3 ≤ m) (hj : 1 ≤ j) (hjm : j < m) :
    ∃ a, a + 3 ≤ m ∧ a < j ∧ j ≤ a + 2 ∧
      Set.Icc 1 (m - 1) \ {a + 1, a + 2} ⊆ Set.Icc 1 (m - 1) \ {j} ∧
      (∀ c ∈ Set.Icc 1 (m - 1) \ {a + 1, a + 2}, ¬ (a < c ∧ c < a + 3)) ∧
      (a = 0 ∨ a ∈ Set.Icc 1 (m - 1) \ {a + 1, a + 2}) ∧
      (a + 3 = m ∨ a + 3 ∈ Set.Icc 1 (m - 1) \ {a + 1, a + 2}) := by
  obtain ⟨a, ha3, haj, hja⟩ : ∃ a, a + 3 ≤ m ∧ a < j ∧ j ≤ a + 2 := by
    by_cases hjm2 : j + 2 ≤ m
    · exact ⟨j - 1, by omega, by omega, by omega⟩
    · exact ⟨j - 2, by omega, by omega, by omega⟩
  refine ⟨a, ha3, haj, hja, ?_, ?_, ?_, ?_⟩
  · rintro c ⟨hc, hc'⟩
    refine ⟨hc, fun hcj => hc' ?_⟩
    rw [Set.mem_singleton_iff] at hcj
    subst hcj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rintro c ⟨-, hc'⟩ ⟨h1, h2⟩
    apply hc'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · rcases Nat.eq_zero_or_pos a with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨⟨h0, by omega⟩, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
  · rcases Nat.lt_or_ge (a + 3) m with h0 | h0
    · refine Or.inr ⟨⟨by omega, by omega⟩, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · exact Or.inl (by omega)

theorem eq_of_graph_of_map_le {j : ℕ} (hj : 1 ≤ j) (hjn : j < n)
    {ψ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))} {u : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hu : u ∈ unitriangular n (ZMod 2)) (hψ : ∀ g, ψ g = graphAut n (u * g * u⁻¹))
    (hM : ∀ g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}),
      ψ g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) : n - j = j := by
  set M := flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) with hMdef
  have hUM : u ∈ M := unitriangular_le_flagStabilizer _ hu
  have hr : u⁻¹ * reflection n (ZMod 2) j hj hjn * u ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hUM) (reflection_mem_parabolic hj hjn)) hUM
  have h1 := hM _ hr
  rw [hψ, show u * (u⁻¹ * reflection n (ZMod 2) j hj hjn * u) * u⁻¹ =
      reflection n (ZMod 2) j hj hjn by group, graphAut_apply,
    graphFun_reflection hj hjn] at h1
  exact eq_of_reflection_mem_parabolic (by omega) (by omega) h1

theorem mul_pow_mul_inv_mem {G : Type*} [Group G] {N : Subgroup G} {x u : G} (hx : x ∈ N)
    (hu : u ∈ Subgroup.normalizer (N : Set G)) (r : ℕ) : (x * u) ^ r * (u ^ r)⁻¹ ∈ N := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : u ^ r * x * (u ^ r)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu r) x).mp hx
    have e : (x * u) ^ (r + 1) * (u ^ (r + 1))⁻¹ =
        ((x * u) ^ r * (u ^ r)⁻¹) * (u ^ r * x * (u ^ r)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem ih h1

theorem mem_of_pow_two_pow_mem {G : Type*} [Group G] {N : Subgroup G} {g : G} {e m : ℕ}
    (hm : Odd m) (hgm : g ^ m = 1) (hN : g ^ 2 ^ e ∈ N) : g ∈ N := by
  have hco : (2 ^ e).gcd (orderOf g) = 1 :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr
      (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hgm)))
  exact (Subgroup.zpowers_le.mpr hN) (mem_zpowers_pow_iff.mpr hco)

theorem mem_perfectCore_of_odd {a j : ℕ} (h : a + 3 ≤ n) (haj : a < j) (hja : j ≤ a + 2)
    {J : Set ℕ} (hJ : J ⊆ Set.Icc 1 (n - 1) \ {j}) (hno : ∀ c ∈ J, ¬ (a < c ∧ c < a + 3))
    {g : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hg : g ∈ flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j})) {m : ℕ} (hm : Odd m)
    (hgm : g ^ m = 1) : g ∈ perfectCore (flagStabilizer n (ZMod 2) J) := by
  have hj1 : 1 ≤ j := by omega
  have hjn : j < n := by omega
  set N := perfectCore (flagStabilizer n (ZMod 2) J) with hNdef
  set U := unitriangular n (ZMod 2) with hUdef
  set M := flagStabilizer n (ZMod 2) (Set.Icc 1 (n - 1) \ {j}) with hMdef
  have hMQ : M ≤ flagStabilizer n (ZMod 2) J := flagStabilizer_anti hJ
  have hQN : flagStabilizer n (ZMod 2) J ≤ Subgroup.normalizer (N : Set _) := fun q hq =>
    L3316.mem_normalizer_perfectCore (Subgroup.le_normalizer hq)
  have hUN : U ≤ Subgroup.normalizer (N : Set _) :=
    (unitriangular_le_flagStabilizer J).trans hQN
  set i₀ : Fin 3 := ⟨j - 1 - a, by omega⟩ with hi₀
  set i₁ : Fin 3 := ⟨j - a, by omega⟩ with hi₁
  have h10 : i₁ ≠ i₀ := fun e => by
    have := congrArg Fin.val e
    simp only [hi₀, hi₁] at this
    omega
  have hTN : (liftT (K := ZMod 2) a 3 h h10 : SpecialLinearGroup (Fin n) (ZMod 2)) ∈ N :=
    Ln2.liftT_mem_perfectCore h le_rfl hno h10
  have hTj : (liftT (K := ZMod 2) a 3 h h10 : SpecialLinearGroup (Fin n) (ZMod 2)) ∉
      stabilizer (flagSpace n (ZMod 2) j) :=
    Ln2.liftT_not_mem_stabilizer h h10 (d := j) (by show j - 1 - a + a < j; omega)
      (by show j ≤ j - a + a; omega)
  have hBNU : upperTriangular n (ZMod 2) ≤ N ⊔ U := by
    rw [upperTriangular_eq_unitriangular]
    exact le_sup_right
  obtain ⟨hNU, -⟩ := borel_overgroups (N ⊔ U) hBNU
  have hjcut : j ∉ borelOvergroupCuts (N ⊔ U) := by
    intro hjI
    have h1 : (liftT (K := ZMod 2) a 3 h h10 : SpecialLinearGroup (Fin n) (ZMod 2)) ∈
        N ⊔ U := Subgroup.mem_sup_left hTN
    rw [hNU] at h1
    exact hTj (mem_flagStabilizer.mp h1 j hjI)
  have hrj : reflection n (ZMod 2) j hj1 hjn ∈ N ⊔ U := by
    by_contra hr
    exact hjcut ⟨hj1, hjn, hr⟩
  have hMNU : M ≤ N ⊔ U := by
    rw [hMdef, parabolic_eq_closure hj1 hjn, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact Subgroup.mem_sup_right hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact hrj
  have hg' : g ∈ ((N ⊔ U : Subgroup _) : Set _) := hMNU hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N U hUN] at hg'
  obtain ⟨x, hx, u, hu, rfl⟩ := hg'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := (SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) (n := n) (by omega)).2.1 ⟨u, hu⟩
  have hue : u ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have h2 := mul_pow_mul_inv_mem hx (hUN hu) (2 ^ e)
  rw [hue, inv_one, mul_one] at h2
  exact mem_of_pow_two_pow_mem hm hgm h2

end CFSG.Quasithin.H13.Ln2P
