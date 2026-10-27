module

public import CFSG.RankThree.PartOne.CTP.Phan5Torus
public import CFSG.RankThree.PartOne.CTP.Phan5Blocks

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFSU5
  CFSG.RankThree.PartOne

section Perfect

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem isPerfect_su_two (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    Group.IsPerfect (Su K 2 f 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀ : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨e⟩ := exists_suid_two_equiv_sl hK hK₀
  have hq : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    classical
    have := Fintype.ofFinite (GaloisField 2 f)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 2 f))) (n := 4) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK₀]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    exact ⟨s, hs⟩
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hq
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem blk5_perfect (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (i : Fin 4) :
    Group.IsPerfect (blk5 K f i) := by
  have := isPerfect_su_two hK hf
  exact Group.IsPerfect.range (blockEmb2 K 2 f 4 i)

end Perfect

section Commute

variable {S : Type*} [Group S]

theorem commute_of_perfect_central (U : Subgroup S) [Group.IsPerfect U] (g : S)
    (h : ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.center S) : ∀ u ∈ U, g * u = u * g := by
  let φ : U →* Subgroup.center S :=
    { toFun := fun u => ⟨g * u * g⁻¹ * (u : S)⁻¹, h u u.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.mp (h v v.2) (u : S)
        have hu : (u : S) * (g * v * g⁻¹ * (v : S)⁻¹) * (u : S)⁻¹ = g * v * g⁻¹ * (v : S)⁻¹ := by
          rw [hz]
          group
        calc g * ((u * v : U) : S) * g⁻¹ * ((u * v : U) : S)⁻¹
            = (g * u * g⁻¹ * (u : S)⁻¹) * ((u : S) * (g * v * g⁻¹ * (v : S)⁻¹) * (u : S)⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
          _ = (g * u * g⁻¹ * (u : S)⁻¹) * (g * v * g⁻¹ * (v : S)⁻¹) := by rw [hu] }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := U)]
    exact Abelianization.commutator_subset_ker φ
  intro u hu
  have h1 : φ ⟨u, hu⟩ = 1 := by
    have : (⟨u, hu⟩ : U) ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top _
    exact this
  have h2 : g * u * g⁻¹ * u⁻¹ = 1 := congrArg Subtype.val h1
  calc g * u = (g * u * g⁻¹ * u⁻¹) * u * g := by group
    _ = u * g := by rw [h2]; group

end Commute

section CentCyclic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

omit [Finite K] [CharP K 2] in
theorem eq_of_cube_eq {n : ℕ} (h3 : ¬ 3 ∣ n) {ν ν' : Kˣ} (h : ν ^ n = 1) (h' : ν' ^ n = 1)
    (hc : ν ^ 3 = ν' ^ 3) : ν = ν' := by
  have hu : (ν * ν'⁻¹) ^ 3 = 1 := by
    rw [mul_pow, inv_pow, ← hc, mul_inv_cancel]
  have hu' : (ν * ν'⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, h, h', inv_one, mul_one]
  have hd1 : orderOf (ν * ν'⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hu
  have hd2 : orderOf (ν * ν'⁻¹) ∣ n := orderOf_dvd_of_pow_eq_one hu'
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h1 : orderOf (ν * ν'⁻¹) = 1 := by
    have := Nat.dvd_gcd hd1 hd2
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  rw [orderOf_eq_one_iff] at h1
  exact mul_inv_eq_one.mp h1

theorem unitaryInvolution_mul_self_eq_one_iff (ν : Kˣ) :
    unitaryInvolution K 2 f (ν : K) * ν = 1 ↔ ν ^ (2 ^ f + 1) = 1 := by
  rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, Units.val_eq_one]

theorem mem_centBlocks_of_comm (g : Su K 2 f 5) (h0 : ∀ u ∈ blk5 K f 0, g * u = u * g)
    (h1 : ∀ u ∈ blk5 K f 1, g * u = u * g) (h3 : ∀ u ∈ blk5 K f 3, g * u = u * g) :
    g ∈ centBlocks K f := by
  rw [Subgroup.mem_centralizer_iff]
  have hle : (blk5 K f 0 ⊔ blk5 K f 1 ⊔ blk5 K f 3 : Subgroup (Su K 2 f 5)) ≤
      Subgroup.centralizer {g} := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro u hu <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro x hx <;> rw [Set.mem_singleton_iff] at hx <;> rw [hx]
    · exact h0 u hu
    · exact h1 u hu
    · exact h3 u hu
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) g (Set.mem_singleton g)).symm

noncomputable def centMu (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ↥(centBlocks K f) →* K where
  toFun g := ((g.1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4
  map_one' := by simp
  map_mul' := by
    intro g h
    obtain ⟨ν₁, μ₁, hg⟩ := (mem_centBlocks_iff hK hf g.1).mp g.2
    obtain ⟨ν₂, μ₂, hh⟩ := (mem_centBlocks_iff hK hf h.1).mp h.2
    have e : (((g * h : ↥(centBlocks K f)).1 : Su K 2 f 5) : GL (Fin 5) K) =
        diagU (![ν₁, ν₁, ν₁, μ₁, μ₁] * ![ν₂, ν₂, ν₂, μ₂, μ₂]) := by
      rw [← diagU_mul, ← hg, ← hh]
      rfl
    show ((((g * h : ↥(centBlocks K f)).1 : Su K 2 f 5) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) 4 4 =
      ((g.1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 *
        ((h.1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4
    rw [e, hg, hh, diagU_apply_same, diagU_apply_same, diagU_apply_same]
    simp

theorem centMu_injective (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    Function.Injective (centMu hK hf) := by
  intro g h hgh
  obtain ⟨ν₁, μ₁, hg⟩ := (mem_centBlocks_iff hK hf g.1).mp g.2
  obtain ⟨ν₂, μ₂, hh⟩ := (mem_centBlocks_iff hK hf h.1).mp h.2
  have m1 := (blockScalar_mem_iff (f := f) ν₁ μ₁).mp (by rw [← hg]; exact g.1.2)
  have m2 := (blockScalar_mem_iff (f := f) ν₂ μ₂).mp (by rw [← hh]; exact h.1.2)
  have hmu : μ₁ = μ₂ := by
    have : ((g.1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 =
        ((h.1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 := hgh
    rw [hg, hh, diagU_apply_same, diagU_apply_same] at this
    exact Units.ext this
  subst hmu
  have hcube : ν₁ ^ 3 = ν₂ ^ 3 := by
    have h1 : (ν₁ : K) ^ 3 = (ν₂ : K) ^ 3 := by
      have hne : (μ₁ : K) ^ 2 ≠ 0 := pow_ne_zero 2 μ₁.ne_zero
      apply mul_right_cancel₀ hne
      rw [m1.2.2, m2.2.2]
    apply Units.ext
    simpa using h1
  have hν : ν₁ = ν₂ := eq_of_cube_eq h3
    ((unitaryInvolution_mul_self_eq_one_iff ν₁).mp m1.1)
    ((unitaryInvolution_mul_self_eq_one_iff ν₂).mp m2.1) hcube
  subst hν
  apply Subtype.ext
  apply Subtype.ext
  rw [hg, hh]

theorem centBlocks_cyclic (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    IsCyclic ↥(centBlocks K f) :=
  isCyclic_of_injective_ringHom (centMu hK hf) (centMu_injective hK hf h3)

theorem exists_centBlocks_element (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (h25 : 25 ∣ 2 ^ f + 1) :
    ∃ g ∈ centBlocks K f, g ^ 25 = 1 ∧ g ∉ Subgroup.center (Su K 2 f 5) := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ f) ^ 2 - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf ω = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, hcard]
  have hQ : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdvd : 25 ∣ orderOf ω := by
    rw [hord]
    refine h25.trans ⟨2 ^ f - 1, ?_⟩
    have h2 : 1 ≤ 2 ^ f := by omega
    have h3 : 1 ≤ (2 ^ f) ^ 2 := by nlinarith
    zify [h2, h3]
    ring
  have hne : orderOf ω ≠ 0 := by
    rw [hord]
    have : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
    omega
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : Kˣ, orderOf μ₀ = 25 :=
    ⟨ω ^ (orderOf ω / 25), orderOf_pow_orderOf_div hne hdvd⟩
  have hμ25 : μ₀ ^ 25 = 1 := by
    rw [← hμ₀]
    exact pow_orderOf_eq_one μ₀
  have hq1 : μ₀ ^ (2 ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := h25
    rw [hm, pow_mul, hμ25, one_pow]
  have hnorm : (μ₀ ^ 16) ^ (2 ^ f + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hq1, one_pow]
  have hdet : ((μ₀ ^ 16 : Kˣ) : K) ^ 3 * (μ₀ : K) ^ 2 = 1 := by
    have : (μ₀ ^ 16) ^ 3 * μ₀ ^ 2 = 1 := by
      rw [← pow_mul, ← pow_add]
      have : μ₀ ^ (16 * 3 + 2) = (μ₀ ^ 25) ^ 2 := by rw [← pow_mul]
      rw [this, hμ25, one_pow]
    have h := congrArg (fun u : Kˣ => (u : K)) this
    simpa using h
  have hmem : (diagU ![μ₀ ^ 16, μ₀ ^ 16, μ₀ ^ 16, μ₀, μ₀] : GL (Fin 5) K) ∈
      SUid (unitaryInvolution K 2 f) 5 :=
    (blockScalar_mem_iff (f := f) (μ₀ ^ 16) μ₀).mpr
      ⟨(unitaryInvolution_mul_self_eq_one_iff _).mpr hnorm,
        (unitaryInvolution_mul_self_eq_one_iff _).mpr hq1, hdet⟩
  let g : Su K 2 f 5 := ⟨_, hmem⟩
  refine ⟨g, (mem_centBlocks_iff hK hf g).mpr ⟨μ₀ ^ 16, μ₀, rfl⟩, ?_, ?_⟩
  · apply Subtype.ext
    show (diagU ![μ₀ ^ 16, μ₀ ^ 16, μ₀ ^ 16, μ₀, μ₀] : GL (Fin 5) K) ^ 25 = 1
    rw [diagU_pow, ← diagU_one]
    congr 1
    funext i
    have h16 : (μ₀ ^ 16) ^ 25 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hμ25, one_pow]
    fin_cases i <;> simp [h16, hμ25]
  · intro hc
    have hsw := Subgroup.mem_center_iff.mp hc (swapSU 5 2 3)
    have hm := comm_matrix (g := g) (u := swapSU 5 2 3) hsw.symm
    rw [coe_swapSU] at hm
    have hgm : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        Matrix.diagonal ![((μ₀ ^ 16 : Kˣ) : K), (μ₀ ^ 16 : Kˣ), (μ₀ ^ 16 : Kˣ), μ₀, μ₀] :=
      blockScalar_val (μ₀ ^ 16) μ₀
    rw [hgm] at hm
    have h23 := diag_entry_eq_of_comm_swap (a := 2) (b := 3) hm
    simp at h23
    have hμeq : μ₀ ^ 16 = μ₀ := Units.ext h23
    have h15 : μ₀ ^ 15 = 1 := by
      have : μ₀ ^ 15 * μ₀ = 1 * μ₀ := by rw [← pow_succ, one_mul]; exact hμeq
      exact mul_right_cancel this
    have := orderOf_dvd_of_pow_eq_one h15
    rw [hμ₀] at this
    omega

end CentCyclic

section Phan

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem not_three_dvd_of_five_dvd {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) : ¬ 3 ∣ 2 ^ f + 1 := by
  have key : ∀ n : ℕ, 2 ^ n % 15 = 1 ∨ 2 ^ n % 15 = 2 ∨ 2 ^ n % 15 = 4 ∨ 2 ^ n % 15 = 8 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  have := key f
  omega

theorem isCyclic_map_of_isCyclic {G H : Type*} [Group G] [Group H] (θ : G →* H) (C : Subgroup G)
    [IsCyclic C] : IsCyclic ↥(C.map θ) :=
  isCyclic_of_surjective (θ.subgroupMap C) (θ.subgroupMap_surjective C)

theorem phan5_centralizer
    {N : Type} [Group N] [Finite N] {f : ℕ} {M : Fin 4 → Subgroup N}
    {B : Subgroup N} (hf : 2 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (h25 : 25 ∣ 2 ^ f + 1)
    (hB : IsElementaryAbelian 5 B) (hgen : (⨆ i, M i) = ⊤)
    (hmod : ∀ i, StatedClassicalModel (M i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      M i ≤ Subgroup.centralizer (M j : Set N) ∧ M i ⊓ M j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(M i ⊔ M j))
    (htor : CTTorusCondition 5 B M) :
    IsCyclic ↥(Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup N) : Set N)) ∧
      ∃ y ∈ Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup N) : Set N), orderOf y = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hsurj, hker, hblk⟩ := phan_blocks (n := 4) (by norm_num) hf Nat.prime_five
    (by norm_num) h5 hB hgen hmod hcomm hadj htor
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have h3 := not_three_dvd_of_five_dvd h5
  have hf1 : 1 ≤ f := by omega
  have hY : Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup N) : Set N) =
      (centBlocks (GaloisField 2 (2 * f)) f).map θ := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, rfl⟩ := hsurj y
      refine ⟨g, ?_, rfl⟩
      have key : ∀ i : Fin 4, M i ≤ M 0 ⊔ M 1 ⊔ M 3 → ∀ u ∈ blk5 (GaloisField 2 (2 * f)) f i,
          g * u = u * g := by
        intro i hi u hu
        have := blk5_perfect hK hf i
        refine commute_of_perfect_central (blk5 (GaloisField 2 (2 * f)) f i) g (fun v hv => ?_) u hu
        apply hker
        rw [MonoidHom.mem_ker]
        have hvM : θ v ∈ M i := by
          rw [← hblk i]
          exact Subgroup.mem_map_of_mem θ hv
        have hcm := Subgroup.mem_centralizer_iff.mp hy (θ v) (hi hvM)
        simp only [map_mul, map_inv]
        rw [← hcm]
        group
      exact mem_centBlocks_of_comm g (key 0 (le_sup_left.trans le_sup_left))
        (key 1 (le_sup_right.trans le_sup_left)) (key 3 le_sup_right)
    · intro hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_iff]
      have key : ∀ i : Fin 4, (blk5 (GaloisField 2 (2 * f)) f i ≤ blk5 (GaloisField 2 (2 * f)) f 0 ⊔
          blk5 (GaloisField 2 (2 * f)) f 1 ⊔ blk5 (GaloisField 2 (2 * f)) f 3) →
          M i ≤ Subgroup.centralizer {θ g} := by
        intro i hi x hx
        rw [← hblk i] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have hug := Subgroup.mem_centralizer_iff.mp hg u (hi hu)
        rw [← map_mul, ← map_mul]
        exact congrArg θ hug.symm
      have hle : (M 0 ⊔ M 1 ⊔ M 3 : Subgroup N) ≤ Subgroup.centralizer {θ g} :=
        sup_le (sup_le (key 0 (le_sup_left.trans le_sup_left))
          (key 1 (le_sup_right.trans le_sup_left))) (key 3 le_sup_right)
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hle hx) (θ g) (Set.mem_singleton _)).symm
  rw [hY]
  refine ⟨?_, ?_⟩
  · have := centBlocks_cyclic hK hf1 h3
    exact isCyclic_map_of_isCyclic θ _
  · obtain ⟨g, hg, hg25, hgc⟩ := exists_centBlocks_element hK hf1 h25
    have hθ1 : θ g ≠ 1 := by
      intro h1
      exact hgc (hker (by rw [MonoidHom.mem_ker]; exact h1))
    have h25' : (θ g) ^ 25 = 1 := by rw [← map_pow, hg25, map_one]
    have hdvd : orderOf (θ g) ∣ 25 := orderOf_dvd_of_pow_eq_one h25'
    have hne1 : orderOf (θ g) ≠ 1 := fun h => hθ1 (orderOf_eq_one_iff.mp h)
    have h5ord : 5 ∣ orderOf (θ g) := by
      obtain ⟨m, hm, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
        (show orderOf (θ g) ∣ 5 ^ 2 by simpa using hdvd)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hne1 (by simpa using hmo)
      rw [hmo]
      exact dvd_pow_self 5 hm0
    exact ⟨(θ g) ^ (orderOf (θ g) / 5), Subgroup.pow_mem _ (Subgroup.mem_map_of_mem θ hg) _,
      orderOf_pow_orderOf_div (Nat.pos_of_dvd_of_pos hdvd (by norm_num)).ne' h5ord⟩

end Phan

end CFSG.RankThree.PartOne.CTP
