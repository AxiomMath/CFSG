module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLTransport
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AutPSL

section Kernel

variable {n : ℕ} {K : Type} [Field K] [CharP K 2]

theorem eq_of_proj_eq_of_mul_self {X Y : SpecialLinearGroup (Fin n) K} (hX : X * X = 1)
    (hY : Y * Y = 1) (h : proj n K X = proj n K Y) : X = Y := by
  have hs : X⁻¹ * Y ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    rw [← scalars_eq_center]
    exact proj_eq_proj_iff.mp h
  have hcomm : X * (X⁻¹ * Y) = X⁻¹ * Y * X := Subgroup.mem_center_iff.mp hs X
  have hss : (X⁻¹ * Y) ^ 2 = 1 := by
    rw [pow_two]
    calc X⁻¹ * Y * (X⁻¹ * Y) = X * X * (X⁻¹ * Y * (X⁻¹ * Y)) := by rw [hX, one_mul]
      _ = X * (X * (X⁻¹ * Y)) * (X⁻¹ * Y) := by group
      _ = X * (X⁻¹ * Y * X) * (X⁻¹ * Y) := by rw [hcomm]
      _ = Y * Y := by group
      _ = 1 := hY
  have h1 := eq_one_of_mem_center_of_sq_eq_one hs hss
  exact (inv_mul_eq_one.mp h1)

theorem mem_center_of_conjAut_eq_one (hn : 1 ≤ n) {A : GL (Fin n) K} (h : conjAut n K A = 1) :
    A ∈ Subgroup.center (GL (Fin n) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have hcomm : ∀ i j : Fin n, i ≠ j →
      Commute (Matrix.single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := by
    intro i j hij
    have hT := HypSixTypeA.transvection_mul_self (F := K) hij 1
    have h1 : proj n K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A
          (SpecialLinearGroup.transvection hij 1)) =
        proj n K (SpecialLinearGroup.transvection hij 1) := by
      rw [← conjAut_proj, h, MulAut.one_apply]
    have h2 := eq_of_proj_eq_of_mul_self (by rw [← map_mul, hT, map_one]) hT h1
    have h3 := congrArg (fun g => ((SpecialLinearGroup.toGL g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) h2
    simp only [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
      at h3
    have h4 : (A : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single i j (1 : K)) =
        (1 + Matrix.single i j (1 : K)) * A := by
      have e : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have e' : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)
          = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h5 : (A : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single i j (1 : K)) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + Matrix.single i j (1 : K) := h3
      calc (A : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single i j (1 : K)) =
          (A : Matrix (Fin n) (Fin n) K) * (1 + Matrix.single i j (1 : K)) *
            (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by rw [e', Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h5]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h4
    exact (add_left_cancel h4).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j hij => hcomm i j hij
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [← hc, h0, map_zero, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hc]

@[expose] noncomputable def pglHom :
    (GL (Fin n) K ⧸ StatedScalars (Fin n) K) →* MulAut (projectiveSL n K) :=
  QuotientGroup.lift _ (conjAut n K) (by
    rintro _ ⟨c, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    rw [conjAut_proj, MulAut.one_apply]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
    have hcent : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    rw [(Subgroup.mem_center_iff.mp hcent _).symm, mul_inv_cancel_right])

omit [CharP K 2] in
theorem pglHom_mk (A : GL (Fin n) K) :
    pglHom (QuotientGroup.mk A : GL (Fin n) K ⧸ StatedScalars (Fin n) K) = conjAut n K A :=
  QuotientGroup.lift_mk _ _ A

theorem pglHom_injective (hn : 1 ≤ n) : Function.Injective (pglHom (n := n) (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, pglHom_mk] at hx
  have hA := mem_center_of_conjAut_eq_one hn hx
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hA
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hA

omit [CharP K 2] in
theorem range_pglHom : (pglHom (n := n) (K := K)).range = inndiag := by
  ext α
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨A, (pglHom_mk A).symm⟩
  · rintro ⟨A, rfl⟩
    exact ⟨_, pglHom_mk A⟩

end Kernel

section PGL

variable {K : Type} [Field K]

theorem card_le_cube_of_pgl [Finite K] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hτ : p ≠ 3 ∨ ∀ τ : K, τ ^ 3 = 1 → τ = 1)
    (E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ 3 := by
  classical
  set Z := StatedScalars (Fin 3) K
  set π := QuotientGroup.mk' Z
  set Et := E.comap π
  have hZEt : Z ≤ Et := fun z hz => by
    change π z ∈ E
    rw [show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact E.one_mem
  have hEtcomm : ∀ x ∈ Et, ∀ y ∈ Et, x * y = y * x := by
    intro x hx y hy
    have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ hx _ hy]
      group
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp h1
    have hconj : x * y * x⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c * y := by
      rw [hc]
      group
    have hc3 : c ^ 3 = 1 := CFSG.RankThree.PartTwo.Sec4.pow_three_eq_one_of_conj_eq_scalar_mul hconj
    obtain ⟨d, hd⟩ := (QuotientGroup.eq_one_iff (x ^ p)).mp (by
      change π (x ^ p) = 1
      rw [map_pow]
      exact hexp _ hx)
    have hcp : c ^ p = 1 := by
      have h2 := CFSG.RankThree.PartTwo.Sec4.conj_zpow_eq hconj (p : ℤ)
      rw [zpow_natCast, ← hd] at h2
      have hcent : Matrix.GeneralLinearGroup.scalar (Fin 3) d ∈ Subgroup.center (GL (Fin 3) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨d, rfl⟩
      rw [Subgroup.mem_center_iff.mp hcent y, mul_inv_cancel_right] at h2
      have h3 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ (-(p : ℤ))) = 1 :=
        mul_eq_right.mp h2.symm
      have h4 : c ^ (-(p : ℤ)) = 1 := by
        have h5 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h3
        simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
          Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h5
        exact Units.ext h5
      rw [_root_.zpow_neg, inv_eq_one, zpow_natCast] at h4
      exact h4
    have hc1 : c = 1 := by
      rcases hτ with h3p | hno
      · have hg : Nat.gcd 3 p = 1 := by
          rcases (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm h3p) with h
          exact h
        have : c ^ Nat.gcd 3 p = 1 := pow_gcd_eq_one.mpr ⟨hc3, hcp⟩
        rwa [hg, pow_one] at this
      · exact Units.ext (hno (c : K) (by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]))
    rw [hc1, map_one, one_mul] at hconj
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [hconj]
  let _ : CommGroup Et :=
    { (inferInstance : Group Et) with mul_comm := fun a b => Subtype.ext (hEtcomm a a.2 b b.2) }
  set pw : Et →* Et := powMonoidHom p
  have hker : Nat.card pw.ker ≤ p ^ 3 := by
    set Ω := pw.ker.map Et.subtype
    have hΩ : Nat.card Ω = Nat.card pw.ker :=
      Subgroup.card_map_of_injective Et.subtype_injective
    rw [← hΩ]
    have := CFSG.RankThree.PartOne.LIT.card_le_pow_card_gl hp hpK Ω
      (by
        rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
        exact hEtcomm a a.2 b b.2)
      (by
        rintro _ ⟨a, ha, rfl⟩
        have : a ^ p = 1 := ha
        exact congrArg Subtype.val this)
    simpa using this
  have hrange : Nat.card pw.range ≤ Nat.card (Z.subgroupOf Et) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    change (a : GL (Fin 3) K) ^ p ∈ Z
    rw [← QuotientGroup.eq_one_iff]
    change π ((a : GL (Fin 3) K) ^ p) = 1
    rw [map_pow]
    exact hexp _ a.2
  have hEt : Nat.card (Z.subgroupOf Et) * Nat.card E = Nat.card Et := by
    set g : Et →* (GL (Fin 3) K ⧸ Z) := π.comp Et.subtype
    have hgk : g.ker = Z.subgroupOf Et := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have hgr : g.range = E := by
      ext e
      constructor
      · rintro ⟨a, rfl⟩
        exact a.2
      · intro he
        obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective e
        exact ⟨⟨A, he⟩, rfl⟩
    rw [← Subgroup.card_ker_mul_card_range g, hgk, hgr]
  have hZpos : 0 < Nat.card (Z.subgroupOf Et) := Nat.card_pos
  have htot := Subgroup.card_ker_mul_card_range pw
  have hle : Nat.card (Z.subgroupOf Et) * Nat.card E ≤ Nat.card (Z.subgroupOf Et) * p ^ 3 := by
    rw [hEt, ← htot]
    calc Nat.card pw.ker * Nat.card pw.range ≤ p ^ 3 * Nat.card (Z.subgroupOf Et) :=
          Nat.mul_le_mul hker hrange
      _ = _ := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hle hZpos

end PGL

section InnerDiag

variable {m : ℕ} {K : Type} [Field K] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) K →* G}

theorem mem_inndiag_of_psiInnerDiag [Finite K] [CharP K 2] (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K)) {p : ℕ} (hp : Odd p)
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G))
    (hI : GGPsiInnerDiag (SpecialLinear.rootDatum m K) ψ c) {α : MulAut (projectiveSL (m + 1) K)}
    (hα : ∀ y y' : SpecialLinearGroup (Fin (m + 1)) K,
      ψ y' = c⁻¹ * ψ y * c → α (proj (m + 1) K y) = proj (m + 1) K y') :
    α ∈ (inndiag : Subgroup (MulAut (projectiveSL (m + 1) K))) := by
  have hn : 3 ≤ m + 1 := by omega
  have hαp : α ^ p = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective (m + 1) K x
    rw [MulAut.one_apply]
    apply HypSixTypeA.projAut_pow_apply hker hc hα p y y
    have hcomm := Subgroup.mem_centralizer_iff.mp hcp (ψ y) ⟨y, rfl⟩
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := K) hn).2 α
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero hn hp hε (by rw [← hαeq]; exact hαp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  obtain ⟨g, ⟨g₀, rfl⟩, hall⟩ := hI
  have hr : 0 < (SpecialLinear.rootDatum m K).rank := by
    change 0 < m
    omega
  obtain ⟨γ, hγ⟩ : (SpecialLinear.rootDatum m K).roots.Nonempty :=
    ⟨_, (CFSG.LieType.Steinberg.RootSystem.ofCartan (SpecialLinear.rootDatum m K).isFiniteType
      (SpecialLinear.rootDatum m K).divisible).single_mem ⟨0, hr⟩⟩
  obtain ⟨h, -, hz⟩ := hall γ hγ
  have hij : (SpecialLinear.idx m γ).1 ≠ (SpecialLinear.idx m γ).2 :=
    (SpecialLinear.idx_spec m hγ).1
  have hσ : σ = 1 := by
    refine HypSixTypeA.field_eq_one hij (A := A) (V := 1) (W := g₀ * h) fun t => ?_
    have hzt := hz (SpecialLinearGroup.transvection hij t) (by
      change _ ∈ SpecialLinear.rootGroup m K γ
      rw [SpecialLinear.rootGroup_eq_idx m K hγ]
      exact SpecialLinear.transvection_mem_rootSubgroup hij t)
    have hconj : ψ (g₀ * h * SpecialLinearGroup.transvection hij t * (g₀ * h)⁻¹) =
        c⁻¹ * ψ (1 * SpecialLinearGroup.transvection hij t * 1⁻¹) * c := by
      calc ψ (g₀ * h * SpecialLinearGroup.transvection hij t * (g₀ * h)⁻¹) =
          ψ g₀ * ψ (h * SpecialLinearGroup.transvection hij t * h⁻¹) * (ψ g₀)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = ψ g₀ * ((c * ψ g₀)⁻¹ * ψ (SpecialLinearGroup.transvection hij t) *
            (c * ψ g₀)) * (ψ g₀)⁻¹ := by rw [hzt]
        _ = _ := by
          simp only [one_mul, inv_one, mul_one]
          group
    rw [← hα _ _ hconj, hαeq, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  rw [hσ, map_one, mul_one] at hαeq
  exact ⟨A, hαeq.symm⟩

end InnerDiag

section Input

theorem pslThreeRankInput_holds : PSLThreeRankInput := by
  intro G _ _ f ψ hf hker hC p Bs hp hp2 hBsE hcard hBsN hBsI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  set K := GaloisField 2 f
  set N := Subgroup.normalizer (ψ.range : Set G)
  set φN := ψ.range.normalizerMonoidHom
  have hφN : Function.Injective φN := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC,
      Subgroup.bot_subgroupOf]
  set Θ := projEquiv (m := 2) (K := K) hker hC
  set χ : N →* MulAut (projectiveSL 3 K) := (MulAut.congr Θ).symm.toMonoidHom.comp φN
  have hχ : Function.Injective χ := (MulAut.congr Θ).symm.injective.comp hφN
  have hχα : ∀ (b : N) (y y' : SpecialLinearGroup (Fin 3) K),
      ψ y' = ((b : G)⁻¹)⁻¹ * ψ y * (b : G)⁻¹ → χ b (proj 3 K y) = proj 3 K y' := by
    intro b y y' hy
    change Θ.symm (φN b (Θ (proj 3 K y))) = proj 3 K y'
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change (b : G) * ψ y * (b : G)⁻¹ = ψ y'
    rw [hy, inv_inv]
  have hmem : ∀ b : N, (b : G) ∈ Bs → χ b ∈ (inndiag : Subgroup (MulAut (projectiveSL 3 K))) := by
    intro b hb
    have hbinv : (b : G)⁻¹ ∈ Bs := Bs.inv_mem hb
    refine mem_inndiag_of_psiInnerDiag (m := 2) (le_refl 2) hker (hp.odd_of_ne_two hp2)
      (Subgroup.inv_mem _ b.2) ?_ (hBsI _ hbinv) (hχα b)
    rw [hBsE.2 _ hbinv]
    exact Subgroup.one_mem _
  set E := (Bs.subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBsN).toEquiv
  have hEI : E ≤ (pglHom (n := 3) (K := K)).range := by
    rw [range_pglHom]
    rintro _ ⟨b, hb, rfl⟩
    exact hmem b hb
  set E' := E.comap (pglHom (n := 3) (K := K))
  have hcardE' : Nat.card E' = Nat.card E := by
    have h : Nat.card (E'.map (pglHom (n := 3) (K := K))) = Nat.card E' :=
      Subgroup.card_map_of_injective (pglHom_injective (n := 3) (K := K) (by norm_num))
    rw [Subgroup.map_comap_eq_self hEI] at h
    exact h.symm
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have h := hBsE.1.is_comm.comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
    have h' : (a : G) * b = b * a := congrArg Subtype.val h
    exact Subtype.ext h'
  have hexpE : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hBsE.2 _ ha)
    rw [this, map_one]
  have hcomm' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
    pglHom_injective (n := 3) (K := K) (by norm_num) (by
      rw [map_mul, map_mul]
      exact hcommE _ hx _ hy)
  have hexp' : ∀ x ∈ E', x ^ p = 1 := fun x hx =>
    pglHom_injective (n := 3) (K := K) (by norm_num) (by
      rw [map_pow, map_one]
      exact hexpE _ hx)
  have hpK : (p : K) ≠ 0 := CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2
  have h4 : p ^ 4 ≤ Nat.card E' := by rw [hcardE', hcardE]; exact hcard
  by_cases h3 : p = 3 ∧ ∃ τ : K, τ ^ 3 = 1 ∧ τ ≠ 1
  · obtain ⟨rfl, τ, hτ, hτ1⟩ := h3
    have h9 := CFSG.RankThree.PartTwo.Sec4.card_le_nine_of_comm hpK hτ hτ1 E' hcomm' hexp'
    omega
  · have hτ : p ≠ 3 ∨ ∀ τ : K, τ ^ 3 = 1 → τ = 1 := by
      by_cases hp3 : p = 3
      · right
        intro τ hτ
        by_contra hτ1
        exact h3 ⟨hp3, τ, hτ, hτ1⟩
      · exact Or.inl hp3
    have hle := card_le_cube_of_pgl hp hpK hτ E' hcomm' hexp'
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

end Input

end AutPSL

end CFSG.StandardType
