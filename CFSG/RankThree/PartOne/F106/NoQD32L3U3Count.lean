module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.BRANCH.RankDet
public import CFSG.RankThree.PartOne.BRANCH.RankTrace
public import CFSG.RankThree.PartOne.S11c.CentralLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Module Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.BRANCH

theorem center_scalar_of_card_eq_sq {n : ℕ} {K : Type} [Field K] {P : Type} [Group P] [Finite P]
    (ρ : P →* GL (Fin n) K) (hρ : Function.Injective ρ) (hnK : (n : K) ≠ 0)
    (hcomm : ∀ g h : P, ∃ c : Kˣ,
      ρ (g * h * g⁻¹ * h⁻¹) = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hcard : Nat.card (P ⧸ Subgroup.center P) = n ^ 2) :
    ∀ z ∈ Subgroup.center P, ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  classical
  have : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  let s : P ⧸ Subgroup.center P → P := Quotient.out
  have hs : ∀ a, (s a : P ⧸ Subgroup.center P) = a := fun a => Quotient.out_eq' a
  let f : (P ⧸ Subgroup.center P) → Matrix (Fin n) (Fin n) K :=
    fun a => ((ρ (s a) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have htr : ∀ a b : P ⧸ Subgroup.center P, a ≠ b →
      Matrix.trace (f a * (((ρ (s b))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 0 := by
    intro a b hab
    have hnc : s a * (s b)⁻¹ ∉ Subgroup.center P := by
      intro h
      apply hab
      have h1 : ((s a * (s b)⁻¹ : P) : P ⧸ Subgroup.center P) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs a, hs b] at h1
      exact mul_inv_eq_one.mp h1
    have := trace_eq_zero_of_noncentral ρ hρ hcomm hnc
    simpa [f] using this
  have hli : LinearIndependent K f := by
    rw [linearIndependent_iff']
    intro t g hsum j hj
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
      Matrix.trace (M * (((ρ (s j))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hsum
    simp only [Finset.sum_mul, Matrix.zero_mul, Matrix.trace_zero, Matrix.smul_mul] at h1
    rw [Matrix.trace_sum] at h1
    simp only [Matrix.trace_smul, smul_eq_mul] at h1
    rw [Finset.sum_eq_single_of_mem j hj] at h1
    · have hjj : Matrix.trace (f j * (((ρ (s j))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
          (n : K) := by
        simp [f]
      rw [hjj] at h1
      exact (mul_eq_zero.mp h1).resolve_right hnK
    · intro i _ hij
      rw [htr i j hij, mul_zero]
  have hspan : Submodule.span K (Set.range f) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    have h1 : Fintype.card (P ⧸ Subgroup.center P) = n ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [Module.finrank_matrix, Module.finrank_self, h1, Fintype.card_fin]
    ring
  intro z hz
  have hcz : ∀ M : Matrix (Fin n) (Fin n) K, Commute (ρ z : Matrix (Fin n) (Fin n) K) M := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range f) := by rw [hspan]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hM
    · rintro _ ⟨a, rfl⟩
      have hz' := Subgroup.mem_center_iff.mp hz (s a)
      have : ρ z * ρ (s a) = ρ (s a) * ρ z := by rw [← map_mul, ← map_mul, hz']
      have h3 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) this
      exact h3
    · exact Commute.zero_right _
    · intro x y _ _ hx hy
      exact hx.add_right hy
    · intro a x _ hx
      exact hx.smul_right a
  obtain ⟨c, hc⟩ : (ρ z : Matrix (Fin n) (Fin n) K) ∈ Set.range (Matrix.scalar (Fin n)) :=
    Matrix.mem_range_scalar_of_commute_single (fun i j _ => (hcz _).symm)
  have hn0 : n ≠ 0 := fun h => hnK (by simp [h])
  have hdet : IsUnit (c ^ n) := by
    have h1 := (Matrix.isUnit_iff_isUnit_det _).mp (ρ z).isUnit
    rw [← hc] at h1
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using h1
  obtain ⟨u, hu⟩ := ((isUnit_pow_iff hn0).mp hdet)
  refine ⟨u, Units.ext ?_⟩
  simp [← hc, hu]


theorem card_le_of_projective_cover_three {m : ℕ} {K : Type} [Field K] (hqK : (3 : K) ≠ 0)
    {P : Type} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (ρ : P →* GL (Fin 3) K) (hρ : Function.Injective ρ)
    (hdet : ∀ g : P, ((ρ g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    (Z₀ : Subgroup P) (hZ₀ : ∀ z ∈ Z₀, ∃ c : Kˣ, ρ z = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hcomm : ∀ g h : P, g * h * g⁻¹ * h⁻¹ ∈ Z₀) (hpow : ∀ x : P, x ^ 3 ∈ Z₀)
    (hcard : Nat.card P = 3 ^ m * Nat.card Z₀) : 3 ^ m ≤ 27 := by
  classical
  have hq : (3 : ℕ).Prime := Nat.prime_three
  have h3K : ((3 : ℕ) : K) ≠ 0 := by simpa using hqK
  have hcommρ : ∀ g h : P, ∃ c : Kˣ,
      ρ (g * h * g⁻¹ * h⁻¹) = Matrix.GeneralLinearGroup.scalar (Fin 3) c :=
    fun g h => hZ₀ _ (hcomm g h)
  have hquot : Nat.card (P ⧸ Subgroup.center P) ≤ 3 ^ 2 :=
    card_quotient_center_le_sq ρ hρ h3K hcommρ
  set C : Subgroup P := Subgroup.center P with hC
  let _ : CommGroup C :=
    { (inferInstance : Group C) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : C →* C := powMonoidHom 3
  have hsq : Nat.card C = Nat.card φ.ker * Nat.card φ.range :=
    (Subgroup.card_ker_mul_card_range φ).symm
  have hrange : Nat.card φ.range ≤ Nat.card Z₀ := by
    have hle : φ.range.map C.subtype ≤ Z₀ := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hpow x
    calc Nat.card φ.range = Nat.card (φ.range.map C.subtype) :=
          (Subgroup.card_map_of_injective C.subtype_injective).symm
      _ ≤ Nat.card Z₀ := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle)
  have hkerP : ∀ a : φ.ker, ((a : C) : P) ^ 3 = 1 := by
    intro a
    have h1 : (a : C) ^ 3 = 1 := a.2
    have := congrArg (fun x : C => (x : P)) h1
    simpa using this
  set Y : Subgroup (GL (Fin 3) K) := (φ.ker.map C.subtype).map ρ with hY
  have hYcard : Nat.card Y = Nat.card φ.ker := by
    rw [hY, Subgroup.card_map_of_injective hρ, Subgroup.card_map_of_injective C.subtype_injective]
  have hYmem : ∀ g ∈ Y, ∃ a : C, a ∈ φ.ker ∧ ρ (a : P) = g := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  have : Finite Y :=
    (Set.Finite.subset (Set.finite_range ρ) (fun g hg => by
      obtain ⟨a, -, rfl⟩ := hYmem g hg
      exact ⟨(a : P), rfl⟩)).to_subtype
  have hYcomm : ∀ g ∈ Y, ∀ h ∈ Y, g * h = h * g := by
    intro g hg h hh
    obtain ⟨a, -, rfl⟩ := hYmem g hg
    obtain ⟨b, -, rfl⟩ := hYmem h hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp a.2 (b : P)).symm
  have hYexp : ∀ g ∈ Y, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := hYmem g hg
    rw [← map_pow]
    have h1 : (a : C) ^ 3 = 1 := ha
    have h2 : (a : P) ^ 3 = 1 := by
      have := congrArg (fun x : C => (x : P)) h1
      simpa using this
    rw [h2, map_one]
  have hYdet : ∀ g ∈ Y, (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := hYmem g hg
    exact hdet a
  have hYbound : Nat.card Y ≤ 3 ^ (3 - 1) := by
    have := card_le_pow_pred_of_det_gl hq hqK Y hYcomm hYexp hYdet
    simpa using this
  have hCcard : Nat.card C ≤ 3 ^ (3 - 1) * Nat.card Z₀ := by
    rw [hsq]
    exact Nat.mul_le_mul (hYcard ▸ hYbound) hrange
  have hPcard : Nat.card P = Nat.card (P ⧸ C) * Nat.card C :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hZpos : 0 < Nat.card Z₀ := Nat.card_pos
  by_cases ha : Nat.card (P ⧸ C) ≤ 3
  · have hchain : 3 ^ m * Nat.card Z₀ ≤ 27 * Nat.card Z₀ := by
      calc 3 ^ m * Nat.card Z₀ = Nat.card P := hcard.symm
        _ = Nat.card (P ⧸ C) * Nat.card C := hPcard
        _ ≤ 3 * (3 ^ (3 - 1) * Nat.card Z₀) := Nat.mul_le_mul ha hCcard
        _ = 27 * Nat.card Z₀ := by norm_num; ring
    exact Nat.le_of_mul_le_mul_right hchain hZpos
  ·
    have hpq : IsPGroup 3 (P ⧸ C) := hP.to_quotient C
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpq
    have hk2 : k = 2 := by
      have h1 : 3 ^ k ≤ 3 ^ 2 := hk ▸ hquot
      have h2 : 3 < 3 ^ k := hk ▸ lt_of_not_ge ha
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
      by_contra hne
      have hk1 : k ≤ 1 := by omega
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      omega
    have hscalar := center_scalar_of_card_eq_sq ρ hρ h3K hcommρ (by rw [hk, hk2])
    have hker3 : Nat.card φ.ker ≤ 3 := by
      have hc : ∀ a : φ.ker, ∃ c : K, c ^ 3 = 1 ∧
          (ρ ((a : C) : P) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
        intro a
        obtain ⟨u, hu⟩ := hscalar ((a : C) : P) a.1.2
        have hu' : (ρ ((a : C) : P) : Matrix (Fin 3) (Fin 3) K) =
            Matrix.scalar (Fin 3) (u : K) := by
          rw [hu]; rfl
        refine ⟨u, ?_, hu'⟩
        have h1 : ρ (((a : C) : P) ^ 3) = 1 := by rw [hkerP a, map_one]
        have h2 : ((ρ ((a : C) : P) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
          rw [← Units.val_pow_eq_pow_val, ← map_pow, h1]; rfl
        rw [hu', ← map_pow] at h2
        have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) h2
        simpa using h3
      choose F hF1 hF2 using hc
      have hinj : Function.Injective F := by
        intro a b hab
        have h1 : (ρ ((a : C) : P) : Matrix (Fin 3) (Fin 3) K) = ρ ((b : C) : P) := by
          rw [hF2 a, hF2 b, hab]
        have h2 : ρ ((a : C) : P) = ρ ((b : C) : P) := Units.ext h1
        exact Subtype.ext (Subtype.ext (hρ h2))
      have hS : ∀ a, F a ∈ (Polynomial.nthRoots 3 (1 : K)).toFinset := fun a => by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
        exact hF1 a
      calc Nat.card φ.ker ≤ Nat.card (Polynomial.nthRoots 3 (1 : K)).toFinset :=
            Nat.card_le_card_of_injective (fun a => ⟨F a, hS a⟩) (fun a b hab => hinj
              (congrArg Subtype.val hab))
        _ ≤ 3 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_coe]
            exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
    have hCle : Nat.card C ≤ 3 * Nat.card Z₀ := by
      rw [hsq]
      exact Nat.mul_le_mul hker3 hrange
    have hchain : 3 ^ m * Nat.card Z₀ ≤ 27 * Nat.card Z₀ := by
      calc 3 ^ m * Nat.card Z₀ = Nat.card P := hcard.symm
        _ = Nat.card (P ⧸ C) * Nat.card C := hPcard
        _ = 3 ^ 2 * Nat.card C := by rw [hk, hk2]
        _ ≤ 3 ^ 2 * (3 * Nat.card Z₀) := Nat.mul_le_mul_left _ hCle
        _ = 27 * Nat.card Z₀ := by ring
    exact Nat.le_of_mul_le_mul_right hchain hZpos


theorem card_le_of_statedProj_three {K : Type} [Field K] [Finite K] (hqK : (3 : K) ≠ 0)
    (M : Subgroup (GL (Fin 3) K))
    (hdet : ∀ g ∈ M, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    {T : Type} [Group T] (e : T ≃* StatedProj M) {D : Subgroup T} (hD : IsElementaryAbelian 3 D) :
    Nat.card D ≤ 27 := by
  classical
  have : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have : Finite T := Finite.of_equiv (StatedProj M) e.symm.toEquiv
  let N : Subgroup M := (StatedScalars (Fin 3) K).subgroupOf M
  let π : M →* T := e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hπker : π.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hDp : IsPGroup 3 D := by
    have := hD
    exact IsElementaryAbelian.isPGroup 3 D
  obtain ⟨P⟩ : Nonempty (Sylow 3 (D.comap π)) := inferInstance
  set P' : Subgroup M := (P : Subgroup (D.comap π)).map (D.comap π).subtype with hP'
  have hmap : P'.map π = D := map_sylow_comap π hπ hDp P
  have hP'fin : Finite P' := inferInstance
  have hP'p : IsPGroup 3 P' :=
    (P.isPGroup').of_equiv
      ((P : Subgroup (D.comap π)).equivMapOfInjective _ (D.comap π).subtype_injective)
  let ρ : P' →* GL (Fin 3) K := M.subtype.comp P'.subtype
  have hρ : Function.Injective ρ := M.subtype_injective.comp P'.subtype_injective
  let f : P' →* T := π.comp P'.subtype
  have hfrange : f.range = D := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hfmem : ∀ x : P', f x ∈ D := fun x => by
    rw [← hfrange]
    exact ⟨x, rfl⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hDp
  have hcard : Nat.card P' = 3 ^ m * Nat.card f.ker := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfrange, hm] at h
    rw [← h, mul_comm]
  have hq1 : ∀ x : P', (f x) ^ 3 = 1 := fun x =>
    elemPow_eq_one_of_isElementaryAbelian (f x) (hfmem x)
  have := card_le_of_projective_cover_three (m := m) hqK hP'p ρ hρ
    (fun g => hdet g.1 g.1.2) f.ker (fun z hz => ?_) (fun g h => ?_) (fun x => ?_) hcard
  · rw [hm]
    exact this
  ·
    have hzM : (z : M) ∈ π.ker := hz
    rw [hπker] at hzM
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hzM
    exact ⟨c, hc.symm⟩
  ·
    rw [MonoidHom.mem_ker]
    have h1 : f g * f h = f h * f g := by
      have := hD.is_comm.comm (⟨f g, hfmem g⟩ : D) ⟨f h, hfmem h⟩
      exact congrArg Subtype.val this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc f g * f h * (f g)⁻¹ * (f h)⁻¹ = (f h * f g) * (f g)⁻¹ * (f h)⁻¹ := by rw [h1]
      _ = 1 := by group
  · rw [MonoidHom.mem_ker, map_pow]
    exact hq1 x

end CFSG.RankThree.PartOne.F106
