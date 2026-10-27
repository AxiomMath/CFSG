module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusLinear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.GroupTheory.QuasisimplePSolvable
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem eq_of_mul_inv_mem_center {X : Type*} [Group X] {Y : Subgroup X}
    (hYp : Group.IsPerfect Y) (φ : X →* X) (h : ∀ y ∈ Y, φ y * y⁻¹ ∈ Subgroup.center X) :
    ∀ y ∈ Y, φ y = y := by
  let ζ : Y →* Subgroup.center X :=
    { toFun := fun y => ⟨φ y * (y : X)⁻¹, h y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := Subgroup.mem_center_iff.mp (h b b.2) (φ a)
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        have ha := Subgroup.mem_center_iff.mp (h a a.2) (φ b * (b : X)⁻¹)
        calc φ a * φ b * ((b : X)⁻¹ * (a : X)⁻¹) = φ a * (φ b * (b : X)⁻¹) * (a : X)⁻¹ := by
              group
          _ = φ b * (b : X)⁻¹ * φ a * (a : X)⁻¹ := by rw [hb]
          _ = φ a * (a : X)⁻¹ * (φ b * (b : X)⁻¹) := by
              rw [mul_assoc (φ b * (b : X)⁻¹), ha] }
  intro y hy
  have h1 := map_eq_one_of_isPerfect hYp ζ ⟨y, hy⟩
  have h2 : φ y * y⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

theorem exists_lift_of_coprime {X Q : Type*} [Group X] [Group Q] {π : X →* Q}
    (hπ : Function.Surjective π) (Y : Subgroup Q)
    (hcop : Nat.Coprime (Nat.card π.ker) (Nat.card Y)) :
    ∃ Y' : Subgroup X, Y'.map π = Y ∧ Disjoint Y' π.ker := by
  set Ŷ := Y.comap π with hŶ
  have hker : π.ker ≤ Ŷ := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    change π x ∈ Y
    rw [hx]
    exact Y.one_mem
  set N := π.ker.subgroupOf Ŷ with hN
  have : N.Normal := Subgroup.Normal.subgroupOf inferInstance _
  let ρ : Ŷ →* Y := (π.comp Ŷ.subtype).codRestrict Y fun x => x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := hπ q
    exact ⟨⟨x, hq⟩, rfl⟩
  have hρker : ρ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hN, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hNcard : Nat.card N = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  have hNindex : N.index = Nat.card Y := by
    rw [← hρker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top]
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := N)
    (by rw [hNcard, hNindex]; exact hcop)
  refine ⟨H.map Ŷ.subtype, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨_, ⟨h, -, rfl⟩, rfl⟩
      exact h.2
    · intro hq
      obtain ⟨x, rfl⟩ := hπ q
      have hx : (⟨x, hq⟩ : Ŷ) ∈ H ⊔ N := by
        rw [sup_comm, hH.sup_eq_top]
        exact Subgroup.mem_top _
      obtain ⟨h, hh, n, hn, hhn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      refine ⟨Ŷ.subtype h, ⟨h, hh, rfl⟩, ?_⟩
      have hn' : π (n : X) = 1 := by
        have := hn
        rw [hN, Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at this
        exact this
      have := congrArg (fun z : Ŷ => π (z : X)) hhn
      simp only [Subgroup.coe_mul, map_mul, hn', mul_one] at this
      exact this
  · rw [Subgroup.disjoint_def]
    rintro _ ⟨h, hh, rfl⟩ hker'
    have hhN : h ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact hker'
    have := Subgroup.disjoint_def.mp hH.disjoint hhN hh
    rw [this]
    rfl

section SL3

variable {k : Type} [Field k]

@[expose] def cycThreeMat (k : Type) [Field k] : Matrix (Fin 3) (Fin 3) k :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cycThree (k : Type) [Field k] : SpecialLinearGroup (Fin 3) k :=
  ⟨cycThreeMat k, by simp [cycThreeMat, Matrix.det_fin_three]⟩

theorem cycThree_pow_three : cycThree k ^ 3 = 1 := by
  have h : cycThreeMat k ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycThreeMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  exact Subtype.ext h

theorem cycThree_not_mem_scalars : cycThree k ∉ scalars 3 k := by
  rintro ⟨c, -, hc⟩
  have h := congrFun (congrFun hc 0) 2
  simp [cycThree, cycThreeMat, Matrix.scalar_apply] at h

theorem pow_three_eq_one_of_mem_scalars {z : SpecialLinearGroup (Fin 3) k}
    (hz : z ∈ scalars 3 k) : z ^ 3 = 1 := by
  obtain ⟨c, hc, hz⟩ := hz
  have h : (z : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
    rw [hz, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  exact Subtype.ext h

theorem eq_one_of_pow_three_of_not_three_dvd {G : Type*} [Group G] {V : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card V) {v : G} (hv : v ∈ V) (hv3 : v ^ 3 = 1) : v = 1 := by
  have h1 : orderOf (⟨v, hv⟩ : V) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hv3))
  have h2 : orderOf (⟨v, hv⟩ : V) ∣ Nat.card V := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
  · exact absurd (h ▸ h2) h3

theorem eq_bot_of_le_of_isSubnormal_sl3 {V V₁ : Subgroup (SpecialLinearGroup (Fin 3) k)}
    (h3 : ¬ 3 ∣ Nat.card V) (hVV₁ : V ≤ V₁) (hV₁ : V₁ ≤ V ⊔ scalars 3 k)
    (hsn : V₁.IsSubnormal) : V = ⊥ := by
  have hsimple : IsSimpleGroup (projectiveSL 3 k) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  rcases (hsn.map (proj_surjective 3 k)).eq_bot_or_top_of_isSimpleGroup hsimple with h | h
  · rw [eq_bot_iff]
    intro v hv
    have hv1 : proj 3 k v = 1 := by
      have : proj 3 k v ∈ V₁.map (proj 3 k) := ⟨v, hVV₁ hv, rfl⟩
      rw [h] at this
      exact this
    rw [proj_eq_one_iff] at hv1
    exact eq_one_of_pow_three_of_not_three_dvd h3 hv (pow_three_eq_one_of_mem_scalars hv1)
  · exfalso
    have ht : proj 3 k (cycThree k) ∈ V₁.map (proj 3 k) := h ▸ Subgroup.mem_top _
    obtain ⟨v₁, hv₁, hv₁t⟩ := ht
    have hz : (cycThree k)⁻¹ * v₁ ∈ scalars 3 k := by
      rw [← proj_eq_one_iff, map_mul, map_inv, hv₁t, inv_mul_cancel]
    obtain ⟨v, hv, z', hz', hvz'⟩ := Subgroup.mem_sup_of_normal_right.mp (hV₁ hv₁)
    set z := (cycThree k)⁻¹ * v₁ * z'⁻¹ with hzdef
    have hzs : z ∈ scalars 3 k := mul_mem hz (inv_mem hz')
    have hvz : v = cycThree k * z := by
      rw [hzdef, ← hvz']
      group
    have hcomm : Commute (cycThree k) z :=
      ((scalars_le_center 3 k hzs).comm (cycThree k)).symm
    have hv3 : v ^ 3 = 1 := by
      rw [hvz, hcomm.mul_pow, cycThree_pow_three, pow_three_eq_one_of_mem_scalars hzs, one_mul]
    have hv1 := eq_one_of_pow_three_of_not_three_dvd h3 hv hv3
    apply cycThree_not_mem_scalars (k := k)
    have : cycThree k = z⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hvz, hv1]
    rw [this]
    exact inv_mem hzs

end SL3

theorem exists_cubeRoot_field (F : Type) [Field F] [Finite F] (c : F) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : F →+* K) (ω μ : K),
      ω ^ 2 + ω + 1 = 0 ∧ μ ^ 3 = φ c := by
  obtain ⟨K₁, _, _, φ₁, ω₁, hω₁⟩ := exists_splittingField_cubeRoot F
  set f : Polynomial K₁ := Polynomial.X ^ 3 - Polynomial.C (φ₁ c) with hf
  have : Finite f.SplittingField := Module.finite_of_finite K₁
  have hdeg : (Polynomial.map (algebraMap K₁ f.SplittingField) f).degree ≠ 0 := by
    have h3 : f.degree = 3 := by
      rw [hf]
      compute_degree!
    rw [Polynomial.degree_map, h3]
    exact three_ne_zero
  obtain ⟨μ, hμ⟩ := (Polynomial.SplittingField.splits f).exists_eval_eq_zero hdeg
  refine ⟨f.SplittingField, inferInstance, inferInstance,
    (algebraMap K₁ f.SplittingField).comp φ₁, algebraMap K₁ f.SplittingField ω₁, μ, ?_, ?_⟩
  · rw [← map_pow, ← map_add, ← map_one (algebraMap K₁ f.SplittingField), ← map_add, hω₁,
      map_zero]
  · simp only [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hμ
    rw [RingHom.comp_apply]
    exact sub_eq_zero.mp hμ

theorem eq_bot_of_commute_glThree_of_pow_three_eq_smul {F : Type}
    [Field F] [Finite F] (h3 : (3 : F) ≠ 0) {A : GL (Fin 3) F} {c : F}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • 1)
    (hns : ∀ a : F, (A : Matrix (Fin 3) (Fin 3) F) ≠ a • 1) (Y : Subgroup (GL (Fin 3) F))
    (hYA : ∀ y ∈ Y, y * A = A * y) (hYp : Group.IsPerfect Y) (hY3 : ¬ 3 ∣ Nat.card Y) :
    Y = ⊥ := by
  obtain ⟨K, _, _, φ, ω, μ, hω, hμ⟩ := exists_cubeRoot_field F c
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := congrArg Matrix.det hA3
    rw [Matrix.det_pow, zero_smul, Matrix.det_zero] at h
    exact (A.isUnit.map Matrix.detMonoidHom).ne_zero (pow_eq_zero_iff (by norm_num) |>.mp h)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact hc0 (φ.injective (hμ.symm.trans (map_zero φ).symm))
  set m := Matrix.GeneralLinearGroup.map (n := Fin 3) φ with hm
  have hinj : Function.Injective m := map_gl_injective φ
  set A' : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) F).map φ with hA'
  set g : Matrix (Fin 3) (Fin 3) K := μ⁻¹ • A' with hg
  have hA'3 : A' ^ 3 = φ c • 1 := by
    rw [hA', ← Matrix.map_pow, hA3]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hg3 : g ^ 3 = 1 := by
    rw [hg, smul_pow, hA'3, smul_smul, inv_pow, ← hμ, inv_mul_cancel₀ (pow_ne_zero 3 hμ0),
      one_smul]
  have hY' : Y.map m = ⊥ := by
    refine eq_bot_of_commute_of_finrank_le_two (three_ne_zero_map φ h3) hω (g := g)
      (fun c' hc' => finrank_range_eigenProj_le_two_of_ne_smul_one hg3 (fun a ha => ?_) hc')
      (Y.map m) ?_ ?_ ?_
    · have hA'a : A' = (μ * a) • 1 := by
        calc A' = μ • g := by rw [hg, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
          _ = (μ * a) • 1 := by rw [ha, smul_smul]
      exact hns _ (eq_smul_one_of_map_eq_smul_one φ hA'a)
    · rintro _ ⟨y, hy, rfl⟩
      have h := congrArg (fun z : GL (Fin 3) F => ((m z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (hYA y hy)
      simp only [map_mul, Units.val_mul] at h
      rw [hg, Matrix.mul_smul, Matrix.smul_mul]
      exact congrArg (μ⁻¹ • ·) h
    · have := hYp
      exact Group.IsPerfect.map m
    · rwa [Subgroup.card_map_of_injective hinj]
  exact (Subgroup.map_eq_bot_iff_of_injective Y hinj).mp hY'

private theorem coprime_card_of_perfect_subgroup_of_complement_derived
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hNPC : CFSG.HasNormalPComplement p ↥(_root_.commutator G))
    (Y : Subgroup G) [Group.IsPerfect Y] : Nat.Coprime p (Nat.card Y) := by
  have hYle : Y ≤ _root_.commutator G := by
    rw [← Subgroup.commutator_eq_self (H := Y), _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect
    (CFSG.hasNormalPComplement_of_le p hYle hNPC)

theorem lift_card_and_perfect {X Q : Type*} [Group X] [Group Q] {π : X →* Q} {Y : Subgroup Q}
    {Y' : Subgroup X} (hmap : Y'.map π = Y) (hdisj : Disjoint Y' π.ker) :
    Nat.card Y' = Nat.card Y ∧ (Group.IsPerfect Y → Group.IsPerfect Y') := by
  let ρ : Y' →* Y := (π.comp Y'.subtype).codRestrict Y fun y => hmap ▸ ⟨y, y.2, rfl⟩
  have hρi : Function.Injective ρ := by
    intro a b hab
    have h1 : π ((a : X) * (b : X)⁻¹) = 1 := by
      have := congrArg Subtype.val hab
      simp only [ρ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
      rw [map_mul, map_inv, this, mul_inv_cancel]
    have h2 := Subgroup.disjoint_def.mp hdisj (Y'.mul_mem a.2 (Y'.inv_mem b.2)) h1
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hρs : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hmap] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, hy⟩, rfl⟩
  let e : Y' ≃* Y := MulEquiv.ofBijective ρ ⟨hρi, hρs⟩
  refine ⟨Nat.card_congr e.toEquiv, fun hYp => ?_⟩
  have := hYp
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

variable {K : Type} [Field K] [Finite K]

theorem coprime_card_scalars {m : ℕ} (hm : ¬ 3 ∣ m) : Nat.Coprime (Nat.card (scalars 3 K)) m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (scalars 3 K) := by
    rw [IsPGroup.iff_orderOf]
    intro z
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simpa using pow_three_eq_one_of_mem_scalars z.2))
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)

theorem eq_bot_of_fix_conjAut_of_pow_three_eq_smul
    {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) {A : GL (Fin 3) K} {c : K}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • 1)
    (hns : ∀ a : K, (A : Matrix (Fin 3) (Fin 3) K) ≠ a • 1)
    (Y : Subgroup (projectiveSL 3 K)) (hYp : Group.IsPerfect Y)
    (hY3 : ¬ 3 ∣ Nat.card Y) (hfix : ∀ y ∈ Y, conjAut 3 K A y = y) : Y = ⊥ := by
  obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (proj_surjective 3 K) Y
    (by rw [ker_proj]; exact coprime_card_scalars hY3)
  obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
  have hfix : ∀ y ∈ Y', slConjugation 3 K A y = y := by
    refine eq_of_mul_inv_mem_center (hY'p hYp)
      (slConjugation 3 K A).toMonoidHom fun y hy => ?_
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have hyY : proj 3 K y ∈ Y := hY'map ▸ ⟨y, hy, rfl⟩
    have h1 := hfix _ hyY
    rw [conjAut_proj] at h1
    change proj 3 K (slConjugation 3 K A y) * (proj 3 K y)⁻¹ = 1
    rw [h1, mul_inv_cancel]
  set Y'' : Subgroup (GL (Fin 3) K) := Y'.map SpecialLinearGroup.toGL with hY''
  have hY''bot : Y'' = ⊥ := by
    refine eq_bot_of_commute_glThree_of_pow_three_eq_smul h3 hA3 hns Y'' ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      apply Units.ext
      have h1 := congrArg (fun z : SpecialLinearGroup (Fin 3) K =>
        (z : Matrix (Fin 3) (Fin 3) K)) (hfix y hy)
      simp only [coe_slConjugation] at h1
      change (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)
      calc (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
          (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
            ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (A : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
        _ = (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) := by
            rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    · have := hY'p hYp
      exact Group.IsPerfect.map _
    · rwa [Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective, hY'card]
  have hY'bot : Y' = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective Y' SpecialLinearGroup.toGL_injective).mp hY''bot
  rw [← hY'map, hY'bot, Subgroup.map_bot]

theorem isSolvable_of_projective_cube_scalar_centralizer_and_complement
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    (h3 : (3 : F) ≠ 0) (ρ : G →* projectiveSL 3 F)
    (hker : ρ.ker ≤ Subgroup.center G) {A : GL (Fin 3) F} {c : F}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • 1)
    (hns : ∀ a : F, (A : Matrix (Fin 3) (Fin 3) F) ≠ a • 1)
    (hfix : ∀ g : G, conjAut 3 F A (ρ g) = ρ g)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator G)) :
    Group.IsSolvable G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  rw [Group.isSolvable_iff_commutator_lt]
  intro Y hY
  refine lt_of_le_of_ne (Subgroup.commutator_le.2 ?_) ?_
  · intro a ha b hb
    rw [_root_.commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
  · intro hperf
    have : Group.IsPerfect Y := Subgroup.isPerfect_iff.mpr hperf
    have hY3 : ¬ 3 ∣ Nat.card Y := Nat.prime_three.coprime_iff_not_dvd.mp
      (coprime_card_of_perfect_subgroup_of_complement_derived hNPC Y)
    let Z := Y.map ρ
    have : Group.IsPerfect Z := Group.IsPerfect.map ρ
    have hZ3 : ¬ 3 ∣ Nat.card Z := fun hd => hY3 (hd.trans (Subgroup.card_map_dvd Y ρ))
    have hZeq : Z = ⊥ :=
      eq_bot_of_fix_conjAut_of_pow_three_eq_smul
        h3 hA3 hns Z inferInstance hZ3
        (by rintro _ ⟨g, _, rfl⟩; exact hfix g)
    have hYs : Group.IsSolvable Y := Group.isSolvable_of_comm fun x y => by
      have hx : ρ (x : G) = 1 := by
        have hm : ρ (x : G) ∈ Z := ⟨x, x.2, rfl⟩
        rwa [hZeq, Subgroup.mem_bot] at hm
      exact Subtype.ext ((Subgroup.mem_center_iff.mp (hker hx)) (y : G)).symm
    exact hY (eq_bot_of_isPerfect_of_isSolvable
      inferInstance hYs)

theorem threePrimeB3_projectiveSL_three_all (h3 : (3 : K) ≠ 0) :
    ThreePrimeB3 (projectiveSL 3 K) := by
  have hsimple : IsSimpleGroup (projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs _
  have hkerc : Nat.card (proj 3 K).ker = Nat.card (scalars 3 K) := by rw [ker_proj]
  by_cases hD : β ∈ linearAutGroup 3 K
  ·
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq] at hD
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨-, d, hd⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hβ])
    have hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    by_cases hAs : ∃ a : K, (A : Matrix (Fin 3) (Fin 3) K) = a • 1
    ·
      obtain ⟨a, ha⟩ := hAs
      have hβ1 : conjAut 3 K A = 1 := by
        ext x
        obtain ⟨g, rfl⟩ := proj_surjective 3 K x
        rw [conjAut_proj, MulAut.one_apply]
        congr 1
        apply Subtype.ext
        rw [coe_slConjugation]
        have hAi : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        calc (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            (g : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
              ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
          _ = (g : Matrix (Fin 3) (Fin 3) K) := by
              rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z, hβ1]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn
        hRs
    · push Not at hAs
      suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
      exact eq_bot_of_fix_conjAut_of_pow_three_eq_smul h3 hA3 hAs Y hYp hY3
        (fun y hy => (hC y).mp (hYC hy))
  ·
    obtain ⟨σ, hσ3, H, hβH⟩ := linear_order_three_field_descent (by norm_num) β hβ hD
    suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
    set τ := conjAut 3 K H with hτ
    set C₀ : Subgroup (projectiveSL 3 K) :=
      (fieldAut 3 K σ).toMonoidHom.eqLocus (MonoidHom.id _) with hC₀
    set Y₀ : Subgroup (projectiveSL 3 K) := Y.map (τ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom
      with hY₀
    have hβτ : ∀ z, β z = z ↔ fieldAut 3 K σ (τ⁻¹ z) = τ⁻¹ z := by
      intro z
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply]
      constructor
      · intro h
        have := congrArg (τ⁻¹ : MulAut (projectiveSL 3 K)) h
        rwa [show τ⁻¹ (τ (fieldAut 3 K σ (τ⁻¹ z))) = fieldAut 3 K σ (τ⁻¹ z) from
          τ.symm_apply_apply _] at this
      · intro h
        rw [h]
        exact τ.apply_symm_apply z
    have hY₀C₀ : Y₀ ≤ C₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hβτ y).mp ((hC y).mp (hYC hy))
    have hsn₀ : (Y₀.subgroupOf C₀).IsSubnormal := by
      let ρ : C →* C₀ :=
        ((τ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom.comp C.subtype).codRestrict C₀ fun c =>
          (hβτ c).mp ((hC c).mp c.2)
      have hρ : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        have hτz : τ⁻¹ (τ z) = z := τ.symm_apply_apply z
        refine ⟨⟨τ z, (hC _).mpr ((hβτ _).mpr ?_)⟩, ?_⟩
        · rw [hτz]
          exact hz
        · apply Subtype.ext
          exact hτz
      have hmap : (Y.subgroupOf C).map ρ = Y₀.subgroupOf C₀ := by
        ext ⟨z, hz⟩
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, hcz⟩
          refine ⟨c, hc, ?_⟩
          exact congrArg Subtype.val hcz
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
      rw [← hmap]
      exact hsn.map hρ
    have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
      rwa [hY₀, Subgroup.card_map_of_injective
        (f := (τ⁻¹ : MulAut (projectiveSL 3 K)).toMonoidHom) (MulEquiv.injective _)]
    have hY₀p : Group.IsPerfect Y₀ := by
      have := hYp
      exact Group.IsPerfect.map _
    obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (proj_surjective 3 K) Y₀
      (by rw [hkerc]; exact coprime_card_scalars hY₀3)
    obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
    have hfix : ∀ y ∈ Y', SpecialLinearGroup.map σ.toRingHom y = y := by
      refine eq_of_mul_inv_mem_center (hY'p hY₀p) (SpecialLinearGroup.map σ.toRingHom)
        fun y hy => ?_
      rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv,
        ← fieldAut_proj]
      have hyY : proj 3 K y ∈ C₀ := hY₀C₀ (hY'map ▸ ⟨y, hy, rfl⟩)
      have h1 : fieldAut 3 K σ (proj 3 K y) = proj 3 K y := hyY
      rw [h1, mul_inv_cancel]
    set ψ := SpecialLinearGroup.map (n := Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ).subtype with hψ
    have hψi : Function.Injective ψ := sl_map_subtype_injective σ
    have hY'ψ : Y' ≤ ψ.range := fun y hy => by
      obtain ⟨y₀, hy₀⟩ := exists_sl_map_subtype_eq (hfix y hy)
      exact ⟨y₀, hy₀⟩
    set V := Y'.comap ψ with hV
    set V₁ := Y₀.comap ((proj 3 K).comp ψ) with hV₁
    have hVmap : V.map ψ = Y' := Subgroup.map_comap_eq_self hY'ψ
    have hV3 : ¬ 3 ∣ Nat.card V := by
      rw [← Subgroup.card_map_of_injective hψi, hVmap, hY'card]
      exact hY₀3
    have hVV₁ : V ≤ V₁ := fun s hs => by
      change proj 3 K (ψ s) ∈ Y₀
      rw [← hY'map]
      exact ⟨ψ s, hs, rfl⟩
    have hV₁V : V₁ ≤ V ⊔ scalars 3 (CFSG.GH74.GLS.IVK.fixedField σ) := by
      intro s hs
      have hs' : proj 3 K (ψ s) ∈ Y'.map (proj 3 K) := by rw [hY'map]; exact hs
      obtain ⟨y, hy, hys⟩ := hs'
      obtain ⟨t, ht⟩ := hY'ψ hy
      have htV : t ∈ V := by
        change ψ t ∈ Y'
        rw [ht]
        exact hy
      have hz : ψ (t⁻¹ * s) ∈ scalars 3 K := by
        rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, map_inv, hys,
          inv_mul_cancel]
      have hzs : t⁻¹ * s ∈ scalars 3 (CFSG.GH74.GLS.IVK.fixedField σ) := by
        obtain ⟨c, hc, hcz⟩ := hz
        set w := t⁻¹ * s with hw
        have hdiag : (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) =
            (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 • 1 := by
          apply eq_smul_one_of_map_eq_smul_one (CFSG.GH74.GLS.IVK.fixedField σ).subtype
          rw [show (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)).map
              (CFSG.GH74.GLS.IVK.fixedField σ).subtype = (ψ w : Matrix (Fin 3) (Fin 3) K) from rfl,
            hcz, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        have hdet := w.2
        rw [hdiag, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
        have hw0 : (w : Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 ≠ 0 := by
          intro h0
          rw [h0, zero_pow (by norm_num)] at hdet
          exact zero_ne_one hdet
        refine ⟨Units.mk0 _ hw0, Units.ext (by simpa using hdet), ?_⟩
        rw [Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
        exact hdiag
      have : s = t * (t⁻¹ * s) := by group
      rw [this]
      exact Subgroup.mul_mem_sup htV hzs
    have hsn₁ : V₁.IsSubnormal := by
      let θ : SpecialLinearGroup (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ) →* C₀ :=
        ((proj 3 K).comp ψ).codRestrict C₀ fun s => by
          change fieldAut 3 K σ (proj 3 K (ψ s)) = proj 3 K (ψ s)
          rw [fieldAut_proj]
          congr 1
          ext i j
          exact CFSG.GH74.GLS.IVK.fixedField_apply σ _
      have hcomap : (Y₀.subgroupOf C₀).comap θ = V₁ := by
        ext s
        rfl
      rw [← hcomap]
      exact hsn₀.comap θ
    have hVbot := eq_bot_of_le_of_isSubnormal_sl3 hV3 hVV₁ hV₁V hsn₁
    have hY'bot : Y' = ⊥ := by rw [← hVmap, hVbot, Subgroup.map_bot]
    have hY₀bot : Y₀ = ⊥ := by rw [← hY'map, hY'bot, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective Y
      (τ⁻¹ : MulAut (projectiveSL 3 K)).injective).mp hY₀bot

omit [Finite K] in
theorem slFieldAut_eq_map (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 3) K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ A =
      SpecialLinearGroup.map σ.toRingHom A := by
  ext i j
  rfl

omit [Finite K] in
theorem eq_of_descendAut_eq {e₁ e₂ : MulAut (SpecialLinearGroup (Fin 3) K)}
    (h : descendAut 3 K e₁ = descendAut 3 K e₂) : e₁ = e₂ := by
  have hperf : Group.IsPerfect (⊤ : Subgroup (SpecialLinearGroup (Fin 3) K)) := by
    have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) (n := 3) le_rfl
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv (G := SpecialLinearGroup (Fin 3) K)).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hfix := eq_of_mul_inv_mem_center hperf (e₂⁻¹ * e₁ : MulAut _).toMonoidHom fun y _ => by
    have h1 := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K y)) h
    simp only [descendAut_proj] at h1
    have h2 : e₂ ((e₂⁻¹ * e₁) y) = e₁ y := e₂.apply_symm_apply _
    have hw : proj 3 K ((e₂⁻¹ * e₁) y) = proj 3 K y := by
      apply (descendAut 3 K e₂).injective
      rw [descendAut_proj, descendAut_proj, h2, h1]
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    change proj 3 K ((e₂⁻¹ * e₁) y) * (proj 3 K y)⁻¹ = 1
    rw [hw, mul_inv_cancel]
  ext y
  have := hfix y (Subgroup.mem_top y)
  change e₂⁻¹ (e₁ y) = y at this
  have h2 := congrArg e₂ this
  rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h2
  rw [h2]

theorem threePrimeB3_slThree (h3 : (3 : K) ≠ 0) :
    ThreePrimeB3 (SpecialLinearGroup (Fin 3) K) := by
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs _
  suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
  set β' := descendAut 3 K β with hβ'
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hβ, map_one]
  by_cases hD : β' ∈ linearAutGroup 3 K
  · rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq] at hD
    obtain ⟨A, hA⟩ := hD
    have hβA : β = slConjugation 3 K A :=
      eq_of_descendAut_eq (by rw [← hβ', ← hA]; rfl)
    obtain ⟨-, d, hd⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hA, hβ'3])
    have hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hfix : ∀ y ∈ Y, (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = y := by
      intro y hy
      have h1 := (hC y).mp (hYC hy)
      rw [hβA] at h1
      have h2 := congrArg (fun z : SpecialLinearGroup (Fin 3) K =>
        (z : Matrix (Fin 3) (Fin 3) K)) h1
      simpa only [coe_slConjugation] using h2
    by_cases hAs : ∃ a : K, (A : Matrix (Fin 3) (Fin 3) K) = a • 1
    ·
      obtain ⟨a, ha⟩ := hAs
      have hCtop : C = ⊤ := by
        rw [eq_top_iff]
        intro z _
        rw [hC z, hβA]
        have hcomm : (A : Matrix (Fin 3) (Fin 3) K) * (z : Matrix (Fin 3) (Fin 3) K) =
            (z : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
          rw [ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
        have hz : ((slConjugation 3 K A
            z : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = z := by
          rw [coe_slConjugation, hcomm, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            mul_one]
        exact Subtype.ext hz
      subst hCtop
      have hYsn : Y.IsSubnormal := by
        have := hsn.map (f := (⊤ : Subgroup (SpecialLinearGroup (Fin 3) K)).subtype)
          (fun z => ⟨⟨z, Subgroup.mem_top z⟩, rfl⟩)
        rwa [Subgroup.subgroupOf_map_subtype, inf_top_eq] at this
      exact eq_bot_of_le_of_isSubnormal_sl3 hY3 le_rfl le_sup_left hYsn
    · push Not at hAs
      have hY'' := eq_bot_of_commute_glThree_of_pow_three_eq_smul h3 hA3 hAs
        (Y.map SpecialLinearGroup.toGL) (by
          rintro _ ⟨y, hy, rfl⟩
          apply Units.ext
          change (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
            (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)
          calc (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) =
              (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
                ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (A : Matrix (Fin 3) (Fin 3) K) := by rw [hfix y hy]
            _ = (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) := by
                rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one])
        (by
          have := hYp
          exact Group.IsPerfect.map _)
        (by rwa [Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective])
      exact (Subgroup.map_eq_bot_iff_of_injective Y SpecialLinearGroup.toGL_injective).mp hY''
  · obtain ⟨σ, hσ3, H, hβ'H⟩ := linear_order_three_field_descent (by norm_num) β' hβ'3 hD
    set τ := slConjugation 3 K H with hτ
    set φ := CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin 3) K σ
      with hφ
    have hβH : β = τ * φ * τ⁻¹ :=
      eq_of_descendAut_eq (by rw [← hβ', hβ'H, map_mul, map_mul, map_inv]; rfl)
    set C₀ : Subgroup (SpecialLinearGroup (Fin 3) K) := φ.toMonoidHom.eqLocus (MonoidHom.id _)
      with hC₀
    set Y₀ : Subgroup (SpecialLinearGroup (Fin 3) K) := Y.map (τ⁻¹ : MulAut _).toMonoidHom
      with hY₀
    have hβτ : ∀ z, β z = z ↔ φ (τ⁻¹ z) = τ⁻¹ z := by
      intro z
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply]
      constructor
      · intro h
        have := congrArg (τ⁻¹ : MulAut (SpecialLinearGroup (Fin 3) K)) h
        rwa [show τ⁻¹ (τ (φ (τ⁻¹ z))) = φ (τ⁻¹ z) from τ.symm_apply_apply _] at this
      · intro h
        rw [h]
        exact τ.apply_symm_apply z
    have hY₀C₀ : Y₀ ≤ C₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hβτ y).mp ((hC y).mp (hYC hy))
    have hsn₀ : (Y₀.subgroupOf C₀).IsSubnormal := by
      let ρ : C →* C₀ :=
        ((τ⁻¹ : MulAut (SpecialLinearGroup (Fin 3) K)).toMonoidHom.comp C.subtype).codRestrict C₀
          fun c => (hβτ c).mp ((hC c).mp c.2)
      have hρ : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        have hτz : τ⁻¹ (τ z) = z := τ.symm_apply_apply z
        refine ⟨⟨τ z, (hC _).mpr ((hβτ _).mpr ?_)⟩, ?_⟩
        · rw [hτz]
          exact hz
        · apply Subtype.ext
          exact hτz
      have hmap : (Y.subgroupOf C).map ρ = Y₀.subgroupOf C₀ := by
        ext ⟨z, hz⟩
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, hcz⟩
          exact ⟨c, hc, congrArg Subtype.val hcz⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
      rw [← hmap]
      exact hsn.map hρ
    have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
      rwa [hY₀, Subgroup.card_map_of_injective
        (f := (τ⁻¹ : MulAut (SpecialLinearGroup (Fin 3) K)).toMonoidHom) (MulEquiv.injective _)]
    set ψ := SpecialLinearGroup.map (n := Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ).subtype with hψ
    have hψi : Function.Injective ψ := sl_map_subtype_injective σ
    have hψC₀ : ∀ s, ψ s ∈ C₀ := fun s => by
      change φ (ψ s) = ψ s
      rw [hφ, slFieldAut_eq_map]
      ext i j
      exact CFSG.GH74.GLS.IVK.fixedField_apply σ _
    have hY₀ψ : Y₀ ≤ ψ.range := fun y hy => by
      have h1 : φ y = y := hY₀C₀ hy
      rw [hφ, slFieldAut_eq_map] at h1
      obtain ⟨y₀, hy₀⟩ := exists_sl_map_subtype_eq h1
      exact ⟨y₀, hy₀⟩
    set V := Y₀.comap ψ with hV
    have hVmap : V.map ψ = Y₀ := Subgroup.map_comap_eq_self hY₀ψ
    have hV3 : ¬ 3 ∣ Nat.card V := by
      rw [← Subgroup.card_map_of_injective hψi, hVmap]
      exact hY₀3
    have hsnV : V.IsSubnormal := by
      let θ : SpecialLinearGroup (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ) →* C₀ :=
        ψ.codRestrict C₀ hψC₀
      have hcomap : (Y₀.subgroupOf C₀).comap θ = V := by
        ext s
        rfl
      rw [← hcomap]
      exact hsn₀.comap θ
    have hVbot := eq_bot_of_le_of_isSubnormal_sl3 hV3 le_rfl le_sup_left hsnV
    have hY₀bot : Y₀ = ⊥ := by rw [← hVmap, hVbot, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective Y
      (τ⁻¹ : MulAut (SpecialLinearGroup (Fin 3) K)).injective).mp hY₀bot

theorem three_ne_zero_of_charP {F : Type} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (hp3 : p ≠ 3) : (3 : F) ≠ 0 := by
  intro h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff F p 3).mp (by exact_mod_cast h)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp hdvd)

open CFSG.Assembly.RankThreeEven (projSL) in
theorem threePrimeB3_projSL_three_galoisField (p e : ℕ)
    [Fact p.Prime] (hp3 : p ≠ 3) : ThreePrimeB3 (projSL 3 (GaloisField p e)) := by
  obtain ⟨τ₀⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p e)
  exact threePrimeB3_of_mulEquiv τ₀
    (threePrimeB3_projectiveSL_three_all (three_ne_zero_of_charP hp3))

theorem threePrimeB3_statedSL_three_all {p n : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hK : Nat.card K = p ^ n) :
    ThreePrimeB3 (CFSG.Assembly.LowTwoRank.StatedSL 3 K) := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact threePrimeB3_of_mulEquiv
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    (threePrimeB3_slThree (three_ne_zero_of_charP hp3))

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
