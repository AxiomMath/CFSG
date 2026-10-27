module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Aux
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
import CFSG.GH74.L5U5.IdentUnitary

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

section Outer

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

namespace U48Out

private theorem commute_scalar4 (g : GL (Fin 4) K) (d : Kˣ) :
    Commute g (GeneralLinearGroup.scalar (Fin 4) d) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact ((Matrix.scalar_commute (d : K) (fun r => Commute.all (d : K) r) _)).eq.symm

private theorem exists_fixedField {φ : K ≃+* K} (hφ : orderOf φ = 3) :
    ∃ k₀ : Subfield K, (∀ a, a ∈ k₀ ↔ φ a = a) ∧ Nat.card k₀ = 4 := by
  have hK6 : Nat.card K = 2 ^ 6 := by rw [card_K]; norm_num
  obtain ⟨-, -, -, -, -, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (n := 6) (by norm_num) hK6
  obtain ⟨-, S, hS, hScard⟩ := hfix (Subgroup.zpowers φ)
  refine ⟨S, fun a => ?_, ?_⟩
  · rw [← SetLike.mem_coe, hS]
    refine ⟨fun h => h φ (Subgroup.mem_zpowers φ), fun h τ hτ => ?_⟩
    have hle : Subgroup.zpowers φ ≤ MulAction.stabilizer (K ≃+* K) a :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
    exact MulAction.mem_stabilizer_iff.mp (hle hτ)
  · rw [hScard, Nat.card_zpowers, hφ]; norm_num

private theorem mem_range_map_of_fixed {φ : K ≃+* K} {k₀ : Subfield K}
    (hk₀ : ∀ a, a ∈ k₀ ↔ φ a = a) {y : GL (Fin 4) K} (hy : glAut φ y = y) :
    y ∈ (GeneralLinearGroup.map k₀.subtype : GL (Fin 4) k₀ →* GL (Fin 4) K).range := by
  have hent : ∀ z : GL (Fin 4) K, glAut φ z = z →
      ∀ i j, ((z : Matrix (Fin 4) (Fin 4) K) i j) ∈ k₀ := by
    intro z hz i j
    rw [hk₀]
    have := congrFun (congrFun
      (congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) hz) i) j
    simpa [coe_glAut] using this
  have hyinv : glAut φ y⁻¹ = y⁻¹ := by rw [map_inv, hy]
  let Y : Matrix (Fin 4) (Fin 4) k₀ :=
    Matrix.of fun i j => ⟨(y : Matrix (Fin 4) (Fin 4) K) i j, hent y hy i j⟩
  let Y' : Matrix (Fin 4) (Fin 4) k₀ :=
    Matrix.of fun i j => ⟨((y⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j, hent _ hyinv i j⟩
  have hinj : Function.Injective (fun M : Matrix (Fin 4) (Fin 4) k₀ => M.map k₀.subtype) :=
    Matrix.map_injective k₀.subtype_injective
  have hYY' : Y * Y' = 1 := by
    apply hinj
    change (Y * Y').map k₀.subtype = (1 : Matrix (Fin 4) (Fin 4) k₀).map k₀.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : Y.map k₀.subtype = (y : Matrix (Fin 4) (Fin 4) K) := by ext i j; rfl
    have h2 : Y'.map k₀.subtype = ((y⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j; rfl
    rw [h1, h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY'Y : Y' * Y = 1 := by
    apply hinj
    change (Y' * Y).map k₀.subtype = (1 : Matrix (Fin 4) (Fin 4) k₀).map k₀.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : Y.map k₀.subtype = (y : Matrix (Fin 4) (Fin 4) K) := by ext i j; rfl
    have h2 : Y'.map k₀.subtype = ((y⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j; rfl
    rw [h1, h2, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨Y, Y', hYY', hY'Y⟩, ?_⟩
  apply Units.ext
  ext i j
  rfl

private theorem not_dvd_of_fixed {φ : K ≃+* K} (hφ : orderOf φ = 3) (B : GL (Fin 4) K)
    (H : Subgroup (GL (Fin 4) K)) (hfix : ∀ x ∈ H, glAut φ (B⁻¹ * x * B) = B⁻¹ * x * B) :
    ¬ 19 ∣ Nat.card H := by
  intro h19
  obtain ⟨k₀, hk₀, hcard⟩ := exists_fixedField hφ
  set ι : GL (Fin 4) k₀ →* GL (Fin 4) K := GeneralLinearGroup.map k₀.subtype with hι
  have hιinj : Function.Injective ι := by
    refine Units.map_injective ?_
    exact Matrix.map_injective k₀.subtype_injective
  set f : GL (Fin 4) K →* GL (Fin 4) K := (MulAut.conj B⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj B⁻¹).injective
  have hle : H.map f ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    have := hfix x hx
    exact mem_range_map_of_fixed hk₀ (by simpa [hf, MulAut.conj_apply, mul_assoc] using this)
  have h1 : Nat.card (H.map f) = Nat.card H := Subgroup.card_map_of_injective hfinj
  have h2 : Nat.card ι.range = Nat.card (GL (Fin 4) k₀) :=
    (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
  have h3 : Nat.card H ∣ Nat.card (GL (Fin 4) k₀) := by
    rw [← h1, ← h2]
    exact Subgroup.card_dvd_of_le hle
  have : Fintype k₀ := Fintype.ofFinite k₀
  have h4 : Nat.card (GL (Fin 4) k₀) = ∏ i : Fin 4, (4 ^ 4 - 4 ^ (i : ℕ)) := by
    have hq : Fintype.card k₀ = 4 := by rw [← Nat.card_eq_fintype_card, hcard]
    rw [Matrix.card_GL_field, hq]
  rw [h4, Fin.prod_univ_four] at h3
  have h19' := h19.trans h3
  norm_num at h19'

private theorem fieldSU4_one' : fieldSU4 1 = 1 := by
  ext g : 2
  change glAut 1 (g : GL (Fin 4) K) = g
  rw [map_one]
  rfl

private theorem fieldSU4_pow' (φ : K ≃+* K) (m : ℕ) : fieldSU4 φ ^ m = fieldSU4 (φ ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, fieldSU4_one']
  | succ m ih =>
    rw [pow_succ, ih]
    ext g : 2
    change glAut (φ ^ m) (glAut φ (g : GL (Fin 4) K)) = glAut (φ ^ (m + 1)) (g : GL (Fin 4) K)
    rw [pow_succ, map_mul]
    rfl

private theorem mul_apply_apply_eq_one' {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    {F α : MulAut X} (g : X) (hα : ∀ x, α x = g * F x * g⁻¹) (hF3 : F ^ 3 = 1)
    (hα3 : α ^ 3 = 1) : g * F g * F (F g) = 1 := by
  have hF3' : ∀ x, F (F (F x)) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hF3
    simpa [pow_succ] using this
  have hα3' : ∀ x, α (α (α x)) = x := fun x => by
    have := congrArg (fun f : MulAut X => f x) hα3
    simpa [pow_succ] using this
  have key : ∀ x, α (α (α x)) = (g * F g * F (F g)) * x * (g * F g * F (F g))⁻¹ := by
    intro x
    simp only [hα, map_mul, map_inv, hF3']
    group
  have hN : g * F g * F (F g) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := key x
    rw [hα3' x] at h1
    calc x * (g * F g * F (F g)) = (g * F g * F (F g)) * x * (g * F g * F (F g))⁻¹ *
          (g * F g * F (F g)) := by rw [← h1]
      _ = (g * F g * F (F g)) * x := by group
  rw [hZ] at hN
  exact Subgroup.mem_bot.mp hN

end U48Out

theorem u48_not_dvd_of_outer (α : MulAut SU4) (hα : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : SU4 →* MulAut SU4).range) (H : Subgroup SU4)
    (hH : ∀ h ∈ H, α h = h) : ¬ 19 ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : K ≃+* K := fieldFactor4 α with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hα, map_one]
  have hφ1 : φ ≠ 1 := fun h => hout (mem_range_conj_of_fieldFactor4_eq_one h)
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨g₀, hg₀⟩ := exists_conj_field4 α
  have hα' : ∀ x, α x = g₀ * fieldSU4 φ x * g₀⁻¹ := fun x => Subtype.ext (by rw [hg₀ x]; rfl)
  have hF3 : fieldSU4 φ ^ 3 = 1 := by rw [U48Out.fieldSU4_pow', hφ3]; exact U48Out.fieldSU4_one'
  have hN : g₀ * fieldSU4 φ g₀ * fieldSU4 φ (fieldSU4 φ g₀) = 1 :=
    U48Out.mul_apply_apply_eq_one' center_SU4 g₀ hα' hF3 hα
  have hc : GeneralLinearGroup.scalar (Fin 4) (1 : Kˣ) = (g₀ : GL (Fin 4) K) *
      GeneralLinearGroup.map (φ : K →+* K) (g₀ : GL (Fin 4) K) *
        GeneralLinearGroup.map ((φ * φ : K ≃+* K) : K →+* K) (g₀ : GL (Fin 4) K) := by
    have h1 := congrArg (fun y : SU4 => (y : GL (Fin 4) K)) hN
    simp only [Subgroup.coe_mul, coe_fieldSU4, OneMemClass.coe_one] at h1
    rw [map_one, ← h1]
    refine congrArg₂ _ (congrArg₂ _ rfl rfl) ?_
    apply Units.ext
    ext i j
    rfl
  obtain ⟨B, d, hB⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_mul_map_eq_scalar_mul_of_orderOf_eq_three
      (n := 4) (by norm_num) hφord (g₀ : GL (Fin 4) K) hc
  set G : GL (Fin 4) K := (g₀ : GL (Fin 4) K) with hG
  set s : GL (Fin 4) K := GeneralLinearGroup.scalar (Fin 4) d with hs
  have hB2 : G * glAut φ B = s * B := hB
  have hB3 : glAut φ B = G⁻¹ * (s * B) := by
    rw [eq_inv_mul_iff_mul_eq]
    exact hB2
  have hfix : ∀ x ∈ H.map (SUid σ4 4).subtype, glAut φ (B⁻¹ * x * B) = B⁻¹ * x * B := by
    rintro _ ⟨y, hy, rfl⟩
    show glAut φ (B⁻¹ * (y : GL (Fin 4) K) * B) = B⁻¹ * (y : GL (Fin 4) K) * B
    set P : GL (Fin 4) K := (y : GL (Fin 4) K) with hP
    have h1 : P = G * glAut φ P * G⁻¹ := by
      have := hg₀ y
      rw [hH y hy] at this
      exact this
    have hPφ : glAut φ P = G⁻¹ * P * G := by
      calc glAut φ P = G⁻¹ * (G * glAut φ P * G⁻¹) * G := by group
        _ = G⁻¹ * P * G := by rw [← h1]
    rw [map_mul, map_mul, map_inv, hB3, hPφ]
    have hcomm : P * s = s * P := (U48Out.commute_scalar4 P d).eq
    calc (G⁻¹ * (s * B))⁻¹ * (G⁻¹ * P * G) * (G⁻¹ * (s * B)) = B⁻¹ * (s⁻¹ * P * s) * B := by group
      _ = B⁻¹ * P * B := by rw [mul_assoc s⁻¹, hcomm, inv_mul_cancel_left]
  have hcard : Nat.card (H.map (SUid σ4 4).subtype) = Nat.card H :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  rw [← hcard]
  exact U48Out.not_dvd_of_fixed hφord B _ hfix

end Outer

section Component

open Matrix CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV (torusSnoc torusSnoc_castSucc torusSnoc_last)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K hK card_K card_units_K)

namespace U48Comp

private theorem perfect_hom_eq_one {L A : Type*} [Group L] [Group.IsPerfect L] [CommGroup A]
    (g : L →* A) (x : L) : g x = 1 := by
  have h : commutator L ≤ g.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    simp [mul_comm]
  rw [Group.IsPerfect.commutator_eq_top] at h
  exact h (Subgroup.mem_top x)

private theorem perfect_mul_eq_one {G : Type*} [Group G] (L : Subgroup G) [Group.IsPerfect L]
    (f : G → K) (hone : f 1 = 1) (hmul : ∀ x ∈ L, ∀ y ∈ L, f (x * y) = f x * f y) :
    ∀ x ∈ L, f x = 1 := by
  intro x hx
  let g : L →* K :=
    { toFun := fun x => f x
      map_one' := hone
      map_mul' := fun x y => hmul x x.2 y y.2 }
  have := perfect_hom_eq_one g.toHomUnits ⟨x, hx⟩
  have h2 := congrArg (fun u : Kˣ => (u : K)) this
  simpa [g] using h2

private theorem card_Su_aux (n : ℕ) : Nat.card (Su K 2 3 n) = Nat.card (StatedSU n (2 ^ 3) K) :=
  Nat.card_congr (MulEquiv.subgroupCongr (SUid_eq_statedSU card_K n)).toEquiv

private theorem card_Su_two : Nat.card (Su K 2 3 2) = 504 := by
  have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hK (n := 2) (by norm_num)
  rw [card_Su_aux]
  have : (Nat.card (StatedSU 2 (2 ^ 3) K) : ℤ) = 504 := by
    rw [h]
    norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast this

private theorem card_Su_three : Nat.card (Su K 2 3 3) = 16547328 := by
  have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hK (n := 3) (by norm_num)
  rw [card_Su_aux]
  have : (Nat.card (StatedSU 3 (2 ^ 3) K) : ℤ) = 16547328 := by
    rw [h]
    norm_num [Finset.prod_Icc_succ_top]
  exact_mod_cast this

private theorem isMulCommutative_of_isPGroup_su2 {Q : Subgroup (Su K 2 3 2)} (hQ : IsPGroup 3 Q) :
    IsMulCommutative Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ 504 := card_Su_two ▸ Subgroup.card_subgroup_dvd_card Q
  have hn2 : n ≤ 2 := by
    by_contra h
    push Not at h
    have h1 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 h
    rw [← hn] at h1
    have := h1.trans hdvd
    norm_num at this
  interval_cases n
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hn).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Nat.card Q = 3 := by rw [hn]; norm_num
    have : IsCyclic Q := isCyclic_of_prime_card (p := 3) this
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hn

private theorem eq_top_of_perfect_subnormal {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) {P : Subgroup X} (hP : Group.IsPerfect P) (hPs : P.IsSubnormal)
    (hP1 : P ≠ ⊥) : P = ⊤ := by
  have hcomp : CFSG.IsComponent (⊤ : Subgroup X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hX,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hPs with h | h
  · exact top_le_iff.mp h
  · exfalso
    apply hP1
    have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer (P : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hcen : P ≤ Subgroup.center X := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) x hx).symm
    have hab : ∀ a b : P, a * b = b * a := fun a b =>
      Subtype.ext ((Subgroup.mem_center_iff.mp (hcen a.2)) b).symm
    have htop : commutator P = ⊤ := hP.commutator_eq_top
    have hbot : commutator P = ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact hab b a
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ commutator P := htop ▸ Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

private theorem aschbacherSolvableCore_eq_bot {G : Type*} [Group G] [Finite G]
    (hq : CFSG.IsQuasisimple G) (hZ : ∀ z ∈ Subgroup.center G, z ^ 3 = 1) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G = ⊥ := by
  obtain ⟨hsolv, hchar, h3, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := G)
      Nat.prime_three
  have hnormal : (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hnormal with h | h
  · exfalso
    have : Nontrivial G := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have hG : Group.IsSolvable G := by
      rw [h] at hsolv
      exact solvable_of_surjective (G := (⊤ : Subgroup G))
        (f := (Subgroup.topEquiv (G := G)).toMonoidHom) (Subgroup.topEquiv (G := G)).surjective
    have := hq.1
    exact Group.IsPerfect.not_isSolvable G hG
  · rw [eq_bot_iff]
    intro x hx
    have hx3 : x ^ 3 = 1 := hZ x (h hx)
    have hord : orderOf (⟨x, hx⟩ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext hx3
    have hord2 : orderOf (⟨x, hx⟩ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G) ∣
        Nat.card (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G) := orderOf_dvd_natCard _
    have : orderOf (⟨x, hx⟩ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h1
      · exact h1
      · rw [h1] at hord2
        exact absurd hord2 h3
    rw [orderOf_eq_one_iff, Subgroup.mk_eq_one] at this
    exact this ▸ Subgroup.one_mem _

private structure CompHyp (c : SU4) (L : Subgroup SU4) : Prop where
  ord : orderOf c = 3
  le : L ≤ Subgroup.centralizer ({c} : Set SU4)
  sn : (L.subgroupOf (Subgroup.centralizer ({c} : Set SU4))).IsSubnormal
  perf : Group.IsPerfect L
  mem : c ∈ L
  nonab : ∃ P : Subgroup SU4, P ≤ L ∧ IsPGroup 3 P ∧ ¬ IsMulCommutative P

private def CompConcl (L : Subgroup SU4) : Prop :=
  19 ∣ Nat.card L ∧ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 L = ⊥ ∧
    ∀ D : Subgroup SU4, D ≤ Subgroup.centralizer (L : Set SU4) →
      CFSG.Open.IsElemAbelian 3 D → Nat.card D ≤ 3

private theorem map_centralizer_singleton (e : SU4 ≃* SU4) (c : SU4) :
    (Subgroup.centralizer ({c} : Set SU4)).map e.toMonoidHom =
      Subgroup.centralizer ({e c} : Set SU4) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e x * e c = e c * e x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy

private theorem CompHyp.map (e : SU4 ≃* SU4) {c : SU4} {L : Subgroup SU4} (h : CompHyp c L) :
    CompHyp (e c) (L.map e.toMonoidHom) where
  ord := (orderOf_injective e.toMonoidHom e.injective c).trans h.ord
  le := by
    rintro _ ⟨l, hl, rfl⟩
    have hlc := Subgroup.mem_centralizer_singleton_iff.mp (h.le hl)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e l * e c = e c * e l
    rw [← map_mul, ← map_mul, hlc]
  sn := by
    let φ : Subgroup.centralizer ({c} : Set SU4) ≃* Subgroup.centralizer ({e c} : Set SU4) :=
      (Subgroup.equivMapOfInjective (Subgroup.centralizer ({c} : Set SU4)) e.toMonoidHom
        e.injective).trans (MulEquiv.subgroupCongr (map_centralizer_singleton e c))
    have hφ : (L.subgroupOf (Subgroup.centralizer ({c} : Set SU4))).map φ.toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf (Subgroup.centralizer ({e c} : Set SU4)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_map_of_mem e.toMonoidHom (Subgroup.mem_subgroupOf.mp hy))
      · intro hx
        obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        exact ⟨⟨l, h.le hl⟩, Subgroup.mem_subgroupOf.mpr hl, Subtype.ext hle⟩
    have hsn := Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective h.sn
    rw [hφ] at hsn
    exact hsn
  perf := by
    haveI := h.perf
    exact Group.IsPerfect.map e.toMonoidHom
  mem := Subgroup.mem_map_of_mem e.toMonoidHom h.mem
  nonab := by
    obtain ⟨P, hPL, hP3, hPn⟩ := h.nonab
    refine ⟨P.map e.toMonoidHom, Subgroup.map_mono hPL, ?_, ?_⟩
    · exact hP3.of_equiv (P.equivMapOfInjective e.toMonoidHom e.injective)
    · intro hcomm
      apply hPn
      refine ⟨⟨fun a b => ?_⟩⟩
      have := hcomm.is_comm.comm ⟨e a, Subgroup.mem_map_of_mem _ a.2⟩
        ⟨e b, Subgroup.mem_map_of_mem _ b.2⟩
      have h2 : e (a : SU4) * e (b : SU4) = e (b : SU4) * e (a : SU4) := congrArg Subtype.val this
      apply Subtype.ext
      apply e.injective
      simpa only [Subgroup.coe_mul, map_mul] using h2

private theorem CompConcl.of_map (e : SU4 ≃* SU4) {L : Subgroup SU4}
    (h : CompConcl (L.map e.toMonoidHom)) : CompConcl L := by
  obtain ⟨h19, hθ, hD⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective] at h19
  · have h1 := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv (p := 3) Nat.prime_three
      (L.equivMapOfInjective e.toMonoidHom e.injective)
    rw [hθ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (L.equivMapOfInjective e.toMonoidHom e.injective).injective).mp h1
  · intro D hD' hDe
    have hle : D.map e.toMonoidHom ≤
        Subgroup.centralizer ((L.map e.toMonoidHom : Subgroup SU4) : Set SU4) := by
      rintro _ ⟨d, hd, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp (hD' hd) x hx
      change e x * e d = e d * e x
      rw [← map_mul, ← map_mul, this]
    have hee : CFSG.Open.IsElemAbelian 3 (D.map e.toMonoidHom) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
        have := hDe.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
        apply Subtype.ext
        change (a : SU4) * b = b * a
        rw [← ha, ← hb]
        change e a' * e b' = e b' * e a'
        rw [← map_mul, ← map_mul]
        exact congrArg e (congrArg Subtype.val this)
      · rintro _ ⟨d, hd, rfl⟩
        change e d ^ 3 = 1
        rw [← map_pow, hDe.2 d hd, map_one]
    have := hD _ hle hee
    rwa [Subgroup.card_map_of_injective e.injective] at this

private abbrev mat (x : SU4) : Matrix (Fin 4) (Fin 4) K :=
  ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

private theorem mat_mul (x y : SU4) : mat (x * y) = mat x * mat y := rfl

private theorem mat_one : mat (1 : SU4) = 1 := rfl

private theorem mat_injective : Function.Injective mat := fun _ _ h => Subtype.ext (Units.ext h)

private theorem mat_pow (x : SU4) (n : ℕ) : mat (x ^ n) = mat x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

private theorem det_mat (x : SU4) : (mat x).det = 1 := x.2.1

private theorem conjTr_mat_mul (x : SU4) : conjTr σ4 (mat x) * mat x = 1 := x.2.2

private def reidxMon (π : Equiv.Perm (Fin 4)) :
    Matrix (Fin 4) (Fin 4) K →* Matrix (Fin 4) (Fin 4) K where
  toFun M := M.submatrix π π
  map_one' := Matrix.submatrix_one_equiv π
  map_mul' M N := (Matrix.submatrix_mul_equiv M N π π π).symm

private def reidxGL (π : Equiv.Perm (Fin 4)) : GL (Fin 4) K →* GL (Fin 4) K :=
  Units.map (reidxMon π)

private theorem coe_reidxGL (π : Equiv.Perm (Fin 4)) (g : GL (Fin 4) K) :
    ((reidxGL π g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (g : Matrix (Fin 4) (Fin 4) K).submatrix π π :=
  rfl

private theorem reidxGL_mem (π : Equiv.Perm (Fin 4)) {g : GL (Fin 4) K} (hg : g ∈ SUid σ4 4) :
    reidxGL π g ∈ SUid σ4 4 := by
  obtain ⟨hdet, hu⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [coe_reidxGL, Matrix.det_submatrix_equiv_self, hdet]
  · have h1 : conjTr σ4 ((g : Matrix (Fin 4) (Fin 4) K).submatrix π π) =
        (conjTr σ4 (g : Matrix (Fin 4) (Fin 4) K)).submatrix π π := by
      unfold conjTr
      rw [← Matrix.submatrix_map, Matrix.transpose_submatrix]
    rw [coe_reidxGL, h1, Matrix.submatrix_mul_equiv, hu, Matrix.submatrix_one_equiv]

private def reidxHom (π : Equiv.Perm (Fin 4)) : SU4 →* SU4 :=
  ((reidxGL π).comp (SUid σ4 4).subtype).codRestrict (SUid σ4 4) fun g => reidxGL_mem π g.2

private theorem mat_reidxHom (π : Equiv.Perm (Fin 4)) (x : SU4) :
    mat (reidxHom π x) = (mat x).submatrix π π :=
  rfl

private def reidx (π : Equiv.Perm (Fin 4)) : SU4 ≃* SU4 :=
  MonoidHom.toMulEquiv (reidxHom π) (reidxHom π⁻¹)
    (MonoidHom.ext fun x => mat_injective (by
      ext i j
      simp [mat_reidxHom]))
    (MonoidHom.ext fun x => mat_injective (by
      ext i j
      simp [mat_reidxHom]))

private theorem exists_perm_aux : ∀ i j k : Fin 4, i ≠ j → j ≠ k → i ≠ k →
    ∃ π : Equiv.Perm (Fin 4), π 0 = i ∧ π 1 = j ∧ π 3 = k := by
  decide

private theorem exists_nf {c : SU4} (hc : orderOf c = 3) :
    ∃ (e : SU4 ≃* SU4) (d : Fin 4 → K), mat (e c) = diagonal d ∧ d 0 = d 1 ∧ d 3 ≠ d 0 := by
  have hc3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  obtain ⟨g, hg⟩ := exists_conj_isDiag (P := Subgroup.zpowers c)
    (fun x hx y hy => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self c i j).eq)
    (fun x hx => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm i, _root_.zpow_mul, zpow_natCast, hc3,
        _root_.one_zpow])
  set c₁ : SU4 := g * c * g⁻¹ with hc₁
  have hdiag : (mat c₁).IsDiag := hg c (Subgroup.mem_zpowers c)
  set d : Fin 4 → K := fun i => mat c₁ i i with hd
  have hmat : mat c₁ = diagonal d := hdiag.diagonal_diag.symm
  have hc₁3 : c₁ ^ 3 = 1 := by rw [hc₁, conj_pow, hc3, mul_one, mul_inv_cancel]
  have hcube : ∀ i, d i ^ 3 = 1 := by
    have h3 : (mat c₁) ^ 3 = 1 := by rw [← mat_pow, hc₁3]; rfl
    rw [hmat, diagonal_pow] at h3
    intro i
    have := congrFun (congrFun h3 i) i
    simpa using this
  have hne : ∀ i, d i ≠ 0 := fun i h0 => by
    have := hcube i
    rw [h0] at this
    norm_num at this
  let f : Fin 4 → μ3 := fun i =>
    ⟨Units.mk0 (d i) (hne i), (mem_rootsOfUnity 3 _).mpr (Units.ext (by simpa using hcube i))⟩
  have : Fintype μ3 := Fintype.ofFinite μ3
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_μ3]; norm_num)
  have hdij : d i = d j := by
    have := congrArg (fun u : μ3 => ((u : Kˣ) : K)) hfij
    simpa [f] using this
  obtain ⟨k, hk⟩ : ∃ k, d k ≠ d i := by
    by_contra hall
    push Not at hall
    have hdet : (mat c₁).det = 1 := det_mat c₁
    rw [hmat, det_diagonal, Fin.prod_univ_four, hall 0, hall 1, hall 2, hall 3] at hdet
    have h3 := hcube i
    have ht : d i = 1 := by
      calc d i = d i * d i ^ 3 := by rw [h3, mul_one]
        _ = d i * d i * d i * d i := by ring
        _ = 1 := hdet
    have hc1 : c₁ = 1 := by
      apply mat_injective
      rw [hmat, mat_one]
      have : d = fun _ => 1 := funext fun k => (hall k).trans ht
      rw [this]
      exact diagonal_one
    have hcc : c = 1 := by
      have : (MulAut.conj g) c = 1 := hc1
      exact (map_eq_one_iff _ (MulEquiv.injective _)).mp this
    rw [hcc, orderOf_one] at hc
    omega
  have hik : i ≠ k := fun h => hk (by rw [h])
  have hjk : j ≠ k := fun h => hk (by rw [← h]; exact hdij.symm)
  obtain ⟨π, hπ0, hπ1, hπ3⟩ := exists_perm_aux i j k hij hjk hik
  refine ⟨(MulAut.conj g).trans (reidx π), fun l => d (π l), ?_, ?_, ?_⟩
  · change (mat c₁).submatrix π π = _
    rw [hmat, Matrix.submatrix_diagonal_equiv]
    rfl
  · simp only [hπ0, hπ1, hdij]
  · simp only [hπ0, hπ3, hk]
    exact hk

private theorem isMulCommutative_of_jointly_injective {Γ G₁ G₂ : Type*} [Group Γ] [Group G₁]
    [Group G₂] (h₁ : ∀ Q : Subgroup G₁, IsPGroup 3 Q → IsMulCommutative Q)
    (h₂ : ∀ Q : Subgroup G₂, IsPGroup 3 Q → IsMulCommutative Q) (f₁ : Γ →* G₁) (f₂ : Γ →* G₂)
    (hinj : ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y) {P : Subgroup Γ} (hP : IsPGroup 3 P) :
    IsMulCommutative P := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have c₁ := (h₁ _ (hP.map f₁)).is_comm.comm ⟨f₁ a, Subgroup.mem_map_of_mem _ a.2⟩
    ⟨f₁ b, Subgroup.mem_map_of_mem _ b.2⟩
  have c₂ := (h₂ _ (hP.map f₂)).is_comm.comm ⟨f₂ a, Subgroup.mem_map_of_mem _ a.2⟩
    ⟨f₂ b, Subgroup.mem_map_of_mem _ b.2⟩
  have e₁ : f₁ (a : Γ) * f₁ (b : Γ) = f₁ (b : Γ) * f₁ (a : Γ) := congrArg Subtype.val c₁
  have e₂ : f₂ (a : Γ) * f₂ (b : Γ) = f₂ (b : Γ) * f₂ (a : Γ) := congrArg Subtype.val c₂
  apply Subtype.ext
  apply hinj
  · simpa only [Subgroup.coe_mul, map_mul] using e₁
  · simpa only [Subgroup.coe_mul, map_mul] using e₂

private def blk1 (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

private def blk2 (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 2 2, M 2 3; M 3 2, M 3 3]

private theorem blk1_one : blk1 (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk1]

private theorem blk2_one : blk2 (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

private theorem blk1_mul (M N : Matrix (Fin 4) (Fin 4) K) (h02 : M 0 2 = 0) (h03 : M 0 3 = 0)
    (h12 : M 1 2 = 0) (h13 : M 1 3 = 0) : blk1 (M * N) = blk1 M * blk1 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk1, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

private theorem blk2_mul (M N : Matrix (Fin 4) (Fin 4) K) (h20 : M 2 0 = 0) (h21 : M 2 1 = 0)
    (h30 : M 3 0 = 0) (h31 : M 3 1 = 0) : blk2 (M * N) = blk2 M * blk2 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, Matrix.mul_apply, Fin.sum_univ_four, h20, h21, h30, h31]

private theorem conjTr_blk1_mul_blk1 (M : Matrix (Fin 4) (Fin 4) K) (h20 : M 2 0 = 0)
    (h21 : M 2 1 = 0) (h30 : M 3 0 = 0) (h31 : M 3 1 = 0) :
    conjTr σ4 (blk1 M) * blk1 M = blk1 (conjTr σ4 M * M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, blk1, Matrix.mul_apply, Fin.sum_univ_four, h20, h21, h30, h31]

private theorem conjTr_blk2_mul_blk2 (M : Matrix (Fin 4) (Fin 4) K) (h02 : M 0 2 = 0)
    (h03 : M 0 3 = 0) (h12 : M 1 2 = 0) (h13 : M 1 3 = 0) :
    conjTr σ4 (blk2 M) * blk2 M = blk2 (conjTr σ4 M * M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, blk2, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

private structure Z22 (x : SU4) : Prop where
  h02 : mat x 0 2 = 0
  h03 : mat x 0 3 = 0
  h12 : mat x 1 2 = 0
  h13 : mat x 1 3 = 0
  h20 : mat x 2 0 = 0
  h21 : mat x 2 1 = 0
  h30 : mat x 3 0 = 0
  h31 : mat x 3 1 = 0

private theorem false_of_Z22 (L : Subgroup SU4) (hperf : Group.IsPerfect L)
    (hZ : ∀ x ∈ L, Z22 x)
    (hP : ∃ P : Subgroup SU4, P ≤ L ∧ IsPGroup 3 P ∧ ¬ IsMulCommutative P) : False := by
  obtain ⟨P, hPL, hP3, hPn⟩ := hP
  haveI := hperf
  have hD1 : ∀ x ∈ L, (blk1 (mat x)).det = 1 :=
    perfect_mul_eq_one L (fun x => (blk1 (mat x)).det) (by simp [mat_one, blk1_one])
      (fun x hx y hy => by
        rw [mat_mul, blk1_mul _ _ (hZ x hx).h02 (hZ x hx).h03 (hZ x hx).h12 (hZ x hx).h13,
          det_mul])
  have hD2 : ∀ x ∈ L, (blk2 (mat x)).det = 1 :=
    perfect_mul_eq_one L (fun x => (blk2 (mat x)).det) (by simp [mat_one, blk2_one])
      (fun x hx y hy => by
        rw [mat_mul, blk2_mul _ _ (hZ x hx).h20 (hZ x hx).h21 (hZ x hx).h30 (hZ x hx).h31,
          det_mul])
  let m₁ : L →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun x => blk1 (mat x)
      map_one' := by simp [mat_one, blk1_one]
      map_mul' := fun x y => by
        have := hZ x x.2
        rw [Subgroup.coe_mul, mat_mul, blk1_mul _ _ this.h02 this.h03 this.h12 this.h13] }
  let m₂ : L →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun x => blk2 (mat x)
      map_one' := by simp [mat_one, blk2_one]
      map_mul' := fun x y => by
        have := hZ x x.2
        rw [Subgroup.coe_mul, mat_mul, blk2_mul _ _ this.h20 this.h21 this.h30 this.h31] }
  let f₁ : L →* Su K 2 3 2 := m₁.toHomUnits.codRestrict (SUid σ4 2) fun x => by
    refine ⟨?_, ?_⟩
    · rw [MonoidHom.coe_toHomUnits]
      exact hD1 x x.2
    · rw [MonoidHom.coe_toHomUnits]
      have := hZ x x.2
      change conjTr σ4 (blk1 (mat x)) * blk1 (mat x) = 1
      rw [conjTr_blk1_mul_blk1 _ this.h20 this.h21 this.h30 this.h31, conjTr_mat_mul, blk1_one]
  let f₂ : L →* Su K 2 3 2 := m₂.toHomUnits.codRestrict (SUid σ4 2) fun x => by
    refine ⟨?_, ?_⟩
    · rw [MonoidHom.coe_toHomUnits]
      exact hD2 x x.2
    · rw [MonoidHom.coe_toHomUnits]
      have := hZ x x.2
      change conjTr σ4 (blk2 (mat x)) * blk2 (mat x) = 1
      rw [conjTr_blk2_mul_blk2 _ this.h02 this.h03 this.h12 this.h13, conjTr_mat_mul, blk2_one]
  have hinj : ∀ x y : L, f₁ x = f₁ y → f₂ x = f₂ y → x = y := by
    intro x y h1 h2
    have e1 : blk1 (mat x) = blk1 (mat y) :=
      congrArg (fun A : Su K 2 3 2 => ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1
    have e2 : blk2 (mat x) = blk2 (mat y) :=
      congrArg (fun A : Su K 2 3 2 => ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h2
    have hx := hZ x x.2
    have hy := hZ y y.2
    apply Subtype.ext
    apply mat_injective
    ext i j
    have e100 := congrFun (congrFun e1 0) 0
    have e101 := congrFun (congrFun e1 0) 1
    have e110 := congrFun (congrFun e1 1) 0
    have e111 := congrFun (congrFun e1 1) 1
    have e200 := congrFun (congrFun e2 0) 0
    have e201 := congrFun (congrFun e2 0) 1
    have e210 := congrFun (congrFun e2 1) 0
    have e211 := congrFun (congrFun e2 1) 1
    simp only [blk1, blk2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e100 e101 e110 e111
    simp only [blk1, blk2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e200 e201 e210 e211
    fin_cases i <;> fin_cases j <;> simp [hx.h02, hx.h03, hx.h12, hx.h13, hx.h20, hx.h21, hx.h30,
      hx.h31, hy.h02, hy.h03, hy.h12, hy.h13, hy.h20, hy.h21, hy.h30, hy.h31] <;> assumption
  have hP' : IsPGroup 3 (P.subgroupOf L) := hP3.comap_subtype
  have := isMulCommutative_of_jointly_injective (fun Q hQ => isMulCommutative_of_isPGroup_su2 hQ)
    (fun Q hQ => isMulCommutative_of_isPGroup_su2 hQ) f₁ f₂ hinj hP'
  apply hPn
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := this.is_comm.comm ⟨⟨a, hPL a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩
    ⟨⟨b, hPL b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
  exact Subtype.ext (congrArg (fun z => ((z : L) : SU4)) (congrArg Subtype.val h))

private def R : Subgroup SU4 :=
  (blockEmb3 K 2 3 3 ⟨0, by norm_num⟩ (by norm_num)).range

private structure Z31 (x : SU4) : Prop where
  h03 : mat x 0 3 = 0
  h13 : mat x 1 3 = 0
  h23 : mat x 2 3 = 0
  h30 : mat x 3 0 = 0
  h31 : mat x 3 1 = 0
  h32 : mat x 3 2 = 0

private theorem mat_blockEmb3 (A : Su K 2 3 3) :
    mat (blockEmb3 K 2 3 3 ⟨0, by norm_num⟩ (by norm_num) A) =
      blockMat 4 0 (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
  rfl

private theorem mem_R_iff {x : SU4} : x ∈ R ↔ Z31 x ∧ mat x 3 3 = 1 := by
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> (rw [mat_blockEmb3]; simp [blockMat_apply])
  · rintro ⟨hZ, h33⟩
    set A₀ : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => mat x i.castSucc j.castSucc with hA₀
    have hxA : mat x = blockMat 4 0 A₀ := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [blockMat_apply, hA₀, hZ.h03, hZ.h13, hZ.h23, hZ.h30, hZ.h31, hZ.h32, h33]
    have hdet : A₀.det = 1 := by
      rw [← det_blockMat (show 0 + 3 ≤ 4 by norm_num), ← hxA]
      exact det_mat x
    have hu : conjTr σ4 A₀ * A₀ = 1 := by
      apply blockMat_injective (show 0 + 3 ≤ 4 by norm_num) (F := K)
      rw [blockMat_mul (by norm_num), ← conjTr_blockMat, ← hxA, blockMat_one]
      exact conjTr_mat_mul x
    have hU : IsUnit (Matrix.det A₀) := by rw [hdet]; exact isUnit_one
    have hval : ((GeneralLinearGroup.mk'' A₀ hU : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A₀ :=
      rfl
    have hmem : GeneralLinearGroup.mk'' A₀ hU ∈ SUid σ4 3 :=
      ⟨by rw [hval]; exact hdet, by rw [hval]; exact hu⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply mat_injective
    rw [mat_blockEmb3, hxA]
    rfl

private theorem R_le_centralizer {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d)
    (h01 : d 0 = d 1) (h12 : d 1 = d 2) : R ≤ Subgroup.centralizer ({c} : Set SU4) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hd : ∀ (a : Fin 4) (j : Fin 3), a.val = 0 + j.val → d a = d 0 := by
    intro a j h
    have hj := j.2
    fin_cases a
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
    · simp at h
      omega
  apply mat_injective
  rw [mat_mul, mat_mul, hc, mat_blockEmb3]
  exact (diagonal_mul_blockMat d (d 0) hd _).symm

private theorem blockEmb3_inj :
    Function.Injective (blockEmb3 K 2 3 3 ⟨0, by norm_num⟩ (by norm_num)) :=
  blockEmb3_injective 3 _ _

private def eR : Su K 2 3 3 ≃* R := MonoidHom.ofInjective blockEmb3_inj

private theorem isQuasisimple_R : CFSG.IsQuasisimple R :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv eR
    (CFSG.GH74.L5U5.isQuasisimple_su (p := 2) (f := 3) card_K (by norm_num) (by norm_num))

private theorem card_R : Nat.card R = 16547328 :=
  (Nat.card_congr eR.toEquiv.symm).trans card_Su_three

private theorem eq_R_of_le {c : SU4} {L : Subgroup SU4}
    (hRC : R ≤ Subgroup.centralizer ({c} : Set SU4))
    (hsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set SU4))).IsSubnormal)
    (hperf : Group.IsPerfect L) (hLR : L ≤ R) (hL1 : L ≠ ⊥) : L = R := by
  have hsnR : (L.subgroupOf R).IsSubnormal := by
    have := hsn.comap (Subgroup.inclusion hRC)
    have h2 : (L.subgroupOf (Subgroup.centralizer ({c} : Set SU4))).comap
        (Subgroup.inclusion hRC) = L.subgroupOf R := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at this
  have hperfR : Group.IsPerfect (L.subgroupOf R) := by
    haveI := hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLR).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hne : L.subgroupOf R ≠ ⊥ := by
    intro h
    apply hL1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hLR hx⟩ : R) ∈ L.subgroupOf R := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have htop := eq_top_of_perfect_subnormal isQuasisimple_R hperfR hsnR hne
  refine le_antisymm hLR fun x hx => ?_
  have : (⟨x, hx⟩ : R) ∈ L.subgroupOf R := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

private theorem entry_zero_of_comm {v : Fin 4 → K} {Y : Matrix (Fin 4) (Fin 4) K}
    (h : diagonal v * Y = Y * diagonal v) {i j : Fin 4} (hij : v i ≠ v j) : Y i j = 0 := by
  have := congrFun (congrFun h i) j
  rw [diagonal_mul, mul_diagonal] at this
  have h2 : (v i - v j) * Y i j = 0 := by linear_combination this
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hij)

private theorem exists_mu3_elem : ∃ u : μ3, IsPrimitiveRoot ((u : Kˣ) : K) 3 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  refine ⟨⟨hu.unit, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hζ.pow_eq_one)
  · simpa using hζ

private def e1 (u : μ3) : SU4 := torusSU4 ![u, u ^ 2, 1]

private def e2 (u : μ3) : SU4 := torusSU4 ![u, 1, u ^ 2]

private theorem mat_e1 (u : μ3) :
    mat (e1 u) = diagonal ![((u : Kˣ) : K), ((u : Kˣ) : K) ^ 2, 1, 1] := by
  have h3 : (u : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp u.2
  have hmat : mat (e1 u) = diagonal fun k => (torusSnoc 3 (fun i =>
      ((![u, u ^ 2, 1] i : μ3) : Kˣ)) k : K) := coe_torusSU4 _
  rw [hmat]
  congr 1
  funext k
  fin_cases k
  · show ((torusSnoc 3 _ (Fin.castSucc 0) : Kˣ) : K) = _
    rw [torusSnoc_castSucc]
    rfl
  · show ((torusSnoc 3 _ (Fin.castSucc 1) : Kˣ) : K) = _
    rw [torusSnoc_castSucc]
    simp
  · show ((torusSnoc 3 _ (Fin.castSucc 2) : Kˣ) : K) = _
    rw [torusSnoc_castSucc]
    simp
  · show ((torusSnoc 3 _ (Fin.last 3) : Kˣ) : K) = _
    rw [torusSnoc_last, Fin.prod_univ_three]
    have hK3 : ((u : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    simp
    rw [← mul_inv, ← pow_succ, hK3, inv_one]

private theorem mat_e2 (u : μ3) :
    mat (e2 u) = diagonal ![((u : Kˣ) : K), 1, ((u : Kˣ) : K) ^ 2, 1] := by
  have h3 : (u : Kˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 _).mp u.2
  have hmat : mat (e2 u) = diagonal fun k => (torusSnoc 3 (fun i =>
      ((![u, 1, u ^ 2] i : μ3) : Kˣ)) k : K) := coe_torusSU4 _
  rw [hmat]
  congr 1
  funext k
  fin_cases k
  · show ((torusSnoc 3 _ (Fin.castSucc 0) : Kˣ) : K) = _
    rw [torusSnoc_castSucc]
    rfl
  · show ((torusSnoc 3 _ (Fin.castSucc 1) : Kˣ) : K) = _
    rw [torusSnoc_castSucc]
    simp
  · show ((torusSnoc 3 _ (Fin.castSucc 2) : Kˣ) : K) = _
    rw [torusSnoc_castSucc]
    simp
  · show ((torusSnoc 3 _ (Fin.last 3) : Kˣ) : K) = _
    rw [torusSnoc_last, Fin.prod_univ_three]
    have hK3 : ((u : Kˣ) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    simp
    rw [← mul_inv, ← pow_succ, hK3, inv_one]

private def p01 : SU4 := blockEmb2 K 2 3 3 ⟨0, by norm_num⟩ (CFSG.ClassicalInvolution.Phan.rotSU σ4)

private def p12 : SU4 := blockEmb2 K 2 3 3 ⟨1, by norm_num⟩ (CFSG.ClassicalInvolution.Phan.rotSU σ4)

private theorem mat_p01 : mat p01 = blockMat 4 0 CFSG.ClassicalInvolution.Phan.rotMat := rfl

private theorem mat_p12 : mat p12 = blockMat 4 1 CFSG.ClassicalInvolution.Phan.rotMat := rfl

private theorem e1_mem_R (u : μ3) : e1 u ∈ R := by
  rw [mem_R_iff]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [mat_e1]

private theorem e2_mem_R (u : μ3) : e2 u ∈ R := by
  rw [mem_R_iff]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [mat_e2]

private theorem p01_mem_R : p01 ∈ R := by
  rw [mem_R_iff]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [mat_p01, blockMat_apply]

private theorem p12_mem_R : p12 ∈ R := by
  rw [mem_R_iff]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [mat_p12, blockMat_apply]

private theorem schur_R {y : SU4} (hy : ∀ x ∈ R, x * y = y * x) :
    ∃ t s : K, mat y = diagonal ![t, t, t, s] := by
  obtain ⟨u, hu⟩ := exists_mu3_elem
  set ζ : K := ((u : Kˣ) : K) with hζ
  have hζ1 : ζ ≠ 1 := hu.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := hu.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hζ0 : ζ ≠ 0 := Units.ne_zero _
  have hζζ : ζ ≠ ζ ^ 2 := by
    intro h
    apply hζ1
    have : ζ * (ζ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hζ0)
  have c1 : diagonal ![ζ, ζ ^ 2, 1, 1] * mat y = mat y * diagonal ![ζ, ζ ^ 2, 1, 1] := by
    have := congrArg mat (hy _ (e1_mem_R u))
    rwa [mat_mul, mat_mul, mat_e1] at this
  have c2 : diagonal ![ζ, 1, ζ ^ 2, 1] * mat y = mat y * diagonal ![ζ, 1, ζ ^ 2, 1] := by
    have := congrArg mat (hy _ (e2_mem_R u))
    rwa [mat_mul, mat_mul, mat_e2] at this
  have y01 : mat y 0 1 = 0 := entry_zero_of_comm c1 (by simpa using hζζ)
  have y10 : mat y 1 0 = 0 := entry_zero_of_comm c1 (by simpa using hζζ.symm)
  have y02 : mat y 0 2 = 0 := entry_zero_of_comm c1 (by simpa using hζ1)
  have y20 : mat y 2 0 = 0 := entry_zero_of_comm c1 (by simpa using hζ1.symm)
  have y03 : mat y 0 3 = 0 := entry_zero_of_comm c1 (by simpa using hζ1)
  have y30 : mat y 3 0 = 0 := entry_zero_of_comm c1 (by simpa using hζ1.symm)
  have y12 : mat y 1 2 = 0 := entry_zero_of_comm c1 (by simpa using hζ2)
  have y21 : mat y 2 1 = 0 := entry_zero_of_comm c1 (by simpa using hζ2.symm)
  have y13 : mat y 1 3 = 0 := entry_zero_of_comm c1 (by simpa using hζ2)
  have y31 : mat y 3 1 = 0 := entry_zero_of_comm c1 (by simpa using hζ2.symm)
  have y23 : mat y 2 3 = 0 := entry_zero_of_comm c2 (by simpa using hζ2)
  have y32 : mat y 3 2 = 0 := entry_zero_of_comm c2 (by simpa using hζ2.symm)
  have h01 : mat y 0 0 = mat y 1 1 := by
    have := congrArg mat (hy _ p01_mem_R)
    rw [mat_mul, mat_mul, mat_p01] at this
    have h := congrFun (congrFun this 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, CFSG.ClassicalInvolution.Phan.rotMat,
      y01, y02, y03] at h
    exact h.symm
  have h12 : mat y 1 1 = mat y 2 2 := by
    have := congrArg mat (hy _ p12_mem_R)
    rw [mat_mul, mat_mul, mat_p12] at this
    have h := congrFun (congrFun this 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, CFSG.ClassicalInvolution.Phan.rotMat,
      y10, y12, y13, y20, y21, y23] at h
    exact h.symm
  refine ⟨mat y 0 0, mat y 3 3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y01, y02, y03, y10, y12, y13, y20, y21, y23, y30, y31, y32,
    ← h01, ← h12]

private theorem diag_of_schur {y : SU4} (hy : ∀ x ∈ R, x * y = y * x) (hy3 : y ^ 3 = 1) :
    ∃ t : K, mat y = diagonal ![t, t, t, 1] ∧ t ^ 3 = 1 := by
  obtain ⟨t, s, hts⟩ := schur_R hy
  have h3 : mat y ^ 3 = 1 := by rw [← mat_pow, hy3]; rfl
  rw [hts] at h3
  have hdiag : diagonal ![t, t, t, s] ^ 3 = diagonal ![t ^ 3, t ^ 3, t ^ 3, s ^ 3] := by
    rw [diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hdiag] at h3
  have ht3 : t ^ 3 = 1 := by simpa using congrFun (congrFun h3 0) 0
  have hdet := det_mat y
  rw [hts, det_diagonal, Fin.prod_univ_four] at hdet
  have hs : s = 1 := by
    have : t * t * t * s = 1 := by simpa using hdet
    calc s = t ^ 3 * s := by rw [ht3, one_mul]
      _ = t * t * t * s := by ring
      _ = 1 := this
  exact ⟨t, by rw [hts, hs], ht3⟩

private theorem pow_three_of_mem_center_R : ∀ z ∈ Subgroup.center R, z ^ 3 = 1 := by
  intro z hz
  have hy : ∀ x ∈ R, x * (z : SU4) = (z : SU4) * x := fun x hx =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x, hx⟩)
  obtain ⟨t, s, hts⟩ := schur_R hy
  have hzR := mem_R_iff.mp z.2
  have hs : s = 1 := by
    have h := hzR.2
    rw [hts] at h
    simpa using h
  have hdet := det_mat (z : SU4)
  rw [hts, det_diagonal, Fin.prod_univ_four, hs] at hdet
  have ht3 : t ^ 3 = 1 := by
    have : t * t * t * 1 = 1 := by simpa using hdet
    calc t ^ 3 = t * t * t * 1 := by ring
      _ = 1 := this
  apply Subtype.ext
  apply mat_injective
  rw [show ((z ^ 3 : R) : SU4) = (z : SU4) ^ 3 from rfl, mat_pow, hts, hs, diagonal_pow]
  change _ = (1 : Matrix (Fin 4) (Fin 4) K)
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [ht3]

private theorem card_le_three_of_le_centralizer_R {D : Subgroup SU4}
    (hD : D ≤ Subgroup.centralizer (R : Set SU4)) (hD3 : ∀ x ∈ D, x ^ 3 = 1) :
    Nat.card D ≤ 3 := by
  have hdiag : ∀ y : D, ∃ t : K, mat (y : SU4) = diagonal ![t, t, t, 1] ∧ t ^ 3 = 1 := by
    intro y
    refine diag_of_schur (fun x hx => ?_) (hD3 y y.2)
    exact (Subgroup.mem_centralizer_iff.mp (hD y.2) x hx)
  let g : D →* K :=
    { toFun := fun y => mat (y : SU4) 0 0
      map_one' := by simp [mat_one]
      map_mul' := fun y y' => by
        obtain ⟨t, ht, -⟩ := hdiag y
        obtain ⟨t', ht', -⟩ := hdiag y'
        rw [Subgroup.coe_mul, mat_mul, ht, ht', diagonal_mul_diagonal]
        simp }
  have hg3 : ∀ y : D, g y ^ 3 = 1 := by
    intro y
    obtain ⟨t, ht, ht3⟩ := hdiag y
    have : g y = t := by
      change mat (y : SU4) 0 0 = t
      rw [ht]
      simp
    rw [this]
    exact ht3
  let h : D →* μ3 := g.toHomUnits.codRestrict μ3 fun y => by
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, hg3, Units.val_one]
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : g y = 1 := by
      have := congrArg (fun z : μ3 => ((z : Kˣ) : K)) hy
      simpa [h] using this
    obtain ⟨t, ht, -⟩ := hdiag y
    have : t = 1 := by
      rw [← h1]
      change t = mat (y : SU4) 0 0
      rw [ht]
      simp
    apply Subtype.ext
    show (y : SU4) = 1
    apply mat_injective
    rw [ht, this, mat_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> rfl
  calc Nat.card D ≤ Nat.card μ3 := Nat.card_le_card_of_injective _ hinj
    _ = 3 := card_μ3

private theorem zero_of_mem_centralizer {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d)
    {x : SU4} (hx : x ∈ Subgroup.centralizer ({c} : Set SU4)) {i j : Fin 4} (hij : d i ≠ d j) :
    mat x i j = 0 := by
  have h2 := congrArg mat (Subgroup.mem_centralizer_singleton_iff.mp hx)
  rw [mat_mul, mat_mul, hc] at h2
  exact entry_zero_of_comm h2.symm hij

private theorem concl_of_nfA {c : SU4} {L : Subgroup SU4} (h : CompHyp c L) {d : Fin 4 → K}
    (hc : mat c = diagonal d) (h01 : d 0 = d 1) (h12 : d 1 = d 2) (h30 : d 3 ≠ d 0) :
    CompConcl L := by
  haveI := h.perf
  have hZ : ∀ x ∈ L, Z31 x := fun x hx => by
    have hxc := h.le hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact zero_of_mem_centralizer hc hxc (Ne.symm h30)
    · exact zero_of_mem_centralizer hc hxc (by rw [← h01]; exact Ne.symm h30)
    · exact zero_of_mem_centralizer hc hxc (by rw [← h12, ← h01]; exact Ne.symm h30)
    · exact zero_of_mem_centralizer hc hxc h30
    · exact zero_of_mem_centralizer hc hxc (by rw [← h01]; exact h30)
    · exact zero_of_mem_centralizer hc hxc (by rw [← h12, ← h01]; exact h30)
  have h33 : ∀ x ∈ L, mat x 3 3 = 1 :=
    perfect_mul_eq_one L (fun x => mat x 3 3) (by simp [mat_one]) (fun x hx y hy => by
      have := hZ x hx
      rw [mat_mul]
      simp [Matrix.mul_apply, Fin.sum_univ_four, this.h30, this.h31, this.h32])
  have hLR : L ≤ R := fun x hx => mem_R_iff.mpr ⟨hZ x hx, h33 x hx⟩
  have hL1 : L ≠ ⊥ := by
    intro hbot
    have hc1 : c = 1 := by
      have : c ∈ (⊥ : Subgroup SU4) := hbot ▸ h.mem
      exact Subgroup.mem_bot.mp this
    have := h.ord
    rw [hc1, orderOf_one] at this
    omega
  have hL : L = R := eq_R_of_le (R_le_centralizer hc h01 h12) h.sn h.perf hLR hL1
  subst hL
  refine ⟨?_, ?_, ?_⟩
  · rw [card_R]
    norm_num
  · exact aschbacherSolvableCore_eq_bot isQuasisimple_R pow_three_of_mem_center_R
  · intro D hD hDe
    exact card_le_three_of_le_centralizer_R hD hDe.2

private theorem false_of_nfB {c : SU4} {L : Subgroup SU4} (h : CompHyp c L) {d : Fin 4 → K}
    (hc : mat c = diagonal d) (h01 : d 0 = d 1) (h20 : d 2 ≠ d 0) (h30 : d 3 ≠ d 0) : False := by
  refine false_of_Z22 L h.perf (fun x hx => ?_) h.nonab
  have hxc := h.le hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zero_of_mem_centralizer hc hxc (Ne.symm h20)
  · exact zero_of_mem_centralizer hc hxc (Ne.symm h30)
  · exact zero_of_mem_centralizer hc hxc (by rw [← h01]; exact Ne.symm h20)
  · exact zero_of_mem_centralizer hc hxc (by rw [← h01]; exact Ne.symm h30)
  · exact zero_of_mem_centralizer hc hxc h20
  · exact zero_of_mem_centralizer hc hxc (by rw [← h01]; exact h20)
  · exact zero_of_mem_centralizer hc hxc h30
  · exact zero_of_mem_centralizer hc hxc (by rw [← h01]; exact h30)

private theorem core {c : SU4} {L : Subgroup SU4} (h : CompHyp c L) {d : Fin 4 → K}
    (hc : mat c = diagonal d) (h01 : d 0 = d 1) (h30 : d 3 ≠ d 0) : CompConcl L := by
  by_cases h20 : d 2 = d 0
  · exact concl_of_nfA h hc h01 (h20.symm ▸ h01.symm ▸ rfl) h30
  · exact (false_of_nfB h hc h01 h20 h30).elim

end U48Comp

theorem u48_component {c : SU4} (hc : orderOf c = 3) {L : Subgroup SU4}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set SU4))
    (hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set SU4))).IsSubnormal)
    (hLp : Group.IsPerfect L) (hcL : c ∈ L)
    (hP : ∃ P : Subgroup SU4, P ≤ L ∧ IsPGroup 3 P ∧ ¬ IsMulCommutative P)
    (hL : 7560 ≤ Nat.card L) :
    19 ∣ Nat.card L ∧ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 L = ⊥ ∧
      ∀ D : Subgroup SU4, D ≤ Subgroup.centralizer (L : Set SU4) →
        CFSG.Open.IsElemAbelian 3 D → Nat.card D ≤ 3 := by
  have _ := hL
  obtain ⟨e, d, hmat, h01, h30⟩ := U48Comp.exists_nf hc
  have h := (U48Comp.CompHyp.mk hc hLc hLsn hLp hcL hP).map e
  exact U48Comp.CompConcl.of_map e (U48Comp.core h hmat h01 h30)

end Component

end CFSG.RankThree.PartTwo.Sec19.SimsC198
