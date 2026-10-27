module

public import CFSG.RankThree.PartOne.K133.PerfectUnip
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.KF.ClsLift
public import CFSG.RankThree.SubgroupLists.CentralThreeLift

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG.Assembly.LowTwoRank Matrix Module
open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (hne : ∃ a b : H, a * b ≠ b * a) : Group.IsPerfect H := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hne
    apply hab
    have : ⁅a, b⁆ ∈ commutator H := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exact h

theorem scalar_eq_smul_one' {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] (r : K) :
    (Matrix.scalar n r : Matrix n n K) = r • (1 : Matrix n n K) := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem hom_perfect_pow_eq_one {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 ≤ p) {G : Type*} [Group G] [Group.IsPerfect G] (σ : G →* GL (Fin 3) K)
    (a : GL (Fin 3) K) (hcomm : ∀ y, σ y * a = a * σ y) (c : Kˣ)
    (hac : a ^ p = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hna : ∀ μ : Kˣ, a ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) μ) : ∀ y, σ y ^ p = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ p = (c : K) := by
    have hsurj : Function.Surjective (frobenius K p) :=
      Finite.surjective_of_injective (frobenius_inj K p)
    obtain ⟨μ, hμ⟩ := hsurj (c : K)
    exact ⟨μ, by simpa [frobenius_def] using hμ⟩
  set A : Matrix (Fin 3) (Fin 3) K := ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hA
  have hAp : A ^ p = (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hac
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [scalar_eq_smul_one'] at this
    exact this
  set N : Matrix (Fin 3) (Fin 3) K := A - μ • (1 : Matrix (Fin 3) (Fin 3) K) with hN
  have hNp : N ^ p = 0 := by
    have hc : Commute A (μ • (1 : Matrix (Fin 3) (Fin 3) K)) := (Commute.one_right A).smul_right μ
    have := sub_pow_char_of_commute p hc
    rw [hN, this, hAp, smul_pow, one_pow, hμ]
    simp
  have hN0 : N ≠ 0 := by
    intro h0
    have hAμ : A = μ • (1 : Matrix (Fin 3) (Fin 3) K) := sub_eq_zero.1 h0
    have hμ0 : μ ≠ 0 := by
      intro hμ0
      rw [hμ0, zero_smul] at hAμ
      have h1 : ((a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A = 1 := by
        rw [hA, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [hAμ, mul_zero] at h1
      exact zero_ne_one (congrFun (congrFun h1 0) 0)
    apply hna (Units.mk0 μ hμ0)
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_eq_smul_one']
    simpa [hA] using hAμ
  let e : Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Module.End K (Fin 3 → K) := Matrix.toLinAlgEquiv'
  let ρ : G →* Module.End K (Fin 3 → K) :=
    (e.toRingEquiv.toMonoidHom).comp ((Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp σ)
  have hρ : ∀ y, ρ y = e ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun y => rfl
  have hcommN : ∀ y, ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N =
      N * ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro y
    have h1 : ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A =
        A * ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) (hcomm y)
      simpa [hA] using this
    rw [hN, mul_sub, sub_mul, h1]
    simp
  have hnil : IsNilpotent (e N) := ⟨p, by rw [← map_pow, hNp, map_zero]⟩
  have hn0 : e N ≠ 0 := fun h => hN0 (e.injective (by rw [h, map_zero]))
  have hrcomm : ∀ y, ρ y * e N = e N * ρ y := fun y => by
    rw [hρ, ← map_mul, ← map_mul, hcommN y]
  have hfin : Module.finrank K (Fin 3 → K) = 3 := by simp
  have hkey := perfect_unipotent_of_nilpotent_three hfin ρ inferInstance hn0 hnil hrcomm
  intro y
  have h3 : ((((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0) := by
    have := hkey y
    rw [hρ] at this
    have h4 : e (((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0 := by
      simpa [map_sub, map_one] using this
    rw [← map_pow] at h4
    exact e.injective (by rw [h4, map_zero])
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  set E : Matrix (Fin 3) (Fin 3) K := ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1 with hE
  have hEy : ((σ y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + E := by rw [hE]; abel
  rw [hEy]
  have hEp : E ^ p = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, p = 3 + k := ⟨p - 3, by omega⟩
    rw [hk, pow_add, h3, zero_mul]
  have := add_pow_char_of_commute (x := (1 : Matrix (Fin 3) (Fin 3) K)) (y := E) p
    (Commute.one_left E)
  rw [this, hEp, one_pow]
  simp

theorem statedProj_three_no_config {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 ≤ p) (M : Subgroup (GL (Fin 3) K)) (x : StatedProj M) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (Kb : Subgroup (StatedProj M)) [IsSimpleGroup Kb] (hKn : ∃ a b : Kb, a * b ≠ b * a)
    (hcomm : ∀ k ∈ Kb, x * k = k * x) : False := by
  classical
  set Z : Subgroup M := (StatedScalars (Fin 3) K).subgroupOf M with hZ
  have hZc : Z ≤ Subgroup.center M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro m
    have hz' : (z : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := hz
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz' (m : GL (Fin 3) K))
  let mk : M →* StatedProj M := QuotientGroup.mk' Z
  have hKperf : Group.IsPerfect Kb := isPerfect_of_simple_nonabelian hKn
  set P₀ : Subgroup M := ⁅Kb.comap mk, Kb.comap mk⁆ with hP₀
  have hP₀perf : Group.IsPerfect P₀ := CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap hZc Kb
  have hP₀map : P₀.map mk = Kb := CFSG.RankThree.SubgroupLists.map_commutator_comap Kb
  have hP₀K : ∀ y ∈ P₀, mk y ∈ Kb := fun y hy => hP₀map ▸ Subgroup.mem_map_of_mem mk hy
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective x
  have hmka : mk a = x := ha
  have hapZ : a ^ p ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    change mk (a ^ p) = 1
    rw [map_pow, hmka, hxp]
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = ((a ^ p : M) : GL (Fin 3) K) :=
    hapZ
  have hna : ∀ μ : Kˣ, (a : GL (Fin 3) K) ≠ Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
    intro μ hμ
    apply hx1
    rw [← hmka]
    change ((a : M) : StatedProj M) = 1
    rw [QuotientGroup.eq_one_iff]
    change (a : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K
    exact ⟨μ, hμ.symm⟩
  have : Group.IsPerfect P₀ := hP₀perf
  have hcommA : ∀ y : P₀, (y : M) * a = a * (y : M) := by
    intro y
    have h := KFU.commute_of_central_commute (S := ↥P₀) (S' := ↥(Subgroup.zpowers a)) mk
      (by rw [QuotientGroup.ker_mk']; exact hZc) P₀.subtype (Subgroup.zpowers a).subtype
      (fun A B => by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 B.2
        have hB : mk (B : M) = x ^ k := by
          rw [← hk, map_zpow, hmka]
        change mk (A : M) * mk (B : M) = mk (B : M) * mk (A : M)
        rw [hB]
        exact (Commute.zpow_right (show Commute (mk (A : M)) x from (hcomm _ (hP₀K _ A.2)).symm) k).eq)
      y ⟨a, Subgroup.mem_zpowers a⟩
    exact h
  let σ : ↥P₀ →* GL (Fin 3) K := M.subtype.comp P₀.subtype
  have hpow := hom_perfect_pow_eq_one hp3 σ (a : GL (Fin 3) K)
    (fun y => by
      have := congrArg (fun m : M => (m : GL (Fin 3) K)) (hcommA y)
      simpa [σ] using this) c (by
        have : ((a ^ p : M) : GL (Fin 3) K) = (a : GL (Fin 3) K) ^ p := rfl
        rw [← this, hc]) hna
  have hKp : IsPGroup p Kb := by
    intro k
    have hk : (k : StatedProj M) ∈ P₀.map mk := by rw [hP₀map]; exact k.2
    obtain ⟨y, hy, hyk⟩ := hk
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    have : (y ^ p : M) = 1 := by
      apply Subtype.ext
      have := hpow ⟨y, hy⟩
      simpa [σ] using this
    show (k : StatedProj M) ^ p = 1
    rw [← hyk, ← map_pow, this, map_one]
  have : Finite Kb := inferInstance
  have hnil : Group.IsNilpotent Kb := hKp.isNilpotent
  have hsol : Group.IsSolvable Kb := inferInstance
  obtain ⟨u, v, huv⟩ := hKn
  exact huv ((IsSimpleGroup.comm_iff_isSolvable).2 hsol u v)

end CFSG.RankThree.PartOne.K133
