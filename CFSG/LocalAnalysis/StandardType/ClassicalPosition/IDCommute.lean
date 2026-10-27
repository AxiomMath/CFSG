module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergRank
public import CFSG.Assembly.Defs
public import CFSG.Open.StatedDefs
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private lemma idCom_lift_mul {U X ι F : Type} [Group U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X} {s s' : GL ι F} {b b' : X}
    (hs : IsGLLift j ψ s b) (hs' : IsGLLift j ψ s' b') :
    IsGLLift j ψ (s * s') (b' * b) := by
  intro u
  obtain ⟨u₂, hu₂j, hu₂ψ⟩ := hs' u
  obtain ⟨u₃, hu₃j, hu₃ψ⟩ := hs u₂
  refine ⟨u₃, ?_, ?_⟩
  · rw [hu₃j, hu₂j]; group
  · rw [← hu₃ψ, ← hu₂ψ]; group

private lemma idCom_lift_one {U X ι F : Type} [Group U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] (j : U →* GL ι F) (ψ : U →* X) :
    IsGLLift j ψ (1 : GL ι F) (1 : X) := by
  intro u
  exact ⟨u, by simp, by simp⟩

private lemma idCom_lift_inv {U X ι F : Type} [Group U] [Finite U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X} {s : GL ι F} {b : X}
    (hj : Function.Injective j) (hs : IsGLLift j ψ s b) :
    IsGLLift j ψ s⁻¹ b⁻¹ := by
  intro u
  let f : U → U := fun v => Classical.choose (hs v)
  have hf_j : ∀ v : U, j (f v) = s * j v * s⁻¹ := fun v => (Classical.choose_spec (hs v)).1
  have hf_ψ : ∀ v : U, b⁻¹ * ψ v * b = ψ (f v) := fun v => (Classical.choose_spec (hs v)).2
  have hf_inj : Function.Injective f := by
    intro v w hvw
    apply hj
    have h := congrArg j hvw
    rw [hf_j v, hf_j w] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  obtain ⟨u₀, hu₀⟩ := hf_surj u
  refine ⟨u₀, ?_, ?_⟩
  · have h := hf_j u₀
    rw [hu₀] at h
    rw [h]
    group
  · have h := hf_ψ u₀
    rw [hu₀] at h
    rw [← h]
    group

private lemma idCom_lift_pow {U X ι F : Type} [Group U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X} {s : GL ι F} {b : X}
    (n : ℕ) (hs : IsGLLift j ψ s b) : IsGLLift j ψ (s ^ n) (b ^ n) := by
  induction n with
  | zero => simpa using idCom_lift_one j ψ
  | succ n ih =>
    have h := idCom_lift_mul ih hs
    rw [show s ^ n * s = s ^ (n + 1) by rw [pow_succ],
        show b * b ^ n = b ^ (n + 1) by rw [pow_succ']] at h
    exact h

private lemma idCom_lift_of_mul_center {U X ι F : Type} [Group U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} {ψ : U →* X} {s s' : GL ι F} {b' : X}
    (hss' : s⁻¹ * s' ∈ Subgroup.center (GL ι F))
    (hs' : IsGLLift j ψ s' b') : IsGLLift j ψ s b' := by
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hs' u
  refine ⟨u', ?_, hu'ψ⟩
  have hz : ∀ g : GL ι F, g * (s⁻¹ * s') = (s⁻¹ * s') * g :=
    Subgroup.mem_center_iff.mp hss'
  have hzx : ∀ g : GL ι F, (s⁻¹ * s') * g * (s⁻¹ * s')⁻¹ = g := by
    intro g
    rw [← hz g]
    group
  rw [hu'j]
  calc s' * j u * s'⁻¹
      = s * ((s⁻¹ * s') * j u * (s⁻¹ * s')⁻¹) * s⁻¹ := by
        rw [show s' = s * (s⁻¹ * s') by group]
        group
    _ = s * j u * s⁻¹ := by rw [hzx]

private lemma idCom_pow_comm {G : Type} [Group G] {z : G}
    (hz : ∀ g : G, g * z = z * g) (k : ℕ) : ∀ g : G, g * z ^ k = z ^ k * g := by
  intro g
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc g * (z ^ k * z) = (g * z ^ k) * z := by group
      _ = (z ^ k * g) * z := by rw [ih]
      _ = z ^ k * (g * z) := by group
      _ = z ^ k * (z * g) := by rw [hz g]
      _ = (z ^ k * z) * g := by group

private lemma idCom_pow_mul {G : Type} [Group G] {s t z : G}
    (hz : ∀ g : G, g * z = z * g) (h : s * t = z * (t * s)) (k : ℕ) :
    s ^ k * t = z ^ k * (t * s ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc s ^ (k + 1) * t = s * (s ^ k * t) := by rw [pow_succ']; group
      _ = s * (z ^ k * (t * s ^ k)) := by rw [ih]
      _ = z ^ k * (s * (t * s ^ k)) := by
        calc s * (z ^ k * (t * s ^ k))
            = (s * z ^ k) * (t * s ^ k) := by group
          _ = (z ^ k * s) * (t * s ^ k) := by rw [idCom_pow_comm hz k s]
          _ = z ^ k * (s * (t * s ^ k)) := by group
      _ = z ^ k * ((s * t) * s ^ k) := by group
      _ = z ^ k * ((z * (t * s)) * s ^ k) := by rw [h]
      _ = z ^ (k + 1) * (t * s ^ (k + 1)) := by rw [pow_succ, pow_succ']; group

private lemma idCom_conjTr_smul {F : Type} [Field F] (σ : F ≃+* F) {n : ℕ} (c : F)
    (A : Matrix (Fin n) (Fin n) F) :
    Unitary.conjTr σ (c • A) = σ c • Unitary.conjTr σ A := by
  ext i j
  simp [Unitary.conjTr, Matrix.map_apply]

private lemma idCom_unitary_mul {F : Type} [Field F] (σ : F ≃+* F) {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (hA : Unitary.conjTr σ A * Unitary.antidiag n * A = Unitary.antidiag n)
    (hB : Unitary.conjTr σ B * Unitary.antidiag n * B = Unitary.antidiag n) :
    Unitary.conjTr σ (A * B) * Unitary.antidiag n * (A * B) = Unitary.antidiag n := by
  rw [Unitary.conjTr_mul]
  calc Unitary.conjTr σ B * Unitary.conjTr σ A * Unitary.antidiag n * (A * B)
      = Unitary.conjTr σ B * (Unitary.conjTr σ A * Unitary.antidiag n * A) * B := by
        simp only [Matrix.mul_assoc]
    _ = Unitary.conjTr σ B * Unitary.antidiag n * B := by rw [hA]
    _ = Unitary.antidiag n := hB

private theorem idCom_core {K : Type} [Field K] [Finite K] {N p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {U X : Type} [Group U] [Finite U] [Group X]
    (j : U →* GL (Fin N) K) (hj : Function.Injective j) (ψ : U →* X)
    {B₁ : Subgroup X} (hB₁pow : ∀ b ∈ B₁, b ^ p = 1)
    (hB₁comm : ∀ b ∈ B₁, ∀ b' ∈ B₁, b * b' = b' * b)
    (hex : ∀ b ∈ B₁, ∃ s, IsGLLift j ψ s b)
    (huniq : ∀ b s s', IsGLLift j ψ s b → IsGLLift j ψ s' b →
      ∃ c : K, ((s'⁻¹ * s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        Matrix.scalar (Fin N) c)
    (h4 : p ^ 4 ≤ Nat.card B₁)
    (hz : ∀ b ∈ B₁, ∀ b' ∈ B₁, ∀ s s', IsGLLift j ψ s b → IsGLLift j ψ s' b' →
      ∀ ζ : K, ζ ≠ 1 → ζ ^ p = 1 →
        ((s * s' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          Matrix.scalar (Fin N) ζ *
            ((s' * s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) →
        B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧ p ^ (N - 3) ≤ Nat.card B₁)
    (hN : 0 < N)
    {b b'} (hb : b ∈ B₁) (hb' : b' ∈ B₁) {s s'} (hs : IsGLLift j ψ s b)
    (hs' : IsGLLift j ψ s' b') : Commute s s' := by
  rw [commute_iff_eq]
  by_contra hnc
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let E : Subgroup (GL (Fin N) K) :=
    { carrier := {s | ∃ b ∈ B₁, IsGLLift j ψ s b}
      one_mem' := by exact ⟨1, B₁.one_mem, idCom_lift_one j ψ⟩
      mul_mem' := by
        rintro a b ⟨ba, hba, ha⟩ ⟨bb, hbb, hb⟩
        exact ⟨bb * ba, B₁.mul_mem hbb hba, idCom_lift_mul ha hb⟩
      inv_mem' := by
        rintro a ⟨ba, hba, ha⟩
        exact ⟨ba⁻¹, B₁.inv_mem hba, idCom_lift_inv hj ha⟩ }
  have hE : ∀ s : GL (Fin N) K, s ∈ E ↔ ∃ b ∈ B₁, IsGLLift j ψ s b := fun _ => Iff.rfl
  have hlift_ss' : IsGLLift j ψ (s * s') (b' * b) := idCom_lift_mul hs hs'
  have hlift_s's : IsGLLift j ψ (s' * s) (b * b') := idCom_lift_mul hs' hs
  rw [hB₁comm b hb b' hb'] at hlift_s's
  obtain ⟨c, hc⟩ := huniq (b' * b) (s * s') (s' * s) hlift_ss' hlift_s's
  let z : GL (Fin N) K := (s' * s)⁻¹ * (s * s')
  have hzmat : (z : Matrix (Fin N) (Fin N) K) = Matrix.scalar (Fin N) c := hc
  have hzcenter : z ∈ Subgroup.center (GL (Fin N) K) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c, hzmat.symm⟩
  have hzcomm : ∀ g : GL (Fin N) K, g * z = z * g := Subgroup.mem_center_iff.mp hzcenter
  have hrel_gl : s * s' = z * (s' * s) := by
    rw [← hzcomm (s' * s)]
    change s * s' = (s' * s) * ((s' * s)⁻¹ * (s * s'))
    group
  have hlift_pow : IsGLLift j ψ (s ^ p) (b ^ p) := idCom_lift_pow p hs
  rw [hB₁pow b hb] at hlift_pow
  obtain ⟨d, hd⟩ := huniq (1 : X) (s ^ p) (1 : GL (Fin N) K) hlift_pow
    (idCom_lift_one j ψ)
  have hd' : ((s ^ p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = Matrix.scalar (Fin N) d := by
    simpa using hd
  have hsp_center : s ^ p ∈ Subgroup.center (GL (Fin N) K) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨d, hd'.symm⟩
  have hsp_comm : ∀ g : GL (Fin N) K, g * s ^ p = s ^ p * g :=
    Subgroup.mem_center_iff.mp hsp_center
  have hc_ne_one : c ≠ 1 := by
    intro hc1
    have hz1 : z = 1 := by
      apply Units.ext
      rw [hzmat, hc1, map_one, Units.val_one]
    exact hnc (by rw [hrel_gl, hz1, one_mul])
  have hcp : c ^ p = 1 := by
    have hzp : z ^ p = 1 := by
      have h := idCom_pow_mul hzcomm hrel_gl p
      have hcomm_sp : s ^ p * s' = s' * s ^ p := (hsp_comm s').symm
      rw [hcomm_sp] at h
      exact mul_right_cancel (a := z ^ p) (b := s' * s ^ p) (c := 1)
        (by rw [one_mul, ← h])
    have hmat : (z ^ p : Matrix (Fin N) (Fin N) K) = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg (fun x : GL (Fin N) K => (x : Matrix (Fin N) (Fin N) K)) hzp
    have hmat2 : (Matrix.scalar (Fin N) c) ^ p = 1 := by
      calc (Matrix.scalar (Fin N) c) ^ p
          = ((z : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) ^ p := by rw [hzmat]
        _ = ((z ^ p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
              rw [Units.val_pow_eq_pow_val]
        _ = 1 := hmat
    have hmat3 : Matrix.scalar (Fin N) (c ^ p) = 1 := by rw [map_pow]; exact hmat2
    exact Matrix.scalar_inj.mp (by rw [hmat3, map_one])
  have hrel_mat : ((s * s' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      Matrix.scalar (Fin N) c * ((s' * s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
    rw [hrel_gl, Units.val_mul, hzmat]
  have hzconcl := hz b hb b' hb' s s' hs hs' c hc_ne_one hcp hrel_mat
  have hE_pow : ∀ a ∈ E, a ^ p ∈ Subgroup.center (GL (Fin N) K) := by
    intro a ha
    obtain ⟨ba, hba, hla⟩ := (hE a).mp ha
    have h1 : IsGLLift j ψ (a ^ p) (ba ^ p) := idCom_lift_pow p hla
    rw [hB₁pow ba hba] at h1
    obtain ⟨d, hd⟩ := huniq (1 : X) (a ^ p) (1 : GL (Fin N) K) h1 (idCom_lift_one j ψ)
    have hd' : ((a ^ p : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        Matrix.scalar (Fin N) d := by simpa using hd
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨d, hd'.symm⟩
  have hE_comm :
      ∀ a ∈ E, ∀ b ∈ E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (GL (Fin N) K) := by
    intro a ha b hb
    obtain ⟨ba, hba, hla⟩ := (hE a).mp ha
    obtain ⟨bb, hbb, hlb⟩ := (hE b).mp hb
    have hab : IsGLLift j ψ (a * b) (bb * ba) := idCom_lift_mul hla hlb
    have hba' : IsGLLift j ψ (b * a) (ba * bb) := idCom_lift_mul hlb hla
    rw [hB₁comm ba hba bb hbb] at hba'
    obtain ⟨c', hc'⟩ := huniq (bb * ba) (a * b) (b * a) hab hba'
    have hw_center :
        ((b * a)⁻¹ * (a * b) : GL (Fin N) K) ∈ Subgroup.center (GL (Fin N) K) :=
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨c', hc'.symm⟩
    have hw_comm : ∀ g : GL (Fin N) K,
        g * ((b * a)⁻¹ * (a * b)) = ((b * a)⁻¹ * (a * b)) * g :=
      Subgroup.mem_center_iff.mp hw_center
    have heq : a * b * a⁻¹ * b⁻¹ = ((b * a)⁻¹ * (a * b) : GL (Fin N) K) := by
      calc a * b * a⁻¹ * b⁻¹ = (b * a) * ((b * a)⁻¹ * (a * b)) * (b * a)⁻¹ := by group
        _ = ((b * a)⁻¹ * (a * b)) := by rw [hw_comm (b * a)]; group
    rw [heq]
    exact hw_center
  have hnc' : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a :=
    ⟨s, (hE s).mpr ⟨b, hb, hs⟩, s', (hE s').mpr ⟨b', hb', hs'⟩, hnc⟩
  obtain ⟨hpdvd, hpdle⟩ := dvd_and_card_le_of_not_commute_lifts hp2 hpK E hE_pow hE_comm hnc'
  have hcount : Nat.card B₁ ≤ Nat.card (E ⧸ (Subgroup.center (GL (Fin N) K)).subgroupOf E) := by
    let pick : B₁ → E := fun x =>
      ⟨Classical.choose (hex x.1 x.2),
        (hE (Classical.choose (hex x.1 x.2))).mpr
          ⟨x.1, x.2, Classical.choose_spec (hex x.1 x.2)⟩⟩
    let f : B₁ → E ⧸ (Subgroup.center (GL (Fin N) K)).subgroupOf E :=
      fun x => QuotientGroup.mk (pick x)
    have hf : Function.Injective f := by
      intro x y hxy
      change QuotientGroup.mk (pick x) = QuotientGroup.mk (pick y) at hxy
      have hmem : (pick x)⁻¹ * (pick y) ∈ (Subgroup.center (GL (Fin N) K)).subgroupOf E :=
        QuotientGroup.eq.mp hxy
      have hcen : ((pick x : GL (Fin N) K)⁻¹ * (pick y : GL (Fin N) K)) ∈
          Subgroup.center (GL (Fin N) K) := by
        simpa using (Subgroup.mem_subgroupOf.mp hmem)
      have hx_lift : IsGLLift j ψ (pick x : GL (Fin N) K) x.1 :=
        Classical.choose_spec (hex x.1 x.2)
      have hy_lift : IsGLLift j ψ (pick y : GL (Fin N) K) y.1 :=
        Classical.choose_spec (hex y.1 y.2)
      have hx_lift_y : IsGLLift j ψ (pick x : GL (Fin N) K) y.1 :=
        idCom_lift_of_mul_center hcen hy_lift
      have hceq : ∀ u : U, y.1⁻¹ * ψ u * y.1 = x.1⁻¹ * ψ u * x.1 := by
        intro u
        obtain ⟨u₁, hu₁j, hu₁ψ⟩ := hx_lift u
        obtain ⟨u₂, hu₂j, hu₂ψ⟩ := hx_lift_y u
        have huu : u₁ = u₂ := hj (by rw [hu₁j, hu₂j])
        rw [← huu] at hu₂ψ
        rw [hu₂ψ, hu₁ψ]
      have hcen_x : x.1 * y.1⁻¹ ∈ Subgroup.centralizer (ψ.range : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨u, rfl⟩ := hh
        have h := hceq u
        calc ψ u * (x.1 * y.1⁻¹)
            = x.1 * (x.1⁻¹ * ψ u * x.1) * y.1⁻¹ := by group
          _ = x.1 * (y.1⁻¹ * ψ u * y.1) * y.1⁻¹ := by rw [h]
          _ = (x.1 * y.1⁻¹) * ψ u := by group
      have hmemB : x.1 * y.1⁻¹ ∈ B₁ := B₁.mul_mem x.2 (B₁.inv_mem y.2)
      have hmem_all : x.1 * y.1⁻¹ ∈ B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) :=
        Subgroup.mem_inf.mpr ⟨hmemB, hcen_x⟩
      have hone : x.1 * y.1⁻¹ = 1 := by
        have h := hmem_all
        rw [hzconcl.1] at h
        exact Subgroup.mem_bot.mp h
      exact Subtype.ext (mul_right_cancel (by rw [hone, mul_inv_cancel]))
    exact Nat.card_le_card_of_injective f hf
  have hpprime : p.Prime := Fact.out
  have hp1 : 1 < p := hpprime.one_lt
  have hle : p ^ (N - 3) ≤ p ^ (N / p + 1) := le_trans hzconcl.2 (le_trans hcount hpdle)
  have hN3 : N - 3 ≤ N / p + 1 := (Nat.pow_le_pow_iff_right hp1).mp hle
  have h4le : p ^ 4 ≤ p ^ (N / p + 1) := le_trans h4 (le_trans hcount hpdle)
  have h4' : 4 ≤ N / p + 1 := (Nat.pow_le_pow_iff_right hp1).mp h4le
  have h3 : 3 ≤ N / p := by omega
  obtain ⟨m, rfl⟩ := hpdvd
  rw [Nat.mul_div_right m hpprime.pos] at hN3 h3
  have hp3 : 3 ≤ p := by
    have := hpprime.two_le
    omega
  have hpm_ge : 3 ≤ p * m := by nlinarith [hp3, h3]
  have hpm : p * m ≤ m + 4 := by omega
  nlinarith [hpm, hp3, h3]

theorem isGLLift_commute_PSL (m f : ℕ) {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hadm : StatedLieAdmissible .PSL (m + 1) 2 f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B₁ : Subgroup X}
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b)
    (hab : IsElemAbelian p B₁) (h4 : p ^ 4 ≤ Nat.card B₁)
    (hHN : p ∣ 2 ^ f - 1 →
      B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧ p ^ ((m + 1) - 3) ≤ Nat.card B₁)
    {b b' : X} (hb : b ∈ B₁) (hb' : b' ∈ B₁) {s s' : GL (Fin (m + 1)) (GaloisField 2 f)}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hs' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b') :
    Commute s s' := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcomm, hpow⟩ := hab
  have hB₁pow : ∀ b ∈ B₁, b ^ p = 1 := hpow
  have hB₁comm : ∀ b ∈ B₁, ∀ b' ∈ B₁, b * b' = b' * b := by
    intro b hb b' hb'
    exact congrArg (fun x : ↥B₁ => (x : X))
      (isMulCommutative_iff.mp hcomm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hpK : (p : GaloisField 2 f) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff (GaloisField 2 f) 2 p] at h0
    have hpe : p = 2 := (Nat.Prime.dvd_iff_eq hp (by decide : (2 : ℕ) ≠ 1)).mp h0
    exact hp2 hpe
  have hex : ∀ b ∈ B₁, ∃ s, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b := by
    intro b hb
    exact exists_isGLLift_PSL m (GaloisField 2 f) ψ hψ (hB₁N hb) (hB₁ b hb)
  have huniq : ∀ b s s', IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b →
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b → ∃ c : GaloisField 2 f,
        ((s'⁻¹ * s : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
          Matrix.scalar (Fin (m + 1)) c := by
    intro b s s' hs hs'
    exact isGLLift_unique_PSL m (GaloisField 2 f) ψ hψ hs hs'
  have hN : 0 < m + 1 := Nat.succ_pos m
  have hz : ∀ b ∈ B₁, ∀ b' ∈ B₁, ∀ s s',
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b →
      IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b' →
      ∀ ζ : GaloisField 2 f, ζ ≠ 1 → ζ ^ p = 1 →
      ((s * s' : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
        Matrix.scalar (Fin (m + 1)) ζ *
          ((s' * s : GL (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) →
      B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧
        p ^ ((m + 1) - 3) ≤ Nat.card B₁ := by
    intro b hb b' hb' s s' hs hs' ζ hζ hζpow _
    apply hHN
    have hf : f ≠ 0 := by have := hadm.2.1; omega
    have hζne : ζ ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hζpow
      exact zero_ne_one hζpow
    let u : (GaloisField 2 f)ˣ := Units.mk0 ζ hζne
    have hu_pow : u ^ p = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0, hζpow]
    have hu_ne : u ≠ 1 := by
      intro h
      apply hζ
      have := congrArg (fun x : (GaloisField 2 f)ˣ => (x : GaloisField 2 f)) h
      simpa [u] using this
    have horder : orderOf u = p := orderOf_eq_prime hu_pow hu_ne
    have hdvd : orderOf u ∣ Nat.card ((GaloisField 2 f)ˣ) := orderOf_dvd_natCard u
    have hcard : Nat.card ((GaloisField 2 f)ˣ) = 2 ^ f - 1 := by
      rw [Nat.card_units, GaloisField.card 2 f hf]
    rw [horder, hcard] at hdvd
    exact hdvd
  exact idCom_core (K := GaloisField 2 f) (N := m + 1) (p := p) hp2 hpK
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective ψ
    hB₁pow hB₁comm hex huniq h4 hz hN hb hb' hs hs'

theorem isGLLift_commute_PSU {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) (hadm : StatedLieAdmissible .PSU n 2 f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B₁ : Subgroup X}
    (hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X))
    (hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b) (hab : IsElemAbelian p B₁)
    (h4 : p ^ 4 ≤ Nat.card B₁)
    (hHN : p ∣ 2 ^ f + 1 →
      B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧ p ^ (n - 3) ≤ Nat.card B₁)
    {b b' : X} (hb : b ∈ B₁) (hb' : b' ∈ B₁) {s s' : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b)
    (hs' : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s' b')
    :
    Commute s s' := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcomm, hpow⟩ := hab
  have hB₁pow : ∀ b ∈ B₁, b ^ p = 1 := hpow
  have hB₁comm : ∀ b ∈ B₁, ∀ b' ∈ B₁, b * b' = b' * b := by
    intro b hb b' hb'
    exact congrArg (fun x : ↥B₁ => (x : X))
      (isMulCommutative_iff.mp hcomm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hpK : (p : F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F 2 p] at h0
    have hpe : p = 2 := (Nat.Prime.dvd_iff_eq hp (by decide : (2 : ℕ) ≠ 1)).mp h0
    exact hp2 hpe
  have hn : 3 ≤ n := hadm.2.2.1
  have hex : ∀ b ∈ B₁,
      ∃ s, IsGLLift
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b := by
    intro b hb
    obtain ⟨s, _, hslift⟩ := exists_isGLLift_PSU hc n hn ψ hψ (hB₁N hb) (hB₁ b hb)
    exact ⟨s, hslift⟩
  have huniq : ∀ b s s',
      IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b →
      IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s' b →
      ∃ c : F, ((s'⁻¹ * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Matrix.scalar (Fin n) c := by
    intro b s s' hs hs'
    exact isGLLift_unique_PSU hc n ψ hψ hs hs'
  have hN : 0 < n := by omega
  have hz : ∀ b ∈ B₁, ∀ b' ∈ B₁, ∀ s s',
      IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s b →
      IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype ψ s' b' →
      ∀ ζ : F, ζ ≠ 1 → ζ ^ p = 1 →
      ((s * s' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Matrix.scalar (Fin n) ζ * ((s' * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) →
      B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧ p ^ (n - 3) ≤ Nat.card B₁ := by
    intro b hb b' hb' s s' hs hs' ζ hζ hζpow hrel
    apply hHN
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    let σ : F ≃+* F := CFSG.LieType.BorelTits.unitaryInvolution F 2 f
    obtain ⟨s₀, hs₀unit, hs₀⟩ := exists_isGLLift_PSU hc n hn ψ hψ (hB₁N hb) (hB₁ b hb)
    obtain ⟨s₀', hs₀'unit, hs₀'⟩ := exists_isGLLift_PSU hc n hn ψ hψ (hB₁N hb') (hB₁ b' hb')
    obtain ⟨c₁, hc₁⟩ := huniq b s s₀ hs hs₀
    obtain ⟨c₂, hc₂⟩ := huniq b' s' s₀' hs' hs₀'
    have hsc₁ : (s : Matrix (Fin n) (Fin n) F) = c₁ • (s₀ : Matrix (Fin n) (Fin n) F) := by
      calc (s : Matrix (Fin n) (Fin n) F)
          = (s₀ : Matrix (Fin n) (Fin n) F) *
              ((s₀⁻¹ * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
            rw [← Units.val_mul]
            congr 1
            group
        _ = (s₀ : Matrix (Fin n) (Fin n) F) * Matrix.scalar (Fin n) c₁ := by rw [hc₁]
        _ = c₁ • (s₀ : Matrix (Fin n) (Fin n) F) := by
            rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
    have hsc₂ : (s' : Matrix (Fin n) (Fin n) F) = c₂ • (s₀' : Matrix (Fin n) (Fin n) F) := by
      calc (s' : Matrix (Fin n) (Fin n) F)
          = (s₀' : Matrix (Fin n) (Fin n) F) *
              ((s₀'⁻¹ * s' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
            rw [← Units.val_mul]
            congr 1
            group
        _ = (s₀' : Matrix (Fin n) (Fin n) F) * Matrix.scalar (Fin n) c₂ := by rw [hc₂]
        _ = c₂ • (s₀' : Matrix (Fin n) (Fin n) F) := by
            rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
    have hc₁ne : c₁ ≠ 0 := by
      intro h0
      have hunit : IsUnit (((s₀⁻¹ * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
        ⟨s₀⁻¹ * s, rfl⟩
      rw [hc₁, h0, map_zero] at hunit
      exact IsUnit.ne_zero hunit rfl
    have hc₂ne : c₂ ≠ 0 := by
      intro h0
      have hunit : IsUnit (((s₀'⁻¹ * s' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
        ⟨s₀'⁻¹ * s', rfl⟩
      rw [hc₂, h0, map_zero] at hunit
      exact IsUnit.ne_zero hunit rfl
    have hne : c₁ * c₂ ≠ 0 := mul_ne_zero hc₁ne hc₂ne
    have hrel_smul : ((s * s' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ζ • ((s' * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [hrel, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have hss' : ((s * s' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (c₁ * c₂) • ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [Units.val_mul, hsc₁, hsc₂, Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hs's : ((s' * s : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (c₂ * c₁) • ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [Units.val_mul, hsc₂, hsc₁, Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hbase : (c₁ * c₂) • ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (ζ * (c₁ * c₂)) • ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      have h := hrel_smul
      rw [hss', hs's] at h
      rw [smul_smul] at h
      rwa [show ζ * (c₂ * c₁) = ζ * (c₁ * c₂) by rw [mul_comm c₂ c₁]] at h
    have hXY : ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ζ • ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      have h' : (c₁ * c₂) • ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          (c₁ * c₂) • (ζ • ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        rw [smul_smul, mul_comm (c₁ * c₂) ζ]
        exact hbase
      exact (smul_right_inj hne).mp h'
    have hX : Unitary.conjTr σ ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Unitary.antidiag n * ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Unitary.antidiag n := by
      change Unitary.conjTr σ
          ((s₀ : Matrix (Fin n) (Fin n) F) * (s₀' : Matrix (Fin n) (Fin n) F)) *
          Unitary.antidiag n *
          ((s₀ : Matrix (Fin n) (Fin n) F) * (s₀' : Matrix (Fin n) (Fin n) F)) =
          Unitary.antidiag n
      exact idCom_unitary_mul σ hs₀unit hs₀'unit
    have hY : Unitary.conjTr σ ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Unitary.antidiag n * ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        Unitary.antidiag n := by
      change Unitary.conjTr σ
          ((s₀' : Matrix (Fin n) (Fin n) F) * (s₀ : Matrix (Fin n) (Fin n) F)) *
          Unitary.antidiag n *
          ((s₀' : Matrix (Fin n) (Fin n) F) * (s₀ : Matrix (Fin n) (Fin n) F)) =
          Unitary.antidiag n
      exact idCom_unitary_mul σ hs₀'unit hs₀unit
    have hanti : (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) =
        (σ ζ * ζ) • Unitary.antidiag n := by
      have hconj : Unitary.conjTr σ ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          σ ζ • Unitary.conjTr σ ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        rw [hXY]
        exact idCom_conjTr_smul σ ζ ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      calc Unitary.antidiag n
          = Unitary.conjTr σ ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              Unitary.antidiag n *
              ((s₀ * s₀' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := hX.symm
        _ = (σ ζ •
              Unitary.conjTr σ ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
              Unitary.antidiag n *
              (ζ • ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
              rw [hconj, hXY]
        _ = (σ ζ * ζ) • (Unitary.conjTr σ
              ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              Unitary.antidiag n *
              ((s₀' * s₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
              simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
              rw [mul_comm ζ (σ ζ)]
        _ = (σ ζ * ζ) • Unitary.antidiag n := by rw [hY]
    have hsigma : σ ζ * ζ = 1 := by
      have hn0 : 0 < n := by omega
      let i0 : Fin n := ⟨0, hn0⟩
      let j0 : Fin n := i0.rev
      have hdiag : (Unitary.antidiag n : Matrix (Fin n) (Fin n) F) i0 j0 = 1 := by
        simp [Unitary.antidiag, j0]
      have hentry : (1 : F) = σ ζ * ζ := by
        have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i0 j0) hanti
        simpa [Matrix.smul_apply, hdiag] using h
      exact hentry.symm
    have hzeta_pow : ζ ^ (2 ^ f + 1) = 1 := by
      have hsig : σ ζ = ζ ^ 2 ^ f := CFSG.LieType.BorelTits.unitaryInvolution_apply F 2 f ζ
      have h := hsigma
      rw [hsig] at h
      rw [pow_succ]
      exact h
    have hζne : ζ ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hζpow
      exact zero_ne_one hζpow
    let u : Fˣ := Units.mk0 ζ hζne
    have hu_pow : u ^ p = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0, hζpow]
    have hu_ne : u ≠ 1 := by
      intro h
      apply hζ
      have := congrArg (fun x : Fˣ => (x : F)) h
      simpa [u] using this
    have horder : orderOf u = p := orderOf_eq_prime hu_pow hu_ne
    have hu_pow_n : u ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0, hzeta_pow]
    have hdvd : orderOf u ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hu_pow_n
    rwa [horder] at hdvd
  exact idCom_core (K := F) (N := n) (p := p) hp2 hpK
    (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
    (Subgroup.subtype_injective _) ψ hB₁pow hB₁comm hex huniq h4 hz hN hb hb' hs hs'

end CFSG.StandardType.ClassicalPosition
