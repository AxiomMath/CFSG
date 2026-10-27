module

public import CFSG.Quasithin.Background.HM22RowAbs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1_scl_scal_mul (S : s16c4v1_Sit D V L hV) {m m' : G}
    {c c' : S.F.K} (hm' : m' ∈ D.M) (hc : s16c4v1_Scal S m c)
    (hc' : s16c4v1_Scal S m' c') : s16c4v1_Scal S (m * m') (c * c') := by
  intro v hv
  have hv' : m' * v * m'⁻¹ ∈ V := s16c4v1_conj_mem S hm' hv
  have h1 : (m * m') * v * (m * m')⁻¹ = m * (m' * v * m'⁻¹) * m⁻¹ := by group
  rw [h1, hc _ hv', hc' v hv, smul_smul]

private theorem s16c4v1_scl_scal_pow (S : s16c4v1_Sit D V L hV) {z : G} {ω : S.F.K}
    (hz : s16c4v1_ScalarOf S z ω) (n : ℕ) : s16c4v1_Scal S (z ^ n) (ω ^ n) := by
  induction n with
  | zero =>
    intro v hv
    simp
  | succ n ih =>
    have h := s16c4v1_scl_scal_mul S hz.1 ih hz.2.2
    simpa [pow_succ] using h

private theorem s16c4v1_scl_cube_pow_three {K : Type} [Field K] {a : K}
    (h : a ^ 2 + a + 1 = 0) : a ^ 3 = 1 := by
  have hfac : a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by ring
  rw [h, mul_zero] at hfac
  exact sub_eq_zero.mp hfac

private theorem s16c4v1_scl_cube_sq_cube {K : Type} [Field K] {a : K}
    (h : a ^ 2 + a + 1 = 0) : (a ^ 2) ^ 2 + a ^ 2 + 1 = 0 := by
  have ha3 : a ^ 3 = 1 := s16c4v1_scl_cube_pow_three h
  have ha4 : a ^ 4 = a := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ha3, one_mul]
  calc (a ^ 2) ^ 2 + a ^ 2 + 1 = a ^ 4 + a ^ 2 + 1 := by ring
    _ = a + a ^ 2 + 1 := by rw [ha4]
    _ = 0 := by linear_combination h

theorem s16c4v1_scalar_cube (S : s16c4v1_Sit D V L hV) {z : G} {ω : S.F.K}
    (hz : s16c4v1_ScalarOf S z ω) : ω ^ 2 + ω + 1 = 0 := by
  have hω0 : ω ≠ 0 := by
    intro h0
    have hle : V ≤ v1Sub D.M ⊥ V hV L := by
      intro v hv
      have hzv : z * v * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 hv
      have hvec : s16c4v1_vec S (z * v * z⁻¹) = 0 := by
        rw [hz.2.2 v hv, h0, zero_smul]
      have hmem : z * v * z⁻¹ ∈ v1Sub D.M ⊥ V hV L :=
        (s16c4v1_vec_eq_zero_iff S hzv).1 hvec
      have hvz : z⁻¹ * (z * v * z⁻¹) * z ∈ v1Sub D.M ⊥ V hV L := by
        simpa using s16c4v1_conj_mem_v1 S (D.M.inv_mem hz.1) hmem
      have hv' : v = z⁻¹ * (z * v * z⁻¹) * z := by group
      rwa [hv']
    have hcardle : Nat.card V ≤ Nat.card (v1Sub D.M ⊥ V hV L) :=
      Nat.card_le_card_of_injective
        (fun v : ↥V => (⟨(v : G), hle v.2⟩ : ↥(v1Sub D.M ⊥ V hV L)))
        (fun a b hab =>
          Subtype.ext (congrArg (fun x : ↥(v1Sub D.M ⊥ V hV L) => (x : G)) hab))
    have hcard : Nat.card V = 2 ^ 8 * Nat.card (v1Sub D.M ⊥ V hV L) := s16c4v1_card_V S
    haveI : Nonempty ↥(v1Sub D.M ⊥ V hV L) := ⟨⟨1, (v1Sub D.M ⊥ V hV L).one_mem⟩⟩
    have hpos : 0 < Nat.card (v1Sub D.M ⊥ V hV L) := Nat.card_pos
    have h256 : Nat.card V = 256 * Nat.card (v1Sub D.M ⊥ V hV L) := by
      rw [hcard]; norm_num
    rw [h256] at hcardle
    omega
  obtain ⟨ω₀, hω₀, hspan⟩ := S.F.exists_omega
  rcases hspan ω with h | h | h | h
  · exact absurd h hω0
  · exact absurd h hz.2.1
  · rw [h]; exact hω₀
  · rw [h]; exact s16c4v1_scl_cube_sq_cube hω₀

theorem s16c4v1_scalar_pow_three (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) :
    ∀ v ∈ V, z ^ 3 * v * (z ^ 3)⁻¹ = v := by
  have hz3M : z ^ 3 ∈ D.M := D.M.pow_mem hz.1 3
  have hscal : s16c4v1_Scal S (z ^ 3) (ω ^ 3) := s16c4v1_scl_scal_pow S hz 3
  have hω3 : ω ^ 3 = 1 := s16c4v1_scl_cube_pow_three (s16c4v1_scalar_cube S hz)
  refine (s16c4v1_centralizes_iff S h1217 hz3M).1 ?_
  intro v hv
  have hv' : z ^ 3 * v * (z ^ 3)⁻¹ ∈ V := s16c4v1_conj_mem S hz3M hv
  have hvec : s16c4v1_vec S (z ^ 3 * v * (z ^ 3)⁻¹) = s16c4v1_vec S v := by
    rw [hscal v hv, hω3, one_smul]
  have hv2 : v * v = 1 := by simpa [pow_two] using hV.2 v hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvmem : (z ^ 3 * v * (z ^ 3)⁻¹) * v⁻¹ ∈ V := V.mul_mem hv' (V.inv_mem hv)
  have hzero : s16c4v1_vec S ((z ^ 3 * v * (z ^ 3)⁻¹) * v⁻¹) = 0 := by
    rw [s16c4v1_vec_mul S hv' (V.inv_mem hv), hvec, hvinv]
    haveI : CharP S.F.K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero S.F.two_eq_zero
    exact CharTwo.add_self_eq_zero _
  exact (s16c4v1_vec_eq_zero_iff S hvmem).1 hzero

private theorem s16c4v1_scl_rho_of_lin (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M)
    (hl : s16c4v1_Lin S m) :
    ∃ (c : S.F.K) (γ : ↥(SUid S.F.σ 4)), c ≠ 0 ∧
      ∀ x : Fin 4 → S.F.K,
        S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV
            ⟨m, s16c4v1_mem_stabTil S hm⟩) x = c • (γ • x) := by
  obtain ⟨c, γ, hc, h⟩ := hl
  refine ⟨c, γ, hc, fun x => ?_⟩
  obtain ⟨v, hv, rfl⟩ := s16c4v1_exists_vec S x
  rw [← s16c4v1_vec_conj S hm hv, h v hv]

private theorem s16c4v1_scl_rho_of_scal (S : s16c4v1_Sit D V L hV) {z : G} {ω : S.F.K}
    (hz : s16c4v1_ScalarOf S z ω) :
    ∀ x : Fin 4 → S.F.K,
      S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV
          ⟨z, s16c4v1_mem_stabTil S hz.1⟩) x = ω • x := by
  intro x
  obtain ⟨v, hv, rfl⟩ := s16c4v1_exists_vec S x
  rw [← s16c4v1_vec_conj S hz.1 hv, hz.2.2 v hv]

private theorem s16c4v1_scl_sameAct (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {a b : G}
    (ha : a ∈ D.M) (hb : b ∈ D.M)
    (h : ∀ u ∈ V, s16c4v1_vec S (a * u * a⁻¹) = s16c4v1_vec S (b * u * b⁻¹)) :
    ∀ u ∈ V, a * u * a⁻¹ = b * u * b⁻¹ := by
  let sa : ↥(stabTil (v1Sub D.M ⊥ V hV L) V) := ⟨a, s16c4v1_mem_stabTil S ha⟩
  let sb : ↥(stabTil (v1Sub D.M ⊥ V hV L) V) := ⟨b, s16c4v1_mem_stabTil S hb⟩
  have hrho : S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV sa) =
      S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV sb) := by
    refine AddEquiv.ext fun x => ?_
    obtain ⟨u, hu, rfl⟩ := s16c4v1_exists_vec S x
    rw [← s16c4v1_vec_conj S ha hu, ← s16c4v1_vec_conj S hb hu]
    exact h u hu
  have hphi : actTil (v1Sub D.M ⊥ V hV L) V hV sa =
      actTil (v1Sub D.M ⊥ V hV L) V hV sb := by
    ext w
    apply S.F.vec_injective
    have h1 : S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV sa) (S.F.vec w) =
        S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV sb) (S.F.vec w) :=
      congrArg (fun f => f (S.F.vec w)) hrho
    rw [S.F.rho_vec, S.F.rho_vec] at h1
    exact h1
  have hy1 : actTil (v1Sub D.M ⊥ V hV L) V hV (sb⁻¹ * sa) = 1 := by
    rw [map_mul, map_inv, hphi, inv_mul_cancel]
  have hyM : b⁻¹ * a ∈ D.M := D.M.mul_mem (D.M.inv_mem hb) ha
  have hcent : ∀ u ∈ V, (b⁻¹ * a) * u * (b⁻¹ * a)⁻¹ = u := by
    refine (s16c4v1_centralizes_iff S h1217 hyM).1 ?_
    intro u hu
    have h1 : actTil (v1Sub D.M ⊥ V hV L) V hV
        ⟨b⁻¹ * a, s16c4v1_mem_stabTil S hyM⟩ = 1 := by
      have hy : (⟨b⁻¹ * a, s16c4v1_mem_stabTil S hyM⟩ :
          ↥(stabTil (v1Sub D.M ⊥ V hV L) V)) = sb⁻¹ * sa := Subtype.ext rfl
      rw [hy, hy1]
    exact (actTil_eq_one_iff (v1Sub D.M ⊥ V hV L) V hV
      ⟨b⁻¹ * a, s16c4v1_mem_stabTil S hyM⟩).1 h1 u hu
  intro u hu
  calc a * u * a⁻¹ = b * (b⁻¹ * a * u * (b⁻¹ * a)⁻¹) * b⁻¹ := by group
    _ = b * u * b⁻¹ := by rw [hcent u hu]

theorem s16c4v1_commute_of_lin (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {m : G} (hm : m ∈ D.M)
    (hl : s16c4v1_Lin S m) :
    ∀ v ∈ V, m * (z * v * z⁻¹) * m⁻¹ = z * (m * v * m⁻¹) * z⁻¹ := by
  obtain ⟨c, γ, hc, hρm⟩ := s16c4v1_scl_rho_of_lin S hm hl
  have hρz := s16c4v1_scl_rho_of_scal S hz
  let a : G := m * z * m⁻¹
  have haM : a ∈ D.M := D.M.mul_mem (D.M.mul_mem hm hz.1) (D.M.inv_mem hm)
  have hsame : ∀ u ∈ V, s16c4v1_vec S (a * u * a⁻¹) = s16c4v1_vec S (z * u * z⁻¹) := by
    intro u hu
    have hu₁ : m⁻¹ * u * m ∈ V := by
      simpa using s16c4v1_conj_mem S (D.M.inv_mem hm) hu
    have hu₂ : z * (m⁻¹ * u * m) * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 hu₁
    have hua : a * u * a⁻¹ = m * (z * (m⁻¹ * u * m) * z⁻¹) * m⁻¹ := by
      simp only [a]; group
    calc s16c4v1_vec S (a * u * a⁻¹)
        = s16c4v1_vec S (m * (z * (m⁻¹ * u * m) * z⁻¹) * m⁻¹) := by rw [hua]
      _ = c • (γ • s16c4v1_vec S (z * (m⁻¹ * u * m) * z⁻¹)) := by
            rw [s16c4v1_vec_conj S hm hu₂, hρm]
      _ = c • (γ • (ω • s16c4v1_vec S (m⁻¹ * u * m))) := by
            rw [hz.2.2 (m⁻¹ * u * m) hu₁]
      _ = c • (ω • (γ • s16c4v1_vec S (m⁻¹ * u * m))) := by
            rw [smul_comm γ ω (s16c4v1_vec S (m⁻¹ * u * m))]
      _ = ω • (c • (γ • s16c4v1_vec S (m⁻¹ * u * m))) := by
            rw [smul_smul, mul_comm c ω, smul_smul]
      _ = ω • (S.F.rho (actTil (v1Sub D.M ⊥ V hV L) V hV
              ⟨m, s16c4v1_mem_stabTil S hm⟩) (s16c4v1_vec S (m⁻¹ * u * m))) := by
            rw [hρm (s16c4v1_vec S (m⁻¹ * u * m))]
      _ = ω • s16c4v1_vec S (m * (m⁻¹ * u * m) * m⁻¹) := by
            rw [s16c4v1_vec_conj S hm hu₁]
      _ = ω • s16c4v1_vec S u := by
            rw [show m * (m⁻¹ * u * m) * m⁻¹ = u by group]
      _ = s16c4v1_vec S (z * u * z⁻¹) := by
            rw [s16c4v1_vec_conj S hz.1 hu, hρz (s16c4v1_vec S u)]
  have hgoal := s16c4v1_scl_sameAct S h1217 haM hz.1 hsame
  intro v hv
  have hv' : m * v * m⁻¹ ∈ V := s16c4v1_conj_mem S hm hv
  have h := hgoal (m * v * m⁻¹) hv'
  have h' : a * (m * v * m⁻¹) * a⁻¹ = m * (z * v * z⁻¹) * m⁻¹ := by
    simp only [a]; group
  rw [← h', h]

theorem s16c4v1_scalar_fpf (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {v : G} (hv : v ∈ V)
    (hfix : z * v * z⁻¹ = v) : v = 1 := by
  haveI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  let tfunG : G → G := fun w => w * (z * w * z⁻¹) * ((z * z) * w * (z * z)⁻¹)
  let c1 : ↥V → ↥V := fun w => ⟨z * (w : G) * z⁻¹, s16c4v1_conj_mem S hz.1 w.2⟩
  let c2 : ↥V → ↥V := fun w => ⟨z * (c1 w : G) * z⁻¹, s16c4v1_conj_mem S hz.1 (c1 w).2⟩
  let tfunV : ↥V → ↥V := fun w => w * c1 w * c2 w
  have htfunV_eq : ∀ w : ↥V, (tfunV w : G) = tfunG w := by
    intro w
    simp only [tfunV, c1, c2, tfunG, Subgroup.coe_mul]
    group
  let tHom : ↥V →* ↥V :=
    { toFun := tfunV
      map_one' := by
        apply Subtype.ext
        simp only [tfunV, c1, c2, Subgroup.coe_mul, Subgroup.coe_one]
        group
      map_mul' := by
        intro x y
        have hc1 : c1 (x * y) = c1 x * c1 y := by
          apply Subtype.ext
          simp only [c1, Subgroup.coe_mul]
          group
        have hc2 : c2 (x * y) = c2 x * c2 y := by
          apply Subtype.ext
          simp only [c2]
          rw [hc1]
          simp only [Subgroup.coe_mul]
          group
        show tfunV (x * y) = tfunV x * tfunV y
        simp only [tfunV, hc1, hc2]
        ac_rfl }
  have ht_mul : ∀ x y : G, x ∈ V → y ∈ V → tfunG (x * y) = tfunG x * tfunG y := by
    intro x y hx hy
    have h := congrArg Subtype.val (map_mul tHom ⟨x, hx⟩ ⟨y, hy⟩)
    change (tfunV (⟨x, hx⟩ * ⟨y, hy⟩) : G) =
      (tfunV ⟨x, hx⟩ : G) * (tfunV ⟨y, hy⟩ : G) at h
    simp only [htfunV_eq, Subgroup.coe_mul] at h
    exact h
  have ht_one : tfunG 1 = 1 := by
    have h := congrArg Subtype.val (map_one tHom)
    change (tfunV (1 : ↥V) : G) = (1 : G) at h
    rwa [htfunV_eq] at h
  have ht_inv : ∀ x : G, x ∈ V → tfunG x⁻¹ = (tfunG x)⁻¹ := by
    intro x hx
    have h := ht_mul x x⁻¹ hx (V.inv_mem hx)
    rw [mul_inv_cancel, ht_one] at h
    exact (inv_eq_of_mul_eq_one_right h.symm).symm
  have htvec : ∀ w : ↥V, s16c4v1_vec S (tfunV w : G) = 0 := by
    intro w
    rw [htfunV_eq w]
    have h1 : z * (w : G) * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 w.2
    have h2 : (z * z) * (w : G) * (z * z)⁻¹ ∈ V := by
      have e : (z * z) * (w : G) * (z * z)⁻¹ = z * (z * (w : G) * z⁻¹) * z⁻¹ := by group
      rw [e]
      exact s16c4v1_conj_mem S hz.1 h1
    simp only [tfunG]
    rw [s16c4v1_vec_mul S (V.mul_mem w.2 h1) h2, s16c4v1_vec_mul S w.2 h1]
    rw [hz.2.2 (w : G) w.2]
    have hvec2 : s16c4v1_vec S ((z * z) * (w : G) * (z * z)⁻¹) =
        ω ^ 2 • s16c4v1_vec S (w : G) := by
      have e : (z * z) * (w : G) * (z * z)⁻¹ = z * (z * (w : G) * z⁻¹) * z⁻¹ := by group
      rw [e, hz.2.2 (z * (w : G) * z⁻¹) h1, hz.2.2 (w : G) w.2, smul_smul, pow_two]
    rw [hvec2]
    have hsum : (1 : S.F.K) + ω + ω ^ 2 = 0 := by
      linear_combination s16c4v1_scalar_cube S hz
    calc s16c4v1_vec S (w : G) + ω • s16c4v1_vec S (w : G)
          + ω ^ 2 • s16c4v1_vec S (w : G)
        = (1 + ω + ω ^ 2) • s16c4v1_vec S (w : G) := by rw [add_smul, add_smul, one_smul]
      _ = 0 := by rw [hsum, zero_smul]
  have ht_memV1 : ∀ w : ↥V, tfunG w ∈ v1Sub D.M ⊥ V hV L := by
    intro w
    rw [← htfunV_eq w]
    exact (s16c4v1_vec_eq_zero_iff S (tfunV w).2).1 (htvec w)
  have ht_conj_L : ∀ (l : G) (hl : l ∈ L) (w : ↥V),
      tfunG (l * (w : G) * l⁻¹) = l * tfunG w * l⁻¹ := by
    intro l hl w
    have hlM : l ∈ D.M := S.sect.setting.hyp151.le hl
    have hlin : s16c4v1_Lin S l := by
      obtain ⟨γ, hγ⟩ := s16c4v1_induces_of_mem_L S hl
      exact ⟨1, γ, one_ne_zero, fun u hu => by rw [hγ u hu, one_smul]⟩
    have hcomm := s16c4v1_commute_of_lin S h1217 hz hlM hlin
    have hw1 : z * (w : G) * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 w.2
    have hw1L : l * (w : G) * l⁻¹ ∈ V := s16c4v1_conj_mem S hlM w.2
    have e1 : l * (z * (w : G) * z⁻¹) * l⁻¹ = z * (l * (w : G) * l⁻¹) * z⁻¹ :=
      hcomm (w : G) w.2
    have e2 : l * ((z * z) * (w : G) * (z * z)⁻¹) * l⁻¹ =
        (z * z) * (l * (w : G) * l⁻¹) * (z * z)⁻¹ := by
      have f : (z * z) * (w : G) * (z * z)⁻¹ = z * (z * (w : G) * z⁻¹) * z⁻¹ := by group
      rw [f, hcomm (z * (w : G) * z⁻¹) hw1, e1]
      group
    rw [← htfunV_eq ⟨l * (w : G) * l⁻¹, hw1L⟩, ← htfunV_eq w]
    simp only [htfunV_eq, tfunG]
    rw [show l * ((w : G) * (z * (w : G) * z⁻¹) * ((z * z) * (w : G) * (z * z)⁻¹)) * l⁻¹ =
        (l * (w : G) * l⁻¹) * (l * (z * (w : G) * z⁻¹) * l⁻¹) *
          (l * ((z * z) * (w : G) * (z * z)⁻¹) * l⁻¹) by group]
    rw [e1, e2]
  have ht_comm : ∀ (a : ↥V) (l : G) (hl : l ∈ L), tfunG ⁅(a : G), l⁆ = 1 := by
    intro a l hl
    have hlM : l ∈ D.M := S.sect.setting.hyp151.le hl
    have ha' : l * (a : G)⁻¹ * l⁻¹ ∈ V :=
      s16c4v1_conj_mem S hlM (V.inv_mem a.2)
    have hdecomp : ⁅(a : G), l⁆ = (a : G) * (l * (a : G)⁻¹ * l⁻¹) := by group
    rw [hdecomp, ht_mul (a : G) (l * (a : G)⁻¹ * l⁻¹) a.2 ha']
    have ha_inv : tfunG ((a : G)⁻¹) = (tfunG (a : G))⁻¹ := ht_inv (a : G) a.2
    have hconj : tfunG (l * (a : G)⁻¹ * l⁻¹) = l * (tfunG (a : G))⁻¹ * l⁻¹ := by
      rw [ht_conj_L l hl ⟨(a : G)⁻¹, V.inv_mem a.2⟩, ha_inv]
    rw [hconj]
    have hmem1 : tfunG (a : G) ∈ v1Sub D.M ⊥ V hV L := ht_memV1 a
    rw [s16c4v1_L_centralizes_V1 S hl ((v1Sub D.M ⊥ V hV L).inv_mem hmem1), mul_inv_cancel]
  let K : Subgroup G := tHom.ker.map V.subtype
  have hVLle : ⁅V, L⁆ ≤ K := by
    refine Subgroup.commutator_le.mpr ?_
    intro a ha l hl
    have hmemV : ⁅a, l⁆ ∈ V := by
      have h : ⁅a, l⁆ ∈ ⁅V, L⁆ := Subgroup.commutator_mem_commutator ha hl
      rwa [s16c4v1_comm_eq S] at h
    refine Subgroup.mem_map.mpr ⟨⟨⁅a, l⁆, hmemV⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change (tfunV ⟨⁅a, l⁆, hmemV⟩ : G) = (1 : G)
    rw [htfunV_eq]
    exact ht_comm ⟨a, ha⟩ l hl
  have hVle : V ≤ K := by rw [← s16c4v1_comm_eq S]; exact hVLle
  have ht_eq_one : ∀ w : ↥V, tfunG w = 1 := by
    intro w
    obtain ⟨w', hw'ker, hw'eq⟩ := Subgroup.mem_map.mp (hVle w.2)
    have h1 : tHom w' = 1 := MonoidHom.mem_ker.mp hw'ker
    have h2 : tfunG w' = 1 := by
      have h := congrArg Subtype.val h1
      change (tfunV w' : G) = (1 : G) at h
      rwa [htfunV_eq] at h
    have hweq : w' = w := Subtype.ext hw'eq
    rw [← hweq]
    exact h2
  have ht_v : tfunG v = v := by
    simp only [tfunG]
    rw [hfix]
    have e : (z * z) * v * (z * z)⁻¹ = z * (z * v * z⁻¹) * z⁻¹ := by group
    rw [e, hfix, hfix]
    have hv2 : v * v = 1 := by simpa [pow_two] using hV.2 v hv
    rw [hv2, one_mul]
  have hone : tfunG v = 1 := ht_eq_one ⟨v, hv⟩
  rw [ht_v] at hone
  exact hone

theorem s16c4v1_lin_of_cent_V1 (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {m : G} (hm : m ∈ D.M)
    (hc : ∀ x ∈ v1Sub D.M ⊥ V hV L, m * x * m⁻¹ = x) : s16c4v1_Lin S m := by
  have hms : m ∈ stabTil (v1Sub D.M ⊥ V hV L) V := s16c4v1_mem_stabTil S hm
  let φ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV) :=
    actTil (v1Sub D.M ⊥ V hV L) V hV ⟨m, hms⟩
  have hmN : m ∈ nBar D.M ⊥ V hV L := by
    rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]
    exact hm
  have hφN : φ ∈ normalizer (lBar (v1Sub D.M ⊥ V hV L) V hV L :
      Set (MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))) :=
    Sixteen24.actTil_v1Sub_mem_normalizer D h1217 S.sect.setting.hyp151 hV hm hmN hms
  have hω3 : ω ^ 3 = 1 := s16c4v1_scl_cube_pow_three (s16c4v1_scalar_cube S hz)
  have hz3 : ∀ w ∈ V, z ^ 3 * w * (z ^ 3)⁻¹ = w :=
    s16c4v1_scalar_pow_three S h1217 hz
  have hlin : S.F.IsLin φ := by
    rcases S.F.isLin_or_isSemi hφN with hl | hs
    · exact hl
    · exfalso
      let a : G := m * z * m⁻¹
      have haM : a ∈ D.M := D.M.mul_mem (D.M.mul_mem hm hz.1) (D.M.inv_mem hm)
      have hazM : a * z ∈ D.M := D.M.mul_mem haM hz.1
      have hvec_a : ∀ w ∈ V, s16c4v1_vec S (a * w * a⁻¹) = ω ^ 2 • s16c4v1_vec S w := by
        intro w hw
        have hw₁ : m⁻¹ * w * m ∈ V := by
          simpa using s16c4v1_conj_mem S (D.M.inv_mem hm) hw
        have hw₂ : z * (m⁻¹ * w * m) * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 hw₁
        have hua : a * w * a⁻¹ = m * (z * (m⁻¹ * w * m) * z⁻¹) * m⁻¹ := by
          simp only [a]; group
        rw [hua, s16c4v1_vec_conj S hm hw₂]
        change S.F.rho φ (s16c4v1_vec S (z * (m⁻¹ * w * m) * z⁻¹)) =
          ω ^ 2 • s16c4v1_vec S w
        rw [hz.2.2 (m⁻¹ * w * m) hw₁]
        rw [hs ω (s16c4v1_vec S (m⁻¹ * w * m))]
        rw [show S.F.rho φ (s16c4v1_vec S (m⁻¹ * w * m)) = s16c4v1_vec S w by
          rw [← s16c4v1_vec_conj S hm hw₁]
          congr 1
          group]
      have hvec_az : ∀ w ∈ V,
          s16c4v1_vec S ((a * z) * w * (a * z)⁻¹) = s16c4v1_vec S w := by
        intro w hw
        have hwz : z * w * z⁻¹ ∈ V := s16c4v1_conj_mem S hz.1 hw
        have hua : (a * z) * w * (a * z)⁻¹ = a * (z * w * z⁻¹) * a⁻¹ := by group
        rw [hua, hvec_a (z * w * z⁻¹) hwz, hz.2.2 w hw, smul_smul]
        rw [show ω ^ 2 * ω = 1 by rw [← pow_succ, hω3], one_smul]
      have hcent : ∀ w ∈ V, (a * z) * w * (a * z)⁻¹ = w := by
        refine (s16c4v1_centralizes_iff S h1217 hazM).1 ?_
        intro w hw
        have hw' : (a * z) * w * (a * z)⁻¹ ∈ V := s16c4v1_conj_mem S hazM hw
        have hw2 : w * w = 1 := by simpa [pow_two] using hV.2 w hw
        have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
        have hzero : s16c4v1_vec S ((a * z) * w * (a * z)⁻¹ * w⁻¹) = 0 := by
          rw [s16c4v1_vec_mul S hw' (V.inv_mem hw), hvec_az w hw, hwinv]
          haveI : CharP S.F.K 2 :=
            CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero S.F.two_eq_zero
          exact CharTwo.add_self_eq_zero _
        exact (s16c4v1_vec_eq_zero_iff S (V.mul_mem hw' (V.inv_mem hw))).1 hzero
      have hV1_bot : v1Sub D.M ⊥ V hV L = ⊥ := by
        apply le_bot_iff.mp
        intro x hx
        have hxV : x ∈ V := s16c4v1_v1_le S hx
        have hzx : z * x * z⁻¹ ∈ v1Sub D.M ⊥ V hV L := s16c4v1_conj_mem_v1 S hz.1 hx
        have hzxV : z * x * z⁻¹ ∈ V := s16c4v1_v1_le S hzx
        have hcent_x := hcent (z * x * z⁻¹) hzxV
        have hcalc : (a * z) * (z * x * z⁻¹) * (a * z)⁻¹ = x := by
          have hzxV1 : z * (z * x * z⁻¹) * z⁻¹ ∈ v1Sub D.M ⊥ V hV L :=
            s16c4v1_conj_mem_v1 S hz.1 hzx
          have hm_wc : m⁻¹ * (z * (z * x * z⁻¹) * z⁻¹) * m =
              z * (z * x * z⁻¹) * z⁻¹ := by
            have h := hc _ hzxV1
            have h' : z * (z * x * z⁻¹) * z⁻¹ =
                m⁻¹ * (z * (z * x * z⁻¹) * z⁻¹) * m := by
              conv_rhs => rw [← h]
              group
            exact h'.symm
          have hwceq : (z * z) * x * (z * z)⁻¹ =
              z * (z * x * z⁻¹) * z⁻¹ := by group
          have hzw : z * (z * (z * x * z⁻¹) * z⁻¹) * z⁻¹ = x := by
            have h := hz3 x hxV
            rw [show z ^ 3 = z * z * z by rw [pow_succ, pow_succ, pow_one]] at h
            rw [← show z * (z * (z * x * z⁻¹) * z⁻¹) * z⁻¹ =
                (z * z * z) * x * (z * z * z)⁻¹ by group] at h
            exact h
          have e1 : (a * z) * (z * x * z⁻¹) * (a * z)⁻¹ =
              a * ((z * z) * x * (z * z)⁻¹) * a⁻¹ := by
            simp only [a]; group
          rw [e1, hwceq]
          simp only [a]
          rw [show m * z * m⁻¹ * (z * (z * x * z⁻¹) * z⁻¹) * (m * z * m⁻¹)⁻¹ =
              m * (z * (m⁻¹ * (z * (z * x * z⁻¹) * z⁻¹) * m) * z⁻¹) * m⁻¹ by group]
          rw [hm_wc, hzw]
          exact hc x hx
        have hfixx : z * x * z⁻¹ = x := (hcalc.symm.trans hcent_x).symm
        exact s16c4v1_scalar_fpf S h1217 hz hxV hfixx
      exact S.ne_bot hV1_bot
  have hlinK : ∀ (c : S.F.K) (x : Fin 4 → S.F.K), S.F.rho φ (c • x) = c • S.F.rho φ x := hlin
  let lin : (Fin 4 → S.F.K) →ₗ[S.F.K] (Fin 4 → S.F.K) :=
    { toFun := S.F.rho φ
      map_add' := fun x y => map_add (S.F.rho φ) x y
      map_smul' := hlinK }
  let A : Matrix (Fin 4) (Fin 4) S.F.K := LinearMap.toMatrix' lin
  have hA_mulVec : ∀ x : Fin 4 → S.F.K, A *ᵥ x = S.F.rho φ x := by
    intro x
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  let linInv : (Fin 4 → S.F.K) →ₗ[S.F.K] (Fin 4 → S.F.K) :=
    { toFun := (S.F.rho φ).symm
      map_add' := fun x y => (S.F.rho φ).symm.map_add x y
      map_smul' := fun c x => by
        apply (S.F.rho φ).injective
        simp only [RingHom.id_apply]
        rw [AddEquiv.apply_symm_apply, hlinK c ((S.F.rho φ).symm x),
          AddEquiv.apply_symm_apply] }
  let B : Matrix (Fin 4) (Fin 4) S.F.K := LinearMap.toMatrix' linInv
  have hlin_mul : lin * linInv = 1 := by
    apply LinearMap.ext
    intro x
    change S.F.rho φ ((S.F.rho φ).symm x) = x
    rw [AddEquiv.apply_symm_apply]
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_mul, hlin_mul, LinearMap.toMatrix'_one]
  have hdet : A.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hAB
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact one_ne_zero h.symm
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hN : ∀ g : ↥(SUid S.F.σ 4), ∃ g' : ↥(SUid S.F.σ 4),
      ∀ x : Fin 4 → S.F.K, A *ᵥ (g • x) = g' • (A *ᵥ x) := by
    intro g
    have hmem : φ * (S.F.π g) * φ⁻¹ ∈ lBar (v1Sub D.M ⊥ V hV L) V hV L := by
      have h := (Subgroup.mem_set_normalizer_iff.1 hφN (S.F.π g)).1 (S.F.π g).2
      simpa using h
    let g' : ↥(SUid S.F.σ 4) := S.F.π.symm ⟨φ * (S.F.π g) * φ⁻¹, hmem⟩
    have hπg' : (S.F.π g' : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV)) =
        φ * (S.F.π g) * φ⁻¹ := by simp [g']
    have hπrho : ∀ (δ : ↥(SUid S.F.σ 4)) (y : Fin 4 → S.F.K),
        S.F.rho (S.F.π δ) y = δ • y := by
      intro δ y
      rw [← S.F.vec_ofVec y, S.F.rho_vec, S.F.vec_action, S.F.vec_ofVec]
    refine ⟨g', fun x => ?_⟩
    calc A *ᵥ (g • x) = S.F.rho φ (g • x) := hA_mulVec _
      _ = S.F.rho φ (S.F.rho (S.F.π g) x) := by rw [hπrho g x]
      _ = S.F.rho (φ * S.F.π g) x := (S.F.rho_mul φ (S.F.π g) x).symm
      _ = S.F.rho (S.F.π g' * φ) x := by
            rw [show φ * S.F.π g = S.F.π g' * φ by rw [hπg']; group]
      _ = S.F.rho (S.F.π g') (S.F.rho φ x) := S.F.rho_mul (S.F.π g') φ x
      _ = g' • (S.F.rho φ x) := hπrho g' (S.F.rho φ x)
      _ = g' • (A *ᵥ x) := by rw [hA_mulVec]
  obtain ⟨c, γ, hc0, hAx⟩ := s16c4v1_lin_normalizer S.F.σ S.F.card_K S.F.isUnitary A hA hN
  refine ⟨c, γ, hc0, fun v hv => ?_⟩
  rw [s16c4v1_vec_conj S hm hv]
  change S.F.rho φ (s16c4v1_vec S v) = c • (γ • s16c4v1_vec S v)
  rw [← hA_mulVec, hAx]


theorem s16c4v1_two_form (S : s16c4v1_Sit D V L hV) {m : G} (hm : m ∈ D.M)
    (hl : s16c4v1_Lin S m) (h2 : ∃ n : ℕ, m ^ (2 ^ n) = 1) :
    ∃ γ : ↥(SUid S.F.σ 4), s16c4v1_Induces S m γ := by
  obtain ⟨n, hn⟩ := h2
  obtain ⟨c, γ, hc0, hρ⟩ := s16c4v1_scl_rho_of_lin S hm hl
  let φ : MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV) :=
    actTil (v1Sub D.M ⊥ V hV L) V hV ⟨m, s16c4v1_mem_stabTil S hm⟩
  have hρφ : ∀ x : Fin 4 → S.F.K, S.F.rho φ x = c • (γ • x) := hρ
  have hφpow : φ ^ (2 ^ n) = 1 := by
    have h : (⟨m, s16c4v1_mem_stabTil S hm⟩ : ↥(stabTil (v1Sub D.M ⊥ V hV L) V)) ^
        (2 ^ n) = 1 := by
      apply Subtype.ext
      simpa using hn
    have := map_pow (actTil (v1Sub D.M ⊥ V hV L) V hV)
      (⟨m, s16c4v1_mem_stabTil S hm⟩ : ↥(stabTil (v1Sub D.M ⊥ V hV L) V)) (2 ^ n)
    rw [h, map_one] at this
    exact this.symm
  have hpow : ∀ k : ℕ, ∀ x : Fin 4 → S.F.K,
      S.F.rho (φ ^ k) x = c ^ k • (γ ^ k • x) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp [UFrame.rho]
    | succ k ih =>
      intro x
      calc S.F.rho (φ ^ (k + 1)) x
          = S.F.rho φ (S.F.rho (φ ^ k) x) := by rw [pow_succ', S.F.rho_mul]
        _ = S.F.rho φ (c ^ k • (γ ^ k • x)) := by rw [ih]
        _ = c • (γ • (c ^ k • (γ ^ k • x))) := hρφ _
        _ = c • (c ^ k • (γ • (γ ^ k • x))) := by
              rw [smul_comm γ (c ^ k) (γ ^ k • x)]
        _ = (c * c ^ k) • (γ • (γ ^ k • x)) := by rw [← smul_smul]
        _ = (c * c ^ k) • ((γ * γ ^ k) • x) := by rw [← mul_smul]
        _ = c ^ (k + 1) • (γ ^ (k + 1) • x) := by rw [pow_succ', pow_succ']
  have hfix : ∀ x : Fin 4 → S.F.K, c ^ (2 ^ n) • (γ ^ (2 ^ n) • x) = x := by
    intro x
    have h := hpow (2 ^ n) x
    rw [hφpow] at h
    rw [← h]
    simp [UFrame.rho]
  let M : Matrix (Fin 4) (Fin 4) S.F.K :=
    (((γ ^ (2 ^ n) : ↥(SUid S.F.σ 4)) : GL (Fin 4) S.F.K) : Matrix (Fin 4) (Fin 4) S.F.K)
  let A : Matrix (Fin 4) (Fin 4) S.F.K := c ^ (2 ^ n) • M
  have hAx : ∀ x : Fin 4 → S.F.K, A *ᵥ x = x := by
    intro x
    have h1 : M *ᵥ x = γ ^ (2 ^ n) • x := by
      rw [← CFSG.ClassicalGroups.Unitary.smul_def]
    change (c ^ (2 ^ n) • M) *ᵥ x = x
    rw [Matrix.smul_mulVec, h1, hfix]
  have hAeq : A = 1 := by
    ext i j
    have h := congrFun (hAx (Pi.single j (1 : S.F.K))) i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h
  have hdetM : M.det = 1 := ((mem_SUid_iff S.F.σ).mp (γ ^ (2 ^ n)).2).1
  have hdet : (c ^ (2 ^ n)) ^ (4 : ℕ) = 1 := by
    have h := congrArg Matrix.det hAeq
    rw [Matrix.det_one] at h
    have h2 : A.det = (c ^ (2 ^ n)) ^ (4 : ℕ) := by
      change (c ^ (2 ^ n) • M).det = (c ^ (2 ^ n)) ^ (4 : ℕ)
      rw [Matrix.det_smul, hdetM, mul_one, Fintype.card_fin]
    rw [h2] at h
    exact h
  haveI : Fintype S.F.K := Fintype.ofFinite S.F.K
  have hc4 : c ^ 4 = c := by
    have := FiniteField.pow_card c
    rwa [Fintype.card_eq_nat_card, S.F.card_K] at this
  have hc2n : c ^ (2 ^ n) = 1 := by
    calc c ^ (2 ^ n) = (c ^ 4) ^ (2 ^ n) := by rw [hc4]
      _ = c ^ (4 * 2 ^ n) := by rw [pow_mul]
      _ = c ^ (2 ^ n * 4) := by rw [mul_comm]
      _ = (c ^ (2 ^ n)) ^ 4 := by rw [pow_mul]
      _ = 1 := hdet
  have hc3 : c ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [Fintype.card_eq_nat_card, S.F.card_K] at h
  have hcone : c = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ n) := (by decide : Nat.Coprime 3 2).pow_right n
    have h := (pow_gcd_eq_one (a := c) (m := 3) (n := 2 ^ n)).mpr ⟨hc3, hc2n⟩
    rw [hcop.gcd_eq_one] at h
    simpa using h
  refine ⟨γ, fun v hv => ?_⟩
  rw [s16c4v1_vec_conj S hm hv]
  change S.F.rho φ (s16c4v1_vec S v) = γ • s16c4v1_vec S v
  rw [hρφ, hcone, one_smul]


theorem s16c4v1_two_hom (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {A : Subgroup G} (hAM : A ≤ D.M)
    (hA2 : IsPGroup 2 A) (hA1 : ∀ a ∈ A, ∀ x ∈ v1Sub D.M ⊥ V hV L, a * x * a⁻¹ = x) :
    ∃ φ : ↥A →* ↥(SUid S.F.σ 4), (∀ a : ↥A, s16c4v1_Induces S (a : G) (φ a)) ∧
      ∀ a : ↥A, φ a = 1 ↔ ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = v := by
  classical
  have hchoice : ∀ a : ↥A, ∃ γ : ↥(SUid S.F.σ 4), s16c4v1_Induces S (a : G) γ := by
    intro a
    have hlin : s16c4v1_Lin S (a : G) :=
      s16c4v1_lin_of_cent_V1 S h1217 hz (hAM a.2) (hA1 (a : G) a.2)
    obtain ⟨k, hk⟩ := hA2 a
    refine s16c4v1_two_form S (hAM a.2) hlin ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  let φ : ↥A → ↥(SUid S.F.σ 4) := fun a => Classical.choose (hchoice a)
  have hφ : ∀ a : ↥A, s16c4v1_Induces S (a : G) (φ a) := fun a => Classical.choose_spec (hchoice a)
  have hone : s16c4v1_Induces S (1 : G) (1 : ↥(SUid S.F.σ 4)) := by
    intro v hv
    simp [s16c4v1_Induces]
  have hker : ∀ a : ↥A, φ a = 1 ↔ ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = v := by
    intro a
    constructor
    · intro ha v hv
      have hcent : ∀ w ∈ V,
          (a : G) * w * (a : G)⁻¹ * w⁻¹ ∈ v1Sub D.M ⊥ V hV L := by
        intro w hw
        have hw' : (a : G) * w * (a : G)⁻¹ ∈ V := s16c4v1_conj_mem S (hAM a.2) hw
        have hvec : s16c4v1_vec S ((a : G) * w * (a : G)⁻¹) = s16c4v1_vec S w := by
          rw [hφ a w hw, ha, one_smul]
        have hw2 : w * w = 1 := by simpa [pow_two] using hV.2 w hw
        have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
        have hmem : (a : G) * w * (a : G)⁻¹ * w⁻¹ ∈ V := V.mul_mem hw' (V.inv_mem hw)
        exact (s16c4v1_vec_eq_zero_iff S hmem).1 (by
          rw [s16c4v1_vec_mul S hw' (V.inv_mem hw), hvec, hwinv]
          haveI : CharP S.F.K 2 :=
            CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero S.F.two_eq_zero
          exact CharTwo.add_self_eq_zero _)
      exact (s16c4v1_centralizes_iff S h1217 (hAM a.2)).1 hcent v hv
    · intro hc
      apply s16c4v1_induces_unique S (hφ a)
      intro v hv
      rw [hc v hv]
      simp [s16c4v1_Induces]
  let ψ : ↥A →* ↥(SUid S.F.σ 4) :=
    { toFun := φ
      map_one' := s16c4v1_induces_unique S (hφ 1) hone
      map_mul' := fun a b =>
        s16c4v1_induces_unique S (hφ (a * b))
          (s16c4v1_induces_mul S (hAM a.2) (hAM b.2) (hφ a) (hφ b)) }
  exact ⟨ψ, hφ, hker⟩


private noncomputable def s16c4v1_scl_zAut (S : s16c4v1_Sit D V L hV) {z : G}
    (hz : z ∈ D.M) : MulAut ↥V where
  toFun w := ⟨z * (w : G) * z⁻¹, s16c4v1_conj_mem S hz w.2⟩
  invFun w := ⟨z⁻¹ * (w : G) * z, by
    have h := s16c4v1_conj_mem S (D.M.inv_mem hz) w.2
    simpa using h⟩
  left_inv w := Subtype.ext (by group)
  right_inv w := Subtype.ext (by group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem s16c4v1_scl_zAut_three (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) :
    ∀ w : ↥V, s16c4v1_scl_zAut S hz.1 (s16c4v1_scl_zAut S hz.1
      (s16c4v1_scl_zAut S hz.1 w)) = w := by
  intro w
  apply Subtype.ext
  change z * (z * (z * (w : G) * z⁻¹) * z⁻¹) * z⁻¹ = (w : G)
  have h := s16c4v1_scalar_pow_three S h1217 hz (w : G) w.2
  rw [show z ^ 3 = z * z * z by rw [pow_succ, pow_succ, pow_one]] at h
  rw [show z * (z * (z * (w : G) * z⁻¹) * z⁻¹) * z⁻¹ =
      (z * z * z) * (w : G) * (z * z * z)⁻¹ by group]
  exact h

private theorem s16c4v1_scl_zAut_fpf (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) :
    ∀ w : ↥V, s16c4v1_scl_zAut S hz.1 w = w → w = 1 := by
  intro w hw
  apply Subtype.ext
  apply s16c4v1_scalar_fpf S h1217 hz w.2
  have h := congrArg Subtype.val hw
  change z * (w : G) * z⁻¹ = (w : G) at h
  exact h

theorem s16c4v1_card_v1 (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card ↥(v1Sub D.M ⊥ V hV L) = 4 ^ k := by
  haveI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  let zAut : MulAut ↥V := s16c4v1_scl_zAut S hz.1
  let X : Subgroup ↥V := (v1Sub D.M ⊥ V hV L).subgroupOf V
  have hXz : ∀ x ∈ X, zAut x ∈ X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change z * (x : G) * z⁻¹ ∈ v1Sub D.M ⊥ V hV L
    exact s16c4v1_conj_mem_v1 S hz.1 hx
  obtain ⟨k, hk⟩ := CFSG.Quasithin.H.Mathieu.M22Row.exists_card_eq_four_pow (V := ↥V)
    (fun w => Subtype.ext (by simpa [pow_two] using hV.2 (w : G) w.2))
    (s16c4v1_scl_zAut_three S h1217 hz) (s16c4v1_scl_zAut_fpf S h1217 hz) X hXz
  have hcard : Nat.card ↥(v1Sub D.M ⊥ V hV L) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (s16c4v1_v1_le S)).symm.toEquiv
  refine ⟨k, ?_, ?_⟩
  · by_contra hlt
    have hk0 : k = 0 := by omega
    have h1 : Nat.card ↥(v1Sub D.M ⊥ V hV L) = 1 := by rw [hcard, hk, hk0, pow_zero]
    exact S.ne_bot (Subgroup.eq_bot_of_card_eq _ h1)
  · rw [hcard, hk]


theorem s16c4v1_card_cent_four_pow (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {Y : Subgroup G}
    (hcomm : ∀ y ∈ Y, ∀ v ∈ V, y * (z * v * z⁻¹) * y⁻¹ = z * (y * v * y⁻¹) * z⁻¹) :
    ∃ j : ℕ, Nat.card ↥(V ⊓ Subgroup.centralizer (Y : Set G)) = 4 ^ j := by
  haveI : IsMulCommutative ↥V := hV.1
  letI : CommGroup ↥V := IsMulCommutative.instCommGroup
  let zAut : MulAut ↥V := s16c4v1_scl_zAut S hz.1
  let X : Subgroup ↥V := (V ⊓ Subgroup.centralizer (Y : Set G)).subgroupOf V
  have hXz : ∀ x ∈ X, zAut x ∈ X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, ?_⟩
    · change z * (x : G) * z⁻¹ ∈ V
      exact s16c4v1_conj_mem S hz.1 hx.1
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxY : y * (x : G) = (x : G) * y :=
        (Subgroup.mem_centralizer_iff.1 hx.2) y hy
      have h := hcomm y hy (x : G) hx.1
      rw [show y * (x : G) * y⁻¹ = (x : G) by rw [hxY]; group] at h
      change y * (z * (x : G) * z⁻¹) = (z * (x : G) * z⁻¹) * y
      calc y * (z * (x : G) * z⁻¹) = (y * (z * (x : G) * z⁻¹) * y⁻¹) * y := by group
        _ = (z * (x : G) * z⁻¹) * y := by rw [h]
  obtain ⟨j, hj⟩ := CFSG.Quasithin.H.Mathieu.M22Row.exists_card_eq_four_pow (V := ↥V)
    (fun w => Subtype.ext (by simpa [pow_two] using hV.2 (w : G) w.2))
    (s16c4v1_scl_zAut_three S h1217 hz) (s16c4v1_scl_zAut_fpf S h1217 hz) X hXz
  refine ⟨j, ?_⟩
  have hcard : Nat.card ↥(V ⊓ Subgroup.centralizer (Y : Set G)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.toEquiv
  rw [hcard, hj]


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
