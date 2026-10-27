module

public import CFSG.Quasithin.EmptyFaithful.S151ZX

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem fpf_pow_of_fpf {V : Type*} [Group V] {z : MulAut V} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : V, z w = w → w = 1) {n : ℕ} (hn : ¬ 3 ∣ n) :
    ∀ w : V, (z ^ n) w = w → w = 1 := by
  have hmod : z ^ n = z ^ (n % 3) := by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hz3, one_pow, mul_one]
  rw [hmod]
  have h3 : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h
  · rw [h, pow_one]
    exact hfpf
  · rw [h]
    intro w hw
    apply hfpf
    have h2 : z ((z ^ 2) w) = z w := by rw [hw]
    have h3' : z ((z ^ 2) w) = w := by
      have : (z * z ^ 2) w = w := by
        rw [← pow_succ', hz3]
        rfl
      simpa [MulAut.mul_apply] using this
    rw [← h2, h3']

theorem input15124SevenElt_holds : Input15124SevenElt := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h7
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hM := hc.ctx.mf
  have hV : V154 T Mc M = VZ T M := hS.hV
  obtain ⟨hVe, d, hA₀⟩ := exists_seven7Data hq hM h7 hV
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  have hzP : d.z ∈ oTwoUpper (autOn M (V154 T Mc M)) := d.ctx.Z_le_P d.gen.zZ
  have hzA : d.z ∈ autOn M (V154 T Mc M) := oTwoUpper_le _ hzP
  have hz3 : d.z ^ 3 = 1 := SevenGen.z3 d.ctx d.gen
  have hfpf : ∀ w : ↥(V154 T Mc M), d.z w = w → w = 1 := SevenGen.fpf_z' d.ctx d.gen
  obtain ⟨m, hmN, hmM, hmz⟩ := mem_autOn_iff_exists.mp hzA
  have hord : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨e, n', hn', hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  have hn'0 : n' ≠ 0 := fun h => by
    rw [h, mul_zero] at hN
    exact hord hN
  have hxord : orderOf (m ^ n') = 3 ^ e := by
    rw [orderOf_pow' m hn'0, hN]
    have hg : Nat.gcd (3 ^ e * n') n' = n' := Nat.gcd_eq_right (dvd_mul_left n' (3 ^ e))
    rw [hg]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'0)
  have hact : ∀ k : ℤ, conjAct (V154 T Mc M) ⟨m ^ k, Subgroup.zpow_mem _ hmN k⟩ = d.z ^ k := by
    intro k
    have : (⟨m ^ k, Subgroup.zpow_mem _ hmN k⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
        (⟨m, hmN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) ^ k := rfl
    rw [this, map_zpow, hmz]
  obtain ⟨-, P₁, P₂, -, -, -, -, -, hprod, hZ1, -, -⟩ := hS.seven_P h7
  have hP₁sub : ∀ q ∈ P₁, q ∈ oTwoUpper (autOn M (V154 T Mc M)) := by
    intro q hq
    have h1 : (1 : MulAut ↥(V154 T Mc M)) ∈
        (centerOf (pCoreOf 3 (autOn M (V154 T Mc M))) : Set (MulAut ↥(V154 T Mc M))) :=
      (centerOf (pCoreOf 3 (autOn M (V154 T Mc M)))).one_mem
    have h2 : (1 : MulAut ↥(V154 T Mc M)) ∈ (P₂ : Set (MulAut ↥(V154 T Mc M))) := P₂.one_mem
    have h3 := Set.mul_mem_mul (Set.mul_mem_mul h1 hq) h2
    rw [one_mul, mul_one, hprod] at h3
    rw [← d.pCore_eq_oTwoUpper]
    exact h3
  have hcomm : ∀ q ∈ P₁, ∀ k : ℤ, q * d.z ^ k = d.z ^ k * q := by
    intro q hq k
    have h1 : q * d.z = d.z * q := d.ctx.Z_central d.gen.zZ (hP₁sub q hq)
    exact (Commute.zpow_right (show Commute q d.z from h1) k).eq
  have hfwd : ∀ k : ℤ, ∀ g ∈ Z₁, m ^ k * g * (m ^ k)⁻¹ ∈ Z₁ := by
    intro k g hg
    rw [hZ1] at hg ⊢
    obtain ⟨hgV, hgC⟩ := Subgroup.mem_inf.mp hg
    have hmk : m ^ k ∈ Subgroup.normalizer ((V154 T Mc M : Subgroup G) : Set G) :=
      Subgroup.zpow_mem _ hmN k
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hmk g).mp hgV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m' hm'
    obtain ⟨hm'M, hm'N, hm'P⟩ := mem_preOn.mp hm'
    have hab : conjAct (V154 T Mc M) ⟨m', hm'N⟩ * conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ =
        conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ * conjAct (V154 T Mc M) ⟨m', hm'N⟩ := by
      rw [hact k]
      exact hcomm _ hm'P k
    let u : ↥(V154 T Mc M) := ⟨g, hgV⟩
    have hau : conjAct (V154 T Mc M) ⟨m', hm'N⟩ u = u := by
      apply Subtype.ext
      rw [conj_coe_apply]
      show m' * g * m'⁻¹ = g
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_iff.mp hgC m' hm'
    have h1 : conjAct (V154 T Mc M) ⟨m', hm'N⟩ (conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u) =
        conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u := by
      calc conjAct (V154 T Mc M) ⟨m', hm'N⟩ (conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u)
          = (conjAct (V154 T Mc M) ⟨m', hm'N⟩ * conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩) u := rfl
        _ = (conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ * conjAct (V154 T Mc M) ⟨m', hm'N⟩) u := by
          rw [hab]
        _ = conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ (conjAct (V154 T Mc M) ⟨m', hm'N⟩ u) := rfl
        _ = conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u := by rw [hau]
    have e1 : ((conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u : ↥(V154 T Mc M)) : G) =
        m ^ k * g * (m ^ k)⁻¹ := conj_coe_apply (V154 T Mc M) ⟨m ^ k, hmk⟩ u
    have e2 : ((conjAct (V154 T Mc M) ⟨m', hm'N⟩
        (conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u) : ↥(V154 T Mc M)) : G) =
        m' * ((conjAct (V154 T Mc M) ⟨m ^ k, hmk⟩ u : ↥(V154 T Mc M)) : G) * m'⁻¹ :=
      conj_coe_apply (V154 T Mc M) ⟨m', hm'N⟩ _
    have h3 := congrArg Subtype.val h1
    rw [e2, e1] at h3
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hxN : m ^ n' ∈ Subgroup.normalizer (Z₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hfwd (n' : ℤ) h hh
      simpa [zpow_natCast] using this
    · intro hh
      have := hfwd (-(n' : ℤ)) _ hh
      have e : m ^ (-(n' : ℤ)) * (m ^ n' * h * (m ^ n')⁻¹) * (m ^ (-(n' : ℤ)))⁻¹ = h := by
        rw [zpow_neg, zpow_natCast, inv_inv]
        group
      rwa [e] at this
  refine ⟨m ^ n', hxN, ⟨e, hxord⟩, ?_⟩
  intro hx
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS.z1_ne
  have hgZ : (g : G) ∈ Z₁ := g.2
  have hgV : (g : G) ∈ V154 T Mc M := (hS.z1_le.trans inf_le_left) hgZ
  have hcomm' : (g : G) * m ^ n' = m ^ n' * g := Subgroup.mem_centralizer_iff.mp hx g hgZ
  have hxN' : m ^ n' ∈ Subgroup.normalizer ((V154 T Mc M : Subgroup G) : Set G) :=
    Subgroup.pow_mem _ hmN n'
  have hact' : conjAct (V154 T Mc M) ⟨m ^ n', hxN'⟩ = d.z ^ n' := by
    have := hact (n' : ℤ)
    simpa [zpow_natCast] using this
  let u : ↥(V154 T Mc M) := ⟨g, hgV⟩
  have hfix : (d.z ^ n') u = u := by
    apply Subtype.ext
    rw [← hact', conj_coe_apply]
    show m ^ n' * g * (m ^ n')⁻¹ = g
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm'.symm
  have hu1 := fpf_pow_of_fpf hz3 hfpf hn' u hfix
  have hg_one : (g : G) = 1 := congrArg (Subtype.val : ↥(V154 T Mc M) → G) hu1
  exact hg1 (Subtype.ext hg_one)

theorem input15124SevenBlock_holds (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) : Input15124SevenBlock :=
  input15124SevenBlock_of hF h36 h38 hK input15124SevenElt_holds

end CFSG.Quasithin
