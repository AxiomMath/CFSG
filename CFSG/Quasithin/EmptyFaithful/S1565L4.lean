module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Matrix

theorem exists_mem_borel_of_model {Y : Type} [Group Y] [Finite Y] {Ks MKs : Subgroup Y}
    {P : Type} [Group P] (e : ↥Ks ≃* P) (Q : Sylow 2 P) (x : P)
    (hx : x ∈ Subgroup.normalizer ((Q : Subgroup P) : Set P))
    (hB : E2.IsBorelIn Ks MKs) : ∃ y ∈ MKs, orderOf y = orderOf x := by
  obtain ⟨S, hS, rfl⟩ := hB
  obtain ⟨hSK, hS2, hSi⟩ := hS
  have hS' : IsPGroup 2 (S.subgroupOf Ks) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  let S' : Sylow 2 ↥Ks := hS'.toSylow hSi
  let Q' : Sylow 2 ↥Ks :=
    Q.comapOfInjective e.toMonoidHom e.injective
      (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
  have : Finite (Sylow 2 ↥Ks) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Ks) Q' S'
  set xK : ↥Ks := e.symm x with hxK
  have hQ'mem : ∀ h : ↥Ks, h ∈ (Q' : Subgroup ↥Ks) ↔ e h ∈ (Q : Subgroup P) := fun h => Iff.rfl
  have hxQ' : xK ∈ Subgroup.normalizer ((Q' : Subgroup ↥Ks) : Set ↥Ks) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQ'mem, hQ'mem, map_mul, map_mul, map_inv, hxK, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hx (e h)
  have hxs : xK • Q' = Q' := Sylow.smul_eq_iff_mem_normalizer.mpr hxQ'
  set y : ↥Ks := g * xK * g⁻¹ with hy
  have hys : y • S' = S' := by
    rw [hy, ← hg, mul_smul, mul_smul, inv_smul_smul, hxs]
  have hyN : y ∈ Subgroup.normalizer ((S' : Subgroup ↥Ks) : Set ↥Ks) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hys
  have hS'mem : ∀ h : ↥Ks, h ∈ (S' : Subgroup ↥Ks) ↔ (h : Y) ∈ S := fun h => Iff.rfl
  have hyY : (y : Y) ∈ Subgroup.normalizer (S : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hhS
      have hhK : h ∈ Ks := hSK hhS
      have := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhK⟩).mp ((hS'mem _).mpr hhS)
      exact (hS'mem _).mp this
    · intro hS2'
      have hhK : h ∈ Ks := by
        have h1 : (y : Y)⁻¹ * ((y : Y) * h * (y : Y)⁻¹) * (y : Y) = h := by group
        rw [← h1]
        exact Ks.mul_mem (Ks.mul_mem (Ks.inv_mem y.2) (hSK hS2')) y.2
      have := (Subgroup.mem_normalizer_iff.mp hyN ⟨h, hhK⟩).mpr ((hS'mem _).mpr hS2')
      exact (hS'mem _).mp this
  have hmem : (y : Y) ∈ Ks ⊓ Subgroup.normalizer (S : Set Y) := ⟨y.2, hyY⟩
  refine ⟨(y : Y), hmem, ?_⟩
  rw [Subgroup.orderOf_coe, hy]
  have h1 : orderOf xK = orderOf x := orderOf_injective e.symm.toMonoidHom e.symm.injective x
  rw [← h1]
  exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective xK)


section PSL2

variable {K : Type} [Field K]

private noncomputable def diagSL2 (ω : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

private theorem coe_diagSL2 (ω : Kˣ) :
    (diagSL2 ω : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(ω : K), ((ω⁻¹ : Kˣ) : K)] := rfl

private theorem diagSL2_mem_upperTriangular (ω : Kˣ) :
    diagSL2 ω ∈ LinearFlag.upperTriangular 2 K := by
  rw [LinearFlag.mem_upperTriangular]
  intro i j hji
  rw [coe_diagSL2, Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

private theorem diagSL2_pow (ω : Kˣ) (r : ℕ) (hω : ω ^ r = 1) : (diagSL2 ω) ^ r = 1 := by
  have h3 : ((ω : K)) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
  have key : ((diagSL2 ω ^ r : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagSL2, Matrix.diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp [h3]
    · simp [h3]
  exact Subtype.ext key

private theorem diagSL2_not_mem_scalars (ω : Kˣ) (hω2 : ω ^ 2 ≠ 1) :
    diagSL2 ω ∉ LinearFlag.scalars 2 K := by
  intro hmem
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hmem
  have h0 := congrFun (congrFun hc 0) 0
  have h1 := congrFun (congrFun hc 1) 1
  rw [coe_diagSL2] at h0 h1
  simp at h0 h1
  have h2 : (ω : K) = (ω : K)⁻¹ := h0.trans h1.symm
  have h3 : ω = ω⁻¹ := Units.ext (by simpa using h2)
  apply hω2
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.mpr h3

theorem exists_order_normalizer_projSL2 [Finite K] [CharP K 2] (r : ℕ) [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (ω : Kˣ) (hω : orderOf ω = r) :
    ∃ Q : Sylow 2 (LinearFlag.projectiveSL 2 K), ∃ x : LinearFlag.projectiveSL 2 K,
      x ∈ Subgroup.normalizer ((Q : Subgroup (LinearFlag.projectiveSL 2 K)) :
        Set (LinearFlag.projectiveSL 2 K)) ∧ orderOf x = r := by
  obtain ⟨Q, hQ⟩ := LinearFlag.exists_sylow_projUnitriangular (K := K) 2 (n := 2) (by norm_num)
  have hωr : ω ^ r = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hω] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).mp this)
  refine ⟨Q, LinearFlag.proj 2 K (diagSL2 ω), ?_, ?_⟩
  · rw [hQ, LinearFlag.normalizer_projUnitriangular 2]
    exact Subgroup.mem_map_of_mem _ (diagSL2_mem_upperTriangular ω)
  · apply orderOf_eq_prime
    · rw [← map_pow, diagSL2_pow ω r hωr, map_one]
    · rw [Ne, LinearFlag.proj_eq_one_iff]
      exact diagSL2_not_mem_scalars ω hω2

end PSL2

section Suzuki

open CFSG.LieType.Ree CFSG.Blueprint

theorem exists_order_normalizer_suzuki {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    ∃ Q : Sylow 2 (suzukiGroup a K), ∃ x : suzukiGroup a K,
      x ∈ Subgroup.normalizer ((Q : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) ∧
        orderOf x = orderOf l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUcard : Nat.card (suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 :=
    (suzuki_unipotent_structure hK).2.1
  have hU2 : IsPGroup 2 (suzukiU a K) :=
    IsPGroup.of_card (n := (2 * a + 1) * 2) (by rw [hUcard, ← pow_mul])
  have hidx : (suzukiU a K).index = (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    have h := (suzukiU a K).card_mul_index
    rw [hUcard, suzuki_order hK] at h
    have hpos : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [h, mul_assoc]
  have hodd : ¬ 2 ∣ (suzukiU a K).index := by
    rw [hidx]
    intro h
    have h1 : Odd (2 ^ (2 * a + 1) - 1) := by
      have : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      have h2 : Even (2 ^ (2 * a + 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      obtain ⟨c, hc⟩ := h2
      exact ⟨c - 1, by omega⟩
    have h2 : Odd ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
      have h2 : Even ((2 ^ (2 * a + 1)) ^ 2) :=
        (Nat.even_pow.mpr ⟨(Nat.even_pow.mpr ⟨even_two, by omega⟩), by omega⟩)
      exact h2.add_one
    have := (Nat.odd_mul.mpr ⟨h1, h2⟩)
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  refine ⟨hU2.toSylow hodd, suzukiDElt a K l, ?_, ?_⟩
  · exact suzukiT_le_normalizer hK (suzukiDElt_mem_suzukiT a K l)
  · let f : Kˣ →* suzukiGroup a K :=
      { toFun := suzukiDElt a K
        map_one' := suzukiDElt_one
        map_mul' := fun l m => (suzukiDElt_mul l m).symm }
    exact orderOf_injective f (fun l m h => (suzukiDElt_inj hK).1 h) l

end Suzuki

theorem exists_odd_prime_dvd_two_pow_sub_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ n - 1 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hne : 2 ^ n - 1 ≠ 1 := by omega
  refine ⟨(2 ^ n - 1).minFac, Nat.minFac_prime hne, ?_, Nat.minFac_dvd _⟩
  intro h2
  have hd : 2 ∣ 2 ^ n - 1 := by
    have := Nat.minFac_dvd (2 ^ n - 1)
    rw [h2] at this
    exact this
  have hev : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  obtain ⟨c, hc⟩ := hev
  omega

theorem exists_odd_order_mem_borel_psl2 {Y : Type} [Group Y] [Finite Y] {Ks MKs : Subgroup Y}
    {n : ℕ} (hn : 2 ≤ n) (hs : IsPSL 2 2 n ↥Ks) (hB : E2.IsBorelIn Ks MKs) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ y ∈ MKs, orderOf y = r := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hn
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rw [Nat.card_units, hK]; exact hrd)
  obtain ⟨Q, x, hx, hxr⟩ := exists_order_normalizer_projSL2 (K := K) r hr2 ω hω
  obtain ⟨y, hy, hyo⟩ := exists_mem_borel_of_model
    ((e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 2 K)).symm) Q x hx hB
  exact ⟨r, hr, hr2, y, hy, hyo.trans hxr⟩

theorem exists_odd_order_mem_borel_sz {Y : Type} [Group Y] [Finite Y]
    {Ks MKs : Subgroup Y} {n : ℕ} (hs : IsSz n ↥Ks) (hB : E2.IsBorelIn Ks MKs) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ y ∈ MKs, orderOf y = r := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hs
  have hn : 2 ≤ n := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hn
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rw [Nat.card_units, hK]; exact hrd)
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
  obtain ⟨Q, x, hx, hxo⟩ := exists_order_normalizer_suzuki hK' l
  obtain ⟨y, hy, hyo⟩ := exists_mem_borel_of_model e Q x hx hB
  exact ⟨r, hr, hr2, y, hy, hyo.trans (hxo.trans hl)⟩

end CFSG.Quasithin
