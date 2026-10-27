module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.LieType.Ree.FixedSubgroupData
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThree
import CFSG.RankThree.PartOne.K128.ReeShape
import CFSG.RankThree.PartOne.SEITZ3.PlaneCount
import CFSG.RankThree.PartOne.SEITZQ1.Plane
import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.SEITZQ1 CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.SEITZ3

theorem ggWeylIrred_of_twF4LargeCoords {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) {Ω : Subgroup G} (P : ℤ → ℤ → G) (hPΩ : ∀ i j, P i j ∈ Ω)
    (hΩP : ∀ y ∈ Ω, ∃ i j, P i j = y)
    (hmul : ∀ i j i' j', P i j * P i' j' = P (i + i') (j + j'))
    (hone : ∀ i j, P i j = 1 ↔ (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j)
    {n₁ n₂ : G} (hn₁ : ∀ i j, n₁ * P i j * n₁⁻¹ = P j i)
    (hn₂ : ∀ i j, n₂ * P i j * n₂⁻¹ = P i (-i - j)) : GGWeylIrred Ω := by
  have hinvp : ∀ c : ℤ, ¬ (p : ℤ) ∣ c → ∃ d : ℤ, (p : ℤ) ∣ c * d - 1 := by
    intro c hc
    have hcop : IsCoprime (p : ℤ) c := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast]
      have : ¬ p ∣ c.natAbs := fun hd => hc (Int.natCast_dvd.mpr hd)
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr this
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨v, ⟨-u, by linear_combination huv⟩⟩
  have hP00 : P 0 0 = 1 := (hone 0 0).2 ⟨dvd_zero _, dvd_zero _⟩
  have hinv : ∀ i j, (P i j)⁻¹ = P (-i) (-j) := by
    intro i j
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, hmul, neg_add_cancel, neg_add_cancel, hP00]
  have hres : ∀ i j i' j', (p : ℤ) ∣ i - i' → (p : ℤ) ∣ j - j' → P i j = P i' j' := by
    intro i j i' j' hi hj
    have h1 : P i j * (P i' j')⁻¹ = 1 := by
      rw [hinv, hmul, ← sub_eq_add_neg, ← sub_eq_add_neg]
      exact (hone _ _).2 ⟨hi, hj⟩
    exact mul_inv_eq_one.mp h1
  have hzpow : ∀ i j (m : ℤ), P i j ^ m = P (m * i) (m * j) := by
    intro i j m
    refine Int.induction_on m ?_ ?_ ?_
    · rw [zpow_zero, zero_mul, zero_mul, hP00]
    · intro k ih
      rw [zpow_add_one, ih, hmul]
      congr 1 <;> ring
    · intro k ih
      rw [zpow_sub_one, ih, hinv, hmul]
      congr 1 <;> ring
  have hn₁N : n₁ ∈ Subgroup.normalizer (Ω : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨i, j, rfl⟩ := hΩP h hh
      rw [hn₁]
      exact hPΩ _ _
    · intro hh
      obtain ⟨i, j, hij⟩ := hΩP _ hh
      have h3 : MulAut.conj n₁ h = MulAut.conj n₁ (P j i) := by
        rw [MulAut.conj_apply, MulAut.conj_apply, ← hij, hn₁]
      rw [(MulAut.conj n₁).injective h3]
      exact hPΩ _ _
  have hn₂N : n₂ ∈ Subgroup.normalizer (Ω : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨i, j, rfl⟩ := hΩP h hh
      rw [hn₂]
      exact hPΩ _ _
    · intro hh
      obtain ⟨i, j, hij⟩ := hΩP _ hh
      have h2 : n₂ * P i (-i - j) * n₂⁻¹ = P i j := by
        rw [hn₂]
        congr 1
        ring
      have h3 : MulAut.conj n₂ h = MulAut.conj n₂ (P i (-i - j)) := by
        rw [MulAut.conj_apply, MulAut.conj_apply, ← hij, h2]
      rw [(MulAut.conj n₂).injective h3]
      exact hPΩ _ _
  intro E hEΩ hEinv
  rcases Subgroup.bot_or_exists_ne_one E with hbot | ⟨x, hxE, hx1⟩
  · exact Or.inl hbot
  right
  refine le_antisymm hEΩ ?_
  obtain ⟨i, j, rfl⟩ := hΩP x (hEΩ hxE)
  have hij : ¬ ((p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) := fun h => hx1 ((hone i j).2 h)
  have hcm : ∀ g ∈ Subgroup.normalizer (Ω : Set G), ∀ y ∈ E, g * y * g⁻¹ * y⁻¹ ∈ E :=
    fun g hg y hy => E.mul_mem (hEinv g hg y hy) (E.inv_mem hy)
  have hu : P (j - i) (i - j) ∈ E := by
    have h := hcm n₁ hn₁N _ hxE
    rwa [hn₁, hinv, hmul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
  have hv : P 0 (-i - 2 * j) ∈ E := by
    have h := hcm n₂ hn₂N _ hxE
    rwa [hn₂, hinv, hmul, show i + -i = 0 by ring, show -i - j + -j = -i - 2 * j by ring] at h
  have hstep : ∀ i' j', P i' j' ∈ E → P j' i' ∈ E := by
    intro i' j' h'
    have h := hEinv n₁ hn₁N _ h'
    rwa [hn₁] at h
  have hgen : P 1 0 ∈ E ∧ P 0 1 ∈ E := by
    by_cases hA : (p : ℤ) ∣ j - i
    · have hB : ¬ (p : ℤ) ∣ -i - 2 * j := by
        intro hB
        apply hij
        have h3i : (p : ℤ) ∣ 3 * i := by
          have h := dvd_add hB (dvd_mul_of_dvd_right hA 2)
          rw [show -i - 2 * j + 2 * (j - i) = -(3 * i) by ring] at h
          exact (dvd_neg).mp h
        have hi : (p : ℤ) ∣ i := by
          rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h3i with h3 | h3
          · have h' : p ∣ 3 := by exact_mod_cast h3
            exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h') hp3
          · exact h3
        refine ⟨hi, ?_⟩
        rw [show j = (j - i) + i by ring]
        exact dvd_add hA hi
      obtain ⟨d, hd⟩ := hinvp _ hB
      have h := E.zpow_mem hv d
      have h01 : P 0 1 ∈ E := by
        rwa [hzpow, hres (d * 0) (d * (-i - 2 * j)) 0 1 (by simp)
          (by rw [show d * (-i - 2 * j) - 1 = (-i - 2 * j) * d - 1 by ring]; exact hd)] at h
      exact ⟨hstep 0 1 h01, h01⟩
    · obtain ⟨d, hd⟩ := hinvp _ hA
      have h := E.zpow_mem hu d
      have h1m : P 1 (-1) ∈ E := by
        rwa [hzpow, hres (d * (j - i)) (d * (i - j)) 1 (-1)
          (by rw [show d * (j - i) - 1 = (j - i) * d - 1 by ring]; exact hd)
          (by
            rw [show d * (i - j) - -1 = -((j - i) * d - 1) by ring]
            exact (dvd_neg).mpr hd)] at h
      have h10 : P 1 0 ∈ E := by
        have h' := hEinv n₂ hn₂N _ h1m
        rwa [hn₂, show -(1 : ℤ) - -1 = 0 by ring] at h'
      exact ⟨h10, hstep 1 0 h10⟩
  obtain ⟨h10, h01⟩ := hgen
  intro y hy
  obtain ⟨a, b, rfl⟩ := hΩP y hy
  have e : P a b = P 1 0 ^ a * P 0 1 ^ b := by
    rw [hzpow, hzpow, hmul]
    congr 1 <;> ring
  rw [e]
  exact E.mul_mem (E.zpow_mem h10 a) (E.zpow_mem h01 b)

theorem exists_ggWeylIrred_unitarySU_twF4Large {f : ℕ} {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K') {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpq : p ∣ 2 ^ f + 1)
    {G : Type} [Group G] (Ψ : unitarySU 2 f K' 3 →* G) (hΨ : Function.Injective Ψ) :
    ∃ Ω : Subgroup G, GGWeylIrred Ω ∧ (∀ x ∈ Ω, x ^ p = 1) ∧ Nat.card Ω = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have hcardU : Nat.card K'ˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ f) 1
    rw [Nat.card_units, h.card, pow_mul']
    exact h1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := K'ˣ) p
    (hcardU ▸ Dvd.dvd.mul_right hpq _)
  set S := Subgroup.zpowers ζ with hS
  have hSp : ∀ s ∈ S, s ^ p = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]))
  have hSq : ∀ s ∈ S, s ^ (2 ^ f + 1) = 1 := fun s hs =>
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hs).trans (by rw [hζ]; exact hpq))
  have hDmem : ∀ i j : ℤ, q1DiagTorus (ζ ^ i, ζ ^ (i + j)) ∈ unitarySU 2 f K' 3 :=
    fun i j => q1DiagTorus_mem_unitarySU h (Prod.ext (hSq _ (Subgroup.zpow_mem_zpowers ζ i))
      (hSq _ (Subgroup.zpow_mem_zpowers ζ (i + j))))
  set P : ℤ → ℤ → G := fun i j => Ψ (⟨_, hDmem i j⟩ : unitarySU 2 f K' 3) with hPdef
  set E₀ : Subgroup (GL (Fin 3) K') := (S.prod S).map q1DiagTorus with hE₀
  have hE₀G : E₀ ≤ unitarySU 2 f K' 3 := by
    rintro _ ⟨u, hu, rfl⟩
    exact q1DiagTorus_mem_unitarySU h (Prod.ext (hSq _ hu.1) (hSq _ hu.2))
  set Ω : Subgroup G := (E₀.subgroupOf (unitarySU 2 f K' 3)).map Ψ with hΩ
  have hcardΩ : Nat.card Ω = p ^ 2 := by
    rw [hΩ, Subgroup.card_map_of_injective hΨ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀G).toEquiv,
      Subgroup.card_map_of_injective q1DiagTorus_injective,
      Nat.card_congr (Subgroup.prodEquiv S S).toEquiv, Nat.card_prod, hS, Nat.card_zpowers, hζ,
      sq]
  have hPΩ : ∀ i j, P i j ∈ Ω := fun i j =>
    Subgroup.mem_map_of_mem Ψ (Subgroup.mem_subgroupOf.mpr ⟨(ζ ^ i, ζ ^ (i + j)),
      ⟨Subgroup.zpow_mem_zpowers ζ i, Subgroup.zpow_mem_zpowers ζ (i + j)⟩, rfl⟩)
  have hΩP : ∀ y ∈ Ω, ∃ i j, P i j = y := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, ⟨hu1, hu2⟩, hud⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hd)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hu1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu2
    refine ⟨m, n - m, ?_⟩
    show Ψ _ = Ψ d
    congr 1
    apply Subtype.ext
    show q1DiagTorus (ζ ^ m, ζ ^ (m + (n - m))) = (d : GL (Fin 3) K')
    rw [← hud, show m + (n - m) = n by ring, hm, hn]
  have hΩexp : ∀ x ∈ Ω, x ^ p = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨u, hu, hud⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hd)
    have hup : u ^ p = 1 := Prod.ext (hSp _ hu.1) (hSp _ hu.2)
    have hdp : d ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hud, ← map_pow, hup, map_one]
      rfl
    rw [← map_pow, hdp, map_one]
  have hmul : ∀ i j i' j', P i j * P i' j' = P (i + i') (j + j') := by
    intro i j i' j'
    show Ψ _ * Ψ _ = Ψ _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show q1DiagTorus _ * q1DiagTorus _ = q1DiagTorus _
    rw [← map_mul, Prod.mk_mul_mk, ← zpow_add, ← zpow_add,
      show i + j + (i' + j') = i + i' + (j + j') by ring]
  have hone : ∀ i j, P i j = 1 ↔ (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j
    show Ψ _ = 1 ↔ _
    rw [map_eq_one_iff Ψ hΨ, Subgroup.mk_eq_one, map_eq_one_iff _ q1DiagTorus_injective,
      Prod.mk_eq_one, ← orderOf_dvd_iff_zpow_eq_one, ← orderOf_dvd_iff_zpow_eq_one, hζ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa using dvd_sub h2 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, dvd_add h1 h2⟩
  have hdiag : ∀ u : K'ˣ × K'ˣ, q1DiagTorus u = diagU (q1DiagVec u) := fun u =>
    Units.ext (by rw [q1DiagTorus, MonoidHom.comp_apply, coe_q1DiagGL, diagU_val])
  set w₁ : unitarySU 2 f K' 3 :=
    ⟨permGL (Equiv.swap (0 : Fin 3) 1), permGL_mem_unitarySU h _⟩ with hw₁
  set w₂ : unitarySU 2 f K' 3 :=
    ⟨permGL (Equiv.swap (1 : Fin 3) 2), permGL_mem_unitarySU h _⟩ with hw₂
  have hn₁ : ∀ i j, Ψ w₁ * P i j * (Ψ w₁)⁻¹ = P j i := by
    intro i j
    show Ψ w₁ * Ψ _ * (Ψ w₁)⁻¹ = Ψ _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show permGL (Equiv.swap (0 : Fin 3) 1) * q1DiagTorus (ζ ^ i, ζ ^ (i + j)) *
      (permGL (Equiv.swap (0 : Fin 3) 1))⁻¹ = q1DiagTorus (ζ ^ j, ζ ^ (j + i))
    rw [hdiag, hdiag, permGL_conj_diagU]
    congr 1
    funext k
    fin_cases k <;> simp [q1DiagVec_apply, Equiv.swap_apply_def] <;> group
  have hn₂ : ∀ i j, Ψ w₂ * P i j * (Ψ w₂)⁻¹ = P i (-i - j) := by
    intro i j
    show Ψ w₂ * Ψ _ * (Ψ w₂)⁻¹ = Ψ _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show permGL (Equiv.swap (1 : Fin 3) 2) * q1DiagTorus (ζ ^ i, ζ ^ (i + j)) *
      (permGL (Equiv.swap (1 : Fin 3) 2))⁻¹ = q1DiagTorus (ζ ^ i, ζ ^ (i + (-i - j)))
    rw [hdiag, hdiag, permGL_conj_diagU]
    congr 1
    funext k
    fin_cases k <;> simp [q1DiagVec_apply, Equiv.swap_apply_def] <;> group
  exact ⟨Ω, ggWeylIrred_of_twF4LargeCoords hp hp3 P hPΩ hΩP hmul hone hn₁ hn₂, hΩexp, hcardΩ⟩

theorem ggWeylIrred_of_sylowShape_twF4Large {G : Type} [Group G] [Finite G] {p e : ℕ}
    (hp : p.Prime) (hshape : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e G) {Ω : Subgroup G}
    (hΩ : GGWeylIrred Ω) (hΩp : ∀ x ∈ Ω, x ^ p = 1) (hΩc : Nat.card Ω = p ^ 2)
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) (h2 : p ^ 2 ≤ Nat.card E) :
    GGWeylIrred E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 _ x.2)⟩
  have hΩpg : IsPGroup p Ω := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hΩp _ x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨Q₀, hΩQ₀⟩ := hΩpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q₀ Q
  have hQS : (Q : Subgroup G) = cj (Q₀ : Subgroup G) c := by
    rw [← hc, Sylow.coe_subgroup_smul]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj E c⁻¹ ≤ (Q₀ : Subgroup G) := by
    intro x hx
    have h1 : x ∈ cj (cj (Q₀ : Subgroup G) c) c⁻¹ := cj_le_cj (hEQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  obtain ⟨φ₀⟩ := hshape (Q₀ : Subgroup G) Q₀.isPGroup' Q₀.not_dvd_index
  have hFexp : ∀ x ∈ cj E c⁻¹, x ^ p = 1 := fun x hx => pow_eq_one_of_mem_cj hE.2 hx
  have hFcard : Nat.card (cj E c⁻¹) ≤ p ^ 2 := by
    have h1 := card_le_sq_of_exponent hp
      (((cj E c⁻¹).subgroupOf (Q₀ : Subgroup G)).map φ₀.toMonoidHom) (by
        rintro _ ⟨y, hy, rfl⟩
        have hyp : y ^ p = 1 := Subtype.ext (hFexp _ hy)
        rw [← map_pow, hyp, map_one])
    rwa [Subgroup.card_map_of_injective φ₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFS).toEquiv] at h1
  have hFeq : cj E c⁻¹ = Ω := plane_unique hp φ₀ hFS hΩQ₀ hFexp hΩp
    (le_antisymm hFcard (by rw [card_cj]; exact h2)) hΩc
  have hEΩ : E = cj Ω c := by rw [← hFeq, cj_inv_cj]
  rw [hEΩ]
  exact ggWeylIrred_map (MulAut.conj c) hΩ

theorem ggSCWeylIrredTwoLU4_reeGamma_twF4Large
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) + 1) :
    GGSCWeylIrredTwoLU4 p ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨Ψ, hΨ⟩ := TwF4SUThree.exists_injective_unitarySU_hom a K hK
  have h : UnitaryFieldData 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  obtain ⟨Ω, hΩ, hΩp, hΩc⟩ := exists_ggWeylIrred_unitarySU_twF4Large h hp (by omega) hpq Ψ hΨ
  intro E hE h2 _
  exact ggWeylIrred_of_sylowShape_twF4Large hp
    (CFSG.RankThree.PartOne.K128.sylowShape_ree_phi2 hK hp hp5 hpq) hΩ hΩp hΩc hE h2

end CFSG.StandardType

end
