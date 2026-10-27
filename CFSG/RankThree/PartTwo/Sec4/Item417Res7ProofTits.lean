module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofF4
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTitsCore
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Sporadic.Schreier.Tits Item434RemTits

namespace Res417Seven

theorem exists_pGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    (h : ∃ P : Subgroup Y, IsPGroup 3 P ∧
      Subgroup.centralizer ({e x} : Set Y) ≤ Subgroup.normalizer (P : Set Y) ∧
      ∀ y ∈ Subgroup.centralizer ({e x} : Set Y), y ^ 3 = 1 → y ∈ P) :
    ∃ P : Subgroup X, IsPGroup 3 P ∧
      Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (P : Set X) ∧
      ∀ y ∈ Subgroup.centralizer ({x} : Set X), y ^ 3 = 1 → y ∈ P := by
  obtain ⟨P, hP3, hPN, hPy⟩ := h
  have hcen : ∀ g : X, g ∈ Subgroup.centralizer ({x} : Set X) →
      e g ∈ Subgroup.centralizer ({e x} : Set Y) := fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← map_mul, ← map_mul, hg]
  refine ⟨P.comap e.toMonoidHom, hP3.comap_of_injective e.toMonoidHom e.injective, fun g hg => ?_,
    fun y hy hy3 => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 := (Subgroup.mem_normalizer_iff.mp (hPN (hcen g hg))) (e z)
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    exact h1
  · show e y ∈ P
    exact hPy (e y) (hcen y hy) (by rw [← map_pow, hy3, map_one])

theorem exists_commute_not_mem_zpowers {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (hcard : 9 ≤ Nat.card G) (hexp : ∀ g : G, g ^ 3 = 1) {s : G} (hs : orderOf s = 3) :
    ∃ y : G, y * s = s * y ∧ y ∉ Subgroup.zpowers s := by
  by_cases hsc : s ∈ Subgroup.center G
  · by_contra hall
    push Not at hall
    have hle : (⊤ : Subgroup G) ≤ Subgroup.zpowers s := fun y _ =>
      hall y (Subgroup.mem_center_iff.mp hsc y)
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, Nat.card_zpowers, hs] at h1
    omega
  · have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hZ : Nontrivial (Subgroup.center G) := hG.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center G)
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hzs : (z : G) * s = s * z := (Subgroup.mem_center_iff.mp z.2 s).symm
    refine ⟨z, hzs, fun hzs' => hsc ?_⟩
    have hz3 : orderOf (z : G) = 3 := orderOf_eq_prime (hexp z) hz1'
    have heq : Subgroup.zpowers (z : G) = Subgroup.zpowers s :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzs')
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hs, hz3])
    have hs' : s ∈ Subgroup.zpowers (z : G) := heq ▸ Subgroup.mem_zpowers s
    exact Subgroup.zpowers_le.mpr z.2 hs'

section Tits


theorem pow_three_eq_one_of_titsD {y : titsD} (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) : y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hy
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hQ : IsPGroup 3 (Subgroup.zpowers y) := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsD sylSylow T
  have hyT : y ∈ (T : Subgroup titsD) := hQT (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyT
  have hyS : g⁻¹ * y * g ∈ (sylSylow : Subgroup titsD) := by
    simpa [MulAut.smul_def, mul_assoc] using hyT
  have hcube := cube_of_mem_sylPerms (mem_sylGrp.mp (Subgroup.mem_subgroupOf.mp hyS))
  have h1 : (g⁻¹ * y * g) ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_three, ← mul_assoc]
    exact hcube)
  have e1 : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
    simpa using (conj_pow (a := g⁻¹) (b := y) (i := 3))
  rw [e1] at h1
  have : y ^ 3 = g * (g⁻¹ * y ^ 3 * g) * g⁻¹ := by group
  rw [this, h1, mul_one, mul_inv_cancel]

theorem exists_commute_of_titsD {x : titsD} (hx : orderOf x = 3) :
    ∃ y : titsD, y * x = x * y ∧ y ^ 3 = 1 ∧ y ∉ Subgroup.zpowers x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylGrp hx
  set s : sylGrp := ⟨((g * x * g⁻¹ : titsD) : Equiv.Perm (Fin 1755)), hg⟩ with hs
  have hsylexp : ∀ t : sylGrp, t ^ 3 = 1 := fun t => Subtype.ext (by
    rw [Subgroup.coe_pow, pow_three, ← mul_assoc]
    exact cube_of_mem_sylPerms (mem_sylGrp.mp t.2))
  have hsylp : IsPGroup 3 sylGrp := IsPGroup.of_card (n := 3) (by rw [card_sylGrp]; norm_num)
  have hso : orderOf s = 3 := by
    rw [hs, Subgroup.orderOf_mk, Subgroup.orderOf_coe, Item434RemTits.orderOf_conj, hx]
  obtain ⟨t, hts, htx⟩ := exists_commute_not_mem_zpowers hsylp (by rw [card_sylGrp]; norm_num)
    hsylexp hso
  set t' : titsD := ⟨t, sylGrp_le_titsD t.2⟩ with ht'
  have hconj : t' * (g * x * g⁻¹) = (g * x * g⁻¹) * t' := by
    apply Subtype.ext
    have h := congrArg Subtype.val hts
    simp only [Subgroup.coe_mul, hs] at h
    simpa only [Subgroup.coe_mul, ht'] using h
  refine ⟨g⁻¹ * t' * g, ?_, ?_, fun hmem => htx ?_⟩
  · calc g⁻¹ * t' * g * x = g⁻¹ * (t' * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * t') * g := by rw [hconj]
      _ = x * (g⁻¹ * t' * g) := by group
  · have ht3 : t' ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ht']
      exact congrArg Subtype.val (hsylexp t))
    have e1 : (g⁻¹ * t' * g) ^ 3 = g⁻¹ * t' ^ 3 * g := by
      simpa using (conj_pow (a := g⁻¹) (b := t') (i := 3))
    rw [e1, ht3, mul_one, inv_mul_cancel]
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : t' = (g * x * g⁻¹) ^ i := by
      rw [conj_zpow, hi]
      group
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, ht'] at *
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_zpow] at h2
    exact h2.symm

theorem exists_card_centralizer_of_titsD
    {x : titsD}
    (hx : orderOf x = 3) :
    ∃ a b : ℕ, Nat.card (Subgroup.centralizer ({x} : Set titsD)) = 2 ^ a * 3 ^ b ∧ b ≤ 3 := by
  set C := Subgroup.centralizer ({x} : Set titsD) with hC
  have hnot : ∀ r : ℕ, (r = 5 ∨ r = 13) → ¬ r ∣ Nat.card C := by
    intro r hr hdvd
    have : Fact r.Prime := ⟨by rcases hr with rfl | rfl <;> norm_num⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hco : orderOf (c : titsD) = r := by rw [Subgroup.orderOf_coe, hc]
    exact mul_ne_mul_of_orderOf hx hr hco (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  have hdvd : Nat.card C ∣ 2 ^ 11 * 3 ^ 3 * 325 := by
    have := Subgroup.card_subgroup_dvd_card C
    rwa [card_titsD, show (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 325 by norm_num] at this
  have hcop : Nat.Coprime (Nat.card C) 325 := by
    rw [show (325 : ℕ) = 5 ^ 2 * 13 by norm_num]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 ?_) ?_
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (hnot 5 (Or.inl rfl))).symm
    · exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (hnot 13 (Or.inr rfl))).symm
  obtain ⟨m, n, hm, hn, hmn⟩ := Nat.dvd_mul.mp (hcop.dvd_of_dvd_mul_right hdvd)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hn
  exact ⟨i, j, hmn.symm, hj⟩

end Tits

section Main


theorem exists_pGroup_of_titsD {x : titsD} (hx : orderOf x = 3) :
    ∃ P : Subgroup titsD, IsPGroup 3 P ∧
      Subgroup.centralizer ({x} : Set titsD) ≤ Subgroup.normalizer (P : Set titsD) ∧
      ∀ y ∈ Subgroup.centralizer ({x} : Set titsD), y ^ 3 = 1 → y ∈ P := by
  set C := Subgroup.centralizer ({x} : Set titsD) with hC
  have hmemC : ∀ g : titsD, g ∈ C ↔ g * x = x * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff
  set x' : C := ⟨x, (hmemC x).mpr rfl⟩ with hx'
  obtain ⟨a, b, hcard, hb⟩ := exists_card_centralizer_of_titsD hx
  have hzp : ∀ y : C, (y : titsD) ∈ Subgroup.zpowers x → y ∈ Subgroup.zpowers x' := by
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hi)⟩
  obtain ⟨P, hPn, hP3, hPy⟩ := exists_normal_of_central_three (H := C) (x := x')
    (fun g => Subtype.ext ((hmemC g).mp g.2)) (by rw [hx', Subgroup.orderOf_mk, hx]) hcard hb
    (fun y ⟨k, hk⟩ => Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact pow_three_eq_one_of_titsD ⟨k, by simpa using congrArg Subtype.val hk⟩))
    (fun u v hu hv huv => Subtype.ext (eq_of_commute_of_orderOf_three hx
      (by rwa [Subgroup.orderOf_coe]) (by rwa [Subgroup.orderOf_coe]) ((hmemC u).mp u.2)
      ((hmemC v).mp v.2) (congrArg Subtype.val huv)))
    (fun u y hu hy3 hyu => by
      by_contra hyx
      have hyx' : (y : titsD) ∉ Subgroup.zpowers x := fun h => hyx (hzp y h)
      have hy3' : (y : titsD) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
      obtain ⟨E, hE9, hEgen⟩ := exists_card_nine_of_commute hx hy3' hyx' ((hmemC y).mp y.2).symm
      have hux : (u : titsD) * x = x * u := (hmemC u).mp u.2
      have hyu' : (y : titsD) * u = u * y := congrArg Subtype.val hyu
      refine false_of_commute_e9 hE9 (by rwa [Subgroup.orderOf_coe]) fun e he => ?_
      obtain ⟨i, j, rfl⟩ := hEgen e he
      have h1 : x ^ i * (u : titsD) = u * x ^ i :=
        (Commute.zpow_left (show Commute x (u : titsD) from hux.symm) i).eq
      have h2 : (y : titsD) ^ j * u = u * (y : titsD) ^ j :=
        (Commute.zpow_left (show Commute (y : titsD) u from hyu') j).eq
      rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc])
    (by
      obtain ⟨y, hyx, hy3, hyz⟩ := exists_commute_of_titsD hx
      refine ⟨⟨y, (hmemC y).mpr hyx⟩, Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3),
        fun h => hyz ?_⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, by
        have := congrArg Subtype.val hi
        rwa [Subgroup.coe_zpow] at this⟩)
  refine ⟨P.map C.subtype, hP3.map _, fun g hg => ?_, fun y hy hy3 => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    set g' : C := ⟨g, hg⟩ with hg'
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨g' * p * g'⁻¹, hPn.conj_mem p hp g', rfl⟩
    · rintro ⟨q, hq, hqz⟩
      refine ⟨g'⁻¹ * q * g'⁻¹⁻¹, hPn.conj_mem q hq g'⁻¹, ?_⟩
      have hqz' : (q : titsD) = g * z * g⁻¹ := hqz
      change (g⁻¹ * (q : titsD) * g⁻¹⁻¹ : titsD) = z
      rw [hqz']
      group
  · exact ⟨⟨y, hy⟩, hPy _ (Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3)), rfl⟩

theorem k417TitsCentThree_holds : Res417Six.K417TitsCentThree := by
  intro X _ f hX x hx
  obtain ⟨e⟩ := titsModelEquiv X 2 f hX
  refine exists_pGroup_of_mulEquiv e (exists_pGroup_of_titsD ?_)
  have h := orderOf_injective e.toMonoidHom e.injective x
  rw [hx] at h
  simpa using h

end Main

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
