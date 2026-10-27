module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Cent
public import CFSG.RankThree.PartTwo.Sec11.Item424FromD4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A11Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open scoped Pointwise

theorem eq_of_cube_of_mem_zpowers {H : Type} [Group H] (σ : H →* H) (hσ : ∀ z, σ (σ (σ z)) = z)
    {y : H} (hy : y ^ 3 = 1) (h : σ y ∈ Subgroup.zpowers y) : σ y = y := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
  have hy3 : (y : H) ^ (3 : ℤ) = 1 := by exact_mod_cast hy
  have hmod : ∀ m : ℤ, y ^ m = y ^ (m % 3) := fun m => zpow_eq_zpow_emod m hy3
  have h2 : σ (σ y) = y ^ (j * j) := by rw [← hj, map_zpow, ← hj, ← zpow_mul]
  have h3 : σ (σ (σ y)) = y ^ (j * j * j) := by
    rw [h2, map_zpow, ← hj, ← zpow_mul, mul_comm j (j * j)]
  rw [hσ] at h3
  have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hj3 with h0 | h1 | h2'
  ·
    have hs : σ y = 1 := by rw [← hj, hmod, h0, zpow_zero]
    have : y = 1 := by rw [← hσ y, hs, map_one, map_one]
    rw [hs, this]
  · rw [← hj, hmod, h1, zpow_one]
  ·
    have hjjj : (j * j * j) % 3 = 2 := by
      have : (j * j * j) % 3 = ((j % 3) * (j % 3) * (j % 3)) % 3 := by
        simp [Int.mul_emod]
      rw [this, h2']
      norm_num
    have hy2 : y = y ^ (2 : ℤ) := by rw [hmod (j * j * j), hjjj] at h3; exact h3
    have hy1 : y = 1 := by
      have : y * y = y * 1 := by
        conv_rhs => rw [hy2]
        rw [mul_one, zpow_two]
      exact mul_left_cancel this
    rw [hy1, map_one]

theorem conj_eq_of_mem_zpowers {G : Type} [Group G] {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (h : x * y * x⁻¹ ∈ Subgroup.zpowers y) : x * y * x⁻¹ = y := by
  have hσ : ∀ z, (MulAut.conj x).toMonoidHom ((MulAut.conj x).toMonoidHom
      ((MulAut.conj x).toMonoidHom z)) = z := by
    intro z
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * (x * (x * z * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * z * (x ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = z := by rw [hx]; group
  exact eq_of_cube_of_mem_zpowers (MulAut.conj x).toMonoidHom hσ hy h

section A5

def c5 : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩
def v51 : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩
def v52 : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩

def V5 : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | x = 1 ∨ x = v51 ∨ x = v52 ∨ x = v51 * v52}
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> decide

theorem c5_pow_three : c5 ^ 3 = 1 := by decide

theorem c5_ne_one : c5 ≠ 1 := by decide

theorem sq_of_mem_V5 : ∀ x ∈ V5, x ^ 2 = 1 := by
  rintro x (rfl | rfl | rfl | rfl) <;> decide

theorem v51_mem_V5 : v51 ∈ V5 := Or.inr (Or.inl rfl)

theorem v51_ne_one : v51 ≠ 1 := by decide

theorem c5_mem_normalizer_V5 : c5 ∈ Subgroup.normalizer (V5 : Set (alternatingGroup (Fin 5))) := by
  refine Subgroup.mem_normalizer_fintype ?_
  rintro x (rfl | rfl | rfl | rfl)
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inr (Or.inr (by decide)))
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (Or.inl (by decide)))

end A5

section A5Type

variable {K : Type} [Group K] [Finite K]

theorem a5_facts (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5)) :
    (∀ z ∈ Subgroup.center K, z ^ 3 = 1 → z = 1) ∧
    (∀ P : Subgroup K, IsPGroup 3 P → Nat.card P ≤ 3) ∧
    (∃ k : K, k ^ 3 = 1 ∧ k ≠ 1 ∧ ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      k ∈ Subgroup.normalizer (U : Set K)) ∧
    aschbacherSolvableCore 3 K = CFSG.pCore 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 K with hO
  set π := QuotientGroup.mk' O with hπ
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hO2.exists_card_eq
  have hZA5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hZO : Subgroup.center K ≤ O := by
    intro z hz
    have h1 : e (π z) ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      obtain ⟨g'', rfl⟩ := QuotientGroup.mk'_surjective O g'
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g'']
    rw [hZA5, Subgroup.mem_bot, map_eq_one_iff _ e.injective, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have hO3 : ∀ z ∈ O, z ^ 3 = 1 → z = 1 := by
    intro z hzO hz3
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hO2) ⟨z, hzO⟩
    have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rw [← Subgroup.orderOf_mk z hzO, hm] at hd
    have h1 : 2 ^ m = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact h
      · exfalso
        have : 2 ∣ 3 := by
          rcases m with _ | m
          · simp at h
          · exact ⟨2 ^ m, by rw [← h, pow_succ]; ring⟩
        omega
    have hord : orderOf z = 1 := by rw [← Subgroup.orderOf_mk z hzO, hm, h1]
    exact orderOf_eq_one_iff.mp hord
  have hcard : Nat.card K = 60 * 2 ^ n := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, Nat.card_congr e.toEquiv, hn,
      Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  refine ⟨fun z hz hz3 => hO3 z (hZO hz) hz3, ?_, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : 3 ^ k ∣ 60 * 2 ^ n := by
      rw [← hk, ← hcard]
      exact Subgroup.card_subgroup_dvd_card P
    rw [hk]
    by_contra hlt
    push Not at hlt
    have hk2 : 2 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k <;> norm_num at hlt
    have h9 : 9 ∣ 15 * 2 ^ (n + 2) := by
      have : 60 * 2 ^ n = 15 * 2 ^ (n + 2) := by ring
      rw [← this]
      exact (pow_dvd_pow 3 hk2).trans hdvd
    have hcop : Nat.Coprime 9 (2 ^ (n + 2)) := Nat.Coprime.pow_right _ (by norm_num)
    have := hcop.dvd_of_dvd_mul_right h9
    norm_num at this
  ·
    set c : K ⧸ O := e.symm c5 with hc
    have hc3 : c ^ 3 = 1 := by rw [hc, ← map_pow, c5_pow_three, map_one]
    have hc1 : c ≠ 1 := by
      rw [hc, Ne, map_eq_one_iff _ e.symm.injective]
      exact c5_ne_one
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective O c
    set k := y ^ (2 ^ n) with hkdef
    have hy3 : y ^ 3 ∈ O := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hy, hc3]
    have hpowO : ∀ z ∈ O, z ^ (2 ^ n) = 1 := by
      intro z hz
      have := pow_card_eq_one' (G := O) (x := ⟨z, hz⟩)
      rw [hn] at this
      simpa using congrArg Subtype.val this
    have hk3 : k ^ 3 = 1 := by
      rw [hkdef, ← pow_mul, mul_comm, pow_mul]
      exact hpowO _ hy3
    have hπk : π k = c ^ (2 ^ n) := by rw [hkdef, map_pow, hy]
    have hk1 : k ≠ 1 := by
      intro h1
      have h2 : c ^ (2 ^ n) = 1 := by rw [← hπk, h1, map_one]
      have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
      have h3 : 3 ∣ 2 ^ n := by rw [← hoc]; exact orderOf_dvd_of_pow_eq_one h2
      have := (Nat.prime_three.dvd_of_dvd_pow h3)
      norm_num at this
    set V : Subgroup (K ⧸ O) := V5.map e.symm.toMonoidHom with hV
    set U : Subgroup K := V.comap π with hU
    refine ⟨k, hk3, hk1, U, ?_, ?_, ?_⟩
    ·
      intro hbot
      obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective O (e.symm v51)
      have huU : u ∈ U := by
        show π u ∈ V
        rw [hu]
        exact ⟨v51, v51_mem_V5, rfl⟩
      rw [hbot, Subgroup.mem_bot] at huU
      have : e.symm v51 = 1 := by rw [← hu, huU, map_one]
      exact v51_ne_one ((map_eq_one_iff _ e.symm.injective).mp this)
    ·
      refine IsPGroup.iff_orderOf.mpr fun u => ?_
      have hu2 : (u : K) ^ 2 ∈ O := by
        have hmem : π (u : K) ∈ V := u.2
        obtain ⟨v, hv, hve⟩ := hmem
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
        change (π (u : K)) ^ 2 = 1
        rw [← hve]
        change (e.symm v) ^ 2 = 1
        rw [← map_pow, sq_of_mem_V5 v hv, map_one]
      have hu4 : u ^ (2 ^ (n + 1)) = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul]
        exact hpowO _ hu2
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu4)
      exact ⟨m, hm⟩
    ·
      refine Subgroup.le_normalizer_comap π ?_
      show π k ∈ Subgroup.normalizer (V : Set (K ⧸ O))
      rw [hπk]
      refine Subgroup.pow_mem _ ?_ _
      rw [hV, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨c5, c5_mem_normalizer_V5, rfl⟩
  ·
    refine le_antisymm ((CFSG.RankThree.PartTwo.Sec4.aschbacherSolvableCore_le_center hK).trans
      hZO) ?_
    exact (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.2.2.2.2
      2 Nat.prime_two (by norm_num)

theorem isType424_of_a5 (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 5)) :
    Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K) := by
  have hθ := (a5_facts hK e).2.2.2
  obtain ⟨ι⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 2) (f := 2)
    (GaloisField.card 2 2 (by norm_num))
  obtain ⟨κ⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
  exact Or.inl ⟨2, by norm_num, ⟨((QuotientGroup.quotientMulEquivOfEq hθ).trans e).trans
    (κ.symm.trans ι)⟩⟩

end A5Type

section Config

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_centralizer_of {d g x : G} (hg : g⁻¹ * d * g⁻¹⁻¹ ∈ Subgroup.zpowers d)
    (hx : x ∈ Subgroup.centralizer {d}) : g * x * g⁻¹ ∈ Subgroup.centralizer {d} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [inv_inv] at hj
  have hxj : x * d ^ j = d ^ j * x := (Commute.zpow_right (show Commute x d from hx) j).eq
  calc g * x * g⁻¹ * d = g * x * (g⁻¹ * d * g) * g⁻¹ := by group
    _ = g * (x * d ^ j) * g⁻¹ := by rw [← hj]; group
    _ = g * (d ^ j * x) * g⁻¹ := by rw [hxj]
    _ = g * (g⁻¹ * d * g) * x * g⁻¹ := by rw [← hj]; group
    _ = d * (g * x * g⁻¹) := by group

theorem mem_normalizer_inf_centralizer {L : Subgroup G} {d n : G}
    (hnL : n ∈ Subgroup.normalizer (L : Set G))
    (hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    n ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
  have h1 : n⁻¹ * d * n⁻¹⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnd) d).mp (Subgroup.mem_zpowers d)
  have h2 : n⁻¹⁻¹ * d * n⁻¹⁻¹⁻¹ ∈ Subgroup.zpowers d := by
    rw [inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp hnd d).mp (Subgroup.mem_zpowers d)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxL, hxd⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hnL x).mp hxL, conj_mem_centralizer_of h1 hxd⟩
  · rintro ⟨hxL, hxd⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hnL x).mpr hxL, ?_⟩
    have := conj_mem_centralizer_of h2 hxd
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem mem_normalizer_zpowers_of_commute {d n : G} (h : n * d = d * n) :
    n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hx)
    exact ((Commute.zpow_left (show Commute d n from h.symm) k)).eq)

theorem a5_facts_map {M : Subgroup G} {K : Subgroup M} (hK : IsComponent K)
    (e5 : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) :
    (∀ z ∈ K.map M.subtype, (∀ y ∈ K.map M.subtype, z * y = y * z) → z ^ 3 = 1 → z = 1) ∧
    (∀ P : Subgroup G, P ≤ K.map M.subtype → IsPGroup 3 P → Nat.card P ≤ 3) ∧
    (∃ k ∈ K.map M.subtype, k ^ 3 = 1 ∧ k ≠ 1 ∧ ∃ U : Subgroup G, U ≤ K.map M.subtype ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ k ∈ Subgroup.normalizer (U : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, hP, ⟨k, hk3, hk1, U, hU1, hU2, hkU⟩, -⟩ := a5_facts hK.1 e5
  set f : ↥K →* G := M.subtype.comp K.subtype with hfdef
  have hf : Function.Injective f := M.subtype_injective.comp K.subtype_injective
  have hrange : f.range = K.map M.subtype := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hmemf : ∀ y : ↥K, f y ∈ K.map M.subtype := fun y => hrange ▸ ⟨y, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hzc hz3
    rw [← hrange] at hz
    obtain ⟨z₀, rfl⟩ := hz
    have hcen : z₀ ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hf
      rw [map_mul, map_mul]
      exact (hzc (f g) (hmemf g)).symm
    have h3 : z₀ ^ 3 = 1 := hf (by rw [map_pow, hz3, map_one])
    rw [hZ z₀ hcen h3, map_one]
  · intro P hPK hP3
    have hle : P ≤ f.range := hrange ▸ hPK
    have hmap : (P.comap f).map f = P := Subgroup.map_comap_eq_self hle
    have hcard : Nat.card (P.comap f) = Nat.card P := by
      conv_rhs => rw [← hmap]
      rw [Subgroup.card_map_of_injective hf]
    obtain ⟨j, hj⟩ := hP3.exists_card_eq
    have hP3' : IsPGroup 3 (P.comap f) := IsPGroup.of_card (n := j) (by rw [hcard, hj])
    rw [← hcard]
    exact hP _ hP3'
  · refine ⟨f k, hmemf k, by rw [← map_pow, hk3, map_one], fun h => hk1 (hf (by
      rw [h, map_one])), U.map f, ?_, ?_, hU2.map f, ?_⟩
    · rw [← hrange, MonoidHom.range_eq_map]
      exact Subgroup.map_mono le_top
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hf]
    · refine Subgroup.mem_normalizer_fintype ?_
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨k * u * k⁻¹, (Subgroup.mem_normalizer_iff.mp hkU u).mp hu, ?_⟩
      rw [map_mul, map_mul, map_inv]

theorem maximal_sup_zpowers (hEF : partTwoE G = partTwoF G) {L K' U : Subgroup G} {a d k : G}
    (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) (hd3 : d ^ 3 = 1) (hadc : a * d = d * a)
    (haC : a ∈ Subgroup.centralizer (L : Set G)) (hdC : d ∉ Subgroup.centralizer (L : Set G))
    (hK'L : K' ≤ L) (hK'd : K' ≤ Subgroup.centralizer {d})
    (hZ : ∀ z ∈ K', (∀ y ∈ K', z * y = y * z) → z ^ 3 = 1 → z = 1)
    (hkK : k ∈ K') (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) (hUK : U ≤ K') (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hkU : k ∈ Subgroup.normalizer (U : Set G)) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k) ∧
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k) = 27 ∧
    ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B →
      Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k ≤ B →
      B = Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdC (Subgroup.one_mem _)
  have hEa := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers ha3
  have hEd := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hd3
  have hEk := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hk3
  have hcad : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a d from hadc) i j).eq
  have hEad := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hEa hEd hcad
  have haK' : a ∈ Subgroup.centralizer (K' : Set G) := Subgroup.centralizer_le hK'L haC
  have hdK' : d ∈ Subgroup.centralizer (K' : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => Subgroup.mem_centralizer_singleton_iff.mp (hK'd hh)
  have hadC : Subgroup.zpowers a ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer (K' : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr haK') (Subgroup.zpowers_le.mpr hdK')
  have hcadk : ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d, ∀ y ∈ Subgroup.zpowers k,
      x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hadC hx) y (Subgroup.zpowers_le.mpr hkK hy)).symm
  have hE := CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hEad hEk hcadk
  have hca : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hcd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hck : Nat.card (Subgroup.zpowers k) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hk3 hk1]
  have hinf1 : Subgroup.zpowers a ⊓ Subgroup.zpowers d = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxd⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hEd.2 x hxd
    have heq : Subgroup.zpowers x = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxd)
        (by rw [hcd, Nat.card_zpowers, orderOf_eq_prime hx3 hx1])
    have hxC : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr haC) hxa)
    exact hdC (hxC (heq ▸ Subgroup.mem_zpowers d))
  have hinf2 : (Subgroup.zpowers a ⊔ Subgroup.zpowers d) ⊓ Subgroup.zpowers k = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxad, hxk⟩
    rw [Subgroup.mem_bot]
    exact hZ x (Subgroup.zpowers_le.mpr hkK hxk)
      (fun y hy => (Subgroup.mem_centralizer_iff.mp (hadC hxad) y hy).symm) (hEk.2 x hxk)
  have hcard9 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d) = 9 := by
    rw [Ronan148R.card_sup_of_commute_of_inf hcad hinf1, hca, hcd]
  have hcard : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k) = 27 := by
    rw [Ronan148R.card_sup_of_commute_of_inf hcadk hinf2, hcard9, hck]
  have hEU : Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k ≤
      Subgroup.normalizer (U : Set G) := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hkU)
    exact hadC.trans ((Subgroup.centralizer_le hUK).trans (Subgroup.centralizer_le_normalizer _))
  have hmemE : Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k ∈ partTwoE G :=
    ⟨hE, hcard, U, hU1, hU2, hEU⟩
  rw [hEF] at hmemE
  exact ⟨hE, hcard, hmemE.2.1⟩

theorem cent_a5_structure (hEF : partTwoE G = partTwoF G) {A L : Subgroup G} (hA : Late.IsE27 A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {d : G} (hdA : d ∈ A)
    (hLd : ¬ L ≤ Subgroup.centralizer {d})
    {K : Subgroup ↥(L ⊓ Subgroup.centralizer {d})} (hK : IsComponent K)
    (e5 : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    {a : G} (haA : a ∈ A) (haC : a ∈ Subgroup.centralizer (L : Set G)) (ha1 : a ≠ 1) :
    A ≤ Subgroup.normalizer ((K.map (L ⊓ Subgroup.centralizer {d}).subtype : Subgroup G) :
      Set G) ∧
    ∃ k₀ ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype, k₀ ≠ 1 ∧ k₀ ^ 3 = 1 ∧
      A = Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k₀ ∧
      ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ, hP3, ⟨k, hkK, hk3, hk1, U, hUK, hU1, hU2, hkU⟩⟩ := a5_facts_map hK e5
  set K' := K.map (L ⊓ Subgroup.centralizer {d}).subtype with hK'
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hdC : d ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    apply hLd
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h y hy)
  have hmax := fun (k : G) (hkK : k ∈ K') (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) (U : Subgroup G)
      (hUK : U ≤ K') (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
      (hkU : k ∈ Subgroup.normalizer (U : Set G)) =>
    maximal_sup_zpowers hEF ha1 (hA3 a haA) (hA3 d hdA) (hAc a haA d hdA) haC hdC hK'L hK'd hZ
      hkK hk1 hk3 hUK hU1 hU2 hkU
  obtain ⟨hEel, -, hEmax⟩ := hmax k hkK hk1 hk3 U hUK hU1 hU2 hkU
  have haM : ∀ y ∈ L ⊓ Subgroup.centralizer {d}, a * y = y * a := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp haC y hy.1).symm
  have hdM : ∀ y ∈ L ⊓ Subgroup.centralizer {d}, d * y = y * d := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  have hAK' : A ≤ Subgroup.normalizer (K' : Set G) := by
    intro x hx
    have hxd : x * d = d * x := hAc x hx d hdA
    have hxM : x ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) :=
      mem_normalizer_inf_centralizer (hAN hx) (mem_normalizer_zpowers_of_commute hxd)
    set ψ := (L ⊓ Subgroup.centralizer {d}).normalizerMonoidHom ⟨x, hxM⟩ with hψ
    have hψa : ∀ m : ↥(L ⊓ Subgroup.centralizer {d}), ((ψ m : ↥(L ⊓ Subgroup.centralizer {d})) : G) = x * m * x⁻¹ := fun _ => rfl
    have hK₁ : IsComponent (K.map ψ.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv ψ hK
    set K₁' := (K.map ψ.toMonoidHom).map (L ⊓ Subgroup.centralizer {d}).subtype with hK₁'
    have hmapK₁ : K₁' = K'.map (MulAut.conj x).toMonoidHom := by
      rw [hK₁', hK', Subgroup.map_map, Subgroup.map_map]
      congr 1
    have hK₁'M : K₁' ≤ L ⊓ Subgroup.centralizer {d} := Subgroup.map_subtype_le _
    rcases CFSG.LocalCores.distinct_components_commute hK hK₁ with heq | hcomm
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change K'.map (MulAut.conj x).toMonoidHom = K'
      rw [← hmapK₁, hK₁', ← heq]
    · exfalso
      have hcomm' : ∀ y ∈ K', ∀ z ∈ K₁', y * z = z * y := by
        rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
        have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hy
        exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hyC z hz).symm)
      obtain ⟨k₁, hk₁K, hk₁⟩ := hkK
      have hkK' : k ∈ K' := ⟨k₁, hk₁K, hk₁⟩
      have hk₁' : (k₁ : G) = k := hk₁
      have hwK₁ : x * k * x⁻¹ ∈ K₁' :=
        ⟨ψ k₁, ⟨k₁, hk₁K, rfl⟩, by rw [Subgroup.coe_subtype, hψa, hk₁']⟩
      set w := x * k * x⁻¹ with hw
      have hw3 : w ^ 3 = 1 := by rw [hw, conj_pow, hk3, mul_one, mul_inv_cancel]
      have hEw : Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k ≤
          Subgroup.centralizer ({w} : Set G) := by
        refine sup_le (sup_le ?_ ?_) ?_
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
            (haM w (hK₁'M hwK₁)))
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
            (hdM w (hK₁'M hwK₁)))
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
            (hcomm' k hkK' w hwK₁))
      have hEw' : CFSG.Assembly.IsElemAbelian 3
          (Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k ⊔ Subgroup.zpowers w) :=
        CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hEel
          (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hw3) (fun y hy z hz => by
            obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
            exact ((Commute.zpow_right (show Commute y w from
              (Subgroup.mem_centralizer_singleton_iff.mp (hEw hy))) j)).eq)
      have hwE : w ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k := by
        rw [← hEmax _ hEw' le_sup_left]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
      have hEK₁ : Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k ≤
          Subgroup.centralizer (K₁' : Set G) := by
        refine sup_le (sup_le ?_ ?_) ?_
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (haM z (hK₁'M hz)).symm)
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (hdM z (hK₁'M hz)).symm)
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (hcomm' k hkK' z hz).symm)
      have hkZ : ∀ y ∈ K', k * y = y * k := by
        intro y hy
        have hy' : x * y * x⁻¹ ∈ K₁' := by
          rw [hmapK₁]
          exact ⟨y, hy, rfl⟩
        have h := Subgroup.mem_centralizer_iff.mp (hEK₁ hwE) _ hy'
        rw [hw] at h
        calc k * y = x⁻¹ * ((x * k * x⁻¹) * (x * y * x⁻¹)) * x := by group
          _ = x⁻¹ * ((x * y * x⁻¹) * (x * k * x⁻¹)) * x := by rw [h]
          _ = y * k := by group
      exact hk1 (hZ k hkK' hkZ hk3)
  set kK : ↥K' := ⟨k, hkK⟩ with hkKdef
  have hkK3 : orderOf kK = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hk3 hk1
  have hfac : (Nat.card ↥K').factorization 3 = 1 := by
    have hz3 : Nat.card (Subgroup.zpowers kK) = 3 := by rw [Nat.card_zpowers, hkK3]
    obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := 3) (n := 1) (by rw [hz3]; norm_num) :
      IsPGroup 3 (Subgroup.zpowers kK)).exists_le_sylow
    have hQc := Sylow.card_eq_multiplicity Q
    have hle3 : Nat.card (Q : Subgroup ↥K') ≤ 3 := by
      have h := hP3 ((Q : Subgroup ↥K').map K'.subtype) (Subgroup.map_subtype_le _)
        (Q.isPGroup'.map K'.subtype)
      rwa [Subgroup.card_map_of_injective K'.subtype_injective] at h
    have hge3 : 3 ≤ Nat.card (Q : Subgroup ↥K') :=
      calc 3 = Nat.card (Subgroup.zpowers kK) := hz3.symm
        _ ≤ Nat.card (Q : Subgroup ↥K') := Subgroup.card_le_of_le hQ
    have hle3' : 3 ^ (Nat.card ↥K').factorization 3 ≤ 3 := hQc ▸ hle3
    have hge3' : 3 ≤ 3 ^ (Nat.card ↥K').factorization 3 := hQc ▸ hge3
    set f := (Nat.card ↥K').factorization 3 with hf
    rcases Nat.lt_or_ge f 1 with h0 | h1
    · have : f = 0 := by omega
      rw [this] at hge3'
      norm_num at hge3'
    · rcases Nat.eq_or_lt_of_le h1 with h1 | h2
      · exact h1.symm
      · exfalso
        have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h2
        omega
  let φ : ↥A →* MulAut ↥K' := K'.normalizerMonoidHom.comp (Subgroup.inclusion hAK')
  letI : MulAction ↥A (Sylow 3 ↥K') := MulAction.compHom _ φ
  have hApg : IsPGroup 3 ↥A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 ↥K') := by
    have h := card_sylow_modEq_one 3 ↥K'
    rintro ⟨m, hm⟩
    rw [hm, Nat.ModEq] at h
    simp at h
  obtain ⟨P, hP⟩ := hApg.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 ↥K') hnd
  let P₀ : Sylow 3 ↥K' := Sylow.ofCard (Subgroup.zpowers kK)
    (by rw [Nat.card_zpowers, hkK3, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K' P₀ P
  have hPeq : (P : Subgroup ↥K') = Subgroup.zpowers (g * kK * g⁻¹) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact MonoidHom.map_zpowers (MulDistribMulAction.toMonoidEnd (MulAut ↥K') ↥K'
      (MulAut.conj g)) kK
  set k₀ : G := ((g * kK * g⁻¹ : ↥K') : G) with hk₀
  have hk₀K : k₀ ∈ K' := (g * kK * g⁻¹).2
  have hk₀e : k₀ = (g : G) * k * (g : G)⁻¹ := rfl
  have hk₀3 : k₀ ^ 3 = 1 := by rw [hk₀e, conj_pow, hk3, mul_one, mul_inv_cancel]
  have hk₀1 : k₀ ≠ 1 := by
    intro h1
    apply hk1
    have : k = (g : G)⁻¹ * k₀ * (g : G) := by rw [hk₀e]; group
    rw [this, h1]
    group
  have hAk₀ : ∀ x ∈ A, x * k₀ = k₀ * x := by
    intro x hx
    have hfix : (⟨x, hx⟩ : ↥A) • P = P := hP ⟨x, hx⟩
    have h1 : g * kK * g⁻¹ ∈ (P : Subgroup ↥K') := by
      rw [hPeq]
      exact Subgroup.mem_zpowers _
    have h2 : (φ ⟨x, hx⟩) • (g * kK * g⁻¹) ∈ (φ ⟨x, hx⟩) • (P : Subgroup ↥K') :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    have hfix' : ((φ ⟨x, hx⟩) • P : Sylow 3 ↥K') = P := hfix
    rw [← Sylow.pointwise_smul_def, hfix', hPeq, MulAut.smul_def] at h2
    have hmemG : x * k₀ * x⁻¹ ∈ Subgroup.zpowers k₀ := by
      have h3 := Subgroup.mem_map_of_mem K'.subtype h2
      rw [MonoidHom.map_zpowers] at h3
      exact h3
    have h4 := conj_eq_of_mem_zpowers (hA3 x hx) hk₀3 hmemG
    calc x * k₀ = x * k₀ * x⁻¹ * x := by group
      _ = k₀ * x := by rw [h4]
  have hgK : (g : G) ∈ K' := g.2
  set U₀ := U.map (MulAut.conj (g : G)).toMonoidHom with hU₀
  have hU₀K : U₀ ≤ K' := by
    rintro _ ⟨u, hu, rfl⟩
    exact K'.mul_mem (K'.mul_mem hgK (hUK hu)) (K'.inv_mem hgK)
  have hU₀1 : U₀ ≠ ⊥ := by
    rwa [Ne, hU₀, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj (g : G)).injective]
  have hk₀U₀ : k₀ ∈ Subgroup.normalizer (U₀ : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨k * u * k⁻¹, (Subgroup.mem_normalizer_iff.mp hkU u).mp hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hk₀e]
    group
  obtain ⟨-, hE0card, hE0max⟩ := hmax k₀ hk₀K hk₀1 hk₀3 U₀ hU₀K hU₀1 (hU2.map _) hk₀U₀
  have hAE : CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers k₀) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hA.1
      (CFSG.RankThree.PartTwo.Sec13.isElemAbelian_zpowers hk₀3) (fun y hy z hz => by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact ((Commute.zpow_right (show Commute y k₀ from hAk₀ y hy) j)).eq)
  have hE0le : Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k₀ ≤
      A ⊔ Subgroup.zpowers k₀ :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left haA))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hdA))) le_sup_right
  have h1 := hE0max _ hAE hE0le
  have hAle : A ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k₀ :=
    le_sup_left.trans h1.le
  have hAeq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k₀ :=
    Subgroup.eq_of_le_of_card_ge hAle (by rw [hE0card, hA.2])
  refine ⟨hAK', k₀, hk₀K, hk₀1, hk₀3, hAeq, ?_⟩
  intro B hB hAB
  rw [hAeq] at hAB ⊢
  exact hE0max B hB hAB

theorem mem_normalizer_inf_of_structure {A L : Subgroup G} {d a k₀ : G}
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {K : Subgroup ↥(L ⊓ Subgroup.centralizer {d})} (hK : IsComponent K)
    (hZ : ∀ z ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype,
      (∀ y ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype, z * y = y * z) → z ^ 3 = 1 → z = 1)
    (haC : a ∈ Subgroup.centralizer (L : Set G))
    (hk₀K : k₀ ∈ K.map (L ⊓ Subgroup.centralizer {d}).subtype) (hk₀3 : k₀ ^ 3 = 1)
    (hk₀1 : k₀ ≠ 1)
    (hAeq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k₀)
    {n : G} (hnA : n ∈ Subgroup.normalizer (A : Set G))
    (hnL : n ∈ Subgroup.normalizer (L : Set G)) :
    n ∈ Subgroup.normalizer
      ((A ⊓ K.map (L ⊓ Subgroup.centralizer {d}).subtype : Subgroup G) : Set G) := by
  set K' := K.map (L ⊓ Subgroup.centralizer {d}).subtype with hK'
  have hnM : n ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) :=
    mem_normalizer_inf_centralizer hnL (hN hnA)
  set ψ := (L ⊓ Subgroup.centralizer {d}).normalizerMonoidHom ⟨n, hnM⟩ with hψ
  have hψa : ∀ m : ↥(L ⊓ Subgroup.centralizer {d}),
      ((ψ m : ↥(L ⊓ Subgroup.centralizer {d})) : G) = n * m * n⁻¹ := fun _ => rfl
  have hK₂ : IsComponent (K.map ψ.toMonoidHom) := CFSG.LocalCores.isComponent_map_mulEquiv ψ hK
  set K₂' := (K.map ψ.toMonoidHom).map (L ⊓ Subgroup.centralizer {d}).subtype with hK₂'
  have hmapK₂ : K₂' = K'.map (MulAut.conj n).toMonoidHom := by
    rw [hK₂', hK', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hK₂'M : K₂' ≤ L ⊓ Subgroup.centralizer {d} := Subgroup.map_subtype_le _
  have hnK' : n ∈ Subgroup.normalizer (K' : Set G) := by
    rcases CFSG.LocalCores.distinct_components_commute hK hK₂ with heq | hcomm
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change K'.map (MulAut.conj n).toMonoidHom = K'
      rw [← hmapK₂, hK₂', ← heq]
    · exfalso
      have hcomm' : ∀ y ∈ K', ∀ z ∈ K₂', y * z = z * y := by
        rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
        have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hy
        exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hyC z hz).symm)
      have hAK₂ : A ≤ Subgroup.centralizer (K₂' : Set G) := by
        rw [hAeq]
        refine sup_le (sup_le ?_ ?_) ?_
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (Subgroup.mem_centralizer_iff.mp haC z (hK₂'M hz).1))
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (Subgroup.mem_centralizer_singleton_iff.mp (hK₂'M hz).2))
        · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun z hz =>
            (hcomm' k₀ hk₀K z hz).symm)
      have hk₀A : k₀ ∈ A := by
        rw [hAeq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k₀)
      have hw : n * k₀ * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnA k₀).mp hk₀A
      have hkZ : ∀ y ∈ K', k₀ * y = y * k₀ := by
        intro y hy
        have hy' : n * y * n⁻¹ ∈ K₂' := by
          rw [hmapK₂]
          exact ⟨y, hy, rfl⟩
        have h := Subgroup.mem_centralizer_iff.mp (hAK₂ hw) _ hy'
        calc k₀ * y = n⁻¹ * ((n * k₀ * n⁻¹) * (n * y * n⁻¹)) * n := by group
          _ = n⁻¹ * ((n * y * n⁻¹) * (n * k₀ * n⁻¹)) * n := by rw [h]
          _ = y * k₀ := by group
      exact hk₀1 (hZ k₀ hk₀K hkZ hk₀3)
  refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hnA x).mp hx.1
  · exact (Subgroup.mem_normalizer_iff.mp hnK' x).mp hx.2

theorem inf_thetaQuotCentralizer_of_structure {A L K' : Subgroup G} {d a k₀ : G}
    (hA : Late.IsE27 A) (hL : IsComponent L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (haA : a ∈ A) (ha1 : a ≠ 1) (haC : a ∈ Subgroup.centralizer (L : Set G)) (hdA : d ∈ A)
    (hdC : d ∉ Subgroup.centralizer (L : Set G))
    (hK'L : K' ≤ L) (hK'd : K' ≤ Subgroup.centralizer {d})
    (hZ : ∀ z ∈ K', (∀ y ∈ K', z * y = y * z) → z ^ 3 = 1 → z = 1)
    (hk₀K : k₀ ∈ K') (hk₀3 : k₀ ^ 3 = 1) (hk₀1 : k₀ ≠ 1) (hk₀A : k₀ ∈ A) :
    A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hdC (Subgroup.one_mem _)
  have hθC : A ⊓ Sec4.thetaQuotCentralizer L ≤ A ⊓ Subgroup.centralizer (L : Set G) := by
    rintro x ⟨hxA, hxθ⟩
    refine ⟨hxA, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hxθ
    have h1 := Sec4.eq_one_of_thetaQuotMulAut_eq_one hL.1 hy
    change (y : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) h1
    change (y : G) * l * (y : G)⁻¹ = l at h2
    calc l * (y : G) = (y : G) * l * (y : G)⁻¹ * (y : G) := by rw [h2]
      _ = (y : G) * l := by group
  set B := A ⊓ Subgroup.centralizer (L : Set G) with hB
  have haB : a ∈ B := ⟨haA, haC⟩
  have hBd : B ⊓ Subgroup.zpowers d = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxd⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hA3 x hxB.1
    have heq : Subgroup.zpowers x = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxd)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1,
          orderOf_eq_prime (hA3 d hdA) hd1])
    exact hdC ((Subgroup.zpowers_le.mpr hxB.2) (heq ▸ Subgroup.mem_zpowers d))
  have hcBd : ∀ x ∈ B, ∀ y ∈ Subgroup.zpowers d, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx.1⟩
      ⟨y, (Subgroup.zpowers_le.mpr hdA) hy⟩)
  have hBcard : Nat.card B ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have hBdvd : Nat.card B ∣ 27 := hA.2 ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hBi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card B ∣ 3 ^ 3 by simpa using hBdvd)
    have h9 : 9 ≤ Nat.card B := by
      rw [hBi] at hgt ⊢
      have hi2 : 2 ≤ i := by
        by_contra h
        push Not at h
        interval_cases i <;> norm_num at hgt
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
    have hsup := Ronan148R.card_sup_of_commute_of_inf hcBd hBd
    rw [Nat.card_zpowers, orderOf_eq_prime (hA3 d hdA) hd1] at hsup
    have hle : B ⊔ Subgroup.zpowers d ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr hdA)
    have hAeq : B ⊔ Subgroup.zpowers d = A :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hsup, hA.2]; omega)
    have hAK' : A ≤ Subgroup.centralizer (K' : Set G) := by
      rw [← hAeq]
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · exact fun x hx => Subgroup.centralizer_le hK'L hx.2
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
          Subgroup.mem_centralizer_singleton_iff.mp (hK'd hh)
    exact hk₀1 (hZ k₀ hk₀K (fun y hy => (Subgroup.mem_centralizer_iff.mp (hAK' hk₀A) y hy).symm)
      hk₀3)
  have hBeq : B = Subgroup.zpowers a := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haB) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (hA3 a haA) ha1]
    exact hBcard
  refine le_antisymm (hθC.trans hBeq.le) (Subgroup.zpowers_le.mpr ⟨haA, ?_⟩)
  change a ∈ Sec4.thetaQuotCentralizer L
  rw [Sec6.mem_thetaQuotCentralizer_iff]
  refine ⟨Subgroup.centralizer_le_normalizer _ haC, fun l hl => ?_⟩
  have hc : a * l = l * a := (Subgroup.mem_centralizer_iff.mp haC l hl).symm
  rw [hc, mul_inv_cancel_right, inv_mul_cancel]
  exact Subgroup.one_mem _

end Config

section Main

theorem autIn_cube_eq_one
    {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a d k₀ : G}
    (hA : Late.IsE27 A) (hAeq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers k₀)
    (hnorm : ∀ h ∈ L, h ∈ Subgroup.normalizer (A : Set G) →
      h * a * h⁻¹ ∈ Subgroup.zpowers a ∧ h * d * h⁻¹ ∈ Subgroup.zpowers d ∧
        h * k₀ * h⁻¹ ∈ Subgroup.zpowers k₀)
    {σ : MulAut ↥A} (hσ : σ ∈ autIn L A) (hσ3 : σ ^ 3 = 1) : σ = 1 := by
  obtain ⟨h, hhN, hhL, rfl⟩ := mem_autIn_iff.mp hσ
  set σ' := A.normalizerMonoidHom ⟨h, hhN⟩ with hσ'
  have hσa : ∀ y : ↥A, ((σ' y : ↥A) : G) = h * y * h⁻¹ := fun _ => rfl
  have hcube : ∀ z : ↥A, σ'.toMonoidHom (σ'.toMonoidHom (σ'.toMonoidHom z)) = z := by
    intro z
    have h1 := congrArg (fun τ : MulAut ↥A => τ z) hσ3
    simpa [pow_succ] using h1
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hfix : ∀ (g : G) (hg : g ∈ A), h * g * h⁻¹ ∈ Subgroup.zpowers g →
      σ' ⟨g, hg⟩ = ⟨g, hg⟩ := by
    intro g hg hmem
    refine eq_of_cube_of_mem_zpowers σ'.toMonoidHom hcube
      (Subtype.ext (by simpa using hA3 g hg)) ?_
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by
      rw [Subgroup.coe_zpow]
      exact hj)⟩
  obtain ⟨hna, hnd, hnk⟩ := hnorm h hhL hhN
  have haA : a ∈ A := by rw [hAeq]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_zpowers a))
  have hdA : d ∈ A := by rw [hAeq]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers d))
  have hkA : k₀ ∈ A := by rw [hAeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k₀)
  set F := σ'.toMonoidHom.eqLocus (MonoidHom.id ↥A) with hF
  have hAF : A ≤ F.map A.subtype := by
    conv_lhs => rw [hAeq]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr ⟨⟨a, haA⟩, hfix a haA hna, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨⟨d, hdA⟩, hfix d hdA hnd, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨⟨k₀, hkA⟩, hfix k₀ hkA hnk, rfl⟩
  ext y
  obtain ⟨z, hzF, hzy⟩ := hAF y.2
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  have h1 : σ' z = z := hzF
  rw [h1]
  rfl

theorem exists_cube_of_perm3
    {X : Type} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    ∃ x : X, x ^ 3 = 1 ∧ x ≠ 1 :=
  ⟨e.symm (finRotate 3), by rw [← map_pow, show finRotate 3 ^ 3 = 1 by decide, map_one],
    fun h => absurd ((map_eq_one_iff e.symm e.symm.injective).mp h) (by decide)⟩

theorem exists_cube_of_dihedral6
    {X : Type} [Group X] (e : X ≃* DihedralGroup 6) :
    ∃ x : X, x ^ 3 = 1 ∧ x ≠ 1 :=
  ⟨e.symm (DihedralGroup.r 2), by
    rw [← map_pow, show (DihedralGroup.r 2 : DihedralGroup 6) ^ 3 = 1 by decide, map_one],
    fun h => absurd ((map_eq_one_iff e.symm e.symm.injective).mp h) (by decide)⟩

theorem false_of_cent_a5
    {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    {A : Subgroup G} (hA : Late.IsE27 A) (hEF : partTwoE G = partTwoF G)
    {L : Subgroup G} (hL : IsComponent L) {d : G} (hdA : d ∈ A)
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hLd : ¬ L ≤ Subgroup.centralizer {d})
    {K : Subgroup ↥(L ⊓ Subgroup.centralizer {d})} (hK : IsComponent K)
    (e5 : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))
    (hCA : A ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ⟨haA, haC⟩, ha1⟩ : ∃ a ∈ A ⊓ Subgroup.centralizer (L : Set G), a ≠ 1 := by
    by_contra h
    push Not at h
    exact hCA (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  obtain ⟨hZ, hP3, -⟩ := a5_facts_map hK e5
  obtain ⟨-, k₀, hk₀K, hk₀1, hk₀3, hAeq, hAmax⟩ :=
    cent_a5_structure hEF hA hAN hdA hLd hK e5 haA haC ha1
  set K' := K.map (L ⊓ Subgroup.centralizer {d}).subtype with hK'
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have hdC : d ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    apply hLd
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h y hy)
  have hk₀A : k₀ ∈ A := by rw [hAeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers k₀)
  have hCAeq : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers a :=
    inf_thetaQuotCentralizer_of_structure hA hL hAN haA ha1 haC hdA hdC hK'L hK'd hZ hk₀K hk₀3
      hk₀1 hk₀A
  have hNK : ∀ n ∈ Subgroup.normalizer (A : Set G), n ∈ Subgroup.normalizer (L : Set G) →
      n ∈ Subgroup.normalizer ((A ⊓ K' : Subgroup G) : Set G) := fun n hnA hnL =>
    mem_normalizer_inf_of_structure hN hK hZ haC hk₀K hk₀3 hk₀1 hAeq hnA hnL
  have hAK'eq : A ⊓ K' = Subgroup.zpowers k₀ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hk₀A, hk₀K⟩) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hk₀3 hk₀1]
    refine hP3 _ inf_le_right ?_
    refine IsPGroup.iff_orderOf.mpr fun x => ?_
    have hx3 : (x : G) ^ 3 = 1 := hA.1.2 x x.2.1
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx3))
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hread : ∀ σ ∈ autIn L A, σ ^ 3 = 1 → σ = 1 := by
    intro σ hσ hσ3
    refine autIn_cube_eq_one hA hAeq (fun h hhL hhN => ⟨?_, ?_, ?_⟩) hσ hσ3
    · have hc : h * a = a * h := Subgroup.mem_centralizer_iff.mp haC h hhL
      rw [hc, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers a
    · exact (Subgroup.mem_normalizer_iff.mp (hN hhN) d).mp (Subgroup.mem_zpowers d)
    · have h1 := hNK h hhN (Subgroup.le_normalizer hhL)
      rw [hAK'eq] at h1
      exact (Subgroup.mem_normalizer_iff.mp h1 k₀).mp (Subgroup.mem_zpowers k₀)
  set C := L ⊔ A with hCdef
  have hLC : L ≤ C := le_sup_left
  have hAC : A ≤ C := le_sup_right
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hAN
  have hC4 : SectionFourHyp C := Sec4.sectionFourHyp_subgroup hG C
  set A' := A.subgroupOf C with hA'def
  have hA'27 : Nat.card A' = 27 := by
    rw [hA'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA.2]
  have hAmax' : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' :=
    Sec11.maximal_subgroupOf_of_le hAmax hA.1 hAC
  have hEF' : partTwoE C = partTwoF C := Sec11.partTwoE_eq_partTwoF_subgroup hEF C
  set L' := L.subgroupOf C with hL'def
  have hL' : L' ∈ thetaComponents 3 C :=
    mem_thetaComponents_of_isComponent3 (CFSG.LocalCores.component_overgroup hL hLC)
  set a' : C := ⟨a, hAC haA⟩ with ha'def
  have ha'3 : orderOf a' = 3 := by
    rw [ha'def, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA.1.2 a haA) ha1
  have hCa : C ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sup_le (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp haC l hl)) (fun x hx => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have ha'Z : a' ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hCa g.2))
  have hLmap : L'.map C.subtype = L := by
    rw [hL'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hLC]
  have hθ : ∀ w : C, w ∈ (aschbacherSolvableCore 3 L').map L'.subtype ↔
      (w : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro w
    have e1 := Sec11.inSubgroup_theta_map_subtype_sub L'
    rw [hLmap] at e1
    rw [e1]
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      have : w' = w := Subtype.ext hww'
      rw [← this]
      exact hw'
  have hCA' : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers a : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAN, hCAeq]
  have hsec : Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) =
      (Subgroup.zpowers a' : Set C) := by
    ext z
    have hz : z ∈ Late.sectionCentralizer A' L' ((aschbacherSolvableCore 3 L').map L'.subtype) ↔
        (z : G) ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      constructor
      · rintro ⟨hzA, hzL⟩
        refine ⟨Subgroup.mem_subgroupOf.mp hzA, fun y hy => ?_⟩
        have := (hθ _).mp (hzL ⟨y, hLC hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact this
      · rintro ⟨hzA, hzY⟩
        refine ⟨Subgroup.mem_subgroupOf.mpr hzA, fun y hy => (hθ _).mpr ?_⟩
        have := hzY (y : G) (Subgroup.mem_subgroupOf.mp hy)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact this
    rw [hz, hCA', SetLike.mem_coe, SetLike.mem_coe]
    constructor
    · intro h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [ha'def] using hk)⟩
    · intro h1
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simp [ha'def]⟩
  set c' : C := ⟨d, hAC hdA⟩ with hc'def
  have hc'A : c' ∈ A' := Subgroup.mem_subgroupOf.mpr hdA
  have hc'a : c' ∉ Subgroup.zpowers a' := by
    intro hc'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'
    apply hdC
    have hk' : a ^ k = d := by simpa [ha'def, hc'def] using congrArg Subtype.val hk
    rw [← hk']
    exact Subgroup.zpow_mem _ haC k
  have hK'C : K' ≤ C := hK'L.trans hLC
  set H := L' ⊓ Subgroup.centralizer ({c'} : Set C) with hHdef
  have hHM : H.map C.subtype = L ⊓ Subgroup.centralizer {d} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyL, hyc⟩, rfl⟩
      have hyc' : y * c' = c' * y := Subgroup.mem_centralizer_singleton_iff.mp hyc
      exact ⟨Subgroup.mem_subgroupOf.mp hyL,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyc')⟩
    · rintro ⟨hxL, hxd⟩
      have hxd' : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxd
      exact ⟨⟨x, hLC hxL⟩, ⟨Subgroup.mem_subgroupOf.mpr hxL,
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxd')⟩, rfl⟩
  set K'' := K'.subgroupOf C with hK''def
  have hK''H : K'' ≤ H := by
    intro x hx
    have hxM := hK'M (Subgroup.mem_subgroupOf.mp hx)
    rw [← hHM] at hxM
    obtain ⟨y, hy, hyx⟩ := hxM
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  let ι : ↥(L ⊓ Subgroup.centralizer {d}) ≃* ↥H :=
    ((H.equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hHM)).symm
  have hιsymm : ∀ h : ↥H, ((ι.symm h : ↥(L ⊓ Subgroup.centralizer {d})) : G) = ((h : C) : G) :=
    fun _ => rfl
  have hK''sub : K''.subgroupOf H = K.map ι.toMonoidHom := by
    ext h
    rw [Subgroup.mem_subgroupOf, hK''def, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv]
    constructor
    · rintro ⟨k, hk, hkh⟩
      have : k = ι.symm h := Subtype.ext (by rw [hιsymm]; exact hkh)
      rw [← this]
      exact hk
    · intro hh
      exact ⟨ι.symm h, hh, hιsymm h⟩
  have hK''mem : K'' ∈ thetaComponentsIn H := by
    rw [mem_thetaComponentsIn_iff]
    refine ⟨hK''H, ?_⟩
    rw [hK''sub]
    exact mem_thetaComponents_of_isComponent3 (CFSG.LocalCores.isComponent_map_mulEquiv ι hK)
  have hKT'' : Sec11.IsType424 (↥K'' ⧸ aschbacherSolvableCore 3 ↥K'') := by
    let eK : ↥K'' ≃* ↥K := (Subgroup.subgroupOfEquivOfLe hK'C).trans
      (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm
    exact Sec11.isType424_of_mulEquiv (QuotientGroup.congr _ _ eK
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eK))
      (isType424_of_a5 hK.1 e5)
  have hAKC : A ⊓ K' ≤ C := inf_le_left.trans hAC
  have hAK : A' ⊓ K'' = (A ⊓ K').subgroupOf C := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hNK' : Subgroup.normalizer (A' : Set C) ≤
      Subgroup.normalizer ((A' ⊓ K'' : Subgroup C) : Set C) := by
    intro w hw
    have hw' : (w : G) ∈ Subgroup.normalizer (A : Set G) := by
      have := (Sec13.coe_mem_normalizer_map_iff C (L' := A')).mpr hw
      rwa [hA'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hAC] at this
    rw [hAK]
    refine (Sec13.coe_mem_normalizer_map_iff C).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAKC]
    exact hNK _ hw' (hCN w.2)
  have h4 := Sec11.item4_24M_holds C hC4 A' hAmax' hA'27 hEF' L' hL' a' ha'3 ha'Z hsec c' hc'A
    hc'a K'' hK''mem hKT'' hNK'
  obtain ⟨eAut⟩ := Sec13.nonempty_autIn_subgroupOf_equiv C hLC hAC
  have hfin : ∀ x : ↥(autIn L A), x ^ 3 = 1 → x = 1 := fun x hx3 =>
    Subtype.ext (hread x x.2 (by simpa using congrArg Subtype.val hx3))
  rcases h4 with ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e2⟩⟩ | ⟨-, ⟨e3⟩⟩ | ⟨-, -, ⟨e4⟩⟩
  · obtain ⟨x, hx3, hx1⟩ := exists_cube_of_perm3 (eAut.symm.trans e1)
    exact hx1 (hfin x hx3)
  · obtain ⟨x, hx3, hx1⟩ := exists_cube_of_dihedral6 (eAut.symm.trans e2)
    exact hx1 (hfin x hx3)
  · obtain ⟨x, hx3, hx1⟩ := exists_cube_of_perm3 (eAut.symm.trans e3)
    exact hx1 (hfin x hx3)
  · obtain ⟨x, hx3, hx1⟩ := exists_cube_of_dihedral6 (eAut.symm.trans e4)
    exact hx1 (hfin x hx3)

theorem false_of_on_of_not_nineteen
    {S : Type} [Group S] (h19 : ¬ 19 ∣ Nat.card S)
    {G : Type} [Group G] [Finite G] (hθ : aschbacherSolvableCore 3 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) (eL : L ⧸ Subgroup.center L ≃* S) {d : G}
    {K : Subgroup ↥(L ⊓ Subgroup.centralizer {d})}
    (hext : IsExtOf (↥K ⧸ CFSG.pCore 2 ↥K) Blueprint.NativeSporadic.ON
      (Multiplicative (ZMod 3))) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := hext
  have h19ON : 19 ∣ Nat.card Blueprint.NativeSporadic.ON := by
    rw [CFSG.Sporadic.ON.card_ON_eq]
    norm_num
  have h19Q : 19 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv]
    exact h19ON.mul_right _
  have h19K : 19 ∣ Nat.card ↥K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    exact h19Q.mul_right _
  have h19L : 19 ∣ Nat.card ↥L :=
    h19K.trans ((Subgroup.card_subgroup_dvd_card K).trans
      (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨m, hm⟩ := (RonanK429.isPGroup_center_of_isComponent hθ hL).exists_card_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L),
    Nat.card_congr eL.toEquiv, hm] at h19L
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h19L with h | h
  · exact h19 h
  · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
    norm_num at this

theorem row427Cent_of_not_nineteen
    {S : Type} [Group S] (h19 : ¬ 19 ∣ Nat.card S) :
    Row427Cent S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨eL⟩ d hdA _ hN hLd K hK hKt hCA
  rcases hKt with h5 | ⟨-, hext⟩
  · obtain ⟨e5⟩ := h5
    exact false_of_cent_a5 hG hA hEF hL hdA hN hLd hK e5 hCA
  · exact false_of_on_of_not_nineteen h19 hθ hL eL hext

theorem rowOf427_of_autRank
    {X : Type} [Group X] (h19 : ¬ 19 ∣ Nat.card X)
    (hR : AutRankLeTwo X) : RowOf427 X := fun S _ _ _ _ ⟨e⟩ =>
  row427_of_cent (row427Cent_of_not_nineteen (by rwa [Nat.card_congr e.toEquiv]))
    (hR.of_mulEquiv e)

end Main

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
