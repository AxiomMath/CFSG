module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MK
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Syl
public import CFSG.RankThree.PartTwo.Sec8.HeringU38MTP

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.KGroups Matrix
  CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.SubgroupLists

section Setup

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (ι : F →+* K)

theorem map_toMat_eq (hι : ∀ a, σ (ι a) = ι a) (A : Mat3) : (A.toMat ι).map σ = A.toMat ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, hι]

theorem mat_suField (g : unitarySU 2 3 K 3) : mat (suField h σ g) = (mat g).map σ := rfl

theorem mat_suConj (D : unitaryIsom3 h) (g : unitarySU 2 3 K 3) :
    mat (suConj h D g) = ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat g *
      ((D : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) := by
  change (((D : GL (Fin 3) K) * (g : GL (Fin 3) K) * (D : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  simp [mat]

theorem mat_inv_isom3 (D : unitaryIsom3 h) :
    (((D : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ :=
  Units.inv_eq_of_mul_eq_one_left D.2

structure RefData (l m : F) (D : unitaryIsom3 h) : Prop where
  hl : l ≠ 0
  hm : m ≠ 0
  hlm : l ≠ m
  hD : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (Dg l m).toMat ι

end Setup

section CoreSyl

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (ι : F →+* K)

@[expose] noncomputable def T0sub : Subgroup (unitarySU 2 3 K 3) :=
  subgroupOfList h ι T0list T0_one T0_unit T0_mul T0_cjT

theorem T0sub_le_fix (hι : ∀ a, σ (ι a) = ι a) : T0sub h ι ≤ u38Fix (suField h σ) := by
  intro g hg
  obtain ⟨A, -, hgA⟩ := hg
  rw [mem_u38Fix]
  apply mat_injective
  rw [mat_suField, hgA, map_toMat_eq ι hι]

theorem card_T0sub (hι : Function.Injective ι) : Nat.card (T0sub h ι) = 8 := by
  rw [T0sub, card_subgroupOfList h ι hι T0_nodup]
  exact T0_len

variable {l m : F} {D : unitaryIsom3 h}

theorem mat_suConj_toSU (hD : RefData h ι l m D) {A : Mat3} (hA : IsU A ∧ A.det = 1) :
    mat (suConj h D (toSU h ι A hA)) = (Dg l m * A * (Dg l m).cjT).toMat ι := by
  rw [mat_suConj, mat_inv_isom3 h D, hD.hD, mat_toSU, toMat_cjT h ι, toMat_mul, toMat_mul]

theorem suConj_mem_T0sub (hD : RefData h ι l m D) {x : unitarySU 2 3 K 3} (hx : x ∈ T0sub h ι) :
    suConj h D x ∈ T0sub h ι := by
  obtain ⟨A, hA, hxA⟩ := hx
  refine ⟨Dg l m * A * (Dg l m).cjT, T0_conj l (mem_allF l) m (mem_allF m) hD.hl hD.hm A hA, ?_⟩
  have hx' : x = toSU h ι A (T0_unit A hA) := mat_injective hxA
  rw [hx', mat_suConj_toSU h ι hD]

theorem T0sub_le_comm (hι : Function.Injective ι) (hD : RefData h ι l m D) :
    T0sub h ι ≤ u38Comm (T0sub h ι) (suConj h D) := by
  intro g hg
  obtain ⟨A, hA, hgA⟩ := hg
  obtain ⟨t1, ht1, t2, ht2, hAeq⟩ :=
    T0_comm l (mem_allF l) m (mem_allF m) hD.hl hD.hm hD.hlm A hA
  have key : ∀ t ∈ T0list, ∃ w ∈ T0sub h ι,
      mat (w * (suConj h D w)⁻¹) = (Mat3.commGen (Dg l m) t).toMat ι := by
    intro t ht
    refine ⟨toSU h ι t (T0_unit t ht), toSU_mem h ι ht, ?_⟩
    rw [mat_mul, mat_inv h, mat_suConj_toSU h ι hD, mat_toSU, toMat_cjT h ι, ← toMat_mul]
    rfl
  obtain ⟨w1, hw1, hy1⟩ := key t1 ht1
  obtain ⟨w2, hw2, hy2⟩ := key t2 ht2
  have hg' : g = (w1 * (suConj h D w1)⁻¹) * (w2 * (suConj h D w2)⁻¹) := by
    apply mat_injective
    rw [mat_mul, hy1, hy2, ← toMat_mul, ← hAeq, hgA]
  rw [hg']
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨w1, hw1, rfl⟩)
    (Subgroup.subset_closure ⟨w2, hw2, rfl⟩)

theorem core_syl (hι : Function.Injective ι) (hισ : ∀ a, σ (ι a) = ι a)
    (hD : RefData h ι l m D) :
    ∃ T : Subgroup (unitarySU 2 3 K 3), T ≤ u38Fix (suField h σ) ∧ Nat.card T = 8 ∧
      (∀ x ∈ T, suConj h D x ∈ T) ∧ T ≤ u38Comm T (suConj h D) :=
  ⟨T0sub h ι, T0sub_le_fix h ι hισ, card_T0sub h ι hι, fun _ hx => suConj_mem_T0sub h ι hD hx,
    T0sub_le_comm h ι hι hD⟩

end CoreSyl

section NormalSylow

theorem mem_of_normal_sylow {S : Type*} [Group S] [Finite S] {G P : Subgroup S} (hPG : P ≤ G)
    (hN : G ≤ Subgroup.normalizer (P : Set S)) (hGc : Nat.card G = 216) (hPc : Nat.card P = 27)
    {z : S} (hz : z ∈ G) {j : ℕ} (hzj : z ^ 3 ^ j = 1) : z ∈ P := by
  have hnorm : (P.subgroupOf G).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPG).mpr hN
  have hP'c : Nat.card (P.subgroupOf G) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG).toEquiv, hPc]
  have hquot : Nat.card (G ⧸ P.subgroupOf G) = 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf G)
    rw [hGc, hP'c] at h1
    omega
  set q : G ⧸ P.subgroupOf G := QuotientGroup.mk (⟨z, hz⟩ : G) with hq
  have hq1 : q ^ 3 ^ j = 1 := by
    rw [hq, ← QuotientGroup.mk_pow]
    have : (⟨z, hz⟩ : G) ^ 3 ^ j = 1 := Subtype.ext (by simpa using hzj)
    rw [this]
    rfl
  have hq2 : q ^ 8 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ P.subgroupOf G) (x := q)
    rwa [hquot] at this
  have hq3 : q = 1 := by
    have h1 := pow_gcd_eq_one.mpr ⟨hq1, hq2⟩
    have hg : Nat.gcd (3 ^ j) 8 = 1 :=
      Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 3 8)
    rwa [hg, pow_one] at h1
  have : (⟨z, hz⟩ : G) ∈ P.subgroupOf G := (QuotientGroup.eq_one_iff _).mp hq3
  exact this

end NormalSylow

section CoreP3

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (ι : F →+* K)

@[expose] noncomputable def P0sub : Subgroup (unitarySU 2 3 K 3) :=
  subgroupOfList h ι P0list P0_one P0_unit P0_mul P0_cjT

theorem P0sub_le_fix (hι : ∀ a, σ (ι a) = ι a) : P0sub h ι ≤ u38Fix (suField h σ) := by
  intro g hg
  obtain ⟨A, -, hgA⟩ := hg
  rw [mem_u38Fix]
  apply mat_injective
  rw [mat_suField, hgA, map_toMat_eq ι hι]

theorem card_P0sub (hι : Function.Injective ι) : Nat.card (P0sub h ι) = 27 := by
  rw [P0sub, card_subgroupOfList h ι hι P0_nodup]
  exact P0_len

theorem conj_mem_P0sub {t p : unitarySU 2 3 K 3} (ht : t ∈ T0sub h ι) (hp : p ∈ P0sub h ι) :
    t * p * t⁻¹ ∈ P0sub h ι := by
  obtain ⟨A, hA, htA⟩ := ht
  obtain ⟨B, hB, hpB⟩ := hp
  refine ⟨A * B * A.cjT, P0_conj A hA B hB, ?_⟩
  rw [mat_mul, mat_mul, mat_inv h, htA, hpB, toMat_cjT h ι, toMat_mul, toMat_mul]

theorem T0sub_le_normalizer_P0sub :
    T0sub h ι ≤ Subgroup.normalizer (P0sub h ι : Set (unitarySU 2 3 K 3)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact fun hp => conj_mem_P0sub h ι ht hp
  · intro hp
    have := conj_mem_P0sub h ι (Subgroup.inv_mem _ ht) hp
    simpa [mul_assoc] using this

theorem card_u38Fix_suField (hσ : orderOf σ = 3) : Nat.card (u38Fix (suField h σ)) = 216 := by
  have := h.finite
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  obtain rfl : f₀ = 1 := by omega
  have h₀ : UnitaryFieldData 2 1 (CFSG.GH74.GLS.IVK.fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  have hrange : u38Fix (suField h σ) = (suIncl h h₀ hbar).range := by
    ext g
    rw [mem_range_suIncl_iff h h₀ hbar]
    rfl
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective (suIncl_injective h h₀ hbar)).toEquiv]
  exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two h₀ rfl

theorem fix_le_normalizer_P0sub (hι : Function.Injective ι) (hισ : ∀ a, σ (ι a) = ι a)
    (hσ : orderOf σ = 3) :
    u38Fix (suField h σ) ≤ Subgroup.normalizer (P0sub h ι : Set (unitarySU 2 3 K 3)) := by
  have := h.finite
  have hGc := card_u38Fix_suField h hσ
  set G := u38Fix (suField h σ) with hG
  set N := Subgroup.normalizer (P0sub h ι : Set (unitarySU 2 3 K 3)) ⊓ G with hNdef
  have hTN : T0sub h ι ≤ N := le_inf (T0sub_le_normalizer_P0sub h ι) (T0sub_le_fix h ι hισ)
  have hPN : P0sub h ι ≤ N := le_inf Subgroup.le_normalizer (P0sub_le_fix h ι hισ)
  have h8 : 8 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hTN
    rwa [card_T0sub h ι hι] at this
  have h27 : 27 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hPN
    rwa [card_P0sub h ι hι] at this
  have h216 : 216 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 27) h8 h27
  have hNG : N ≤ G := inf_le_right
  have hNc : Nat.card N ∣ 216 := hGc ▸ Subgroup.card_dvd_of_le hNG
  have hNeq : Nat.card N = 216 := Nat.dvd_antisymm hNc h216
  have : N = G := Subgroup.eq_of_le_of_card_ge hNG (by rw [hGc, hNeq])
  intro g hg
  rw [← this] at hg
  exact hg.1

end CoreP3

section P3Main

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} (ι : F →+* K)

theorem mat_blk (hιs : ∀ y : K, σ y = y → ∃ a, ι a = y) {x : unitarySU 2 3 K 3}
    (hxL : x ∈ leviSU3 (K := K) (2 ^ 3)) (hαx : suField h σ x = x) :
    ∃ a b c d : F, mat x = (blk a b c d).toMat ι := by
  obtain ⟨A, -, hA⟩ := hxL
  have hA' : (x : GL (Fin 3) K) = blockGL3 A := hA.symm
  have hmat : mat x = leviMat (A : Matrix (Fin 2) (Fin 2) K) := by
    show ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [hA']
    rfl
  have hfix : ∀ i j, σ (mat x i j) = mat x i j := by
    intro i j
    have := congrArg (fun g => mat g i j) hαx
    simpa [mat_suField] using this
  obtain ⟨a, ha⟩ := hιs _ (hfix 0 0)
  obtain ⟨b, hb⟩ := hιs _ (hfix 0 1)
  obtain ⟨c, hc⟩ := hιs _ (hfix 1 0)
  obtain ⟨d, hd⟩ := hιs _ (hfix 1 1)
  refine ⟨a, b, c, d, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mat3.toMat, blk, ← ha, ← hb, ← hc, ← hd, hmat, leviMat]

variable [Finite K]

theorem eq_x0_or_x0i (hι : Function.Injective ι) (hιs : ∀ y : K, σ y = y → ∃ a, ι a = y)
    {x : unitarySU 2 3 K 3} (hxL : x ∈ leviSU3 (K := K) (2 ^ 3)) (hαx : suField h σ x = x)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    x = toSU h ι x0 x0_unit ∨ x = toSU h ι x0i x0i_unit := by
  obtain ⟨a, b, c, d, hxm⟩ := mat_blk h ι hιs hxL hαx
  have hunit := (mem_unitarySU_iff h).mp x.2
  have hu2 : ((mat x).map h.bar)ᵀ * mat x = 1 := hunit.2
  have hdet : (mat x).det = 1 := hunit.1
  have hU : IsU (blk a b c d) := by
    show (blk a b c d).cjT * blk a b c d = 1
    apply toMat_injective ι hι
    rw [toMat_mul, ← toMat_cjT h ι, ← hxm, hu2, toMat_one]
  have hd : (blk a b c d).det = 1 := by
    apply hι
    rw [← toMat_det, ← hxm, hdet, map_one]
  have h3 : blk a b c d * blk a b c d * blk a b c d = 1 := by
    apply toMat_injective ι hι
    have h3x : mat (x * x * x) = 1 := by rw [← pow_three', hx3, mat_one]
    rw [toMat_mul, toMat_mul, ← hxm, ← mat_mul, ← mat_mul, h3x, toMat_one]
  have hne : blk a b c d ≠ 1 := by
    intro h1
    apply hx1
    apply mat_injective
    rw [hxm, h1, toMat_one, mat_one]
  have hcls := su2_cls a (mem_allF a) b (mem_allF b) c (mem_allF c) d (mem_allF d) hU hd h3 hne
  rcases hcls with hc | hc
  · left
    apply mat_injective
    rw [hxm, hc, mat_toSU]
  · right
    apply mat_injective
    rw [hxm, hc, mat_toSU]

theorem T0sub_le_u38Two (hι : Function.Injective ι) (hισ : ∀ a, σ (ι a) = ι a) :
    T0sub h ι ≤ u38Two (suField h σ) := by
  intro g hg
  have hfix : g ∈ u38Fix (suField h σ) := T0sub_le_fix h ι hισ hg
  have h8 : g ^ 2 ^ 3 = 1 := by
    have := pow_card_eq_one' (G := T0sub h ι) (x := ⟨g, hg⟩)
    rw [card_T0sub h ι hι] at this
    have h1 := congrArg Subtype.val this
    simpa using h1
  exact Subgroup.subset_closure ⟨hfix, 3, h8⟩

theorem u38Two_le_fix (α : MulAut (unitarySU 2 3 K 3)) : u38Two α ≤ u38Fix α :=
  (Subgroup.closure_le _).mpr fun _ hy => hy.1

theorem p3_of_x0_or_x0i (hι : Function.Injective ι) (hισ : ∀ a, σ (ι a) = ι a)
    (hσ : orderOf σ = 3) {x : unitarySU 2 3 K 3}
    (hx : x = toSU h ι x0 x0_unit ∨ x = toSU h ι x0i x0i_unit) :
    x ∈ u38Two (suField h σ) ∧ ∀ z ∈ u38Two (suField h σ), (∃ j : ℕ, z ^ 3 ^ j = 1) →
      z ∈ Subgroup.closure {y | ∃ g ∈ u38Two (suField h σ), y = g * x * g⁻¹} := by
  set I := u38Two (suField h σ) with hI
  set x0S := toSU h ι x0 x0_unit with hx0S
  set x0iS := toSU h ι x0i x0i_unit with hx0iS
  set piS := toSU h ι piM piM_unit with hpiS
  set zS := toSU h ι zM zM_unit with hzS
  obtain ⟨hs1U, hs1d, hs1s, hs2U, hs2d, hs2s⟩ := s_unit
  set s1S := toSU h ι s1 ⟨hs1U, hs1d⟩ with hs1S
  set s2S := toSU h ι s2 ⟨hs2U, hs2d⟩ with hs2S
  set tS := toSU h ι (Eich 1 ωF) (T0_unit _ Eich_mem) with htS
  have hfixS : ∀ {A : Mat3} (hA : IsU A ∧ A.det = 1),
      toSU h ι A hA ∈ u38Fix (suField h σ) := by
    intro A hA
    rw [mem_u38Fix]
    apply mat_injective
    rw [mat_suField, mat_toSU, map_toMat_eq ι hισ]
  have hs1sq : s1S ^ 2 ^ 1 = 1 := by
    apply mat_injective
    rw [pow_one, pow_two, mat_mul, mat_toSU, ← toMat_mul, hs1s, toMat_one, mat_one]
  have hs2sq : s2S ^ 2 ^ 1 = 1 := by
    apply mat_injective
    rw [pow_one, pow_two, mat_mul, mat_toSU, ← toMat_mul, hs2s, toMat_one, mat_one]
  have hs1I : s1S ∈ I := Subgroup.subset_closure ⟨hfixS _, 1, hs1sq⟩
  have hs2I : s2S ∈ I := Subgroup.subset_closure ⟨hfixS _, 1, hs2sq⟩
  have hx0eq : x0S = s1S * s2S := by
    apply mat_injective
    rw [mat_mul, mat_toSU, mat_toSU, mat_toSU, ← toMat_mul, x0_eq]
  have hx0ieq : x0iS = s2S * s1S := by
    apply mat_injective
    rw [mat_mul, mat_toSU, mat_toSU, mat_toSU, ← toMat_mul, x0i_eq]
  have hx0inv : x0S * x0iS = 1 := by
    apply mat_injective
    rw [mat_mul, mat_toSU, mat_toSU, ← toMat_mul, x0_x0i.1, toMat_one, mat_one]
  have hx0I : x0S ∈ I := hx0eq ▸ Subgroup.mul_mem _ hs1I hs2I
  have hx0iI : x0iS ∈ I := hx0ieq ▸ Subgroup.mul_mem _ hs2I hs1I
  have htI : tS ∈ I := T0sub_le_u38Two h ι hι hισ (toSU_mem h ι Eich_mem)
  have hpi : piS = tS * x0S * tS⁻¹ := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_inv h, mat_toSU, mat_toSU, mat_toSU, toMat_cjT h ι, ← toMat_mul,
      ← toMat_mul, T0_normalizes_x0]
  have hz : zS = piS * x0S * piS⁻¹ * x0S⁻¹ := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_mul, mat_inv h, mat_inv h, mat_toSU, mat_toSU, mat_toSU,
      toMat_cjT h ι, toMat_cjT h ι, ← toMat_mul, ← toMat_mul, ← toMat_mul, comm_pi_x0]
  have hP0Q : P0sub h ι ≤ Subgroup.closure {x0S, piS} := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := hp
    obtain ⟨i, -, j, -, k, -, hAeq⟩ := P0_form A hA
    have hpe : p = zS ^ i * x0S ^ j * piS ^ k := by
      apply mat_injective
      rw [mat_mul, mat_mul, mat_pow, mat_pow, mat_pow, mat_toSU, mat_toSU, mat_toSU, hpA, hAeq,
        toMat_mul, toMat_mul, toMat_pow, toMat_pow, toMat_pow]
    have hzQ : zS ∈ Subgroup.closure {x0S, piS} := by
      rw [hz]
      have hx : x0S ∈ Subgroup.closure {x0S, piS} := Subgroup.subset_closure (by simp)
      have hp : piS ∈ Subgroup.closure {x0S, piS} := Subgroup.subset_closure (by simp)
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hp hx)
        (Subgroup.inv_mem _ hp)) (Subgroup.inv_mem _ hx)
    rw [hpe]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hzQ _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  set N := Subgroup.closure {y | ∃ g ∈ I, y = g * x * g⁻¹} with hN
  have hxN : x ∈ N := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by simp⟩
  have hx0N : x0S ∈ N := by
    rcases hx with rfl | rfl
    · exact hxN
    · have : x0S = x0iS⁻¹ := eq_inv_of_mul_eq_one_left hx0inv
      rw [this]
      exact Subgroup.inv_mem _ hxN
  have hpiN : piS ∈ N := by
    rcases hx with rfl | rfl
    · rw [hpi]
      exact Subgroup.subset_closure ⟨tS, htI, rfl⟩
    · have : x0S = x0iS⁻¹ := eq_inv_of_mul_eq_one_left hx0inv
      have hconj : tS * x0iS * tS⁻¹ ∈ N := Subgroup.subset_closure ⟨tS, htI, rfl⟩
      have : piS = (tS * x0iS * tS⁻¹)⁻¹ := by rw [hpi, this]; group
      rw [this]
      exact Subgroup.inv_mem _ hconj
  have hQN : Subgroup.closure {x0S, piS} ≤ N := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hx0N
    · exact hpiN
  refine ⟨?_, fun z hzI ⟨j, hj⟩ => ?_⟩
  · rcases hx with rfl | rfl
    · exact hx0I
    · exact hx0iI
  · have hzG : z ∈ u38Fix (suField h σ) := u38Two_le_fix _ hzI
    have := h.finite
    have hzP : z ∈ P0sub h ι :=
      mem_of_normal_sylow (P0sub_le_fix h ι hισ) (fix_le_normalizer_P0sub h ι hι hισ hσ)
        (card_u38Fix_suField h hσ) (card_P0sub h ι hι) hzG hj
    exact hQN (hP0Q hzP)

theorem u38Fix_suConj_eq (D : unitaryIsom3 h) :
    u38Fix (suConj h D) = suCentralizer (2 ^ 3) (D : GL (Fin 3) K) := by
  ext g
  rw [mem_u38Fix, mem_suCentralizer]
  constructor
  · intro hg
    have h1 := congrArg (fun y : unitarySU 2 3 K 3 => (y : GL (Fin 3) K)) hg
    simp only [coe_suConj, Subgroup.coe_inv] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro hg
    apply Subtype.ext
    rw [coe_suConj, Subgroup.coe_inv, ← hg, mul_inv_cancel_right]

variable {l m : F} {D : unitaryIsom3 h}

theorem core_p3 (hι : Function.Injective ι) (hισ : ∀ a, σ (ι a) = ι a)
    (hιs : ∀ y : K, σ y = y → ∃ a, ι a = y) (hσ : orderOf σ = 3) (hD : RefData h ι l m D)
    {x : unitarySU 2 3 K 3} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hαx : suField h σ x = x)
    (hxK : x ∈ (perfectResidual (u38Fix (suConj h D))).map (u38Fix (suConj h D)).subtype) :
    x ∈ u38Two (suField h σ) ∧ ∀ z ∈ u38Two (suField h σ), (∃ j : ℕ, z ^ 3 ^ j = 1) →
      z ∈ Subgroup.closure {y | ∃ g ∈ u38Two (suField h σ), y = g * x * g⁻¹} := by
  have hq : 4 ≤ 2 ^ 3 := by norm_num
  have hlm' : ι l ≠ ι m := fun e => hD.hlm (hι e)
  have ht : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ι l, ι l, ι m] := by
    rw [hD.hD]
    exact toMat_diag ι l l m
  have hlevi : x ∈ leviSU3 (K := K) (2 ^ 3) := by
    have e2 := inSubgroup_perfectResidual_suCentralizer_eq h hq hlm' ht
    rw [← e2, ← u38Fix_suConj_eq]
    exact hxK
  exact p3_of_x0_or_x0i h ι hι hισ hσ (eq_x0_or_x0i h ι hι hιs hlevi hαx hx1 hx3)

end P3Main

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
