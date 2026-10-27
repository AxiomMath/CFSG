module

public import CFSG.Quasithin.H13.NQCatJ4Line
public import CFSG.Quasithin.H13.NQCatJ4FrattiniGen
public import CFSG.RankThree.SubgroupLists.ExtraspecialCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open scoped commutatorElement Matrix

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] [Finite G] {P : Subgroup G} {n : G}
    (hn : n ∈ normalizer (P : Set G)) : P.map (MulAut.conj n).toMonoidHom = P := by
  have hinj : Function.Injective (MulAut.conj n).toMonoidHom := (MulAut.conj n).injective
  refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective hinj])
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 hn x).1 hx

theorem map_line_eq
    {g : Sporadic.J4.J} {P : Subgroup Sporadic.J4.J}
    (hPg : P ≤ j4Q.map (MulAut.conj g).toMonoidHom)
    (hCP : (zpowers j4z).map (MulAut.conj g).toMonoidHom ≤ P) (k : Sporadic.J4.J)
    (hk : P.map (MulAut.conj k).toMonoidHom = P) :
    ((zpowers j4z).map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      (zpowers j4z).map (MulAut.conj g).toMonoidHom := by
  have hinj : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective hinj])
  rintro _ ⟨u, hu, rfl⟩
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
    exact one_mem _
  have hcu : (MulAut.conj k).toMonoidHom u = k * u * k⁻¹ := rfl
  rw [hcu]
  have huP : k * u * k⁻¹ ∈ P := hk ▸ (⟨u, hCP hu, rfl⟩ :
    k * u * k⁻¹ ∈ P.map (MulAut.conj k).toMonoidHom)
  have hku1 : k * u * k⁻¹ ≠ 1 := fun h => hu1 (by
    calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group)
  have h2 : fixDim (k * u * k⁻¹) = 2 := by
    rw [fixDim_conj]
    exact (fixDim_of_mem_conj g (map_mono (zpowers_le.2 ElevenData.z_mem) hu) hu1).1 hu
  by_contra hnot
  have h12 := (fixDim_of_mem_conj g (hPg huP) hku1).2 hnot
  omega

theorem pow_eleven_of_le_conj
    {g : Sporadic.J4.J} {P : Subgroup Sporadic.J4.J}
    (hPg : P ≤ j4Q.map (MulAut.conj g).toMonoidHom) (x : P) : x ^ 11 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (j4DataConj g).pow_eleven ((closure_conj g).symm ▸ hPg x.2))

theorem frattini_eq_bot_of_card
    {g : Sporadic.J4.J} {P : Subgroup Sporadic.J4.J}
    (hPg : P ≤ j4Q.map (MulAut.conj g).toMonoidHom) (hcard : Nat.card P = 11 ^ 2) :
    frattini P = ⊥ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [CFSG.RankThree.PartTwo.frattini_eq_commutator (IsPGroup.of_card hcard)
    (pow_eleven_of_le_conj hPg)]
  have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  rw [_root_.commutator_def, eq_bot_iff, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_eq_one_iff_mul_comm.2 (hc.is_comm.comm a b)]
  exact one_mem _

theorem isSolvable_range_of_card_sq
    {P : Subgroup Sporadic.J4.J} (hP : IsPGroup 11 P)
    (hcard : Nat.card P = 11 ^ 2) : Group.IsSolvable (normalizerFrattiniAction P).range := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hPg⟩ := exists_le_conj hP
  have hΦ := frattini_eq_bot_of_card hPg hcard
  have hCP : (zpowers j4z).map (MulAut.conj g).toMonoidHom ≤ P := by
    rw [← zpowers_conj]
    exact (j4DataConj g).zpowers_le_of_card ((closure_conj g).symm ▸ hPg) hcard
  set C := (zpowers j4z).map (MulAut.conj g).toMonoidHom with hCdef
  set L : Subgroup (P ⧸ frattini P) := (C.subgroupOf P).map (QuotientGroup.mk' (frattini P))
  obtain ⟨-, hEcomm, -, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  have hEc : ∀ a b : P ⧸ frattini P, a * b = b * a := hEcomm.is_comm.comm
  have : L.Normal := ⟨fun l hl e => by rw [hEc e l, mul_inv_cancel_right]; exact hl⟩
  have hmk : Function.Injective (QuotientGroup.mk' (frattini P)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
  have hinjg : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hCcard : Nat.card C = 11 := by
    rw [hCdef, card_map_of_injective hinjg, Nat.card_zpowers, j4Data.orderOf_z]
  have hLcard : Nat.card L = 11 := by
    rw [card_map_of_injective hmk, Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv, hCcard]
  have hEcard : Nat.card (P ⧸ frattini P) = 11 ^ 2 := by
    rw [← hcard]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hΦ |>.trans
      QuotientGroup.quotientBot).toEquiv
  have : IsCyclic L := isCyclic_of_prime_card hLcard
  have : IsCyclic ((P ⧸ frattini P) ⧸ L) := by
    refine isCyclic_of_prime_card (p := 11) ?_
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    rw [hEcard, hLcard] at h
    omega
  refine isSolvable_of_stabilizes hEc L _ fun γ hγ => ?_
  obtain ⟨n, rfl⟩ := hγ
  have hnC := map_line_eq hPg hCP n (map_conj_eq_of_mem_normalizer n.2)
  have hinj : Function.Injective (MulEquiv.toMonoidHom (M := P ⧸ frattini P)
      (N := P ⧸ frattini P) (normalizerFrattiniAction P n)) :=
    (normalizerFrattiniAction P n).injective
  refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective hinj])
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  have hcP : (n : Sporadic.J4.J) * c * (n : Sporadic.J4.J)⁻¹ ∈ P :=
    (mem_normalizer_iff.1 n.2 c).1 c.2
  refine ⟨⟨(n : Sporadic.J4.J) * c * (n : Sporadic.J4.J)⁻¹, hcP⟩, ?_, ?_⟩
  · have hcC : (c : Sporadic.J4.J) ∈ C := hc
    have hnc : (n : Sporadic.J4.J) * c * (n : Sporadic.J4.J)⁻¹ ∈ C := by
      rw [hCdef] at hcC ⊢
      rw [← hnC]
      exact ⟨c, hcC, rfl⟩
    exact hnc
  · have h1 := normalizerFrattiniAction_mk P n c
    have h2 : normalizerConj P n c = ⟨(n : Sporadic.J4.J) * c * (n : Sporadic.J4.J)⁻¹, hcP⟩ :=
      Subtype.ext (normalizerConj_apply P n c)
    rw [h2] at h1
    rw [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, h1]

theorem zmod_eleven_det : (0 : ZMod 11) * 9 - 6 * 7 = 2 := by decide

theorem mulVec_single_one_apply (M : Matrix (Fin 2) (Fin 2) (ZMod 11)) (i j : Fin 2) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

theorem conj_relations
    (g : Sporadic.J4.J) :
    (g * j4h * g⁻¹) * (g * j4x * g⁻¹) * (g * j4h * g⁻¹)⁻¹ =
        (g * j4x * g⁻¹) ^ 0 * (g * j4y * g⁻¹) ^ 7 * ⁅g * j4x * g⁻¹, g * j4y * g⁻¹⁆ ^ 1 ∧
      (g * j4h * g⁻¹) * (g * j4y * g⁻¹) * (g * j4h * g⁻¹)⁻¹ =
        (g * j4x * g⁻¹) ^ 6 * (g * j4y * g⁻¹) ^ 9 * ⁅g * j4x * g⁻¹, g * j4y * g⁻¹⁆ ^ 6 := by
  rw [commutator_conj]
  have hc : ∀ a b c : Sporadic.J4.J,
      g * (a * b * c) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by
    intro a b c
    group
  constructor
  · calc (g * j4h * g⁻¹) * (g * j4x * g⁻¹) * (g * j4h * g⁻¹)⁻¹ =
          g * (j4h * j4x * j4h⁻¹) * g⁻¹ := by group
      _ = g * (j4x ^ 0 * j4y ^ 7 * j4z ^ 1) * g⁻¹ := by rw [j4h_conj_x]
      _ = _ := by rw [hc, ← conj_pow, ← conj_pow, ← conj_pow]
  · calc (g * j4h * g⁻¹) * (g * j4y * g⁻¹) * (g * j4h * g⁻¹)⁻¹ =
          g * (j4h * j4y * j4h⁻¹) * g⁻¹ := by group
      _ = g * (j4x ^ 6 * j4y ^ 9 * j4z ^ 6) * g⁻¹ := by rw [j4h_conj_y]
      _ = _ := by rw [hc, ← conj_pow, ← conj_pow, ← conj_pow]

theorem eq_bot_of_isPerfect_of_relations
    {G : Type*} [Group G] [Finite G] {x y h : G}
    (D : ElevenData x y) (hrx : h * x * h⁻¹ = x ^ 0 * y ^ 7 * ⁅x, y⁆ ^ 1)
    (hry : h * y * h⁻¹ = x ^ 6 * y ^ 9 * ⁅x, y⁆ ^ 6) (h11 : ¬ 11 ^ 4 ∣ Nat.card G)
    (h25 : ¬ 25 ∣ Nat.card G)
    (S : Subgroup (normalizerFrattiniAction (closure ({x, y} : Set G))).range)
    [Group.IsPerfect S] : S = ⊥ := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let P := closure ({x, y} : Set G)
  let E := P ⧸ frattini P
  have hxP : x ∈ P := mem_closure_pair_left _ _
  have hyP : y ∈ P := mem_closure_pair_right _ _
  have hzP : ⁅x, y⁆ ∈ P := ElevenData.z_mem
  obtain ⟨-, hEcomm, hEpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient D.isPGroup
  have hEc : ∀ a b : E, a * b = b * a := hEcomm.is_comm.comm
  have hΦ : frattini P = center P :=
    D.isExtraspecial.2.2.1
  have hΦcard : Nat.card (frattini P) = 11 := by
    rw [hΦ]
    exact D.isExtraspecial.2.2.2
  have hEcard : Nat.card E = 11 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (frattini P)
    rw [D.card_closure, hΦcard] at h1
    have h2 : Nat.card E * 11 = 11 ^ 2 * 11 := by rw [← h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  set xb : E := ((⟨x, hxP⟩ : P) : E) with hxbdef
  set yb : E := ((⟨y, hyP⟩ : P) : E) with hybdef
  have hzb : (((⟨⁅x, y⁆, hzP⟩ : P)) : E) = 1 := by
    rw [QuotientGroup.eq_one_iff, hΦ]
    have hz : ⁅x, y⁆ ∈ (center P).map P.subtype := by
      rw [D.center_eq]
      exact mem_zpowers _
    obtain ⟨c, hc, hce⟩ := hz
    have hc' : c = ⟨⁅x, y⁆, hzP⟩ := Subtype.ext hce
    exact hc' ▸ hc
  have hword : ∀ q : E, ∃ i j : ℕ, i < 11 ∧ j < 11 ∧ q = xb ^ i * yb ^ j := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, j, k, hi, hj, -, hp⟩ := D.exists_word p.2
    refine ⟨i, j, hi, hj, ?_⟩
    have hp' : p = ⟨x, hxP⟩ ^ i * ⟨y, hyP⟩ ^ j * ⟨⁅x, y⁆, hzP⟩ ^ k :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_pow]; exact hp)
    rw [hp', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow, QuotientGroup.mk_pow, hzb, one_pow, mul_one]
  have hxb11 : xb ^ 11 = 1 := hEpow xb
  have hyb11 : yb ^ 11 = 1 := hEpow yb
  have hswap : ∀ a b c d : E, a * b * (c * d) = a * c * (b * d) := fun a b c d => by
    rw [mul_assoc, ← mul_assoc b, hEc b c, mul_assoc c, ← mul_assoc]
  let F : Multiplicative (Fin 2 → ZMod 11) →* E :=
    { toFun := fun v =>
        xb ^ (Multiplicative.toAdd v 0).val * yb ^ (Multiplicative.toAdd v 1).val
      map_one' := by simp only [toAdd_one, Pi.zero_apply, ZMod.val_zero, pow_zero, mul_one]
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply]
        rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hxb11, ← pow_eq_pow_mod _ hyb11,
          pow_add, pow_add]
        exact hswap _ _ _ _ }
  have hF : ∀ v, F v =
      xb ^ (Multiplicative.toAdd v 0).val * yb ^ (Multiplicative.toAdd v 1).val := fun _ => rfl
  have hFsurj : Function.Surjective F := by
    intro q
    obtain ⟨i, j, hi, hj, rfl⟩ := hword q
    refine ⟨Multiplicative.ofAdd ![(i : ZMod 11), (j : ZMod 11)], ?_⟩
    rw [hF, toAdd_ofAdd]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.val_natCast,
      Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  have hFbij : Function.Bijective F := hFsurj.bijective_of_nat_card_le (by
    rw [hEcard, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  let e : E ≃* Multiplicative (Fin 2 → ZMod 11) := (MulEquiv.ofBijective F hFbij).symm
  have hv1 : (1 : ZMod 11).val = 1 := rfl
  have he0 : e xb = Multiplicative.ofAdd (Pi.single 0 1) := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, hF, toAdd_ofAdd]
    simp [hv1]
  have he1 : e yb = Multiplicative.ofAdd (Pi.single 1 1) := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, hF, toAdd_ofAdd]
    simp [hv1]
  have hhP : P.map (MulAut.conj h).toMonoidHom =
      P := by
    have hle : P.map (MulAut.conj h).toMonoidHom ≤
        P := by
      rw [MonoidHom.map_closure, closure_le, Set.image_pair]
      intro u hu
      rcases hu with rfl | rfl
      · show h * x * h⁻¹ ∈ _
        rw [hrx]
        exact ElevenData.word_mem 0 7 1
      · show h * y * h⁻¹ ∈ _
        rw [hry]
        exact ElevenData.word_mem 6 9 6
    have hinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective hinj])
  have hhN : h ∈ normalizer (P : Set G) := NQTerm.mem_normalizer_of_map_conj_eq hhP
  set σ := normalizerFrattiniAction P ⟨h, hhN⟩ with hσdef
  have hσx : σ xb = yb ^ 7 := by
    rw [hxbdef, normalizerFrattiniAction_mk]
    have hc : normalizerConj P ⟨h, hhN⟩ ⟨x, hxP⟩ =
        ⟨x, hxP⟩ ^ 0 * ⟨y, hyP⟩ ^ 7 * ⟨⁅x, y⁆, hzP⟩ ^ 1 :=
      Subtype.ext (by
        rw [normalizerConj_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hrx)
    rw [hc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow, QuotientGroup.mk_pow, hzb, pow_zero, one_pow, mul_one, one_mul]
  have hσy : σ yb = xb ^ 6 * yb ^ 9 := by
    rw [hybdef, normalizerFrattiniAction_mk]
    have hc : normalizerConj P ⟨h, hhN⟩ ⟨y, hyP⟩ =
        ⟨x, hxP⟩ ^ 6 * ⟨y, hyP⟩ ^ 9 * ⟨⁅x, y⁆, hzP⟩ ^ 6 :=
      Subtype.ext (by
        rw [normalizerConj_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hry)
    rw [hc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow, QuotientGroup.mk_pow, hzb, one_pow, mul_one]
  set M := ((CFSG.SectionRank.Ccomm.elemAutEquivGL e σ : GL (Fin 2) (ZMod 11)) :
    Matrix (Fin 2) (Fin 2) (ZMod 11)) with hMdef
  have hM0 : M *ᵥ Pi.single 0 1 = (7 : ℕ) • Pi.single 1 1 := by
    have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e σ xb
    rw [he0, toAdd_ofAdd, hσx, map_pow, he1, toAdd_pow, toAdd_ofAdd] at h1
    exact h1
  have hM1 : M *ᵥ Pi.single 1 1 = (6 : ℕ) • Pi.single 0 1 + (9 : ℕ) • Pi.single 1 1 := by
    have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e σ yb
    rw [he1, toAdd_ofAdd, hσy, map_mul, map_pow, map_pow, he0, he1, toAdd_mul, toAdd_pow,
      toAdd_pow, toAdd_ofAdd, toAdd_ofAdd] at h1
    exact h1
  have hdet : M.det = 2 := by
    have e00 := congrFun hM0 0
    have e10 := congrFun hM0 1
    have e01 := congrFun hM1 0
    have e11 := congrFun hM1 1
    rw [mulVec_single_one_apply] at e00 e10 e01 e11
    have m00 : M 0 0 = 0 := by rw [e00]; simp
    have m10 : M 1 0 = 7 := by rw [e10]; simp
    have m01 : M 0 1 = 6 := by rw [e01]; simp
    have m11 : M 1 1 = 9 := by rw [e11]; simp
    rw [Matrix.det_fin_two, m00, m10, m01, m11]
    exact zmod_eleven_det
  let δ : MulAut E →* (ZMod 11)ˣ := Matrix.GeneralLinearGroup.det.comp
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom
  have hδσ : ((δ σ : (ZMod 11)ˣ) : ZMod 11) = 2 := by
    show ((Matrix.GeneralLinearGroup.det (CFSG.SectionRank.Ccomm.elemAutEquivGL e σ) :
      (ZMod 11)ˣ) : ZMod 11) = 2
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet
  have hordσ : orderOf (δ σ) = 10 := by
    rw [← orderOf_units, hδσ]
    exact orderOf_two_zmod_eleven
  let I := (normalizerFrattiniAction P).range
  have hPK : P.subgroupOf (normalizer (P : Set G)) ≤ (normalizerFrattiniAction P).ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.one_apply, normalizerFrattiniAction_mk, QuotientGroup.eq, hΦ,
        ← D.isExtraspecial.2.1]
      have hnP : (n : G) ∈ P := hn
      have hcomm : (normalizerConj P n u)⁻¹ * u = ⁅(⟨n, hnP⟩ : P), u⁻¹⁆ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply, commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [hcomm, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  have hNcard : Nat.card (normalizer (P : Set G)) =
      Nat.card (normalizerFrattiniAction P).ker * Nat.card I := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (normalizerFrattiniAction P).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, mul_comm]
  have hker11 : 11 ^ 3 ∣ Nat.card (normalizerFrattiniAction P).ker := by
    have h1 := card_dvd_of_le hPK
    rwa [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, D.card_closure] at h1
  have hNG : Nat.card (normalizer (P : Set G)) ∣ Nat.card G := card_subgroup_dvd_card _
  have h11I : ¬ 11 ∣ Nat.card I := by
    intro h1
    apply h11
    refine dvd_trans ?_ hNG
    rw [hNcard, pow_succ]
    exact mul_dvd_mul hker11 h1
  have h25I : ¬ 25 ∣ Nat.card I := fun h1 =>
    h25 (h1.trans ((Dvd.intro_left _ hNcard.symm).trans hNG))
  have hσI : σ ∈ I := ⟨⟨h, hhN⟩, rfl⟩
  have h5δ : 5 ∣ Nat.card (I.map δ) := by
    have h1 : orderOf (⟨δ σ, ⟨σ, hσI, rfl⟩⟩ : I.map δ) = 10 :=
      (orderOf_injective (I.map δ).subtype (I.map δ).subtype_injective
        ⟨δ σ, ⟨σ, hσI, rfl⟩⟩).symm.trans hordσ
    have h2 := orderOf_dvd_natCard (⟨δ σ, ⟨σ, hσI, rfl⟩⟩ : I.map δ)
    rw [h1] at h2
    exact (by norm_num : 5 ∣ 10).trans h2
  have hIδ := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker δ I
  have h5K : ¬ 5 ∣ Nat.card (I ⊓ δ.ker : Subgroup (MulAut E)) := fun h1 =>
    h25I (by rw [hIδ, show (25 : ℕ) = 5 * 5 by norm_num]; exact mul_dvd_mul h5δ h1)
  set S₁ := S.map I.subtype with hS₁def
  have : Group.IsPerfect S₁ := Group.IsPerfect.map _
  have hS₁δ : S₁.map δ = ⊥ := by
    have : Group.IsPerfect (S₁.map δ) := Group.IsPerfect.map _
    have : IsMulCommutative (S₁.map δ) :=
      ⟨⟨fun a b => Subtype.ext (mul_comm (a : (ZMod 11)ˣ) b)⟩⟩
    exact Subgroup.eq_bot_of_subsingleton _
  have hS₁K : S₁ ≤ I ⊓ δ.ker := le_inf (map_subtype_le S) ((Subgroup.map_eq_bot_iff _).1 hS₁δ)
  have hS₁5 : ¬ 5 ∣ Nat.card S₁ := fun h1 => h5K (h1.trans (card_dvd_of_le hS₁K))
  have hS₁11 : ¬ 11 ∣ Nat.card S₁ := fun h1 =>
    h11I (h1.trans (card_dvd_of_le (map_subtype_le S)))
  set S₂ := S₁.map (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom with hS₂def
  have : Group.IsPerfect S₂ := Group.IsPerfect.map _
  have hS₂card : Nat.card S₂ = Nat.card S₁ :=
    card_map_of_injective (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
  by_contra hS
  have hS₂ne : S₂ ≠ ⊥ := by
    intro h1
    apply hS
    rw [hS₂def, map_eq_bot_iff_of_injective _ (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective,
      hS₁def, map_eq_bot_iff_of_injective _ I.subtype_injective] at h1
    exact h1
  obtain ⟨-, -, -, -, -, h5'⟩ :=
    CFSG.SectionRank.Ccomm.perfect_prime_linear_recognition (p := 11) (by norm_num) S₂ hS₂ne
  obtain ⟨φ⟩ := h5' (by rw [hS₂card]; exact hS₁11)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h60 : Nat.card (S₂ ⧸ center S₂) = 60 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.SectionRank.Ccomm.card_PSL2_zmod (by norm_num)]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center S₂)
  rw [h60, hS₂card] at h1
  exact hS₁5 (h1 ▸ Dvd.dvd.mul_right (by norm_num : 5 ∣ 60) _)

theorem not_dvd_card_J4J_eleven
    : ¬ 11 ^ 4 ∣ Nat.card Sporadic.J4.J := by
  rw [card_J4J]
  norm_num

theorem not_dvd_card_J4J_five : ¬ 25 ∣ Nat.card Sporadic.J4.J := by
  rw [card_J4J]
  norm_num

theorem J4_noncyclic_eleven_subgroup_frattini_normalizer_image_is_solvable
    (P : Subgroup Sporadic.J4.J) (hP : IsPGroup 11 P) (hPc : ¬ IsCyclic P) :
    IsElementaryAbelian 11 (P ⧸ frattini P) ∧ Nat.card (P ⧸ frattini P) = 11 ^ 2 ∧
      Group.IsSolvable (normalizerFrattiniAction P).range ∧
      ∀ K : Subgroup (normalizerFrattiniAction P).range, Group.IsPerfect K → K = ⊥ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have helem := (CFSG.GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  have hle := exists_le_conj hP
  rcases hle with ⟨g, hPg⟩
  have hinjg : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hkex := hP.exists_card_eq
  rcases hkex with ⟨k, hk⟩
  have hk3 : k ≤ 3 := by
    have h1 := card_le_of_le hPg
    rw [card_map_of_injective hinjg, hk, j4Data.card_closure] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hk23 : k = 2 ∨ k = 3 := by
    rcases (show k ≤ 1 ∨ k = 2 ∨ k = 3 by omega) with h1 | h2 | h3
    · exfalso
      apply hPc
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · have : Subsingleton P := by
          rw [← Finite.card_le_one_iff_subsingleton, hk, pow_zero]
        infer_instance
      · exact isCyclic_of_prime_card (hk.trans (pow_one 11))
    · exact Or.inl h2
    · exact Or.inr h3
  have key : Nat.card (P ⧸ frattini P) = 11 ^ 2 ∧
      Group.IsSolvable (normalizerFrattiniAction P).range := by
    rcases hk23 with rfl | rfl
    · refine ⟨?_, isSolvable_range_of_card_sq hP hk⟩
      rw [← hk]
      exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq (frattini_eq_bot_of_card hPg hk)
        |>.trans QuotientGroup.quotientBot).toEquiv
    · have hPeq : P = Subgroup.closure ({g * j4x * g⁻¹, g * j4y * g⁻¹} : Set Sporadic.J4.J) := by
        rw [closure_conj]
        exact eq_of_le_of_card_ge hPg (by
          rw [card_map_of_injective hinjg, hk, j4Data.card_closure])
      subst hPeq
      have D := j4DataConj g
      refine ⟨?_, isSolvable_of_forall_isPerfect fun K hK =>
        eq_bot_of_isPerfect_of_relations D (conj_relations g).1 (conj_relations g).2
          not_dvd_card_J4J_eleven not_dvd_card_J4J_five K⟩
      have hΦcard : Nat.card (frattini (Subgroup.closure
          ({g * j4x * g⁻¹, g * j4y * g⁻¹} : Set Sporadic.J4.J))) = 11 := by
        rw [D.isExtraspecial.2.2.1]
        exact D.isExtraspecial.2.2.2
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (frattini (Subgroup.closure ({g * j4x * g⁻¹, g * j4y * g⁻¹} : Set Sporadic.J4.J)))
      rw [D.card_closure, hΦcard] at h1
      omega
  refine ⟨helem, key.1, key.2, fun K hK => ?_⟩
  have := key.2
  exact eq_bot_of_isPerfect K

end CFSG.Quasithin.H13.NQCat
