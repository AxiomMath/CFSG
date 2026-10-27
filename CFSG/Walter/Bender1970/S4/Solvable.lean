module

public import CFSG.Walter.Bender1970.S4.Rank
import CFSG.FeitThompson.OddOrderTheorem
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.Open CFSG.SectionRank CFSG.SectionRank.Ccomm

section Perfect

variable {G : Type*} [Group G]

theorem le_ker_of_isPerfect {A : Type*} [Group A] [Group.IsSolvable A] (K : Subgroup G)
    [Group.IsPerfect K] (f : G →* A) : K ≤ f.ker := by
  have : Group.IsPerfect (f.comp K.subtype).range := Group.IsPerfect.range _
  have : Subsingleton (f.comp K.subtype).range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (f.comp K.subtype).range inferInstance
  intro k hk
  have h1 : (⟨f k, ⟨k, hk⟩, rfl⟩ : (f.comp K.subtype).range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem eq_bot_of_isPerfect_of_le_isSolvable {K L : Subgroup G} [Group.IsPerfect K] (hKL : K ≤ L)
    (hL : Group.IsSolvable L) : K = ⊥ := by
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKL)
      (Subgroup.inclusion_injective hKL)
  have : Subsingleton K := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable K inferInstance
  exact Subgroup.eq_bot_of_subsingleton K

theorem exists_derivedSeries_succ_eq (X : Type*) [Group X] [Finite X] :
    ∃ n : ℕ, derivedSeries X (n + 1) = derivedSeries X n := by
  by_contra h
  push Not at h
  have key : ∀ n : ℕ, Nat.card (derivedSeries X n) + n ≤ Nat.card X := by
    intro n
    induction n with
    | zero => rw [derivedSeries_zero, Subgroup.card_top, add_zero]
    | succ n ih =>
      have hle : derivedSeries X (n + 1) ≤ derivedSeries X n :=
        derivedSeries_antitone X (Nat.le_succ n)
      have hlt : Nat.card (derivedSeries X (n + 1)) < Nat.card (derivedSeries X n) :=
        Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (h n))
      omega
  have h1 := key (Nat.card X)
  have h2 := Nat.card_pos (α := derivedSeries X (Nat.card X))
  omega

end Perfect

section GLTwo

theorem matrix_fin_two_eq_one_or_neg_one {k : Type*} [Field k] {M : Matrix (Fin 2) (Fin 2) k}
    (h2 : (2 : k) ≠ 0) (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [Matrix.det_fin_two_of] at hdet
  rw [Matrix.mul_fin_two, Matrix.one_fin_two] at hM
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10
  have hs : a + d ≠ 0 := fun hs => h2 (by linear_combination -e00 - hdet + a * hs)
  have hb : b = 0 :=
    (mul_eq_zero.1 (show b * (a + d) = 0 by linear_combination e01)).resolve_right hs
  have hc : c = 0 :=
    (mul_eq_zero.1 (show c * (a + d) = 0 by linear_combination e10)).resolve_right hs
  subst hb hc
  have ha0 : a ≠ 0 := fun ha => by rw [ha] at e00; simp at e00
  have hd : d = a := sub_eq_zero.1 ((mul_eq_zero.1 (show a * (d - a) = 0 by
    linear_combination hdet - e00)).resolve_left ha0)
  subst hd
  rcases mul_eq_zero.1 (show (d - 1) * (d + 1) = 0 by linear_combination e00) with ha | ha
  · left
    rw [sub_eq_zero.1 ha, Matrix.one_fin_two]
  · right
    rw [eq_neg_of_add_eq_zero_left ha, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem eq_bot_of_isPerfect_le_mulAut {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {W : Type*}
    [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1) (hcard : Nat.card W ≤ p ^ 2)
    {Y : Subgroup (MulAut W)} (hY : BenderSuzuki.HasAbelianSylow 2 Y) [Group.IsPerfect Y] :
    Y = ⊥ := by
  classical
  have hWp : IsPGroup p W := fun w => ⟨1, by rw [pow_one, hpow]⟩
  obtain ⟨d, hd⟩ := hWp.exists_card_eq
  have hd2 : d ≤ 2 := by
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hd
  set φ := elemAutEquivGL e with hφ
  set Y' := Y.map φ.toMonoidHom with hY'
  have : Group.IsPerfect Y' := Group.IsPerfect.map _
  suffices hY'1 : Y' = ⊥ by
    rwa [hY', Subgroup.map_eq_bot_iff_of_injective _ φ.injective] at hY'1
  have hY'syl : BenderSuzuki.HasAbelianSylow 2 Y' :=
    hY.of_mulEquiv (Y.equivMapOfInjective φ.toMonoidHom φ.injective)
  have hdet : ∀ g ∈ Y', Matrix.GeneralLinearGroup.det g = 1 := fun g hg =>
    le_ker_of_isPerfect Y' Matrix.GeneralLinearGroup.det hg
  rcases Nat.lt_or_ge d 2 with hlt | hge
  ·
    have hc : ∀ a b : GL (Fin d) (ZMod p), a * b = b * a := by
      interval_cases d
      · intro a b
        exact Subsingleton.elim _ _
      · exact GL_one_comm
    have : IsMulCommutative Y' := ⟨⟨fun a b => Subtype.ext (hc a b)⟩⟩
    exact Subgroup.eq_bot_of_subsingleton Y'
  have hd2' : d = 2 := le_antisymm hd2 hge
  subst hd2'
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have hinv : ∀ g ∈ Y', g ^ 2 = 1 → g ≠ 1 → g = -1 := by
    intro g hg hg2 hg1
    have hM : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) * g = 1 := by
      rw [← Units.val_mul, ← pow_two, hg2, Units.val_one]
    have hdetM : (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
      have h' := congrArg Units.val (hdet g hg)
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h'
    rcases matrix_fin_two_eq_one_or_neg_one h2 hM hdetM with h | h
    · exact absurd (Units.ext h) hg1
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 Y') := inferInstance
  have hScomm : IsMulCommutative (S : Subgroup Y') := hY'syl S
  have hScyc : IsCyclic (S : Subgroup Y') := by
    by_contra hcyc
    obtain ⟨r, hr, E, hES, -, hEexp, hEcard⟩ := exists_elementary_of_not_isCyclic hScomm hcyc
    have hr2 : r = 2 := by
      have : Fact r.Prime := ⟨hr⟩
      have hE1 : Nontrivial E := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        have := hr.two_le
        nlinarith
      obtain ⟨x, hx⟩ := exists_ne (1 : E)
      have hxo : orderOf (x : Y') = r := orderOf_eq_prime (hEexp x x.2)
        (fun h => hx (Subtype.ext h))
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hES x.2⟩
      have hdvd : r ∣ 2 ^ k := by
        rw [← hxo]
        exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd)
    subst hr2
    obtain ⟨a, haE, ha1, -⟩ := exists_mem_ne_one_ne (Q := E) (by nlinarith) (1 : Y')
    obtain ⟨b, hbE, hb1, hba⟩ := exists_mem_ne_one_ne (Q := E) (by nlinarith) a
    have hav := hinv (a : GL (Fin 2) (ZMod p)) a.2
      (by rw [← Subgroup.coe_pow, hEexp a haE, Subgroup.coe_one])
      (fun h => ha1 (Subtype.ext h))
    have hbv := hinv (b : GL (Fin 2) (ZMod p)) b.2
      (by rw [← Subgroup.coe_pow, hEexp b hbE, Subgroup.coe_one])
      (fun h => hb1 (Subtype.ext h))
    exact hba (Subtype.ext (hbv.trans hav.symm))
  have hodd : Odd (Nat.card Y') := by
    by_contra hodd
    have hmin : (Nat.card Y').minFac = 2 :=
      (Nat.minFac_eq_two_iff _).2 (Nat.not_odd_iff_even.mp hodd).two_dvd
    have hNC := hScyc.normalizer_le_centralizer hmin
    have hScenter : (S : Subgroup Y') ≤
        CFSG.centerIn (G := Y') (Subgroup.normalizer ((S : Subgroup Y') : Set Y')) := by
      intro s hs
      refine ⟨S.le_normalizer hs, ?_⟩
      change s ∈ Subgroup.centralizer ((Subgroup.normalizer ((S : Subgroup Y') : Set Y')) : Set Y')
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact ((Subgroup.mem_centralizer_iff.mp (hNC hn)) s hs).symm
    obtain ⟨N, hNn, hNcop, hquot⟩ :=
      CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 2 S
        hScenter
    have : Group.IsNilpotent (Y' ⧸ N) := hquot.isNilpotent
    have : Group.IsSolvable (Y' ⧸ N) := inferInstance
    have hN : N = ⊤ := by
      have h := le_ker_of_isPerfect (⊤ : Subgroup Y') (QuotientGroup.mk' N)
      rw [QuotientGroup.ker_mk'] at h
      exact top_le_iff.mp h
    apply hodd
    rw [← Subgroup.card_top (G := Y'), ← hN]
    exact hNcop.odd_of_left
  have : Group.IsSolvable Y' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Subsingleton Y' := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable Y' inferInstance
  exact Subgroup.eq_bot_of_subsingleton Y'

end GLTwo

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_isPerfect {D Q : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : HasAbelianSylowTwo D) [Group.IsPerfect D] (hQp : IsPGroup p Q)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : rank Q ≤ 2) :
    D ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hQ1 : Q = ⊥
  · intro d _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hQ1, SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  obtain ⟨D₀, hD₀c, -, hD₀exp, -, -, hker⟩ := supercritical_witness hp2 hQp
  have hD₀p : IsPGroup p D₀ := hQp.to_subgroup D₀
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hD₀p
  have hexpD : ∀ x : D₀, x ^ p = 1 := fun x => Subtype.ext (hD₀exp x x.2)
  have hrankD : CFSG.Open.pRank p (⊤ : Subgroup D₀) ≤ 2 := by
    let ι : D₀ →* G := Q.subtype.comp D₀.subtype
    have hι : Function.Injective ι := Q.subtype_injective.comp D₀.subtype_injective
    have hle : (⊤ : Subgroup D₀).map ι ≤ Q := by
      rintro _ ⟨x, -, rfl⟩
      exact (x : Q).2
    calc CFSG.Open.pRank p (⊤ : Subgroup D₀) ≤ CFSG.Open.pRank p ((⊤ : Subgroup D₀).map ι) :=
          pRank_le_map hp.one_lt ι hι ⊤
      _ ≤ CFSG.Open.pRank p Q := pRank_mono hp.one_lt hle
      _ = rank Q := (rank_eq_pRank_of_isPGroup hp hQp).symm
      _ ≤ 2 := hQ2
  have hWcard : Nat.card (D₀ ⧸ frattini D₀) ≤ p ^ 2 :=
    (rank_two_exponent_prime_order_bound hD₀p hexpD hrankD).2
  let _ : MulDistribMulAction D Q := Subgroup.conjMulDistribMulActionOfLeNormalizer D Q hDQ
  let ρ₀ : D →* MulAut Q := MulDistribMulAction.toMulAut D Q
  have hρ₀ : ∀ (d : D) (x : Q), ((ρ₀ d x : Q) : G) = (d : G) * x * (d : G)⁻¹ :=
    fun _ _ => rfl
  let ρ : D →* MulAut (D₀ ⧸ frattini D₀) := (frattiniAction D₀).comp ρ₀
  have hY : BenderSuzuki.HasAbelianSylow 2 ρ.range :=
    ((show BenderSuzuki.HasAbelianSylow 2 D from hD)).mapSurjective ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hρ1 : ρ.range = ⊥ := eq_bot_of_isPerfect_le_mulAut hp2 hWcomm hWpow hWcard hY
  have hρ₀ker : ρ₀.range ≤ (frattiniAction D₀).ker := by
    rintro _ ⟨d, rfl⟩
    rw [MonoidHom.mem_ker]
    have : ρ d ∈ ρ.range := ⟨d, rfl⟩
    rw [hρ1, Subgroup.mem_bot] at this
    exact this
  have : Group.IsPerfect ρ₀.range := Group.IsPerfect.range ρ₀
  have hρ₀p : IsPGroup p ρ₀.range := hker.to_le hρ₀ker
  have hρ₀1 : ρ₀.range = ⊥ := by
    have : Group.IsNilpotent ρ₀.range := hρ₀p.isNilpotent
    have : Subsingleton ρ₀.range := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact Group.IsPerfect.not_isNilpotent ρ₀.range inferInstance
    exact Subgroup.eq_bot_of_subsingleton _
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : ρ₀ ⟨d, hd⟩ = 1 := by
    have : ρ₀ ⟨d, hd⟩ ∈ ρ₀.range := ⟨_, rfl⟩
    rw [hρ₀1, Subgroup.mem_bot] at this
    exact this
  have h2 := congrArg (fun α : MulAut Q => ((α ⟨x, hx⟩ : Q) : G)) h1
  simp only [hρ₀, MulAut.one_apply] at h2
  calc x * d = d * x * d⁻¹ * d := by rw [h2]
    _ = d * x := by group

instance componentLayerOf_subgroupOf_normal (H : Subgroup G) :
    ((componentLayerOf H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (componentLayerOf_isNormalIn H).1).mpr
    (le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn H))

theorem bender1970_4_3
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) :
    Group.IsSolvable (H ⧸ (componentLayerOf H).subgroupOf H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHA := hG.isAStar_of_isCoatom (isCoatom_of_mem_benderM hH)
  obtain ⟨n, hn⟩ := exists_derivedSeries_succ_eq H
  set D := derivedSeries H n with hDdef
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr (by rw [← derivedSeries_succ, hn])
  set D' := D.map H.subtype with hD'def
  have : Group.IsPerfect D' := Group.IsPerfect.map _
  have hD'H : D' ≤ H := Subgroup.map_subtype_le D
  have hDO : D ≤ oStar H := by
    have : (oStar H).Normal := oStar_normal
    have hodd : Odd (Nat.card (H ⧸ oStar H)) := by
      rw [← Subgroup.index_eq_card, oStar, Subgroup.index_comap_of_surjective _
        (QuotientGroup.mk'_surjective _)]
      exact hHA.2.1
    have : Group.IsSolvable (H ⧸ oStar H) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have h := le_ker_of_isPerfect D (QuotientGroup.mk' (oStar H))
    rwa [QuotientGroup.ker_mk'] at h
  have hD2 : D' ≤ Subgroup.centralizer (qCoreOf H 2 : Set G) := by
    set N := H ⊓ Subgroup.centralizer (qCoreOf H 2 : Set G) with hNdef
    set C := N.subgroupOf H with hCdef
    have : C.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      fun h hh => mem_normalizer_inf (Subgroup.le_normalizer hh)
        (Bender35.mem_normalizer_centralizer
          (le_normalizer_of_isNormalIn (qCoreOf_normal_in H 2) hh))
    obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
    have hSC : (S : Subgroup H) ≤ C := by
      intro s hs
      refine Subgroup.mem_subgroupOf.mpr ⟨s.2, ?_⟩
      have hP : IsPGroup 2 ((S : Subgroup H).map H.subtype) := S.isPGroup'.map _
      exact le_centralizer_twoCore_of_hasAbelianSylowTwo hHA.1 (Subgroup.map_subtype_le _) hP
        ⟨s, hs, rfl⟩
    have hodd : Odd (Nat.card (H ⧸ C)) := by
      rw [← Subgroup.index_eq_card]
      have h1 : C.index ∣ (S : Subgroup H).index := Subgroup.index_dvd_of_le hSC
      have h2 : ¬ 2 ∣ (S : Subgroup H).index := S.not_dvd_index
      exact Nat.not_even_iff_odd.mp fun he => h2 (he.two_dvd.trans h1)
    have : Group.IsSolvable (H ⧸ C) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have h := le_ker_of_isPerfect D (QuotientGroup.mk' C)
    rw [QuotientGroup.ker_mk'] at h
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (h hx)).2
  have hDq : ∀ q : ℕ, q.Prime → q ≠ 2 → D' ≤ Subgroup.centralizer (qCoreOf H q : Set G) :=
    fun q hq hq2 => le_centralizer_of_isPerfect hq hq2 (hG.hasAbelianSylowTwo.subgroup D')
      (qCoreOf_isPGroup H q) (hD'H.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in H q)))
      (Bender42.rank_qCoreOf_le_two hG ht hH hq hq2)
  have hDF : D' ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf H : Set G) := by
    rw [Subgroup.le_centralizer_iff, (show CFSG.fittingSubgroupOf H = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf H)]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    rw [← Subgroup.le_centralizer_iff]
    by_cases hq2 : q.1.1 = 2
    · rw [hq2]
      exact hD2
    · exact hDq q.1.1 hq hq2
  have hDFs : D' ≤ generalizedFittingSubgroupOf H :=
    le_generalizedFittingSubgroupOf_of_le_oStar hHA (Subgroup.map_mono hDO) hDF
  set E' := (componentLayerOf H).subgroupOf H with hE'def
  set F' := (CFSG.fittingSubgroupOf H).subgroupOf H with hF'def
  have hF'eq : F' = CFSG.fittingSubgroup H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hDF' : D ≤ F' ⊔ E' := by
    intro x hx
    have hx' : (x : G) ∈ generalizedFittingSubgroupOf H := hDFs ⟨x, hx, rfl⟩
    rw [hF'def, hE'def, ← Subgroup.subgroupOf_sup (CFSG.fittingSubgroupOf_le H)
      (componentLayerOf_isNormalIn H).1]
    exact Subgroup.mem_subgroupOf.mpr hx'
  have hDE : D ≤ E' := by
    set π := QuotientGroup.mk' E' with hπdef
    have : Group.IsPerfect (D.map π) := Group.IsPerfect.map _
    have hF'solv : Group.IsSolvable F' := by
      rw [hF'eq]
      infer_instance
    have hFsolv : Group.IsSolvable (F'.map π) :=
      Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π F')
    have hle : D.map π ≤ F'.map π := by
      calc D.map π ≤ (F' ⊔ E').map π := Subgroup.map_mono hDF'
        _ = F'.map π ⊔ E'.map π := Subgroup.map_sup _ _ _
        _ = F'.map π := by
          rw [(Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' E').ge, sup_bot_eq]
    have hbot := eq_bot_of_isPerfect_of_le_isSolvable hle hFsolv
    rwa [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk'] at hbot
  rw [Group.isSolvable_def]
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective E') n, ← hDdef, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
  exact hDE

end CFSG.Walter
