module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6TorusFrameComp
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusPackage

public section

namespace CFSG.StandardType

private noncomputable def pElementsMapEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (T : Subgroup G) (p : ℕ) :
    {y : G // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} ≃
      {y : H // y ∈ T.map e.toMonoidHom ∧ ∃ k : ℕ, y ^ p ^ k = 1} where
  toFun y := by
    refine ⟨e y.1, ⟨y.1, y.2.1, rfl⟩, ?_⟩
    obtain ⟨k, hk⟩ := y.2.2
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  invFun y := by
    refine ⟨e.symm y.1, ?_, ?_⟩
    · obtain ⟨x, hx, hxe⟩ := y.2.1
      have hxey : e.symm y.1 = x := by
        rw [← hxe]
        exact e.symm_apply_apply x
      rw [hxey]
      exact hx
    · obtain ⟨k, hk⟩ := y.2.2
      refine ⟨k, e.injective ?_⟩
      simp only [map_pow, e.apply_symm_apply, hk, map_one]
  left_inv y := Subtype.ext (e.symm_apply_apply y.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

private theorem card_pElements_map_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (T : Subgroup G) (p : ℕ) :
    Nat.card {y : H // y ∈ T.map e.toMonoidHom ∧ ∃ k : ℕ, y ^ p ^ k = 1} =
      Nat.card {y : G // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} :=
  (Nat.card_congr (pElementsMapEquiv e T p)).symm

private theorem card_pElements_abelian {G : Type*} [Group G] (T : Subgroup G)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {p q j e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hcard : Nat.card T * 3 ^ j = q ^ 6) (hcardTne : Nat.card T ≠ 0)
    (hpq : padicValNat p q = e) :
    Nat.card {y : G // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (6 * e) := by
  classical
  have : Finite T := Nat.finite_of_card_ne_zero hcardTne
  let P : Subgroup G :=
    { carrier := {y : G | y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1}
      one_mem' := ⟨T.one_mem, ⟨0, by simp⟩⟩
      mul_mem' := by
        rintro y z ⟨hyT, hyPe⟩ ⟨hzT, hzPe⟩
        refine ⟨T.mul_mem hyT hzT, ?_⟩
        obtain ⟨a, ha⟩ := hyPe
        obtain ⟨b, hb⟩ := hzPe
        refine ⟨max a b, ?_⟩
        have hya : y ^ p ^ max a b = 1 := by
          have h1 : orderOf y ∣ p ^ a := orderOf_dvd_iff_pow_eq_one.mpr ha
          have h2 : p ^ a ∣ p ^ max a b := pow_dvd_pow p (le_max_left a b)
          exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)
        have hzb : z ^ p ^ max a b = 1 := by
          have h1 : orderOf z ∣ p ^ b := orderOf_dvd_iff_pow_eq_one.mpr hb
          have h2 : p ^ b ∣ p ^ max a b := pow_dvd_pow p (le_max_right a b)
          exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)
        have hcommyz : Commute y z := hcomm y hyT z hzT
        calc (y * z) ^ p ^ max a b
            = y ^ p ^ max a b * z ^ p ^ max a b := hcommyz.mul_pow _
          _ = 1 := by rw [hya, hzb, mul_one]
      inv_mem' := by
        rintro y ⟨hyT, hyPe⟩
        refine ⟨T.inv_mem hyT, ?_⟩
        obtain ⟨a, ha⟩ := hyPe
        exact ⟨a, by rw [inv_pow, ha, inv_one]⟩ }
  have hPT : P ≤ T := fun y hy => hy.1
  have hPgroup : IsPGroup p (P.subgroupOf T) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    have hg : ((g : ↥T) : G) ∈ P := by
      simpa only [Subgroup.mem_subgroupOf] using g.2
    obtain ⟨k, hk⟩ := hg.2
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hPgroup
  have hQP : (Q : Subgroup ↥T) ≤ P.subgroupOf T := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨k, hk⟩ := (Sylow.isPGroup' Q).exists_pow_pow_eq_one ⟨y, hy⟩
    refine ⟨(y : ↥T).2, k, ?_⟩
    have h := congrArg (fun z : ↥Q => ((z : ↥T) : G)) hk
    simpa using h
  have hEq : (Q : Subgroup ↥T) = P.subgroupOf T := le_antisymm hQP hPQ
  have hcardPsub : Nat.card (P.subgroupOf T) = p ^ (Nat.card T).factorization p := by
    rw [← hEq]
    exact Sylow.card_eq_multiplicity Q
  have hpow : padicValNat p (Nat.card T) = 6 * e := by
    have hmul := padicValNat.mul (p := p) hcardTne (pow_ne_zero j (by norm_num : (3 : ℕ) ≠ 0))
    rw [hcard, padicValNat.pow] at hmul
    have h3 : padicValNat p (3 ^ j) = 0 := by
      rw [padicValNat.pow]
      have hp3val : padicValNat p 3 = 0 := by
        by_contra hne
        have hle : 1 ≤ padicValNat p 3 := Nat.one_le_iff_ne_zero.mpr hne
        have hdvd : p ^ 1 ∣ 3 :=
          (Nat.pow_dvd_iff_le_padicValNat (p := p) (k := 1) (n := 3)
            (Fact.out : p.Prime).ne_one (by norm_num)).2 hle
        exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).1
          (by simpa using hdvd))
      rw [hp3val, mul_zero]
    rw [hpq] at hmul
    omega
  have hcardP : Nat.card P = p ^ (6 * e) := by
    have h1 : Nat.card P = Nat.card (P.subgroupOf T) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT)).symm
    rw [h1, hcardPsub, Nat.factorization_def (Nat.card T) (Fact.out : p.Prime), hpow]
  have hfinal : Nat.card {y : G // y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} = Nat.card P :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1, y.2⟩
        invFun := fun y => ⟨y.1, y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  rw [hfinal]
  exact hcardP

namespace ExcFrames

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_torusFramePackage
    {f p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    TwE6TB.GGTwE6TorusFramePackage p ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (by norm_num))
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, hlang, hι₀, hbase, hTcomm, hrangeT, htors,
    ⟨j, hjcard⟩, hcent⟩ := exists_langFrame hp5 hf hpq K hK σ hσ L Fr hFr
  obtain ⟨t', m', ht', hact', hU', -⟩ := exists_frameAutPackage hp5 hf hpq K hK σ hσ
  have hp3 : p ≠ 3 := by omega
  have hXel : IsElemAbelian p ι₀.range := by
    let : Module (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p) := inferInstance
    exact NoOffE8Five.isElemAbelian_range_of_module (p := p) ι₀
  have hXcard : Nat.card ι₀.range = p ^ 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι₀).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    simp [ZMod.card]
    rfl
  have hXsc : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ x ∈ ι₀.range, c * x = x * c) → c ^ p = 1 → c ∈ ι₀.range :=
    fun c hc hcp => htors c (hcent c hc) hcp
  have h54 : p ^ 4 ≤ Nat.card ι₀.range := by
    rw [hXcard]
    exact Nat.pow_le_pow_right (by omega : 0 < p) (by norm_num : 4 ≤ 6)
  obtain ⟨c, hc⟩ := hU' ι₀.range hXel h54 hXsc
  let T' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    T.map (MulAut.conj c⁻¹).toMonoidHom
  have ht'range : t'.range = ι₀.range.map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [hc, Subgroup.map_map]
    have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom
        = MonoidHom.id ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
      refine MonoidHom.ext fun x => ?_
      change c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x
      group
    rw [hcomp, Subgroup.map_id]
  have hmapc : t'.range.map (MulAut.conj c).toMonoidHom = ι₀.range := by
    rw [ht'range, Subgroup.map_map]
    have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj c⁻¹).toMonoidHom
        = MonoidHom.id ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
      refine MonoidHom.ext fun x => ?_
      change c * (c⁻¹ * x * (c⁻¹)⁻¹) * c⁻¹ = x
      group
    rw [hcomp, Subgroup.map_id]
  have hle' : t'.range ≤ T' := by
    rw [ht'range]
    exact Subgroup.map_mono hrangeT
  have hT'comm : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show (MulAut.conj c⁻¹) x * (MulAut.conj c⁻¹) y = (MulAut.conj c⁻¹) y * (MulAut.conj c⁻¹) x
    rw [← map_mul, ← map_mul, hTcomm x hx y hy]
  have hcent' : ∀ b : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ x ∈ t'.range, b * x = x * b) → b ∈ T' := by
    intro b hb
    have hbT : c * b * c⁻¹ ∈ T := by
      apply hcent
      intro x hx
      have hy : (MulAut.conj c⁻¹) x ∈ t'.range := by
        rw [ht'range]
        exact ⟨x, hx, rfl⟩
      have hcomm := hb _ hy
      show (c * b * c⁻¹) * x = x * (c * b * c⁻¹)
      calc (c * b * c⁻¹) * x = c * (b * ((MulAut.conj c⁻¹) x)) * c⁻¹ := by
            simp only [MulAut.conj_apply]
            group
        _ = c * (((MulAut.conj c⁻¹) x) * b) * c⁻¹ := by rw [hcomm]
        _ = x * (c * b * c⁻¹) := by
            simp only [MulAut.conj_apply]
            group
    exact ⟨c * b * c⁻¹, hbT, by
      show (MulAut.conj c⁻¹) (c * b * c⁻¹) = b
      rw [MulAut.conj_apply]
      group⟩
  have htors' : ∀ y ∈ T', y ^ p = 1 → y ∈ t'.range := by
    intro y hy hyp
    obtain ⟨x, hxT, rfl⟩ := hy
    have hxp : x ^ p = 1 := by
      have hf : Function.Injective (MulAut.conj c⁻¹).toMonoidHom := (MulAut.conj c⁻¹).injective
      apply hf
      rw [map_pow, hyp, map_one]
    rw [ht'range]
    exact ⟨x, htors x hxT hxp, rfl⟩
  let d := padicValNat p (2 ^ f + 1)
  have hpe : p ^ d ∣ 2 ^ f + 1 := pow_padicValNat_dvd (p := p) (n := 2 ^ f + 1)
  have hcardT : Nat.card {y : ↥(graphFixedRootGroup TwistTag.E6 K σ) //
      y ∈ T ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (6 * d) := by
    have hTne : Nat.card T ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hjcard
      exact (pow_ne_zero 6 (by exact Nat.succ_ne_zero (2 ^ f))) hjcard.symm
    exact card_pElements_abelian T hTcomm hp3 hjcard hTne rfl
  have hcardT' : Nat.card {y : ↥(graphFixedRootGroup TwistTag.E6 K σ) //
      y ∈ T' ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (6 * d) := by
    change Nat.card {y : ↥(graphFixedRootGroup TwistTag.E6 K σ) //
      y ∈ T.map (MulAut.conj c⁻¹).toMonoidHom ∧ ∃ k : ℕ, y ^ p ^ k = 1} = p ^ (6 * d)
    rw [card_pElements_map_mulEquiv (MulAut.conj c⁻¹) T p, hcardT]
  have hcomp' : ∀ x ∈ t'.range, x ≠ 1 → ∀ J' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ),
      IsComponentOf J' (Subgroup.centralizer {x}) →
      ∃ s ∈ J', s ∈ T' ∧ orderOf s = p ^ d := by
    intro x hx hx1 J' hJ'
    let w : ↥(graphFixedRootGroup TwistTag.E6 K σ) := MulAut.conj c x
    have hw : w ∈ ι₀.range := by
      have hmem : w ∈ t'.range.map (MulAut.conj c).toMonoidHom := ⟨x, hx, rfl⟩
      rwa [hmapc] at hmem
    have hw1 : w ≠ 1 := by
      intro h
      apply hx1
      have h' : (MulAut.conj c⁻¹) ((MulAut.conj c) x) = 1 := by
        simpa only [w, map_one] using congrArg (MulAut.conj c⁻¹) h
      have hcancel : (MulAut.conj c⁻¹) ((MulAut.conj c) x) = x := by
        simp only [MulAut.conj_apply]
        group
      rwa [hcancel] at h'
    have hJw : IsComponentOf (J'.map (MulAut.conj c).toMonoidHom)
        (Subgroup.centralizer {w}) := by
      have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv
        (MulAut.conj c) hJ'
      rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton (MulAut.conj c) x] at h
    have hJwA : CFSG.Assembly.IsComponentOf (J'.map (MulAut.conj c).toMonoidHom)
        (Subgroup.centralizer {w}) := CFSG.Assembly.isComponentOf_iff_open.mpr hJw
    obtain ⟨y, hyJw, hyT, hyord⟩ :=
      exists_fullOrder_of_component hp5 hf hpq hpe K hK σ hσ L Fr hFr hg₀C hlang
        T ι₀ hbase hcent hw hw1 hJwA
    refine ⟨(MulAut.conj c⁻¹) y, ?_, ?_, ?_⟩
    · obtain ⟨z, hzJ', hzy⟩ := hyJw
      rw [← hzy]
      have hcancel : (MulAut.conj c⁻¹) ((MulAut.conj c).toMonoidHom z) = z := by
        show (MulAut.conj c⁻¹) ((MulAut.conj c) z) = z
        simp only [MulAut.conj_apply]
        group
      rw [hcancel]
      exact hzJ'
    · exact ⟨y, hyT, rfl⟩
    · have hord : orderOf ((MulAut.conj c⁻¹) y) = orderOf y :=
        orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective y
      rw [hord, hyord]
  exact ⟨t', m', T', d, ht', hact', hU', hT'comm, hle', hcent', htors', hcardT', hcomp'⟩

end ExcFrames

namespace TwE6TB

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTwE6TorusFramePackage_of_mulEquiv {p : ℕ} [NeZero p] {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGTwE6TorusFramePackage p R) : GGTwE6TorusFramePackage p R' := by
  obtain ⟨t, m, T, d, ht, hact, hU, hTcomm, hle, hcent, htors, hcard, hcomp⟩ := h
  refine ⟨e.toMonoidHom.comp t, e.toMonoidHom.comp m, T.map e.toMonoidHom, d,
    e.injective.comp ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v s
    simpa only [MonoidHom.comp_apply, map_mul, map_inv] using congrArg e.toMonoidHom (hact v s)
  · intro E' hE' h4' hSC'
    let E : Subgroup R := E'.comap e.toMonoidHom
    have hE : IsElemAbelian p E := by
      dsimp only [E]
      rw [Subgroup.comap_equiv_eq_map_symm' e E']
      exact IsElemAbelian.map hE' e.symm.toMonoidHom
    have hcardE : Nat.card E = Nat.card E' := by
      dsimp only [E]
      rw [Subgroup.comap_equiv_eq_map_symm' e E',
        Subgroup.card_map_of_injective e.symm.injective]
    have h4 : p ^ 4 ≤ Nat.card E := by rw [hcardE]; exact h4'
    have hmap : E' = E.map e.toMonoidHom := by
      dsimp only [E]
      exact (Subgroup.map_comap_eq_self_of_surjective e.surjective E').symm
    have hSC : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E := by
      intro g hg hgp
      show e g ∈ E'
      apply hSC' (e g)
      · intro y hy
        rw [hmap] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        show e g * e x = e x * e g
        rw [← map_mul, ← map_mul, hg x hx]
      · rw [← map_pow, hgp, map_one]
    obtain ⟨c, hc⟩ := hU E hE h4 hSC
    refine ⟨e c, ?_⟩
    rw [hmap, hc, MonoidHom.range_comp]
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change e (c * x * c⁻¹) = e c * e x * (e c)⁻¹
    rw [map_mul, map_mul, map_inv]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hTcomm x hx y hy]
  · rintro _ ⟨s, rfl⟩
    exact ⟨t s, hle ⟨s, rfl⟩, rfl⟩
  · intro b hb
    have hbR : e.symm b ∈ T := by
      apply hcent
      intro x hx
      have hmem : e x ∈ (e.toMonoidHom.comp t).range := by
        rw [MonoidHom.range_comp]
        exact ⟨x, hx, rfl⟩
      have h := hb (e x) hmem
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact h
    exact ⟨e.symm b, hbR, e.apply_symm_apply b⟩
  · intro y hy hyp
    obtain ⟨x, hxT, rfl⟩ := hy
    have hxp : x ^ p = 1 := by
      have hf : Function.Injective e.toMonoidHom := e.injective
      apply hf
      rw [map_pow, hyp, map_one]
    rw [MonoidHom.range_comp]
    exact ⟨x, htors x hxT hxp, rfl⟩
  · rw [card_pElements_map_mulEquiv e T p, hcard]
  · intro x' hx' hx'1 J' hJ'
    rw [MonoidHom.range_comp] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    have hx1 : x ≠ 1 := fun h => hx'1 (by rw [h, map_one])
    have hJ'x : IsComponentOf J' (Subgroup.centralizer {e x}) := hJ'
    let J : Subgroup R := J'.map e.symm.toMonoidHom
    have hJ : IsComponentOf J (Subgroup.centralizer {x}) := by
      have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv e.symm hJ'x
      rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e.symm (e x),
        e.symm_apply_apply] at h
    obtain ⟨s, hsJ, hsT, hsord⟩ := hcomp x hx hx1 J hJ
    refine ⟨e s, ?_, ⟨s, hsT, rfl⟩, ?_⟩
    · obtain ⟨z, hzJ', hzs⟩ := hsJ
      simpa [← hzs] using hzJ'
    · have hord : orderOf (e s) = orderOf s :=
        orderOf_injective e.toMonoidHom e.injective s
      rw [hord, hsord]

theorem ggTwE6TorusFramePackage_recipeR
    {n p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    GGTwE6TorusFramePackage p (TwE6Delta.RecipeR K n) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK
    (iterateFrobenius K 2 n) (iterateFrobenius_def 2 n)
  exact ggTwE6TorusFramePackage_of_mulEquiv e.symm
    (ExcFrames.exists_torusFramePackage hp5 hn hpq K hK (iterateFrobenius K 2 n)
      (iterateFrobenius_def 2 n))

end TwE6TB

end CFSG.StandardType
