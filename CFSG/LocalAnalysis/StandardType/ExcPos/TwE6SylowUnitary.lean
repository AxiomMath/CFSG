module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTwE6
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Two
public import CFSG.CGT.PushingUpLit.BHSSym.SylowTransfer
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.GGFinModel CFSG.Open CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE Polynomial

open scoped Matrix

set_option linter.unusedSectionVars false

private theorem lk0xttb_sylow_in_torus {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {C : Type} [Group C] {D : LangDatum τ L} {ι : C →* ModGL τ L}
    (hp : p.Prime) (hι : Function.Injective ι) (hd : LangDescent D p ι)
    (hord : (Nat.card C).factorization p ≤ (Nat.card D.torus).factorization p) :
    ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfm := hd.finite_model
  have hTM := D.torus_le_model
  haveI hTfin : Finite D.torus :=
    Finite.of_injective (Subgroup.inclusion hTM) (Subgroup.inclusion_injective hTM)
  have hΓfin : Finite D.Γ :=
    Finite.of_injective (Subgroup.inclusion hd.Γ_le_model) (Subgroup.inclusion_injective _)
  obtain ⟨P0⟩ : Nonempty (Sylow p D.torus) := inferInstance
  set P1 : Subgroup (ModGL τ L) := (P0 : Subgroup D.torus).map D.torus.subtype with hP1
  have hP1T : P1 ≤ D.torus := Subgroup.map_subtype_le _
  have hP1p : IsPGroup p P1 := P0.isPGroup'.map _
  have hP1Γ : P1 ≤ D.Γ := hd.pgroup_le_Γ P1 (hP1T.trans hTM) hP1p
  have hP1card : Nat.card P1 = p ^ (Nat.card D.torus).factorization p := by
    rw [hP1, Subgroup.card_map_of_injective D.torus.subtype_injective, Sylow.card_eq_multiplicity]
  set P2 : Subgroup D.Γ := P1.subgroupOf D.Γ with hP2
  have hP2card : Nat.card P2 = Nat.card P1 := by
    rw [← Subgroup.card_map_of_injective D.Γ.subtype_injective, hP2, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hP1Γ]
  have hΓcard : Nat.card D.Γ = Nat.card C := (Nat.card_congr (hd.mulEquiv hι).toEquiv).symm
  have hle : (Nat.card D.torus).factorization p ≤ (Nat.card D.Γ).factorization p := by
    have hdvd : p ^ (Nat.card D.torus).factorization p ∣ Nat.card D.Γ := by
      rw [← hP1card, ← hP2card]
      exact Subgroup.card_subgroup_dvd_card P2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 hdvd
  have hcard : Nat.card P2 = p ^ (Nat.card D.Γ).factorization p := by
    rw [hP2card, hP1card]
    congr 1
    rw [hΓcard]
    exact le_antisymm (hΓcard ▸ hle) hord
  refine ⟨Sylow.ofCard P2 hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hP1T hx)

private theorem lk0xttb_permLattice_one {τ : Tag} (u : Fin τ.rank → ℤ) :
    permLattice (1 : Equiv.Perm (Fin τ.rank)) u = u := rfl

private theorem lk0xttb_permCongr_one {R N : ℕ} (h : R = N) :
    (finCongr h).permCongr (1 : Equiv.Perm (Fin R)) = (1 : Equiv.Perm (Fin N)) := by
  subst h
  rfl

private theorem lk0xttb_permLattice_permCongr_one {τ : Tag} {R : ℕ}
    (h : R = τ.rank) (u : Fin τ.rank → ℤ) :
    permLattice ((finCongr h).permCongr (1 : Equiv.Perm (Fin R))) u = u := by
  rw [lk0xttb_permCongr_one, lk0xttb_permLattice_one]

private theorem lk0xttb_hv (x : Fin (langTag .twistedE6).rank → ℤ) :
    ((coxeterSystem (langTag .twistedE6)).wordProd
      (twE6TwoWord : List (Fin (langTag .twistedE6).rank))) • x =
      toMat (langTag .twistedE6).rank twE6TwoMat *ᵥ ggGraphLat .twistedE6 x := by
  rw [wordProd_smul_eq_wordMat_mulVec (τ := langTag .twistedE6)
    (l := (twE6TwoWord : List (Fin (langTag .twistedE6).rank)))]
  rw [show wordMat (langTag .twistedE6)
      (twE6TwoWord : List (Fin (langTag .twistedE6).rank)) =
      toMat (langTag .twistedE6).rank
        (lmul (langTag .twistedE6).rank twE6TwoMat twE6PermList) from twE6Two_wordMat]
  rw [toMat_lmul, ← Matrix.mulVec_mulVec]
  congr 1
  exact (permLattice_E6_eq x).symm

private theorem lk0xttb_ggGraph_invol (u : Fin (langTag .twistedE6).rank → ℤ) :
    ggGraphLat .twistedE6 (ggGraphLat .twistedE6 u) = u := by
  ext j
  fin_cases j <;> rfl

private theorem lk0xttb_hv_tw (x : Fin TwistTag.E6.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
      toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]

private theorem lk0xttb_hΦ (x : ℤ) :
    ((cyclotomic 1 ℤ).eval (-x)).natAbs = ((cyclotomic 2 ℤ).eval x).natAbs := by
  rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
    show -x - 1 = -(x + 1) by ring, Int.natAbs_neg]

private theorem lk0xttb_ggWeylLaw {p f : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpf : p ∣ 2 ^ f + 1)
    (ht : GGExcFive .twistedE6) :
    GGWeylLaw .twistedE6 p f ht ((coxeterSystem (langTag .twistedE6)).wordProd
      (twE6TwoWord : List (Fin (langTag .twistedE6).rank))) := by
  intro u
  have hndvd : ¬ p ∣ 2 ^ f - 1 := by
    intro h
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hsub : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hpf h
    have h2 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [h2] at hsub
    have := Nat.le_of_dvd (by norm_num) hsub
    omega
  have hε : eps p f = -1 := by
    unfold eps
    rw [if_neg hndvd]
  rw [hε, piB_twistedE6_of_dvd f hpf,
    lk0xttb_permLattice_permCongr_one (rank_eq_langTag f ht) u, neg_one_smul]
  rw [lk0xttb_hv (ggGraphLat .twistedE6 u)]
  rw [lk0xttb_ggGraph_invol u]
  have hM : toMat (langTag .twistedE6).rank twE6TwoMat = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem twE6_tt_unitary :
    ∀ (f : ℕ), 1 ≤ f → ∀ (p : ℕ), p.Prime → 7 ≤ p → p ∣ 2 ^ f + 1 →
      ∀ E : Subgroup (ModGL (langTag .twistedE6) GGL), E ≤ ggFixGp .twistedE6 f →
        IsPGroup p ↥E → TwE6LawPos p f E := by
  intro f hf p hp h7 hpf E hE hEp
  classical
  let K := GaloisField 2 (2 * f)
  letI : Algebra K GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), Nat.mul_comm 2 f, ← pow_mul]
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 f
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => by
    show (iterateFrobeniusEquiv K 2 f) c = c ^ 2 ^ f
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  let v : WeylGroup TwistTag.E6.tag := (coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord
  let M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    toMat TwistTag.E6.tag.rank twE6TwoMat
  have hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x := lk0xttb_hv_tw
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := 2) (f := f) hf GGL v
  let D : LangDatum TwistTag.E6.tag GGL :=
    LangDatum.ofTwist TwistTag.E6 (ggFrobT f) (2 ^ f) (ggFrobT_apply f) v hg0C hg0
  have hD : D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f) := rfl
  have hfix : D.fix = ggFixGp .twistedE6 f := ggFixGp_eq_fix (t := .twistedE6) D rfl
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag GGL :=
    (baseChangeGL (algebraMap K GGL)).comp (twistedE6RootGroup K σ).subtype
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd := langDescent_twE6 (K := K) (L := GGL) Nat.prime_two hf hK σ hσ (ggFrobT_apply f) D hD
    hp (by omega)
  have hT0 := twistedTorus_E6_eq_map (L := GGL) (ggFrobT f) v M hv
  set B : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    M - ((2 ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval ((2 ^ f : ℕ) : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hp3 : 3 < p := by omega
  have hpq : ¬ p ∣ 2 ^ f := by
    intro h
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hsub : p ∣ (2 ^ f + 1) - 2 ^ f := Nat.dvd_sub hpf h
    have h2 : (2 ^ f + 1) - 2 ^ f = 1 := by omega
    rw [h2] at hsub
    exact hp.not_dvd_one hsub
  have he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 2 := by
    have h0 : (((2 ^ f + 1 : ℕ)) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ f + 1)).2 hpf
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at h0
    have hq : ((2 : ZMod p) ^ f) = -1 := eq_neg_of_add_eq_zero_left h0
    have hqf : (((2 ^ f : ℕ)) : ZMod p) = -1 := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact hq
    have h2 : (((2 ^ f : ℕ)) : ZMod p) ^ 2 = 1 := by rw [hqf]; ring
    have hdvd : orderOf (((2 ^ f : ℕ)) : ZMod p) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact h2
    have hne1 : orderOf (((2 ^ f : ℕ)) : ZMod p) ≠ 1 := by
      intro h
      have : (((2 ^ f : ℕ)) : ZMod p) = 1 := orderOf_eq_one_iff.1 h
      rw [hqf] at this
      exact neg_one_ne_one_zmod hp (by omega) this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne1
    · exact h
  have he' : orderOf (((-(2 ^ f : ℕ) : ℤ) : ℤ) : ZMod p) = 1 := by
    have h := orderOf_neg_natCast_zmod hp (by omega) hpq he
    rwa [show ennola 2 = 1 by decide] at h
  have hq2 : 2 ≤ 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num : (1 : ℕ) < 2)
  set Q : ℤ := -((2 ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (p : ℤ) ∣ Q := fun h =>
    hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have hchar : M.charpoly = ([2, 2, 2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod :=
    twE6Two_charpoly
  have hso : ∀ d ∈ ([2, 2, 2, 2, 2, 2] : List ℕ), d ≠ 2 → d ∈ [1, 2, 3, 4, 6] := by decide
  have hcount : ((degreesE Tag.E6).filter fun d => (1 : ℕ) ∣ d).length =
      ([2, 2, 2, 2, 2, 2] : List ℕ).count 2 := by decide
  have hdeg : ∀ d ∈ degreesE Tag.E6, (1 : ℕ) ∣ d → ¬ p ∣ d / 1 :=
    not_dvd_div_of_720 hp h7 (by decide)
  have hDd : ∀ d ∈ degreesE Tag.E6, (1 : ℕ) ∣ d → d ≠ 0 ∧ ¬ p ∣ d / 1 := fun d hd hed =>
    ⟨by
      have hpos : ∀ d ∈ degreesE Tag.E6, 0 < d := by decide
      exact (hpos d hd).ne'
    , hdeg d hd hed⟩
  have hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      (p ^ ((2 ^ f) ^ 2 - 1).factorization p) ^
        (([2, 2, 2, 2, 2, 2] : List ℕ).count 2) := by
    rw [ordProj_card_twistedE6 Nat.prime_two hf K hK σ hσ hp hp3 hpq,
      prod_ordProj_int_pow_sub_one hp (by omega) hQ2 hpQ he' (degreesE Tag.E6) hDd, hcount,
      ← ordProj_cyclotomic_int_eval hp hQ2 he' (by norm_num : (1 : ℕ) ≠ 0)]
    have h1 := ordProj_cyclotomic_eval hp hq2 he (by norm_num : (2 : ℕ) ≠ 0)
    have h2 : ((cyclotomic 1 ℤ).eval Q).natAbs =
        ((cyclotomic 2 ℤ).eval ((2 ^ f : ℕ) : ℤ)).natAbs := by
      have := lk0xttb_hΦ ((2 ^ f : ℕ) : ℤ)
      simpa [hQdef] using this
    rw [h2, h1]
  have hchar' : M.charpoly = cyclotomic 2 ℤ ^ ([2, 2, 2, 2, 2, 2] : List ℕ).count 2 *
      ((([2, 2, 2, 2, 2, 2] : List ℕ).filter fun d => d ≠ 2).map
        (fun d => cyclotomic d ℤ)).prod := by
    rw [hchar, prod_cyclotomic_split 2 [2, 2, 2, 2, 2, 2]]
  have hR := not_dvd_cyclotomic_eval_of_mem_small hp (by omega) he [2, 2, 2, 2, 2, 2] hso
  have hposq : 0 < (cyclotomic 2 ℤ).eval ((2 ^ f : ℕ) : ℤ) :=
    cyclotomic_pos' 2 (by exact_mod_cast hq2)
  have hRne : (((([2, 2, 2, 2, 2, 2] : List ℕ).filter fun d => d ≠ 2).map
      (fun d => cyclotomic d ℤ)).prod).eval ((2 ^ f : ℕ) : ℤ) ≠ 0 := fun h =>
    hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval ((2 ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hchar', eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hposq.ne') hRne
  have hBne : B.det ≠ 0 := fun h =>
    hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub Nat.prime_two (dvd_pow_self 2 (by omega) : 2 ∣ 2 ^ f) M
    (by norm_num : (2 : ℕ) ≠ 0) twE6Two_pow
  have hcard : Nat.card D.torus = (M.charpoly.eval ((2 ^ f : ℕ) : ℤ)).natAbs := by
    show Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) GGL v)
      (twistHom TwistTag.E6 GGL (ggFrobT f))) = _
    rw [hT0, Subgroup.card_map_of_injective CFSG.LieType.Chevalley.rootDiagUnit_injective,
      natCard_fixedCharTuples M (ggFrobT f) (ggFrobT_apply f) hBne hcop, hdetB]
  have hordN : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ ((M.charpoly.eval ((2 ^ f : ℕ) : ℤ)).natAbs).factorization p := by
    rw [hord, hchar', ordProj_cyclotomic_pow_mul_eval hp hq2 he (by norm_num : (2 : ℕ) ≠ 0) hR]
  have hord_le : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
      (Nat.card D.torus).factorization p := by
    rw [hcard]
    exact (Nat.pow_right_injective hp.two_le hordN).le
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfm := hd.finite_model
  haveI hΓfin : Finite D.Γ :=
    Finite.of_injective (Subgroup.inclusion hd.Γ_le_model) (Subgroup.inclusion_injective _)
  have hSylow := lk0xttb_sylow_in_torus (D := D) (ι := ι) hp hι hd hord_le
  obtain ⟨S₀, hS₀⟩ := hSylow
  have hEfix : E ≤ D.fix := hfix.symm ▸ hE
  let E'' : Subgroup (ModGL TwistTag.E6.tag GGL) := E
  let E' : Subgroup (ModGL TwistTag.E6.tag GGL) := E''.map (MulAut.conj g0⁻¹).toMonoidHom
  have hE'model : E' ≤ D.model := by
    rw [LangDescent.model_eq D]
    exact Subgroup.map_mono hEfix
  have hE'p : IsPGroup p E' := hEp.map _
  have hE'Γ : E' ≤ D.Γ := hd.pgroup_le_Γ E' hE'model hE'p
  have hQp : IsPGroup p (E'.subgroupOf D.Γ) := hE'p.comap_subtype
  obtain ⟨m, -, hm⟩ := CFSG.CGT.PushingUpLit.BHSSym.exists_conj_le_of_isPGroup
    (G := D.Γ) (p := p) (T := (S₀ : Subgroup D.Γ)) S₀.isPGroup' S₀.not_dvd_index le_top hQp
    le_top
  have hconj_torus : E'.map (MulAut.conj (m : ModGL TwistTag.E6.tag GGL)).toMonoidHom ≤ D.torus := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hx' : (⟨x, hE'Γ hx⟩ : D.Γ) ∈ E'.subgroupOf D.Γ := Subgroup.mem_subgroupOf.2 hx
    have hmem := hm ⟨x, hE'Γ hx⟩ hx'
    have hmem' : ((m * ⟨x, hE'Γ hx⟩ * m⁻¹ : D.Γ) : ModGL TwistTag.E6.tag GGL) ∈ D.torus :=
      Subgroup.mem_subgroupOf.1 (hS₀ hmem)
    simpa [MulAut.conj_apply] using hmem'
  let g : ModGL TwistTag.E6.tag GGL := g0 * (m : ModGL TwistTag.E6.tag GGL)⁻¹
  have hgadj : g ∈ adjointGroup TwistTag.E6.tag GGL := by
    have hmmem : (m : ModGL TwistTag.E6.tag GGL) ∈ adjointGroup TwistTag.E6.tag GGL :=
      (inf_le_left : D.model ≤ adjointGroup TwistTag.E6.tag GGL) (hd.Γ_le_model m.2)
    exact Subgroup.mul_mem _ hg0C (Subgroup.inv_mem _ hmmem)
  have hglang : D.Φ g = g * D.n := by
    have hmΓ : (m : ModGL TwistTag.E6.tag GGL) ∈ D.model := hd.Γ_le_model m.2
    have hmmodel : D.n * D.Φ (m : ModGL TwistTag.E6.tag GGL) * D.n⁻¹ =
        (m : ModGL TwistTag.E6.tag GGL) := ((LangDatum.mem_model (D := D)).1 hmΓ).2
    have hmΦ : D.Φ (m : ModGL TwistTag.E6.tag GGL) =
        D.n⁻¹ * (m : ModGL TwistTag.E6.tag GGL) * D.n := by
      calc D.Φ (m : ModGL TwistTag.E6.tag GGL)
          = D.n⁻¹ * (D.n * D.Φ (m : ModGL TwistTag.E6.tag GGL) * D.n⁻¹) * D.n := by group
        _ = D.n⁻¹ * (m : ModGL TwistTag.E6.tag GGL) * D.n := by rw [hmmodel]
    have hmΦinv : D.Φ ((m : ModGL TwistTag.E6.tag GGL)⁻¹) =
        D.n⁻¹ * (m : ModGL TwistTag.E6.tag GGL)⁻¹ * D.n := by
      rw [map_inv, hmΦ]; group
    have hg0' : D.Φ g0 = g0 * D.n := hg0
    show D.Φ (g0 * (m : ModGL TwistTag.E6.tag GGL)⁻¹) =
      g0 * (m : ModGL TwistTag.E6.tag GGL)⁻¹ * D.n
    rw [map_mul, hg0', hmΦinv]
    group
  have hmap_eq : E''.map (MulAut.conj g⁻¹).toMonoidHom =
      E'.map (MulAut.conj (m : ModGL TwistTag.E6.tag GGL)).toMonoidHom := by
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom =
        (MulAut.conj (m : ModGL TwistTag.E6.tag GGL)).toMonoidHom.comp
          (MulAut.conj g0⁻¹).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g⁻¹ = (m : ModGL TwistTag.E6.tag GGL) * g0⁻¹ by simp [g]]
      group
    rw [hcomp, Subgroup.map_map]
  have htor : D.torus = twistedTorusOf D.n D.Φ := rfl
  have hgtor : E''.map (MulAut.conj g⁻¹).toMonoidHom ≤ D.torus := by
    rw [htor, hmap_eq]
    exact hconj_torus
  have ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨ht, v, (g : ModGL (langTag .twistedE6) GGL), ?_,
    lk0xttb_ggWeylLaw hp h7 hpf ht⟩
  exact ⟨hgadj, hglang, hgtor⟩

end CFSG.StandardType.LieKnownR2.ExcPos
