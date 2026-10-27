module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoTorus
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveFrameKer
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveConjSix
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
import CFSG.GH74.Statements
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
import CFSG.RankThree.PartOne.BRANCH.RankRee
import CFSG.RankThree.PartOne.CTP.SeitzFineU5
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.N143.Weyl613Defs
import CFSG.RankThree.PartOne.N143X.KF64WSimple
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
open Multiplicative
open scoped MatrixGroups

private lemma frameSplitAux_isElemAbelian_top (p d : ℕ) [Fact p.Prime] :
    CFSG.Open.IsElemAbelian p (⊤ : Subgroup (Multiplicative (Fin d → ZMod p))) := by
  refine ⟨inferInstance, fun x _ => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  show (p : ℕ) • Multiplicative.toAdd x = 0
  ext i
  show (p : ℕ) • (Multiplicative.toAdd x i) = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private def frameSplitAux_kerSubmodule {p n : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (g : Multiplicative (Fin n → ZMod p) →* G) :
    Submodule (ZMod p) (Fin n → ZMod p) where
  carrier := {v | g (Multiplicative.ofAdd v) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change g (Multiplicative.ofAdd (v + w)) = 1
    rw [ofAdd_add, map_mul, hv, hw, one_mul]
  smul_mem' := by
    intro c v hv
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    change g (Multiplicative.ofAdd (c • v)) = 1
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow,
      hv, one_pow]

private def frameSplitAux_kerEquiv {p n : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (g : Multiplicative (Fin n → ZMod p) →* G) :
    ↥(frameSplitAux_kerSubmodule g) ≃ ↥g.ker where
  toFun x := ⟨Multiplicative.ofAdd (x : Fin n → ZMod p), x.2⟩
  invFun x := ⟨Multiplicative.toAdd (x : Multiplicative (Fin n → ZMod p)), by
    change g (x : Multiplicative _) = 1
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply Multiplicative.ofAdd _
  right_inv x := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply Multiplicative.ofAdd _

private lemma frameSplitAux_card_kerSubmodule {p n : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] (g : Multiplicative (Fin n → ZMod p) →* G) :
    Nat.card ↥(frameSplitAux_kerSubmodule g) = Nat.card ↥g.ker :=
  Nat.card_congr (frameSplitAux_kerEquiv g)

private lemma frameSplitAux_isElemAbelian_range {p n : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] (g : Multiplicative (Fin n → ZMod p) →* G) :
    CFSG.Open.IsElemAbelian p g.range := by
  have h := CFSG.Open.IsElemAbelian.map (frameSplitAux_isElemAbelian_top p n) g
  rwa [Subgroup.map_top] at h

private lemma frameSplitAux_finrank_ker_ge {p n : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] [Finite G] (g : Multiplicative (Fin n → ZMod p) →* G) {r : ℕ}
    (hdim : Module.finrank (ZMod p) (Fin n → ZMod p) = 6)
    (hr : Nat.card g.range ≤ p ^ r) :
    6 - r ≤ Module.finrank (ZMod p) (frameSplitAux_kerSubmodule g) := by
  let K := frameSplitAux_kerSubmodule g
  let d := Module.finrank (ZMod p) K
  have hp : p.Prime := Fact.out
  have hV : Nat.card (Multiplicative (Fin n → ZMod p)) = p ^ 6 := by
    rw [Nat.card_congr Multiplicative.toAdd,
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := Fin n → ZMod p),
      Nat.card_zmod, hdim]
  have hkr := Subgroup.card_ker_mul_card_range g
  have hKcard : Nat.card K = Nat.card ↥g.ker := frameSplitAux_card_kerSubmodule g
  have hd : Nat.card K = p ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := K), Nat.card_zmod]
  have h6 : 6 ≤ d + r := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    calc p ^ 6 = Nat.card (Multiplicative (Fin n → ZMod p)) := hV.symm
      _ = Nat.card ↥g.ker * Nat.card ↥g.range := hkr.symm
      _ = Nat.card K * Nat.card ↥g.range := by rw [hKcard]
      _ = p ^ d * Nat.card ↥g.range := by rw [hd]
      _ ≤ p ^ d * p ^ r := Nat.mul_le_mul_left _ hr
      _ = p ^ (d + r) := (pow_add p d r).symm
  have hgoal : 6 - r ≤ d := by omega
  simpa [d, K] using hgoal

private lemma frameSplitAux_finrank_inf_ge {p n : ℕ} [Fact p.Prime]
    (hdim : Module.finrank (ZMod p) (Fin n → ZMod p) = 6)
    (A B : Submodule (ZMod p) (Fin n → ZMod p)) :
    Module.finrank (ZMod p) A + Module.finrank (ZMod p) B - 6 ≤
      Module.finrank (ZMod p) ↥(A ⊓ B) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hle := Submodule.finrank_le (A ⊔ B)
  rw [hdim] at hle
  omega

private lemma frameSplitAux_finrank_add_le {p n : ℕ} [Fact p.Prime]
    (hdim : Module.finrank (ZMod p) (Fin n → ZMod p) = 6)
    {A B : Submodule (ZMod p) (Fin n → ZMod p)} (hinf : A ⊓ B = ⊥) :
    Module.finrank (ZMod p) A + Module.finrank (ZMod p) B ≤ 6 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hbot : Module.finrank (ZMod p) ↥(A ⊓ B) = 0 := by rw [hinf]; simp
  have hle := Submodule.finrank_le (A ⊔ B)
  rw [hdim] at hle
  omega


private lemma frameSplitAux_frameMap_mem_three {K : Type} [Field K]
    (σ : K →+* K) (y : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K)))
    (h3 : y 3 = 1) :
    TwFive.frameMap σ y ∈ (frameHom σ 0).range ⊔ (frameHom σ 1).range ⊔
      (frameHom σ 2).range := by
  have hy : y = Pi.mulSingle 0 (y 0) * Pi.mulSingle 1 (y 1) *
      Pi.mulSingle 2 (y 2) := by
    funext i
    fin_cases i <;> simp [h3]
  rw [hy]
  simp only [map_mul, TwFive.frameMap_mulSingle]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨y 0, rfl⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨y 1, rfl⟩)))
    (Subgroup.mem_sup_right ⟨y 2, rfl⟩)

private lemma frameSplitAux_frameMap_mem_iSup {K : Type} [Field K]
    (σ : K →+* K) (y : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K))) :
    TwFive.frameMap σ y ∈ ⨆ i, (frameHom σ i).range := by
  have hy : y = Pi.mulSingle 0 (y 0) * Pi.mulSingle 1 (y 1) *
      Pi.mulSingle 2 (y 2) * Pi.mulSingle 3 (y 3) := by
    funext i
    fin_cases i <;> simp
  rw [hy]
  simp only [map_mul, TwFive.frameMap_mulSingle]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_iSup_of_mem 0 ⟨y 0, rfl⟩)
    (Subgroup.mem_iSup_of_mem 1 ⟨y 1, rfl⟩))
    (Subgroup.mem_iSup_of_mem 2 ⟨y 2, rfl⟩))
    (Subgroup.mem_iSup_of_mem 3 ⟨y 3, rfl⟩)

private lemma frameSplitAux_frameMap_eq_three {K : Type} [Field K]
    (σ : K →+* K) (y : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K)))
    (h0 : y 0 = 1) (h1 : y 1 = 1) (h2 : y 2 = 1) :
    TwFive.frameMap σ y = frameHom σ 3 (y 3) := by
  have hy : y = Pi.mulSingle 3 (y 3) := by
    funext i
    fin_cases i <;> simp [h0, h1, h2]
  rw [hy, TwFive.frameMap_mulSingle]
  simp

private lemma frameSplitAux_card_range_prod_cyclic {p n : ℕ} [Fact p.Prime]
    {A B : Type} [Group A] [Group B] [Finite A] [Finite B] [IsCyclic A] [IsCyclic B]
    (g : Multiplicative (Fin n → ZMod p) →* A × B) :
    Nat.card g.range ≤ p ^ 2 := by
  let fst : A × B →* A := MonoidHom.fst A B
  let snd : A × B →* B := MonoidHom.snd A B
  let f : ↥g.range → ↥(g.range.map fst) × ↥(g.range.map snd) := fun x =>
    (⟨(x : A × B).1, ⟨x.1, x.2, rfl⟩⟩, ⟨(x : A × B).2, ⟨x.1, x.2, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z => (z.1 : A)) hxy) (congrArg (fun z => (z.2 : B)) hxy)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hle
  have h1 : Nat.card ↥(g.range.map fst) ≤ p :=
    CFSG.StandardType.card_le_of_isElemAbelian_of_cyclic (G := A) (p := p)
      (E := g.range.map fst) (Fact.out : p.Prime)
      (CFSG.Open.IsElemAbelian.map (frameSplitAux_isElemAbelian_range g) fst)
      (Subgroup.isCyclic (g.range.map fst))
  have h2 : Nat.card ↥(g.range.map snd) ≤ p :=
    CFSG.StandardType.card_le_of_isElemAbelian_of_cyclic (G := B) (p := p)
      (E := g.range.map snd) (Fact.out : p.Prime)
      (CFSG.Open.IsElemAbelian.map (frameSplitAux_isElemAbelian_range g) snd)
      (Subgroup.isCyclic (g.range.map snd))
  calc Nat.card ↥g.range ≤ Nat.card ↥(g.range.map fst) * Nat.card ↥(g.range.map snd) := hle
    _ ≤ p * p := Nat.mul_le_mul h1 h2
    _ = p ^ 2 := by ring

theorem exists_frame_split_twE6
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    {T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥(twistedE6RootGroup K σ)}
    (hTinj : Function.Injective T) :
    ∃ c : ↥(twistedE6RootGroup K σ),
      (∃ VG W : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p), IsCompl VG W ∧
        Module.finrank (ZMod p) VG = 5 ∧
        (∀ t ∈ VG, c * T (ofAdd t) * c⁻¹ ∈ (frameHom σ.toRingHom 0).range ⊔
          (frameHom σ.toRingHom 1).range ⊔ (frameHom σ.toRingHom 2).range ⊔
          (torusG σ.toRingHom).range) ∧
        (∀ t ∈ W, c * T (ofAdd t) * c⁻¹ ∈ (frameHom σ.toRingHom 3).range)) ∧
      (∃ VG W : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p), IsCompl VG W ∧
        Module.finrank (ZMod p) VG = 4 ∧
        (∀ t ∈ VG, c * T (ofAdd t) * c⁻¹ ∈ ⨆ i, (frameHom σ.toRingHom i).range) ∧
        (∀ t ∈ W, c * T (ofAdd t) * c⁻¹ ∈ (torusG σ.toRingHom).range)) := by
  classical
  let σ' : K →+* K := σ.toRingHom
  have hσ' : ∀ c, σ' c = c ^ 2 ^ n := hσ
  let k : Type := RingHom.eqLocusField σ' (RingHom.id K)
  haveI hkFinite : Finite k := inferInstance
  have hn1 : 1 ≤ n := by omega
  have hkcard : Nat.card k = 2 ^ n := by
    dsimp [k]
    exact CFSG.RankThree.Chevalley.card_eqLocusField_of_pow Nat.prime_two hn1 hK hσ'
  have hp : p.Prime := Fact.out
  have hpk : ¬ p ∣ Nat.card k := by
    rw [hkcard]
    intro hd
    have h1 : p ∣ 2 ^ n + 1 - 2 ^ n := Nat.dvd_sub hpq hd
    rw [show 2 ^ n + 1 - 2 ^ n = 1 by omega] at h1
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have hpk0 : (p : k) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpk
  have hdim : Module.finrank (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p) = 6 := by
    rw [Module.finrank_fin_fun]
    rfl
  have hTe : CFSG.Open.IsElemAbelian p (MonoidHom.range T) :=
    frameSplitAux_isElemAbelian_range T
  have hTexp : ∀ x ∈ T.range, x ^ p = 1 := fun x hx => hTe.2 x hx
  obtain ⟨c, hc⟩ : ∃ c : ↥(twistedE6RootGroup K σ),
      (T.range).map (MulAut.conj c).toMonoidHom ≤ frameTorusGroup σ' := by
    have hsplit : p = 5 ∨ 7 ≤ p := by
      have hpne6 : p ≠ 6 := by
        rintro rfl
        norm_num at hp
      omega
    rcases hsplit with hp_eq | hp7
    · subst hp_eq
      obtain ⟨_, -, -, hVle, hVconj⟩ :=
        TwFive.exists_elemAbelian_conj_le_six (ℓ := 2) (f := n) Nat.prime_two K hK σ hσ hpq
      obtain ⟨g, hg⟩ := hVconj T.range hTe
      exact ⟨g, hg.trans hVle⟩
    · exact exists_conj_le_frame_torusG (ℓ := 2) (f := n) Nat.prime_two hn1 K hK σ hσ
        hp7 hpq T.range hTexp
  let H := (Fin 4 → SL(2, k)) × (↥(normOne σ') × ↥(normOne σ'))
  haveI hHfin : Finite H := inferInstance
  let ψ : H →* ↥(twistedE6RootGroup K σ) := TwFive.frameTorusMap σ'
  let T' : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(twistedE6RootGroup K σ) := (MulAut.conj c).toMonoidHom.comp T
  let S : Subgroup ↥(twistedE6RootGroup K σ) := T'.range
  have hT'inj : Function.Injective T' := (MulAut.conj c).injective.comp hTinj
  have hS_le : S ≤ frameTorusGroup σ' := by
    dsimp [S, T']
    rw [MonoidHom.range_comp]
    exact hc
  have hS_elem : CFSG.Open.IsElemAbelian p S := by
    change CFSG.Open.IsElemAbelian p (MonoidHom.range T')
    exact frameSplitAux_isElemAbelian_range T'
  have hS_card : Nat.card S = p ^ 6 := by
    change Nat.card (MonoidHom.range T') = p ^ 6
    rw [← Nat.card_congr (MonoidHom.ofInjective hT'inj).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hrange : ψ.range = frameTorusGroup σ' := by
    rw [frameTorusGroup]
    dsimp [ψ]
    rw [TwFive.frameTorusMap, MonoidHom.noncommCoprod_range, TwFive.frameMap,
      MonoidHom.noncommPiCoprod_range]
  have hS_le' : S ≤ ψ.range := by
    rw [hrange]
    exact hS_le
  have hker : ¬ p ∣ Nat.card ψ.ker := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxp : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hxp' : (x : H) ^ p = 1 := by simpa using congrArg Subtype.val hxp
    have hx1 : x = 1 := Subtype.ext
      (TwFive.frameTorusMap_eq_one_of_pow σ' hp hp5 (x : H) (m := 1)
        (by simpa using hxp') (MonoidHom.mem_ker.mp x.2))
    rw [hx1] at hx
    have hp1 : p = 1 := by simpa using hx.symm
    exact hp.ne_one hp1
  obtain ⟨E', hE'e, hE'map, hE'card⟩ :=
    TwFive.exists_lift_of_le_range ψ hker hS_le' hS_elem
  have hE'card6 : Nat.card ↥E' = p ^ 6 := hE'card.trans hS_card
  let ψE : ↥E' →* ↥S :=
    (ψ.comp E'.subtype).codRestrict S (fun x => by
      rw [← hE'map]
      exact ⟨x, x.2, rfl⟩)
  have hψE_inj : Function.Injective ψE := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxpsi : ψ (x : H) = 1 := by
      have h := congrArg Subtype.val hx
      simpa [ψE] using h
    have hxker : (x : H) ∈ ψ.ker := MonoidHom.mem_ker.mpr hxpsi
    have hxp : (x : H) ^ p = 1 := hE'e.2 (x : H) x.2
    have hxcard : (x : H) ^ Nat.card ψ.ker = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := ψ.ker) (x := ⟨(x : H), hxker⟩))
    have hcop : Nat.Coprime p (Nat.card ψ.ker) :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 hker
    exact Subtype.ext (TwFive.frameTorus_eq_one_of_pow_coprime (x : H) hxp hxcard hcop)
  have hψE_surj : Function.Surjective ψE := by
    intro s
    have hs : (s : ↥(twistedE6RootGroup K σ)) ∈ E'.map ψ := by
      rw [hE'map]
      exact s.2
    obtain ⟨x, hxE, hxeq⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨x, hxE⟩, Subtype.ext (by simpa [ψE] using hxeq)⟩
  let e : ↥E' ≃* ↥S := MulEquiv.ofBijective ψE ⟨hψE_inj, hψE_surj⟩
  let T'S : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥S :=
    T'.codRestrict S (fun t => ⟨t, rfl⟩)
  let χ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* H :=
    E'.subtype.comp (e.symm.toMonoidHom.comp T'S)
  have hχψ : ∀ t, ψ (χ t) = c * T t * c⁻¹ := by
    intro t
    have h1 : (ψE (e.symm (T'S t)) : ↥(twistedE6RootGroup K σ)) = T' t := by
      have h2 : ψE (e.symm (T'S t)) = T'S t := e.apply_symm_apply (T'S t)
      rw [h2]
      rfl
    simpa [χ, ψE, T', MulAut.conj_apply] using h1
  have hχinj : Function.Injective χ := by
    intro a b hab
    have h := congrArg ψ hab
    rw [hχψ a, hχψ b] at h
    exact hT'inj (by simpa [T', MulAut.conj_apply] using h)
  let g0 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* SL(2, k) :=
    (Pi.evalMonoidHom (fun _ : Fin 4 => SL(2, k)) 0).comp
      ((MonoidHom.fst (Fin 4 → SL(2, k))
        (↥(normOne σ') × ↥(normOne σ'))).comp χ)
  let g1 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* SL(2, k) :=
    (Pi.evalMonoidHom (fun _ : Fin 4 => SL(2, k)) 1).comp
      ((MonoidHom.fst (Fin 4 → SL(2, k))
        (↥(normOne σ') × ↥(normOne σ'))).comp χ)
  let g2 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* SL(2, k) :=
    (Pi.evalMonoidHom (fun _ : Fin 4 => SL(2, k)) 2).comp
      ((MonoidHom.fst (Fin 4 → SL(2, k))
        (↥(normOne σ') × ↥(normOne σ'))).comp χ)
  let g3 : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* SL(2, k) :=
    (Pi.evalMonoidHom (fun _ : Fin 4 => SL(2, k)) 3).comp
      ((MonoidHom.fst (Fin 4 → SL(2, k))
        (↥(normOne σ') × ↥(normOne σ'))).comp χ)
  let gT : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      (↥(normOne σ') × ↥(normOne σ')) :=
    (MonoidHom.snd (Fin 4 → SL(2, k))
      (↥(normOne σ') × ↥(normOne σ'))).comp χ
  let K0 := frameSplitAux_kerSubmodule g0
  let K1 := frameSplitAux_kerSubmodule g1
  let K2 := frameSplitAux_kerSubmodule g2
  let K3 := frameSplitAux_kerSubmodule g3
  let KT := frameSplitAux_kerSubmodule gT
  have h0r : Nat.card (MonoidHom.range g0) ≤ p :=
    card_le_of_isElemAbelian_specialLinear_two (K := k) hpk0
      (frameSplitAux_isElemAbelian_range g0)
  have h1r : Nat.card (MonoidHom.range g1) ≤ p :=
    card_le_of_isElemAbelian_specialLinear_two (K := k) hpk0
      (frameSplitAux_isElemAbelian_range g1)
  have h2r : Nat.card (MonoidHom.range g2) ≤ p :=
    card_le_of_isElemAbelian_specialLinear_two (K := k) hpk0
      (frameSplitAux_isElemAbelian_range g2)
  have h3r : Nat.card (MonoidHom.range g3) ≤ p :=
    card_le_of_isElemAbelian_specialLinear_two (K := k) hpk0
      (frameSplitAux_isElemAbelian_range g3)
  have hTr : Nat.card (MonoidHom.range gT) ≤ p ^ 2 := by
    haveI : IsCyclic Kˣ := inferInstance
    haveI : IsCyclic ↥(normOne σ') := Subgroup.isCyclic (normOne σ')
    exact frameSplitAux_card_range_prod_cyclic gT
  have hd0 : 5 ≤ Module.finrank (ZMod p) K0 := by
    have h := frameSplitAux_finrank_ker_ge g0 (r := 1) hdim (by rw [pow_one]; exact h0r)
    simpa [K0] using h
  have hd1 : 5 ≤ Module.finrank (ZMod p) K1 := by
    have h := frameSplitAux_finrank_ker_ge g1 (r := 1) hdim (by rw [pow_one]; exact h1r)
    simpa [K1] using h
  have hd2 : 5 ≤ Module.finrank (ZMod p) K2 := by
    have h := frameSplitAux_finrank_ker_ge g2 (r := 1) hdim (by rw [pow_one]; exact h2r)
    simpa [K2] using h
  have hd3 : 5 ≤ Module.finrank (ZMod p) K3 := by
    have h := frameSplitAux_finrank_ker_ge g3 (r := 1) hdim (by rw [pow_one]; exact h3r)
    simpa [K3] using h
  have hdT : 4 ≤ Module.finrank (ZMod p) KT := by
    have h := frameSplitAux_finrank_ker_ge gT (r := 2) hdim hTr
    simpa [KT] using h
  have hd01 : 4 ≤ Module.finrank (ZMod p) ↥(K0 ⊓ K1) := by
    have h := frameSplitAux_finrank_inf_ge hdim K0 K1
    omega
  have hd012 : 3 ≤ Module.finrank (ZMod p) ↥((K0 ⊓ K1) ⊓ K2) := by
    have h := frameSplitAux_finrank_inf_ge hdim (K0 ⊓ K1) K2
    omega
  have hfive : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      g0 (ofAdd t) = 1 → g1 (ofAdd t) = 1 → g2 (ofAdd t) = 1 →
      g3 (ofAdd t) = 1 → gT (ofAdd t) = 1 → t = 0 := by
    intro t h0 h1 h2 h3 hT
    have hχ1 : χ (ofAdd t) = 1 := by
      apply Prod.ext
      · funext i
        fin_cases i
        · simpa [g0] using h0
        · simpa [g1] using h1
        · simpa [g2] using h2
        · simpa [g3] using h3
      · apply Prod.ext
        · simpa [gT] using congrArg Prod.fst hT
        · simpa [gT] using congrArg Prod.snd hT
    have hof : ofAdd t = 1 := hχinj (by simpa using hχ1)
    exact ofAdd_eq_one.mp hof
  let W1 : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p) :=
    ((K0 ⊓ K1) ⊓ K2) ⊓ KT
  let W2 : Submodule (ZMod p) (Fin TwistTag.E6.tag.rank → ZMod p) :=
    ((K0 ⊓ K1) ⊓ K2) ⊓ K3
  have hdW1 : 1 ≤ Module.finrank (ZMod p) W1 := by
    have h := frameSplitAux_finrank_inf_ge hdim ((K0 ⊓ K1) ⊓ K2) KT
    have hle : 3 + 4 - 6 ≤ Module.finrank (ZMod p) ↥((K0 ⊓ K1) ⊓ K2) +
        Module.finrank (ZMod p) ↥KT - 6 :=
      Nat.sub_le_sub_right (Nat.add_le_add hd012 hdT) 6
    have h76 : 3 + 4 - 6 = 1 := by norm_num
    rw [h76] at hle
    exact hle.trans h
  have hdW2 : 2 ≤ Module.finrank (ZMod p) W2 := by
    have h := frameSplitAux_finrank_inf_ge hdim ((K0 ⊓ K1) ⊓ K2) K3
    have hle : 3 + 5 - 6 ≤ Module.finrank (ZMod p) ↥((K0 ⊓ K1) ⊓ K2) +
        Module.finrank (ZMod p) ↥K3 - 6 :=
      Nat.sub_le_sub_right (Nat.add_le_add hd012 hd3) 6
    have h76 : 3 + 5 - 6 = 2 := by norm_num
    rw [h76] at hle
    exact hle.trans h
  have hinf1 : K3 ⊓ W1 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro t ht
    dsimp [W1] at ht
    have h0 : g0 (ofAdd t) = 1 := ht.2.1.1.1
    have h1 : g1 (ofAdd t) = 1 := ht.2.1.1.2
    have h2 : g2 (ofAdd t) = 1 := ht.2.1.2
    have h3 : g3 (ofAdd t) = 1 := ht.1
    have hT : gT (ofAdd t) = 1 := ht.2.2
    exact hfive t h0 h1 h2 h3 hT
  have hinf2 : KT ⊓ W2 = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro t ht
    dsimp [W2] at ht
    have h0 : g0 (ofAdd t) = 1 := ht.2.1.1.1
    have h1 : g1 (ofAdd t) = 1 := ht.2.1.1.2
    have h2 : g2 (ofAdd t) = 1 := ht.2.1.2
    have h3 : g3 (ofAdd t) = 1 := ht.2.2
    have hT : gT (ofAdd t) = 1 := ht.1
    exact hfive t h0 h1 h2 h3 hT
  have hsum1 : Module.finrank (ZMod p) K3 + Module.finrank (ZMod p) W1 ≤ 6 :=
    frameSplitAux_finrank_add_le hdim hinf1
  have hsum2 : Module.finrank (ZMod p) KT + Module.finrank (ZMod p) W2 ≤ 6 :=
    frameSplitAux_finrank_add_le hdim hinf2
  have hd3eq : Module.finrank (ZMod p) K3 = 5 := by omega
  have hdW1eq : Module.finrank (ZMod p) W1 = 1 := by omega
  have hdTeq : Module.finrank (ZMod p) KT = 4 := by omega
  have hdW2eq : Module.finrank (ZMod p) W2 = 2 := by omega
  have hcompl1 : IsCompl K3 W1 := by
    refine IsCompl.of_eq hinf1 ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq K3 W1
    have hbot : Module.finrank (ZMod p) ↥(K3 ⊓ W1) = 0 := by rw [hinf1]; simp
    have hsup : Module.finrank (ZMod p) ↥(K3 ⊔ W1) = 6 := by
      rw [hbot, add_zero] at h
      rw [h, hd3eq, hdW1eq]
    apply Submodule.eq_top_of_finrank_eq
    rw [hsup, Module.finrank_fin_fun]
    rfl
  have hcompl2 : IsCompl KT W2 := by
    refine IsCompl.of_eq hinf2 ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq KT W2
    have hbot : Module.finrank (ZMod p) ↥(KT ⊓ W2) = 0 := by rw [hinf2]; simp
    have hsup : Module.finrank (ZMod p) ↥(KT ⊔ W2) = 6 := by
      rw [hbot, add_zero] at h
      rw [h, hdTeq, hdW2eq]
    apply Submodule.eq_top_of_finrank_eq
    rw [hsup, Module.finrank_fin_fun]
    rfl
  refine ⟨c, ?_, ?_⟩
  · refine ⟨K3, W1, hcompl1, hd3eq, ?_, ?_⟩
    · intro t ht
      let y := (χ (ofAdd t)).1
      let s := (χ (ofAdd t)).2
      have hpair : χ (ofAdd t) = (y, s) := Prod.ext rfl rfl
      have h3 : y 3 = 1 := by
        have hg : g3 (ofAdd t) = 1 := ht
        simpa [g3, hpair] using hg
      have hψeq : c * T (ofAdd t) * c⁻¹ =
          TwFive.frameMap σ' y * torusG σ' s := by
        rw [← hχψ (ofAdd t), hpair, TwFive.frameTorusMap_apply]
      rw [hψeq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
        (frameSplitAux_frameMap_mem_three σ' y h3)) (Subgroup.mem_sup_right ⟨s, rfl⟩)
    · intro t ht
      dsimp [W1] at ht
      let y := (χ (ofAdd t)).1
      let s := (χ (ofAdd t)).2
      have hpair : χ (ofAdd t) = (y, s) := Prod.ext rfl rfl
      have h0 : g0 (ofAdd t) = 1 := ht.1.1.1
      have h1 : g1 (ofAdd t) = 1 := ht.1.1.2
      have h2 : g2 (ofAdd t) = 1 := ht.1.2
      have hT : gT (ofAdd t) = 1 := ht.2
      have hy0 : y 0 = 1 := by simpa [g0, hpair] using h0
      have hy1 : y 1 = 1 := by simpa [g1, hpair] using h1
      have hy2 : y 2 = 1 := by simpa [g2, hpair] using h2
      have hs : s = 1 := by simpa [gT, hpair] using hT
      have hψeq : c * T (ofAdd t) * c⁻¹ =
          TwFive.frameMap σ' y * torusG σ' s := by
        rw [← hχψ (ofAdd t), hpair, TwFive.frameTorusMap_apply]
      rw [hψeq, frameSplitAux_frameMap_eq_three σ' y hy0 hy1 hy2, hs, map_one, mul_one]
      exact ⟨y 3, rfl⟩
  · refine ⟨KT, W2, hcompl2, hdTeq, ?_, ?_⟩
    · intro t ht
      let y := (χ (ofAdd t)).1
      let s := (χ (ofAdd t)).2
      have hpair : χ (ofAdd t) = (y, s) := Prod.ext rfl rfl
      have hT : gT (ofAdd t) = 1 := ht
      have hs : s = 1 := by simpa [gT, hpair] using hT
      have hψeq : c * T (ofAdd t) * c⁻¹ =
          TwFive.frameMap σ' y * torusG σ' s := by
        rw [← hχψ (ofAdd t), hpair, TwFive.frameTorusMap_apply]
      rw [hψeq, hs, map_one, mul_one]
      exact frameSplitAux_frameMap_mem_iSup σ' y
    · intro t ht
      dsimp [W2] at ht
      let y := (χ (ofAdd t)).1
      let s := (χ (ofAdd t)).2
      have hpair : χ (ofAdd t) = (y, s) := Prod.ext rfl rfl
      have h0 : g0 (ofAdd t) = 1 := ht.1.1.1
      have h1 : g1 (ofAdd t) = 1 := ht.1.1.2
      have h2 : g2 (ofAdd t) = 1 := ht.1.2
      have h3 : g3 (ofAdd t) = 1 := ht.2
      have hy0 : y 0 = 1 := by simpa [g0, hpair] using h0
      have hy1 : y 1 = 1 := by simpa [g1, hpair] using h1
      have hy2 : y 2 = 1 := by simpa [g2, hpair] using h2
      have hy3 : y 3 = 1 := by simpa [g3, hpair] using h3
      have hy : y = 1 := by
        funext i
        fin_cases i <;> simp [hy0, hy1, hy2, hy3]
      have hψeq : c * T (ofAdd t) * c⁻¹ =
          TwFive.frameMap σ' y * torusG σ' s := by
        rw [← hχψ (ofAdd t), hpair, TwFive.frameTorusMap_apply]
      rw [hψeq, hy, map_one, one_mul]
      exact ⟨s, rfl⟩

end CFSG.StandardType.PhiTwoRootGen
