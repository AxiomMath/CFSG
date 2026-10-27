module

public import CFSG.Sporadic.Co1I301.Elements
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.Sporadic.Co1Patterson.GraphFixDim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1I301.Native
  CFSG.Sporadic.Co1.Module CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8
  CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped Matrix

private theorem two_le_fixCount_of_act {R : CFSG.Sporadic.Co1Schreier.Native.Rows} {v : ℕ}
    (hv0 : v ≠ 0) (hv : v < 2 ^ 24) (hR : CFSG.Sporadic.Co1Schreier.Native.act R v = v) :
    2 ≤ CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount (rowsMatrix 24 R) := by
  have hne : toVecD 24 v ≠ 0 := fun h =>
    hv0 (toVecD_injective hv (Nat.two_pow_pos 24) (h.trans (toVecD_zero 24).symm))
  have hfix : rowsMatrix 24 R *ᵥ toVecD 24 v = toVecD 24 v := by
    rw [rowsMatrix_mulVec_toVecD, hR]
  unfold CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount
  haveI : Nontrivial {w : Fin 24 → ZMod 2 // rowsMatrix 24 R *ᵥ w = w} :=
    ⟨⟨⟨0, Matrix.mulVec_zero _⟩, ⟨toVecD 24 v, hfix⟩, fun h => hne (congrArg Subtype.val h).symm⟩⟩
  exact Finite.one_lt_card

private theorem facts_of_equiv {G H : Type} [Group G] [Group H] {C : Subgroup G} {J : Subgroup H}
    (e : ↥C ≃* ↥J) (hq : CFSG.Open.IsQuasisimple ↥J) (hz : Nat.card ↥(Subgroup.center ↥J) = 3)
    (hS : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* TauCeti.SporadicName.Suz.Group)) :
    CFSG.Open.IsQuasisimple ↥C ∧ Nat.card ↥(Subgroup.center ↥C) = 3 ∧
      Nonempty ((↥C ⧸ Subgroup.center ↥C) ≃* TauCeti.SporadicName.Suz.Group) := by
  obtain ⟨eS⟩ := hS
  refine ⟨CFSG.HardMathSupport.Timmesfeld.Proving.isQuasisimple_of_mulEquiv' e.symm hq, ?_,
    ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans eS⟩⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact hz

private theorem layer_of_facts {G : Type} [Group G] [Finite G] {d : G}
    (hq : CFSG.Open.IsQuasisimple ↥(centralizer ({d} : Set G)))
    (hz : Nat.card ↥(Subgroup.center ↥(centralizer ({d} : Set G))) = 3) :
    GLAPPrimeCore 3 ↥(centralizer ({d} : Set G)) = ⊥ ∧
      GLAPLayer 3 (centralizer ({d} : Set G)) = centralizer ({d} : Set G) := by
  set C := centralizer ({d} : Set G)
  have hCn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hp3 : 3 ∣ Nat.card ↥C := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥C)
    rwa [hz] at h
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (C : Set G)) := by
    intro c
    refine ⟨1, ?_⟩
    have hc := Subgroup.mem_inf.1 c.2
    have hcZ : (⟨(c : G), hc.1⟩ : ↥C) ∈ Subgroup.center ↥C :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 g g.2)
    have h3 : (⟨⟨(c : G), hc.1⟩, hcZ⟩ : ↥(Subgroup.center ↥C)) ^ 3 = 1 := by
      rw [← hz]
      exact pow_card_eq_one'
    have h4 := congrArg (fun y : ↥(Subgroup.center ↥C) => ((y : ↥C) : G)) h3
    rw [pow_one]
    apply Subtype.ext
    simpa using h4
  have hcore :=
    CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three
      le_rfl hCn hq hp3 hcent
  exact ⟨hcore, glaPLayer_eq_of_unique_glaPComponent
    (CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal_quasisimple le_rfl hCn hq hcore)
    fun J hJ => CFSG.HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple
      Nat.prime_three le_rfl hCn hq hcore hcent hJ⟩

private theorem isTypeWithCenter_of_facts {G : Type} [Group G] [Finite G] {d : G}
    (hq : CFSG.Open.IsQuasisimple ↥(centralizer ({d} : Set G)))
    (hz : Nat.card ↥(Subgroup.center ↥(centralizer ({d} : Set G))) = 3)
    (hS : Nonempty ((↥(centralizer ({d} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({d} : Set G))) ≃* TauCeti.SporadicName.Suz.Group)) :
    IsTypeWithCenter 3 (centralizer ({d} : Set G)) (sporIs .Suz) 3 := by
  obtain ⟨eS⟩ := hS
  let e : PQuot 3 (centralizer ({d} : Set G)) ≃* ↥(centralizer ({d} : Set G)) :=
    (QuotientGroup.quotientMulEquivOfEq (layer_of_facts hq hz).1).trans QuotientGroup.quotientBot
  refine ⟨⟨.sporadic .Suz, rfl,
    ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans eS⟩⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hz]


private theorem root_fixes (j : ℕ) (hj : j < 3) :
    ∃ v : ℕ, v ≠ 0 ∧ v < 2 ^ 24 ∧ CFSG.Sporadic.Co1Schreier.Native.act
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows j) v = v := by
  have h := co1RowCheck_parts.2.2.1
  simp only [chkRoots, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  interval_cases j
  · exact ⟨25668, (h (0, 25668) (by simp [rootFix])).1, by norm_num,
      (h (0, 25668) (by simp [rootFix])).2⟩
  · exact ⟨452, (h (1, 452) (by simp [rootFix])).1, by norm_num,
      (h (1, 452) (by simp [rootFix])).2⟩
  · exact ⟨17819, (h (2, 17819) (by simp [rootFix])).1, by norm_num,
      (h (2, 17819) (by simp [rootFix])).2⟩

private theorem exists_conj_threeA :
    ∃ g x : ↥GA, co1MatEquiv dC = g * x * g⁻¹ ∧
      MRep (CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA.rootRows3A ()) (x : GL24) := by
  have hs : orderOf (co1MatEquiv dC) = 3 := (orderOf_co1MatEquiv dC).trans orderOf_dC
  obtain ⟨g, x, hgx, hx⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_census_three _ hs
  refine ⟨g, x, hgx, ?_⟩
  have hdm : rowsMatrix 24 (dRw ()) =
      (((co1MatEquiv dC : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
    nrep_dC.symm.trans (matHom_eq_nativeEmb dC)
  have hfix : CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount
      ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) ≤ 1 := by
    have h1 := CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount_conj (g : GL24) (x : GL24)
    rw [← h1]
    have h2 : ((g : GL24) * (x : GL24) * (g : GL24)⁻¹ : GL24) =
        ((co1MatEquiv dC : ↥GA) : GL24) := by
      rw [hgx]
      rfl
    rw [h2, ← hdm]
    exact fixCount_dC_le
  have hroot : ∀ j < 3, ¬ MRep
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows j) (x : GL24) := by
    intro j hj hrep
    obtain ⟨v, hv0, hv, hact⟩ := root_fixes j hj
    have h2 := two_le_fixCount_of_act hv0 hv hact
    have hrep' : rowsMatrix 24
        (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows j) =
        ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := hrep
    rw [hrep'] at h2
    omega
  rcases hx with h | h | h | h
  · exact absurd h (hroot 0 (by norm_num))
  · exact absurd h (hroot 1 (by norm_num))
  · exact absurd h (hroot 2 (by norm_num))
  · exact h

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA CFSG.HardMathSupport.Dickson.I271.TabCo1 in
private theorem card_cent_threeA_le {x : GL24} (hx : MRep (rootRows3A ()) x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set GL24) ⊓ GA) ≤ 1345036492800 := by
  have h := (Certificates.certificate17620 : threeACheck () = true)
  simp only [threeACheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, and_assoc, List.all_eq_true] at h
  obtain ⟨hD, hwx, hw1, hxr, hx1, hx3, hcm, hxu, hxw, hw01, hw10, hg01, hrels, hcomm, hb1,
    hcnt1⟩ := h
  haveI : Finite GL24 := inferInstance
  have rx := rep_nd (ext := ext) hD 95
  have hxe : x = kG ext 95 := hx.eq (by rw [← hxr]; exact rx)
  subst hxe
  exact (card_cent_le_of_powBoundN rx 3 hb1).trans hcnt1

private theorem nonempty_centD_equiv (g x : ↥GA) (hgx : co1MatEquiv dC = g * x * g⁻¹) :
    Nonempty (↥(centralizer ({dC} : Set NativeSporadic.Co1)) ≃*
      ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA)) := by
  let ψ : NativeSporadic.Co1 →* GL24 := (MulAut.conj ((g : GL24)⁻¹)).toMonoidHom.comp nativeEmb
  have hψ : ∀ c, ψ c = (g : GL24)⁻¹ * nativeEmb c * (g : GL24) := fun c => by
    simp [ψ]
  have hψinj : Function.Injective ψ := fun a b h =>
    nativeEmb_injective ((MulAut.conj ((g : GL24)⁻¹)).injective h)
  have hψd : ψ dC = (x : GL24) := by
    rw [hψ, nativeEmb_apply, hgx]
    simp [mul_assoc]
  have hψmem : ∀ c, ψ c ∈ GA := fun c => by
    rw [hψ]
    exact GA.mul_mem (GA.mul_mem (GA.inv_mem g.2) (nativeEmb_mem c)) g.2
  have hψsurj : ∀ y ∈ GA, ∃ c, ψ c = y := fun y hy => by
    obtain ⟨c, hc⟩ := exists_nativeEmb_eq (GA.mul_mem (GA.mul_mem g.2 hy) (GA.inv_mem g.2))
    exact ⟨c, by rw [hψ, hc]; group⟩
  have hmap : (centralizer ({dC} : Set NativeSporadic.Co1)).map ψ =
      Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, hψmem c⟩
      have h1 : c * dC = dC * c :=
        (@Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance dC c).1 hc
      have h2 : ψ c * ψ dC = ψ dC * ψ c := by rw [← map_mul, ← map_mul, h1]
      rw [hψd] at h2
      exact (@Subgroup.mem_centralizer_singleton_iff GL24 inferInstance (x : GL24) (ψ c)).2 h2
    · intro hy
      obtain ⟨hyC, hyA⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨c, rfl⟩ := hψsurj y hyA
      refine ⟨c, ?_, rfl⟩
      have h2 : ψ c * ψ dC = ψ dC * ψ c := by
        rw [hψd]
        exact (@Subgroup.mem_centralizer_singleton_iff GL24 inferInstance (x : GL24) (ψ c)).1 hyC
      have h1 : c * dC = dC * c := hψinj (by rw [map_mul, map_mul]; exact h2)
      exact (@Subgroup.mem_centralizer_singleton_iff NativeSporadic.Co1 inferInstance dC c).2 h1
  exact ⟨((centralizer ({dC} : Set NativeSporadic.Co1)).equivMapOfInjective ψ hψinj).trans
    (MulEquiv.subgroupCongr hmap)⟩

private theorem centD_facts :
    CFSG.Open.IsQuasisimple ↥(centralizer ({dC} : Set NativeSporadic.Co1)) ∧
      Nat.card ↥(Subgroup.center ↥(centralizer ({dC} : Set NativeSporadic.Co1))) = 3 ∧
      Nonempty ((↥(centralizer ({dC} : Set NativeSporadic.Co1)) ⧸
        Subgroup.center ↥(centralizer ({dC} : Set NativeSporadic.Co1))) ≃*
          TauCeti.SporadicName.Suz.Group) := by
  obtain ⟨g, x, hgx, hx⟩ := exists_conj_threeA
  obtain ⟨e⟩ := nonempty_centD_equiv g x hgx
  obtain ⟨J, hJC, -, hq, -, hcard3, -, hqcard, ⟨eJ⟩⟩ :=
    CFSG.HardMathSupport.Dickson.I271.TabCo1.threeA_data
      CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv hx
  have hJcard : Nat.card ↥J = 1345036492800 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J), hqcard, hcard3]
  have hJeq : J = Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA :=
    Subgroup.eq_of_le_of_card_ge hJC (by rw [hJcard]; exact card_cent_threeA_le hx)
  exact facts_of_equiv (e.trans (MulEquiv.subgroupCongr hJeq.symm)) hq hcard3 ⟨eJ⟩

theorem rowIOf_dC : rowIOf 3 dC = centralizer ({dC} : Set NativeSporadic.Co1) :=
  (layer_of_facts centD_facts.1 centD_facts.2.1).2

theorem isTypeWithCenter_centralizer_dC :
    IsTypeWithCenter 3 (centralizer ({dC} : Set NativeSporadic.Co1)) (sporIs .Suz) 3 :=
  isTypeWithCenter_of_facts centD_facts.1 centD_facts.2.1 centD_facts.2.2

end CFSG.Sporadic.Co1I301
