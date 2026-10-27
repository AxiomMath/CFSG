module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeBasics
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTorus.TwoSummands
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTorus.BorelMoves
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTorus.SylowProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTorus.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveApply

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem torus_setup_Tor7 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {K : Subgroup G}
    (hLK : c.L = ⨆ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom) {t : G} (htT : t ∈ D.T)
    (htwo : ∀ X ∈ conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N),
      X = barSub ⊥ A hA K ∨ X = barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) :
    (c.L ≤ stabTil ⊥ A) ∧ (K ≤ stabTil ⊥ A) ∧
    (K.map (MulAut.conj t).toMonoidHom ≤ stabTil ⊥ A) ∧
    (t ∈ c.N) ∧ (t ∈ stabTil ⊥ A) ∧
    (barSub ⊥ A hA c.L = barSub ⊥ A hA K ⊔
      barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) ∧
    fixV (barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) = ⊥ ∧
    IsSylowIn 2 (D.T ⊓ c.L) c.L ∧
    IsSylowIn 2 (barSub ⊥ A hA (D.T ⊓ c.L))
      (barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) := by
  classical
  have hNst : c.N ≤ stabTil ⊥ A :=
    le_inf hAN (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have htN : t ∈ c.N := Ctx23L.T_le_N c htT
  have htst : t ∈ stabTil ⊥ A := hNst htN
  have hLst : c.L ≤ stabTil ⊥ A :=
    le_inf ((Ctx23L.L_le_N c).trans hAN) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hK1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by ext x; simp
  have hKL : K ≤ c.L := by
    rw [hLK]
    exact le_iSup_of_le ⟨(1 : G), D.T.one_mem⟩ (le_of_eq hK1.symm)
  have hKst : K ≤ stabTil ⊥ A := hKL.trans hLst
  have hKtst : K.map (MulAut.conj t).toMonoidHom ≤ stabTil ⊥ A := by
    have hKtL : K.map (MulAut.conj t).toMonoidHom ≤ c.L := by
      rw [hLK]
      exact le_iSup_of_le ⟨t, htT⟩ le_rfl
    exact hKtL.trans hLst
  have hSL : IsSylowIn 2 (D.T ⊓ c.L) c.L := Ctx23L.isSylowIn_inf_of_le_normalizer c.hL.1.1
  have hLA : barSub ⊥ A hA c.L =
      barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom) :=
    TwoConj.barSub_L_eq_sup c hA hAN hLK htT htwo
  have hfixL : fixV (barSub ⊥ A hA K ⊔
      barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) = ⊥ := by
    rw [← hLA]
    exact fixV_barSub_eq_bot c hA hAV hAN
  have hSA' : IsSylowIn 2 (barSub ⊥ A hA (D.T ⊓ c.L))
      (barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) := by
    rw [← hLA]
    exact isSylowIn_barSub hA inf_le_right hLst hSL
  exact ⟨hLst, hKst, hKtst, htN, htst, hLA, hfixL, hSL, hSA'⟩

private theorem exists_torus_pair_Tor7 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {K : Subgroup G}
    {t : G} (htT : t ∈ D.T)
    (hcomp : CFSG.Open.IsComponentOf (barSub ⊥ A hA K) (barSub ⊥ A hA c.N))
    (hne : barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom) ≠ barSub ⊥ A hA K)
    (hsum : IsDirSumOver (conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N)) (fun X => commV X))
    (htwo : ∀ X ∈ conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N),
      X = barSub ⊥ A hA K ∨ X = barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom))
    {g : MulAut (Vtil ⊥ A hA)} (hg : g ∈ barSub ⊥ A hA c.N)
    (hgT : g ∈ barSub ⊥ A hA D.T)
    (hX' : (barSub ⊥ A hA K).map (MulAut.conj g).toMonoidHom =
      barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) :
    ∃ (z : G) (hzA : z ∈ A) (hzZ : z ∈ D.Z) (v v' : Vtil ⊥ A hA),
      v ∈ commV (barSub ⊥ A hA K) ∧
      v' ∈ commV (barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) ∧
      v * v' = mkTil ⊥ A hA (IntMod.mk hA ⟨z, hzA⟩) ∧ v ≠ 1 ∧
      v ∈ fixV (barSub ⊥ A hA (D.T ⊓ c.L) ⊓ barSub ⊥ A hA K) := by
  classical
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Ctx23L.inf_Z_ne_bot c hAV hAne ((Ctx23L.T_le_N c).trans hAN))
  have hzA : (z : G) ∈ A := z.2.1
  have hzZ : (z : G) ∈ D.Z := z.2.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  let zt : Vtil ⊥ A hA := mkTil ⊥ A hA (IntMod.mk hA ⟨(z : G), hzA⟩)
  have hzt_ne : zt ≠ 1 := fun h => hz1' ((TwoConj.mkTil_mk_eq_one_iff hA hzA).1 h)
  have hzt_fix : zt ∈ fixV (barSub ⊥ A hA D.T) := by
    rw [fixV_T_barSub_eq c hA hAV hAN]
    exact (mem_imgTil ⊥ A hA (A ⊓ D.Z) zt).2
      ⟨IntMod.mk hA ⟨(z : G), hzA⟩, ⟨hzA, hzZ⟩, rfl⟩
  have hgz : g zt = zt := (mem_fixV.mp hzt_fix) g hgT
  obtain ⟨v, hv, v', hv', hvsum, hv1⟩ :=
    TwoConj.exists_mul_eq_ne_one hg hX' hne hsum htwo hzt_ne hgz
  have hvS0 : v ∈ fixV (barSub ⊥ A hA (D.T ⊓ c.L) ⊓ barSub ⊥ A hA K) := by
    rw [mem_fixV]
    intro s hs
    have hsDT : s ∈ barSub ⊥ A hA D.T := barSub_mono ⊥ A hA inf_le_left hs.1
    have hxv : s (v * v') = v * v' := by rw [hvsum]; exact (mem_fixV.mp hzt_fix) s hsDT
    exact TwoConj.apply_eq_of_apply_mul_eq hcomp hg hX' hne hsum hs.2 hv' hxv
  exact ⟨z, hzA, hzZ, v, v', hv, hv', hvsum, hv1, hvS0⟩

private theorem exists_torus_borel_Tor7 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h209 : S20_9 D) (hBS : KBorelSolv20_7)
    (h1930 : H1930 D) (hBI : KNatBorelIrr) (hTa : KTab23a)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {K : Subgroup G} {t : G}
    {n : ℕ} (hn : 2 < n)
    (hnat : (IsL2 ↥(barSub ⊥ A hA K) n ∧
        BinaryNaturalSL (barSub ⊥ A hA K) (commV (barSub ⊥ A hA K)) ⊥ 2 n) ∨
      (Even n ∧ IsOmegaMinus ↥(barSub ⊥ A hA K) 4 (n / 2) ∧
        NatOmegaMinus (barSub ⊥ A hA K) (commV (barSub ⊥ A hA K)) ⊥ 4 (n / 2)))
    {v : Vtil ⊥ A hA} (hv : v ∈ commV (barSub ⊥ A hA K))
    (hvS : v ∈ fixV (barSub ⊥ A hA (D.T ⊓ c.L) ⊓ barSub ⊥ A hA K)) (hv1 : v ≠ 1)
    (hLst : c.L ≤ stabTil ⊥ A)
    (hSL : IsSylowIn 2 (D.T ⊓ c.L) c.L)
    (hLA : barSub ⊥ A hA c.L =
      barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom))
    (hSA' : IsSylowIn 2 (barSub ⊥ A hA (D.T ⊓ c.L))
      (barSub ⊥ A hA K ⊔ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)))
    (hcommXX' : ∀ x ∈ barSub ⊥ A hA K,
      ∀ y ∈ barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom), x * y = y * x)
    (hperf : ⁅barSub ⊥ A hA K, barSub ⊥ A hA K⁆ = barSub ⊥ A hA K)
    (hS0 : IsSylowIn 2 (barSub ⊥ A hA (D.T ⊓ c.L) ⊓ barSub ⊥ A hA K)
      (barSub ⊥ A hA K))
    (hfixX : commV (barSub ⊥ A hA K) ⊓ fixV (barSub ⊥ A hA K) = ⊥) :
    ∃ (bA : MulAut (Vtil ⊥ A hA)), (bA ∈ barSub ⊥ A hA K ∧ bA v ≠ v) ∧
      ∃ b : ↥(stabTil ⊥ A), (b : G) ∈ D.M ∧ actTil ⊥ A hA b = bA := by
  classical
  haveI : Finite (MulAut (Vtil ⊥ A hA)) := Finite.of_injective
    (fun (g : MulAut (Vtil ⊥ A hA)) (w : Vtil ⊥ A hA) => g w)
    (fun a b h => MulEquiv.ext (congrFun h))
  have hv2 : v ^ 2 = 1 := TwoConj.sq_eq_one_Vtil hA v
  obtain ⟨bA, hbA, hbAv⟩ :=
    TwoConj.exists_mem_inf_normalizer_apply_ne_of_commV hBI hTa hperf hS0 hfixX hn hnat
      hv hvS hv1 hv2
  have hbAX : bA ∈ barSub ⊥ A hA K := hbA.1
  have hbAnormSA : bA ∈ normalizer
      (barSub ⊥ A hA (D.T ⊓ c.L) : Set (MulAut (Vtil ⊥ A hA))) :=
    TwoConj.inf_normalizer_le_normalizer hcommXX' hSA' hbA
  have hbAL : bA ∈ barSub ⊥ A hA c.L := by rw [hLA]; exact Subgroup.mem_sup_left hbAX
  have hbAinf : bA ∈ barSub ⊥ A hA (c.L ⊓ normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) :=
    TwoConj.barSub_inf_normalizer_le hA hLst hSL ⟨hbAL, hbAnormSA⟩
  obtain ⟨b, hb, hbact⟩ :=
    (mem_barSub ⊥ A hA (c.L ⊓ normalizer ((D.T ⊓ c.L : Subgroup G) : Set G)) bA).1 hbAinf
  have hbM : (b : G) ∈ D.M := Ctx23L.borel_le_M c h207 h209 hBS h1930 hb
  exact ⟨bA, ⟨hbAX, hbAv⟩, b, hbM, hbact⟩

private theorem false_of_torus_data_Tor7 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {A : Subgroup G} (hA : IsElemAbelian 2 A) {K : Subgroup G}
    (hLK : c.L = ⨆ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom) {t : G} (htT : t ∈ D.T)
    (hcomp : CFSG.Open.IsComponentOf (barSub ⊥ A hA K) (barSub ⊥ A hA c.N))
    (hne : barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom) ≠ barSub ⊥ A hA K)
    (hsum : IsDirSumOver (conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N)) (fun X => commV X))
    {g : MulAut (Vtil ⊥ A hA)} (hg : g ∈ barSub ⊥ A hA c.N)
    (hX' : (barSub ⊥ A hA K).map (MulAut.conj g).toMonoidHom =
      barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom))
    (hKtst : K.map (MulAut.conj t).toMonoidHom ≤ stabTil ⊥ A)
    {z : G} (hzA : z ∈ A) (hzZ : z ∈ D.Z) {v v' : Vtil ⊥ A hA}
    (hv' : v' ∈ commV (barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)))
    (hvsum : v * v' = mkTil ⊥ A hA (IntMod.mk hA ⟨z, hzA⟩))
    {bA : MulAut (Vtil ⊥ A hA)} (hbAX : bA ∈ barSub ⊥ A hA K) (hbAv : bA v ≠ v)
    {b : ↥(stabTil ⊥ A)} (hbM : (b : G) ∈ D.M) (hbact : actTil ⊥ A hA b = bA) : False := by
  classical
  obtain ⟨huA, hcomm⟩ := TwoConj.mkTil_commutator_eq hA b.2 hzA
  have hb' : (⟨(b : G), b.2⟩ : ↥(stabTil ⊥ A)) = b := Subtype.ext rfl
  have hkeq : mkTil ⊥ A hA (IntMod.mk hA ⟨(b : G) * z * (b : G)⁻¹ * z⁻¹, huA⟩) =
      bA v * v⁻¹ := by
    rw [hcomm, hb', hbact, ← hvsum]
    exact (TwoConj.apply_mul_inv_eq hcomp hg hX' hne hsum hbAX v hv').1
  have huU : (b : G) * z * (b : G)⁻¹ * z⁻¹ ∈ D.U := TwoConj.commutator_mem_U D hbM hzZ
  have hu1 : (b : G) * z * (b : G)⁻¹ * z⁻¹ ≠ 1 := by
    intro h1
    have h1' : mkTil ⊥ A hA
        (IntMod.mk hA ⟨(b : G) * z * (b : G)⁻¹ * z⁻¹, huA⟩) = 1 :=
      (TwoConj.mkTil_mk_eq_one_iff hA huA).2 h1
    rw [hkeq] at h1'
    exact hbAv (mul_inv_eq_one.mp h1')
  have hũfix : mkTil ⊥ A hA (IntMod.mk hA ⟨(b : G) * z * (b : G)⁻¹ * z⁻¹, huA⟩) ∈
      fixV (barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom)) := by
    have hmem : mkTil ⊥ A hA (IntMod.mk hA ⟨(b : G) * z * (b : G)⁻¹ * z⁻¹, huA⟩) ∈
        commV (barSub ⊥ A hA K) := by
      rw [hkeq]
      exact (TwoConj.apply_mul_inv_eq hcomp hg hX' hne hsum hbAX v hv').2
    exact (TwoConj.commV_le_fixV hcomp hg hX' hne hsum).2 hmem
  have hKu : K.map (MulAut.conj t).toMonoidHom ≤ centralizer
      ({(b : G) * z * (b : G)⁻¹ * z⁻¹} : Set G) :=
    TwoConj.le_centralizer_of_mkTil_mem_fixV hA hKtst huA hũfix
  exact TwoConj.false_of_map_conj_le_centralizer c hLK htT huU hu1 hKu

theorem false_of_case_one_of_two_conjugates {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h209 : S20_9 D) (hBS : KBorelSolv20_7)
    (h1930 : H1930 D) (hBI : KNatBorelIrr) (hTa : KTab23a)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V) (hAne : A ≠ ⊥)
    (hAN : c.N ≤ Subgroup.normalizer (A : Set G)) {K : Subgroup G}
    (hLK : c.L = ⨆ s : D.T, K.map (MulAut.conj (s : G)).toMonoidHom) {t : G} (htT : t ∈ D.T)
    (hcomp : CFSG.Open.IsComponentOf (barSub ⊥ A hA K) (barSub ⊥ A hA c.N))
    (hne : barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom) ≠ barSub ⊥ A hA K)
    (hsum : IsDirSumOver (conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N)) (fun X => commV X))
    (htwo : ∀ X ∈ conjSet (barSub ⊥ A hA K) (barSub ⊥ A hA c.N),
      X = barSub ⊥ A hA K ∨ X = barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom))
    {n : ℕ} (hn : 2 < n)
    (hnat : (IsL2 ↥(barSub ⊥ A hA K) n ∧
        BinaryNaturalSL (barSub ⊥ A hA K) (commV (barSub ⊥ A hA K)) ⊥ 2 n) ∨
      (Even n ∧ IsOmegaMinus ↥(barSub ⊥ A hA K) 4 (n / 2) ∧
        NatOmegaMinus (barSub ⊥ A hA K) (commV (barSub ⊥ A hA K)) ⊥ 4 (n / 2))) :
    False := by
  classical
  obtain ⟨hLst, hKst, hKtst, htN, htst, hLA, hfixL, hSL, hSA'⟩ :=
    torus_setup_Tor7 c hA hAV hAN hLK htT htwo
  let g : MulAut (Vtil ⊥ A hA) := actTil ⊥ A hA ⟨t, htst⟩
  have hg : g ∈ barSub ⊥ A hA c.N := actTil_mem_barSub ⊥ A hA htN htst
  have hgT : g ∈ barSub ⊥ A hA D.T := actTil_mem_barSub ⊥ A hA htT htst
  have hX' : (barSub ⊥ A hA K).map (MulAut.conj g).toMonoidHom =
      barSub ⊥ A hA (K.map (MulAut.conj t).toMonoidHom) :=
    (TwelveTwentyThree.barSub_map_conj hA hKst htst).symm
  have hcommXX' := TwoConj.mul_comm_of_map_conj hcomp hg hX' hne
  haveI : Finite (MulAut (Vtil ⊥ A hA)) := Finite.of_injective
    (fun (g : MulAut (Vtil ⊥ A hA)) (w : Vtil ⊥ A hA) => g w)
    (fun a b h => MulEquiv.ext (congrFun h))
  have hS0 : IsSylowIn 2 (barSub ⊥ A hA (D.T ⊓ c.L) ⊓ barSub ⊥ A hA K)
      (barSub ⊥ A hA K) := TwoConj.isSylowIn_inf_left hcommXX' hSA'
  have hperf : ⁅barSub ⊥ A hA K, barSub ⊥ A hA K⁆ = barSub ⊥ A hA K :=
    CFSG.Quasithin.B15P4.perfect_of_isComponentOf hcomp
  have hfixX : commV (barSub ⊥ A hA K) ⊓ fixV (barSub ⊥ A hA K) = ⊥ :=
    TwoConj.commV_inf_fixV_eq_bot hcomp hg hX' hne hsum hfixL
  obtain ⟨z, hzA, hzZ, v, v', hv, hv', hvsum, hv1, hvS0⟩ :=
    exists_torus_pair_Tor7 c hA hAV hAne hAN htT hcomp hne hsum htwo hg hgT hX'
  obtain ⟨bA, ⟨hbAX, hbAv⟩, b, hbM, hbact⟩ :=
    exists_torus_borel_Tor7 c h207 h209 hBS h1930 hBI hTa hA hn hnat hv hvS0 hv1
      hLst hSL hLA hSA' hcommXX' hperf hS0 hfixX
  exact false_of_torus_data_Tor7 c hA hLK htT hcomp hne hsum hg hX' hKtst hzA hzZ hv' hvsum
    hbAX hbAv hbM hbact

end CFSG.LocalAnalysis.UniquenessCase.UC22
