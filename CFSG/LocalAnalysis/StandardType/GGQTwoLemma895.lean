module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTrivial
public import CFSG.LocalAnalysis.StandardType.GGFFProp2
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProofSL
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open scoped IsMulCommutative MatrixGroups

theorem ggAutDispl_le_inf {G : Type} [Group G] {Bs J : Subgroup G}
    (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G)) :
    ggAutDispl Bs (ggAutomizer J Bs) ≤ Bs ⊓ J := by
  rw [ggAutDispl, Subgroup.closure_le]
  rintro y ⟨φ, hφ, b, rfl⟩
  rw [mem_ggAutomizer_iff] at hφ
  obtain ⟨n, hnJ, hnN, hnφ⟩ := hφ
  have hmemBs : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Bs := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hnφ]
    exact Bs.mul_mem (Bs.inv_mem b.2)
      ((Subgroup.mem_normalizer_iff.mp hnN (b : G)).mp b.2)
  have hmemJ : ((b⁻¹ * φ b : ↥Bs) : G) ∈ J := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hnφ]
    have hbJ : (b : G)⁻¹ * n * (b : G) ∈ J := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBsJ b.2)) n).mp hnJ
    rw [show (b : G)⁻¹ * (n * (b : G) * n⁻¹) = (b : G)⁻¹ * n * (b : G) * n⁻¹ by group]
    exact J.mul_mem hbJ (J.inv_mem hnJ)
  exact ⟨hmemBs, hmemJ⟩

theorem ne_bot_of_two_le_card_ggAutDispl {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} (h : 2 ≤ Nat.card (ggAutDispl Bs A)) : A ≠ ⊥ := by
  intro hbot
  have hdispl : ggAutDispl Bs A = ⊥ := by
    rw [ggAutDispl, eq_bot_iff, Subgroup.closure_le]
    rintro y ⟨φ, hφ, b, rfl⟩
    rw [hbot] at hφ
    have hφ1 : φ = 1 := by simpa using hφ
    rw [hφ1]
    simp
  rw [hdispl] at h
  simp at h

theorem dvd_card_of_two_le_card_ggAutDispl {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs J : Subgroup G} (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hBsJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (h : 2 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs))) : p ∣ Nat.card J := by
  have hEle : CFSG.Assembly.IsElemAbelian p (ggAutDispl Bs (ggAutomizer J Bs)) :=
    hBs.mono ((ggAutDispl_le_inf hBsJ).trans inf_le_left)
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hEle.isPGroup
  have hn1 : 1 ≤ n := by
    by_contra h0
    have h0' : n = 0 := by omega
    rw [h0', pow_zero] at hn
    omega
  have hdvd : p ∣ Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) := by
    rw [hn]
    exact dvd_pow_self p (by omega)
  exact hdvd.trans (Subgroup.card_dvd_of_le ((ggAutDispl_le_inf hBsJ).trans inf_le_right))

theorem ggQ2_inv_conj_x_mem_ggAutDispl {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) (h9 : 9 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs))) {g : G}
    (hle : (ggAutDispl Bs (ggAutomizer J Bs)).map (MulAut.conj g).toMonoidHom ≤ D) :
    g⁻¹ * x * g ∈ ggAutDispl Bs (ggAutomizer J Bs) := by
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hDcard : Nat.card D = 9 := by
    rw [hDJ.1.2.2.1, hp]
    norm_num
  have hcardmap : Nat.card ((ggAutDispl Bs (ggAutomizer J Bs)).map
      (MulAut.conj g).toMonoidHom) = Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : (ggAutDispl Bs (ggAutomizer J Bs)).map (MulAut.conj g).toMonoidHom = D := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardmap]
    omega
  have hxD : x ∈ D := hDJ.1.2.2.2.1
  have hxm : x ∈ (ggAutDispl Bs (ggAutomizer J Bs)).map (MulAut.conj g).toMonoidHom := by
    rw [heq]
    exact hxD
  obtain ⟨a, ha, hae⟩ := hxm
  have : g⁻¹ * x * g = a := by
    rw [← hae]
    change g⁻¹ * (g * a * g⁻¹) * g = a
    group
  rw [this]
  exact ha

theorem ggHasLabel_of_mulEquiv_SL6 {G : Type} [Group G] {L : Subgroup G}
    (e : SL(6, ZMod 2) ≃* ↥L) : GGHasLabel ⟨.A, 5, 1⟩ ↥L := by
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) = ⊥ :=
    FieldFiveSL.center_SL_eq_bot_of_card_two (K := ZMod 2) (m := 5)
      (by norm_num [Nat.card_zmod])
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin 6) (ZMod 2) ≃* ↥L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hmod : CFSG.Open.StatedClassicalModel ↥L .PSL 6 2 1 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by omega, by decide, by decide⟩,
      ZMod 2, inferInstance, inferInstance, by norm_num [Nat.card_zmod], ?_⟩
    exact ⟨e'.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 6 (ZMod 2))⟩
  exact ggHasLabel_typeA hmod

theorem ggHasLabel_of_mulEquiv_SL7 {G : Type} [Group G] {L : Subgroup G}
    (e : SL(7, ZMod 2) ≃* ↥L) : GGHasLabel ⟨.A, 6, 1⟩ ↥L := by
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 7) (ZMod 2)) = ⊥ :=
    FieldFiveSL.center_SL_eq_bot_of_card_two (K := ZMod 2) (m := 6)
      (by norm_num [Nat.card_zmod])
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin 7) (ZMod 2) ≃* ↥L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hmod : CFSG.Open.StatedClassicalModel ↥L .PSL 7 2 1 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by omega, by decide, by decide⟩,
      ZMod 2, inferInstance, inferInstance, by norm_num [Nat.card_zmod], ?_⟩
    exact ⟨e'.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 7 (ZMod 2))⟩
  exact ggHasLabel_typeA hmod

namespace GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF81 (autOrder)

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

theorem autOrder_of_prop2 (hFF : GGFFLinearProp2Input) {G : Type} [Group G] [Finite G] {b : G}
    {K : Subgroup G} {z : Fin 3 → K} (h : Setting b K z)
    (hlab : GGHasLabel ⟨.A, 5, 1⟩ K ∨ GGHasLabel ⟨.A, 6, 1⟩ K) (hchar : IsCharTwoType G) :
    autOrder (Bt b z) = 384 ∨ autOrder (Bt b z) = 1152 := by
  have hKN : (K.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal := by
    refine ⟨fun k hk c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact h.nor c c.2 k hk
  have hc := hFF G b K (tor (zs z)) h.ord h.le hKN hlab (tor_le z)
    (isElemAbelian_tor h.zs_pow h.zs_comm) (h.card_torG.trans (by norm_num)) h.cyc h.meet hchar
  have hBt : Subgroup.closure {b} ⊔ tor (zs z) = Bt b z := by
    rw [← Subgroup.zpowers_eq_closure]
    rfl
  rw [hBt, card_ggAutomizer_top] at hc
  exact hc

open CFSG.RankThree.PartTwo.Sec21.FF81 CFSG.RankThree.PartTwo.Sec21.FF81.P51T
  CFSG.RankThree.PartTwo.Sec21.FF81.P51

theorem cfgOf_eq_mA_or_mB_of_autOrder {G : Type} [Group G]
    [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}
    [CFSG.IsElementaryAbelian 3 (Bt b z)]
    {β : Module.Basis (Fin 4) (ZMod 3) (Additive ↥(Bt b z))}
    (hβ : ∀ i, ((Additive.toMul (β i) : ↥(Bt b z)) : G) =
      ![b, zs z 0, zs z 1, zs z 2] i)
    (h : Setting b K z) (hord : autOrder (Bt b z) = 384 ∨ autOrder (Bt b z) = 1152) :
    (cfgOf (ρU β).range).1 = mA ∨ (cfgOf (ρU β).range).1 = mB := by
  have hH0 := h.hasH0
  have hyp := P51T.hyp_of hH0 h.stab h.meetB β hβ
  set Γ := (ρU β).range with hΓdef
  have hcard := card_eq hyp
  have haut : autOrder (Bt b z) = Nat.card Γ := autOrder_eq β
  have hOm : ∀ m : Fin 7 → Bool, (cfgOf Γ).1 = m →
      Om Γ = ↑((nonzeroL.filter fun w => m (tab w).1).toFinset) := by
    intro m hm
    ext w
    rw [om_iff hyp, hm]
    simp
  have hautm : ∀ m : Fin 7 → Bool, (m = mA ∨ m = mB ∨ m = mC ∨ m = mD ∨ m = mE) →
      (cfgOf Γ).1 = m → autOrder (Bt b z) = 96 * lineCount m := by
    intro m hm hcm
    rw [haut, hcard, hOm m hcm, Set.ncard_coe_finset, vecCount m hm]
    ring
  rcases cfgOf_good hyp with hA | ⟨hB, -⟩ | ⟨hC, -⟩ | hD | hE
  · exact Or.inl hA
  · exact Or.inr hB
  · have := hautm mC (by simp) hC
    rw [lineCount_mC] at this
    omega
  · have := hautm mD (by simp) hD
    rw [lineCount_mD] at this
    omega
  · have := hautm mE (by simp) hE
    rw [lineCount_mE] at this
    omega

theorem cvG_conj_eq_vecElt {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G}
    {z : Fin 3 → K} [CFSG.IsElementaryAbelian 3 (Bt b z)]
    {β : Module.Basis (Fin 4) (ZMod 3) (Additive ↥(Bt b z))}
    (hβ : ∀ i, ((Additive.toMul (β i) : ↥(Bt b z)) : G) =
      ![b, zs z 0, zs z 1, zs z 2] i)
    {n : G} {v : Fin 3 → ZMod 3} (hnb : n * b * n⁻¹ = vecElt (zs z) v) :
    cvG β (n * b * n⁻¹) = ![0, v 0, v 1, v 2] := by
  have hz : ∀ i : Fin 3, zs z i ∈ Bt b z := zs_mem_Bt b z
  have hcv : ∀ i : Fin 4, cvG β (![b, zs z 0, zs z 1, zs z 2] i) = e i := fun i => by
    rw [← hβ i, cvG_of_mem β (Additive.toMul (β i)).2]
    exact cv_basis β i
  have hpow : ∀ (y : G) (hy : y ∈ Bt b z) (k : ℕ), cvG β (y ^ k) = k • cvG β y := by
    intro y hy k
    rw [cvG_of_mem β ((Bt b z).pow_mem hy k), cvG_of_mem β hy]
    have h1 : (⟨y ^ k, (Bt b z).pow_mem hy k⟩ : ↥(Bt b z)) =
        (⟨y, hy⟩ : ↥(Bt b z)) ^ k := rfl
    rw [h1]
    have := cv_zpow β ⟨y, hy⟩ (k : ℤ)
    rwa [zpow_natCast, natCast_zsmul] at this
  rw [hnb]
  simp only [vecElt]
  rw [cvG_mul β (Subgroup.mul_mem _ ((Bt b z).pow_mem (hz 0) _) ((Bt b z).pow_mem (hz 1) _))
      ((Bt b z).pow_mem (hz 2) _),
    cvG_mul β ((Bt b z).pow_mem (hz 0) _) ((Bt b z).pow_mem (hz 1) _),
    hpow _ (hz 0), hpow _ (hz 1), hpow _ (hz 2)]
  have h1 : cvG β (zs z 0) = e 1 := hcv 1
  have h2 : cvG β (zs z 1) = e 2 := hcv 2
  have h3 : cvG β (zs z 2) = e 3 := hcv 3
  rw [h1, h2, h3]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply]
  fin_cases j <;> simp [e, nsmul_eq_mul]

open CFSG.RankThree.PartTwo.Sec21.FF81 CFSG.RankThree.PartTwo.Sec21.FF81.P51T
  CFSG.RankThree.PartTwo.Sec21.FF81.P51 in
theorem wt_eq_one_of_conj {G : Type} [Group G] [Finite G]
    {b : G} {K : Subgroup G} {z : Fin 3 → K} (h : Setting b K z)
    (hord : autOrder (Bt b z) = 384 ∨ autOrder (Bt b z) = 1152)
    {g : G} {v : Fin 3 → ZMod 3} (hg : g * b * g⁻¹ = vecElt (zs z) v) : wt v = 1 := by
  obtain ⟨n, hn, hnb⟩ := h.fusion (tor_le_Bt b z (vecElt_mem_tor _ v)) hg
  have hH0 := h.hasH0
  have : CFSG.IsElementaryAbelian 3 (Bt b z) := hH0.1.1
  obtain ⟨β, hβ⟩ := exists_basis (B := Bt b z) hH0.1.2 hH0.2.1
  have hyp := P51T.hyp_of hH0 h.stab h.meetB β hβ
  set Γ := (ρU β).range with hΓdef
  have hcfg := cfgOf_eq_mA_or_mB_of_autOrder hβ h hord
  have hw := cvG_conj_eq_vecElt hβ hnb
  have hmem : ![0, v 0, v 1, v 2] ∈ Om Γ := by
    refine ⟨ρU β ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩, ?_⟩
    have hn0 : ((⟨n, hn⟩ : CFSG.RankThree.PartTwo.Sec21.FF79.Nor (Bt b z)) : G) *
        ((Additive.toMul (β 0) : Bt b z) : G) *
        ((⟨n, hn⟩ : CFSG.RankThree.PartTwo.Sec21.FF79.Nor (Bt b z)) : G)⁻¹ = n * b * n⁻¹ := by
      rw [hβ 0]
      rfl
    rw [coe_ρU, ρM_col, hn0, hw]
  obtain ⟨-, hk⟩ := (om_iff hyp _).1 hmem
  have key : ∀ v : Fin 3 → ZMod 3, (mA (orbOf ![0, v 0, v 1, v 2]) = true ∨
      mB (orbOf ![0, v 0, v 1, v 2]) = true) → wt v = 1 := by
    decide
  apply key
  change (cfgOf Γ).1 (orbOf ![0, v 0, v 1, v 2]) = true at hk
  rcases hcfg with h' | h' <;> rw [h'] at hk
  · exact Or.inl hk
  · exact Or.inr hk

end GGFF.Setting

theorem exists_nonisCyclic_pSubgroup_of_model {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {z : Fin 3 → ↥L} (hMz : GGFF.Model ↥L z) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  have hEA : CFSG.Assembly.IsElemAbelian 3 ((GGFF.tor z).map L.subtype) :=
    hMz.isElemAbelian_tor'.map _
  have hcard27 : Nat.card ((GGFF.tor z).map L.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hMz.card_tor']
  refine ⟨(GGFF.tor z).map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro y
    exact ⟨1, Subtype.ext (by simpa using hEA.2 y y.2)⟩
  · intro hcyc
    have hexp : Monoid.exponent ↥((GGFF.tor z).map L.subtype) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by simpa using hEA.2 y y.2)
    rw [IsCyclic.exponent_eq_card, hcard27] at hexp
    norm_num at hexp

theorem ggQ2_isConj_of_conj (hFF : GGFFLinearProp2Input)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    {H : Type} [Group H] {t : Fin 3 → H} (hM : GGFF.Model H t) (e : H ≃* ↥L)
    (hlab : GGHasLabel ⟨.A, 5, 1⟩ ↥L ∨ GGHasLabel ⟨.A, 6, 1⟩ ↥L)
    {g : G} {d : ↥L} (hg : g * x * g⁻¹ = (d : G)) : IsConj d (e (t 0)) := by
  subst hp
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hSs : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSs.2.2.2.1.1
  have hx3 : x ^ 3 = 1 := hSs.1.1.2 x hSs.2.1
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hg, conj_pow, hx3, mul_one, mul_inv_cancel, Subgroup.coe_one]
  have hM' : GGFF.Model ↥L (fun i => e (t i)) := hM.ofMulEquiv e
  obtain ⟨h, v, hhv⟩ := hM'.fus d hd3
  obtain ⟨z, hz⟩ : ∃ z : Fin 3 → ↥L, z = fun i => h * e (t i) * h⁻¹ := ⟨_, rfl⟩
  have hMz : GGFF.Model ↥L z := by rw [hz]; exact hM'.conj h
  have hdz : d = vecElt z v := by
    rw [hhv, hz]
    have := GGFF.vecElt_map (MulAut.conj h) (fun i => e (t i)) v
    simp only [MulAut.conj_apply] at this
    exact this.symm
  obtain ⟨S, hSL, hSp, hScyc⟩ := exists_nonisCyclic_pSubgroup_of_model hMz
  have hset : GGFF.Setting x L z :=
    ⟨⟨have : Fact (Nat.Prime 3) := ⟨by norm_num⟩; orderOf_eq_prime hx3 hSs.2.2.1,
      hLx, fun c hc k hk =>
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_of_sstar hSs ⟨S, hSL, hSp, hScyc⟩ hc) k).mp hk,
      hMz, hSs.2.2.2.2⟩, ⟨g, by rw [hg]; exact d.2⟩⟩
  have hord := GGFF.Setting.autOrder_of_prop2 hFF hset hlab hS.1.1.1.2.2.2.1
  have hwt : GGFF.wt v = 1 := GGFF.Setting.wt_eq_one_of_conj hset hord (g := g) (by
    rw [hg, hdz]
    exact (GGFF.vecElt_map L.subtype z v).symm)
  have hv0 : v ≠ 0 := fun h0 => by
    rw [h0] at hwt
    exact absurd hwt (by decide)
  have hc : IsConj (vecElt z v) (vecElt z (Pi.single 0 1)) :=
    (hMz.conj_iff v (Pi.single 0 1) hv0 (by decide)).mpr (by rw [hwt]; decide)
  have hz0 : z 0 = h * e (t 0) * h⁻¹ := by rw [hz]
  rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one, ← hdz, hz0] at hc
  exact hc.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)

theorem ggQ2_false_of_conj_mem_ggAutDispl
    (hFF : GGFFLinearProp2Input) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3)
    (hT : GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
        (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.T 0) ∨
      GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
        (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.T 0))
    {g : G} (hg : g * x * g⁻¹ ∈ ggAutDispl Bs (ggAutomizer J Bs)) : False := by
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hBsC hBstar.1 hDJ.1
      (GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1)
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  have hgL : g * x * g⁻¹ ∈ L := hJL (ggAutDispl_le_inf hBsJ hg).2
  rcases hT with ⟨e, he⟩ | ⟨e, he⟩
  · exact he ⟨_, hgL⟩ hg (ggQ2_isConj_of_conj hFF hS hp GGFF.model_SL6 e
      (Or.inl (ggHasLabel_of_mulEquiv_SL6 e)) rfl)
  · exact he ⟨_, hgL⟩ hg (ggQ2_isConj_of_conj hFF hS hp GGFF.model_SL7 e
      (Or.inr (ggHasLabel_of_mulEquiv_SL7 e)) rfl)

theorem ggQTwoLemma895Prime_of_lBalance
    (hLB : GGLBalanceInput) (hFF : GGFFLinearProp2Input)
    (hp3 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGQTwoSetting p B Bs x L D J → p = 3)
    (hcell : GGQTwoVACCell) : GGQTwoLemma895Prime := by
  intro G _ _ p B Bs x L D J hS u hu hu1 htr h4
  have hp : p = 3 := hp3 G p B Bs x L D J hS
  obtain ⟨hI1, hK1, h9, hT⟩ := hcell G p B Bs x L D J hS hp h4
  have h2 : 2 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) := by omega
  have hprime : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hS.1.1.2.2
  have hBsC : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hBsC hBstar.1 hDJ.1
      (GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1)
  have hpJ : p ∣ Nat.card J :=
    @dvd_card_of_two_le_card_ggAutDispl G _ _ p ⟨hprime⟩ Bs J hBstar.2.1 hBsJ h2
  have hAJ : ggAutomizer J Bs ≠ ⊥ := ne_bot_of_two_le_card_ggAutDispl h2
  intro φ hφ hφu
  obtain ⟨g, -, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
  refine mem_ggAutomizer_iff.mpr ⟨g, ?_, hgN, hgφ⟩
  by_cases hDg : D.map (MulAut.conj g).toMonoidHom = D
  · exact ggQ2_normalizer_inf_le_of_dvd hLB hpJ hS.1 hAJ hK1
      ⟨hgN, mem_normalizer_iff_map_conj.mpr hDg⟩
  · exfalso
    have hgu : g * (u : G) * g⁻¹ ∈ Subgroup.zpowers (u : G) := by
      have hmem : (φ u : G) ∈ Subgroup.zpowers (u : G) := by
        have h := Subgroup.mem_map_of_mem Bs.subtype hφu
        rw [MonoidHom.map_zpowers] at h
        exact h
      rwa [hgφ u] at hmem
    have hle := ggQ2_trivialLine_conj_displ_le hLB hS hpJ hI1 hu hu1 htr hgN hgu hDg
    have hmem := ggQ2_inv_conj_x_mem_ggAutDispl hS hp h9 hle
    exact ggQ2_false_of_conj_mem_ggAutDispl hFF hS hp hT (g := g⁻¹) (by simpa using hmem)

end CFSG.StandardType

end
