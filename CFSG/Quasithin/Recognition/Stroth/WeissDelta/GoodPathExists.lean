module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.GoodPath

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem le_inf_sup_of_le_sup {z w y : V} (hw : Γ.Adj z w) (hy : Γ.Adj z y)
    (B : Subgroup H) (hBsoc : B ≤ socleAt H Γ z)
    (hBz : B ≤ MulAction.stabilizer H z)
    (h : socTorus H Γ z w y ≤ B ⊔ fixingSubgroup H (Γ.neighborSet z)) :
    socTorus H Γ z w y ≤
      (B ⊓ socTorus H Γ z w y) ⊔ fixingSubgroup H (Γ.neighborSet z) := by
  intro t ht
  have hBnorm : B ≤ Subgroup.normalizer
      (fixingSubgroup H (Γ.neighborSet z) : Set H) :=
    hBz.trans (stabilizer_le_normalizer_fixingSubgroup (H := H) (Γ := Γ) (z := z))
  have ht' : t ∈ ((B ⊔ fixingSubgroup H (Γ.neighborSet z) : Subgroup H) : Set H) := h ht
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B
    (fixingSubgroup H (Γ.neighborSet z)) hBnorm] at ht'
  rcases ht' with ⟨b, hb, k, hk, hbk⟩
  have htw : t ∈ MulAction.stabilizer H w := ht.1.2
  have hty : t ∈ MulAction.stabilizer H y := ht.2
  have hksoc : k ∈ socTorus H Γ z w y := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mem_sup_right hk
    · exact (mem_fixingSubgroup_iff H).mp hk w hw
    · exact (mem_fixingSubgroup_iff H).mp hk y hy
  have hksw : k ∈ MulAction.stabilizer H w :=
    (mem_fixingSubgroup_iff H).mp hk w hw
  have hksy : k ∈ MulAction.stabilizer H y :=
    (mem_fixingSubgroup_iff H).mp hk y hy
  have hbS : b ∈ socTorus H Γ z w y := by
    have hbeq : b = t * k⁻¹ := by rw [← hbk]; group
    refine ⟨⟨hBsoc hb, ?_⟩, ?_⟩
    · rw [hbeq]
      exact Subgroup.mul_mem _ htw (Subgroup.inv_mem _ hksw)
    · rw [hbeq]
      exact Subgroup.mul_mem _ hty (Subgroup.inv_mem _ hksy)
  rw [← hbk]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hb, hbS⟩))
    (Subgroup.mem_sup_right hk)

private theorem exists_odd_torus_generator {z w y : V} (hLz : LocalFacts H Γ z)
    (hz : Γ.Adj z w) (hy : Γ.Adj z y) (hwy : w ≠ y)
    (B : Subgroup H) (hBsoc : B ≤ socleAt H Γ z)
    (hBz : B ≤ MulAction.stabilizer H z)
    (hsup : socTorus H Γ z w y ≤ B ⊔ fixingSubgroup H (Γ.neighborSet z)) :
    ∃ b ∈ B ⊓ socTorus H Γ z w y, Odd (orderOf b) ∧
      socTorus H Γ z w y ≤ Subgroup.closure {b} ⊔ fixingSubgroup H (Γ.neighborSet z) := by
  have hgen : socTorus H Γ z w y ≤
      (B ⊓ socTorus H Γ z w y) ⊔ fixingSubgroup H (Γ.neighborSet z) :=
    le_inf_sup_of_le_sup hz hy B hBsoc hBz hsup
  exact hLz.torusGen w y hz hy hwy (B ⊓ socTorus H Γ z w y) inf_le_right hgen

private theorem odd_relIndex_of_odd_card {z : V} {K : Subgroup H} (hK : Odd (Nat.card K)) :
    Odd ((fixingSubgroup H (Γ.neighborSet z)).relIndex K) :=
  hK.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)

private theorem odd_card_closure_singleton {b : H} (hb : Odd (orderOf b)) :
    Odd (Nat.card (Subgroup.closure {b})) := by
  rw [← Subgroup.zpowers_eq_closure b, Nat.card_zpowers]
  exact hb

theorem conj_mem_socleAt {z : V} {c x : H} (hcz : c • z = z)
    (hx : x ∈ socleAt H Γ z) :
    c * x * c⁻¹ ∈ socleAt H Γ z := by
  have h := socleAt_smul (H := H) (Γ := Γ) c z
  rw [hcz] at h
  have hmem : (MulAut.conj c) x ∈ socleAt H Γ z := by
    rw [h]
    exact Subgroup.mem_map_of_mem _ hx
  simpa [MulAut.conj_apply] using hmem

private theorem conj_torus_generator {z : V} {c b : H} (hcz : c • z = z)
    {w y : V} (hcw : c • w = w)
    (hgen : socTorus H Γ z w y ≤
      Subgroup.closure {b} ⊔ fixingSubgroup H (Γ.neighborSet z)) :
    socTorus H Γ z w (c • y) ≤
      Subgroup.closure {c * b * c⁻¹} ⊔ fixingSubgroup H (Γ.neighborSet z) := by
  have hsoc : socTorus H Γ z w (c • y) =
      (socTorus H Γ z w y).map (MulAut.conj c).toMonoidHom := by
    have h := socTorus_smul (H := H) (Γ := Γ) c z w y
    rw [hcz, hcw] at h
    exact h
  rw [hsoc]
  calc
    (socTorus H Γ z w y).map (MulAut.conj c).toMonoidHom ≤
        (Subgroup.closure {b} ⊔ fixingSubgroup H (Γ.neighborSet z)).map
          (MulAut.conj c).toMonoidHom := Subgroup.map_mono hgen
    _ = Subgroup.closure {c * b * c⁻¹} ⊔ fixingSubgroup H (Γ.neighborSet z) := by
      rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_singleton]
      have hb : (MulAut.conj c).toMonoidHom b = c * b * c⁻¹ := by
        simp [MulAut.conj_apply]
      rw [hb]
      congr 1
      have h := fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) c z
      rw [hcz] at h
      exact h.symm

theorem exists_isGoodPath_snoc [Finite H] {n : ℕ} (hn : 3 ≤ n) (hM : MoufangCondition H Γ n)
    (hne : ∀ v w : V, Γ.Adj v w → ∃ u, Γ.Adj v u ∧ u ≠ w)
    (hL : ∀ z, LocalFacts H Γ z) {s : ℕ} (hs : 1 ≤ s) {p : GPath Γ s}
    (hp : IsGoodPath H p) : ∃ w, ∃ h : Γ.Adj (p s) w, IsGoodPath H (p.snoc w h) := by
  classical
  induction s with
  | zero => omega
  | succ t ih =>
    by_cases hbase : t + 1 ≤ n
    · obtain ⟨u, hu, hune⟩ := hne (p (t + 1)) (p t) (p.adj t (by omega)).symm
      have hnb : (p.snoc u hu).NoBack :=
        GPath.noBack_snoc hp.1 hu (fun _ => by simpa using hune)
      refine ⟨u, hu, ?_⟩
      exact isGoodPath_of_noBack hn hM hne (fun z => (hL z).kernel_le)
        (s := t + 2) (by omega) hnb
    · have hlong : n + 1 ≤ t + 1 := by omega
      have ht : 3 ≤ t := by omega
      set q : GPath Γ t := p.drop 1 (by omega : 1 ≤ t + 1) with hq_def
      have hqgood : IsGoodPath H q :=
        hp.drop 1 (by omega : 1 ≤ t + 1)
      obtain ⟨w, hw, hW1⟩ := ih (by omega) hqgood
      set W1 : GPath Γ (t + 1) := q.snoc w hw with hW1_def
      have hW1_nb : W1.NoBack := hW1.1
      have hW1_apply : ∀ i, i ≤ t → W1 i = p (i + 1) := by
        intro i hi
        have h1 : W1 i = q i := by
          rw [hW1_def]
          exact GPath.snoc_of_le q w hw hi
        have h2 : q i = p (i + 1) := by
          rw [hq_def]
          simpa [Nat.add_comm] using GPath.drop_apply p 1 (by omega) (i := i) hi
        rw [h1, h2]
      have hW1_last : W1 (t + 1) = w := by
        rw [hW1_def]
        exact GPath.snoc_last q w hw
      have hw_p : Γ.Adj (p (t + 1)) w := by
        have h := hw
        rw [hq_def, GPath.drop_apply p 1 (by omega) (i := t) (by omega)] at h
        simpa [Nat.add_comm] using h
      have hW1_nb_s : p t ≠ w := by
        have h := hW1_nb (t - 1) (by omega)
        rw [hW1_apply (t - 1) (by omega), show t - 1 + 1 = t by omega,
          show t - 1 + 2 = t + 1 by omega, hW1_last] at h
        exact h
      have hnotback : p t ≠ w := hW1_nb_s
      let xs : V := p (t + 1)
      let xsm : V := p t
      let Sbs : Subgroup H := socTorus H Γ xs xsm w
      let Bbs : Subgroup H := W1.stabPath ⊓ socleAt H Γ xs
      have hBbs_soc : Bbs ≤ socleAt H Γ xs := inf_le_right
      have hBbs_stab : Bbs ≤ MulAction.stabilizer H xs := by
        intro g hg
        rw [MulAction.mem_stabilizer_iff]
        have h := (GPath.mem_stabPath_iff.mp hg.1) t (by omega)
        rwa [hW1_apply t le_rfl] at h
      have hgoodW1 : Sbs ≤ Bbs ⊔ fixingSubgroup H (Γ.neighborSet xs) := by
        have h := hW1.2 t (by omega) (by omega : t < t + 1)
        rw [hW1_apply t le_rfl, hW1_apply (t - 1) (by omega),
          show t - 1 + 1 = t by omega, hW1_last] at h
        exact h
      have hxs_xsm : Γ.Adj xs xsm := by
        have h := p.adj t (by omega : t < t + 1)
        exact h.symm
      have hxs_w : Γ.Adj xs w := hw_p
      have hxsm_w : xsm ≠ w := hnotback
      obtain ⟨bs, hbs, hbs_odd, hbs_gen⟩ :=
        exists_odd_torus_generator (hL xs) hxs_xsm hxs_w hxsm_w Bbs hBbs_soc
          hBbs_stab hgoodW1
      have hbsW1 : bs ∈ W1.stabPath := hbs.1.1
      have hbs_soc : bs ∈ socleAt H Γ xs := hbs.1.2
      let S1 : Subgroup H := socTorus H Γ (p 1) (p 0) (p 2)
      let B1 : Subgroup H := p.stabPath ⊓ socleAt H Γ (p 1)
      have hB1_soc : B1 ≤ socleAt H Γ (p 1) := inf_le_right
      have hB1_stab : B1 ≤ MulAction.stabilizer H (p 1) := by
        intro g hg
        rw [MulAction.mem_stabilizer_iff]
        exact (GPath.mem_stabPath_iff.mp hg.1) 1 (by omega)
      have hgood1 : S1 ≤ B1 ⊔ fixingSubgroup H (Γ.neighborSet (p 1)) :=
        hp.2 1 (by omega) (by omega)
      have h02 : p 0 ≠ p 2 := hp.1 0 (by omega)
      obtain ⟨b1, hb1, hb1_odd, hb1_gen⟩ :=
        exists_odd_torus_generator (hL (p 1)) (p.adj 0 (by omega)).symm
          (p.adj 1 (by omega)) h02 B1 hB1_soc hB1_stab hgood1
      have hb1Gp : b1 ∈ p.stabPath := hb1.1.1
      have hA1_le : Subgroup.closure {b1} ≤
          MulAction.stabilizer H (p 1) ⊓ MulAction.stabilizer H (p 2) := by
        rw [Subgroup.closure_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        refine ⟨?_, ?_⟩
        · exact MulAction.mem_stabilizer_iff.mpr
            ((GPath.mem_stabPath_iff.mp hb1Gp) 1 (by omega))
        · exact MulAction.mem_stabilizer_iff.mpr
            ((GPath.mem_stabPath_iff.mp hb1Gp) 2 (by omega))
      have hBs_le : Subgroup.closure {bs} ≤
          MulAction.stabilizer H (p 1) ⊓ MulAction.stabilizer H (p 2) := by
        rw [Subgroup.closure_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        refine ⟨?_, ?_⟩
        · refine MulAction.mem_stabilizer_iff.mpr ?_
          have h := (GPath.mem_stabPath_iff.mp hbsW1) 0 (by omega)
          rwa [hW1_apply 0 (by omega)] at h
        · refine MulAction.mem_stabilizer_iff.mpr ?_
          have h := (GPath.mem_stabPath_iff.mp hbsW1) 1 (by omega)
          rwa [hW1_apply 1 (by omega)] at h
      have hA1_odd : Odd ((fixingSubgroup H (Γ.neighborSet (p 1))).relIndex
          (Subgroup.closure {b1})) :=
        odd_relIndex_of_odd_card (odd_card_closure_singleton hb1_odd)
      have hBs_odd : Odd ((fixingSubgroup H (Γ.neighborSet (p 1))).relIndex
          (Subgroup.closure {bs})) :=
        odd_relIndex_of_odd_card (odd_card_closure_singleton hbs_odd)
      have hsup1 : socTorus H Γ (p 1) (p 2) (p 0) ≤
          Subgroup.closure {b1} ⊔ fixingSubgroup H (Γ.neighborSet (p 1)) := by
        have h := hb1_gen
        rwa [socTorus_comm (H := H) (Γ := Γ) (p 1) (p 0) (p 2)] at h
      obtain ⟨c, hc, hcfix⟩ := (hL (p 1)).oddConj (p 2) (p 0)
        (p.adj 1 (by omega)) (p.adj 0 (by omega)).symm (fun h => h02 h.symm)
        (Subgroup.closure {b1}) (Subgroup.closure {bs}) hA1_le hBs_le hA1_odd hBs_odd hsup1
      let a : H := c * bs * c⁻¹
      have ha_fix0 : a • p 0 = p 0 := hcfix bs (Subgroup.subset_closure (by simp))
      have hc_stab : ∀ i, 1 ≤ i → i ≤ t + 1 → c ∈ MulAction.stabilizer H (p i) := by
        intro i hi1 hit
        have hA : Subgroup.closure {b1} ≤ MulAction.stabilizer H (p i) := by
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact MulAction.mem_stabilizer_iff.mpr
            ((GPath.mem_stabPath_iff.mp hb1Gp) i (by omega))
        have hB : Subgroup.closure {bs} ≤ MulAction.stabilizer H (p i) := by
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          refine MulAction.mem_stabilizer_iff.mpr ?_
          have h := (GPath.mem_stabPath_iff.mp hbsW1) (i - 1) (by omega)
          rw [hW1_apply (i - 1) (by omega), show i - 1 + 1 = i by omega] at h
          exact h
        exact (sup_le hA hB) hc
      have ha_fix : ∀ i, i ≤ t + 1 → a • p i = p i := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact ha_fix0
        · have hbsi : bs • p i = p i := by
            have h := (GPath.mem_stabPath_iff.mp hbsW1) (i - 1) (by omega)
            rw [hW1_apply (i - 1) (by omega), show i - 1 + 1 = i by omega] at h
            exact h
          have hci : c • p i = p i :=
            MulAction.mem_stabilizer_iff.mp (hc_stab i hi0 hi)
          have hciinv : c⁻¹ • p i = p i :=
            MulAction.mem_stabilizer_iff.mp (Subgroup.inv_mem _ (hc_stab i hi0 hi))
          calc
            a • p i = c • (bs • (c⁻¹ • p i)) := by
              change (c * bs * c⁻¹) • p i = c • (bs • (c⁻¹ • p i))
              rw [mul_smul, mul_smul]
            _ = c • (bs • p i) := by rw [hciinv]
            _ = c • p i := by rw [hbsi]
            _ = p i := hci
      have hbs_w : bs • w = w := by
        have h := (GPath.mem_stabPath_iff.mp hbsW1) (t + 1) (by omega)
        rwa [hW1_last] at h
      let xp : V := c • w
      have ha_fix_xp : a • xp = xp := by
        show (c * bs * c⁻¹) • (c • w) = c • w
        rw [mul_smul, mul_smul, inv_smul_smul, hbs_w]
      have hcxs : c • xs = xs :=
        MulAction.mem_stabilizer_iff.mp (hc_stab (t + 1) (by omega) le_rfl)
      have hcsm : c • xsm = xsm :=
        MulAction.mem_stabilizer_iff.mp (hc_stab t (by omega) (by omega))
      have ha_soc : a ∈ socleAt H Γ xs := conj_mem_socleAt hcxs hbs_soc
      have ha_gen : socTorus H Γ xs xsm xp ≤
          Subgroup.closure {a} ⊔ fixingSubgroup H (Γ.neighborSet xs) := by
        have h := conj_torus_generator (z := xs) (c := c) (b := bs) hcxs
          (w := xsm) (y := w) hcsm hbs_gen
        simpa [xp, a] using h
      have h' : Γ.Adj (p (t + 1)) xp := by
        have h := (GraphAction.adj_smul c (p (t + 1)) w).mpr hw_p
        rwa [hcxs] at h
      have hxp_ne : xp ≠ p t := by
        intro h
        have hcsm' : c • p t = p t := hcsm
        have hweq : w = p t := by
          apply MulAction.injective c
          change c • w = c • p t
          rw [show c • w = p t from h, hcsm']
        exact hnotback hweq.symm
      refine ⟨xp, h', ?_⟩
      have hnb : (p.snoc xp h').NoBack :=
        GPath.noBack_snoc hp.1 h' (fun _ => by simpa using hxp_ne)
      refine ⟨hnb, ?_⟩
      intro i hi0 his
      by_cases hi : i = t + 1
      · subst i
        have ha_mem : a ∈ (p.snoc xp h').stabPath := by
          rw [GPath.mem_stabPath_iff]
          intro l hl
          by_cases hlt : l ≤ t + 1
          · rw [GPath.snoc_of_le _ _ _ hlt]
            exact ha_fix l hlt
          · have hl' : l = t + 2 := by omega
            subst l
            rw [GPath.snoc_last]
            exact ha_fix_xp
        have hcl : Subgroup.closure {a} ≤
            (p.snoc xp h').stabPath ⊓ socleAt H Γ (p (t + 1)) := by
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨ha_mem, ha_soc⟩
        rw [GPath.snoc_of_le _ _ _ (by omega : t + 1 ≤ t + 1),
          GPath.snoc_of_le _ _ _ (by omega : t + 1 - 1 ≤ t + 1), GPath.snoc_last]
        exact le_trans ha_gen (sup_le_sup hcl le_rfl)
      · have hit : i ≤ t := by omega
        let Si : Subgroup H := socTorus H Γ (p i) (p (i - 1)) (p (i + 1))
        let Bi : Subgroup H := p.stabPath ⊓ socleAt H Γ (p i)
        have hBi_soc : Bi ≤ socleAt H Γ (p i) := inf_le_right
        have hBi_stab : Bi ≤ MulAction.stabilizer H (p i) := by
          intro g hg
          rw [MulAction.mem_stabilizer_iff]
          exact (GPath.mem_stabPath_iff.mp hg.1) i (by omega)
        have hprev_ne : p (i - 1) ≠ p (i + 1) := by
          have h := hp.1 (i - 1) (by omega)
          rwa [show i - 1 + 2 = i + 1 by omega] at h
        have hgood_i : Si ≤ Bi ⊔ fixingSubgroup H (Γ.neighborSet (p i)) :=
          hp.2 i hi0 (by omega)
        obtain ⟨bi, hbi, hbi_odd, hbi_gen⟩ :=
          exists_odd_torus_generator (hL (p i)) (by
            have h := (p.adj (i - 1) (by omega)).symm
            rwa [show i - 1 + 1 = i by omega] at h)
            (p.adj i (by omega)) hprev_ne Bi hBi_soc hBi_stab hgood_i
        have hbiGp : bi ∈ p.stabPath := hbi.1.1
        have hAs_le : Subgroup.closure {a} ≤
            MulAction.stabilizer H xs ⊓ MulAction.stabilizer H xsm := by
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          refine ⟨?_, ?_⟩
          · exact MulAction.mem_stabilizer_iff.mpr (ha_fix (t + 1) le_rfl)
          · exact MulAction.mem_stabilizer_iff.mpr (ha_fix t (by omega))
        have hBi_le : Subgroup.closure {bi} ≤
            MulAction.stabilizer H xs ⊓ MulAction.stabilizer H xsm := by
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          refine ⟨?_, ?_⟩
          · exact MulAction.mem_stabilizer_iff.mpr
              ((GPath.mem_stabPath_iff.mp hbiGp) (t + 1) (by omega))
          · exact MulAction.mem_stabilizer_iff.mpr
              ((GPath.mem_stabPath_iff.mp hbiGp) t (by omega))
        have ha_odd : Odd (orderOf a) := by
          have ha_eq : a = (MulAut.conj c).toMonoidHom bs := by
            simp [a, MulAut.conj_apply]
          rw [ha_eq, orderOf_injective (MulAut.conj c).toMonoidHom
            (MulAut.conj c).injective bs]
          exact hbs_odd
        have hA_odd : Odd ((fixingSubgroup H (Γ.neighborSet xs)).relIndex
            (Subgroup.closure {a})) :=
          odd_relIndex_of_odd_card (odd_card_closure_singleton ha_odd)
        have hBi_odd' : Odd ((fixingSubgroup H (Γ.neighborSet xs)).relIndex
            (Subgroup.closure {bi})) :=
          odd_relIndex_of_odd_card (odd_card_closure_singleton hbi_odd)
        obtain ⟨ci, hci, hcifix⟩ := (hL xs).oddConj xsm xp hxs_xsm h' hxp_ne.symm
          (Subgroup.closure {a}) (Subgroup.closure {bi}) hAs_le hBi_le hA_odd hBi_odd' ha_gen
        let b'i : H := ci * bi * ci⁻¹
        have hci_stab : ∀ l, l ≤ t + 1 → ci ∈ MulAction.stabilizer H (p l) := by
          intro l hl
          have hA : Subgroup.closure {a} ≤ MulAction.stabilizer H (p l) := by
            rw [Subgroup.closure_le]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact MulAction.mem_stabilizer_iff.mpr (ha_fix l hl)
          have hB : Subgroup.closure {bi} ≤ MulAction.stabilizer H (p l) := by
            rw [Subgroup.closure_le]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact MulAction.mem_stabilizer_iff.mpr
              ((GPath.mem_stabPath_iff.mp hbiGp) l hl)
          exact (sup_le hA hB) hci
        have hci_pos : ci • p i = p i :=
          MulAction.mem_stabilizer_iff.mp (hci_stab i (by omega))
        have hbi'_mem : b'i ∈ (p.snoc xp h').stabPath := by
          rw [GPath.mem_stabPath_iff]
          intro l hl
          by_cases hlt : l ≤ t + 1
          · rw [GPath.snoc_of_le _ _ _ hlt]
            have hci_l : ci • p l = p l :=
              MulAction.mem_stabilizer_iff.mp (hci_stab l hlt)
            have hciinv_l : ci⁻¹ • p l = p l :=
              MulAction.mem_stabilizer_iff.mp (Subgroup.inv_mem _ (hci_stab l hlt))
            have hbi_l : bi • p l = p l := (GPath.mem_stabPath_iff.mp hbiGp) l hlt
            calc
              b'i • p l = ci • (bi • (ci⁻¹ • p l)) := by
                change (ci * bi * ci⁻¹) • p l = ci • (bi • (ci⁻¹ • p l))
                rw [mul_smul, mul_smul]
              _ = ci • (bi • p l) := by rw [hciinv_l]
              _ = ci • p l := by rw [hbi_l]
              _ = p l := hci_l
          · have hl' : l = t + 2 := by omega
            subst l
            rw [GPath.snoc_last]
            exact hcifix bi (Subgroup.subset_closure (by simp))
        have hbi'_soc : b'i ∈ socleAt H Γ (p i) :=
          conj_mem_socleAt hci_pos hbi.1.2
        have hbi'_gen : Si ≤ Subgroup.closure {b'i} ⊔
            fixingSubgroup H (Γ.neighborSet (p i)) := by
          have hci_next : ci • p (i + 1) = p (i + 1) :=
            MulAction.mem_stabilizer_iff.mp (hci_stab (i + 1) (by omega))
          have hci_prev : ci • p (i - 1) = p (i - 1) :=
            MulAction.mem_stabilizer_iff.mp (hci_stab (i - 1) (by omega))
          have h := conj_torus_generator (z := p i) (c := ci) (b := bi) hci_pos
            (w := p (i - 1)) (y := p (i + 1)) hci_prev hbi_gen
          rw [hci_next] at h
          simpa [Si, b'i] using h
        have hcl : Subgroup.closure {b'i} ≤
            (p.snoc xp h').stabPath ⊓ socleAt H Γ (p i) := by
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨hbi'_mem, hbi'_soc⟩
        rw [GPath.snoc_of_le _ _ _ (by omega : i ≤ t + 1),
          GPath.snoc_of_le _ _ _ (by omega : i - 1 ≤ t + 1),
          GPath.snoc_of_le _ _ _ (by omega : i + 1 ≤ t + 1)]
        exact le_trans hbi'_gen (sup_le_sup hcl le_rfl)

end CFSG.Quasithin.Stroth.WeissDelta
