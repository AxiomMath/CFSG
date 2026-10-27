module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniBlockType
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LocalAnalysis.ComponentInitial.KnownFourGroupDiagonalPump
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks

private theorem cuq2sp_card_statedSp_eq_ordBC {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (r : ℕ) :
    Nat.card (StatedSp r K) = CFSG.Open.ordBC r (2 ^ f) := by
  rw [SymplecticFlag.card_statedSp (K := K) r, hK, CFSG.Open.ordBC]
  have hodd : Odd (2 ^ f - 1) := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [pow_succ]
    exact ⟨2 ^ g - 1, by have := Nat.one_le_two_pow (n := g); omega⟩
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [hg, Nat.div_one, sq]

private theorem cuq2sp_ordBC_one_eq_ordA_one (f : ℕ) (hf : 1 ≤ f) :
    CFSG.Open.ordBC 1 (2 ^ f) = CFSG.Open.ordA 1 (2 ^ f) := by
  rw [CFSG.Open.ordBC, CFSG.Open.ordA]
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have hodd : Odd (2 ^ f - 1) := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [pow_succ]
      exact ⟨2 ^ g - 1, by have := Nat.one_le_two_pow (n := g); omega⟩
    exact Nat.coprime_two_left.mpr hodd
  rw [hg, Nat.div_one]
  simp [Finset.Icc_self]

theorem q2UniSp_fixedBlock_false {H : Type} [Group H] {F C : Subgroup H}
    (hC : IsComponentOf C F) {K : Type} [Field K] [Finite K] [CharP K 2] {n₁ : ℕ}
    (e : ↥F ≃* ↥(StatedSp n₁ K)) {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E)
    (hd : 3 ≤ d) (hdm : ¬ (d = 3 ∧ m = 1))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :
    False := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite E := hE.finite
  haveI : Fintype E := Fintype.ofFinite E
  have hmem : 1 ≤ m := hE.one_le
  have hKcardE : Nat.card E = (2 ^ m) ^ 2 := by
    rw [hE.card, ← pow_mul, Nat.mul_comm 2 m]
  have hadmU : CFSG.Open.StatedLieAdmissible .PSU d 2 m := by
    refine ⟨Nat.prime_two, hmem, hd, ?_⟩
    intro h
    rw [Prod.mk.injEq] at h
    exact hdm ⟨h.1, Nat.pow_right_injective (show 2 ≤ 2 by norm_num) (by
      change (2 : ℕ) ^ m = (2 : ℕ) ^ 1
      rw [h.2])⟩
  have hmodU : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) .PSU d 2 m :=
    CFSG.StandardType.statedClassicalModel_unitary (K := E) d m hKcardE hadmU
  have hU : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) =
      CFSG.Open.ordTwistedA (d - 1) (2 ^ m) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmodU).2.1 rfl
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have smallFalse : (n₁ = 0 ∨ (n₁ = 1 ∧ Nat.card K = 2)) → False := by
    intro hsmall
    have hCF0 : CFSG.Assembly.IsComponentOf (C.subgroupOf F) ⊤ :=
      (isComponentOf_map_iff (f := F.subtype) F.subtype_injective).mp (by
        rw [Subgroup.map_subgroupOf_eq_of_le hC.1, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
        exact hC)
    have hmap := CFSG.isComponentOf_map_mulEquiv e
      (CFSG.Assembly.isComponentOf_iff_open.mp hCF0)
    have hFtop : (⊤ : Subgroup ↥F).map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.surjective
    rw [hFtop] at hmap
    have hC' : CFSG.Assembly.IsComponentOf ((C.subgroupOf F).map e.toMonoidHom) ⊤ :=
      CFSG.Assembly.isComponentOf_iff_open.mpr hmap
    exact (not_isComponentOf_statedSp_of_small hsmall
      (((C.subgroupOf F).map e.toMonoidHom).map (StatedSp n₁ K).subtype))
      (isComponentOf_map_subtype_top hC')
  have h64 : 2 ^ 6 ∣ CFSG.Open.ordTwistedA (d - 1) (2 ^ m) := by
    obtain ⟨r, -, hmul⟩ :=
      (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := d - 1) (g := m) (by omega) hmem).two
    rw [hmul]
    refine dvd_mul_of_dvd_left (pow_dvd_pow 2 ?_) r
    by_cases hd3 : d = 3
    · subst hd3
      have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · exact absurd ⟨rfl, by omega⟩ hdm
        · exact h
      have hexp : (3 - 1) * ((3 - 1) + 1) / 2 = 3 := by norm_num
      rw [hexp]
      omega
    · have h3 : 3 ≤ d - 1 := by omega
      have h4 : 4 ≤ (d - 1) + 1 := by omega
      have h12 : 3 * 4 ≤ (d - 1) * ((d - 1) + 1) := Nat.mul_le_mul h3 h4
      have hX : 6 ≤ (d - 1) * ((d - 1) + 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        omega
      exact hX.trans (Nat.le_mul_of_pos_left _ (by omega))
  by_cases hsmall : n₁ = 0 ∨ (n₁ = 1 ∧ Nat.card K = 2)
  · exact smallFalse hsmall
  · by_cases h42 : n₁ = 2 ∧ Nat.card K = 2
    · obtain ⟨hn2', hK2⟩ := h42
      subst hn2'
      have hcardC : Nat.card (↥C ⧸ Subgroup.center ↥C) =
          CFSG.Open.ordTwistedA (d - 1) (2 ^ m) :=
        (Nat.card_congr θ.toEquiv).trans hU
      have hdvd1 : Nat.card (↥C ⧸ Subgroup.center ↥C) ∣ Nat.card ↥C :=
        Subgroup.card_quotient_dvd_card _
      have hdvd2 : Nat.card ↥C ∣ Nat.card ↥F := by
        have h := Subgroup.card_subgroup_dvd_card (C.subgroupOf F)
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC.1).toEquiv] at h
      have hF720 : Nat.card ↥F = 720 := by
        rw [Nat.card_congr e.toEquiv, SymplecticFlag.card_statedSp_two, hK2]
        norm_num
      rw [hcardC] at hdvd1
      have hbad : 2 ^ 6 ∣ 720 := h64.trans (hdvd1.trans (hF720 ▸ hdvd2))
      norm_num at hbad
    · have hn₁ : 1 ≤ n₁ := by
        rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
        · exact absurd (Or.inl h0) hsmall
        · exact hpos
      have h1 : ¬(n₁ = 1 ∧ Nat.card K = 2) := fun h => hsmall (Or.inr h)
      have h2 : ¬(n₁ = 2 ∧ Nat.card K = 2) := h42
      have hqSp : CFSG.Open.IsQuasisimple (StatedSp n₁ K) :=
        CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.isQuasisimple_statedSp_of_not_small
          (K := K) hn₁ h1 h2
      have hqF : CFSG.Assembly.IsQuasisimple F :=
        CFSG.Assembly.IsQuasisimple.of_mulEquiv e hqSp
      have hCF : C = F := CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hqF hC
      let eCF : ↥C ≃* ↥F := MulEquiv.subgroupCongr hCF
      let eQ : ↥C ⧸ Subgroup.center ↥C ≃*
          ↥(StatedSp n₁ K) ⧸ Subgroup.center ↥(StatedSp n₁ K) :=
        (QuotientGroup.congr _ _ eCF (Subgroup.map_center_eq eCF)).trans
          (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
      let θK := eQ.symm.trans θ
      have hEq : Nat.card (↥(StatedSp n₁ K) ⧸ Subgroup.center ↥(StatedSp n₁ K)) =
          Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))) :=
        Nat.card_congr θK.toEquiv
      have hZ : Subgroup.center ↥(StatedSp n₁ K) = ⊥ :=
        CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.center_statedSp_eq_bot
          (K := K) n₁
      have hG : Nat.card (↥(StatedSp n₁ K) ⧸ Subgroup.center ↥(StatedSp n₁ K)) =
          CFSG.Open.ordBC n₁ (2 ^ (f : ℕ)) := by
        rw [hZ,
          show Nat.card (↥(StatedSp n₁ K) ⧸ (⊥ : Subgroup ↥(StatedSp n₁ K))) =
            Nat.card ↥(StatedSp n₁ K) from
              Nat.card_congr (QuotientGroup.quotientBot (G := ↥(StatedSp n₁ K))).toEquiv]
        exact cuq2sp_card_statedSp_eq_ordBC hf hK n₁
      have horder : CFSG.Open.ordBC n₁ (2 ^ (f : ℕ)) =
          CFSG.Open.ordTwistedA (d - 1) (2 ^ m) :=
        hG.symm.trans (hEq.trans hU)
      have hu : 2 ≤ d - 1 := by omega
      by_cases hsp : n₁ = 1
      · subst hsp
        have hordA : CFSG.Open.ordA 1 (2 ^ (f : ℕ)) =
            CFSG.Open.ordTwistedA (d - 1) (2 ^ m) := by
          rw [← cuq2sp_ordBC_one_eq_ordA_one (f : ℕ) hf]
          exact horder
        exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA le_rfl hf hu hmem) hordA
      · have hn2 : 2 ≤ n₁ := by omega
        by_cases h3 : 3 ≤ n₁
        · exact (CFSG.Timmesfeld.Orders.ordBC_ne_ordTwistedA h3 hf hu hmem) horder
        · have hn₁2 : n₁ = 2 := by omega
          subst hn₁2
          have hN3 : (f : ℕ) * 4 ≠ 3 := by omega
          have hN6 : (f : ℕ) * 4 ≠ 6 := by omega
          exact (CFSG.Timmesfeld.Orders.ne_ordTwistedA_of_dvd_closed
            (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hf)
            CFSG.Timmesfeld.Orders.zBC_dvd_closed
            ((CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) hf).ne_small hN3 hN6) hu hmem) horder

theorem q2UniSp_block {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (s : ↥(StatedSp n K)) (hso : Odd (orderOf s)) (C : Subgroup ↥(StatedSp n K))
    (hC : IsComponentOf C (Subgroup.centralizer ({s} : Set ↥(StatedSp n K))))
    {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d)
    (hdm : ¬ (d = 3 ∧ m = 1))
    (hJE : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m)))) :
    Q2UniBlockHom (Subgroup.centralizer ({s} : Set ↥(StatedSp n K))) C := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨θ⟩ := hJE
  have hodd : Odd (orderOf (s : GL (Fin n ⊕ Fin n) K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hP, -, -, hc, hsup, hcard⟩ :=
    centralizer_block_decomp_Sp (s : GL (Fin n ⊕ Fin n) K) s.2 hodd
  have hcent : Subgroup.centralizer ({s} : Set ↥(StatedSp n K)) =
      (Subgroup.centralizer {(s : GL (Fin n ⊕ Fin n) K)}).comap (StatedSp n K).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent] at hC ⊢
  rw [← hsup] at hC
  obtain ⟨ε, hε, hCε⟩ := exists_isComponentOf_block P _ hc hC
  have hle : ∀ i : ↥P, glBlockCentralizer (StatedSp n K).subtype
      ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) i.1 ≤
      (Subgroup.centralizer {(s : GL (Fin n ⊕ Fin n) K)}).comap (StatedSp n K).subtype := by
    intro i
    rw [← hsup]
    exact le_iSup₂ (f := fun (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (_ : ε ∈ P) =>
      glBlockCentralizer (StatedSp n K).subtype
        ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε) i.1 i.2
  have hsup' : (⨆ i : ↥P, glBlockCentralizer (StatedSp n K).subtype
      ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) i.1) =
      (Subgroup.centralizer {(s : GL (Fin n ⊕ Fin n) K)}).comap (StatedSp n K).subtype :=
    (iSup_subtype' (f := fun (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (_ : ε ∈ P) =>
      glBlockCentralizer (StatedSp n K).subtype
        ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε)).symm.trans hsup
  have hcard' : Nat.card ↥((Subgroup.centralizer {(s : GL (Fin n ⊕ Fin n) K)}).comap
      (StatedSp n K).subtype) = ∏ i : ↥P, Nat.card ↥(glBlockCentralizer (StatedSp n K).subtype
        ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) i.1) := by
    rw [hcard]
    exact (Finset.prod_coe_sort P (fun ε => Nat.card ↥(glBlockCentralizer (StatedSp n K).subtype
      ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε))).symm
  have hcomm' : ∀ i j : ↥P, i ≠ j → ∀ x ∈ glBlockCentralizer (StatedSp n K).subtype
      ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) i.1,
      ∀ y ∈ glBlockCentralizer (StatedSp n K).subtype
        ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) j.1, Commute x y :=
    fun i j hij => hc i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
  obtain ⟨ρ, -, -, hρ⟩ := q2_block_projection_conj
    (fun i : ↥P => glBlockCentralizer (StatedSp n K).subtype
      ({(s : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) i.1) _ hle hcomm' hsup' hcard'
    ⟨ε, hε⟩
  rcases blockGroup_iso_Sp_cases (s : GL (Fin n ⊕ Fin n) K) s.2 hodd (hP ε hε) with
    ⟨n₁, ⟨e⟩⟩ | ⟨b, D, _, _, _, ⟨e⟩⟩ | ⟨a, Q, D, _, _, _, hDQ, ⟨e⟩⟩
  · exact (q2UniSp_fixedBlock_false hCε e hE hd hdm θ).elim
  · exact (q2Uni_linearBlock_false hCε e hE hd hdm θ).elim
  · obtain ⟨k, rfl, hD⟩ := exists_unitaryFieldData_two hDQ
    have e' := e.trans (guFullEquivUnitGroup hD)
    obtain ⟨ha, hak⟩ := q2Uni_unitaryBlock_params hCε hD e' hE hd hdm θ
    exact q2UniBlockHom_of_unitaryBlock ρ hρ hD ha hak e' hCε

theorem q2UniSpProj_lift {K : Type} [Field K] [Finite K] [CharP K 2] {l : ℕ} [NeZero l]
    {A : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K l)))} (hA : IsMulCommutative ↥A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenSpGroup K l)))
    {u : MulAut (LargeEvenProj (LargeEvenSpGroup K l))} (hu : u ∈ A)
    (huodd : Odd (orderOf u)) {J : Subgroup (LargeEvenProj (LargeEvenSpGroup K l))}
    (hJ : IsComponentOf J (ggAutFixedSubgroup u)) (hAJ : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J)
    {d m : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 m E) (hd : 3 ≤ d)
    (hdm : ¬ (d = 3 ∧ m = 1))
    (hJE : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin d) E (2 ^ m))))
    (M : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))
    (hM : ∀ α ∈ M, ∃ a ∈ A, ∀ j j' : ↥J,
      (j' : LargeEvenProj (LargeEvenSpGroup K l)) = a (j : LargeEvenProj (LargeEvenSpGroup K l)) →
        α (QuotientGroup.mk j) = QuotientGroup.mk j') :
    Q2UnitaryLift M := by
  classical
  have hZ := TableBSymp.center_spProj_eq_bot (K := K) (m := l)
  have hconj : Function.Injective
      (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K l) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K l))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZ)
  let e := TableBSymp.spProjEquivSp (K := K) (m := l)
  refine q2UnitaryLift_of_innerActor hconj hA hAI hu ?_ hAJ M hM
  intro s hs
  have hsodd : Odd (orderOf (e s)) := by
    have hord : orderOf u = orderOf s := by
      rw [← hs]
      exact orderOf_injective _ hconj s
    rw [MulEquiv.orderOf_eq, ← hord]
    exact huodd
  have hJc : IsComponentOf J (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSpGroup K l)))) := by
    have h := hJ
    rw [← hs, ggAutFixedSubgroup_mulAut_conj] at h
    exact h
  have hmap : (Subgroup.centralizer ({s} : Set (LargeEvenProj (LargeEvenSpGroup K l)))).map
      e.toMonoidHom = Subgroup.centralizer ({e s} : Set ↥(LargeEvenSpGroup K l)) := by
    have h := CFSG.ABGDGroups.map_inf_centralizer_of_injective e.toMonoidHom e.injective ⊤ s
    rwa [top_inf_eq, Subgroup.map_top_of_surjective _ e.surjective, top_inf_eq] at h
  have hJm : IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({e s} : Set ↥(LargeEvenSpGroup K l))) := by
    have h := CFSG.isComponentOf_map_mulEquiv e (CFSG.Assembly.isComponentOf_iff_open.mp hJc)
    rw [hmap] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mpr h
  obtain ⟨θ⟩ := hJE
  let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  let eJc : ↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) :=
    QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  refine Q2UniBlockHom.of_mulEquiv e ?_
  rw [hmap]
  exact q2UniSp_block (e s) hsodd (J.map e.toMonoidHom) hJm hE hd hdm ⟨eJc.symm.trans θ⟩

end CFSG.StandardType
