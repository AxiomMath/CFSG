module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UNt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16h_uelem_conjSubgroup_le_of_mem {K M : Subgroup G} (hK : K ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup K x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hK hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16h_uelem_conj_noncyclic {p : ℕ} {K P : Subgroup G} (hPK : P ≤ K)
    (hPp : IsPGroup p P) (hPc : ¬ IsCyclic ↥P) (x : G) :
    conjSubgroup P x ≤ conjSubgroup K x ∧ IsPGroup p (conjSubgroup P x) ∧
      ¬ IsCyclic ↥(conjSubgroup P x) := by
  have e := Subgroup.equivMapOfInjective P (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective
  refine ⟨fun y hy => ?_, hPp.of_equiv e, fun hc => hPc (e.isCyclic.2 hc)⟩
  rw [mem_conjSubgroup_iff] at hy ⊢
  exact hPK hy

private theorem s16h_uelem_mem_fixV_sup {W : Type} [CommGroup W] {A B : Subgroup (MulAut W)}
    {v : W} (hA : v ∈ fixV A) (hB : v ∈ fixV B) : v ∈ fixV (A ⊔ B) := by
  intro z hz
  have hle : A ⊔ B ≤ MulAction.stabilizer (MulAut W) v :=
    sup_le (fun x hx => MulAction.mem_stabilizer_iff.mpr (hA x hx))
      (fun y hy => MulAction.mem_stabilizer_iff.mpr (hB y hy))
  exact MulAction.mem_stabilizer_iff.mp (hle hz)

private theorem s16h_uelem_barSub_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {X₁ X₂ : Subgroup G} (h₁ : X₁ ≤ stabTil V₀ V) (h₂ : X₂ ≤ stabTil V₀ V) :
    barSub V₀ V hV (X₁ ⊔ X₂) = barSub V₀ V hV X₁ ⊔ barSub V₀ V hV X₂ := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

private theorem s16h_uelem_bar_conj {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (L : Subgroup G) {x : G} (hx : x ∈ D.M) :
    ∃ q ∈ Mbar D.M V₀ V h.isElemAbelian, barSub V₀ V h.isElemAbelian (conjSubgroup L x) =
      (lBar V₀ V h.isElemAbelian L).map (MulAut.conj q).toMonoidHom := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  exact ⟨(actTil V₀ V h.isElemAbelian ⟨x, hMs hx⟩)⁻¹,
    inv_mem (actTil_mem_barSub V₀ V h.isElemAbelian hx (hMs hx)),
    s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian (hMs hx) L⟩

private theorem s16h_uelem_pRank_bar {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (L : Subgroup G) {x : G} (hx : x ∈ D.M) (p : ℕ) :
    CFSG.Open.pRank p (barSub V₀ V h.isElemAbelian (conjSubgroup L x)) =
      CFSG.Open.pRank p (lBar V₀ V h.isElemAbelian L) := by
  obtain ⟨q, -, hq⟩ := s16h_uelem_bar_conj h L hx
  rw [hq]
  exact s16h_pRank_map_aut p _ (MulAut.conj q)

theorem s16h_condU_of_derived_elemAbelian (D : Data G) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (hσ : D.sig = D.sig1) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLe : IsElemAbelian p (lBar V₀ V h.hyp151.isElemAbelian L))
    (hr : 2 ≤ CFSG.Open.pRank p (lBar V₀ V h.hyp151.isElemAbelian L))
    (hd : lBar V₀ V h.hyp151.isElemAbelian L ≤
      ⁅Mbar D.M V₀ V h.hyp151.isElemAbelian, Mbar D.M V₀ V h.hyp151.isElemAbelian⁆) :
    s16h_CondU D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  obtain ⟨X, hXd, hXn, hXe, hXB⟩ := s16h_normalClosure_data (Mb := Mbar D.M V₀ V hV)
    (Lb := lBar V₀ V hV L) (B := lBar V₀ V hV L) le_rfl hLe
    (fun b hb l hl => congrArg Subtype.val (hLe.1.is_comm.comm ⟨b, hb⟩ ⟨l, hl⟩)) hd
    (fun q hq q' hq' hne => (s16h_conj_comm_inf_of_conc hW hq hq' hne).1)
  intro x hx w hw hw0
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  have hLx : conjSubgroup L x ≤ D.M := s16h_uelem_conjSubgroup_le_of_mem h.hyp151.le hx
  obtain ⟨q, hq, hbx⟩ := s16h_uelem_bar_conj h.hyp151.hyp125 L hx
  have hle : barSub V₀ V hV (conjSubgroup L x) ≤
      X ⊓ barSub V₀ V hV (F11.CElt D.M V₀ w) :=
    le_inf (hbx.le.trans (hXB q hq))
      (barSub_mono V₀ V hV (s16h_le_celt_of_mem_preTil_fixV hV hMs hLx hw))
  have h1 := CFSG.SectionRank.pRank_mono hp.one_lt hle
  rw [s16h_uelem_pRank_bar h.hyp151.hyp125 L hx p] at h1
  exact s16h_uniqueMax_cent_of_bar_pRank D hSig h61 h63 h77 h869 h111 h112 hThin hCyc h127 hσ
    h.hyp16 hp hp2 (hXd.trans (Subgroup.commutator_le_self _)) hXn hXe hXd hwV hw0 (by omega)

theorem s16h_condU2_of_central_derived (D : Data G) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (h127 : R127 D)
    (hσ : D.sig = D.sig1) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian))}
    (hBL : B ≤ lBar V₀ V h.hyp151.isElemAbelian L) (hB1 : B ≠ ⊥) (hBe : IsElemAbelian p B)
    (hBc : ∀ b ∈ B, ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, b * l = l * b)
    (hBd : B ≤ ⁅Mbar D.M V₀ V h.hyp151.isElemAbelian, Mbar D.M V₀ V h.hyp151.isElemAbelian⁆) :
    s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  obtain ⟨X, hXd, hXn, hXe, hXB⟩ := s16h_normalClosure_data (Mb := Mbar D.M V₀ V hV)
    (Lb := lBar V₀ V hV L) hBL hBe hBc hBd
    (fun q hq q' hq' hne => (s16h_conj_comm_inf_of_conc hW hq hq' hne).1)
  have hBp : p ∣ Nat.card B := by
    have := Fact.mk hp
    exact (CFSG.Open.IsElemAbelian.isPGroup hBe).card_eq_or_dvd.resolve_left
      (mt Subgroup.card_eq_one.1 hB1)
  intro x hx y hy hne w hw hw0
  obtain ⟨hwx, hwy⟩ := Subgroup.mem_inf.1 hw
  have hwV : w ∈ V := preTil_le V₀ V hV _ hwx
  have hLx : conjSubgroup L x ≤ D.M := s16h_uelem_conjSubgroup_le_of_mem h.hyp151.le hx
  have hLy : conjSubgroup L y ≤ D.M := s16h_uelem_conjSubgroup_le_of_mem h.hyp151.le hy
  obtain ⟨qx, hqx, hx'⟩ := s16h_uelem_bar_conj h.hyp151.hyp125 L hx
  obtain ⟨qy, hqy, hy'⟩ := s16h_uelem_bar_conj h.hyp151.hyp125 L hy
  have hcx := barSub_mono V₀ V hV (s16h_le_celt_of_mem_preTil_fixV hV hMs hLx hwx)
  have hcy := barSub_mono V₀ V hV (s16h_le_celt_of_mem_preTil_fixV hV hMs hLy hwy)
  rw [hx'] at hcx hne
  rw [hy'] at hcy hne
  obtain ⟨hcomm, hinf⟩ := s16h_conj_comm_inf_of_conc hW hqx hqy hne
  have hBxL : B.map (MulAut.conj qx).toMonoidHom ≤
      (lBar V₀ V hV L).map (MulAut.conj qx).toMonoidHom := Subgroup.map_mono hBL
  have hByL : B.map (MulAut.conj qy).toMonoidHom ≤
      (lBar V₀ V hV L).map (MulAut.conj qy).toMonoidHom := Subgroup.map_mono hBL
  have hc' : ⁅B.map (MulAut.conj qx).toMonoidHom, B.map (MulAut.conj qy).toMonoidHom⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hBxL hByL).trans hcomm.le)
  have hi' : B.map (MulAut.conj qx).toMonoidHom ⊓ B.map (MulAut.conj qy).toMonoidHom = ⊥ :=
    le_bot_iff.1 ((inf_le_inf hBxL hByL).trans hinf.le)
  have hdx : p ∣ Nat.card ↥(B.map (MulAut.conj qx).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj qx).injective]
  have hdy : p ∣ Nat.card ↥(B.map (MulAut.conj qy).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj qy).injective]
  have h2 := s16h_two_le_pRank_sup hp hc' hi' hdx hdy
  have h1 := CFSG.SectionRank.pRank_mono hp.one_lt
    (sup_le (le_inf (hXB qx hqx) (hBxL.trans hcx)) (le_inf (hXB qy hqy) (hByL.trans hcy)))
  exact s16h_uniqueMax_cent_of_bar_pRank D hSig h61 h63 h77 h869 h111 h112 hThin hCyc h127 hσ
    h.hyp16 hp hp2 (hXd.trans (Subgroup.commutator_le_self _)) hXn hXe hXd hwV hw0 (by omega)

theorem s16h_condU_of_noncyclic (D : Data G) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    {p : ℕ} (hp : p.Prime)
    (hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup p P → ¬ IsCyclic ↥P →
      P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hr : 2 ≤ CFSG.Open.pRank p (lBar V₀ V h.hyp151.isElemAbelian L)) :
    s16h_CondU D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨P, hPL, hPp, hPc⟩ := s16c34_exists_noncyclic_of_lBar hV hp hr
  intro x hx w hw hw0
  have hwV : w ∈ V := preTil_le V₀ V hV _ hw
  obtain ⟨hPx, hPxp, hPxc⟩ := s16h_uelem_conj_noncyclic hPL hPp hPc x
  have hLx : conjSubgroup L x ≤ D.M := s16h_uelem_conjSubgroup_le_of_mem h.hyp151.le hx
  exact hgood w hwV hw0 _ hPxp hPxc (hPx.trans (s16h_le_celt_of_mem_preTil_fixV hV hMs hLx hw))

theorem s16h_condU2_of_noncyclic (D : Data G) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    {p : ℕ} (hp : p.Prime)
    (hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup p P → ¬ IsCyclic ↥P →
      P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hrk : ∀ x ∈ D.M, ∀ y ∈ D.M,
      barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x) ≠
        barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L y) →
      2 ≤ CFSG.Open.pRank p (barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x) ⊔
        barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L y))) :
    s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  intro x hx y hy hne w hw hw0
  obtain ⟨hwx, hwy⟩ := Subgroup.mem_inf.1 hw
  have hwV : w ∈ V := preTil_le V₀ V hV _ hwx
  have hLx : conjSubgroup L x ≤ D.M := s16h_uelem_conjSubgroup_le_of_mem h.hyp151.le hx
  have hLy : conjSubgroup L y ≤ D.M := s16h_uelem_conjSubgroup_le_of_mem h.hyp151.le hy
  have hsup := s16h_uelem_barSub_sup V₀ V hV (hLx.trans hMs) (hLy.trans hMs)
  obtain ⟨P, hPL, hPp, hPc⟩ := s16c34_exists_noncyclic_of_lBar hV hp
    (L := conjSubgroup L x ⊔ conjSubgroup L y) (by
      unfold lBar
      rw [hsup]
      exact hrk x hx y hy hne)
  have hw' : w ∈ preTil V₀ V hV
      (fixV (barSub V₀ V hV (conjSubgroup L x ⊔ conjSubgroup L y))) := by
    rw [hsup]
    rw [mem_preTil_iff_of_mem V₀ V hV _ hwV] at hwx hwy ⊢
    exact s16h_uelem_mem_fixV_sup hwx hwy
  exact hgood w hwV hw0 P hPp hPc
    (hPL.trans (s16h_le_celt_of_mem_preTil_fixV hV hMs (sup_le hLx hLy) hw'))

theorem s16h_condU2_of_dvd (D : Data G) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (lBar V₀ V h.hyp151.isElemAbelian L))
    (hgood : ∀ w ∈ V, w ∉ V₀ → ∀ P : Subgroup G, IsPGroup p P → ¬ IsCyclic ↥P →
      P ≤ F11.CElt D.M V₀ w → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian := by
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  refine s16h_condU2_of_noncyclic D h hp hgood fun x hx y hy hne => ?_
  obtain ⟨qx, hqx, hx'⟩ := s16h_uelem_bar_conj h.hyp151.hyp125 L hx
  obtain ⟨qy, hqy, hy'⟩ := s16h_uelem_bar_conj h.hyp151.hyp125 L hy
  rw [hx', hy'] at hne ⊢
  obtain ⟨hcomm, hinf⟩ := s16h_conj_comm_inf_of_conc hW hqx hqy hne
  refine s16h_two_le_pRank_sup hp hcomm hinf ?_ ?_ <;>
    rwa [Subgroup.card_map_of_injective (MulAut.conj _).injective]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
