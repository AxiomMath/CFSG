module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_uniqueMax_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {E X : Subgroup G} (hE : IsPGroup p E) (hEc : ¬ IsCyclic ↥E) (hEX : E ≤ X)
    (hXM : X ≤ D.M) : UniqueMax D.M X :=
  ElevenFourteen.uniqueMax_of_le D.maxLocal (h61 p hp E (hEX.trans hXM) hE hEc) hEX hXM

theorem s16c34_card_v0_le_four (D : Data G) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    Nat.card V₀ ≤ 4 := by
  have hcard : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub h.hyp125.pairFacts.elemAbelian₀.isPGroup
  rw [hcard]
  calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h.small
    _ = 4 := by norm_num

private theorem s16c34_not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    ¬ p ∣ 2 ^ n := fun hdvd =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem s16c34_uniqueMax_cent_of_cElt (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G}
    (hPp : IsPGroup p P) (hPc : ¬ IsCyclic ↥P) {w : G} (hwV : w ∈ V) (hwV₀ : w ∉ V₀)
    (hP : P ≤ F11.CElt D.M V₀ w) : UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hpp := D.sig_prime p hp
  obtain ⟨n, -, hn⟩ := r113_holds D V₀ V (Hyp125.hyp11 h127 h.hyp125)
    (s16c34_card_v0_le_four D h) w hwV hwV₀
  have hindex : ¬ p ∣ (D.M ⊓ centralizer ({w} : Set G)).relIndex (F11.CElt D.M V₀ w) := by
    rw [hn]
    exact s16c34_not_dvd_two_pow hpp.1 hpp.2 n
  obtain ⟨B, hB, hBp, hBc⟩ :=
    c23_exists_noncyclic_le_of_not_dvd_relIndex hpp.1 hP hindex hPp hPc
  exact s16c34_uniqueMax_of_noncyclic D h61 hp hBp hBc hB inf_le_left

theorem s16c34_uniqueMax_cent_of_mem_v0 (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) (h3 : 3 ≤ CFSG.Open.pRank p D.M) {w : G}
    (hw : w ∈ V₀) (hw1 : w ≠ 1) : UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hpp := D.sig_prime p hp
  have hp3 : 3 ≤ p := by
    have h2 := hpp.1.two_le
    have hne := hpp.2
    omega
  obtain ⟨E, hEM, hEea, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := p) (M := D.M) (k := 3) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h3)
  have hMn : D.M ≤ normalizer (V₀ : Set G) := h.hyp125.pairFacts.le_normalizer₀
  have hS : ((V₀ : Set G) \ {1}).ncard ≤ 3 := by
    have h4 : Nat.card V₀ ≤ 4 := s16c34_card_v0_le_four D h
    have h5 : (V₀ : Set G).ncard = Nat.card V₀ := (Nat.card_coe_set_eq (V₀ : Set G)).symm
    have h6 : ((V₀ : Set G) \ {1}).ncard = (V₀ : Set G).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem V₀.one_mem
    omega
  have hSw : ∀ e ∈ E, e * w * e⁻¹ ∈ (V₀ : Set G) \ {1} := by
    intro e he
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMn (hEM he)) w).mp hw, ?_⟩
    intro h1
    apply hw1
    have h2 : e * w * e⁻¹ = 1 := h1
    simpa using h2
  have hnc := c23_not_isCyclic_inf_centralizer hpp.1 hp3 hEea hEcard hS hSw
  exact s16c34_uniqueMax_of_noncyclic D h61 hp
    (IsElemAbelian.isPGroup (IsElemAbelian.mono hEea inf_le_left)) hnc
    (inf_le_inf_right _ hEM) inf_le_left

theorem s16c34_wSub_le_preTil_fixV {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {L' : Subgroup G}
    {K : Subgroup (MulAut (Vtil V₀ V hV))} (hK : commSub (wTil V₀ V hV L') K = ⊥) :
    wSub V₀ V hV L' ≤ preTil V₀ V hV (fixV K) := by
  intro w hw
  unfold wSub at hw
  obtain ⟨y, hyval, hyW⟩ := (mem_preTil V₀ V hV (wTil V₀ V hV L')).1 hw
  exact (mem_preTil V₀ V hV (fixV K)).2 ⟨y, hyval, commSub_eq_bot_iff.mp hK hyW⟩

theorem s16c34_wSub_conj_le_preTil_fixV (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {m c : G} (hm : m ∈ D.M) (hc : c ∈ D.M)
    (hne : barSub V₀ V h.isElemAbelian (conjSubgroup L c) ≠
      barSub V₀ V h.isElemAbelian (conjSubgroup L m)) :
    wSub V₀ V h.isElemAbelian (conjSubgroup L m) ≤
      preTil V₀ V h.isElemAbelian (fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L c))) := by
  have hV := h.isElemAbelian
  have hnn : c * m⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
    hne ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV hm hc).1 hmem)
  exact s16c34_wSub_le_preTil_fixV hV (s15_Kbar_commute_conj h hm hc hnn).2

theorem s16c34_v1Sub_le_preTil_fixV (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {c : G} (hc : c ∈ D.M) :
    v1Sub D.M V₀ V h.isElemAbelian L ≤
      preTil V₀ V h.isElemAbelian (fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L c))) := by
  have hV := h.isElemAbelian
  intro w hw
  have hwV : w ∈ V := s15_Infra_v1Sub_le h.hyp125 hV hw
  rw [mem_preTil_iff_of_mem V₀ V hV _ hwV]
  exact s15_Core_imgTil_v1Sub_le_fixV h hc
    ((mem_imgTil V₀ V hV _ _).2 ⟨IntMod.mk hV ⟨w, hwV⟩, hw, rfl⟩)

private theorem s16c34_conjSubgroup_mono_v {A B : Subgroup G} (h : A ≤ B) (x : G) :
    conjSubgroup A x ≤ conjSubgroup B x := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy ⊢
  exact h hy

private theorem s16c34_conjSubgroup_le_of_mem_v {A M : Subgroup G} (hA : A ≤ M) {x : G}
    (hx : x ∈ M) : conjSubgroup A x ≤ M := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hx) (hA hy)) hx
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  rwa [e] at h1

private theorem s16c34_isPGroup_conj_v {p : ℕ} {P : Subgroup G} (hP : IsPGroup p P) (x : G) :
    IsPGroup p (conjSubgroup P x) :=
  hP.of_equiv (Subgroup.equivMapOfInjective P (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective)

private theorem s16c34_not_isCyclic_conj_v {P : Subgroup G} (hP : ¬ IsCyclic ↥P) (x : G) :
    ¬ IsCyclic ↥(conjSubgroup P x) := fun hc =>
  hP ((Subgroup.equivMapOfInjective P (MulAut.conj x⁻¹).toMonoidHom
    (MulAut.conj x⁻¹).injective).isCyclic.2 hc)

theorem s16c34_uniqueMax_of_mem_preTil (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) {p : ℕ} (hp : p ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M) {P : Subgroup G} (hPL : P ≤ L) (hPp : IsPGroup p P)
    (hPc : ¬ IsCyclic ↥P) {x : G} (hx : x ∈ D.M) {w : G}
    (hw : w ∈ preTil V₀ V h.hyp151.isElemAbelian
      (fixV (barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x)))) (hw1 : w ≠ 1) :
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  by_cases hw0 : w ∈ V₀
  · exact s16c34_uniqueMax_cent_of_mem_v0 D h61 h.hyp16 hp h3 hw0 hw1
  · have hwV : w ∈ V := preTil_le V₀ V hV _ hw
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀
    have hLx : conjSubgroup L x ≤ D.M := s16c34_conjSubgroup_le_of_mem_v h.hyp151.le hx
    have hLxY := le_preBarSub_barSub (M := D.M) (V₀ := V₀) hV hLx (hLx.trans hMs)
    obtain ⟨y, hyval, hyfix⟩ := (mem_preTil V₀ V hV _).1 hw
    have hY := s16c34_preBarSub_le_cElt (M := D.M) hV hyfix
    rw [hyval] at hY
    exact s16c34_uniqueMax_cent_of_cElt D h61 h127 h.hyp16 hp (s16c34_isPGroup_conj_v hPp x)
      (s16c34_not_isCyclic_conj_v hPc x) hwV hw0
      ((s16c34_conjSubgroup_mono_v hPL x).trans (hLxY.trans hY))

theorem s16c34_unique₁_of_pRank (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) {p : ℕ} (hp : p ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (h2 : 2 ≤ CFSG.Open.pRank p (lBar V₀ V h.hyp151.isElemAbelian L))
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨P, hPL, hPp, hPc⟩ := s16c34_exists_noncyclic_of_lBar hV (D.sig_prime p hp).1 h2
  obtain ⟨x, hx, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 hs
  have hle : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤
      preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) :=
    sup_le (s16c34_wSub_le_preTil_fixV hV (h.hyp151.commute x hx hxn).2)
      (s16c34_v1Sub_le_preTil_fixV D h.hyp151 hx)
  intro w hw hw1
  exact s16c34_uniqueMax_of_mem_preTil D h61 h127 h hp h3 hPL hPp hPc hx (hle hw) hw1

theorem s16c34_unique₂_of_pRank (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) {p : ℕ} (hp : p ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (h2 : 2 ≤ CFSG.Open.pRank p (lBar V₀ V h.hyp151.isElemAbelian L)) :
    ∀ x ∈ D.M, ∀ y ∈ D.M,
      ∀ w ∈ v1Sub D.M V₀ V h.hyp151.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨P, hPL, hPp, hPc⟩ := s16c34_exists_noncyclic_of_lBar hV (D.sig_prime p hp).1 h2
  intro x hx y _ w hw hw1
  have hle : v1Sub D.M V₀ V hV L ⊔ (⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
      X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y}, X) ≤
      preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L x))) := by
    refine sup_le (s16c34_v1Sub_le_preTil_fixV D h.hyp151 hx) (iSup₂_le fun X hX => ?_)
    obtain ⟨⟨m, hm, rfl⟩, hXx, -⟩ := hX
    have hne : barSub V₀ V hV (conjSubgroup L x) ≠ barSub V₀ V hV (conjSubgroup L m) := by
      intro heq
      apply hXx
      rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm),
        ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx)]
      unfold wSub wTil
      rw [heq]
    have hW := s16c34_wSub_conj_le_preTil_fixV D h.hyp151 hm hx hne
    rwa [s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm)] at hW
  exact s16c34_uniqueMax_of_mem_preTil D h61 h127 h hp h3 hPL hPp hPc hx (hle hw) hw1

private theorem s16c34_isPGroup_two_sub_v {V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hUV : U ≤ V) : IsPGroup 2 U := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hV.2 g.1 (hUV g.2)

private theorem s16c34_wConj_le_v (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V h.isElemAbelian L) : X ≤ V := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L h.isElemAbelian (hMs hm)]
  exact preTil_le V₀ V h.isElemAbelian _

theorem s16c34_hyp154_of_fields (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (h1 : ∀ w ∈ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (h2 : ∀ x ∈ D.M, ∀ y ∈ D.M,
      ∀ w ∈ v1Sub D.M V₀ V h.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hs : 1 < s15 D.M V₀ V h.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.isElemAbelian L < gamma15 D.M V₀ V h.isElemAbelian L - 1) :
    Hyp154 D V₀ V L := by
  have hV := h.isElemAbelian
  refine ⟨h, h1, fun x hx y hy _ => h2 x hx y hy, ?_⟩
  intro g hg X hX Y hY hXY hne
  by_cases hs2 : s15 D.M V₀ V hV L = 2
  · exact ⟨hs2, hδ hs2⟩
  · exfalso
    have hcard : ({X, Y} : Set (Subgroup G)).ncard < (wConj D.M V₀ V hV L).ncard := by
      rw [Set.ncard_pair hXY, ncard_wConj D h hV]
      omega
    obtain ⟨Z, hZ, hZXY⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard
    obtain ⟨c, hc, rfl⟩ := hZ
    have hZX : X ≠ conjSubgroup (wSub V₀ V hV L) c := fun e => hZXY (Or.inl e.symm)
    have hZY : Y ≠ conjSubgroup (wSub V₀ V hV L) c := fun e => hZXY (Or.inr e.symm)
    have hV1 : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
    have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
    have hX' : X ≤ ⨆ X' ∈ {X' | X' ∈ wConj D.M V₀ V hV L ∧
        X' ≠ conjSubgroup (wSub V₀ V hV L) c ∧ X' ≠ conjSubgroup (wSub V₀ V hV L) c}, X' := by
      have hmem : X ∈ {X' | X' ∈ wConj D.M V₀ V hV L ∧
          X' ≠ conjSubgroup (wSub V₀ V hV L) c ∧ X' ≠ conjSubgroup (wSub V₀ V hV L) c} :=
        ⟨hX, hZX, hZX⟩
      exact le_iSup₂_of_le X hmem le_rfl
    have hY' : Y ≤ ⨆ X' ∈ {X' | X' ∈ wConj D.M V₀ V hV L ∧
        X' ≠ conjSubgroup (wSub V₀ V hV L) c ∧ X' ≠ conjSubgroup (wSub V₀ V hV L) c}, X' := by
      have hmem : Y ∈ {X' | X' ∈ wConj D.M V₀ V hV L ∧
          X' ≠ conjSubgroup (wSub V₀ V hV L) c ∧ X' ≠ conjSubgroup (wSub V₀ V hV L) c} :=
        ⟨hY, hZY, hZY⟩
      exact le_iSup₂_of_le Y hmem le_rfl
    have hU₁ : ∀ w ∈ X ⊔ Y ⊔ v1Sub D.M V₀ V hV L, w ≠ 1 →
        UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
      intro w hw hw1
      refine h2 c hc c hc w ?_ hw1
      exact (sup_le (sup_le (hX'.trans le_sup_right) (hY'.trans le_sup_right)) le_sup_left) hw
    exact hne (inf_conjSubgroup_eq_bot_of_uniqueMax D.maxLocal
      (s16c34_isPGroup_two_sub_v hV
        (sup_le (sup_le (s16c34_wConj_le_v D h hX) (s16c34_wConj_le_v D h hY)) hV1))
      (s16c34_isPGroup_two_sub_v hV (sup_le hWV hV1)) hU₁ h1 hg)

theorem s16c34_hyp154_of_pRank (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) {p : ℕ} (hp : p ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank p D.M)
    (h2 : 2 ≤ CFSG.Open.pRank p (lBar V₀ V h.hyp151.isElemAbelian L))
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L < gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1) :
    Hyp154 D V₀ V L :=
  s16c34_hyp154_of_fields D h.hyp151 (s16c34_unique₁_of_pRank D h61 h127 h hp h3 h2 hs)
    (s16c34_unique₂_of_pRank D h61 h127 h hp h3 h2) hs hδ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
