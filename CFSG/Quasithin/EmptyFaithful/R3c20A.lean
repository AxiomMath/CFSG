module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.SBc6Blocks
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3CompBasic
public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.Quasithin.EmptyFaithful.SBc6Ctx

public section

namespace CFSG.Quasithin

namespace R3c20

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.A5.G3 (isChi0Block_conj conjJoin_le_of_le le_normalizer_conjJoin')
open scoped commutatorElement
open CFSG.Quasithin.SBc6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_twoResidual_of_isShort2 {H L : Subgroup G} (hL : IsShort2 L) (hLH : L ≤ H) :
    L ≤ twoResidual H := by
  intro x hx
  rw [mem_twoResidual_iff]
  intro N hNH hHN h2N
  have hnorm : (N.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hLH.trans hHN)
  have hp : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      obtain ⟨k, hk⟩ := h2N (l : G) (hLH l.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have htop := hL.1 (N.subgroupOf L) hp
  have : (⟨x, hx⟩ : ↥L) ∈ N.subgroupOf L := by rw [htop]; exact Subgroup.mem_top _
  exact this

theorem commutator_self_ne_bot_of_isChi0Block {I L : Subgroup G}
    (hL : IsChi0Block I L) : ⁅L, L⁆ ≠ ⊥ := by
  intro hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 3 ∣ Nat.card L :=
    C1GN.three_dvd_card_of_isChiBlock (C1GN.isChiBlock_of_isChi0Block hL.1 hL)
  have hLchar : CharTwo L := hL.1.1.2.1
  have hcent : L ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h1 : ⁅y, x⁆ ∈ ⁅L, L⁆ := Subgroup.commutator_mem_commutator (pCoreOf_le 2 L hy) hx
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hle : L ≤ pCoreOf 2 L := fun x hx => hLchar ⟨hx, hcent hx⟩
  have hp : IsPGroup 2 L := (pCoreOf_isPGroup 2 L).to_le hle
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h3
  have := Nat.prime_three.dvd_of_dvd_pow h3
  omega

omit [Finite G] in
theorem conjSub_eq_map (t : G) (B : Subgroup G) :
    B6.conjSub t B = B.map (MulAut.conj t).toMonoidHom := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨t⁻¹ * x * t, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy

theorem twoResidual_eq_conjJoin {H T L : Subgroup G} (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hL : IsChi0Block H L) (hH : H = conjJoin T L ⊔ T) : twoResidual H = conjJoin T L := by
  have hLH : L ≤ H := hL.1.2.1
  have hle : conjJoin T L ≤ H := conjJoin_le_of_le hTH hLH
  have hN : H ≤ Subgroup.normalizer (conjJoin T L : Set G) := by
    rw [hH]
    exact sup_le Subgroup.le_normalizer (le_normalizer_conjJoin' T L)
  refine le_antisymm (twoResidual_le_of_isTwoQuotient hle hN ?_) ?_
  · exact B6.isTwoQuotient_of_sup_eq hT hN (by rw [sup_comm]; exact hH.symm)
  · refine iSup_le fun s => ?_
    have hb : IsChi0Block H (L.map (MulAut.conj (s : G)).toMonoidHom) :=
      isChi0Block_conj hL (hTH s.2)
    exact le_twoResidual_of_isShort2 hb.1.1 hb.1.2.1

theorem conj_eq_or_eq_of_conjJoin {H T L : Subgroup G} (hch : CharTwo H) (hTH : T ≤ H)
    (hL : IsChi0Block H L) {t : G} (htT : t ∈ T)
    (hjoin : conjJoin T L = L ⊔ L.map (MulAut.conj t).toMonoidHom) :
    ∀ s ∈ T, L.map (MulAut.conj s).toMonoidHom = L ∨
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
  intro s hs
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hBb : IsChi0Block H (L.map (MulAut.conj s).toMonoidHom) := isChi0Block_conj hL (hTH hs)
  have hLt : IsChi0Block H (L.map (MulAut.conj t).toMonoidHom) := isChi0Block_conj hL (hTH htT)
  have c1 : ⁅L.map (MulAut.conj s).toMonoidHom, L⁆ = ⊥ :=
    distinctBlocksCommuteStatement H _ L hch hBb.1 hL.1 h1
  have c2 : ⁅L.map (MulAut.conj s).toMonoidHom, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥ :=
    distinctBlocksCommuteStatement H _ _ hch hBb.1 hLt.1 h2
  have hBj : L.map (MulAut.conj s).toMonoidHom ≤ conjJoin T L :=
    le_iSup (fun s : T => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨s, hs⟩
  rw [hjoin] at hBj
  have hcent : L ⊔ L.map (MulAut.conj t).toMonoidHom ≤
      Subgroup.centralizer ((L.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact c1)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact c2)
  exact commutator_self_ne_bot_of_isChi0Block hBb
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hBj.trans hcent))

theorem c126Third_of_blockData {H T L : Subgroup G} (hchar : CharTwo H) (hTH : T ≤ H)
    (hT2 : IsPGroup 2 T) (hL : IsChi0Block H L) (hLJ : ⁅L, thompsonJ T⁆ = L)
    (hHj : H = conjJoin T L ⊔ T)
    (hcase : conjJoin T L = L ∨ ∃ t ∈ T, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
      conjJoin T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) :
    ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
      (∀ i, IsChi0Block H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
      (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
      (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
      (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j) := by
  rcases hcase with hcj | ⟨t, ht, hne, hjoin, hc⟩
  · have hnorm : ∀ s ∈ T, L.map (MulAut.conj s).toMonoidHom = L := by
      intro s hs
      have hle : L.map (MulAut.conj s).toMonoidHom ≤ L := by
        have h1 : L.map (MulAut.conj s).toMonoidHom ≤ conjJoin T L :=
          le_iSup (fun s : T => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨s, hs⟩
        rwa [hcj] at h1
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
    refine ⟨1, fun _ => L, le_rfl, fun _ => ⟨hL, hLJ⟩, fun i j hij =>
      absurd (Subsingleton.elim i j) hij, ?_, ?_, ?_⟩
    · rw [twoResidual_eq_conjJoin hT2 hTH hL hHj, hcj]
      simp
    · intro s hs i
      exact ⟨i, by rw [conjSub_eq_map, hnorm s hs]⟩
    · intro i j
      exact ⟨1, T.one_mem, by rw [conjSub_eq_map, A5.G3.map_conj_one]⟩
  · have hLt : IsChi0Block H (L.map (MulAut.conj t).toMonoidHom) := isChi0Block_conj hL (hTH ht)
    have hJt : (thompsonJ T).map (MulAut.conj t).toMonoidHom = thompsonJ T :=
      GammaExtra.map_conj_eq_self_of_mem_normalizer
        (GammaExtra.normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer ht))
    have hLJt : ⁅L.map (MulAut.conj t).toMonoidHom, thompsonJ T⁆ =
        L.map (MulAut.conj t).toMonoidHom := by
      conv_lhs => rw [← hJt]
      rw [← Subgroup.map_commutator, hLJ]
    have horb := conj_eq_or_eq_of_conjJoin hchar hTH hL ht hjoin
    set Lt : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hLtdef
    let K : Fin 2 → Subgroup G := fun i => if i = 0 then L else Lt
    have hK0 : K 0 = L := by simp [K]
    have hK1 : K 1 = Lt := by simp [K]
    refine ⟨2, K, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Fin.forall_fin_two, hK0, hK1]
      exact ⟨⟨hL, hLJ⟩, ⟨hLt, hLJt⟩⟩
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · show ⁅K 0, K 1⁆ = ⊥
        rw [hK0, hK1]; exact hc
      · show ⁅K 1, K 0⁆ = ⊥
        rw [hK0, hK1, Subgroup.commutator_comm]; exact hc
      · exact absurd rfl hij
    · rw [twoResidual_eq_conjJoin hT2 hTH hL hHj, hjoin]
      refine le_antisymm (sup_le (le_iSup K 0 |>.trans' hK0.ge) (le_iSup K 1 |>.trans' hK1.ge))
        (iSup_le fun i => ?_)
      fin_cases i
      · show K 0 ≤ _
        rw [hK0]; exact le_sup_left
      · show K 1 ≤ _
        rw [hK1]; exact le_sup_right
    · intro s hs
      rw [Fin.forall_fin_two, hK0, hK1]
      refine ⟨?_, ?_⟩
      · rw [conjSub_eq_map]
        rcases horb s hs with h | h
        · exact ⟨0, by rw [h, hK0]⟩
        · exact ⟨1, by rw [h, hK1]⟩
      · rw [conjSub_eq_map, hLtdef, A5.G3.map_conj_map_conj]
        rcases horb (s * t) (T.mul_mem hs ht) with h | h
        · exact ⟨0, by rw [h, hK0]⟩
        · exact ⟨1, by rw [h, hK1]⟩
    · rw [Fin.forall_fin_two, Fin.forall_fin_two, Fin.forall_fin_two, hK0, hK1]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact ⟨1, T.one_mem, by rw [conjSub_eq_map, A5.G3.map_conj_one]⟩
      · exact ⟨t, ht, by rw [conjSub_eq_map]⟩
      · refine ⟨t⁻¹, T.inv_mem ht, ?_⟩
        rw [conjSub_eq_map, hLtdef, A5.G3.map_conj_map_conj, inv_mul_cancel, A5.G3.map_conj_one]
      · exact ⟨1, T.one_mem, by rw [conjSub_eq_map, A5.G3.map_conj_one]⟩

theorem c126Third_of_minParabolicBlocks (hMB : MinParabolicBlocks) {H T M : Subgroup G}
    (hmin : MinParabolic H T M) (hchar : CharTwo H) (hSQ : IsSQTKTC H)
    (hno : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ T → (R.subgroupOf T).Characteristic →
      ¬ H ≤ Subgroup.normalizer (R : Set G)) :
    ∃ (r : ℕ) (K : Fin r → Subgroup G), 1 ≤ r ∧
      (∀ i, IsChi0Block H (K i) ∧ ⁅K i, thompsonJ T⁆ = K i) ∧
      (∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) ∧ twoResidual H = ⨆ i, K i ∧
      (∀ t ∈ T, ∀ i, ∃ j, B6.conjSub t (K i) = K j) ∧
      (∀ i j, ∃ t ∈ T, B6.conjSub t (K i) = K j) := by
  have hSyl := hmin.isSylow
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥H :=
    ⟨fun p hp hp2 => by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hSQ.2 p hp hp2, hSQ.1⟩
  obtain ⟨L, hL, hLJ, hHj, hcase⟩ := hMB G T H
    ⟨hSyl, hchar, minParabolic_exists_iff.mp ⟨M, hmin⟩, hsqtk, hno⟩
  exact c126Third_of_blockData hchar hSyl.1 hSyl.2.1 hL hLJ hHj hcase

omit [Finite G] in
theorem not_le_of_blocks_trans {I S Iz : Subgroup G} {r : ℕ} {K : Fin r → Subgroup G}
    (hSIz : S ≤ Iz) (hI : ¬ I ≤ Iz) (hres : I = S ⊔ ⨆ i, K i)
    (htrans : ∀ i j, ∃ t ∈ S, B6.conjSub t (K i) = K j) : ∀ i, ¬ K i ≤ Iz := by
  intro i hi
  have hall : ∀ j, K j ≤ Iz := by
    intro j
    obtain ⟨t, ht, htj⟩ := htrans i j
    have htIz : t ∈ Iz := hSIz ht
    rw [← htj]
    intro x hx
    rw [B6.mem_conjSub] at hx
    have h4 := Iz.mul_mem (Iz.mul_mem htIz (hi hx)) (Iz.inv_mem htIz)
    simpa [mul_assoc] using h4
  exact hI (by rw [hres]; exact sup_le hSIz (iSup_le hall))

theorem input1469C126_of_mpb (hMB : MinParabolicBlocks) : Input1469C126 := by
  intro G _ _ I S Iz hSQ hchar hmin hcgs
  have hI : ¬ I ≤ Iz := not_le_of_gt hmin.maximal.1
  have hno : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ S → (R.subgroupOf S).Characteristic →
      ¬ I ≤ Subgroup.normalizer (R : Set G) := by
    intro R hR0 hRS hRch hRI
    have hle : I ⊓ Subgroup.normalizer (R : Set G) ≤ cgsIn I S := by
      unfold cgsIn
      exact le_iSup_of_le R (le_iSup_of_le hRS (le_iSup_of_le hR0 (le_iSup_of_le hRch le_rfl)))
    exact hI (le_trans (fun x hx => hle ⟨hx, hRI hx⟩) hcgs)
  obtain ⟨r, K, hr, hK, hcomm, hres, hmap, htrans⟩ :=
    c126Third_of_minParabolicBlocks hMB hmin hchar hSQ hno
  have hres' : I = S ⊔ ⨆ i, K i := by
    have := MinParabolic.eq_twoResidual_sup hmin
    rwa [hres, sup_comm] at this
  have hne : ∀ i j : Fin r, i ≠ j → K i ≠ K j := fun i j hij hKij =>
    commutator_self_ne_bot_of_isChi0Block (hK i).1 (by
      have := hcomm i j hij
      rwa [← hKij] at this)
  have hr2 : r ≤ 2 := by
    by_contra hr3
    have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2 :=
      hSQ.2 3 Nat.prime_three (by norm_num)
    let a : Fin r := ⟨0, by omega⟩
    let b : Fin r := ⟨1, by omega⟩
    let c : Fin r := ⟨2, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
    have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
    have h3 : ∀ i, 3 ∣ Nat.card (K i) := fun i =>
      C1GN.three_dvd_card_of_isChiBlock (C1GN.isChiBlock_of_isChi0Block (hK i).1.1 (hK i).1)
    exact L238.three_blocks_false_cat (X := I) hX3 (hK a).1.1.2.1 (hK b).1.1.2.1
      (hK c).1.1.2.1 ⟨(hK a).1.1.1.2.1, (hK b).1.1.1.2.1, (hK c).1.1.1.2.1⟩
      ⟨h3 a, h3 b, h3 c⟩ (hne a b hab) (hne a c hac) (hne b c hbc)
      ⟨hcomm a b hab, hcomm a c hac, hcomm b c hbc⟩
  exact ⟨r, K, ⟨hr, hr2, fun i => (hK i).1, hcomm, hres', htrans, hmap⟩,
    not_le_of_blocks_trans hmin.le hI hres' htrans⟩

theorem input30Blocks_of_mpb (hMB : MinParabolicBlocks) : Input30Blocks := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hn hBorel
  have hMP := minParabolic_of_ctx c hn hBorel
  obtain ⟨n, hn1, hPSL⟩ := hn
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := c25.facts.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hsyl.2.1
  obtain ⟨hLcJ, -, -, -, hStarQ, hLQ⟩ := c25.conc
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLcJ
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hI0 : pCoreOf 2 I ≠ ⊥ := c25.ctx.inH.1.2
  have hqtfe := hh.hyp.qtfe
  have hSQ : IsSQTKTC I :=
    ⟨kGroup_of_pCoreOf_ne_bot hqtfe.qtke hqtfe.simple hqtfe.nonabelian hI0,
      stronglyQuasithin_of_pCoreOf_ne_bot hqtfe.qtke hI0⟩
  obtain ⟨r, K, hr, hK, hcomm, hres, -, htrans⟩ :=
    c126Third_of_minParabolicBlocks hMB hMP c25.ctx.charTwo hSQ
      (fun R hR0 hRS hRch => c.c29.no_char R hRS hR0 hRch)
  have hsup : (⨆ i, K i) = L := hres.symm.trans (twoResidual_eq_of_ctx c)
  have hKL : ∀ i, K i ≤ L := fun i => hsup ▸ le_iSup K i
  have hKn : ∀ i, L ≤ Subgroup.normalizer (K i : Set G) := fun i => by
    rw [← hsup]
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm j i hij)).trans
        (Subgroup.centralizer_le_normalizer _)
  obtain ⟨ψ, hψsurj, hψker⟩ := exists_cover_of_ctx c
  have hsimple : IsSimpleGroup ↥(Star153 T I L) := isSimpleGroup_of_psl hn1 hPSL
  have hnoncomm : ¬ ∀ a b : ↥(Star153 T I L), a * b = b * a := fun h =>
    not_isQuasisimple_of_comm h hStarQ
  have hmap : ∀ i, ((K i).subgroupOf L).map ψ = ⊥ ∨ ((K i).subgroupOf L).map ψ = ⊤ := fun i => by
    have h1 : ((K i).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hKL i)).mpr (hKn i)
    have h2 : (((K i).subgroupOf L).map ψ).Normal := Subgroup.Normal.map h1 ψ hψsurj
    exact hsimple.eq_bot_or_eq_top_of_normal _
  have hbot : ∀ i, ((K i).subgroupOf L).map ψ = ⊥ ↔
      K i ≤ Subgroup.centralizer (UI153 T I : Set G) := fun i => by
    constructor
    · intro h x hx
      have hmem : ψ ⟨x, hKL i hx⟩ ∈ ((K i).subgroupOf L).map ψ :=
        Subgroup.mem_map_of_mem ψ hx
      rw [h, Subgroup.mem_bot] at hmem
      exact (hψker _).1 hmem
    · intro h
      rw [eq_bot_iff]
      rintro y ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot]
      exact (hψker x).2 (h hx)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ¬ K i₀ ≤ Subgroup.centralizer (UI153 T I : Set G) := by
    by_contra hall
    push Not at hall
    have hLZ : L ≤ Subgroup.centralizer (UI153 T I : Set G) := by
      rw [← hsup]
      exact iSup_le hall
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥(Star153 T I L))
    obtain ⟨x, rfl⟩ := hψsurj a
    exact ha ((hψker x).2 (hLZ x.2))
  have hall : ∀ j, ¬ K j ≤ Subgroup.centralizer (UI153 T I : Set G) := by
    intro j hj
    obtain ⟨s, hs, hsj⟩ := htrans i₀ j
    apply hi₀
    intro x hx
    have h1 : s * x * s⁻¹ ∈ K j := by
      rw [← hsj, B6.mem_conjSub]
      simpa [mul_assoc] using hx
    have h2 := hj h1
    rw [Subgroup.mem_centralizer_iff] at h2 ⊢
    intro u hu
    have hu' : s * u * s⁻¹ ∈ UI153 T I := (Subgroup.mem_normalizer_iff.mp (hIU (hSI hs)) u).mp hu
    have h3 := h2 _ hu'
    have h4 : s * (u * x) * s⁻¹ = s * (x * u) * s⁻¹ := by
      calc s * (u * x) * s⁻¹ = (s * u * s⁻¹) * (s * x * s⁻¹) := by group
        _ = (s * x * s⁻¹) * (s * u * s⁻¹) := h3
        _ = s * (x * u) * s⁻¹ := by group
    simpa using h4
  have hmapTop : ∀ j, ((K j).subgroupOf L).map ψ = ⊤ := fun j =>
    (hmap j).resolve_left fun h => hall j ((hbot j).1 h)
  have hsub : ∀ i j : Fin r, i = j := by
    intro i j
    by_contra hij
    apply hnoncomm
    intro a b
    have ha : a ∈ ((K i).subgroupOf L).map ψ := hmapTop i ▸ Subgroup.mem_top a
    have hb : b ∈ ((K j).subgroupOf L).map ψ := hmapTop j ▸ Subgroup.mem_top b
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hxy : (y : G) * (x : G) = (x : G) * (y : G) :=
      Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i j hij)) hx) (y : G) hy
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext hxy.symm)
  have hLK : L = K i₀ := by
    refine le_antisymm ?_ (hKL i₀)
    rw [← hsup]
    exact iSup_le fun j => by rw [hsub j i₀]
  have hchi : IsChi0Block I L := hLK ▸ (hK i₀).1
  refine ⟨hchi.1, ?_⟩
  rcases hchi.2 with hlin | hA3 | hA5
  · exact Or.inl hlin
  · exfalso
    obtain ⟨α, hαs, hαk, -⟩ := hA3
    have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ α.ker) :=
      QuotientGroup.quotientMulEquivOfEq hαk.symm
    have e2 := QuotientGroup.quotientKerEquivOfSurjective α hαs
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin 3)) :=
      Nat.card_congr (e1.trans e2).toEquiv
    have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    exact not_isQuasisimple_of_comm (comm_of_card_three (hc.trans h3)) hLQ
  · exact Or.inr hA5

end R3c20

end CFSG.Quasithin
