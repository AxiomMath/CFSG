module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase11
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Arith

private theorem s16e_card_GL_two_dvd {d : ℕ} (hd : d ≤ 4) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases d <;> simp [Fin.prod_univ_succ]

private theorem s16e_not_cube_dvd_20160 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ 20160 := by
  intro h
  have hle : p ^ 3 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hp27 : p ≤ 27 := by
    by_contra hc
    push Not at hc
    have : 28 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  interval_cases p <;> first | exact hp2 rfl | (norm_num at h; done) | (norm_num at hp; done)

private theorem s16e_not_sq_dvd_168 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 168 := by
  intro h
  have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have hp13 : p ≤ 13 := by nlinarith
  interval_cases p <;> first | exact hp2 rfl | (norm_num at h; done) | (norm_num at hp; done)

end Arith

section Generic

variable {T : Type*} [CommGroup T]

theorem s16e_card_eq_two_pow_rk_top [Finite T] (hT : ∀ v : T, v ^ 2 = 1) :
    Nat.card T = 2 ^ rk ↥(⊤ : Subgroup T) := by
  rw [← card_eq_two_pow hT ⊤, Subgroup.card_top]

theorem s16e_pRank_lt_three_of_rk_le_four [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {d : ℕ}
    (hd : d ≤ 4) (hcard : Nat.card T = 2 ^ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut T)) : CFSG.Open.pRank p A < 3 := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEA, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
  have h1 : p ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hge
  have h2 : Nat.card E ∣ Nat.card A := Subgroup.card_dvd_of_le hEA
  have h3 : Nat.card A ∣ Nat.card (MulAut T) := Subgroup.card_subgroup_dvd_card A
  have h4 : Nat.card (MulAut T) ∣ Nat.card (GL (Fin d) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (fun a b => mul_comm a b) hT hcard
  exact s16e_not_cube_dvd_20160 hp hp2
    (h1.trans (h2.trans (h3.trans (h4.trans (s16e_card_GL_two_dvd hd)))))

theorem s16e_card_le_sq [Finite T] (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup (MulAut T)} (hEM : E ≤ M) (hEp : ∀ e ∈ E, e ^ p = 1) {a : ℕ}
    (hEcard : Nat.card E = p ^ a) : Nat.card E ≤ p ^ 2 := by
  have hA : ∀ e ∈ E, A.map (MulAut.conj e).toMonoidHom = A := fun e he =>
    s16n9b_two_normalizes_of_odd h (hEM he) (n := p) (hp.odd_of_ne_two hp2) (hEp e he)
  have hstW : E ≤ stabSub (commSub ⊤ A) := by
    intro e he
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← s15_Infra_commSub_top_map_conj A e, hA e he]
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  have hstW' : E ≤ stabSub ((commSub ⊤ A).map g.toMonoidHom) := by
    intro e he
    apply s16n9b_mem_stabSub_of_map_eq
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ e,
      s16n9b_two_normalizes_conj h (hEM he) (hA e he)]
  have hrk' : rk ↥((commSub ⊤ A).map g.toMonoidHom) = 3 := by
    rw [s16n9b_rk_map]
    exact hrk
  have h168 := s16n9b_card_mulAut_rank_three hT hrk
  have h168' := s16n9b_card_mulAut_rank_three hT hrk'
  have hn : ¬ p ^ 2 ∣ 168 := s16e_not_sq_dvd_168 hp hp2
  have h1 := s16n9b_card_le_mul_card_inf_centSub hp hEcard hstW h168 hn
  have hdvd : Nat.card ↥(E ⊓ centSub (commSub ⊤ A)) ∣ p ^ a :=
    hEcard ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h2 := s16n9b_card_le_mul_card_inf_centSub hp hb (inf_le_left.trans hstW') h168' hn
  have h3 : E ⊓ centSub (commSub ⊤ A) ⊓ centSub ((commSub ⊤ A).map g.toMonoidHom) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨-, hx1⟩, hx2⟩ := hx
    rw [Subgroup.mem_bot]
    apply MulEquiv.ext
    intro t
    have ht : t ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
      rw [h.sup]
      exact Subgroup.mem_top t
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 ht
    have e1 : x y = y := hx1 y hy
    have e2 : x z = z := hx2 z hz
    rw [map_mul, e1, e2]
    rfl
  rw [h3, Subgroup.card_bot] at h2
  calc Nat.card E ≤ p * Nat.card ↥(E ⊓ centSub (commSub ⊤ A)) := h1
    _ ≤ p * (p * 1) := Nat.mul_le_mul_left p h2
    _ = p ^ 2 := by ring

theorem s16e_two_pRank_lt_three [Finite T] (hT : ∀ v : T, v ^ 2 = 1)
    {M A : Subgroup (MulAut T)} {g : MulAut T} (h : S16n9bTwo M A g)
    (hrk : rk ↥(commSub ⊤ A) = 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p M < 3 := by
  by_contra hge
  push Not at hge
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  have h1 := s16e_card_le_sq hT h hrk hp hp2 hEM hE.2 hEcard
  have h2 : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos hge
  have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem s16e_rk_top_eq_two_mul [Finite T] {M A : Subgroup (MulAut T)} {g : MulAut T}
    (h : S16n9bTwo M A g) : rk ↥(⊤ : Subgroup T) = 2 * rk ↥(commSub ⊤ A) := by
  have h1 := rk_sup_add_rk_inf (commSub ⊤ A) ((commSub ⊤ A).map g.toMonoidHom)
  rw [h.sup, h.inf, rk_bot, s16n9b_rk_map] at h1
  omega

end Generic

section Construction

variable {G : Type} [Group G] [Finite G]

theorem s16e_twoConj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hV1 : v1Sub D.M V₀ V hV L = V₀) (hs : s15 D.M V₀ V hV L = 2) :
    ∃ g : MulAut (Vtil V₀ V hV), S16n9bTwo (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g := by
  have h : Hyp151 D V₀ V L := hset.hyp151
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  show ∃ g : MulAut (Vtil V₀ V hV), S16n9bTwo (Mbar D.M V₀ V hV) (barSub V₀ V hV L) g
  have hS : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}.ncard = 2 :=
    hs
  obtain ⟨x, y, hxy, hSxy⟩ := Set.ncard_eq_two.1 hS
  have hAS : barSub V₀ V hV L ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨1, (Mbar D.M V₀ V hV).one_mem, (s16n9b_map_conj_one _).symm⟩
  rw [hSxy] at hAS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAS
  obtain ⟨B, hBA, hSAB⟩ : ∃ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≠ barSub V₀ V hV L ∧
      {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
        X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {barSub V₀ V hV L, B} := by
    rcases hAS with h1 | h1
    · exact ⟨y, fun hy => hxy (h1.symm.trans hy.symm), by rw [hSxy, h1]⟩
    · exact ⟨x, fun hx => hxy (hx.trans h1), by rw [hSxy, h1, Set.pair_comm]⟩
  have hBS : B ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    rw [hSAB]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨φ₀, hφ₀M, hBφ₀⟩ := hBS
  obtain ⟨m₀, hm₀M, hKm₀⟩ := s16n9b_exists_conj_eq h hV hφ₀M
  have hAB : (barSub V₀ V hV L).map (MulAut.conj φ₀).toMonoidHom = B := hBφ₀.symm
  have hKB : barSub V₀ V hV (conjSubgroup L m₀) = B := hKm₀.trans hAB
  have hne1 : m₀ * (1 : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have := (s15_Infra_mul_inv_mem_nBar_iff (L := L) h.hyp125 hV D.M.one_mem hm₀M).1 hmem
    rw [conjSubgroup_one, hKB] at this
    exact hBA this
  have hne2 : (1 : G) * m₀⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have := (s15_Infra_mul_inv_mem_nBar_iff (L := L) h.hyp125 hV hm₀M D.M.one_mem).1 hmem
    rw [conjSubgroup_one, hKB] at this
    exact hBA this.symm
  have hc1 : ⁅barSub V₀ V hV L, B⁆ = ⊥ ∧
      commSub (commSub ⊤ (barSub V₀ V hV L)) B = ⊥ := by
    have := s15_Kbar_commute_conj h (m := 1) (m' := m₀) D.M.one_mem hm₀M hne1
    rwa [conjSubgroup_one, hKB] at this
  have hc2 : commSub (commSub ⊤ B) (barSub V₀ V hV L) = ⊥ := by
    have := (s15_Kbar_commute_conj h (m := m₀) (m' := 1) hm₀M D.M.one_mem hne2).2
    rwa [conjSubgroup_one, hKB] at this
  have hWB : (commSub ⊤ (barSub V₀ V hV L)).map φ₀.toMonoidHom = commSub ⊤ B := by
    rw [← hAB, s15_Infra_commSub_top_map_conj]
  have hKcases : ∀ m : G, m ∈ D.M → barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L ∨
      barSub V₀ V hV (conjSubgroup L m) = B := by
    intro m hm
    have hmem : barSub V₀ V hV (conjSubgroup L m) ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨(actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹,
        Subgroup.inv_mem _ (actTil_mem_barSub V₀ V hV hm (hMs hm)),
        s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L⟩
    rw [hSAB] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hW : ∀ m : G, m ∈ D.M →
      imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m) =
        commSub ⊤ (barSub V₀ V hV (conjSubgroup L m)) := by
    intro m hm
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm), wSub, imgTil_preTil]
    rfl
  refine ⟨φ₀, ?_⟩
  refine ⟨barSub_mono V₀ V hV h.le, hφ₀M, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hAB]
    exact hBA
  ·
    rw [hAB]
    exact hc1.1
  ·
    intro φ hφ
    have hmem : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
          X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := ⟨φ, hφ, rfl⟩
    rw [hSAB] at hmem
    rcases hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ((Set.mem_singleton_iff.1 h1).trans hAB.symm)
  ·
    intro b hb w hw
    rw [hAB] at hb
    exact mem_fixV.1 (commSub_eq_bot_iff.1 hc1.2 hw) b hb
  ·
    intro a ha w hw
    rw [hWB] at hw
    exact mem_fixV.1 (commSub_eq_bot_iff.1 hc2 hw) a ha
  ·
    rw [hWB]
    have hbot := s15_Core_inf_iSup_imgTil_wSub_eq_bot h hL (1 : D.M)
    rw [hV1] at hbot
    have hA1 : commSub ⊤ (barSub V₀ V hV L) ≤
        imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) ((1 : D.M) : G)) := by
      have := hW 1 D.M.one_mem
      rw [conjSubgroup_one, conjSubgroup_one] at this
      rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
      exact this.symm.le
    have hcond : barSub V₀ V hV (conjSubgroup L ((⟨m₀, hm₀M⟩ : D.M) : G)) ≠
        barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G)) := by
      show barSub V₀ V hV (conjSubgroup L m₀) ≠ barSub V₀ V hV (conjSubgroup L 1)
      rw [conjSubgroup_one, hKB]
      exact hBA
    have hB1 : commSub ⊤ B ≤ ⨆ (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
          barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G))),
        imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) (m' : G)) := by
      have h1 := hW m₀ hm₀M
      rw [hKB] at h1
      rw [← h1]
      exact le_iSup₂ (f := fun (m' : D.M)
        (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
          barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G))) =>
        imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) (m' : G)))
        ⟨m₀, hm₀M⟩ hcond
    exact le_bot_iff.1 ((inf_le_inf hA1 hB1).trans hbot.le)
  ·
    rw [hWB]
    have htop := s15_Two_iSup_commSub_eq_top D h1217 h hL
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup (Vtil V₀ V hV))
        = ⨆ m : D.M, commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G))) := htop.symm
      _ ≤ commSub ⊤ (barSub V₀ V hV L) ⊔ commSub ⊤ B := by
        refine iSup_le fun m => ?_
        rcases hKcases m m.2 with h1 | h1
        · exact (congrArg (commSub ⊤) h1).le.trans le_sup_left
        · exact (congrArg (commSub ⊤) h1).le.trans le_sup_right

theorem s16e_pRank_mBar_lt_three_of_rk_three (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = V₀)
    (hs : s15 D.M V₀ V hV L = 2) (hrk : rk ↥(wTil V₀ V hV L) = 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (Mbar D.M V₀ V hV) < 3 := by
  obtain ⟨g, hg⟩ := s16e_twoConj D h1217 hV hset hL hV1 hs
  exact s16e_two_pRank_lt_three (s15_Infra_vtil_sq_eq_one V₀ V hV) hg hrk hp hp2

theorem s16e_pRank_mBar_lt_three_of_rk_le_two (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = V₀)
    (hs : s15 D.M V₀ V hV L = 2) (hrk : rk ↥(wTil V₀ V hV L) ≤ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (Mbar D.M V₀ V hV) < 3 := by
  obtain ⟨g, hg⟩ := s16e_twoConj D h1217 hV hset hL hV1 hs
  have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
  have h1 := s16e_rk_top_eq_two_mul hg
  have h2 : rk ↥(commSub ⊤ (lBar V₀ V hV L)) ≤ 2 := hrk
  exact s16e_pRank_lt_three_of_rk_le_four hT (d := rk ↥(⊤ : Subgroup (Vtil V₀ V hV)))
    (by omega) (s16e_card_eq_two_pow_rk_top hT) hp hp2 (Mbar D.M V₀ V hV)

end Construction

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
