module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA2AAA2BA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BC
public import CFSG.Quasithin.EmptyFaithful.S152He9W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_SL4MixedAux
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl4_inf_frame_eq_bot {W : Type} [CommGroup W] [Finite W]
    {L L' : Subgroup (MulAut W)}
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hL : UC22.IsAlt ↥L 5) (hLL' : L ≠ L') (hcard : Nat.card ↥L' = Nat.card ↥L) :
    L ⊓ L' = ⊥ := by
  obtain ⟨e⟩ := hL
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hLnorm : L ≤ Subgroup.normalizer ((L ⊓ L') : Set (MulAut W)) := by
    refine (show L ≤ Subgroup.centralizer ((L ⊓ L') : Set (MulAut W)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm a ha y hy.2).symm
  have hnorm : ((L ⊓ L').subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hLnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ L').subgroupOf L) with hbot | htop
  · rw [Subgroup.subgroupOf_eq_bot] at hbot
    rw [disjoint_iff] at hbot
    simpa [inf_of_le_left inf_le_left] using hbot
  · exfalso
    have hle : L ≤ L' := (Subgroup.subgroupOf_eq_top.1 htop).trans inf_le_right
    exact hLL' (Subgroup.eq_of_le_of_card_ge hle hcard.le)

private theorem s16h_barSub_zpowers_eq_zpowers {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {M : Subgroup G} (hM : M ≤ stabTil V₀ V) {g : G} (hg : g ∈ M) :
    barSub V₀ V hV (Subgroup.zpowers g) =
      Subgroup.zpowers (actTil V₀ V hV ⟨g, hM hg⟩) := by
  have hsub : (Subgroup.zpowers g).subgroupOf (stabTil V₀ V) =
      Subgroup.zpowers (⟨g, hM hg⟩ : stabTil V₀ V) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  unfold barSub
  rw [hsub, MonoidHom.map_zpowers]

private theorem s16h_actTil_eq_one_of_barSub_zpowers_eq_bot {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) {M : Subgroup G} (hM : M ≤ stabTil V₀ V) {g : G} (hg : g ∈ M)
    (hbot : barSub V₀ V hV (Subgroup.zpowers g) = ⊥) :
    actTil V₀ V hV ⟨g, hM hg⟩ = 1 := by
  have hmem : actTil V₀ V hV ⟨g, hM hg⟩ ∈ barSub V₀ V hV (Subgroup.zpowers g) :=
    actTil_mem_barSub V₀ V hV (Subgroup.mem_zpowers g) (hM hg)
  rw [hbot] at hmem
  simpa using hmem

private theorem s16h_barSub_zpowers_ne_bot_of_not_mem_cTilde {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) {M : Subgroup G} (hMn : M ≤ normalizer (V : Set G))
    (hM : M ≤ stabTil V₀ V) {g : G} (hg : g ∈ M) (hgC : g ∉ F11.CTilde M V₀ V) :
    barSub V₀ V hV (Subgroup.zpowers g) ≠ ⊥ := by
  intro hbot
  apply hgC
  rw [mem_cTilde_iff hV hMn]
  exact ⟨hg, hM hg, s16h_actTil_eq_one_of_barSub_zpowers_eq_bot hV hM hg hbot⟩

theorem s16h_sl4_pure_to_mixed
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y) (hYcard : Nat.card ↥Y = 9)
    (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T) :
    ∀ r ∈ (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G),
      orderOf r = 3 → ¬ s16h_SL4Mixed V L h.hyp151.isElemAbelian x r →
      ∃ s ∈ (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G),
        orderOf s = 3 ∧ s16h_SL4Mixed V L h.hyp151.isElemAbelian x s := by
  intro r hrR hr3 hnot
  have hV := h.hyp151.isElemAbelian
  have hMn : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil hMn h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hHM : Y ⊔ D.T ≤ D.M := sup_le hYM D.sylowM.le
  have hrM : r ∈ D.M := hHM hrR.1
  let R : Subgroup G := (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)
  have hRR : r ∈ R := hrR
  have hRM : R ≤ D.M := inf_le_left.trans hHM
  have hCtilde : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) :=
    s16h_sl4_engine_b_three_not_dvd_kernel D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin
      hZ hbad hrow hZ4 hxM hxn hZ0
  have hrC : r ∉ F11.CTilde D.M ⊥ V := by
    intro hrc
    have hdvd : orderOf r ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) :=
      Subgroup.orderOf_dvd_natCard _ hrc
    rw [hr3] at hdvd
    exact hCtilde hdvd
  have hrbar_ne : barSub ⊥ V hV (Subgroup.zpowers r) ≠ ⊥ :=
    s16h_barSub_zpowers_ne_bot_of_not_mem_cTilde hV hMn hMs hrM hrC
  have hTc : D.T ≤ Subgroup.normalizer (E3.cClos V 1 D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := 1) D.T)
  have hTNc : D.T ≤ Subgroup.normalizer
      (Subgroup.centralizer (E3.cClos V 1 D.T : Set G) : Set G) :=
    hTc.trans (CFSG.BenderSuzuki.le_normalizer_centralizer_of_le_normalizer
      (V := Subgroup.normalizer (E3.cClos V 1 D.T : Set G))
      (J := E3.cClos V 1 D.T) le_rfl)
  have hTR : D.T ≤ Subgroup.normalizer (R : Set G) := by
    rw [show R = (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) from rfl]
    exact (le_inf (le_sup_right.trans Subgroup.le_normalizer) hTNc).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Y ⊔ D.T)
        (K := Subgroup.centralizer (E3.cClos V 1 D.T : Set G)))
  obtain ⟨B, hBne, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  have hxMbar : actTil ⊥ V hV ⟨x, hMs hxM⟩ ∈ Mbar D.M ⊥ V hV :=
    actTil_mem_barSub ⊥ V hV hxM (hMs hxM)
  have hxinvMbar : actTil ⊥ V hV ⟨x⁻¹, hMs (D.M.inv_mem hxM)⟩ ∈ Mbar D.M ⊥ V hV :=
    actTil_mem_barSub ⊥ V hV (D.M.inv_mem hxM) (hMs (D.M.inv_mem hxM))
  have hBx : barSub ⊥ V hV (conjSubgroup L x) = B := by
    have hbarx : barSub ⊥ V hV (conjSubgroup L x) =
        (barSub ⊥ V hV L).map
          (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom :=
      s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L
    have hact : (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹ =
        actTil ⊥ V hV ⟨x⁻¹, hMs (D.M.inv_mem hxM)⟩ := by
      rw [show (⟨x, hMs hxM⟩ : stabTil ⊥ V) = ⟨x⁻¹, hMs (D.M.inv_mem hxM)⟩⁻¹ from
        Subtype.ext (by simp), map_inv, inv_inv]
    rw [hbarx, hact]
    rcases F.perm (actTil ⊥ V hV ⟨x⁻¹, hMs (D.M.inv_mem hxM)⟩) hxinvMbar with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exfalso
      have hh : barSub ⊥ V hV (conjSubgroup L x) = barSub ⊥ V hV L := by
        rw [hbarx, hact]
        exact h1
      exact hxn ((s15_Infra_mem_nBar_iff h.hyp151.hyp125 hV hxM).2 hh)
    · exact h1
  have hnot' : barSub ⊥ V hV (Subgroup.zpowers r) ≤ barSub ⊥ V hV L ∨
      barSub ⊥ V hV (Subgroup.zpowers r) ≤ B := by
    have hh := hnot
    unfold s16h_SL4Mixed at hh
    by_cases hA : barSub ⊥ V hV (Subgroup.zpowers r) ≤ barSub ⊥ V hV L
    · exact Or.inl hA
    · by_cases hB' : barSub ⊥ V hV (Subgroup.zpowers r) ≤
          barSub ⊥ V hV (conjSubgroup L x)
      · exact Or.inr (by rw [hBx] at hB'; exact hB')
      · exact absurd ⟨hA, hB'⟩ hh
  obtain ⟨t, htT, htB⟩ := F.swap
  obtain ⟨u, huT, huact⟩ := (mem_barSub ⊥ V hV D.T t).1 htT
  have hconjR : ∀ w ∈ D.T, w * r * w⁻¹ ∈ R := by
    intro w hw
    have hwinv : w⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).inv_mem (hTR hw)
    simpa using (Subgroup.mem_normalizer_iff''.1 hwinv r).1 hRR
  have hconj3 : ∀ w : G, orderOf (w * r * w⁻¹) = 3 := by
    intro w
    rw [← SemiconjBy.orderOf_eq w (show SemiconjBy w r (w * r * w⁻¹) from by
      show w * r = (w * r * w⁻¹) * w
      group)]
    exact hr3
  have hBtinv : B.map (MulAut.conj t⁻¹).toMonoidHom = barSub ⊥ V hV L := by
    rw [← htB, Subgroup.map_map]
    have hcomp : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        MonoidHom.id (MulAut (Vtil ⊥ V hV)) := by
      ext w x
      change (MulAut.conj t⁻¹) ((MulAut.conj t) w) x = w x
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [hcomp, Subgroup.map_id]
    rfl
  have hbot : barSub ⊥ V hV L ⊓ B = ⊥ :=
    s16h_sl4_inf_frame_eq_bot F.comm (s16h_sl4_isAlt_of_rowSL2 hrow) hBne.symm
      (by
        rw [← htB]
        exact Subgroup.card_map_of_injective (MulAut.conj t).injective)
  have hkey : ∃ a b : G, a ∈ R ∧ b ∈ R ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      barSub ⊥ V hV (Subgroup.zpowers a) ≤ barSub ⊥ V hV L ∧
      barSub ⊥ V hV (Subgroup.zpowers b) ≤ B ∧
      barSub ⊥ V hV (Subgroup.zpowers a) ≠ ⊥ ∧
      barSub ⊥ V hV (Subgroup.zpowers b) ≠ ⊥ := by
    rcases hnot' with hA | hB'
    · have hEq : barSub ⊥ V hV (Subgroup.zpowers ((u : G) * r * (u : G)⁻¹)) =
          (barSub ⊥ V hV (Subgroup.zpowers r)).map (MulAut.conj t).toMonoidHom := by
        have h1 : Subgroup.zpowers ((u : G) * r * (u : G)⁻¹) =
            conjSubgroup (Subgroup.zpowers r) ((u⁻¹ : stabTil ⊥ V) : G) := by
          rw [conjSubgroup, MonoidHom.map_zpowers]
          simp [MulAut.conj_apply]
        rw [h1, s15_Infra_barSub_conjSubgroup ⊥ V hV (u⁻¹).2 (Subgroup.zpowers r)]
        have hact : (actTil ⊥ V hV (u⁻¹))⁻¹ = t := by
          rw [map_inv, huact, inv_inv]
        rw [hact]
      refine ⟨r, (u : G) * r * (u : G)⁻¹, hRR, hconjR (u : G) huT, hr3,
        hconj3 (u : G), hA, ?_, hrbar_ne, ?_⟩
      · rw [hEq]
        exact (Subgroup.map_mono hA).trans (le_of_eq htB)
      · rw [hEq]
        exact fun hbot' => hrbar_ne (Subgroup.map_injective
          (MulAut.conj t).injective (by simpa using hbot'))
    · have hEq : barSub ⊥ V hV (Subgroup.zpowers ((u : G)⁻¹ * r * (u : G))) =
          (barSub ⊥ V hV (Subgroup.zpowers r)).map (MulAut.conj t⁻¹).toMonoidHom := by
        have h1 : Subgroup.zpowers ((u : G)⁻¹ * r * (u : G)) =
            conjSubgroup (Subgroup.zpowers r) (u : G) := by
          rw [conjSubgroup, MonoidHom.map_zpowers]
          simp [MulAut.conj_apply]
        rw [h1, s15_Infra_barSub_conjSubgroup ⊥ V hV u.2 (Subgroup.zpowers r), huact]
      refine ⟨(u : G)⁻¹ * r * (u : G), r,
        (by simpa using hconjR (u : G)⁻¹ (D.T.inv_mem huT)), hRR,
        (by simpa using hconj3 (u : G)⁻¹), hr3, ?_, hB', ?_, hrbar_ne⟩
      · rw [hEq]
        exact (Subgroup.map_mono hB').trans (le_of_eq hBtinv)
      · rw [hEq]
        exact fun hbot' => hrbar_ne (Subgroup.map_injective
          (MulAut.conj t⁻¹).injective (by simpa using hbot'))
  obtain ⟨a, b, haR, hbR, ha3, hb3, haL, hbL, ha1, hb1⟩ := hkey
  let φ : ↥R →* MulAut (Vtil ⊥ V hV) := (barHom ⊥ V hV hMs).comp (Subgroup.inclusion hRM)
  have hφa : φ ⟨a, haR⟩ = actTil ⊥ V hV ⟨a, hMs (hRM haR)⟩ := rfl
  have hφb : φ ⟨b, hbR⟩ = actTil ⊥ V hV ⟨b, hMs (hRM hbR)⟩ := rfl
  have hφaL : φ ⟨a, haR⟩ ∈ barSub ⊥ V hV L := by
    rw [hφa]
    exact haL (actTil_mem_barSub ⊥ V hV (Subgroup.mem_zpowers a) (hMs (hRM haR)))
  have hφbB : φ ⟨b, hbR⟩ ∈ B := by
    rw [hφb]
    exact hbL (actTil_mem_barSub ⊥ V hV (Subgroup.mem_zpowers b) (hMs (hRM hbR)))
  have hφa1 : φ ⟨a, haR⟩ ≠ 1 := by
    intro h1
    apply ha1
    rw [s16h_barSub_zpowers_eq_zpowers hV hMs (hRM haR)]
    rw [show actTil ⊥ V hV ⟨a, hMs (hRM haR)⟩ = 1 from h1]
    exact Subgroup.zpowers_one_eq_bot
  have hφb1 : φ ⟨b, hbR⟩ ≠ 1 := by
    intro h1
    apply hb1
    rw [s16h_barSub_zpowers_eq_zpowers hV hMs (hRM hbR)]
    rw [show actTil ⊥ V hV ⟨b, hMs (hRM hbR)⟩ = 1 from h1]
    exact Subgroup.zpowers_one_eq_bot
  have hφa3 : (φ ⟨a, haR⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨a, haR⟩ : ↥R) ^ 3 = 1 := by
      apply Subtype.ext
      show a ^ 3 = 1
      exact orderOf_dvd_iff_pow_eq_one.1 (by rw [ha3])
    rw [h3, map_one]
  have hφb3 : (φ ⟨b, hbR⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨b, hbR⟩ : ↥R) ^ 3 = 1 := by
      apply Subtype.ext
      show b ^ 3 = 1
      exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hb3])
    rw [h3, map_one]
  have hker3 : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker φ) := by
    intro h3
    have hker_le : (MonoidHom.ker φ).map R.subtype ≤ F11.CTilde D.M ⊥ V := by
      intro g hg
      obtain ⟨k, hk, rfl⟩ := hg
      have hk1 : φ k = 1 := MonoidHom.mem_ker.1 hk
      rw [mem_cTilde_iff hV hMn]
      exact ⟨hRM k.2, hMs (hRM k.2), hk1⟩
    have h3map : 3 ∣ Nat.card ↥((MonoidHom.ker φ).map R.subtype) := by
      rwa [Subgroup.card_map_of_injective R.subtype_injective]
    exact hCtilde (h3map.trans (Subgroup.card_dvd_of_le hker_le))
  obtain ⟨s, hs3, hsL, hsB⟩ :=
    s16h_exists_order_three_pow_not_mem φ F.comm hbot hφaL hφbB hφa1 hφb1 hφa3 hφb3 hker3
  refine ⟨(s : G), s.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hs3
  · have hmem : actTil ⊥ V hV ⟨(s : G), hMs (hRM s.2)⟩ ∈
        barSub ⊥ V hV (Subgroup.zpowers (s : G)) :=
      actTil_mem_barSub ⊥ V hV (Subgroup.mem_zpowers (s : G)) (hMs (hRM s.2))
    have hφs : φ s = actTil ⊥ V hV ⟨(s : G), hMs (hRM s.2)⟩ := rfl
    unfold s16h_SL4Mixed
    constructor
    · intro hle
      exact hsL (hφs ▸ hle hmem)
    · intro hle
      rw [hBx] at hle
      exact hsB (hφs ▸ hle hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
