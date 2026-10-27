module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type*} [CommGroup T]

theorem s16n9b_map_conj_map_conj (A : Subgroup (MulAut T)) (x y : MulAut T) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem s16n9b_map_conj_one (A : Subgroup (MulAut T)) :
    A.map (MulAut.conj (1 : MulAut T)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem s16n9b_rk_map (e : MulAut T) (U : Subgroup T) : rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective e.injective]

theorem s16n9b_rk_le_commV [Finite T] {W : Subgroup T} {φ : MulAut T}
    (hinj : ∀ w ∈ W, φ w = w → w = 1) :
    rk ↥W ≤ rk ↥(commV (Subgroup.zpowers φ)) := by
  have h1 := rk_map_add_rk_inf_ker (commHom φ) W
  have h2 : W ⊓ (commHom φ).ker = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_inf, ker_commHom, mem_fixV_zpowers_iff_apply] at hw
    exact Subgroup.mem_bot.2 (hinj w hw.1 hw.2)
  have h3 : rk ↥(W.map (commHom φ)) ≤ rk ↥(commV (Subgroup.zpowers φ)) := by
    rw [commV_zpowers_eq_map]
    exact rk_mono (Subgroup.map_mono le_top)
  rw [h2, rk_bot] at h1
  omega

theorem s16n9b_commV_le_of_fix {W W' : Subgroup T} (hsup : W ⊔ W' = ⊤) {φ : MulAut T}
    (hfix : ∀ w ∈ W, φ w = w) (hinv : φ ∈ stabSub W') : commV (Subgroup.zpowers φ) ≤ W' := by
  have hc : φ ∈ centSub W := fun u hu => hfix u hu
  have hz1 : Subgroup.zpowers φ ≤ centSub W := (Subgroup.zpowers_le).2 hc
  have hz2 : Subgroup.zpowers φ ≤ stabSub W' := (Subgroup.zpowers_le).2 hinv
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  have hv : v ∈ W ⊔ W' := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨w, hw, w', hw', rfl⟩ := Subgroup.mem_sup.1 hv
  have h1 : x w = w := hz1 hx w hw
  have h2 : x w' ∈ W' := (mem_stabSub.1 (hz2 hx) w').2 hw'
  have h3 : x (w * w') * (w * w')⁻¹ = x w' * w'⁻¹ := by
    rw [map_mul, h1, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  rw [h3]
  exact W'.mul_mem h2 (W'.inv_mem hw')

theorem s16n9b_mem_stabSub_of_map_eq {W : Subgroup T} {φ : MulAut T}
    (h : W.map φ.toMonoidHom = W) : φ ∈ stabSub W := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ W.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : φ u ∈ W.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'
    exact hu'

structure S16n9bTwo (M A : Subgroup (MulAut T)) (g : MulAut T) : Prop where
  le : A ≤ M
  mem : g ∈ M
  ne : A.map (MulAut.conj g).toMonoidHom ≠ A
  comm : ⁅A, A.map (MulAut.conj g).toMonoidHom⁆ = ⊥
  conj : ∀ φ ∈ M, A.map (MulAut.conj φ).toMonoidHom = A ∨
    A.map (MulAut.conj φ).toMonoidHom = A.map (MulAut.conj g).toMonoidHom
  fixB : ∀ b ∈ A.map (MulAut.conj g).toMonoidHom, ∀ w ∈ commSub ⊤ A, b w = w
  fixA : ∀ a ∈ A, ∀ w ∈ (commSub ⊤ A).map g.toMonoidHom, a w = w
  inf : commSub ⊤ A ⊓ (commSub ⊤ A).map g.toMonoidHom = ⊥
  sup : commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom = ⊤

@[expose] def S16n9bRank (M A : Subgroup (MulAut T)) (r : ℕ) : Prop :=
  ∀ φ ∈ M, (∃ a : ℕ, orderOf φ = 2 ^ a) → A.map (MulAut.conj φ).toMonoidHom = A →
    (∀ w ∈ commSub ⊤ A, φ w = w) ∨ r ≤ rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers φ))

theorem s16n9b_two_invFix [Finite T] {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) {p N r : ℕ} (hN : N < rk ↥(commSub ⊤ A))
    (hr : N < 2 * r) (hp : ∃ a ∈ A, orderOf a = p) (hrank : S16n9bRank M A r) :
    s16n9bInvFix M p N := by
  obtain ⟨a₀, ha₀A, ha₀p⟩ := hp
  intro φ hφM hφ2 hrk z hz hz1
  have hcomm_le : rk ↥(commV (Subgroup.zpowers φ)) ≤ N := by
    have := rkIdx_fixV_zpowers φ
    omega
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  rcases h.conj φ hφM with hA | hB
  swap
  ·
    exfalso
    have hWφ : (commSub ⊤ A).map φ.toMonoidHom = (commSub ⊤ A).map g.toMonoidHom := by
      rw [← s15_Infra_commSub_top_map_conj A φ, hB, hgB]
    have hinj : ∀ w ∈ commSub ⊤ A, φ w = w → w = 1 := by
      intro w hw hfix
      have h1 : φ w ∈ (commSub ⊤ A).map g.toMonoidHom := by
        rw [← hWφ]
        exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
      rw [hfix] at h1
      have h2 : w ∈ commSub ⊤ A ⊓ (commSub ⊤ A).map g.toMonoidHom := ⟨hw, h1⟩
      rw [h.inf] at h2
      exact Subgroup.mem_bot.1 h2
    have := s16n9b_rk_le_commV hinj
    omega
  have hWφ : (commSub ⊤ A).map φ.toMonoidHom = commSub ⊤ A := by
    rw [← s15_Infra_commSub_top_map_conj A φ, hA]
  have hBφ : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
    rw [s16n9b_map_conj_map_conj]
    rcases h.conj (φ * g) (M.mul_mem hφM h.mem) with h1 | h1
    · exfalso
      apply h.ne
      have h2 : A.map (MulAut.conj φ⁻¹).toMonoidHom = A := by
        have := congrArg (fun X : Subgroup (MulAut T) => X.map (MulAut.conj φ⁻¹).toMonoidHom) hA
        simp only [s16n9b_map_conj_map_conj, inv_mul_cancel, s16n9b_map_conj_one] at this
        exact this.symm
      calc A.map (MulAut.conj g).toMonoidHom
          = (A.map (MulAut.conj (φ * g)).toMonoidHom).map (MulAut.conj φ⁻¹).toMonoidHom := by
            rw [s16n9b_map_conj_map_conj, inv_mul_cancel_left]
        _ = A.map (MulAut.conj φ⁻¹).toMonoidHom := by rw [h1]
        _ = A := h2
    · exact h1
  have hW'φ : ((commSub ⊤ A).map g.toMonoidHom).map φ.toMonoidHom =
      (commSub ⊤ A).map g.toMonoidHom := by
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ φ, hBφ]
  have hstW : φ ∈ stabSub (commSub ⊤ A) := s16n9b_mem_stabSub_of_map_eq hWφ
  have hstW' : φ ∈ stabSub ((commSub ⊤ A).map g.toMonoidHom) :=
    s16n9b_mem_stabSub_of_map_eq hW'φ
  obtain ⟨φ', hφ'⟩ : ∃ φ' : MulAut T, φ' = g⁻¹ * φ * g := ⟨_, rfl⟩
  have hφ'M : φ' ∈ M := by
    rw [hφ']
    exact M.mul_mem (M.mul_mem (M.inv_mem h.mem) hφM) h.mem
  have hφ'2 : ∃ a : ℕ, orderOf φ' = 2 ^ a := by
    obtain ⟨a, ha⟩ := hφ2
    refine ⟨a, ?_⟩
    rw [← ha]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective φ
    rw [hφ']
    simpa [MulAut.conj_apply] using this
  have hAφ' : A.map (MulAut.conj φ').toMonoidHom = A := by
    have e1 : A.map (MulAut.conj φ').toMonoidHom =
        ((A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom := by
      rw [s16n9b_map_conj_map_conj, s16n9b_map_conj_map_conj, hφ']
    rw [e1, hBφ, s16n9b_map_conj_map_conj, inv_mul_cancel, s16n9b_map_conj_one]
  have hφ'W : ∀ w ∈ commSub ⊤ A, φ (g w) = g (φ' w) := by
    intro w _
    rw [hφ']
    simp [MulAut.mul_apply]
  have hr1 := hrank φ hφM hφ2 hA
  have hr2 := hrank φ' hφ'M hφ'2 hAφ'
  rcases hr1 with hfixW | hrW
  ·
    have hle : commV (Subgroup.zpowers φ) ≤ (commSub ⊤ A).map g.toMonoidHom :=
      s16n9b_commV_le_of_fix h.sup hfixW hstW'
    exact ⟨a₀, h.le ha₀A, ha₀p, h.fixA a₀ ha₀A z (hle hz)⟩
  rcases hr2 with hfixW' | hrW'
  ·
    have hfixW'' : ∀ w' ∈ (commSub ⊤ A).map g.toMonoidHom, φ w' = w' := by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hw'
      show φ (g w) = g w
      rw [hφ'W w hw, hfixW' w hw]
    have hsup' : (commSub ⊤ A).map g.toMonoidHom ⊔ commSub ⊤ A = ⊤ := by
      rw [sup_comm]; exact h.sup
    have hle : commV (Subgroup.zpowers φ) ≤ commSub ⊤ A :=
      s16n9b_commV_le_of_fix hsup' hfixW'' hstW
    refine ⟨(MulAut.conj g) a₀, ?_, ?_, ?_⟩
    · simp only [MulAut.conj_apply]
      exact M.mul_mem (M.mul_mem h.mem (h.le ha₀A)) (M.inv_mem h.mem)
    · rw [← ha₀p]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₀
    · exact h.fixB _ (Subgroup.mem_map.2 ⟨a₀, ha₀A, rfl⟩) z (hle hz)
  ·
    exfalso
    have hrW'' : r ≤ rk ↥(commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ)) := by
      have e1 := s15_Core_commSub_map_conj (commSub ⊤ A) (Subgroup.zpowers φ') g
      have e2 : (Subgroup.zpowers φ').map (MulAut.conj g).toMonoidHom = Subgroup.zpowers φ := by
        rw [MonoidHom.map_zpowers]
        congr 1
        rw [hφ']
        simp [MulAut.conj_apply]
        group
      rw [e2] at e1
      rw [e1, s16n9b_rk_map]
      exact hrW'
    have hU1 : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ≤ commSub ⊤ A :=
      commSub_le_of_invariant fun x hx w hw =>
        (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW hx) w).2 hw
    have hU2 : commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ) ≤
        (commSub ⊤ A).map g.toMonoidHom :=
      commSub_le_of_invariant fun x hx w hw =>
        (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW' hx) w).2 hw
    have hc1 : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ≤ commV (Subgroup.zpowers φ) := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    have hc2 : commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ) ≤
        commV (Subgroup.zpowers φ) := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    have hbot : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ⊓
        commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf hU1 hU2).trans h.inf.le)
    have hsum := rk_sup_add_rk_inf (commSub (commSub ⊤ A) (Subgroup.zpowers φ))
      (commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ))
    rw [hbot, rk_bot] at hsum
    have hle := rk_mono (sup_le hc1 hc2)
    omega

end Generic


section Construction

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_exists_conj_eq {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV) :
    ∃ m : G, m ∈ D.M ∧ barSub V₀ V hV (conjSubgroup L m) =
      (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom := by
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hgm : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil _ _).inv_mem g.2
  have hgt : actTil V₀ V hV ⟨(g : G)⁻¹, hgm⟩ = (actTil V₀ V hV g)⁻¹ := by
    rw [show (⟨(g : G)⁻¹, hgm⟩ : stabTil V₀ V) = ⟨g, g.2⟩⁻¹ from rfl, map_inv]
  refine ⟨(g : G)⁻¹, D.M.inv_mem hgM, ?_⟩
  rw [← hgφ, s15_Infra_barSub_conjSubgroup V₀ V hV hgm L]
  congr 1
  rw [hgt, inv_inv]

theorem s16n9b_twoConj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 2) :
    ∃ g : MulAut (Vtil V₀ V hV), S16n9bTwo (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g := by
  have h : Hyp151 D V₀ V L := hc.setting.hyp151
  have hL : barSub V₀ V hV L ≠ ⊥ := hc.ne_bot
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
    rw [v1Sub_of_ne_bot D.M V₀ V hV L hV0] at hbot
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

end Construction

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
