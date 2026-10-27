module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENineBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2V1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement Pointwise

section Generic

variable {T : Type} [CommGroup T]

private def s1614e3Case9Com (φ : MulAut T) : T →* T where
  toFun t := φ t * t⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

private theorem s1614e3Case9Com_apply (φ : MulAut T) (t : T) :
    s1614e3Case9Com φ t = φ t * t⁻¹ := rfl

private theorem s1614e3Case9Com_ker (φ : MulAut T) :
    (s1614e3Case9Com φ).ker = fixV (Subgroup.zpowers φ) := by
  ext t
  rw [MonoidHom.mem_ker, s1614e3Case9Com_apply, mul_inv_eq_one, mem_fixV_zpowers_iff_apply]

private theorem s1614e3_case9_mQuot_eq_rk_image [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (W : Subgroup T) (φ : MulAut T) :
    E3.mQuot W (W ⊓ fixV (Subgroup.zpowers φ)) =
      rk ↥(W.map (s1614e3Case9Com φ)) := by
  have h1 := rk_map_add_rk_inf_ker (s1614e3Case9Com φ) W
  rw [s1614e3Case9Com_ker] at h1
  have h2 : E3.mQuot W (W ⊓ fixV (Subgroup.zpowers φ)) +
      rk ↥(W ⊓ fixV (Subgroup.zpowers φ)) = rk ↥W := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hT).to_subgroup W)
      (inf_le_left : W ⊓ fixV (Subgroup.zpowers φ) ≤ W)
    rw [card_eq_two_pow hT, card_eq_two_pow hT, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh.symm
  omega

private theorem s1614e3_case9_mQuot_le_rk_commSub [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (W : Subgroup T) (φ : MulAut T) :
    E3.mQuot W (W ⊓ fixV (Subgroup.zpowers φ)) ≤ rk ↥(commSub W (Subgroup.zpowers φ)) := by
  rw [s1614e3_case9_mQuot_eq_rk_image hT W φ]
  apply rk_mono (G := T)
  rintro _ ⟨w, hw, rfl⟩
  exact Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, w, hw, rfl⟩
private theorem s1614e3_case9_map_conj_map_conj (A : Subgroup (MulAut T)) (x y : MulAut T) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s1614e3_case9_map_conj_one (A : Subgroup (MulAut T)) :
    A.map (MulAut.conj (1 : MulAut T)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

end Generic

private theorem s1614e3_case9_eq_pair_of_ncard_two {α : Type*} {s : Set α} {a b : α}
    (hs : s.ncard = 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  obtain ⟨Y₁, Y₂, -, hYset⟩ := Set.ncard_eq_two.1 hs
  rw [hYset] at ha hb ⊢
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha, ← hb]
  · rw [← ha, ← hb, Set.pair_comm]
  · exact absurd (ha.trans hb.symm) hab

variable {G : Type} [Group G] [Finite G]

theorem s1614e3_case9_rank (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h9 : Case168_9 D ⊥ V hV L) :
    s16n9b_case9Rank (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) 3 := by
  have hv1 : v1Sub D.M ⊥ V hV L = ⊥ := s16c167_v1Sub_eq_bot_of_case9 D hV rfl h9
  intro φ hφM hφ2 hφA
  obtain ⟨Z, hZcard, hZnorm, hZL, hZJ, hZf, -⟩ := s16t_case9_frame D h1217 hV hc hv1 h9
  obtain ⟨-, hL3, -, hsum, -⟩ := h9
  have hL : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  have hJ : NatSum3 (lBar ⊥ V hV L) (wTil ⊥ V hV L) := s16c167_natSum3_of_sumOfNat hsum
  have hWv : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  obtain ⟨a, ha⟩ := hφ2
  have hφpow : φ ^ 2 ^ a = 1 := by rw [← ha]; exact pow_orderOf_eq_one φ
  have hφZ : Z.map (MulAut.conj φ).toMonoidHom = Z := hZnorm φ hφM
  have hφW : (wTil ⊥ V hV L).map φ.toMonoidHom = wTil ⊥ V hV L := by
    show (commSub ⊤ (lBar ⊥ V hV L)).map φ.toMonoidHom = commSub ⊤ (lBar ⊥ V hV L)
    rw [← s15_Infra_commSub_top_map_conj (lBar ⊥ V hV L) φ, hφA]
  obtain ⟨⟨l, hl, hxl⟩, -⟩ :=
    s16c167_natSum3_normalizer_two hWv hL hJ hZcard hZL hZJ hZf hφpow hφZ hφA hφW
  by_cases hl1 : l = 1
  · left
    intro w hw
    simpa [hl1] using hxl w hw
  · right
    have h3 := s16n9b_natSum3_comm_rank hWv hL hJ hl hl1
    have hfix : wTil ⊥ V hV L ⊓ fixV (Subgroup.zpowers l) =
        wTil ⊥ V hV L ⊓ fixV (Subgroup.zpowers φ) := by
      ext w
      rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_fixV_zpowers l w, mem_fixV_zpowers φ w]
      constructor
      · rintro ⟨hw, hlw⟩
        exact ⟨hw, (hxl w hw).trans hlw⟩
      · rintro ⟨hw, hφw⟩
        exact ⟨hw, (hxl w hw).symm.trans hφw⟩
    have h3' : 3 ≤ E3.mQuot (wTil ⊥ V hV L)
        (wTil ⊥ V hV L ⊓ fixV (Subgroup.zpowers φ)) := by
      rw [← hfix]
      exact h3
    exact h3'.trans (s1614e3_case9_mQuot_le_rk_commSub hWv (wTil ⊥ V hV L) φ)


theorem s1614e3_case9_two (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h9 : Case168_9 D ⊥ V hV L) :
    ∃ g : MulAut (Vtil ⊥ V hV),
      s16n9b_case9Two (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) g := by
  have hv1 : v1Sub D.M ⊥ V hV L = ⊥ := s16c167_v1Sub_eq_bot_of_case9 D hV rfl h9
  classical
  have hS : Setting16 D ⊥ V L := hc.setting
  have hH : Hyp151 D ⊥ V L := hS.hyp151
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  obtain ⟨g₂, hg₂M, hg₂ne⟩ : ∃ g ∈ Mbar D.M ⊥ V hV,
      (lBar ⊥ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar ⊥ V hV L := by
    by_contra hcon
    have hsingle : {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
        ∃ φ ∈ Mbar D.M ⊥ V hV,
          Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = {lBar ⊥ V hV L} := by
      ext Y
      constructor
      · rintro ⟨φ, hφM, rfl⟩
        by_contra hne
        exact hcon ⟨φ, hφM, hne⟩
      · rintro rfl
        exact ⟨1, (Mbar D.M ⊥ V hV).one_mem, by ext y; simp⟩
    rw [hsingle] at hcls
    simp at hcls
  obtain ⟨x, hxM, hxg₂⟩ := (mem_barSub ⊥ V hV D.M g₂).1 hg₂M
  have hgne : (lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom ≠ lBar ⊥ V hV L := by
    intro h
    apply hg₂ne
    have h' := congrArg (fun X : Subgroup (MulAut (Vtil ⊥ V hV)) =>
      X.map (MulAut.conj g₂).toMonoidHom) h
    rw [s1614e3_case9_map_conj_map_conj, mul_inv_cancel, s1614e3_case9_map_conj_one] at h'
    exact h'.symm
  have hgM : g₂⁻¹ ∈ Mbar D.M ⊥ V hV := (Mbar D.M ⊥ V hV).inv_mem hg₂M
  have hconjinv : ((MulAut.conj g₂)⁻¹).toMonoidHom =
      (MulAut.conj g₂⁻¹).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply]
  have hbar : barSub ⊥ V hV (conjSubgroup L (x : G)) =
      (lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV x.2 L, hxg₂]
    exact congrArg (fun f : MulAut (Vtil ⊥ V hV) →* MulAut (Vtil ⊥ V hV) =>
      (barSub ⊥ V hV L).map f) hconjinv
  have hxnbar : (x : G) ∉ nBar D.M ⊥ V hV L := by
    intro hx
    rw [s15_Infra_mem_nBar_iff hS.hyp16.hyp125 hV hxM] at hx
    rw [hbar] at hx
    exact hgne hx
  have hcomm := hH.commute (x : G) hxM hxnbar
  rw [hbar] at hcomm
  have hABne : lBar ⊥ V hV L ≠
      (lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := fun h => hgne h.symm
  have hpair : {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} =
      {lBar ⊥ V hV L, (lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom} :=
    s1614e3_case9_eq_pair_of_ncard_two hcls
      ⟨1, (Mbar D.M ⊥ V hV).one_mem, by ext y; simp⟩ ⟨g₂⁻¹, hgM, rfl⟩ hABne
  have hrk0 : rk ↥(wTil ⊥ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 18 :=
    s16t_case9_rk_top D h1217 hV hH hv1 hc.ne_bot hs15 hsum
  obtain ⟨hind, hsup⟩ := s16t_case9_directSum D h1217 hV hH hv1 hc.ne_bot
  have hn2 : (conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrktop
  have hWmem : (wTil ⊥ V hV L) ∈ conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L) :=
    ⟨1, (Mbar D.M ⊥ V hV).one_mem, by ext y; simp⟩
  have hW'mem : (wTil ⊥ V hV L).map g₂⁻¹.toMonoidHom ∈
      conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L) := ⟨g₂⁻¹, hgM, rfl⟩
  have hWne : (wTil ⊥ V hV L) ≠ (wTil ⊥ V hV L).map g₂⁻¹.toMonoidHom := by
    intro h
    apply hgne
    have hmem : lBar ⊥ V hV L ∈ {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
        ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨1, (Mbar D.M ⊥ V hV).one_mem, by ext y; simp⟩
    have hstab : (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)).map
        g₂⁻¹.toMonoidHom = commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L) := by
      show (wTil ⊥ V hV L).map g₂⁻¹.toMonoidHom = wTil ⊥ V hV L
      exact h.symm
    exact s16c167_normalizes_of_stab hcls hn2 (lBar ⊥ V hV L) hmem g₂⁻¹ hgM hstab
  have hpairW : conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L) =
      {wTil ⊥ V hV L, (wTil ⊥ V hV L).map g₂⁻¹.toMonoidHom} :=
    s1614e3_case9_eq_pair_of_ncard_two hn2 hWmem hW'mem hWne
  have hdisj : wTil ⊥ V hV L ⊓ (wTil ⊥ V hV L).map g₂⁻¹.toMonoidHom = ⊥ :=
    disjoint_iff.mp ((sSupIndep_pair hWne).mp (hpairW ▸ hind))
  have hsup' : wTil ⊥ V hV L ⊔ (wTil ⊥ V hV L).map g₂⁻¹.toMonoidHom = ⊤ := by
    have h := hpairW ▸ hsup
    rwa [sSup_pair] at h
  refine ⟨g₂⁻¹, ⟨barSub_mono ⊥ V hV hH.le, hgM, hgne, hcomm.1, ?_, ?_, ?_, hdisj, hsup'⟩⟩
  · intro φ hφM
    have hmem : (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        ({lBar ⊥ V hV L, (lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom} :
          Set (Subgroup (MulAut (Vtil ⊥ V hV)))) := by
      rw [← hpair]
      exact ⟨φ, hφM, rfl⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro b hb w hw
    have hle : wTil ⊥ V hV L ≤
        fixV ((lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom) :=
      commSub_eq_bot_iff.mp hcomm.2
    exact (mem_fixV.mp (hle hw)) b hb
  · intro a ha w hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    have hmemg : g₂ * a * g₂⁻¹ ∈ (lBar ⊥ V hV L).map (MulAut.conj g₂).toMonoidHom :=
      Subgroup.mem_map.2 ⟨a, ha, rfl⟩
    have hAg : (lBar ⊥ V hV L).map (MulAut.conj g₂).toMonoidHom =
        (lBar ⊥ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
      have hσ : (lBar ⊥ V hV L).map (MulAut.conj g₂).toMonoidHom ∈
          {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
            ∃ φ ∈ Mbar D.M ⊥ V hV,
              Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} :=
        ⟨g₂, hg₂M, rfl⟩
      rw [hpair] at hσ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
      rcases hσ with h | h
      · exact absurd h hg₂ne
      · exact h
    rw [hAg] at hmemg
    have hfix := (mem_fixV.mp (commSub_eq_bot_iff.mp hcomm.2 hw₀)) (g₂ * a * g₂⁻¹) hmemg
    calc a (g₂⁻¹ w₀) = g₂⁻¹ ((g₂ * a * g₂⁻¹) w₀) := by simp [MulAut.mul_apply]
      _ = g₂⁻¹ w₀ := by rw [hfix]

theorem s1614e3_case9_frame (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h9 : Case168_9 D ⊥ V hV L) :
    ∃ Z : Subgroup (MulAut (Vtil ⊥ V hV)),
      Z ≤ Mbar D.M ⊥ V hV ∧
      Nat.card ↥Z = 7 ∧
      (∀ x ∈ Mbar D.M ⊥ V hV, Z.map (MulAut.conj x).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ l ∈ lBar ⊥ V hV L, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ wTil ⊥ V hV L, z w ∈ wTil ⊥ V hV L) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ wTil ⊥ V hV L, z w ≠ w) ∧
      (∀ x ∈ Mbar D.M ⊥ V hV, (wTil ⊥ V hV L).map x.toMonoidHom = wTil ⊥ V hV L →
        (lBar ⊥ V hV L).map (MulAut.conj x).toMonoidHom = lBar ⊥ V hV L) := by
  have hv1 : v1Sub D.M ⊥ V hV L = ⊥ := s16c167_v1Sub_eq_bot_of_case9 D hV rfl h9
  have hS : Setting16 D ⊥ V L := hc.setting
  obtain ⟨⟨e₀⟩, hL3, hs15, hsum, -⟩ := h9
  have e : ↥(fstarBar D.M ⊥ V hV) ≃*
      (Multiplicative (ZMod 7) × ↥(lBar ⊥ V hV L) × ↥(lBar ⊥ V hV L)) := e₀
  have hL : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  obtain ⟨hind0', hsup0'⟩ := s16t_case9_directSum D h1217 hV hS.hyp151 hv1 hc.ne_bot
  have hrk0 : rk ↥(wTil ⊥ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 18 :=
    s16t_case9_rk_top D h1217 hV hS.hyp151 hv1 hc.ne_bot hs15 hsum
  have hn2 : (conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind0' hsup0' hrk0 hrktop
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts (Mbar D.M ⊥ V hV)
  have hSC := s16c167_isPSL_simpleCentreless hL
  have hperf := s16c167_isPSL_isPerfect hL
  have hout := s16c167_isPSL_outer_solvable hL
  have hev := s16c167_isPSL_even_card hL
  have hOutF : Group.IsSolvable (Outer ↥(Fstar (Mbar D.M ⊥ V hV))) :=
    s16c167_frame_outer_cyclic_square_solvable hSC hperf hout e
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hS.hyp151.le
  have hLF : lBar ⊥ V hV L ≤ Fstar (Mbar D.M ⊥ V hV) :=
    s16c167_frame_le_of_perfect hFX hLX hFn hself hOutF hperf
  have hZcard : Nat.card ↥((Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
      (Fstar (Mbar D.M ⊥ V hV)).subtype) = 7 := by
    rw [s16c167_frame_centerF_card (F := Fstar (Mbar D.M ⊥ V hV)) hSC.center e,
      Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hZconj := s16c167_frame_centerF_conj (X := Mbar D.M ⊥ V hV)
    (F := Fstar (Mbar D.M ⊥ V hV)) hFn
  have hZM : (Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
      (Fstar (Mbar D.M ⊥ V hV)).subtype ≤ Mbar D.M ⊥ V hV :=
    (Subgroup.map_subtype_le _).trans hFX
  refine ⟨(Subgroup.center ↥(Fstar (Mbar D.M ⊥ V hV))).map
    (Fstar (Mbar D.M ⊥ V hV)).subtype, hZM, hZcard, hZconj, ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    exact (s16c167_frame_mem_centerF.1 hz).2 l (hLF hl)
  · intro z hz w hw
    refine commSub_top_stable151b (X := lBar ⊥ V hV L) (g := z) (fun x hx => ?_) w hw
    have h1 : x * z = z * x := ((s16c167_frame_mem_centerF.1 hz).2 x (hLF hx)).symm
    have h2 : z * x * z⁻¹ = x := by rw [← h1]; group
    rw [h2]
    exact hx
  · exact s16c167_frame_faithful_of_conj_sup (p := 7) (by norm_num) hZcard hZconj
      (U := wTil ⊥ V hV L) (X := Mbar D.M ⊥ V hV) hsup0'
  · intro x hx hstab
    have hmem : lBar ⊥ V hV L ∈ {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
        ∃ φ ∈ Mbar D.M ⊥ V hV,
          Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨1, (Mbar D.M ⊥ V hV).one_mem, by ext y; simp⟩
    have hstab' : (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)).map
        x.toMonoidHom = commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L) := by
      show (wTil ⊥ V hV L).map x.toMonoidHom = wTil ⊥ V hV L
      exact hstab
    exact s16c167_normalizes_of_stab (X := Mbar D.M ⊥ V hV) (L := lBar ⊥ V hV L)
      hcls hn2 (lBar ⊥ V hV L) hmem x hx hstab'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
