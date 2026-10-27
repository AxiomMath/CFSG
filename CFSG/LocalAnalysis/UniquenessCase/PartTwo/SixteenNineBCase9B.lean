module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Generic

variable {T : Type} [CommGroup T]

private def s16n9bCase9Com (φ : MulAut T) : T →* T where
  toFun t := φ t * t⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

private theorem s16n9bCase9Com_apply (φ : MulAut T) (t : T) :
    s16n9bCase9Com φ t = φ t * t⁻¹ := rfl

private theorem s16n9bCase9Com_ker (φ : MulAut T) :
    (s16n9bCase9Com φ).ker = fixV (Subgroup.zpowers φ) := by
  ext t
  rw [MonoidHom.mem_ker, s16n9bCase9Com_apply, mul_inv_eq_one, mem_fixV_zpowers_iff_apply]

private theorem s16n9b_case9_mQuot_eq_rk_image [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (W : Subgroup T) (φ : MulAut T) :
    E3.mQuot W (W ⊓ fixV (Subgroup.zpowers φ)) =
      rk ↥(W.map (s16n9bCase9Com φ)) := by
  have h1 := rk_map_add_rk_inf_ker (s16n9bCase9Com φ) W
  rw [s16n9bCase9Com_ker] at h1
  have h2 : E3.mQuot W (W ⊓ fixV (Subgroup.zpowers φ)) +
      rk ↥(W ⊓ fixV (Subgroup.zpowers φ)) = rk ↥W := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hT).to_subgroup W)
      (inf_le_left : W ⊓ fixV (Subgroup.zpowers φ) ≤ W)
    rw [card_eq_two_pow hT, card_eq_two_pow hT, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh.symm
  omega

private theorem s16n9b_case9_mQuot_le_rk_commSub [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    (W : Subgroup T) (φ : MulAut T) :
    E3.mQuot W (W ⊓ fixV (Subgroup.zpowers φ)) ≤ rk ↥(commSub W (Subgroup.zpowers φ)) := by
  rw [s16n9b_case9_mQuot_eq_rk_image hT W φ]
  apply rk_mono (G := T)
  rintro _ ⟨w, hw, rfl⟩
  exact Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, w, hw, rfl⟩

private theorem s16n9b_case9_commV_le_range (φ : MulAut T) :
    commV (Subgroup.zpowers φ) ≤ (s16n9bCase9Com φ).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have key : ∀ n : ℤ, ∀ v : T, (φ ^ n) v * v⁻¹ ∈ (s16n9bCase9Com φ).range := by
    intro n
    induction n using Int.induction_on with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      have hs : (φ ^ ((k : ℤ) + 1)) v = φ ((φ ^ (k : ℤ)) v) := by
        rw [add_comm, zpow_one_add]
        rfl
      have h1 : (φ ^ ((k : ℤ) + 1)) v * v⁻¹ =
          s16n9bCase9Com φ ((φ ^ (k : ℤ)) v) * ((φ ^ (k : ℤ)) v * v⁻¹) := by
        rw [hs, s16n9bCase9Com_apply]
        group
      rw [h1]
      exact (s16n9bCase9Com φ).range.mul_mem ⟨_, rfl⟩ (ih v)
    | pred k ih =>
      intro v
      have hs : (φ ^ (-(k : ℤ))) v = φ ((φ ^ (-(k : ℤ) - 1)) v) := by
        have : (φ ^ (-(k : ℤ))) = φ * φ ^ (-(k : ℤ) - 1) := by
          rw [← zpow_one_add]; congr 1; ring
        rw [this]
        rfl
      have h1 : (φ ^ (-(k : ℤ) - 1)) v * v⁻¹ =
          (s16n9bCase9Com φ ((φ ^ (-(k : ℤ) - 1)) v))⁻¹ * ((φ ^ (-(k : ℤ))) v * v⁻¹) := by
        rw [hs, s16n9bCase9Com_apply]
        group
      rw [h1]
      exact (s16n9bCase9Com φ).range.mul_mem ((s16n9bCase9Com φ).range.inv_mem ⟨_, rfl⟩) (ih v)
  exact key n v

private theorem s16n9b_case9_rk_commV_le [Finite T] (φ : MulAut T) :
    rk (commV (Subgroup.zpowers φ)) ≤ rkIdx (fixV (Subgroup.zpowers φ)) := by
  have h1 : rk (commV (Subgroup.zpowers φ)) ≤ rk (s16n9bCase9Com φ).range :=
    rk_mono (s16n9b_case9_commV_le_range φ)
  have h2 : rkIdx (fixV (Subgroup.zpowers φ)) = rk (s16n9bCase9Com φ).range := by
    unfold rkIdx rk
    rw [← s16n9bCase9Com_ker, Subgroup.index_ker]
  omega

private theorem s16n9b_case9_map_conj_map_conj (A : Subgroup (MulAut T)) (x y : MulAut T) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem s16n9b_case9_map_conj_one (A : Subgroup (MulAut T)) :
    A.map (MulAut.conj (1 : MulAut T)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

private theorem s16n9b_case9_rk_map (e : MulAut T) (U : Subgroup T) :
    rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  unfold rk
  rw [Subgroup.card_map_of_injective e.injective]

private theorem s16n9b_case9_rk_le_commV [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {W : Subgroup T} {φ : MulAut T} (hinj : ∀ w ∈ W, φ w = w → w = 1) :
    rk ↥W ≤ rk ↥(commV (Subgroup.zpowers φ)) := by
  have hmem : ∀ w : W, s16n9bCase9Com φ (w : T) ∈ commV (Subgroup.zpowers φ) := fun w =>
    Subgroup.subset_closure ⟨φ, Subgroup.mem_zpowers φ, (w : T), rfl⟩
  let f : ↥W →* ↥(commV (Subgroup.zpowers φ)) :=
    ((s16n9bCase9Com φ).comp W.subtype).codRestrict _ hmem
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : s16n9bCase9Com φ (w : T) = 1 := congrArg Subtype.val hw
    rw [s16n9bCase9Com_apply, mul_inv_eq_one] at h1
    exact Subtype.ext (hinj w w.2 h1)
  have hcard : Nat.card ↥W ≤ Nat.card ↥(commV (Subgroup.zpowers φ)) :=
    Nat.card_le_card_of_injective f hf
  rw [card_eq_two_pow hT W, card_eq_two_pow hT] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

theorem s16n9b_case9_commV_le_of_fix {W W' : Subgroup T} (hsup : W ⊔ W' = ⊤)
    {φ : MulAut T} (hfix : ∀ w ∈ W, φ w = w) (hinv : φ ∈ stabSub W') :
    commV (Subgroup.zpowers φ) ≤ W' := by
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

theorem s16n9b_case9_mem_stabSub_of_map_eq {W : Subgroup T} {φ : MulAut T}
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

structure s16n9b_case9Two (M A : Subgroup (MulAut T)) (g : MulAut T) : Prop where
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

@[expose] def s16n9b_case9Rank (M A : Subgroup (MulAut T)) (r : ℕ) : Prop :=
  ∀ φ ∈ M, (∃ a : ℕ, orderOf φ = 2 ^ a) → A.map (MulAut.conj φ).toMonoidHom = A →
    (∀ w ∈ commSub ⊤ A, φ w = w) ∨ r ≤ rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers φ))

theorem s16n9b_case9_two_invFix [Finite T] (hT : ∀ t : T, t ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : s16n9b_case9Two M A g) {p N r : ℕ} (hN : N < rk ↥(commSub ⊤ A))
    (hr : N < 2 * r) (hp : ∃ a ∈ A, orderOf a = p) (hrank : s16n9b_case9Rank M A r) :
    s16n9bInvFix M p N := by
  obtain ⟨a₀, ha₀A, ha₀p⟩ := hp
  intro φ hφM hφ2 hrk z hz hz1
  have hcomm_le : rk ↥(commV (Subgroup.zpowers φ)) ≤ N :=
    (s16n9b_case9_rk_commV_le φ).trans hrk
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
    have := s16n9b_case9_rk_le_commV hT hinj
    omega
  have hWφ : (commSub ⊤ A).map φ.toMonoidHom = commSub ⊤ A := by
    rw [← s15_Infra_commSub_top_map_conj A φ, hA]
  have hBφ : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom := by
    rw [s16n9b_case9_map_conj_map_conj]
    rcases h.conj (φ * g) (M.mul_mem hφM h.mem) with h1 | h1
    · exfalso
      apply h.ne
      have h2 : A.map (MulAut.conj φ⁻¹).toMonoidHom = A := by
        have := congrArg (fun X : Subgroup (MulAut T) =>
          X.map (MulAut.conj φ⁻¹).toMonoidHom) hA
        simp only [s16n9b_case9_map_conj_map_conj, inv_mul_cancel,
          s16n9b_case9_map_conj_one] at this
        exact this.symm
      calc A.map (MulAut.conj g).toMonoidHom
          = (A.map (MulAut.conj (φ * g)).toMonoidHom).map
              (MulAut.conj φ⁻¹).toMonoidHom := by
            rw [s16n9b_case9_map_conj_map_conj, inv_mul_cancel_left]
        _ = A.map (MulAut.conj φ⁻¹).toMonoidHom := by rw [h1]
        _ = A := h2
    · exact h1
  have hW'φ : ((commSub ⊤ A).map g.toMonoidHom).map φ.toMonoidHom =
      (commSub ⊤ A).map g.toMonoidHom := by
    rw [← hgB, ← s15_Infra_commSub_top_map_conj _ φ, hBφ]
  have hstW : φ ∈ stabSub (commSub ⊤ A) := s16n9b_case9_mem_stabSub_of_map_eq hWφ
  have hstW' : φ ∈ stabSub ((commSub ⊤ A).map g.toMonoidHom) :=
    s16n9b_case9_mem_stabSub_of_map_eq hW'φ
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
      rw [hφ']
      simp only [mul_assoc]
      rw [← s16n9b_case9_map_conj_map_conj A (φ * g) g⁻¹,
        ← s16n9b_case9_map_conj_map_conj A g φ]
    rw [e1, hBφ, s16n9b_case9_map_conj_map_conj, inv_mul_cancel, s16n9b_case9_map_conj_one]
  have hφ'W : ∀ w ∈ commSub ⊤ A, φ (g w) = g (φ' w) := by
    intro w _
    rw [hφ']
    simp [MulAut.mul_apply]
  have hr1 := hrank φ hφM hφ2 hA
  have hr2 := hrank φ' hφ'M hφ'2 hAφ'
  rcases hr1 with hfixW | hrW
  ·
    have hle : commV (Subgroup.zpowers φ) ≤ (commSub ⊤ A).map g.toMonoidHom :=
      s16n9b_case9_commV_le_of_fix h.sup hfixW hstW'
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
      s16n9b_case9_commV_le_of_fix hsup' hfixW'' hstW
    refine ⟨(MulAut.conj g) a₀, ?_, ?_, ?_⟩
    · simp only [MulAut.conj_apply]
      exact M.mul_mem (M.mul_mem h.mem (h.le ha₀A)) (M.inv_mem h.mem)
    · rw [← ha₀p]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a₀
    · exact h.fixB _ (Subgroup.mem_map.2 ⟨a₀, ha₀A, rfl⟩) z (hle hz)
  ·
    exfalso
    have hrW_rk : r ≤ rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers φ)) := hrW
    have hrW'_rk : r ≤ rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers φ')) := hrW'
    have hrW'' : r ≤ rk ↥(commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ)) := by
      have e1 := s15_Core_commSub_map_conj (commSub ⊤ A) (Subgroup.zpowers φ') g
      have e2 : (Subgroup.zpowers φ').map (MulAut.conj g).toMonoidHom = Subgroup.zpowers φ := by
        rw [MonoidHom.map_zpowers]
        refine congrArg Subgroup.zpowers ?_
        change g * φ' * g⁻¹ = φ
        rw [hφ']
        group
      rw [e2] at e1
      rw [e1, s16n9b_case9_rk_map]
      exact hrW'_rk
    have hU1 : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ≤ commSub ⊤ A :=
      commSub_le_of_invariant fun x hx w hw =>
        (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW hx) w).2 hw
    have hU2 : commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ) ≤
        (commSub ⊤ A).map g.toMonoidHom :=
      commSub_le_of_invariant fun x hx w hw =>
        (mem_stabSub.1 ((Subgroup.zpowers_le).2 hstW' hx) w).2 hw
    have hbot : commSub (commSub ⊤ A) (Subgroup.zpowers φ) ⊓
        commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf hU1 hU2).trans h.inf.le)
    have hsum := rk_sup_add_rk_inf (commSub (commSub ⊤ A) (Subgroup.zpowers φ))
      (commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ))
    rw [hbot, rk_bot, add_zero] at hsum
    have hle : rk ↥(commSub (commSub ⊤ A) (Subgroup.zpowers φ) ⊔
        commSub ((commSub ⊤ A).map g.toMonoidHom) (Subgroup.zpowers φ)) ≤
        rk ↥(commV (Subgroup.zpowers φ)) :=
      rk_mono (by
        rw [commV_eq_commSub]
        exact sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl))
    omega

end Generic

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case9_isPSL_of_isL3 {X : Type} [Group X] (h : IsL3 X 1) :
    IsPSL 3 2 1 X := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals exact absurd h0 (by norm_num)

private theorem s16n9b_case9_eq_pair_of_ncard_two {α : Type*} {s : Set α} {a b : α}
    (hs : s.ncard = 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  obtain ⟨Y₁, Y₂, -, hYset⟩ := Set.ncard_eq_two.1 hs
  rw [hYset] at ha hb ⊢
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha, ← hb]
  · rw [← ha, ← hb, Set.pair_comm]
  · exact absurd (ha.trans hb.symm) hab

theorem s16n9b_case9_rank (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h9 : Case168_9 D V₀ V hV L) :
    s16n9b_case9Rank (Mbar D.M V₀ V hV) (lBar V₀ V hV L) 3 := by
  intro φ hφM hφ2 hφA
  obtain ⟨Z, hZcard, hZnorm, hZL, hZJ, hZf, -⟩ := s16n9b_case9_frame D h1217 hV hc hV0 h9
  obtain ⟨-, hL3, -, hsum, -⟩ := h9
  have hL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  have hJ : NatSum3 (lBar V₀ V hV L) (wTil V₀ V hV L) := s16c167_natSum3_of_sumOfNat hsum
  have hWv : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  obtain ⟨a, ha⟩ := hφ2
  have hφpow : φ ^ 2 ^ a = 1 := by rw [← ha]; exact pow_orderOf_eq_one φ
  have hφZ : Z.map (MulAut.conj φ).toMonoidHom = Z := hZnorm φ hφM
  have hφW : (wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV L := by
    show (commSub ⊤ (lBar V₀ V hV L)).map φ.toMonoidHom = commSub ⊤ (lBar V₀ V hV L)
    rw [← s15_Infra_commSub_top_map_conj (lBar V₀ V hV L) φ, hφA]
  obtain ⟨⟨l, hl, hxl⟩, -⟩ :=
    s16c167_natSum3_normalizer_two hWv hL hJ hZcard hZL hZJ hZf hφpow hφZ hφA hφW
  by_cases hl1 : l = 1
  · left
    intro w hw
    simpa [hl1] using hxl w hw
  · right
    have h3 := s16n9b_natSum3_comm_rank hWv hL hJ hl hl1
    have hfix : wTil V₀ V hV L ⊓ fixV (Subgroup.zpowers l) =
        wTil V₀ V hV L ⊓ fixV (Subgroup.zpowers φ) := by
      ext w
      rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_fixV_zpowers l w, mem_fixV_zpowers φ w]
      constructor
      · rintro ⟨hw, hlw⟩
        exact ⟨hw, (hxl w hw).trans hlw⟩
      · rintro ⟨hw, hφw⟩
        exact ⟨hw, (hxl w hw).symm.trans hφw⟩
    have h3' : 3 ≤ E3.mQuot (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (Subgroup.zpowers φ)) := by
      rw [← hfix]
      exact h3
    exact h3'.trans (s16n9b_case9_mQuot_le_rk_commSub hWv (wTil V₀ V hV L) φ)

theorem s16n9b_case9_two (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h9 : Case168_9 D V₀ V hV L) :
    ∃ g : MulAut (Vtil V₀ V hV),
      s16n9b_case9Two (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g := by
  classical
  have hS : Setting16 D V₀ V L := hc.setting
  have hH : Hyp151 D V₀ V L := hS.hyp151
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  obtain ⟨g₂, hg₂M, hg₂ne⟩ : ∃ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar V₀ V hV L := by
    by_contra hcon
    have hsingle : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {lBar V₀ V hV L} := by
      ext Y
      constructor
      · rintro ⟨φ, hφM, rfl⟩
        by_contra hne
        exact hcon ⟨φ, hφM, hne⟩
      · rintro rfl
        exact ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    rw [hsingle] at hcls
    simp at hcls
  obtain ⟨x, hxM, hxg₂⟩ := (mem_barSub V₀ V hV D.M g₂).1 hg₂M
  have hgne : (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom ≠ lBar V₀ V hV L := by
    intro h
    apply hg₂ne
    have h' := congrArg (fun X : Subgroup (MulAut (Vtil V₀ V hV)) =>
      X.map (MulAut.conj g₂).toMonoidHom) h
    rw [s16n9b_case9_map_conj_map_conj, mul_inv_cancel, s16n9b_case9_map_conj_one] at h'
    exact h'.symm
  have hgM : g₂⁻¹ ∈ Mbar D.M V₀ V hV := (Mbar D.M V₀ V hV).inv_mem hg₂M
  have hconjinv : ((MulAut.conj g₂)⁻¹).toMonoidHom =
      (MulAut.conj g₂⁻¹).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply]
  have hbar : barSub V₀ V hV (conjSubgroup L (x : G)) =
      (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV x.2 L, hxg₂]
    exact congrArg (fun f : MulAut (Vtil V₀ V hV) →* MulAut (Vtil V₀ V hV) =>
      (barSub V₀ V hV L).map f) hconjinv
  have hxnbar : (x : G) ∉ nBar D.M V₀ V hV L := by
    intro hx
    rw [s15_Infra_mem_nBar_iff hS.hyp16.hyp125 hV hxM] at hx
    rw [hbar] at hx
    exact hgne hx
  have hcomm := hH.commute (x : G) hxM hxnbar
  rw [hbar] at hcomm
  have hABne : lBar V₀ V hV L ≠
      (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := fun h => hgne h.symm
  have hpair : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} =
      {lBar V₀ V hV L, (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom} :=
    s16n9b_case9_eq_pair_of_ncard_two hcls
      ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩ ⟨g₂⁻¹, hgM, rfl⟩ hABne
  have hrk0 : rk ↥(wTil V₀ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
    s16n9b_case9_rk_top D h1217 hV hH hV0 hc.ne_bot hs15 hsum
  obtain ⟨hind, hsup⟩ := s16n9b_case9_directSum D h1217 hV hH hV0 hc.ne_bot
  have hn2 : (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrktop
  have hWmem : (wTil V₀ V hV L) ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) :=
    ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
  have hW'mem : (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom ∈
      conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) := ⟨g₂⁻¹, hgM, rfl⟩
  have hWne : (wTil V₀ V hV L) ≠ (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom := by
    intro h
    apply hgne
    have hmem : lBar V₀ V hV L ∈ {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    have hstab : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)).map
        g₂⁻¹.toMonoidHom = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) := by
      show (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom = wTil V₀ V hV L
      exact h.symm
    exact s16c167_normalizes_of_stab hcls hn2 (lBar V₀ V hV L) hmem g₂⁻¹ hgM hstab
  have hpairW : conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) =
      {wTil V₀ V hV L, (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom} :=
    s16n9b_case9_eq_pair_of_ncard_two hn2 hWmem hW'mem hWne
  have hdisj : wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom = ⊥ :=
    disjoint_iff.mp ((sSupIndep_pair hWne).mp (hpairW ▸ hind))
  have hsup' : wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom = ⊤ := by
    have h := hpairW ▸ hsup
    rwa [sSup_pair] at h
  refine ⟨g₂⁻¹, ⟨barSub_mono V₀ V hV hH.le, hgM, hgne, hcomm.1, ?_, ?_, ?_, hdisj, hsup'⟩⟩
  · intro φ hφM
    have hmem : (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        ({lBar V₀ V hV L, (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom} :
          Set (Subgroup (MulAut (Vtil V₀ V hV)))) := by
      rw [← hpair]
      exact ⟨φ, hφM, rfl⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro b hb w hw
    have hle : wTil V₀ V hV L ≤
        fixV ((lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom) :=
      commSub_eq_bot_iff.mp hcomm.2
    exact (mem_fixV.mp (hle hw)) b hb
  · intro a ha w hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    have hmemg : g₂ * a * g₂⁻¹ ∈ (lBar V₀ V hV L).map (MulAut.conj g₂).toMonoidHom :=
      Subgroup.mem_map.2 ⟨a, ha, rfl⟩
    have hAg : (lBar V₀ V hV L).map (MulAut.conj g₂).toMonoidHom =
        (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
      have hσ : (lBar V₀ V hV L).map (MulAut.conj g₂).toMonoidHom ∈
          {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
            ∃ φ ∈ Mbar D.M V₀ V hV,
              Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
