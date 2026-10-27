module

public import CFSG.Quasithin.Background.B3ThreeCore
public import CFSG.Quasithin.EmptyFaithful.S143LB

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.Quasithin.B3 CFSG.Quasithin.S143

theorem zmod_two_add_self_gc (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem n6ToV_act_perm (σ : Equiv.Perm (Fin 6)) (a : N6) :
    n6ToV (n6Act σ a) = Mod.act 6 Mod.ut0 σ (n6ToV a) := by
  rw [n6ToV_apply, n6ToV_apply, act_pi6, pi6_eq_iff]
  refine esub_of_const _ _ (Multiplicative.toAdd a.1 (σ⁻¹ 5)) fun i => ?_
  show Multiplicative.toAdd a.1 (σ.symm i) = Multiplicative.toAdd (n6Act σ a).1 i + _
  rw [n6Act_val]
  show _ = Multiplicative.toAdd a.1 (σ⁻¹ i) + Multiplicative.toAdd a.1 (σ⁻¹ 5) +
    Multiplicative.toAdd a.1 (σ⁻¹ 5)
  rw [add_assoc, zmod_two_add_self_gc, add_zero]
  rfl

@[expose] def cK : Mod → ℕ
  | .u0 => 2
  | _ => 1

@[expose] noncomputable def projK : (k : Mod) → Mod.V 6 k →* Mod.V 6 Mod.ut0
  | .u0 => projU0 6
  | .ut0 => MonoidHom.id _
  | .u => 1
  | .ut => 1

theorem cK_pos {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) : 0 < cK k := by
  rcases hk with rfl | rfl <;> decide

theorem projK_surjective {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) :
    Function.Surjective (projK k) := by
  rcases hk with rfl | rfl
  · exact Function.surjective_id
  · exact projU0_surjective

theorem projU0_act (σ : Gp 6) (w : Mod.V 6 Mod.u0) :
    projU0 6 (Mod.act 6 Mod.u0 σ w) = Mod.act 6 Mod.ut0 σ (projU0 6 w) :=
  incl_act u0_le_ut0 u0_N_le σ w

theorem projK_act {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (σ : Gp 6) (w : Mod.V 6 k) :
    projK k (Mod.act 6 k σ w) = Mod.act 6 Mod.ut0 σ (projK k w) := by
  rcases hk with rfl | rfl
  · rfl
  · exact projU0_act σ w

theorem act_c0 (σ : Gp 6) :
    Mod.act 6 Mod.u0 σ (c0 6 (by norm_num)) = c0 6 (by norm_num) := by
  show Mod.act 6 Mod.u0 σ (QuotientGroup.mk ⟨eVec 6, eVec_mem_U0_iff.2 (by norm_num)⟩) = _
  rw [act_mk]
  congr 1

theorem card_ker_projK {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) :
    Nat.card (projK k).ker = cK k := by
  rcases hk with rfl | rfl
  · show Nat.card (MonoidHom.id (Mod.V 6 Mod.ut0)).ker = 1
    rw [MonoidHom.ker_id, Subgroup.card_bot]
  · show Nat.card (projU0 6).ker = 2
    rw [Nat.card_eq_two_iff' (1 : (projU0 6).ker)]
    refine ⟨⟨c0 6 (by norm_num), c0_mem_ker (by norm_num)⟩, ?_, ?_⟩
    · intro h
      exact c0_ne_one (by norm_num) (by norm_num) (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩ hne
      rcases projU0_ker (hn := by norm_num) hy with h | h
      · exact absurd (Subtype.ext h) hne
      · exact Subtype.ext h

theorem ker_projK_le_fixV {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (K : Subgroup (Gp 6)) :
    (projK k).ker ≤ fixV (K.map (Mod.act 6 k)) := by
  rcases hk with rfl | rfl
  · have : (projK Mod.ut0).ker = ⊥ := MonoidHom.ker_id
    rw [this]
    exact bot_le
  · intro x hx
    rintro _ ⟨σ, -, rfl⟩
    rcases projU0_ker (hn := by norm_num) hx with rfl | rfl
    · exact map_one _
    · exact act_c0 σ

theorem sum_eq_one_of_shift {σ : Equiv.Perm (Fin 6)} {f : Fin 6 → ZMod 2}
    (h : ∀ i, f (σ i) = f i + 1) : ∑ i, f i = 1 := by
  have hg : ∀ i, (f (σ i)).val + (f i).val = 1 := fun i => by
    have := h i
    generalize f (σ i) = a at this
    generalize f i = b at this
    revert a b
    decide
  have h1 : ∑ i, (f (σ i)).val = ∑ i, (f i).val := Equiv.sum_comp σ (fun i => (f i).val)
  have h2 : ∑ i, ((f (σ i)).val + (f i).val) = 6 := by
    rw [Finset.sum_congr rfl (fun i _ => hg i)]
    simp
  rw [Finset.sum_add_distrib, h1] at h2
  have h3 : ∑ i, (f i).val = 3 := by omega
  have h4 : (∑ i, f i) = ((∑ i, (f i).val : ℕ) : ZMod 2) := by
    rw [Nat.cast_sum]
    simp
  rw [h4, h3]
  decide

theorem permAct_mul_inv_ne_eVec (σ : Gp 6) {w : U 6} (hw : w ∈ U0 6) :
    permAct 6 σ w * w⁻¹ ≠ eVec 6 := by
  intro h
  have hs : ∀ i, w.val (σ.symm i) = w.val i + 1 := fun i => by
    have h1 := congrArg (fun z : U 6 => z.val i) h
    simp only [U.val_mul, U.val_inv, permAct_val, eVec] at h1
    calc w.val (σ.symm i) = (w.val (σ.symm i) + -w.val i) + w.val i :=
          (neg_add_cancel_right _ _).symm
      _ = 1 + w.val i := by rw [h1]
      _ = w.val i + 1 := add_comm _ _
  have h2 : ∑ i, w.val i = 1 := by
    have := sum_eq_one_of_shift (σ := σ.symm) (f := w.val) fun i => hs i
    exact this
  have h3 : ∑ i, w.val i = 0 := by
    have h1 : wt 6 w = 1 := hw
    have h2 : wt 6 w = Multiplicative.ofAdd (∑ i, w.val i) := rfl
    rw [h2] at h1
    exact ofAdd_eq_one.1 h1
  rw [h3] at h2
  exact absurd h2 (by decide)

theorem act_u0_mul_inv_ne_c0 (σ : Gp 6) (w : Mod.V 6 Mod.u0) :
    Mod.act 6 Mod.u0 σ w * w⁻¹ ≠ c0 6 (by norm_num) := by
  induction w using QuotientGroup.induction_on with
  | H w =>
    intro h
    rw [act_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h
    have h2 := QuotientGroup.eq.1 h
    apply permAct_mul_inv_ne_eVec σ w.2
    have h3 : (permAct 6 σ (w : U 6) * (w : U 6)⁻¹)⁻¹ * eVec 6 = 1 := Subgroup.mem_bot.1 h2
    exact inv_mul_eq_one.1 h3

theorem fixV_map_projK {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (K : Subgroup (Gp 6)) :
    (fixV (K.map (Mod.act 6 k))).map (projK k) = fixV (K.map (Mod.act 6 Mod.ut0)) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ _ ⟨σ, hσ, rfl⟩
    rw [← projK_act hk]
    exact congrArg (projK k) (hw _ (Subgroup.mem_map_of_mem _ hσ))
  · intro hv
    obtain ⟨w, rfl⟩ := projK_surjective hk v
    refine ⟨w, ?_, rfl⟩
    rintro _ ⟨σ, hσ, rfl⟩
    have h1 := hv _ (Subgroup.mem_map_of_mem _ hσ)
    rcases hk with rfl | rfl
    · exact h1
    · have h2 : projU0 6 (Mod.act 6 Mod.u0 σ w * w⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have : projU0 6 (Mod.act 6 Mod.u0 σ w) = projU0 6 w := (projU0_act σ w).trans h1
        rw [this, mul_inv_cancel]
      rcases projU0_ker (hn := by norm_num) h2 with h | h
      · exact mul_inv_eq_one.1 h
      · exact absurd h (act_u0_mul_inv_ne_c0 σ w)

theorem card_map_mul_card_ker {G H : Type*} [Group G] [Group H] (f : G →* H) (A : Subgroup G)
    (h : f.ker ≤ A) : Nat.card (A.map f) * Nat.card f.ker = Nat.card A := by
  have h1 := Subgroup.card_ker_mul_card_range (f.domRestrict A)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h1
  have h2 : Nat.card ↥(f.ker.subgroupOf A) = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [h2, mul_comm] at h1
  exact h1

theorem card_modV_ut0 : Nat.card (Mod.V 6 Mod.ut0) = 16 := by
  rw [← Nat.card_congr n6ModEquiv.toEquiv, n6_card]

theorem card_modV {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) :
    Nat.card (Mod.V 6 k) = 16 * cK k := by
  have h := Subgroup.card_ker_mul_card_of_surjective (projK_surjective hk)
  rw [card_ker_projK hk, card_modV_ut0] at h
  rw [← h, mul_comm]

theorem card_fixV_act {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (K : Subgroup (Gp 6)) :
    Nat.card (fixV (K.map (Mod.act 6 k))) =
      cK k * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) := by
  have h := card_map_mul_card_ker (projK k) (fixV (K.map (Mod.act 6 k)))
    (ker_projK_le_fixV hk K)
  rw [fixV_map_projK hk, card_ker_projK hk] at h
  rw [← h, mul_comm]

theorem rkIdx_fixV_act {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (K : Subgroup (Gp 6)) :
    rkIdx (fixV (K.map (Mod.act 6 k))) = rkIdx (fixV (K.map (Mod.act 6 Mod.ut0))) := by
  unfold rkIdx
  congr 1
  have h1 := Subgroup.index_mul_card (fixV (K.map (Mod.act 6 k)))
  have h2 := Subgroup.index_mul_card (fixV (K.map (Mod.act 6 Mod.ut0)))
  rw [card_modV hk, card_fixV_act hk] at h1
  rw [card_modV_ut0] at h2
  have hc := cK_pos hk
  have ha : 0 < Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right ha
  apply Nat.eq_of_mul_eq_mul_left hc
  calc cK k * ((fixV (K.map (Mod.act 6 k))).index * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))))
      = (fixV (K.map (Mod.act 6 k))).index *
        (cK k * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0)))) := by ring
    _ = 16 * cK k := h1
    _ = cK k * ((fixV (K.map (Mod.act 6 Mod.ut0))).index *
        Nat.card (fixV (K.map (Mod.act 6 Mod.ut0)))) := by rw [h2]; ring

theorem rk_act (k : Mod) (K : Subgroup (Gp 6)) :
    rk (K.map (Mod.act 6 k)) = rk (K.map (Mod.act 6 Mod.ut0)) := by
  unfold rk
  rw [Subgroup.card_map_of_injective (act_injective (by norm_num) k),
    Subgroup.card_map_of_injective (act_injective (by norm_num) Mod.ut0)]

theorem rAV_act {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0) (K : Subgroup (Gp 6)) :
    rAV (K.map (Mod.act 6 k)) = rAV (K.map (Mod.act 6 Mod.ut0)) := by
  unfold rAV
  rw [rkIdx_fixV_act hk, rk_act]

theorem isFFStarOffender_map_iff_inj {G W : Type*} [Group G] [CommGroup W] {f : G →* MulAut W}
    (hf : Function.Injective f) {X A : Subgroup G} :
    IsFFStarOffender (X.map f) (A.map f) ↔
      A ≤ X ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
        ∀ B : Subgroup G, B ≤ A →
          Nat.card B * Nat.card (fixV (B.map f)) ≤ Nat.card A * Nat.card (fixV (A.map f)) := by
  constructor
  · rintro ⟨h1, h2, ⟨h3, h4⟩, h5⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).1 h1, ?_, fun a ha b hb => ?_,
      fun a ha => ?_, fun B hB => ?_⟩
    · rwa [Ne, ← Subgroup.map_eq_bot_iff_of_injective A hf]
    · apply hf
      rw [map_mul, map_mul]
      exact h3 _ (Subgroup.mem_map_of_mem _ ha) _ (Subgroup.mem_map_of_mem _ hb)
    · apply hf
      rw [map_pow, map_one]
      exact h4 _ (Subgroup.mem_map_of_mem _ ha)
    · have := h5 (B.map f) (Subgroup.map_mono hB)
      rwa [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨Subgroup.map_mono h1, ?_, ⟨?_, ?_⟩, ?_⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective A hf]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, h3 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, h4 a ha, map_one]
    · intro B' hB'
      have hBmap : (A ⊓ B'.comap f).map f = B' := by
        ext y
        constructor
        · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
          exact hx2
        · intro hy
          obtain ⟨x, hx, hxy⟩ := hB' hy
          exact ⟨x, ⟨hx, by show f x ∈ B'; rw [hxy]; exact hy⟩, hxy⟩
      have := h5 (A ⊓ B'.comap f) inf_le_left
      rwa [← hBmap, Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf]

theorem isFFStarOffender_map_iff_scale {G W W' : Type*} [Group G] [CommGroup W] [CommGroup W']
    {f : G →* MulAut W} {f' : G →* MulAut W'} (hf : Function.Injective f)
    (hf' : Function.Injective f') {c : ℕ} (hc : 0 < c)
    (hfix : ∀ B : Subgroup G, Nat.card (fixV (B.map f)) = c * Nat.card (fixV (B.map f')))
    {X A : Subgroup G} :
    IsFFStarOffender (X.map f) (A.map f) ↔ IsFFStarOffender (X.map f') (A.map f') := by
  rw [isFFStarOffender_map_iff_inj hf, isFFStarOffender_map_iff_inj hf']
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  refine forall_congr' fun B => forall_congr' fun _ => ?_
  have e : ∀ p q x y : ℕ, p * (c * x) ≤ q * (c * y) ↔ p * x ≤ q * y := fun p q x y => by
    rw [show p * (c * x) = c * (p * x) by ring, show q * (c * y) = c * (q * y) by ring]
    exact Nat.mul_le_mul_left_iff hc
  rw [hfix B, hfix A]
  exact e _ _ _ _

theorem isFFStarOffender_act_iff {k : Mod} (hk : k = Mod.ut0 ∨ k = Mod.u0)
    (X A : Subgroup (Gp 6)) :
    IsFFStarOffender (X.map (Mod.act 6 k)) (A.map (Mod.act 6 k)) ↔
      IsFFStarOffender (X.map (Mod.act 6 Mod.ut0)) (A.map (Mod.act 6 Mod.ut0)) :=
  isFFStarOffender_map_iff_scale (act_injective (by norm_num) k)
    (act_injective (by norm_num) Mod.ut0) (cK_pos hk) (card_fixV_act hk)

end CFSG.Quasithin.H13.U3.GC137
