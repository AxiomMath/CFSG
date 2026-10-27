module

public import CFSG.RankThree.CentralCover.SteinbergBNVectorPairing
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open CFSG.RankThree.Classical2 CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem eq_one_of_det_neg_one {M : Type*} [Group M] {r : ℕ} [NeZero r] (hr : Odd r) {γ : M}
    (hγ : γ ^ r = 1) {a b c d : ZMod r} (hdet : a * d - b * c = -1)
    (h : γ = (γ ^ d.val) ^ a.val * ((γ⁻¹) ^ b.val) ^ c.val) : γ = 1 := by
  rw [← pow_mul, ← pow_mul, inv_pow] at h
  have h1 : γ * γ ^ (b.val * c.val) = γ ^ (d.val * a.val) := by
    rw [eq_mul_inv_iff_mul_eq] at h
    exact h
  have hmod : (d.val * a.val + 1) % r = (b.val * c.val) % r := by
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    linear_combination hdet
  have h2 : γ ^ (d.val * a.val + 1) = γ ^ (b.val * c.val) := by
    rw [pow_eq_pow_mod _ hγ, hmod, ← pow_eq_pow_mod _ hγ]
  have h3 : γ ^ (b.val * c.val) * γ ^ 2 = γ ^ (b.val * c.val) * 1 := by
    calc γ ^ (b.val * c.val) * γ ^ 2 = (γ * γ ^ (b.val * c.val)) * γ := by group
      _ = γ ^ (d.val * a.val) * γ := by rw [h1]
      _ = γ ^ (d.val * a.val + 1) := (pow_succ _ _).symm
      _ = γ ^ (b.val * c.val) := h2
      _ = γ ^ (b.val * c.val) * 1 := (mul_one _).symm
  have h4 : γ ^ 2 = 1 := mul_left_cancel h3
  exact CFSG.RankThree.Classical2.eq_one_of_sq_eq_one_of_pow_eq_one hr h4 hγ

theorem four_dimensional_normalizer_actual_central_cover_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {H : Type*} [Group H] (φ : Y →* H) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod r) V] (e : Multiplicative V →* H)
    (he : Function.Injective e) (hV : Nat.card V = r ^ 4)
    (Dm Dp W : Submodule (ZMod r) V) (hsum : Dm ⊔ Dp ⊔ W = ⊤)
    (_hind : Disjoint Dm (Dp ⊔ W) ∧ Disjoint Dp W)
    (hDm : Module.finrank (ZMod r) Dm = 1) (hDp : Module.finrank (ZMod r) Dp = 1)
    (hW : Module.finrank (ZMod r) W = 2) (σ : V →ₗ[ZMod r] V)
    (hσm : ∀ v ∈ Dm, σ v = -v) (hσp : ∀ v ∈ Dp, σ v = v) (hσW : ∀ v ∈ W, σ v ∈ W)
    (hdet : LinearMap.det (σ.restrict hσW) = -1) (hTm : IsUnit (σ.restrict hσW - 1))
    (hTp : IsUnit (σ.restrict hσW + 1)) {n : H}
    (hn : ∀ v, n * e (.ofAdd v) * n⁻¹ = e (.ofAdd (σ v))) {z : H} (hz : orderOf z = 2)
    (hzD : ∀ v, Commute z (e (.ofAdd v))) :
    (∀ x ∈ e.range.comap φ, ∀ y ∈ e.range.comap φ, x * y = y * x) ∧
      ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
        IsElemAbelian r A ∧ Nat.card A = r ^ 4 ∧
        IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) ∧ 4 ≤ localRank r G := by
  classical
  have hodd : Odd r := hr.out.odd_of_ne_two hr2
  have hpow : ∀ v : V, e (.ofAdd v) ^ r = 1 := fun v => by
    rw [← map_pow, ← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod r), ZMod.natCast_self,
      zero_smul, ofAdd_zero, map_one]
  have hβr : ∀ v w : V, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) ^ r = 1 := fun v w => by
    rw [← liftComm_pow_left hφ hker (commute_map_ofAdd e v w), hpow, liftComm_one_left hφ hker]
  have hinv : ∀ v w : V, liftComm φ hφ (e (.ofAdd (σ v))) (e (.ofAdd (σ w))) =
      liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) := fun v w => by
    rw [← hn, ← hn, liftComm_conj hφ hker (commute_map_ofAdd e v w)]
  have hneg : ∀ v w : V, liftComm φ hφ (e (.ofAdd (-v))) (e (.ofAdd w)) =
      (liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)))⁻¹ := fun v w => by
    rw [ofAdd_neg, map_inv, liftComm_inv_left hφ hker (commute_map_ofAdd e v w)]
  have hneg' : ∀ v w : V, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd (-w))) =
      (liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)))⁻¹ := fun v w => by
    rw [liftComm_swap hφ, hneg, liftComm_swap hφ (e (.ofAdd w)), inv_inv]
  have hmp : ∀ v ∈ Dm, ∀ w ∈ Dp, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 := by
    intro v hv w hw
    refine liftComm_eq_one_of_conj_inv hφ hker hodd (commute_map_ofAdd e v w) (hpow v) n ?_ ?_
    · rw [hn, hσm v hv, ofAdd_neg, map_inv]
    · rw [hn, hσp w hw]
  have hmW : ∀ v ∈ Dm, ∀ w ∈ W, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 := by
    intro v hv w hw
    obtain ⟨u, hu⟩ := hTp
    set w' : W := (↑u⁻¹ : Module.End (ZMod r) W) ⟨w, hw⟩
    have hw' : σ w' + w' = w := by
      have := congrArg Subtype.val (show (σ.restrict hσW + 1) w' = ⟨w, hw⟩ by
        rw [← hu]
        simp only [w']
        rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply])
      simpa using this
    rw [← hw', liftComm_add_right e hφ hker]
    have h1 := hinv v w'
    rw [hσm v hv, hneg] at h1
    rw [← h1, mul_inv_cancel]
  have hpW : ∀ v ∈ Dp, ∀ w ∈ W, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 := by
    intro v hv w hw
    obtain ⟨u, hu⟩ := hTm
    set w' : W := (↑u⁻¹ : Module.End (ZMod r) W) ⟨w, hw⟩
    have hw' : σ w' + -(w' : V) = w := by
      have := congrArg Subtype.val (show (σ.restrict hσW - 1) w' = ⟨w, hw⟩ by
        rw [← hu]
        simp only [w']
        rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply])
      simpa [sub_eq_add_neg] using this
    rw [← hw', liftComm_add_right e hφ hker, hneg']
    have h1 := hinv v w'
    rw [hσp v hv] at h1
    rw [h1, mul_inv_cancel]
  have : NeZero r := ⟨hr.out.ne_zero⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact (pow_pos hr.out.pos 4).ne')
  obtain ⟨xm, -, hxm⟩ := finrank_eq_one_iff'.1 hDm
  obtain ⟨xp, -, hxp⟩ := finrank_eq_one_iff'.1 hDp
  have hDm_le : Dm ≤ Submodule.span (ZMod r) {(xm : V)} := by
    intro v hv
    obtain ⟨c, hc⟩ := hxm ⟨v, hv⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  have hDp_le : Dp ≤ Submodule.span (ZMod r) {(xp : V)} := by
    intro v hv
    obtain ⟨c, hc⟩ := hxp ⟨v, hv⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  let b := Module.finBasisOfFinrankEq (ZMod r) W hW
  have hW_eq : W = Submodule.span (ZMod r) (Set.range fun i => (b i : V)) := by
    have : (Set.range fun i => (b i : V)) = W.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  set M := LinearMap.toMatrix b b (σ.restrict hσW) with hM
  have hσb : ∀ j, σ (b j : V) = M 0 j • (b 0 : V) + M 1 j • (b 1 : V) := by
    intro j
    have h1 := b.sum_repr (σ.restrict hσW (b j))
    rw [Fin.sum_univ_two] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Submodule.coe_add, Submodule.coe_smul, LinearMap.coe_restrict_apply] at h2
    rw [← h2, hM, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hdetM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = -1 := by
    rw [← Matrix.det_fin_two, hM, LinearMap.det_toMatrix, hdet]
  have hWW : liftComm φ hφ (e (.ofAdd (b 0 : V))) (e (.ofAdd (b 1 : V))) = 1 := by
    set γ := liftComm φ hφ (e (.ofAdd (b 0 : V))) (e (.ofAdd (b 1 : V))) with hγ
    have h1 := hinv (b 0 : V) (b 1 : V)
    rw [hσb, hσb, liftComm_add_left e hφ hker, liftComm_add_right e hφ hker,
      liftComm_add_right e hφ hker, liftComm_smul_left e hφ hker, liftComm_smul_left e hφ hker,
      liftComm_smul_left e hφ hker, liftComm_smul_left e hφ hker, liftComm_smul_right e hφ hker,
      liftComm_smul_right e hφ hker, liftComm_smul_right e hφ hker,
      liftComm_smul_right e hφ hker, liftComm_self, liftComm_self, one_pow, one_pow, one_pow,
      one_pow, one_mul, mul_one, ← hγ, liftComm_swap hφ, ← hγ] at h1
    exact eq_one_of_det_neg_one hodd (hβr _ _) hdetM h1.symm
  set S : Set V := {(xm : V), (xp : V), (b 0 : V), (b 1 : V)} with hS
  have hspan : Submodule.span (ZMod r) S = ⊤ := by
    rw [eq_top_iff, ← hsum]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hDm_le.trans (Submodule.span_mono (by simp [hS]))
    · exact hDp_le.trans (Submodule.span_mono (by simp [hS]))
    · rw [hW_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [hS]
  have hxmD : (xm : V) ∈ Dm := xm.2
  have hxpD : (xp : V) ∈ Dp := xp.2
  have hbW : ∀ i, (b i : V) ∈ W := fun i => (b i).2
  have hsym : ∀ v w : V, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 →
      liftComm φ hφ (e (.ofAdd w)) (e (.ofAdd v)) = 1 := fun v w h => by
    rw [liftComm_swap, h, inv_one]
  have hpairs : ∀ v ∈ S, ∀ w ∈ S, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 := by
    intro v hv w hw
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      first
      | exact liftComm_self hφ _
      | exact hmp _ hxmD _ hxpD
      | exact hmW _ hxmD _ (hbW _)
      | exact hpW _ hxpD _ (hbW _)
      | exact hWW
      | exact hsym _ _ (hmp _ hxmD _ hxpD)
      | exact hsym _ _ (hmW _ hxmD _ (hbW _))
      | exact hsym _ _ (hpW _ hxpD _ (hbW _))
      | exact hsym _ _ hWW
  have hall : ∀ v w : V, liftComm φ hφ (e (.ofAdd v)) (e (.ofAdd w)) = 1 := fun v w =>
    liftComm_eq_one_of_mem_span e hφ hker hpairs (by rw [hspan]; trivial)
      (by rw [hspan]; trivial)
  have hF : ∀ x ∈ e.range.comap φ, ∀ y ∈ e.range.comap φ, x * y = y * x :=
    fun x hx y hy => mul_comm_of_liftComm_eq_one hφ hker (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [← ofAdd_toAdd a, ← ofAdd_toAdd a']
      exact hall _ _) hx hy
  have hcard : r ^ 4 ≤ Nat.card e.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective he).toEquiv]
    exact hV.ge
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, hloc, hrank⟩ :=
    central_cover_involution_witness Y hφ hker hr.out hr2
      (fun x hx => by obtain ⟨a, rfl⟩ := hx; rw [← ofAdd_toAdd a]; exact hpow _) hF hcard hz
      (fun x hx => by obtain ⟨a, rfl⟩ := hx; rw [← ofAdd_toAdd a]; exact hzD _)
  exact ⟨hF, u, huY, hu, A, hA, hAab, hAcard, hloc, hrank⟩

end CFSG.RankThree.CentralCover
