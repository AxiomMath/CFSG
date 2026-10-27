module

public import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem ncard_mul_card_inf_centralizer_eq [Finite G] {K : Subgroup G} {w : G} {A : Set G}
    (hA : A = {y | ∃ k ∈ K, k * w * k⁻¹ = y}) :
    A.ncard * Nat.card ↥(K ⊓ Subgroup.centralizer ({w} : Set G)) = Nat.card K := by
  classical
  let e : G ≃* ConjAct G := ConjAct.toConjAct
  set K' : Subgroup (ConjAct G) := K.map e.toMonoidHom with hK'
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hstab : (MulAction.stabilizer K' w).map K'.subtype =
      (K ⊓ Subgroup.centralizer ({w} : Set G)).map e.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp s.2
      have hs' : (s : ConjAct G) • w = w := hs
      rw [ConjAct.smul_def, ← hks] at hs'
      have hkw : k * w * k⁻¹ = w := by simpa [e] using hs'
      refine Subgroup.mem_map.mpr ⟨k, Subgroup.mem_inf.mpr ⟨hk, ?_⟩, hks⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * w = (k * w * k⁻¹) * k := by group
        _ = w * k := by rw [hkw]
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨hkK, hkw⟩ := Subgroup.mem_inf.mp hk
      refine ⟨⟨_, Subgroup.mem_map_of_mem _ hkK⟩, ?_, rfl⟩
      show (e.toMonoidHom k : ConjAct G) • w = w
      rw [ConjAct.smul_def]
      simp only [e, MulEquiv.coe_toMonoidHom, ConjAct.ofConjAct_toConjAct]
      rw [(Subgroup.mem_centralizer_singleton_iff.mp hkw)]
      group
  have horbit : MulAction.orbit K' w = A := by
    rw [hA]
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp s.2
      refine ⟨k, hk, ?_⟩
      show k * w * k⁻¹ = (s : ConjAct G) • w
      rw [ConjAct.smul_def, ← hks]
      simp [e]
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨e.toMonoidHom k, Subgroup.mem_map_of_mem _ hk⟩, ?_⟩
      show (e.toMonoidHom k : ConjAct G) • w = k * w * k⁻¹
      rw [ConjAct.smul_def]
      simp [e]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer K' w)
  rw [MulAction.index_stabilizer, horbit] at h1
  have h2 : Nat.card (MulAction.stabilizer K' w) =
      Nat.card ↥(K ⊓ Subgroup.centralizer ({w} : Set G)) := by
    rw [← Subgroup.card_map_of_injective (f := K'.subtype) K'.subtype_injective, hstab,
      Subgroup.card_map_of_injective hinj]
  have h3 : Nat.card K' = Nat.card K := Subgroup.card_map_of_injective hinj
  rw [← h3, ← h1, h2, mul_comm]

theorem sevenEight_of_sevenSix (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {p : ℕ} (hp : ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → orderOf (x * y) = p)
    (hα : hC.alpha = {hC.d}) (hA : (AalphaStar D hC.alpha).Nonempty) {m : ℕ}
    (hl : {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard = m ^ 2 * (p - 1))
    (hμ : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).ncard = p)
    (hH : Nat.card ↥(Halpha D hC.alpha) =
      2 * p * m ^ 2 * Nat.card (Subgroup.center ↥(Halpha D hC.alpha)))
    (h77 : ∀ z ∈ Subgroup.center ↥(Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d) :
    p = 3 := by
  classical
  have hD := hC.setup.oddT
  have hu : hC.d ∈ D := hC.hd
  have hu2 : hC.d * hC.d = 1 := hD.mul_self_eq_one hu
  set H : Subgroup G := Halpha D hC.alpha with hHdef
  set K : Subgroup G := Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G))
    with hKdef
  have hAeq : AalphaStar D hC.alpha = {y | y ∈ D ∧ ¬ Commute y hC.d} := by
    rw [hC.AalphaStar_eq_diff_alpha, hα]
    ext y
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro ⟨hyD, hyu⟩
      exact ⟨⟨hyD, hyu⟩, fun h => hyu (h ▸ Commute.refl _)⟩
  obtain ⟨w, hw⟩ := hA
  have hwA : w ∈ {y | y ∈ D ∧ ¬ Commute y hC.d} := hAeq ▸ hw
  have hKu : ∀ k ∈ K, k * hC.d * k⁻¹ = hC.d := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ({hC.d} : Set G) :=
      (Subgroup.closure_le _).mpr (fun _ hy => hy.2) hk
    rw [Subgroup.mem_centralizer_singleton_iff.mp hk']
    group
  have horbit : {y | y ∈ D ∧ ¬ Commute y hC.d} = {y | ∃ k ∈ K, k * w * k⁻¹ = y} := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hk, hky⟩ :=
        cenGen_transitive_AalphaStar_unconditional hC hsecond w hw y (hAeq ▸ hy)
      exact ⟨k, hk, hky⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨hC.setup.normal k w hwA.1, fun hc => hwA.2 ?_⟩
      have := (Commute.conj_iff k⁻¹).mpr hc
      rw [show k⁻¹ * (k * w * k⁻¹) * k⁻¹⁻¹ = w by group,
        show k⁻¹ * hC.d * k⁻¹⁻¹ = hC.d by
          rw [inv_inv]
          have := hKu k hk
          calc k⁻¹ * hC.d * k = k⁻¹ * (k * hC.d * k⁻¹) * k := by rw [this]
            _ = hC.d := by group] at this
      exact this
  have hos := ncard_mul_card_inf_centralizer_eq horbit
  rw [hl] at hos
  have hDC : (D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G) ⊆ insert hC.d (DalphaStar D hC.alpha) := by
    rintro y ⟨hyD, hyc⟩
    have hyu : Commute y hC.d := Subgroup.mem_centralizer_singleton_iff.mp hyc
    rcases (Set.ext_iff.mp hC.eq_alpha_union y).mp hyD with (h | h) | h
    · rw [hα] at h
      exact Or.inl h
    · exact Or.inr h
    · exact ((mem_Gamma_iff.mp (show y ∈ Gamma hC from h)).2.1 hyu).elim
  have hKle : K ≤ H ⊔ Subgroup.zpowers hC.d := by
    rw [hKdef, Subgroup.closure_le]
    intro y hy
    rcases hDC hy with h | h
    · rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
  have hHK : H ≤ K := by
    rw [hHdef, Halpha, Subgroup.closure_le]
    intro y hy
    exact Subgroup.subset_closure ⟨DalphaStar_subset hC.isBlock_alpha hy,
      Subgroup.mem_centralizer_singleton_iff.mpr (hC.DalphaStar_subset_commute hy).2.eq⟩
  have huK : hC.d ∈ K := Subgroup.subset_closure ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hKeq : K = H ⊔ Subgroup.zpowers hC.d :=
    le_antisymm hKle (sup_le hHK ((Subgroup.zpowers_le).mpr huK))
  have hHu : ∀ h ∈ H, Commute h hC.d := by
    intro h hh
    refine Subgroup.closure_induction (p := fun y _ => Commute y hC.d) ?_ ?_ ?_ ?_ hh
    · intro y hy
      exact (hC.DalphaStar_subset_commute hy).2
    · exact Commute.one_left _
    · intro y z _ _ hy hz
      exact hy.mul_left hz
    · intro y _ hy
      exact hy.inv_left
  have hKcard : Nat.card K = 4 * p * m ^ 2 := by
    by_cases huH : hC.d ∈ H
    · have hKH : K = H := by
        rw [hKeq]
        exact sup_eq_left.mpr ((Subgroup.zpowers_le).mpr huH)
      have hZeq : Subgroup.center ↥H = Subgroup.zpowers (⟨hC.d, huH⟩ : ↥H) := by
        apply le_antisymm
        · intro z hz
          rcases h77 z hz with h | h
          · rw [show z = 1 from Subtype.ext h]
            exact Subgroup.one_mem _
          · rw [show z = ⟨hC.d, huH⟩ from Subtype.ext h]
            exact Subgroup.mem_zpowers _
        · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hHu g g.2).eq
      have hZ : Nat.card (Subgroup.center ↥H) = 2 := by
        rw [hZeq, Nat.card_zpowers, Subgroup.orderOf_mk]
        exact hD.orderOf_eq_two hu
      rw [hKH, hH, hZ]
      ring
    · have hZ : Nat.card (Subgroup.center ↥H) = 1 := by
        have hbot : Subgroup.center ↥H = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          rcases h77 z hz with h | h
          · exact (Subgroup.mem_bot).mpr (Subtype.ext h)
          · exact (huH (h ▸ z.2)).elim
        rw [hbot, Subgroup.card_bot]
      have hK2 : Nat.card K = 2 * Nat.card H := by
        rw [hKeq]
        refine CFSG.Sporadic.SmallOddCore.card_sup_zpowers (by rw [sq]; exact hu2) ?_ huH
        intro h hh
        rw [← (hHu h hh).eq, mul_inv_cancel_right]
        exact hh
      rw [hK2, hH, hZ]
      ring
  rw [hKcard] at hos
  have hwD : w ∈ D := hwA.1
  have hwu : ¬ Commute w hC.d := hwA.2
  have hpw : orderOf (hC.d * w) = p := hp _ hu _ hwD (fun h => hwu h.symm)
  have hodd : Odd p := hpw ▸ hD.odd_of_not_commute hu hwD (fun h => hwu h.symm)
  have hp1 : p ≠ 1 := by
    intro h
    rw [h] at hpw
    have e := hD.eq_of_mul_eq_one hu (orderOf_eq_one_iff.mp hpw)
    rw [← e] at hwu
    exact hwu (Commute.refl _)
  have hp3 : 3 ≤ p := by
    obtain ⟨r, hr⟩ := hodd
    omega
  have hm0 : 0 < m := by
    have hpos : 0 < {y | y ∈ D ∧ ¬ Commute y hC.d}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨w, hwA⟩
    rw [hl] at hpos
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hpos
      simp at hpos
    · exact h
  set c := Nat.card ↥(K ⊓ Subgroup.centralizer ({w} : Set G)) with hc
  have hpc : (p - 1) * c = 4 * p := by
    have hm2 : 0 < m ^ 2 := pow_pos hm0 2
    apply Nat.eq_of_mul_eq_mul_left hm2
    calc m ^ 2 * ((p - 1) * c) = m ^ 2 * (p - 1) * c := by ring
      _ = 4 * p * m ^ 2 := hos
      _ = m ^ 2 * (4 * p) := by ring
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hpc
  have hc5 : 5 ≤ c := by nlinarith
  have hc6 : c ≤ 6 := by nlinarith
  interval_cases c
  ·
    exfalso
    have hq : q = 4 := by omega
    subst hq
    obtain ⟨v, hv⟩ : (commSet D hC.d ∩ commSet D w).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _), hμ w hwD hwu]
      norm_num
    obtain ⟨⟨hvD, hvu, -⟩, ⟨-, hvw, -⟩⟩ := hv
    have hvK : v ∈ K ⊓ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.subset_closure ⟨hvD,
        Subgroup.mem_centralizer_singleton_iff.mpr hvu.eq⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hvw.eq⟩
    have h2 := orderOf_dvd_natCard (⟨v, hvK⟩ : ↥(K ⊓ Subgroup.centralizer ({w} : Set G)))
    rw [Subgroup.orderOf_mk, hD.orderOf_eq_two hvD, ← hc] at h2
    omega
  · omega

end CFSG.OddTranspositions

end
