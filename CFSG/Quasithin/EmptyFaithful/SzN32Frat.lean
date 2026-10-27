module

public import CFSG.Quasithin.EmptyFaithful.SzN32Defs
public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.Quasithin.SzN32

namespace Frat

theorem isCoatom_map_of_ker_le {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) {M : Subgroup G} (hM : f.ker ≤ M) (hmax : IsCoatom M) :
    IsCoatom (M.map f) := by
  refine ⟨fun h => hmax.1 ?_, fun K hK => ?_⟩
  · have := congrArg (Subgroup.comap f) h
    rwa [Subgroup.comap_map_eq_self hM, Subgroup.comap_top] at this
  · have hle : M ≤ K.comap f := Subgroup.map_le_iff_le_comap.1 hK.le
    have hne : M ≠ K.comap f := by
      intro h
      rw [h, Subgroup.map_comap_eq_self_of_surjective hf] at hK
      exact lt_irrefl _ hK
    have htop : K.comap f = ⊤ := hmax.2 _ (lt_of_le_of_ne hle hne)
    rw [← Subgroup.map_comap_eq_self_of_surjective hf K, htop,
      Subgroup.map_top_of_surjective f hf]

theorem le_frattini_iff {G : Type*} [Group G] {X : Subgroup G} :
    X ≤ frattini G ↔ ∀ M : Subgroup G, IsCoatom M → X ≤ M := by
  simp only [frattini, Order.radical, le_iInf_iff, Set.mem_ofPred_eq]

theorem exists_pow_orderOf_eq_three {G : Type*} [Group G] (hG : IsPGroup 3 G) {x : G}
    (hx : x ≠ 1) : ∃ n : ℕ, orderOf (x ^ n) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hG x
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    rintro rfl
    exact hx (orderOf_eq_one_iff.1 (by simpa using hk))
  refine ⟨3 ^ j, ?_⟩
  have hdvd : 3 ^ j ∣ orderOf x := by
    rw [hk]
    exact pow_dvd_pow 3 (Nat.le_succ j)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hk, pow_succ,
    Nat.mul_div_cancel_left _ (by positivity)]

theorem cm_eq_one_of_mem_center {G : Type*} [Group G] {c : G} (hc : c ∈ Subgroup.center G)
    (d : G) : cm c d = 1 := by
  have h := Subgroup.mem_center_iff.1 hc d⁻¹
  unfold cm
  calc c⁻¹ * d⁻¹ * c * d = c⁻¹ * (d⁻¹ * c) * d := by simp only [mul_assoc]
    _ = 1 := by rw [h]; simp

end Frat

theorem comap_frattini_quotient_le {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ frattini G) : (frattini (G ⧸ N)).comap (QuotientGroup.mk' N) ≤ frattini G := by
  refine Frat.le_frattini_iff.2 fun M hM => ?_
  have hker : (QuotientGroup.mk' N).ker ≤ M := by
    rw [QuotientGroup.ker_mk']
    exact hN.trans (frattini_le_coatom hM)
  have hmax := Frat.isCoatom_map_of_ker_le (QuotientGroup.mk'_surjective N) hker hM
  calc (frattini (G ⧸ N)).comap (QuotientGroup.mk' N)
      ≤ (M.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
        Subgroup.comap_mono (frattini_le_coatom hmax)
    _ = M := Subgroup.comap_map_eq_self hker

theorem commutator_le_frattini {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G) :
    commutator G ≤ frattini G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent G := hG.isNilpotent
  refine Frat.le_frattini_iff.2 fun M hM => ?_
  have : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
  have hcard : Nat.card (G ⧸ M) = 3 := hG.isCoatom_iff_index_eq_prime.1 hM
  have : IsCyclic (G ⧸ M) := isCyclic_of_prime_card hcard
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [← QuotientGroup.ker_mk' M, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

theorem exists_central_card_three {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    {K : Subgroup G} [K.Normal] (hK : K ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≤ K ∧ Z ≤ Subgroup.center G ∧ Nat.card Z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent G := hG.isNilpotent
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hK)
  replace hx1 : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨n, hn⟩ := Frat.exists_pow_orderOf_eq_three hG hx1
  obtain ⟨hxK, hxZ⟩ := Subgroup.mem_inf.1 hx
  refine ⟨Subgroup.zpowers (x ^ n), ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.2 (pow_mem hxK n)
  · exact Subgroup.zpowers_le.2 (pow_mem hxZ n)
  · rw [Nat.card_zpowers, hn]

theorem exists_normal_index_three {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G)
    {L H : Subgroup G} [L.Normal] [H.Normal] (hLH : L < H) :
    ∃ E : Subgroup G, E.Normal ∧ L ≤ E ∧ E ≤ H ∧ Nat.card H = 3 * Nat.card E ∧
      ∀ h ∈ H, ∀ g : G, cm h g ∈ E := by
  obtain ⟨E, ⟨hEn, hLE, hEH⟩, hmax⟩ := (wellFounded_gt (α := Subgroup G)).has_min
    {E : Subgroup G | E.Normal ∧ L ≤ E ∧ E < H} ⟨L, inferInstance, le_rfl, hLH⟩
  have : E.Normal := hEn
  have hf : Function.Surjective (QuotientGroup.mk' E) := QuotientGroup.mk'_surjective E
  have hker : (QuotientGroup.mk' E).ker = E := QuotientGroup.ker_mk' E
  have : (H.map (QuotientGroup.mk' E)).Normal := Subgroup.Normal.map inferInstance _ hf
  have hHne : H.map (QuotientGroup.mk' E) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, hker] at h
    exact absurd hEH (not_lt_of_ge h)
  obtain ⟨Z, hZH, hZc, hZ3⟩ := exists_central_card_three (hG.to_quotient E) hHne
  have : Z.Normal := Subgroup.normal_of_le_center hZc
  have hEF : E ≤ Z.comap (QuotientGroup.mk' E) := hker.symm.le.trans (Z.ker_le_comap _)
  have hFH : Z.comap (QuotientGroup.mk' E) ≤ H :=
    calc Z.comap (QuotientGroup.mk' E)
        ≤ (H.map (QuotientGroup.mk' E)).comap (QuotientGroup.mk' E) := Subgroup.comap_mono hZH
      _ = H := Subgroup.comap_map_eq_self (hker.le.trans hEH.le)
  have hcardF : Nat.card (Z.comap (QuotientGroup.mk' E)) = 3 * Nat.card E := by
    have h1 := (Subgroup.index_mul_card (H := Z.comap (QuotientGroup.mk' E)))
    have h2 := (Subgroup.index_mul_card (H := E))
    have h3 := (Subgroup.index_mul_card (H := Z))
    have h4 : (Z.comap (QuotientGroup.mk' E)).index = Z.index :=
      Subgroup.index_comap_of_surjective Z hf
    have hpos : 0 < Z.index := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Z.index * Nat.card (Z.comap (QuotientGroup.mk' E))
        = (Z.comap (QuotientGroup.mk' E)).index * Nat.card (Z.comap (QuotientGroup.mk' E)) := by
          rw [h4]
      _ = Nat.card G := h1
      _ = E.index * Nat.card E := h2.symm
      _ = (Z.index * Nat.card Z) * Nat.card E := by rw [Subgroup.index_eq_card E, ← h3]
      _ = Z.index * (3 * Nat.card E) := by rw [hZ3]; ring
  have hFeq : Z.comap (QuotientGroup.mk' E) = H := by
    by_contra hne
    refine hmax _ ⟨inferInstance, hLE.trans hEF, lt_of_le_of_ne hFH hne⟩ ?_
    refine lt_of_le_of_ne hEF fun h => ?_
    have hE0 : 0 < Nat.card E := Nat.card_pos
    rw [← h] at hcardF
    omega
  refine ⟨E, hEn, hLE, hEH.le, hFeq ▸ hcardF, fun h hh g => ?_⟩
  have hc : QuotientGroup.mk' E h ∈ Subgroup.center (G ⧸ E) := hZc (hFeq.ge hh)
  refine (QuotientGroup.eq_one_iff _).1 ?_
  show QuotientGroup.mk' E (cm h g) = 1
  rw [map_cm]
  exact Frat.cm_eq_one_of_mem_center hc _

end CFSG.Quasithin.SzN32
