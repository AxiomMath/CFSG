module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CoverFinal
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Cover

open CFSG CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Lift

variable {L X : Type*} [Group L] [Group X] {π : L →* X}

theorem exists_elemAbelian_lift_sub [Finite L] [Finite X] (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) {n m : ℕ}
    (x : Fin n → X) (hx3 : ∀ i, x i ^ 3 = 1) (hxc : ∀ i j, x i * x j = x j * x i)
    (g : Fin m → X) (M : Fin m → Fin n → Fin n → ℕ)
    (hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ M j k i).prod)
    (k₀ l₀ : Fin n) (cs : Fin n → Fin n → List (ℕ × ℕ))
    (hlin : ∀ k l, Pi.single (k, l) 1 =
      ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum)
    (cs' : Fin n → List (ℕ × ℕ))
    (hlin' : ∀ i, Pi.single i 1 =
      ((cs' i).map fun p => p.1 • (cubeRelations M).getD p.2 0).sum)
    {Y : Subgroup X} (hY : Y ≤ Subgroup.closure (Set.range x)) (hY27 : 27 ≤ Nat.card Y)
    {c : L} (hc : c ∈ π.ker) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) :
    ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      ∀ y ∈ E, π y ∈ Y := by
  obtain ⟨y, hyπ, hy3, hyc⟩ := exists_lift hπ hker x hx3 hxc g M hrel k₀ l₀ cs hlin cs' hlin'
  have hcen : ∀ a : L, Commute a c := fun a => Subgroup.mem_center_iff.mp (hker hc) a
  set S : Set L := Set.range y ∪ {c} with hS
  have hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    rintro a (⟨i, rfl⟩ | rfl) b (⟨j, rfl⟩ | rfl)
    · exact hyc i j
    · exact hcen _
    · exact (hcen _).symm
    · exact Commute.refl _
  have hS3 : ∀ a ∈ S, a ^ 3 = 1 := by
    rintro a (⟨i, rfl⟩ | rfl)
    · exact hy3 i
    · exact hc3
  have hE0 := Item434SporE81.isElemAbelian_closure_of_comm hSc hS3
  have hyE : ∀ i, y i ∈ Subgroup.closure S := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hcE : c ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  set E : Subgroup L := Subgroup.closure S ⊓ Y.comap π with hEdef
  have hrange0 : Subgroup.closure (Set.range x) ≤
      (π.comp (Subgroup.closure S).subtype).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨y i, hyE i⟩, hyπ i⟩
  refine ⟨E, Sec5.isElemAbelian_of_le hE0 inf_le_left, ?_, fun a ha => ha.2⟩
  let φ : E →* X := π.comp E.subtype
  have hrange : Y ≤ φ.range := by
    intro v hv
    obtain ⟨⟨e, he⟩, hev⟩ := hrange0 (hY hv)
    refine ⟨⟨e, he, ?_⟩, hev⟩
    change π e ∈ Y
    have : π e = v := hev
    rw [this]
    exact hv
  have hcE' : c ∈ E := ⟨hcE, by
    show π c ∈ Y
    rw [MonoidHom.mem_ker.mp hc]
    exact one_mem _⟩
  have hc' : (⟨c, hcE'⟩ : E) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact hc
  have h3 : 3 ∣ Nat.card φ.ker := by
    have hord : orderOf (⟨⟨c, hcE'⟩, hc'⟩ : φ.ker) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact orderOf_eq_prime hc3 hc1
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hker3 : 3 ≤ Nat.card φ.ker := Nat.le_of_dvd Nat.card_pos h3
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hr : 27 ≤ Nat.card φ.range := hY27.trans (Subgroup.card_le_of_le hrange)
  calc 81 = 3 * 27 := by norm_num
    _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul hker3 hr
    _ = Nat.card E := hcard

end Lift

section Cover

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X] [Finite X]

theorem false_of_cover_gen (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    (hout : ¬ 3 ∣ Nat.card (Outer X)) (hZ : Subgroup.center (layer G) ≠ ⊥)
    (hX : ∀ U : Subgroup X, CFSG.Assembly.IsElemAbelian 3 U → Nat.card U = 9 →
      ∃ us : Set X, (∀ u ∈ us, u ∈ U ∧ u ≠ 1) ∧ ∃ d : LiftData X, ∃ Y : Subgroup X,
        Y ≤ Subgroup.closure (Set.range d.x) ∧ 27 ≤ Nat.card Y ∧
          Y ≤ Subgroup.closure (⋃ u ∈ us, (Subgroup.centralizer ({u} : Set X) : Set X))) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card h.layerStar = 9 := by
    rcases h.card_layerStar with h9 | ⟨-, hZ'⟩
    · exact h9
    · exact absurd hZ' hZ
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
    have h1 := h.card_inf_mul_card_layerStar
    rw [h9] at h1
    omega
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq h e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hAmap : Nat.card (A.map (quotConj e)) = 9 := by
    rw [card_map_quotConj_eq h e]
    exact h9
  have hP9 : Nat.card P = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hAmap]
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj h e)
  have hinn : A.map (quotConj e) ≤ (MulAut.conj : X →* MulAut X).range := by
    rw [← hPmap]
    exact Subgroup.map_le_range _ _
  have hu : ∀ u ∈ P, (MulAut.conj : X →* MulAut X) u ∈ A.map (quotConj e) := fun u hu => by
    rw [← hPmap]
    exact ⟨u, hu, rfl⟩
  obtain ⟨us, hus, d, Y, hY1, hY2, hY3⟩ := hX P hPe hP9
  obtain ⟨u₀, hu₀P, hu₀1⟩ : ∃ u₀ ∈ P, u₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hall
    rw [this, Subgroup.card_bot] at hP9
    omega
  have hZp : IsPGroup 3 (Subgroup.center (layer G)) := h.isPGroup_center_layer
  have hZnt : Nontrivial (Subgroup.center (layer G)) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hZ
  have hdvd : 3 ∣ Nat.card (Subgroup.center (layer G)) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rcases k with _ | k
    · exfalso
      have : Nat.card (Subgroup.center (layer G)) = 1 := by simpa using hk
      exact (Subgroup.card_eq_one.mp this ▸ hZ) rfl |>.elim
    · rw [hk]
      exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (layer G)) 3 hdvd
  have hc3 : (c : layer G) ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val this
  have hc1 : (c : layer G) ≠ 1 := by
    intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    omega
  have hcker : (c : layer G) ∈ (layerQuot e).ker := by
    rw [ker_layerQuot]
    exact c.2
  set Hm : Subgroup (layer G) := M.comap (layer G).subtype with hHm
  have hlift : ∀ u ∈ P, u ≠ 1 → ∀ x : layer G, layerQuot e x ∈ Subgroup.centralizer ({u} : Set X) →
      x ∈ Hm := fun u huP hu1 x hx =>
    coe_mem_M_of_centralizer h e hcen hinn hC3 hu1 (hu u huP) hx
  have hkerHm : (layerQuot e).ker ≤ Hm := fun z hz =>
    hlift u₀ hu₀P hu₀1 z (by
      rw [MonoidHom.mem_ker.mp hz]
      exact one_mem _)
  have hgen : Subgroup.closure (⋃ u ∈ us, (Subgroup.centralizer ({u} : Set X) : Set X)) ≤
      Hm.map (layerQuot e) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu', hxu⟩ := hx
    obtain ⟨y, rfl⟩ := layerQuot_surjective e x
    exact ⟨y, hlift u (hus u hu').1 (hus u hu').2 y hxu, rfl⟩
  obtain ⟨E, hE, hE81, hEπ⟩ := exists_elemAbelian_lift_sub (π := layerQuot e)
    (layerQuot_surjective e) (le_of_eq (ker_layerQuot e)) d.x d.hx3 d.hxc d.g d.M d.hrel d.k₀ d.l₀
    d.cs d.hlin d.cs' d.hlin' hY1 hY2 hcker hc1 hc3
  refine false_of_le_M h (D := E.map (layer G).subtype)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE) ?_ ?_
  · rw [Subgroup.card_map_of_injective (layer G).subtype_injective]
    exact hE81
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy'Hm, hy'π⟩ := hgen (hY3 (hEπ y hy))
    have hyy : y * y'⁻¹ ∈ (layerQuot e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy'π, mul_inv_cancel]
    have : y ∈ Hm := by
      have := Hm.mul_mem (hkerHm hyy) hy'Hm
      simpa using this
    exact this

end Cover

end CFSG.RankThree.PartTwo.Sec4.Item434Cover
