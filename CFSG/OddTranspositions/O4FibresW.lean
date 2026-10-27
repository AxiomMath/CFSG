module

public import CFSG.OddTranspositions.O4FibresSetup
public import CFSG.OddTranspositions.O4PairTenAbstract
public import CFSG.GroupTheory.TenPointPartition
public import CFSG.Timmesfeld.Bridge.Asc72Theorem
public import CFSG.OddTranspositions.O4CloseReduction

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def Omega (D : Set G) (X : Subgroup G) (R : Subgroup X) [R.Normal] :
    Set (X ⧸ R) :=
  (QuotientGroup.mk' R) '' {x : X | (x : G) ∈ D}

theorem exists_normalized_iso (hC : HypothesisC D) {u w v z : G}
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha)
    (hz : ∃ n : ℕ, Odd n ∧ 1 < n ∧ orderOf (u * v * w) = 2 * n ∧ z = (u * v * w) ^ n)
    {X : Subgroup G} (hKX : thirdK D z ≤ X) (huX : u ∈ X) {R : Subgroup X} [R.Normal]
    (hPX : O4PairData (X ⧸ R) (Omega D X R)) :
    ∃ e : (X ⧸ R) ≃* PSigmaL225, e '' Omega D X R = class65 ∧
      e (QuotientGroup.mk' R ⟨u, huX⟩) = SemidirectProduct.inr frob25 := by
  classical
  obtain ⟨e, he⟩ := hPX
  have huD : u ∈ D := hC.isBlock_alpha.subset hu
  let θ : PSigmaL225 := e (QuotientGroup.mk' R ⟨u, huX⟩)
  have hθclass : θ ∈ class65 := by
    have hθΩ : QuotientGroup.mk' R ⟨u, huX⟩ ∈ Omega D X R :=
      ⟨⟨u, huX⟩, huD, rfl⟩
    have h : θ ∈ e '' Omega D X R := ⟨_, hθΩ, rfl⟩
    rwa [he] at h
  obtain ⟨c, hc⟩ := isConj_iff.mp ((mem_class65_iff θ).mp hθclass)
  have hc' : c⁻¹ * θ * c = SemidirectProduct.inr frob25 := by
    rw [← hc]
    group
  let e' : (X ⧸ R) ≃* PSigmaL225 := e.trans (MulAut.conj c⁻¹)
  have hclass : (MulAut.conj c⁻¹) '' class65 = class65 := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_class65_iff] at hz ⊢
      exact hz.trans (isConj_iff.mpr ⟨c⁻¹, rfl⟩)
    · intro hx
      refine ⟨(MulAut.conj c⁻¹).symm x, ?_, ?_⟩
      · rw [mem_class65_iff] at hx ⊢
        have hxy : IsConj x (c * x * c⁻¹) := isConj_iff.mpr ⟨c, rfl⟩
        exact hx.trans (by simpa [MulAut.conj_symm_apply] using hxy)
      · exact MulEquiv.apply_symm_apply (MulAut.conj c⁻¹) x
  have himage : e' '' Omega D X R = class65 := by
    calc e' '' Omega D X R
        = (MulAut.conj c⁻¹) '' (e '' Omega D X R) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨e z, ⟨z, hz, rfl⟩, rfl⟩
          · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
            exact ⟨z, hz, rfl⟩
      _ = (MulAut.conj c⁻¹) '' class65 := by rw [he]
      _ = class65 := hclass
  refine ⟨e', himage, ?_⟩
  change (MulAut.conj c⁻¹) θ = SemidirectProduct.inr frob25
  rw [MulAut.conj_apply]
  simpa using hc'

theorem image_W_eq_ten {u : G} (hD : IsOddTransp D) (huD : u ∈ D)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (huX : u ∈ X)
    (e : (X ⧸ R) ≃* PSigmaL225) (he : e '' Omega D X R = class65)
    (heu : e (QuotientGroup.mk' R ⟨u, huX⟩) = SemidirectProduct.inr frob25) :
    e '' {z : X ⧸ R | ∃ y : X, y ∈ W D u X R huX ∧ QuotientGroup.mk' R y = z} =
      Set.range y := by
  classical
  have hbase : (SemidirectProduct.inr frob25 : PSigmaL225) ∉ Set.range y := by
    have hcard11 : (insert (SemidirectProduct.inr frob25) (Set.range y)).ncard = 11 := by
      rw [← commuting_class65_eq, ← Nat.card_coe_set_eq]
      exact card_comm_class65 _ inr_frob25_mem_class65
    have hrange10 : (Set.range y).ncard = 10 := by
      rw [← Nat.card_coe_set_eq]
      exact (Nat.card_congr (Equiv.ofInjective y y_injective).symm).trans (Nat.card_fin 10)
    intro hmem
    rw [Set.insert_eq_of_mem hmem, hrange10] at hcard11
    omega
  ext p
  constructor
  · rintro ⟨z, hzS, rfl⟩
    obtain ⟨x, hxW, hxz⟩ := hzS
    rw [← hxz]
    have hxclass : e (QuotientGroup.mk' R x) ∈ class65 := by
      have hΩ : QuotientGroup.mk' R x ∈ Omega D X R := ⟨x, W_subset_D x hxW, rfl⟩
      have h : e (QuotientGroup.mk' R x) ∈ e '' Omega D X R := ⟨_, hΩ, rfl⟩
      rwa [he] at h
    have hxcomm : Commute (e (QuotientGroup.mk' R x)) (SemidirectProduct.inr frob25) := by
      have hcommX : Commute x ⟨u, huX⟩ := by
        rw [commute_iff_eq]
        exact Subtype.ext (by simpa using (W_commute_u x hxW).eq)
      simpa only [heu] using (hcommX.map (QuotientGroup.mk' R)).map e
    have hxne : e (QuotientGroup.mk' R x) ≠ SemidirectProduct.inr frob25 := by
      intro h
      exact (mem_W_iff.mp hxW).2.2 (e.injective (h.trans heu.symm))
    have hmem : e (QuotientGroup.mk' R x) ∈
        insert (SemidirectProduct.inr frob25) (Set.range y) := by
      rw [← commuting_class65_eq]
      exact ⟨hxclass, hxcomm⟩
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact absurd h hxne
    · exact h
  · rintro ⟨i, hi⟩
    rw [← hi]
    have hyiΩ : y i ∈ e '' Omega D X R := by
      rw [he]
      exact y_mem_class65 i
    obtain ⟨z, hzΩ, hzE⟩ := hyiΩ
    obtain ⟨x, hxD, hxz⟩ := hzΩ
    have hxe : e (QuotientGroup.mk' R x) = y i := by
      rw [hxz]
      exact hzE
    have hyi_ne : y i ≠ SemidirectProduct.inr frob25 := by
      intro h
      exact hbase ⟨i, h⟩
    have hneX : QuotientGroup.mk' R x ≠ QuotientGroup.mk' R ⟨u, huX⟩ := by
      intro h
      apply hyi_ne
      rw [← hxe, h, heu]
    have hcommQ : Commute (QuotientGroup.mk' R x) (QuotientGroup.mk' R ⟨u, huX⟩) := by
      have h1 : Commute (e.symm (y i)) (e.symm (SemidirectProduct.inr frob25)) :=
        (y_commute_base i).map e.symm
      have h2 : e.symm (y i) = QuotientGroup.mk' R x := by
        rw [← hxe, MulEquiv.symm_apply_apply]
      have h3 : e.symm (SemidirectProduct.inr frob25) = QuotientGroup.mk' R ⟨u, huX⟩ := by
        rw [← heu, MulEquiv.symm_apply_apply]
      rwa [h2, h3] at h1
    have hcommX : Commute x ⟨u, huX⟩ :=
      Asc72.commute_of_commute_of_ne (Asc72.IsOddTransp.preimage hD X) hxD huD hneX hcommQ
    have hcommG : Commute (x : G) u := by
      rw [commute_iff_eq]
      simpa using congrArg Subtype.val hcommX.eq
    have hxW : x ∈ W D u X R huX := mem_W_iff.mpr ⟨hxD, hcommG, hneX⟩
    exact ⟨QuotientGroup.mk' R x, ⟨x, hxW, rfl⟩, hxe⟩

theorem W_subset_DalphaStar_of_Wstar_nonempty (hC : HypothesisC D) {u : G}
    (hu : u ∈ hC.alpha) {X : Subgroup G} {R : Subgroup X} [R.Normal] (huX : u ∈ X)
    (e : (X ⧸ R) ≃* PSigmaL225) (he : e '' Omega D X R = class65)
    (heu : e (QuotientGroup.mk' R ⟨u, huX⟩) = SemidirectProduct.inr frob25)
    (hWstar : ∃ y : X, y ∈ W D u X R huX ∧ (y : G) ∈ DalphaStar D hC.alpha) :
    ∀ y : X, y ∈ W D u X R huX → (y : G) ∈ DalphaStar D hC.alpha := by
  classical
  let S : Set (X ⧸ R) :=
    {z : X ⧸ R | ∃ y : X, y ∈ W D u X R huX ∧ QuotientGroup.mk' R y = z}
  have himage : e '' S = Set.range y :=
    image_W_eq_ten hC.setup.oddT (hC.isBlock_alpha.subset hu) huX e he heu
  let comm : Fin 10 → Fin 10 → Prop := fun i j => Commute (y i) (y j)
  let A : Set (Fin 10) :=
    {i | ∃ w : X, w ∈ W D u X R huX ∧ (w : G) ∈ hC.alpha ∧
      e (QuotientGroup.mk' R w) = y i}
  let B : Set (Fin 10) :=
    {i | ∃ w : X, w ∈ W D u X R huX ∧ (w : G) ∈ DalphaStar D hC.alpha ∧
      e (QuotientGroup.mk' R w) = y i}
  have hcover : A ∪ B = Set.univ := by
    ext i
    constructor
    · intro _
      exact Set.mem_univ i
    · intro _
      have hyS : y i ∈ e '' S := by
        rw [himage]
        exact Set.mem_range_self i
      obtain ⟨z, hzS, hzi⟩ := hyS
      obtain ⟨w, hwW, hwz⟩ := hzS
      have hweq : e (QuotientGroup.mk' R w) = y i := by
        rw [hwz]
        exact hzi
      rcases W_subset_alpha_union hC hu w hwW with hα | hα
      · exact Or.inl ⟨w, hwW, hα, hweq⟩
      · exact Or.inr ⟨w, hwW, hα, hweq⟩
  have hAB : ∀ i ∈ A, ∀ j ∈ B, comm i j := by
    rintro i ⟨a, haW, haα, hai⟩ j ⟨b, hbW, hbα, hbj⟩
    obtain ⟨β, hβ, hbβ⟩ := mem_DalphaStar_iff.mp hbα
    have hcommG : Commute (a : G) (b : G) :=
      (mem_Dalpha_iff.mp hβ).2.2.2 (a : G) haα (b : G) hbβ
    have hcommX : Commute a b := by
      rw [commute_iff_eq]
      exact Subtype.ext (by simpa using hcommG.eq)
    have hcommE : Commute (e (QuotientGroup.mk' R a)) (e (QuotientGroup.mk' R b)) :=
      (hcommX.map (QuotientGroup.mk' R)).map e
    rw [hai, hbj] at hcommE
    exact hcommE
  have hBne : B.Nonempty := by
    obtain ⟨v₀, hv₀W, hv₀α⟩ := hWstar
    have hv₀S : e (QuotientGroup.mk' R v₀) ∈ e '' S :=
      ⟨QuotientGroup.mk' R v₀, ⟨v₀, hv₀W, rfl⟩, rfl⟩
    rw [himage] at hv₀S
    obtain ⟨i, hi⟩ := hv₀S
    exact ⟨i, v₀, hv₀W, hv₀α, hi.symm⟩
  have hAempty : A = ∅ := by
    rcases CFSG.GroupTheory.partition_of_card_ten comm (fun i j h => h.symm)
      (Nat.card_fin 10) (fun i => y_commuting_others i) A B hcover hAB with hA | hB
    · exact hA
    · rw [hB] at hBne
      exact absurd hBne Set.not_nonempty_empty
  intro y₀ hy₀
  by_contra hnot
  have hy₀α : (y₀ : G) ∈ hC.alpha := by
    rcases W_subset_alpha_union hC hu y₀ hy₀ with h | h
    · exact h
    · exact absurd h hnot
  have hy₀S : e (QuotientGroup.mk' R y₀) ∈ e '' S :=
    ⟨QuotientGroup.mk' R y₀, ⟨y₀, hy₀, rfl⟩, rfl⟩
  rw [himage] at hy₀S
  obtain ⟨i, hi⟩ := hy₀S
  have hiA : i ∈ A := ⟨y₀, hy₀, hy₀α, hi.symm⟩
  rw [hAempty] at hiA
  exact Set.notMem_empty i hiA

theorem W_subset_DalphaStar_of_v_not_mem (hC : HypothesisC D) {u w v : G}
    (htri : IsTriangle D u w v) (hu : u ∈ hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] (huX : u ∈ X) (hvX : v ∈ X)
    (e : (X ⧸ R) ≃* PSigmaL225) (he : e '' Omega D X R = class65)
    (heu : e (QuotientGroup.mk' R ⟨u, huX⟩) = SemidirectProduct.inr frob25)
    (hvne : QuotientGroup.mk' R ⟨v, hvX⟩ ≠ QuotientGroup.mk' R ⟨u, huX⟩) :
    ∀ y : X, y ∈ W D u X R huX → (y : G) ∈ DalphaStar D hC.alpha := by
  have hvD : v ∈ D := htri.2.1
  have hvu : Commute v u := by
    obtain ⟨β, hβ, hvβ⟩ := mem_DalphaStar_iff.mp hv
    exact ((mem_Dalpha_iff.mp hβ).2.2.2 u hu v hvβ).symm
  have hvW : (⟨v, hvX⟩ : X) ∈ W D u X R huX :=
    mem_W_iff.mpr ⟨hvD, hvu, hvne⟩
  exact W_subset_DalphaStar_of_Wstar_nonempty hC hu huX e he heu
    ⟨⟨v, hvX⟩, hvW, hv⟩

end CFSG.OddTranspositions.QZ

end
