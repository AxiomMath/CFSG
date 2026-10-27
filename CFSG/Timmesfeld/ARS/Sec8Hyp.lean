module

public import CFSG.Timmesfeld.ARS.Sec8HypRadical
public import CFSG.Timmesfeld.ARS.Sec8HypTwoCore
public import CFSG.Timmesfeld.ARS.ConfigTransfer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace LeviQuot

variable {V : Subgroup G}

theorem iSup_eq_of_iSup_quotMap_eq_top_of_trans {Δ : Set (Subgroup G)} {E₀ : Subgroup G}
    (hΔV : ∀ X ∈ Δ, X ≤ V) (hΔtrans : ∀ X ∈ Δ, ∃ g ∈ V, conjSub E₀ g = X) (hgen : gen Δ = V)
    (hab : ∃ X ∈ Δ, ∃ Y ∈ Δ, ¬ Commuting X Y) {ι : Type*} {A B : ι → Subgroup G}
    (hA : ∀ k, A k ∈ Δ) (hB : ∀ k, B k ∈ Δ)
    (h : ⨆ k, (quotMap V (A k) ⊔ quotMap V (B k)) = ⊤) : ⨆ k, (A k ⊔ B k) = V := by
  set H := ⨆ k, (A k ⊔ B k) with hH
  have hHV : H ≤ V := iSup_le fun k => sup_le (hΔV _ (hA k)) (hΔV _ (hB k))
  set K : Subgroup ↥V := ⨆ k, ((A k).subgroupOf V ⊔ (B k).subgroupOf V) with hK
  have hKH : K ≤ H.subgroupOf V := iSup_le fun k => sup_le
    (Subgroup.comap_mono (le_sup_left.trans (le_iSup (fun k => A k ⊔ B k) k)))
    (Subgroup.comap_mono (le_sup_right.trans (le_iSup (fun k => A k ⊔ B k) k)))
  have hKmap : K.map (QuotientGroup.mk' (Subgroup.center ↥V)) = ⊤ := by
    rw [hK, Subgroup.map_iSup]
    simp only [Subgroup.map_sup]
    exact h
  have hdec : ∀ v : ↥V, ∃ k : ↥V, (k : G) ∈ H ∧ k⁻¹ * v ∈ Subgroup.center ↥V := fun v => by
    obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.1 (hKmap ▸ Subgroup.mem_top
      (QuotientGroup.mk' (Subgroup.center ↥V) v))
    exact ⟨k, Subgroup.mem_subgroupOf.1 (hKH hk), QuotientGroup.eq.1 hkv⟩
  have hnorm : ∀ g ∈ V, conjSub H g ≤ H := by
    intro g hg
    obtain ⟨k, hkH, hz⟩ := hdec ⟨g, hg⟩
    rintro _ ⟨y, hy, rfl⟩
    change g * y * g⁻¹ ∈ H
    have hzc : (k : G)⁻¹ * g * y = y * ((k : G)⁻¹ * g) := by
      have e := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hHV hy⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e
      exact e.symm
    have e : g * y * g⁻¹ = k * y * (k : G)⁻¹ := by
      calc g * y * g⁻¹ = k * ((k : G)⁻¹ * g * y) * ((k : G)⁻¹ * g)⁻¹ * (k : G)⁻¹ := by group
        _ = k * (y * ((k : G)⁻¹ * g)) * ((k : G)⁻¹ * g)⁻¹ * (k : G)⁻¹ := by rw [hzc]
        _ = k * y * (k : G)⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hkH hy) (H.inv_mem hkH)
  obtain ⟨X₁, hX₁, Y₁, hY₁, hXY⟩ := hab
  have hι : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hXY
    have hH0 : H = ⊥ := by
      rw [hH]
      exact iSup_of_empty _
    intro x hx y hy
    obtain ⟨k, hkH, hz⟩ := hdec ⟨x, hΔV X₁ hX₁ hx⟩
    rw [hH0, Subgroup.mem_bot] at hkH
    have hk1 : k = 1 := Subtype.ext hkH
    rw [hk1, inv_one, one_mul] at hz
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hΔV Y₁ hY₁ hy⟩)).symm
  obtain ⟨k₀⟩ := hι
  refine le_antisymm hHV ?_
  rw [← hgen]
  refine gen_le fun X hX => ?_
  obtain ⟨g, hg, rfl⟩ := hΔtrans X hX
  obtain ⟨g₀, hg₀, hA₀⟩ := hΔtrans _ (hA k₀)
  have hE : conjSub E₀ g = conjSub (A k₀) (g * g₀⁻¹) := by
    rw [← hA₀, ← conjSub_mul, inv_mul_cancel_right]
  rw [hE]
  exact (Subgroup.map_mono (le_sup_left.trans (le_iSup (fun k => A k ⊔ B k) k₀))).trans
    (hnorm _ (V.mul_mem hg (V.inv_mem hg₀)))

end LeviQuot

namespace Levi

section Quot

variable (h : Hyp G R) {A A₀ E₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hE₀ : E₀ ∈ leviSet R A A₀)
include h hA hAne hA₀ hE₀

omit h hA hAne hA₀ hE₀ in
theorem quot_hmap : ∀ X ∈ comp R A A₀ E₀,
    quotMap (gen (comp R A A₀ E₀)) X ∈ quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀) :=
  fun X hX => ⟨X, hX, rfl⟩

omit h hA hAne hA₀ hE₀ in
theorem quot_hsurj : ∀ X' ∈ quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀),
    ∃ X ∈ comp R A A₀ E₀, quotMap (gen (comp R A A₀ E₀)) X = X' :=
  fun _ ⟨X, hX, e⟩ => ⟨X, hX, e⟩

theorem quot_hinj : Set.InjOn (quotMap (gen (comp R A A₀ E₀))) (comp R A A₀ E₀) := by
  have := h.finite
  exact LeviQuot.injOn_quotMap h.root h.noIsolated (comp_subset_R h hA hAne hA₀ hE₀)
    (fun _ hX => le_gen hX) fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX

theorem quot_hcomm : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀,
    Commuting (quotMap (gen (comp R A A₀ E₀)) X) (quotMap (gen (comp R A A₀ E₀)) Y) →
      Commuting X Y := by
  have := h.finite
  exact fun _ hX _ hY => LeviQuot.commuting_of_commuting_quotMap h.root
    (comp_subset_R h hA hAne hA₀ hE₀) (fun _ hX => le_gen hX)
    (fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX)
    (fun _ hX _ hY hs => commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs) hX hY

theorem quot_hopp : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀,
    Opposite (quotMap (gen (comp R A A₀ E₀)) X) (quotMap (gen (comp R A A₀ E₀)) Y) →
      Opposite X Y := by
  have := h.finite
  exact fun _ hX _ hY => LeviQuot.opposite_of_opposite_quotMap h.root
    (comp_subset_R h hA hAne hA₀ hE₀) (fun _ hX => le_gen hX)
    (fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX) hX hY

theorem isRootClass_quot : IsRootClass (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀)) := by
  have := h.finite
  exact LeviQuot.isRootClass_quotClass h.root h.noIsolated (comp_subset_R h hA hAne hA₀ hE₀)
    (fun _ hX => le_gen hX) (fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX)
    Relation.ReflTransGen.refl
    (fun _ hX _ hg => conjSub_mem_comp_of_mem_gen h hA hAne hA₀ hE₀ hX hg)
    (fun _ hX => exists_conjSub_eq_of_mem_comp h hA hAne hA₀ hE₀ hX)
    (fun _ hX _ hY hs => commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs) rfl

theorem quot_hspec : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀,
    Special (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀))
      (quotMap (gen (comp R A A₀ E₀)) X) (quotMap (gen (comp R A A₀ E₀)) Y) →
      Special R X Y := by
  have := h.finite
  exact fun _ hX _ hY => LeviQuot.special_of_special_quotMap h.root h.noIsolated
    (comp_subset_R h hA hAne hA₀ hE₀) (fun _ hX => le_gen hX)
    (fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX)
    (isRootClass_quot h hA hAne hA₀ hE₀) hX hY

theorem quot_hcl : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀, Special R X Y →
    ⁅X, Y⁆ ∈ comp R A A₀ E₀ ∧ quotMap (gen (comp R A A₀ E₀)) ⁅X, Y⁆ =
      ⁅quotMap (gen (comp R A A₀ E₀)) X, quotMap (gen (comp R A A₀ E₀)) Y⁆ :=
  fun _ hX _ hY hs => ⟨commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs,
    LeviQuot.quotMap_commutator (le_gen hX) (le_gen hY)⟩

theorem card_quot_lt :
    Nat.card (↥(gen (comp R A A₀ E₀)) ⧸ Subgroup.center ↥(gen (comp R A A₀ E₀))) <
      Nat.card G := by
  have := h.finite
  refine LeviQuot.card_lt fun htop => h.root.ne_bot A hA ?_
  have hle : gen (comp R A A₀ E₀) ≤ levi R A A₀ := gen_mono (comp_subset h hA hAne hA₀ hE₀)
  have hbot := M_inf_levi_eq_bot h hA hA₀
  rw [htop, top_le_iff] at hle
  rw [hle, inf_top_eq] at hbot
  rw [← le_bot_iff, ← hbot]
  exact QD.le_M_self

theorem rootClosure_quotClass_eq_singleton
    (hnd : ∃ X ∈ comp R A A₀ E₀, ∃ Y ∈ comp R A A₀ E₀, Special R X Y) :
    ∀ X' ∈ quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀),
      rootClosure (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀)) X' = {X'} := by
  have := h.finite
  rintro _ ⟨X, hX, rfl⟩
  refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 (mem_rootClosure_self ⟨X, hX, rfl⟩))
  rintro _ hY
  obtain ⟨Y, hY', rfl⟩ := hY.1
  have hiff := (LeviQuot.mem_rootClosure_quotMap_iff h.root (comp_subset_R h hA hAne hA₀ hE₀)
    (fun _ hX => le_gen hX) (fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX)
    (fun _ hX _ hY hs => commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs) hX hY').1 hY
  have hall : ∀ Z ∈ leviSet R A A₀, Commuting X Z ↔ Commuting Y Z := by
    intro Z hZ
    by_cases hZΔ : Z ∈ comp R A A₀ E₀
    · exact hiff Z hZΔ
    · have hc : ∀ {W : Subgroup G}, W ∈ comp R A A₀ E₀ → Commuting W Z := fun hW =>
        commuting_of_notMem_comp h hA hAne hA₀ (comp_subset h hA hAne hA₀ hE₀ hW) hZ (by
          rw [comp_eq_of_mem hW]
          exact hZΔ)
      exact ⟨fun _ => hc hY', fun _ => hc hX⟩
  rw [eq_of_commuting_iff h hA hAne hA₀ hE₀ hnd hX hY' hall]
  exact Set.mem_singleton _

theorem quotHyp (hnd : ∃ X ∈ comp R A A₀ E₀, ∃ Y ∈ comp R A A₀ E₀, Special R X Y) :
    Hyp (↥(gen (comp R A A₀ E₀)) ⧸ Subgroup.center ↥(gen (comp R A A₀ E₀)))
      (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀)) := by
  have := h.finite
  have hR' := isRootClass_quot h hA hAne hA₀ hE₀
  have hiso' := LeviQuot.noIsolated_quotClass h.root h.noIsolated
    (comp_subset_R h hA hAne hA₀ hE₀) (fun _ hX => le_gen hX)
    (fun _ hX => exists_opposite_mem_comp h hA hAne hA₀ hE₀ hX)
    (V := gen (comp R A A₀ E₀))
  have hnd' := LeviQuot.isNondegenerate_quotClass (fun _ hX => le_gen hX)
    (fun _ hX _ hY hs => commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs) hnd
    (V := gen (comp R A A₀ E₀))
  have hZ' := LeviQuot.center_eq_bot (fun _ hX => le_gen hX)
    (fun _ hX => exists_conjSub_eq_of_mem_comp h hA hAne hA₀ hE₀ hX)
    (fun _ hX _ hY hs => commutator_mem_comp h hA hAne hA₀ hE₀ hX hY hs) rfl hnd
  exact ⟨inferInstance, hR', hnd', hZ', fun N hN hN2 =>
    TwoCore.eq_bot_of_rootClosure_eq_singleton hR' hiso' hnd' hZ'
      (rootClosure_quotClass_eq_singleton h hA hAne hA₀ hE₀ hnd) hN hN2⟩

theorem iSup_eq_of_iSup_quotMap_eq_top {ι : Type*} {A' B' : ι → Subgroup G}
    (hA' : ∀ k, A' k ∈ comp R A A₀ E₀) (hB' : ∀ k, B' k ∈ comp R A A₀ E₀)
    (himg : ⨆ k, (quotMap (gen (comp R A A₀ E₀)) (A' k) ⊔
      quotMap (gen (comp R A A₀ E₀)) (B' k)) = ⊤) :
    ⨆ k, (A' k ⊔ B' k) = gen (comp R A A₀ E₀) := by
  obtain ⟨F, hF, hEF⟩ := exists_opposite_mem_comp h hA hAne hA₀ hE₀ Relation.ReflTransGen.refl
  exact LeviQuot.iSup_eq_of_iSup_quotMap_eq_top_of_trans (fun _ hX => le_gen hX)
    (fun _ hX => exists_conjSub_eq_of_mem_comp h hA hAne hA₀ hE₀ hX) rfl
    ⟨E₀, Relation.ReflTransGen.refl, F, hF, hEF.not_commuting (h.root.ne_bot E₀ hE₀.1.1)⟩
    hA' hB' himg

theorem exists_isConfig_of_quot {r : ℕ} {adj : Fin r → Fin r → Prop}
    {A' B' : Fin r → Subgroup (↥(gen (comp R A A₀ E₀)) ⧸ Subgroup.center ↥(gen (comp R A A₀ E₀)))}
    (hX' : IsConfig (quotClass (gen (comp R A A₀ E₀)) (comp R A A₀ E₀)) adj A' B') :
    ∃ A₁ B₁ : Fin r → Subgroup G, IsConfig R adj A₁ B₁ ∧ ∀ k, A₁ k ∈ comp R A A₀ E₀ ∧
      B₁ k ∈ comp R A A₀ E₀ ∧ quotMap (gen (comp R A A₀ E₀)) (A₁ k) = A' k ∧
        quotMap (gen (comp R A A₀ E₀)) (B₁ k) = B' k := by
  have := h.finite
  exact IsConfig.of_correspondence (isRootClass_quot h hA hAne hA₀ hE₀) _
    (comp_subset_R h hA hAne hA₀ hE₀) (quot_hmap (E₀ := E₀)) (quot_hsurj (E₀ := E₀))
    (quot_hinj h hA hAne hA₀ hE₀) (quot_hcomm h hA hAne hA₀ hE₀) (quot_hopp h hA hAne hA₀ hE₀)
    (quot_hspec h hA hAne hA₀ hE₀) (quot_hcl h hA hAne hA₀ hE₀) hX'

end Quot

theorem eq_of_commuting_iff_of_mem_leviSet (h : Hyp G R) {A A₀ E E' : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hE' : E' ∈ leviSet R A A₀)
    (hnd : ∃ X ∈ comp R A A₀ E, ∃ Y ∈ comp R A A₀ E, Special R X Y)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) : E = E' := by
  refine eq_of_commuting_iff h hA hAne hA₀ hE hnd Relation.ReflTransGen.refl ?_ hEE'
  by_contra hn
  obtain ⟨F, hF, hEF⟩ := exists_opposite_mem_comp h hA hAne hA₀ hE Relation.ReflTransGen.refl
  have hFΛ := comp_subset h hA hAne hA₀ hE hF
  have hFE' : Commuting F E' := commuting_of_notMem_comp h hA hAne hA₀ hFΛ hE' (by
    rw [comp_eq_of_mem hF]
    exact hn)
  exact hEF.not_commuting (h.root.ne_bot E hE.1.1) ((hEE' F hFΛ).2 hFE'.symm)

theorem eq_of_commuting_iff_of_forall_special (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hnd : ∀ E ∈ leviSet R A A₀, ∃ X ∈ comp R A A₀ E, ∃ Y ∈ comp R A A₀ E, Special R X Y) :
    ∀ E ∈ leviSet R A A₀, ∀ E' ∈ leviSet R A A₀,
      (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E' :=
  fun _ hE _ hE' => eq_of_commuting_iff_of_mem_leviSet h hA hAne hA₀ hE hE' (hnd _ hE)

end Levi

end CFSG.Timmesfeld.ARS
