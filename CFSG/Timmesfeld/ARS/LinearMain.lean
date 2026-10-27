module

public import CFSG.Timmesfeld.ARS.LinearChain
public import CFSG.Timmesfeld.ARS.LinearSpan
public import CFSG.Timmesfeld.ARS.Cases
public import CFSG.Timmesfeld.ARS.Sec5Maximal
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.Timmesfeld.RankTwo.LeviData

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal Matrix

namespace Linear

namespace IsRootFrame

section Frame

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {m : ℕ}
  {X : Fin (m + 1) → Fin (m + 1) → Subgroup G} (hX : IsRootFrame R (m + 1) X)
include hX

theorem iSup_adj_eq_top : (⨆ k : Fin m, (X k.castSucc k.succ ⊔ X k.succ k.castSucc)) = ⊤ := by
  set L := ⨆ k : Fin m, (X k.castSucc k.succ ⊔ X k.succ k.castSucc) with hL
  have hadj : ∀ i j : Fin (m + 1), j.val = i.val + 1 → X i j ≤ L ∧ X j i ≤ L := by
    intro i j hij
    have hk : i.val < m := by omega
    have hi : (⟨i.val, hk⟩ : Fin m).castSucc = i := Fin.ext rfl
    have hj : (⟨i.val, hk⟩ : Fin m).succ = j := Fin.ext (by simp [hij])
    rw [← hi, ← hj]
    exact ⟨le_iSup_of_le (⟨i.val, hk⟩ : Fin m) le_sup_left,
      le_iSup_of_le (⟨i.val, hk⟩ : Fin m) le_sup_right⟩
  have hcomm : ∀ H K : Subgroup G, H ≤ L → K ≤ L → ⁅H, K⁆ ≤ L := fun H K hH hK =>
    Subgroup.commutator_le.2 fun h hh k hk => by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem (hH hh) (hK hk)) (L.inv_mem (hH hh)))
        (L.inv_mem (hK hk))
  have key : ∀ d (i j : Fin (m + 1)), j.val = i.val + (d + 1) → X i j ≤ L ∧ X j i ≤ L := by
    intro d
    induction d with
    | zero => exact fun i j hij => hadj i j hij
    | succ d ih =>
      intro i j hij
      set i' : Fin (m + 1) := ⟨i.val + 1, by omega⟩
      have h1 := hadj i i' rfl
      have h2 := ih i' j (by simp only [i']; omega)
      have hii' : i ≠ i' := fun h => by
        have := congrArg Fin.val h
        simp only [i'] at this
        omega
      have hi'j : i' ≠ j := fun h => by
        have := congrArg Fin.val h
        simp only [i'] at this
        omega
      have hij' : i ≠ j := fun h => by
        have := congrArg Fin.val h
        omega
      refine ⟨?_, ?_⟩
      · rw [← (hX.special i i' j hii' hi'j hij').2]
        exact hcomm _ _ h1.1 h2.1
      · rw [← (hX.special j i' i hi'j.symm hii'.symm hij'.symm).2]
        exact hcomm _ _ h2.2 h1.2
  rw [eq_top_iff, ← hX.iSup_eq_top]
  refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hv with h | h
  · exact (key (j.val - i.val - 1) i j (by omega)).1
  · exact (key (i.val - j.val - 1) j i (by omega)).2

theorem config {i j : Fin m} (hij : j.val = i.val + 1) :
    Special R (X i.castSucc i.succ) (X j.castSucc j.succ) ∧
      Commuting (X i.succ i.castSucc) (X j.castSucc j.succ) ∧
      ⁅X i.succ i.castSucc, ⁅X i.castSucc i.succ, X j.castSucc j.succ⁆⁆ = X j.castSucc j.succ ∧
      Commuting (X i.castSucc i.succ) (X j.succ j.castSucc) ∧
      ⁅⁅X i.castSucc i.succ, X j.castSucc j.succ⁆, X j.succ j.castSucc⁆ = X i.castSucc i.succ ∧
      Special R (X i.succ i.castSucc) (X j.succ j.castSucc) := by
  rw [castSucc_eq_succ_of_val (m := m) hij]
  have hv : ∀ a b : Fin (m + 1), a.val ≠ b.val → a ≠ b := fun a b h e => h (congrArg Fin.val e)
  have hab : i.castSucc ≠ i.succ := hv _ _ (by simp)
  have hbc : i.succ ≠ j.succ := hv _ _ (by simp only [Fin.val_succ]; omega)
  have hac : i.castSucc ≠ j.succ := hv _ _ (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  refine ⟨(hX.special _ _ _ hab hbc hac).1, hX.commuting _ _ _ _ hab.symm hbc hbc hab.symm, ?_,
    hX.commuting _ _ _ _ hab hbc.symm hab hbc.symm, ?_, (hX.special _ _ _ hbc.symm hab.symm
      hac.symm).1.symm⟩
  · rw [(hX.special _ _ _ hab hbc hac).2]
    exact (hX.special _ _ _ hab.symm hac hbc).2
  · rw [(hX.special _ _ _ hab hbc hac).2]
    exact (hX.special _ _ _ hac hbc.symm hab).2

end Frame

theorem lieModel {G : Type} [Group G] [Finite G] {R : Set (Subgroup G)} (hR : IsRootClass R)
    (hiso : NoIsolated R) (hZ : Subgroup.center G = ⊥) {m : ℕ} (hm : 2 ≤ m)
    {X : Fin (m + 1) → Fin (m + 1) → Subgroup G} (hX : IsRootFrame R (m + 1) X) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      Blueprint.LieModel G .PSL (m + 1) 2 f := by
  set k₀ : Fin m := ⟨0, by omega⟩
  have hne : ∀ k : Fin m, k.castSucc ≠ k.succ := fun k => Fin.castSucc_lt_succ.ne
  have hA : ∀ k : Fin m, X k.castSucc k.succ ∈ R := fun k => hX.mem _ _ (hne k)
  have hB : ∀ k : Fin m, X k.succ k.castSucc ∈ R := fun k => hX.mem _ _ (hne k).symm
  have hAB : ∀ k : Fin m, Opposite (X k.castSucc k.succ) (X k.succ k.castSucc) :=
    fun k => hX.opposite _ _ (hne k)
  obtain ⟨n, hn, hq, φ₀, hφ₀, hφ₀'⟩ := (hAB k₀).exists_mulEquiv_SL2' hR (hA k₀)
  obtain ⟨hinj₀, hup₀, hlow₀⟩ := injective_of_mulEquiv φ₀ hφ₀ hφ₀'
  obtain ⟨ρ, -, hρ, hedge⟩ := exists_chain hR hiso hA hB hAB (fun i j hij => hX.config hij) k₀
    hq hinj₀ hup₀ hlow₀
  set F := GaloisField 2 n
  have hcard : ∀ E ∈ R, Nat.card E = 2 ^ n := fun E hE => (hR.card_eq hE (hA k₀)).trans hq
  have hF : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  have hu : ∀ k, Set.range (fun c => ρ k (tv 0 1 c)) = (X k.castSucc k.succ : Set G) :=
    fun k => by rw [← (hρ k).2.1]; exact range_tv_upper (ρ k)
  have hv : ∀ k, Set.range (fun c => ρ k (tv 1 0 c)) = (X k.succ k.castSucc : Set G) :=
    fun k => by rw [← (hρ k).2.2]; exact range_tv_lower (ρ k)
  have hgen : Subgroup.closure (⋃ k, Set.range (fun c => ρ k (tv 0 1 c)) ∪
      Set.range (fun c => ρ k (tv 1 0 c))) = ⊤ := by
    rw [Subgroup.closure_iUnion]
    simp_rw [Subgroup.closure_union, hu, hv, Subgroup.closure_eq]
    exact hX.iSup_adj_eq_top
  have hnt : ∃ k c, ρ k (tv 0 1 c) ≠ 1 := by
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hA k₀)
    rw [← SetLike.mem_coe, ← hu] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨k₀, c, ha1⟩
  refine ⟨n, hn, hcard, ?_⟩
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    obtain rfl : m = 2 := by omega
    obtain ⟨ψ, hψ⟩ := hedge ⟨0, by omega⟩ ⟨1, by omega⟩ rfl
    have hsurj : Function.Surjective ψ := by
      rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_range] at hg
      obtain ⟨k, ⟨c, rfl⟩ | ⟨c, rfl⟩⟩ := hg <;> fin_cases k
      · exact MonoidHom.mem_range.2 ⟨tv 0 1 c, (hψ c).1⟩
      · exact MonoidHom.mem_range.2 ⟨tv 1 2 c, (hψ c).2.2.1⟩
      · exact MonoidHom.mem_range.2 ⟨tv 1 0 c, (hψ c).2.1⟩
      · exact MonoidHom.mem_range.2 ⟨tv 2 1 c, (hψ c).2.2.2⟩
    obtain ⟨k, c, hc⟩ := hnt
    obtain ⟨g, hg⟩ := hsurj (ρ k (tv 0 1 c))
    exact lieModel_of_center_eq_bot hZ (lieModel_quotient_of_surjective
      (SpecialLinear.isQuasisimple 2 F le_rfl) (lieModel_SL3_quotient Nat.prime_two hn hF) hsurj
      ⟨g, by rw [hg]; exact hc⟩)
  ·
    have hfr : SimplyLacedFrame (SpecialLinear.rootDatum m F) F (fun i j => j.val = i.val + 1)
        (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
      refine ⟨fun i j hij => hedge i j hij, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩,
        fun i j hij h1 h2 c d => ?_⟩
      change Fin m at i j
      have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
      have hv' : ∀ a b : Fin (m + 1), a.val ≠ b.val → a ≠ b :=
        fun a b h e => h (congrArg Fin.val e)
      have mu : ∀ k c, ρ k (tv 0 1 c) ∈ X k.castSucc k.succ := fun k c => by
        rw [← SetLike.mem_coe, ← hu]
        exact ⟨c, rfl⟩
      have mv : ∀ k c, ρ k (tv 1 0 c) ∈ X k.succ k.castSucc := fun k c => by
        rw [← SetLike.mem_coe, ← hv]
        exact ⟨c, rfl⟩
      refine ⟨hX.commuting _ _ _ _ (hne i) (hne j) (hv' _ _ ?_) (hv' _ _ ?_) _ (mu i c) _ (mu j d),
        hX.commuting _ _ _ _ (hne i) (hne j).symm (hv' _ _ ?_) (hv' _ _ ?_) _ (mu i c) _ (mv j d),
        hX.commuting _ _ _ _ (hne i).symm (hne j) (hv' _ _ ?_) (hv' _ _ ?_) _ (mv i c) _ (mu j d),
        hX.commuting _ _ _ _ (hne i).symm (hne j).symm (hv' _ _ ?_) (hv' _ _ ?_) _ (mv i c) _
          (mv j d)⟩ <;>
        simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
    exact lieModel_of_simplyLacedFrame
      (CurtisTits.curtisTitsConclusion_specialLinear
        ⟨Nat.prime_two, hn, by omega, fun h => by injection h; omega,
          fun h => by injection h; omega⟩ hF hm3)
      (leviConePresented_specialLinear m F) (simplyLacedLevis_specialLinear m F) hZ hfr hgen hnt

end IsRootFrame

end Linear

theorem lieModel_PSL_of_isTI' {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) :
    ∃ m f : ℕ, Nat.card ↥(gen Δ) = Nat.card A ^ m ∧ Nat.card A = 2 ^ f ∧ 2 ≤ m ∧ 1 ≤ f ∧
      Blueprint.LieModel G .PSL (m + 1) 2 f := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow hR hiso hnd hΩ hΔ.isWeakTI hA
  obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame hR hiso hnd hΩ hΔ hA hm
  obtain ⟨f, hf, hcard, hL⟩ := hX.lieModel hR hiso h.center hm2
  exact ⟨m, f, hm, hcard A (hΔ.1 hA), hm2, hf, hL⟩

theorem lieModel_PSL_of_isTI {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {Δ : Set (Subgroup G)} (hΔ : IsTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) :
    ∃ n f : ℕ, 3 ≤ n ∧ 1 ≤ f ∧ Blueprint.LieModel G .PSL n 2 f := by
  obtain ⟨m, f, -, -, hm2, hf, hL⟩ := lieModel_PSL_of_isTI' h hΔ hA
  exact ⟨m + 1, f, by omega, hf, hL⟩

theorem caseLInput : CaseLInput := by
  intro G _ R h A hA hmax
  obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
  exact Or.inl (lieModel_PSL_of_isTI h hΔ hAΔ)

end CFSG.Timmesfeld.ARS
