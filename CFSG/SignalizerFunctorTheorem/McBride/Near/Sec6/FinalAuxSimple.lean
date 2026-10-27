module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxComp

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem mem_centralizer_of_mem_centralizer_kOf {H K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (H : Set G)) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hC : H ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (haK : a ∈ Subgroup.centralizer (K : Set G)) : a ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hax : a * x * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp ha x).mp hx
  have hw : a * x * a⁻¹ * x⁻¹ ∈ H ⊓ Subgroup.centralizer (K : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hax (inv_mem hx), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk2 : x⁻¹ * k * x ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hKn (inv_mem hx)) k).mp hk
      simpa using this
    have e1 : Commute a⁻¹ (x⁻¹ * k * x) :=
      (Commute.inv_left ((Subgroup.mem_centralizer_iff.mp haK _ hk2).symm))
    have e2 : a * k = k * a := (Subgroup.mem_centralizer_iff.mp haK k hk).symm
    calc k * (a * x * a⁻¹ * x⁻¹)
        = (k * a) * x * a⁻¹ * x⁻¹ := by group
      _ = (a * k) * x * a⁻¹ * x⁻¹ := by rw [e2]
      _ = a * x * (x⁻¹ * k * x) * a⁻¹ * x⁻¹ := by group
      _ = a * x * (a⁻¹ * (x⁻¹ * k * x)) * x⁻¹ := by rw [e1.eq]; group
      _ = (a * x * a⁻¹ * x⁻¹) * k := by group
  rw [hC, Subgroup.mem_bot] at hw
  calc x * a = (a * x * a⁻¹ * x⁻¹)⁻¹ * (a * x) := by group
    _ = a * x := by rw [hw]; simp

section Simple

variable (h : Counterexample p A θ)

include h

theorem NT.lcal_eq_singleton
    {a : G} (ha : NT A θ a) (hs : FN A θ a = A) :
    ∃ J, lcal (θ a) = {J} ∧ kOf (θ a) = J := by
  obtain ⟨J₀, hJ₀⟩ := ha.lcal_nonempty h
  have hlc : lcal (θ a) = {J₀} := by
    ext J
    refine ⟨fun hJ => ?_, fun hJ => ?_⟩
    · obtain ⟨g, hgA, rfl⟩ := ha.exists_conj_A h hJ₀ hJ
      have hgF : g ∈ FN A θ a := by rw [hs]; exact hgA
      have hgN : g ∈ Subgroup.normalizer (J₀ : Set G) := (mem_FN_iff.mp hgF).2 J₀ hJ₀
      exact Set.mem_singleton_iff.mpr (Nonsolv.L69.map_conj_eq_self_iff.mpr hgN)
    · rw [Set.mem_singleton_iff] at hJ
      exact hJ ▸ hJ₀
  refine ⟨J₀, hlc, ?_⟩
  have := (ha.isDirectProduct h).sSup_eq
  rw [hlc, sSup_singleton] at this
  exact this.symm

theorem eq_thetaOf_of_simple
    {B : Subgroup G} (hB : B ∈ rSetN p A θ 2) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) (hs : FN A θ b = A) :
    θ b = thetaOf θ B ∧ B ≤ Subgroup.centralizer (kOf (θ b) : Set G) := by
  have hθ := h.hyp.nearFunctor
  have hbn := NT.of_mem_rSetN_two h hB hb hb1
  obtain ⟨hB1, hBA, hBns, -⟩ := h.mem_rSetN_iff.mp hB
  obtain ⟨J, hlc, hKJ⟩ := hbn.lcal_eq_singleton h hs
  have hJ : J ∈ lcal (θ b) := hlc ▸ Set.mem_singleton J
  have hBc : B ≤ Subgroup.centralizer (kOf (θ b) : Set G) := by
    by_contra hBc
    obtain ⟨β, hβB, hβc⟩ := IsConcreteLE.not_le_iff_exists.mp hBc
    have hβA : β ∈ A := hBA hβB
    have hβc' : β ∉ Subgroup.centralizer (J : Set G) := hKJ ▸ hβc
    have hβF : β ∈ FN A θ b := by rw [hs]; exact hβA
    have hβN : β ∈ A ⊓ Subgroup.normalizer (J : Set G) := ⟨hβA, (mem_FN_iff.mp hβF).2 J hJ⟩
    have hsolJ := hbn.isSolvable_cenIn_norIn h hJ
    rw [← hbn.cenIn_singleton_eq h hJ hβN hβc'] at hsolJ
    have hX : Group.IsSolvable ↥(thetaOf θ B ⊓ kOf (θ b)) := by
      refine Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (?_ : thetaOf θ B ⊓ kOf (θ b) ≤ J ⊓ Subgroup.centralizer ({β} : Set G)))
      intro y hy
      refine ⟨hKJ ▸ hy.2, ?_⟩
      have hyc := Subgroup.mem_centralizer_iff.mp (hθ.isFunctor.thetaOf_le_centralizer hBA hy.1)
        β hβB
      show y ∈ Subgroup.centralizer ({β} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyc.symm
    have hzR := hbn.zpowers_mem_rSet h
    obtain ⟨hz1, hzA, hzns⟩ := (h.mem_rSet_iff).mp hzR
    have hsec := h.lemma63a hz1 hzA hzns
    rw [hθ.isFunctor.thetaOf_zpowers hbn.mem hbn.ne_one] at hsec
    exact hBns (isSolvable_of_inf_of_section (K := kOf (θ b))
      (thetaOf_le_apply hb hb1) (Nonsolv.le_normalizer_kOf (θ b)) hsec hX)
  refine ⟨?_, hBc⟩
  have hsol := hbn.sol_eq_bot h
  have hcen : θ b ≤ Subgroup.centralizer (B : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    have := mem_centralizer_of_mem_centralizer_kOf
      (hθ.isFunctor.normalized b hbn.mem hbn.ne_one (hBA hβ)) (Nonsolv.le_normalizer_kOf (θ b))
      (centralizer_kOf_eq_bot hsol) (hBc hβ)
    exact (Subgroup.mem_centralizer_iff.mp this x hx).symm
  refine le_antisymm ?_ (thetaOf_le_apply hb hb1)
  have h1 := hθ.isFunctor.inf_centralizer_eq_thetaOf hbn.mem hbn.ne_one hBA
  rw [sup_eq_right.mpr (Subgroup.zpowers_le.mpr hb)] at h1
  rw [← h1]
  exact le_inf le_rfl hcen

theorem not_forall_simple
    {B : Subgroup G} (hB : B ∈ rSetN p A θ 2) {u : G} (hu : u ∈ B)
    (hu1 : u ≠ 1) : ¬ ∀ b ∈ B, b ∉ Subgroup.zpowers u → FN A θ b = A := by
  intro hall
  have hθ := h.hyp.nearFunctor
  obtain ⟨hB1, hBA, hBns, -⟩ := h.mem_rSetN_iff.mp hB
  have huA : u ∈ A := hBA hu
  have hle : wsub p A θ ≤ kOf (θ u) := by
    rw [← h.lemma64 hB]
    refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    by_cases hbu : b ∈ Subgroup.zpowers u
    · have hz : Subgroup.zpowers b = Subgroup.zpowers u :=
        (eq_zpowers_of_mem h (zpowers_mem_E1 h huA hu1) hbu hb1).symm
      rw [hθ.isFunctor.eq_of_zpowers_eq (hBA hb) hb1 huA hu1 hz]
    · obtain ⟨hθb, -⟩ := eq_thetaOf_of_simple h hB hb hb1 (hall b hb hbu)
      rw [hθb, ← h.perfRes_thetaOf_eq_kOf hB1 hBA hBns]
      exact (perfRes_mono (thetaOf_le_apply hu hu1)).trans (h.perfRes_apply_le_kOf huA hu1)
  have hmem : kOf (θ u) ∈ assoc p A θ :=
    mem_assoc_of_le hθ.prime (apply_mem_assoc hθ huA hu1) (kOf_le _)
      (Nonsolv.le_normalizer_kOf_of_le_normalizer (hθ.isFunctor.normalized u huA hu1))
  exact h.notComplete ⟨kOf (θ u), hmem, fun X hX => (le_sSup hX).trans hle⟩

theorem exists_zpowers_of_not_mem
    {E : Subgroup G} (hE : E ∈ signalizerFunctorEk p 1 A)
    (hn : E ∉ rSetN p A θ 1) :
    ∃ e ∈ A, e ≠ 1 ∧ Subgroup.zpowers e = E ∧ Group.IsSolvable (θ e) := by
  obtain ⟨e, heA, he1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.hyp.prime hE
  refine ⟨e, heA, he1, rfl, ?_⟩
  by_contra hns
  exact hn ((h.zpowers_mem_rSetN_one_iff).mpr ⟨heA, he1, hns⟩)

theorem eq_of_not_mem_rSetN
    {E₁ E₂ : Subgroup G} (h₁ : E₁ ∈ signalizerFunctorEk p 1 A)
    (h₂ : E₂ ∈ signalizerFunctorEk p 1 A) (hn₁ : E₁ ∉ rSetN p A θ 1)
    (hn₂ : E₂ ∉ rSetN p A θ 1) : E₁ = E₂ := by
  by_contra hne
  have hθ := h.hyp.nearFunctor
  obtain ⟨e₁, he₁A, he₁1, rfl, hs₁⟩ := exists_zpowers_of_not_mem h h₁ hn₁
  obtain ⟨e₂, he₂A, he₂1, rfl, hs₂⟩ := exists_zpowers_of_not_mem h h₂ hn₂
  set B₀ := Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ with hB₀
  have hB₀E : B₀ ∈ signalizerFunctorEk p 2 A := sup_mem_E2_of_ne h h₁ h₂ hne
  obtain ⟨B, hB⟩ := h.rSetN_two_nonempty
  obtain ⟨hB1, hBA, hBns, hBcard⟩ := h.mem_rSetN_iff.mp hB
  have hBE : B ∈ signalizerFunctorEk p 2 A := ⟨hBA, hBcard⟩
  have hBne : B ≠ B₀ := by
    intro heq
    apply hBns
    rw [heq]
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (thetaOf_anti (le_sup_left : Subgroup.zpowers e₁ ≤ B₀) |>.trans_eq
        (hθ.isFunctor.thetaOf_zpowers he₁A he₁1) : thetaOf θ B₀ ≤ θ e₁))
  have hinf := inf_mem_E1_of_ne_E2 h hBE hB₀E hBne
  obtain ⟨u, hu, hu1, hzu⟩ : ∃ u ∈ B ⊓ B₀, u ≠ 1 ∧ B ⊓ B₀ = Subgroup.zpowers u := by
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ B ⊓ B₀, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : B ⊓ B₀ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
      rw [this] at hinf
      have := hinf.2
      rw [Subgroup.card_bot] at this
      exact h.hyp.prime.one_lt.ne (by rw [pow_one] at this; exact this)
    exact ⟨u, hu, hu1, eq_zpowers_of_mem h hinf hu hu1⟩
  refine not_forall_simple h hB hu.1 hu1 fun b hbB hbu => ?_
  have hb1 : b ≠ 1 := fun h1 => hbu (h1 ▸ one_mem _)
  have hbn := NT.of_mem_rSetN_two h hB hbB hb1
  have hbB₀ : b ∉ B₀ := fun hb₀ => hbu (hzu ▸ (⟨hbB, hb₀⟩ : b ∈ B ⊓ B₀))
  have hbA : b ∈ A := hBA hbB
  have h1 : Subgroup.zpowers e₁ ≤ FN A θ b := by
    rw [Subgroup.zpowers_le]
    refine hbn.mem_FN_of_isSolvable h he₁A he₁1 ?_
    rw [sup_comm]
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (thetaOf_anti (le_sup_left : Subgroup.zpowers e₁ ≤ _) |>.trans_eq
        (hθ.isFunctor.thetaOf_zpowers he₁A he₁1)))
  have h2 : Subgroup.zpowers e₂ ≤ FN A θ b := by
    rw [Subgroup.zpowers_le]
    refine hbn.mem_FN_of_isSolvable h he₂A he₂1 ?_
    rw [sup_comm]
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (thetaOf_anti (le_sup_left : Subgroup.zpowers e₂ ≤ _) |>.trans_eq
        (hθ.isFunctor.thetaOf_zpowers he₂A he₂1)))
  have h3 : Subgroup.zpowers b ≤ FN A θ b := by
    rw [Subgroup.zpowers_le, mem_FN_iff]
    refine ⟨hbA, fun J hJ => ?_⟩
    have : b ∈ Subgroup.centralizer (θ b : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (hθ.isFunctor.le_centralizer b hbA hb1 hx)
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (lcal_le hJ)) this)
  have hsup := sup_zpowers_eq_top_of_not_mem h hB₀E hbA hbB₀
  have hle : A ≤ FN A θ b := hsup.symm.le.trans (sup_le (sup_le h1 h2) h3)
  exact le_antisymm (FN_le b) hle

end Simple

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
