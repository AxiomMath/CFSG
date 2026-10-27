module

public import CFSG.Quasithin.Background.FFC5T2
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.FFC5Piece
public import CFSG.Quasithin.Background.FFC5T1

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section T4

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem mem_zpowers_of_sq {M : Type*} [Group M] {u : M} (hu : u ^ 2 = 1) {y : M}
    (hy : y ∈ Subgroup.zpowers u) : y = 1 ∨ y = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : u ^ (2 : ℤ) = 1 := by simpa using hu
  have : u ^ k = u ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rw [this]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · left; simp
  · right; simp

theorem sup_zpowers_eq_top {X : Subgroup V} (hX : X.index = 2) {u : V} (hu : u ∉ X) :
    X ⊔ Subgroup.zpowers u = ⊤ := by
  rw [Subgroup.index_eq_two_iff] at hX
  obtain ⟨a, ha⟩ := hX
  have hcos : ∀ b : V, b ∉ X → b * a ∈ X := fun b hb => by
    rcases ha b with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hb
  rw [eq_top_iff]
  intro v _
  by_cases hv : v ∈ X
  · exact Subgroup.mem_sup_left hv
  · have h1 : v * u⁻¹ ∈ X := by
      have := X.mul_mem (hcos v hv) (X.inv_mem (hcos u hu))
      have e : v * a * (u * a)⁻¹ = v * u⁻¹ := by group
      rwa [e] at this
    have : v = (v * u⁻¹) * u := by simp
    rw [this]
    exact Subgroup.mul_mem_sup h1 (Subgroup.mem_zpowers u)

omit [CommGroup V] in
theorem card_zpowers_of_sq {M : Type*} [Group M] {u : M} (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    Nat.card ↥(Subgroup.zpowers u) = 2 := by
  have h1 : orderOf u = 2 := orderOf_eq_prime hu hne
  rw [Nat.card_zpowers, h1]

theorem U1_facts [Finite V] {W V₂ : Subgroup V} {u : V} (hbot : V₂ ⊓ W = ⊥) (huX : u ∉ W ⊔ V₂)
    (hu : u ^ 2 = 1) :
    (W ⊔ Subgroup.zpowers u) ⊓ V₂ = ⊥ ∧ Nat.card ↥(W ⊔ Subgroup.zpowers u) = 2 * Nat.card ↥W := by
  have huW : u ∉ W := fun h => huX (Subgroup.mem_sup_left h)
  have hu1 : u ≠ 1 := fun h => huW (h ▸ W.one_mem)
  have hWz : W ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxW, hxz⟩
    rcases mem_zpowers_of_sq hu hxz with h | h
    · exact Subgroup.mem_bot.2 h
    · exact absurd (h ▸ hxW) huW
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxV⟩
    obtain ⟨w, hw, y, hy, rfl⟩ := Subgroup.mem_sup.1 hx
    rcases mem_zpowers_of_sq hu hy with h1 | h1
    · rw [h1, mul_one] at hxV ⊢
      have : w ∈ V₂ ⊓ W := ⟨hxV, hw⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 this
    · exfalso
      apply huX
      rw [h1] at hxV
      have : u = w⁻¹ * (w * u) := by simp
      rw [this]
      exact Subgroup.mul_mem_sup (W.inv_mem hw) hxV
  · have := card_sup_mul_card_inf W (Subgroup.zpowers u)
    rw [hWz, Subgroup.card_bot, mul_one, card_zpowers_of_sq hu hu1] at this
    rw [this, mul_comm]

omit [CommGroup V] in
theorem map_sup3_mem {M : Type*} [CommGroup M] {W C W₁ : Subgroup M} {u : M} (g : MulAut M)
    (hu : g u ∈ W₁) (hw : ∀ w ∈ W, g w ∈ W₁)
    (hc : ∀ c ∈ C, g c ∈ W₁) : ∀ x ∈ W ⊔ Subgroup.zpowers u ⊔ C, g x ∈ W₁ := by
  intro x hx
  obtain ⟨y, hy, c, hcC, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨w, hwW, z, hz, rfl⟩ := Subgroup.mem_sup.1 hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [map_mul, map_mul, map_zpow]
  exact W₁.mul_mem (W₁.mul_mem (hw w hwW) (W₁.zpow_mem hu k)) (hc c hcC)

omit [CommGroup V] in
theorem perfect_of_natural3 {M : Type} [CommGroup M] {L : Subgroup (MulAut M)} {U : Subgroup M}
    (hnat : BinaryNaturalSL L U ⊥ 3 1) : ⁅L, L⁆ = L := by
  obtain ⟨D⟩ := exists_natQuot3 hnat
  have hp : Group.IsPerfect SL3F2 :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2) (n := 3) (le_refl 3)
  have : Group.IsPerfect ↥L := Group.IsPerfect.ofSurjective (f := D.ρ) D.surj
  exact Subgroup.isPerfect_iff.mp this

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem case3_of [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hnat : BinaryNaturalSL G₁ (commV G₁) ⊥ 3 1)
    (hidx : (commV G₁ ⊔ fixV G₁).index = 2) (hgood : GoodFactor (autSub G₂ (fixV G₁)))
    (hu : ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ ∧ ∀ g ∈ G₂, g u * u⁻¹ ∈ fixV G) : B56Case3 G := by
  obtain ⟨u, huX, hcu⟩ := hu
  obtain ⟨hF₂, hP₂⟩ := B510Fa.GoodFactor.transport h hgood
  have hbot : fixV G₁ ⊓ commV G₁ = ⊥ := by
    obtain ⟨K, hK, hf, hc, π, hπ⟩ := hnat
    exact fixV_inf_eq_bot_of_nat (by norm_num : 2 ≤ 3) hπ
  have hbot' : fixV G₁ ⊓ commV G₁ = ⊥ := hbot
  obtain ⟨hU₁V₂, hU₁card⟩ := U1_facts hbot huX (hV u)
  have hCV₂ : fixV G ≤ fixV G₁ := B1.fixV_le_fixV h.G₁_le
  have hCfix : ∀ c ∈ fixV G, ∀ g ∈ G, g c = c := fun c hc g hg => hc g hg
  have hWinv₁ : ∀ g ∈ G₁, ∀ w ∈ commV G₁, g w ∈ commV G₁ := commV_invariant_self G₁
  have hG₁u : ∀ g ∈ G₁, g u * u⁻¹ ∈ commV G₁ := fun g hg =>
    Subgroup.subset_closure ⟨g, hg, u, rfl⟩
  have hsub : ∀ (g : MulAut V), (g ∈ G₁ ∨ g ∈ G₂) →
      ∀ x ∈ commV G₁ ⊔ Subgroup.zpowers u ⊔ fixV G,
        g x ∈ commV G₁ ⊔ Subgroup.zpowers u ⊔ fixV G := by
    intro g hg
    apply map_sup3_mem
    · rcases hg with hg | hg
      · have : g u = (g u * u⁻¹) * u := by simp
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hG₁u g hg)))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
      · have : g u = (g u * u⁻¹) * u := by simp
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcu g hg))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
    · intro w hw
      rcases hg with hg | hg
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hWinv₁ g hg w hw))
      · rw [h.triv₁ g hg w hw]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hw)
    · intro c hc
      have hgc : g c = c := by
        rcases hg with hg | hg
        · exact hc g (h.G₁_le hg) |>.trans rfl
        · exact hc g (h.G₂_le hg)
      rw [hgc]
      exact Subgroup.mem_sup_right hc
  set W₁ : Subgroup V := commV G₁ ⊔ Subgroup.zpowers u ⊔ fixV G with hW₁
  have hinvG : ∀ g ∈ G, ∀ x ∈ W₁, g x ∈ W₁ := by
    intro g hg x hx
    have h1 : G₁ ≤ stabSub W₁ :=
      le_stabSub_of_invariant (fun g hg x hx => hsub g (Or.inl hg) x hx)
    have h2 : G₂ ≤ stabSub W₁ :=
      le_stabSub_of_invariant (fun g hg x hx => hsub g (Or.inr hg) x hx)
    have h3 : G ≤ stabSub W₁ := by rw [← h.sup]; exact sup_le h1 h2
    exact ((h3 hg) x).2 hx
  have hinvV₂ : ∀ g ∈ G, ∀ x ∈ fixV G₁, g x ∈ fixV G₁ := fun g hg x hx => (h.stab_G hg x).2 hx
  have hWW₁ : commV G₁ ≤ W₁ := le_sup_left.trans le_sup_left
  have hCW₁ : fixV G ≤ W₁ := le_sup_right
  have hsupTop : W₁ ⊔ fixV G₁ = ⊤ := by
    rw [eq_top_iff, ← sup_zpowers_eq_top hidx huX]
    refine sup_le (sup_le (hWW₁.trans le_sup_left) le_sup_right) ?_
    exact ((le_sup_right : Subgroup.zpowers u ≤ commV G₁ ⊔ Subgroup.zpowers u).trans
      (le_sup_left : commV G₁ ⊔ Subgroup.zpowers u ≤ W₁)).trans
      (le_sup_left : W₁ ≤ W₁ ⊔ fixV G₁)
  have hW₁V₂ : W₁ ⊓ fixV G₁ = fixV G := by
    refine le_antisymm ?_ (le_inf hCW₁ hCV₂)
    rintro x ⟨hx, hxV⟩
    obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.1 hx
    have hyV : y ∈ fixV G₁ := by
      have := (fixV G₁).mul_mem hxV ((fixV G₁).inv_mem (hCV₂ hc))
      simpa using this
    have : y ∈ (commV G₁ ⊔ Subgroup.zpowers u) ⊓ fixV G₁ := ⟨hy, hyV⟩
    rw [hU₁V₂, Subgroup.mem_bot] at this
    rw [this, one_mul]
    exact hc
  have hUC : (commV G₁ ⊔ Subgroup.zpowers u) ⊓ fixV G = ⊥ :=
    eq_bot_iff.2 (hU₁V₂ ▸ inf_le_inf_left _ hCV₂)
  have hcard : Nat.card ↥W₁ = 2 ^ 4 * Nat.card ↥(fixV G) := by
    have := card_sup_mul_card_inf (commV G₁ ⊔ Subgroup.zpowers u) (fixV G)
    rw [hUC, Subgroup.card_bot, mul_one, hU₁card] at this
    have h8 : Nat.card ↥(commV G₁) = 2 ^ 3 := (natural3_facts hnat).2
    show Nat.card ↥(commV G₁ ⊔ Subgroup.zpowers u ⊔ fixV G) = _
    rw [this, h8]
    ring
  have hperf : ⁅G₁, G₁⁆ = G₁ := perfect_of_natural3 hnat
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hnat
  have hirr := B5.isIrr_of_realizes (by norm_num : 2 ≤ 3) hπ
  have hUZ : commV G₁ ⊓ fixV G = ⊥ := eq_bot_iff.2 (by
    rw [← hbot, inf_comm]
    exact inf_le_inf_right _ hCV₂)
  have hnat' : BinaryNaturalSL G₁ (commV G₁ ⊔ fixV G) (fixV G) 3 1 :=
    ⟨K, hK, hf, hc, π, extend_fixV h.G₁_le hπ hUZ⟩
  have hmod : modComm G₁ W₁ = commV G₁ := by
    rw [modComm_eq_commSub]
    apply le_antisymm
    · exact (commSub_mono le_top le_rfl).trans (le_of_eq (commV_eq_commSub G₁).symm)
    · calc commV G₁ = commSub (commV G₁) G₁ := (B5.commSub_commV_eq hperf).symm
        _ ≤ commSub W₁ G₁ := commSub_mono hWW₁ le_rfl
  have hindec : ¬ ∃ A B : Subgroup V, fixV G < A ∧ fixV G < B ∧ XMod.IsInv ↥G₁ A ∧
      XMod.IsInv ↥G₁ B ∧ A ⊔ B = W₁ ∧ A ⊓ B = fixV G := by
    rintro ⟨A, B, hA, hB, hAi, hBi, hAB, hABC⟩
    have hclaim : ∀ X : Subgroup V, fixV G < X → XMod.IsInv ↥G₁ X → X ≤ W₁ → X ⊓ commV G₁ ≠ ⊥ := by
      intro X hCX hXi hXW₁ hbotX
      obtain ⟨x, hxX, hxC⟩ := IsConcreteLE.exists_of_lt hCX
      apply hxC
      have hx₁ : x ∈ fixV G₁ := by
        intro g hg
        have h1 : (g : MulAut V) x * x⁻¹ ∈ X ⊓ commV G₁ :=
          ⟨X.mul_mem (hXi ⟨g, hg⟩ x hxX) (X.inv_mem hxX), Subgroup.subset_closure ⟨g, hg, x, rfl⟩⟩
        rw [hbotX, Subgroup.mem_bot] at h1
        exact mul_inv_eq_one.1 h1
      rw [← hW₁V₂]
      exact ⟨hXW₁ hxX, hx₁⟩
    have hAW := hclaim A hA hAi (hAB ▸ le_sup_left)
    have hBW := hclaim B hB hBi (hAB ▸ le_sup_right)
    have hinvW : ∀ J : Subgroup V, XMod.IsInv ↥G₁ J → XMod.IsInv ↥G₁ (J ⊓ commV G₁) := fun J hJ a l hl =>
      ⟨hJ a l hl.1, hπ.2.2.2.1 a l hl.2⟩
    have hdich : ∀ X : Subgroup V, XMod.IsInv ↥G₁ X → X ⊓ commV G₁ ≠ ⊥ → commV G₁ ≤ X := by
      intro X hXi hne
      rcases hirr.2.2 (X ⊓ commV G₁) (hinvW X hXi) bot_le inf_le_right with h1 | h1
      · exact absurd h1 hne
      · exact inf_eq_right.1 h1
    have hWA := hdich A hAi hAW
    have hWB := hdich B hBi hBW
    have : commV G₁ ≤ fixV G := hABC ▸ le_inf hWA hWB
    have h2 : commV G₁ ≤ fixV G₁ ⊓ commV G₁ := le_inf (this.trans hCV₂) le_rfl
    rw [hbot] at h2
    have hnb : ⊥ < commV G₁ := hirr.2.1
    exact absurd (le_bot_iff.1 h2) hnb.ne'
  have hiso : Nonempty (↥G₁ ≃* ↥(StatedSL 3 (ZMod 2))) := (natural3_facts ⟨K, hK, hf, hc, π, hπ⟩).1
  have hF₁ : B56FactorList ↥G₁ :=
    Or.inr (Or.inr ⟨1, K, hK, hf, le_rfl, odd_one, hc,
      ⟨(MulEquiv.ofBijective π ⟨injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩).symm⟩⟩)
  refine ⟨G₁, G₂, h.sup, h.inf, h.comm, hF₁, hF₂, W₁, fixV G₁, hCW₁, hCV₂,
    fun a l hl => hinvG a a.2 l hl, fun a l hl => hinvV₂ a a.2 l hl, hsupTop, hW₁V₂, ?_, hP₂⟩
  refine Or.inr (Or.inr ⟨hiso, hWW₁, hcard, hindec, ?_⟩)
  rw [hmod]
  exact hnat'

end B510Fa

end T4

end FFC

end CFSG.Quasithin
