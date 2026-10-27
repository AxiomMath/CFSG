module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B51Sum

variable {V : Type} [CommGroup V]

theorem eq_of_card_le_two [Finite V] {S : Subgroup V} (hS : Nat.card S ≤ 2) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have : Fintype S := Fintype.ofFinite _
  have hcard : ({⟨1, S.one_mem⟩, ⟨x, hx⟩, ⟨y, hy⟩} : Finset S).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hxy (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨fun h => hx1 h.symm, fun h => hy1 h.symm⟩
  have h := Finset.card_le_univ ({⟨1, S.one_mem⟩, ⟨x, hx⟩, ⟨y, hy⟩} : Finset S)
  rw [hcard, Fintype.card_eq_nat_card] at h
  omega

theorem apply_mem_commSub {B : Subgroup (MulAut V)} {M : Subgroup V}
    (hBM : ∀ b ∈ B, ∀ x ∈ M, b x ∈ M) {b : MulAut V} (hb : b ∈ B) {d : V}
    (hd : d ∈ commSub M B) : b d ∈ commSub M B := by
  unfold commSub at hd ⊢
  induction hd using Subgroup.closure_induction with
  | mem d hd =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hd
    refine Subgroup.subset_closure ⟨b * x * b⁻¹, B.mul_mem (B.mul_mem hb hx) (B.inv_mem hb),
      b w, hBM b hb w hw, ?_⟩
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul d e _ _ hd he => rw [map_mul]; exact Subgroup.mul_mem _ hd he
  | inv d _ hd => rw [map_inv]; exact Subgroup.inv_mem _ hd

theorem apply_eq_of_mem_commSub [Finite V] {B : Subgroup (MulAut V)} {M : Subgroup V}
    (hBM : ∀ b ∈ B, ∀ x ∈ M, b x ∈ M) (hc : Nat.card (commSub M B) ≤ 2) {b : MulAut V}
    (hb : b ∈ B) {d : V} (hd : d ∈ commSub M B) : b d = d := by
  by_cases hd1 : d = 1
  · rw [hd1, map_one]
  · refine eq_of_card_le_two hc (apply_mem_commSub hBM hb hd) hd ?_ hd1
    intro h
    apply hd1
    rw [← map_one b] at h
    exact b.injective h

theorem card_le_relIndex_aux [Finite V] {M : Subgroup V} (n : ℕ) :
    ∀ B : Subgroup (MulAut V), Nat.card B = n → (∀ b ∈ B, ∀ x ∈ M, b x ∈ M) →
      (∀ b ∈ B, (∀ x ∈ M, b x = x) → b = 1) → Nat.card (commSub M B) ≤ 2 →
      Nat.card B ≤ (fixV B ⊓ M).relIndex M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hn hBM hf hc
  by_cases hB : B = ⊥
  · rw [hB, Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  obtain ⟨⟨b₀, hb₀B⟩, hb₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB
  have hb₀1 : b₀ ≠ 1 := fun h => hb₀ (Subtype.ext h)
  obtain ⟨x₀, hx₀M, hx₀⟩ : ∃ x₀ ∈ M, b₀ x₀ ≠ x₀ := by
    by_contra hno
    push Not at hno
    exact hb₀1 (hf b₀ hb₀B hno)
  have hmem : ∀ b ∈ B, b x₀ * x₀⁻¹ ∈ commSub M B := fun b hb =>
    Subgroup.subset_closure ⟨b, hb, x₀, hx₀M, rfl⟩
  let φ : ↥B →* ↥(commSub M B) :=
    { toFun := fun b => ⟨(b : MulAut V) x₀ * x₀⁻¹, hmem b b.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have h := apply_eq_of_mem_commSub hBM hc a.2 (hmem b b.2)
        rw [map_mul, map_inv] at h
        show (a : MulAut V) ((b : MulAut V) x₀) * x₀⁻¹ =
          ((a : MulAut V) x₀ * x₀⁻¹) * ((b : MulAut V) x₀ * x₀⁻¹)
        calc (a : MulAut V) ((b : MulAut V) x₀) * x₀⁻¹
            = ((a : MulAut V) ((b : MulAut V) x₀) * ((a : MulAut V) x₀)⁻¹) *
                ((a : MulAut V) x₀ * x₀⁻¹) := by group
          _ = ((b : MulAut V) x₀ * x₀⁻¹) * ((a : MulAut V) x₀ * x₀⁻¹) := by rw [h]
          _ = _ := mul_comm _ _ }
  set B₀ : Subgroup (MulAut V) := φ.ker.map B.subtype with hB₀
  have hB₀B : B₀ ≤ B := Subgroup.map_subtype_le _
  have hfixB₀ : ∀ b ∈ B₀, b x₀ = x₀ := by
    rintro _ ⟨b, hb, rfl⟩
    have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hb)
    exact mul_inv_eq_one.1 h
  have hcardB₀ : Nat.card B₀ = Nat.card φ.ker :=
    Subgroup.card_map_of_injective B.subtype_injective
  have hrange : Nat.card φ.range = 2 := by
    apply le_antisymm ((Subgroup.card_le_card_group _).trans hc)
    have hne : φ.range ≠ ⊥ := by
      intro hbot
      have h1 : φ ⟨b₀, hb₀B⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact hx₀ (mul_inv_eq_one.1 (congrArg Subtype.val h1))
    have h1 : Nat.card φ.range ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    have h0 : 0 < Nat.card φ.range := Nat.card_pos
    omega
  have hcardB : Nat.card B = Nat.card B₀ * 2 := by
    rw [hcardB₀, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hpos : 0 < Nat.card B₀ := Nat.card_pos
  have hlt : Nat.card B₀ < n := by omega
  have hc₀ : Nat.card (commSub M B₀) ≤ 2 :=
    (Subgroup.card_le_of_le (commSub_mono le_rfl hB₀B)).trans hc
  have hIH := ih _ hlt B₀ rfl (fun b hb => hBM b (hB₀B hb)) (fun b hb => hf b (hB₀B hb)) hc₀
  have hle : fixV B ⊓ M ≤ fixV B₀ ⊓ M :=
    inf_le_inf_right M fun x hx b hb => hx b (hB₀B hb)
  have hx₀B₀ : x₀ ∈ fixV B₀ ⊓ M := ⟨fun b hb => hfixB₀ b hb, hx₀M⟩
  have hidx : 2 ≤ (fixV B ⊓ M).relIndex (fixV B₀ ⊓ M) := by
    have h1 : (fixV B ⊓ M).relIndex (fixV B₀ ⊓ M) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro h
      exact hx₀ ((h hx₀B₀).1 b₀ hb₀B)
    have h0 : (fixV B ⊓ M).relIndex (fixV B₀ ⊓ M) ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  rw [← Subgroup.relIndex_mul_relIndex (fixV B ⊓ M) (fixV B₀ ⊓ M) M hle inf_le_right, hcardB,
    mul_comm (Subgroup.relIndex _ _)]
  exact Nat.mul_le_mul hIH hidx

theorem card_le_relIndex [Finite V] {B : Subgroup (MulAut V)} {M : Subgroup V}
    (hBM : ∀ b ∈ B, ∀ x ∈ M, b x ∈ M) (hf : ∀ b ∈ B, (∀ x ∈ M, b x = x) → b = 1)
    (hc : Nat.card (commSub M B) ≤ 2) : Nat.card B ≤ (fixV B ⊓ M).relIndex M :=
  card_le_relIndex_aux _ B rfl hBM hf hc

theorem fixV_inf_sup_le {B : Subgroup (MulAut V)} {I₁ I₂ : Subgroup V} (hI : I₁ ⊓ I₂ = ⊥)
    (h₁ : ∀ b ∈ B, ∀ x ∈ I₁, b x ∈ I₁) (h₂ : ∀ b ∈ B, ∀ x ∈ I₂, b x ∈ I₂) :
    fixV B ⊓ (I₁ ⊔ I₂) ≤ (fixV B ⊓ I₁) ⊔ (fixV B ⊓ I₂) := by
  rintro x ⟨hxB, hx⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Subgroup.mem_sup.1 hx
  have key : ∀ b ∈ B, b x₁ = x₁ ∧ b x₂ = x₂ := by
    intro b hb
    have hb' : b x₁ * b x₂ = x₁ * x₂ := by rw [← map_mul]; exact hxB b hb
    have hd : b x₁ * x₁⁻¹ ∈ I₁ ⊓ I₂ := by
      refine ⟨I₁.mul_mem (h₁ b hb x₁ hx₁) (I₁.inv_mem hx₁), ?_⟩
      have e : b x₁ * x₁⁻¹ = x₂ * (b x₂)⁻¹ := by
        have h3 : b x₁ = x₁ * x₂ * (b x₂)⁻¹ := by rw [← hb', mul_inv_cancel_right]
        rw [h3, mul_assoc x₁, mul_comm x₁, mul_inv_cancel_right]
      rw [e]
      exact I₂.mul_mem hx₂ (I₂.inv_mem (h₂ b hb x₂ hx₂))
    rw [hI, Subgroup.mem_bot, mul_inv_eq_one] at hd
    refine ⟨hd, ?_⟩
    rw [hd] at hb'
    exact mul_left_cancel hb'
  exact Subgroup.mul_mem_sup ⟨fun b hb => (key b hb).1, hx₁⟩ ⟨fun b hb => (key b hb).2, hx₂⟩

theorem commSub_ne_bot {B : Subgroup (MulAut V)} {I : Subgroup V} (hB : B ≠ ⊥)
    (hf : ∀ b ∈ B, (∀ x ∈ I, b x = x) → b = 1) : commSub I B ≠ ⊥ := by
  intro h
  apply hB
  rw [eq_bot_iff]
  intro b hb
  exact Subgroup.mem_bot.2 (hf b hb fun x hx => commSub_eq_bot_iff.1 h hx b hb)

theorem card_mul_card_le_index [Finite V] {B : Subgroup (MulAut V)} {I₁ I₂ : Subgroup V}
    (hI : I₁ ⊓ I₂ = ⊥) (h₁ : ∀ b ∈ B, ∀ x ∈ I₁, b x ∈ I₁) (h₂ : ∀ b ∈ B, ∀ x ∈ I₂, b x ∈ I₂)
    (hf₁ : ∀ b ∈ B, (∀ x ∈ I₁, b x = x) → b = 1) (hf₂ : ∀ b ∈ B, (∀ x ∈ I₂, b x = x) → b = 1)
    (hc : Nat.card (commV B) ≤ 4) : Nat.card B * Nat.card B ≤ (fixV B).index := by
  by_cases hB : B = ⊥
  · rw [hB, Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.2 Subgroup.index_ne_zero_of_finite
  have hc₁ := commSub_ne_bot hB hf₁
  have hc₂ := commSub_ne_bot hB hf₂
  have hd : commSub I₁ B ⊓ commSub I₂ B = ⊥ :=
    le_bot_iff.1 (hI ▸ inf_le_inf (commSub_le_of_invariant h₁) (commSub_le_of_invariant h₂))
  have hsup : commSub I₁ B ⊔ commSub I₂ B ≤ commV B := by
    rw [commV_eq_commSub]
    exact sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl)
  have hcard := card_sup_mul_card_inf (commSub I₁ B) (commSub I₂ B)
  rw [hd, Subgroup.card_bot, mul_one] at hcard
  have hle4 : Nat.card (commSub I₁ B) * Nat.card (commSub I₂ B) ≤ 4 :=
    hcard ▸ (Subgroup.card_le_of_le hsup).trans hc
  have h2₁ : 2 ≤ Nat.card (commSub I₁ B) := by
    have := Nat.card_pos (α := commSub I₁ B)
    have : Nat.card (commSub I₁ B) ≠ 1 := fun h => hc₁ (Subgroup.card_eq_one.1 h)
    omega
  have h2₂ : 2 ≤ Nat.card (commSub I₂ B) := by
    have := Nat.card_pos (α := commSub I₂ B)
    have : Nat.card (commSub I₂ B) ≠ 1 := fun h => hc₂ (Subgroup.card_eq_one.1 h)
    omega
  have hle₁ : Nat.card (commSub I₁ B) ≤ 2 := by nlinarith
  have hle₂ : Nat.card (commSub I₂ B) ≤ 2 := by nlinarith
  have hr₁ := card_le_relIndex h₁ hf₁ hle₁
  have hr₂ := card_le_relIndex h₂ hf₂ hle₂
  set F := fixV B with hF
  have hM := card_sup_mul_card_inf I₁ I₂
  rw [hI, Subgroup.card_bot, mul_one] at hM
  have hFd : (F ⊓ I₁) ⊓ (F ⊓ I₂) = ⊥ :=
    le_bot_iff.1 (hI ▸ inf_le_inf inf_le_right inf_le_right)
  have hFM := card_sup_mul_card_inf (F ⊓ I₁) (F ⊓ I₂)
  rw [hFd, Subgroup.card_bot, mul_one] at hFM
  have hFle : Nat.card ↥(F ⊓ (I₁ ⊔ I₂)) ≤ Nat.card ↥(F ⊓ I₁) * Nat.card ↥(F ⊓ I₂) :=
    hFM ▸ Subgroup.card_le_of_le (fixV_inf_sup_le hI h₁ h₂)
  have e₁ := Subgroup.relIndex_mul_card F I₁
  have e₂ := Subgroup.relIndex_mul_card F I₂
  have eM := Subgroup.relIndex_mul_card F (I₁ ⊔ I₂)
  rw [Subgroup.inf_relIndex_right] at hr₁ hr₂
  have hprod : F.relIndex I₁ * F.relIndex I₂ ≤ F.relIndex (I₁ ⊔ I₂) := by
    have hpos : 0 < Nat.card ↥(F ⊓ (I₁ ⊔ I₂)) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc F.relIndex I₁ * F.relIndex I₂ * Nat.card ↥(F ⊓ (I₁ ⊔ I₂))
        ≤ F.relIndex I₁ * F.relIndex I₂ * (Nat.card ↥(F ⊓ I₁) * Nat.card ↥(F ⊓ I₂)) :=
          Nat.mul_le_mul_left _ hFle
      _ = (F.relIndex I₁ * Nat.card ↥(F ⊓ I₁)) * (F.relIndex I₂ * Nat.card ↥(F ⊓ I₂)) := by
          ring
      _ = F.relIndex (I₁ ⊔ I₂) * Nat.card ↥(F ⊓ (I₁ ⊔ I₂)) := by rw [e₁, e₂, eM, hM]
  have hidx : F.relIndex (I₁ ⊔ I₂) ≤ F.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top Subgroup.index_ne_zero_of_finite
  calc Nat.card B * Nat.card B ≤ F.relIndex I₁ * F.relIndex I₂ := Nat.mul_le_mul hr₁ hr₂
    _ ≤ F.relIndex (I₁ ⊔ I₂) := hprod
    _ ≤ F.index := hidx

theorem four_lt_card_commV [Finite V] {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    {I₁ I₂ : Subgroup V} (hI : I₁ ⊓ I₂ = ⊥) (h₁ : ∀ a ∈ A, ∀ x ∈ I₁, a x ∈ I₁)
    (h₂ : ∀ a ∈ A, ∀ x ∈ I₂, a x ∈ I₂) (hf₁ : ∀ a ∈ A, (∀ x ∈ I₁, a x = x) → a = 1)
    (hf₂ : ∀ a ∈ A, (∀ x ∈ I₂, a x = x) → a = 1) : 4 < Nat.card (commV A) := by
  by_contra hle
  push Not at hle
  have hsq := card_mul_card_le_index hI h₁ h₂ hf₁ hf₂ hle
  have hff := hA.2.2.2 ⊥ bot_le
  have hfix : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
    rw [eq_top_iff]
    intro v _ x hx
    rw [Subgroup.mem_bot.1 hx]
    rfl
  rw [Subgroup.card_bot, one_mul, hfix, Subgroup.card_top] at hff
  have hidx := Subgroup.card_mul_index (fixV A)
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hCpos : 0 < Nat.card (fixV A) := Nat.card_pos
  have h1 : Nat.card A * Nat.card A * Nat.card (fixV A) ≤ Nat.card A * Nat.card (fixV A) := by
    calc Nat.card A * Nat.card A * Nat.card (fixV A) ≤ (fixV A).index * Nat.card (fixV A) :=
          Nat.mul_le_mul_right _ hsq
      _ = Nat.card V := by rw [mul_comm, hidx]
      _ ≤ _ := hff
  have h2 : Nat.card A * Nat.card A ≤ Nat.card A * 1 := by
    have := Nat.le_of_mul_le_mul_right (h1.trans (by rw [mul_comm])) hCpos
    simpa [mul_comm] using this
  have h3 : Nat.card A ≤ 1 := Nat.le_of_mul_le_mul_left h2 hApos
  exact hA.2.1 ((Subgroup.card_le_one_iff_eq_bot _).1 h3)

theorem matrix_eq_one_of_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {N : Matrix ι ι K} (h : ∀ v : ι → K, N.mulVec v = v) : N = 1 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h1
  rw [Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using h1

theorem eq_one_of_realizesVia_nat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : (FFModel.nat Γ).Gam →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U ⊥ π)
    {g : MulAut V} (hg : g ∈ H) (hgU : ∀ u ∈ U, g u = u) : g = 1 := by
  obtain ⟨hπ, -, -, -, -, -, -, β, hβ, -, hβe⟩ := h
  obtain ⟨γ, hγ⟩ := hπ ⟨g, hg⟩
  have hgu : ∀ u : ↥U, ((π γ : ↥H) : MulAut V) (u : V) = u := fun u => by
    rw [hγ]
    exact hgU u u.2
  set γ' : ↥Γ := γ with hγ'
  have hfix : ∀ v : ι → K, ((γ' : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec v = v := by
    intro v
    set m : Multiplicative (ι → K) := Multiplicative.ofAdd v with hm
    obtain ⟨u, hu⟩ := hβ (QuotientGroup.mk ⟨m, Subgroup.mem_top _⟩)
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := by rw [hgu u]; exact u.2
    have h1 := hβe γ u ⟨m, Subgroup.mem_top _⟩ hu' (Subgroup.mem_top _) hu
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext (hgu u)
    rw [h2, hu, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h5 : _ ∈ (⊥ : Subgroup (Multiplicative (ι → K))) := h1
    have h4 : m⁻¹ * natAct Γ γ' m = 1 := Subgroup.mem_bot.1 h5
    rw [inv_mul_eq_one] at h4
    exact (congrArg Multiplicative.toAdd h4).symm
  have hγ1 : γ' = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact matrix_eq_one_of_mulVec hfix
  have h1 : π γ' = 1 := by rw [hγ1]; exact map_one π
  rw [hγ] at h1
  exact congrArg Subtype.val h1

theorem eq_one_of_realizesVia_dualNat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : (FFModel.dualNat Γ).Gam →* ↥H} (h : (FFModel.dualNat Γ).RealizesVia H U ⊥ π)
    {g : MulAut V} (hg : g ∈ H) (hgU : ∀ u ∈ U, g u = u) : g = 1 := by
  obtain ⟨hπ, -, -, -, -, -, -, β, hβ, -, hβe⟩ := h
  obtain ⟨γ, hγ⟩ := hπ ⟨g, hg⟩
  have hgu : ∀ u : ↥U, ((π γ : ↥H) : MulAut V) (u : V) = u := fun u => by
    rw [hγ]
    exact hgU u u.2
  set γ' : ↥Γ := γ with hγ'
  have hfix : ∀ v : ι → K,
      (Matrix.transpose (((γ'⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).mulVec v =
        v := by
    intro v
    set m : Multiplicative (ι → K) := Multiplicative.ofAdd v with hm
    obtain ⟨u, hu⟩ := hβ (QuotientGroup.mk ⟨m, Subgroup.mem_top _⟩)
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := by rw [hgu u]; exact u.2
    have h1 := hβe γ u ⟨m, Subgroup.mem_top _⟩ hu' (Subgroup.mem_top _) hu
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext (hgu u)
    rw [h2, hu, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h5 : _ ∈ (⊥ : Subgroup (Multiplicative (ι → K))) := h1
    have h4 : m⁻¹ * dualNatAct Γ γ' m = 1 := Subgroup.mem_bot.1 h5
    rw [inv_mul_eq_one] at h4
    exact (congrArg Multiplicative.toAdd h4).symm
  have hγ1 : γ'⁻¹ = 1 := by
    apply Subtype.ext
    apply Units.ext
    have h := matrix_eq_one_of_mulVec hfix
    have h' := congrArg Matrix.transpose h
    rw [Matrix.transpose_transpose, Matrix.transpose_one] at h'
    exact h'
  rw [inv_eq_one] at hγ1
  have h1 : π γ' = 1 := by rw [hγ1]; exact map_one π
  rw [hγ] at h1
  exact congrArg Subtype.val h1

theorem four_lt_card_commV_of_case1ii [Finite V] {G L A : Subgroup (MulAut V)}
    (h : B51Case1ii G L) (hA : IsFFStarOffender G A) : 4 < Nat.card (commV A) := by
  obtain ⟨hGL, -, K, _, _, -, I, π, hind, -, hreal, -⟩ := h
  have hAL : A ≤ L := hGL ▸ hA.1
  have hinv : ∀ i, ∀ a ∈ A, ∀ x ∈ I i, a x ∈ I i := fun i a ha x hx =>
    (hreal i).2.2.2.1 ⟨a, hAL ha⟩ x hx
  have hdisj : I 0 ⊓ I 1 = ⊥ := disjoint_iff.1 (hind.pairwiseDisjoint (by decide))
  exact four_lt_card_commV hA hdisj (hinv 0) (hinv 1)
    (fun a ha hfix => eq_one_of_realizesVia_nat (hreal 0) (hAL ha) hfix)
    (fun a ha hfix => eq_one_of_realizesVia_nat (hreal 1) (hAL ha) hfix)

theorem four_lt_card_commV_of_case1iii [Finite V] {G L A : Subgroup (MulAut V)} {n : ℕ}
    (h : B51Case1iii G L n) (hA : IsFFStarOffender G A) : 4 < Nat.card (commV A) := by
  obtain ⟨hGL, -, π, U₁, U₂, ⟨-, hdisj⟩, hR₁, hR₂⟩ := h
  have hAL : A ≤ L := hGL ▸ hA.1
  exact four_lt_card_commV hA hdisj (fun a ha x hx => hR₁.2.2.2.1 ⟨a, hAL ha⟩ x hx)
    (fun a ha x hx => hR₂.2.2.2.1 ⟨a, hAL ha⟩ x hx)
    (fun a ha hfix => eq_one_of_realizesVia_nat hR₁ (hAL ha) hfix)
    (fun a ha hfix => eq_one_of_realizesVia_dualNat hR₂ (hAL ha) hfix)

theorem copies_eq_one_of_case1iv [Finite V] {G L A : Subgroup (MulAut V)}
    (h : B51Case1iv G L) (hA : IsFFStarOffender G A) (hc : Nat.card (commV A) ≤ 4) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      DirectSumOfCopies L (commV L) ⊥
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) 1 := by
  obtain ⟨hGL, n, hn, k, hk1, -, I, π, hZ, hind, hsup, hreal⟩ := h
  refine ⟨n, hn, ?_⟩
  have hAL : A ≤ L := hGL ▸ hA.1
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by omega
    exact ⟨I, π, hZ, hind, hsup, hreal⟩
  · exfalso
    set i₀ : Fin k := ⟨0, by omega⟩
    set i₁ : Fin k := ⟨1, by omega⟩
    have hne : i₁ ≠ i₀ := by
      intro h
      have := congrArg Fin.val h
      simp [i₀, i₁] at this
    have hdisj : I i₀ ⊓ I i₁ = ⊥ := by
      refine le_bot_iff.1 ((inf_le_inf_left _ ?_).trans (hind i₀).le)
      exact le_sup_of_le_right (le_iSup₂_of_le i₁ hne le_rfl)
    refine absurd hc (not_le.2 (four_lt_card_commV hA hdisj
      (fun a ha x hx => (hreal i₀).2.2.2.1 ⟨a, hAL ha⟩ x hx)
      (fun a ha x hx => (hreal i₁).2.2.2.1 ⟨a, hAL ha⟩ x hx)
      (fun a ha hfix => eq_one_of_realizesVia_nat (hreal i₀) (hAL ha) hfix)
      (fun a ha hfix => eq_one_of_realizesVia_nat (hreal i₁) (hAL ha) hfix)))

end B51Sum

end CFSG.Quasithin
