module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFive
public import CFSG.Quasithin.Recognition.Kleidman.F204.CritBasic

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

@[expose] def MaxElem (Q : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ Q ∧ IsElemAbelian 2 A ∧ ∀ B : Subgroup G, B ≤ Q → IsElemAbelian 2 B →
    Nat.card B ≤ Nat.card A}

omit [Finite G] in
theorem isElemAbelian_conjSub {A : Subgroup G} (h : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (conjSub g A) := by
  obtain ⟨hc, hsq⟩ := h
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have hx : g⁻¹ * (x : G) * g ∈ A := mem_conjSub.mp x.2
    have hy : g⁻¹ * (y : G) * g ∈ A := mem_conjSub.mp y.2
    have := congrArg Subtype.val (hc.is_comm.comm (⟨_, hx⟩ : A) (⟨_, hy⟩ : A))
    simp only [Subgroup.coe_mul] at this
    have e : (x : G) * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    have e2 : (y : G) * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    show (x : G) * y = y * x
    rw [e, e2, this]
  · have hx' : g⁻¹ * x * g ∈ A := mem_conjSub.mp hx
    have := hsq _ hx'
    have hcp := conj_pow (a := g⁻¹) (b := x) (i := 2)
    simp only [inv_inv] at hcp
    have e : x ^ 2 = g * ((g⁻¹ * x * g) ^ 2) * g⁻¹ := by rw [hcp]; group
    rw [e, this]; group

omit [Finite G] in
theorem conjSub_mem_MaxElem {Q : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    {A : Subgroup G} (hA : A ∈ MaxElem Q) : conjSub g A ∈ MaxElem Q := by
  obtain ⟨hAQ, hAe, hAmax⟩ := hA
  have hgQ : conjSub g Q = Q := conjSub_eq_of_mem_normalizer hg
  have hgiQ : conjSub g⁻¹ Q = Q := conjSub_eq_of_mem_normalizer (inv_mem hg)
  refine ⟨?_, isElemAbelian_conjSub hAe g, fun B hB hBe => ?_⟩
  · rw [← hgQ]; exact conjSub_mono g hAQ
  · have h1 : conjSub g⁻¹ B ≤ Q := by rw [← hgiQ]; exact conjSub_mono g⁻¹ hB
    have h2 := hAmax _ h1 (isElemAbelian_conjSub hBe g⁻¹)
    rw [card_conjSub] at h2
    rw [card_conjSub]; exact h2

omit [Finite G] in
theorem iSup_MaxElem_normalized (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((⨆ A ∈ MaxElem Q, A : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G),
      ∀ x ∈ (⨆ A ∈ MaxElem Q, A : Subgroup G), g * x * g⁻¹ ∈ (⨆ A ∈ MaxElem Q, A : Subgroup G) := by
    intro g hg x hx
    have hle : (⨆ A ∈ MaxElem Q, A : Subgroup G) ≤
        (⨆ A ∈ MaxElem Q, A : Subgroup G).comap (MulAut.conj g).toMonoidHom := by
      refine iSup₂_le fun A hA => ?_
      intro y hy
      have : conjSub g A ≤ (⨆ A ∈ MaxElem Q, A : Subgroup G) :=
        le_iSup₂_of_le (conjSub g A) (conjSub_mem_MaxElem hg hA) le_rfl
      exact this (mem_conjSub_of_mem' hy)
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem isElemAbelian_bot : IsElemAbelian 2 (⊥ : Subgroup G) :=
  ⟨⟨⟨fun x y => by
      apply Subtype.ext
      have hx : (x : G) = 1 := Subgroup.mem_bot.mp x.2
      have hy : (y : G) = 1 := Subgroup.mem_bot.mp y.2
      simp [hx, hy]⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx]; simp⟩

theorem MaxElem_nonempty (Q : Subgroup G) : ∃ A, A ∈ MaxElem Q := by
  have hne : ({A : Subgroup G | A ≤ Q ∧ IsElemAbelian 2 A} : Set (Subgroup G)).Nonempty :=
    ⟨⊥, bot_le, isElemAbelian_bot⟩
  obtain ⟨A, ⟨hAQ, hAe⟩, hA⟩ := Set.exists_max_image
    ({A : Subgroup G | A ≤ Q ∧ IsElemAbelian 2 A} : Set (Subgroup G)) (fun A => Nat.card A)
    (Set.toFinite _) hne
  exact ⟨A, hAQ, hAe, fun B hB hBe => hA B ⟨hB, hBe⟩⟩

theorem exists_maxElem_not_le (F : Frame L1 L2 S D X) {δ u : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hu : u ∈ nbrs δ)
    (hR : stab δ ≤ Subgroup.normalizer ((Qv δ ⊓ Qv u : Subgroup G) : Set G)) :
    ∃ A ∈ MaxElem (Qv u), ¬ A ≤ Qv δ := by
  by_contra hcon
  have hcon : ∀ A ∈ MaxElem (Qv u), A ≤ Qv δ := fun A hA' => by
    by_contra hn; exact hcon ⟨A, hA', hn⟩
  have hA := Amal.of_frame F
  obtain ⟨A0, hA0⟩ := MaxElem_nonempty (Qv u)
  have hEq : MaxElem (Qv δ ⊓ Qv u) = MaxElem (Qv u) := by
    ext A
    constructor
    · rintro ⟨hAR, hAe, hAmax⟩
      have hA0R : A0 ≤ Qv δ ⊓ Qv u := le_inf (hcon A0 hA0) hA0.1
      have h1 := hAmax A0 hA0R hA0.2.1
      refine ⟨hAR.trans inf_le_right, hAe, fun B hB hBe => ?_⟩
      exact (hA0.2.2 B hB hBe).trans h1
    · intro hAm
      refine ⟨le_inf (hcon A hAm) hAm.1, hAm.2.1, fun B hB hBe => hAm.2.2 B (hB.trans inf_le_right) hBe⟩
  set J : Subgroup G := ⨆ A ∈ MaxElem (Qv u), A with hJ
  have hQu_st : Qv u ≤ stab u := pCoreOf_le 2 (stab u)
  have hQu_sd : Qv u ≤ stab δ := hA.Qv_le_stab_of_mem_nbrs (show δ ∈ nbrs u from (show (graph _ _ _).Adj δ u from hu).symm)
  have hJle : J ≤ stab δ ⊓ stab u := by
    refine iSup₂_le fun A hA' => ?_
    exact le_inf (hA'.1.trans hQu_sd) (hA'.1.trans hQu_st)
  have hNu : stab u ≤ Subgroup.normalizer (J : Set G) :=
    (le_normalizer_pCoreOf 2 (stab u)).trans (iSup_MaxElem_normalized (Qv u))
  have hNδ : stab δ ≤ Subgroup.normalizer (J : Set G) := by
    have := hR.trans (iSup_MaxElem_normalized (Qv δ ⊓ Qv u))
    rwa [hEq] at this
  have hJbot : J = ⊥ := hA.eq_bot_of_normalizes_both hu hJle hNδ hNu
  have hQne : Qv u ≠ ⊥ := hA.Qv_ne_bot u
  have hp2 : IsPGroup 2 (Qv u) := pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := hp2.exists_card_eq
  have hk1 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hQne (Subgroup.eq_bot_of_card_eq _ hk)
  have h2dvd : 2 ∣ Nat.card (Qv u) := by
    rw [hk]; exact dvd_pow_self 2 hk1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Qv u) 2 h2dvd
  have hB : Subgroup.zpowers (x : G) ≤ Qv u := (Subgroup.zpowers_le).mpr x.2
  have hBe : IsElemAbelian 2 (Subgroup.zpowers (x : G)) := by
    refine ⟨inferInstance, fun z hz => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hx2 : (x : G) ^ 2 = 1 := by
      have : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      simpa using congrArg Subtype.val this
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = 2 := by
    have ho : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    rw [Nat.card_zpowers, ho]
  have h2le : 2 ≤ Nat.card A0 := hcard ▸ hA0.2.2 _ hB hBe
  have hA0bot : A0 ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at h2le; omega
  apply hA0bot
  rw [eq_bot_iff, ← hJbot]
  exact le_iSup₂_of_le A0 hA0 le_rfl

end CFSG.Quasithin.Kleidman.F204
