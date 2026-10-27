module

public import CFSG.Quasithin.Vol2.Ch10SecEProd
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem oTwoUpper_oTwoUpper (H : Subgroup G) : oTwoUpper (oTwoUpper H) = oTwoUpper H :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)

variable [Finite G]

theorem oTwoUpper_autI {V : Subgroup G} (hV : IsElemAbelian 2 V) {H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) :
    oTwoUpper (autI hV H) = autI hV (oTwoUpper H) := by
  set N := Subgroup.normalizer (V : Set G)
  have h1 : oTwoUpper (H.subgroupOf N) = (oTwoUpper H).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le hHN,
      Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le H).trans hHN)]
  unfold autI
  rw [oTwoUpper_map, h1]

theorem iSup_pair_ne {X : Type*} [Group X] [DecidableEq (Subgroup X)] {K₁ K₂ : Subgroup X}
    (hne : K₂ ≠ K₁) : (⨆ L' ∈ ({K₁, K₂} : Finset (Subgroup X)), ⨆ (_ : L' ≠ K₁), L') = K₂ := by
  apply le_antisymm
  · refine iSup₂_le fun L' hL' => iSup_le fun h => ?_
    rcases Finset.mem_insert.mp hL' with rfl | hL'
    · exact absurd rfl h
    · rw [Finset.mem_singleton.mp hL']
  · exact le_iSup₂_of_le (f := fun L' _ => ⨆ (_ : L' ≠ K₁), L') K₂ (by simp)
      (le_iSup_of_le hne le_rfl)

theorem oTwoUpper_conjAut_eq_bot {W : Type*} [CommGroup W] {g : MulAut W}
    {K : Subgroup (MulAut W)} (h : oTwoUpper K = ⊥) : oTwoUpper (B1.conjAut g K) = ⊥ := by
  refine le_bot_iff.mp ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hx, ho⟩
  have hx' := B1.mem_conjAut.mp hx
  have hord : orderOf (g⁻¹ * x * g) = orderOf x := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    rwa [MulAut.conj_apply, inv_inv] at h1
  have h1 : g⁻¹ * x * g ∈ oTwoUpper K := mem_oTwoUpper_of_odd hx' (hord ▸ ho)
  rw [h, Subgroup.mem_bot] at h1
  have : x = 1 := by
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [SetLike.mem_coe, this]
  exact Subgroup.one_mem _

theorem eq_oTwoUpper_of_e23 {V : Subgroup G} (hV : IsElemAbelian 2 V) {H T : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) {A B : Subgroup (MulAut (IntMod V hV))}
    (hAs : IsSimpleGroup ↥A) (hBs : IsSimpleGroup ↥B)
    (hAn : ∃ a ∈ A, ∃ a' ∈ A, a * a' ≠ a' * a) (hBn : ∃ b ∈ B, ∃ b' ∈ B, b * b' ≠ b' * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hN : autI hV (oTwoUpper H) = A ⊔ B) (hJ : oTwoUpper H ≤ thompsonJ H)
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (hcard : I.card = 1 ∨ I.card = 2)
    (hJeq : autI hV (thompsonJ H) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (htrans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L') :
    (∃ K ∈ I, (∀ K' ∈ I, K' = K) ∧ autI hV (thompsonJ H) = K ∧ oTwoUpper K = A ⊔ B) ∨
      ∃ K₁ ∈ I, ∃ K₂ ∈ I, (∀ K ∈ I, K = K₁ ∨ K = K₂) ∧ K₁ ≠ K₂ ∧
        autI hV (thompsonJ H) = K₁ ⊔ K₂ ∧ oTwoUpper K₁ = A ∧ oTwoUpper K₂ = B ∧
        (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ K₁ ⊓ K₂ = ⊥ := by
  classical
  have hKH : ∀ K ∈ I, K ≤ autI hV H := fun K hK =>
    (le_iSup₂_of_le (f := fun L (_ : L ∈ I) => L) K hK le_rfl).trans
      (hJeq.symm.le.trans (autI_mono hV (iSup₂_le fun _ hA => hA.1)))
  have hOK : ∀ K ∈ I, oTwoUpper K ≤ A ⊔ B := fun K hK =>
    (oTwoUpper_mono (hKH K hK)).trans ((oTwoUpper_autI hV hHN).le.trans hN.le)
  have hNJ : A ⊔ B ≤ oTwoUpper (autI hV (thompsonJ H)) := by
    calc A ⊔ B = autI hV (oTwoUpper H) := hN.symm
      _ = autI hV (oTwoUpper (oTwoUpper H)) := by rw [oTwoUpper_oTwoUpper]
      _ = oTwoUpper (autI hV (oTwoUpper H)) :=
        (oTwoUpper_autI hV ((oTwoUpper_le H).trans hHN)).symm
      _ ≤ oTwoUpper (autI hV (thompsonJ H)) := oTwoUpper_mono (autI_mono hV hJ)
  rcases hcard with h1 | h2
  · obtain ⟨K, rfl⟩ := Finset.card_eq_one.mp h1
    have hJK : autI hV (thompsonJ H) = K := by rw [hJeq, Finset.iSup_singleton]
    refine Or.inl ⟨K, Finset.mem_singleton_self K, fun K' h => Finset.mem_singleton.mp h, hJK,
      le_antisymm (hOK K (Finset.mem_singleton_self K)) (hJK ▸ hNJ)⟩
  · obtain ⟨K₁, K₂, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hK₁ : K₁ ∈ ({K₁, K₂} : Finset _) := Finset.mem_insert_self _ _
    have hK₂ : K₂ ∈ ({K₁, K₂} : Finset _) := by simp
    have hJK : autI hV (thompsonJ H) = K₁ ⊔ K₂ := by
      rw [hJeq, Finset.iSup_insert, Finset.iSup_singleton]
    have hc := hcomm K₁ hK₁ K₂ hK₂ hne
    have hi : K₁ ⊓ K₂ = ⊥ := by
      have := hind K₁ hK₁
      rwa [iSup_pair_ne hne.symm] at this
    have hNO : A ⊔ B ≤ oTwoUpper K₁ ⊔ oTwoUpper K₂ := (hJK ▸ hNJ).trans (oTwoUpper_sup_le hc hi)
    have hAbot : A ⊔ B ≠ ⊥ := by
      intro hb
      obtain ⟨a, ha, a', ha', hne'⟩ := hAn
      have h1 : a ∈ (⊥ : Subgroup _) := hb ▸ Subgroup.mem_sup_left ha
      have h2 : a' ∈ (⊥ : Subgroup _) := hb ▸ Subgroup.mem_sup_left ha'
      rw [Subgroup.mem_bot] at h1 h2
      exact hne' (by rw [h1, h2])
    have hO : ∀ {P Q : Subgroup (MulAut (IntMod V hV))}, P ∈ ({K₁, K₂} : Finset _) →
        Q ∈ ({K₁, K₂} : Finset _) → oTwoUpper P = ⊥ → oTwoUpper Q = ⊥ := by
      intro P Q hP hQ hPb
      obtain ⟨t, -, ht⟩ := htrans P hP Q hQ
      rw [← ht]
      exact oTwoUpper_conjAut_eq_bot hPb
    have hO₁ : oTwoUpper K₁ ≠ ⊥ := fun hb =>
      hAbot (le_bot_iff.mp (hNO.trans (by rw [hb, hO hK₁ hK₂ hb, sup_bot_eq])))
    have hO₂ : oTwoUpper K₂ ≠ ⊥ := fun hb =>
      hAbot (le_bot_iff.mp (hNO.trans (by rw [hb, hO hK₂ hK₁ hb, sup_bot_eq])))
    have hmem : ∀ K ∈ ({K₁, K₂} : Finset _), K = K₁ ∨ K = K₂ := fun K hK => by simpa using hK
    rcases eq_oTwoUpper_or_eq_oTwoUpper hc hi hO₁ hO₂ hAs hBs hAn hBn hAB
      (hOK K₁ hK₁) (hOK K₂ hK₂) hNO with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact Or.inr ⟨K₁, hK₁, K₂, hK₂, hmem, hne, hJK, e₁.symm, e₂.symm, hc, hi⟩
    · refine Or.inr ⟨K₂, hK₂, K₁, hK₁, fun K hK => (hmem K hK).symm, hne.symm,
        by rw [hJK, sup_comm], e₁.symm, e₂.symm, fun a ha b hb => (hc b hb a ha).symm, ?_⟩
      rw [inf_comm]; exact hi

end CFSG.Quasithin.Vol2.Ch10.SecE
