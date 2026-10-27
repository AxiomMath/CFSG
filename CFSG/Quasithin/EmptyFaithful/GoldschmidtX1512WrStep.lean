module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Ext
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Shape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace X1512

variable {G : Type} [Group G] {n : ℕ}

theorem NatMod.relIndex_eq (hn : n = 3 ∨ n = 5) {K L X : Subgroup G} [(L.subgroupOf X).Normal]
    {Ψ : ↥K →* Equiv.Perm (Fin n)} {β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X}
    (hM : NatMod n K L X Ψ β) : L.relIndex X = 2 ^ (n - 1) := by
  let e : ↥(G6.coreMod n) ≃* (↥X ⧸ L.subgroupOf X) := MulEquiv.ofBijective β ⟨hM.inj, hM.surj⟩
  show Nat.card (↥X ⧸ L.subgroupOf X) = _
  rw [← Nat.card_congr e.toEquiv, card_coreMod hn]

theorem NatMod.card_eq (hn : n = 3 ∨ n = 5) {K L X : Subgroup G} [(L.subgroupOf X).Normal]
    {Ψ : ↥K →* Equiv.Perm (Fin n)} {β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X}
    (hM : NatMod n K L X Ψ β) (hLX : L ≤ X) : Nat.card X = 2 ^ (n - 1) * Nat.card L := by
  have h := Subgroup.relIndex_mul_card (H := L) (K := X)
  rw [inf_eq_left.mpr hLX, hM.relIndex_eq hn] at h
  exact h.symm

theorem NatMod.ne (hn : n = 3 ∨ n = 5) {K L X : Subgroup G} [(L.subgroupOf X).Normal]
    {Ψ : ↥K →* Equiv.Perm (Fin n)} {β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X}
    (hM : NatMod n K L X Ψ β) : L ≠ X := by
  intro h
  have h1 := hM.relIndex_eq hn
  rw [h, Subgroup.relIndex_self] at h1
  rcases hn with rfl | rfl <;> norm_num at h1

theorem NatMod.mem_of_mem {K L X : Subgroup G} [(L.subgroupOf X).Normal]
    {Ψ : ↥K →* Equiv.Perm (Fin n)} {β : ↥(G6.coreMod n) →* ↥X ⧸ L.subgroupOf X}
    (hM : NatMod n K L X Ψ β) (k : ↥K) {x : G} (hx : x ∈ X) : (k : G) * x * (k : G)⁻¹ ∈ X := by
  obtain ⟨u, hu⟩ := hM.surj (QuotientGroup.mk ⟨x, hx⟩)
  exact (hM.equiv k u ⟨x, hx⟩ hu).1

theorem exists_nontrivial_action (hn : n = 3 ∨ n = 5) {F L X : Subgroup G}
    {θ : ↥F →* Equiv.Perm (Fin n)} (hθs : Function.Surjective θ)
    (hθk : θ.ker = (cSecIn F L X).subgroupOf F) :
    ∃ f ∈ F, ∃ x ∈ X, f * x * f⁻¹ * x⁻¹ ∉ L := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), σ ≠ 1 := by
    rcases hn with rfl | rfl
    · exact ⟨Equiv.swap 0 1, by decide⟩
    · exact ⟨Equiv.swap 0 1, by decide⟩
  obtain ⟨f, rfl⟩ := hθs σ
  refine ⟨f, f.2, ?_⟩
  by_contra hall
  push Not at hall
  apply hσ
  have hmem : (f : G) ∈ cSecIn F L X := Subgroup.subset_closure ⟨f.2, fun x hx => hall x hx⟩
  have : f ∈ θ.ker := by
    rw [hθk]
    exact Subgroup.mem_subgroupOf.mpr hmem
  exact this

theorem card_wreath (n : ℕ) :
    Nat.card (Equiv.Perm (Fin n) ≀ᵣ Multiplicative (ZMod 2)) = (n.factorial) ^ 2 * 2 := by
  rw [Nat.card_congr
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin n)) (Multiplicative (ZMod 2))),
    Nat.card_prod, Nat.card_fun, Nat.card_perm]
  simp [Nat.card_eq_fintype_card]

theorem relIndex_eq_two_of_wreath {H J C : Subgroup G} (hCH : C ≤ H) (hJH : J ≤ H)
    (hφ : QuotIsoWith H C J (Equiv.Perm (Fin n) ≀ᵣ Multiplicative (ZMod 2))
      (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))) : (J ⊔ C).relIndex H = 2 := by
  obtain ⟨φ, hφs, hφk, ⟨e⟩⟩ := hφ
  have hsup : (J ⊔ C).subgroupOf H = J.subgroupOf H ⊔ C.subgroupOf H :=
    Subgroup.subgroupOf_sup hJH hCH
  have hC0 : (C.subgroupOf H).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hφk]
  have hmap : ((J ⊔ C).subgroupOf H).map φ = (J.subgroupOf H).map φ := by
    rw [hsup, Subgroup.map_sup, hC0, sup_bot_eq]
  have hker : φ.ker ≤ (J ⊔ C).subgroupOf H := by
    rw [hφk]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr
      ((le_sup_right : C ≤ J ⊔ C) (Subgroup.mem_subgroupOf.mp hx))
  have hidx : ((J ⊔ C).subgroupOf H).index = (((J ⊔ C).subgroupOf H).map φ).index := by
    conv_lhs => rw [← Subgroup.comap_map_eq_self hker]
    exact Subgroup.index_comap_of_surjective _ hφs
  have h1 := Subgroup.card_mul_index (((J ⊔ C).subgroupOf H).map φ)
  rw [hmap, Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, card_wreath] at h1
  have hpos : 0 < (Nat.card (Fin n)).factorial ^ 2 := by positivity
  show ((J ⊔ C).subgroupOf H).index = 2
  rw [hidx, hmap]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 : (n.factorial) ^ 2 * (((J.subgroupOf H).map φ).index) = (n.factorial) ^ 2 * 2 := by
    rw [← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h2

theorem exists_wrStep (hn : n = 3 ∨ n = 5) {T Pm H U L N A : Subgroup G}
    [(L.subgroupOf N).Normal] (c : ShapeCtx T Pm H U L N A)
    (hφ : QuotIsoWith H (cSecIn H L N) (thompsonJ H)
      (Equiv.Perm (Fin n) ≀ᵣ Multiplicative (ZMod 2)) (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)))
    (hpair : NaturalSnPair n H L N) :
    ∃ (F₁ F₂ X₁ X₂ : Subgroup G) (_ : (L.subgroupOf X₁).Normal) (_ : (L.subgroupOf X₂).Normal),
      NaturalSn n F₁ L X₁ ∧ NaturalSn n F₂ L X₂ ∧ WrStep H U L N (F₁ ⊔ F₂) F₁ F₂ X₁ X₂ ∧
        F₁ ⊔ F₂ = thompsonJ H ⊔ cSecIn H L N := by
  obtain ⟨F₁, F₂, X₁, X₂, hn₁, hn₂, hF₁H, hF₂H, -, -, hLX₁, hX₁N, hLX₂, hX₂N, hX₁₂, hX₁₂N,
    hF₂X₁, hF₁X₂, hFF, hNat₁, hNat₂⟩ := hpair
  have := hn₁
  have := hn₂
  obtain ⟨θ₁, β₁, hθ₁s, hθ₁k, hM₁⟩ := natMod_of_naturalSn hn hNat₁
  obtain ⟨θ₂, β₂, hθ₂s, hθ₂k, hM₂⟩ := natMod_of_naturalSn hn hNat₂
  have hKH : F₁ ⊔ F₂ ≤ H := sup_le hF₁H hF₂H
  have hidx : (F₁ ⊔ F₂).relIndex H = 2 := by
    rw [hFF]
    exact relIndex_eq_two_of_wreath (S152Fin.cSecIn_le_left H L N) (S152Fin.thompsonJ_le_left H) hφ
  have hnorm : ((F₁ ⊔ F₂).subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hidx
  refine ⟨F₁, F₂, X₁, X₂, hn₁, hn₂, hNat₁, hNat₂, ?_, hFF⟩
  exact
    { elemAbelian := c.elem
      step := c.step
      FFK := rfl
      K_idx := hidx
      K_le := hKH
      F₁_le := hF₁H
      F₂_le := hF₂H
      L_le₁ := hLX₁
      X₁_le := hX₁N
      L_le₂ := hLX₂
      X₂_le := hX₂N
      inf_eq := hX₁₂
      sup_eq := hX₁₂N
      F₂_triv := hF₂X₁
      F₁_triv := hF₁X₂
      F₁_norm := fun f hf x hx => hM₁.mem_of_mem ⟨f, hf⟩ hx
      F₂_norm := fun f hf x hx => hM₂.mem_of_mem ⟨f, hf⟩ hx
      K_normal := fun σ hσ b hb =>
        hnorm.conj_mem ⟨b, hKH hb⟩ (Subgroup.mem_subgroupOf.mpr hb) ⟨σ, hσ⟩
      irr₁ := fun Y hLY hYX hY => hM₁.irreducible hn hθ₁s hLX₁ hLY hYX hY
      irr₂ := fun Y hLY hYX hY => hM₂.irreducible hn hθ₂s hLX₂ hLY hYX hY
      card_eq := by rw [hM₁.card_eq hn hLX₁, hM₂.card_eq hn hLX₂]
      L_ne₁ := hM₁.ne hn
      L_ne₂ := hM₂.ne hn
      nontriv₁ := exists_nontrivial_action hn hθ₁s hθ₁k
      nontriv₂ := exists_nontrivial_action hn hθ₂s hθ₂k }

end X1512

end CFSG.Quasithin
