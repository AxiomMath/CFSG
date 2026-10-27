module

public import CFSG.Quasithin.EmptyFaithful.SzN32Step
public import CFSG.Quasithin.EmptyFaithful.SzN32Base

public section

namespace CFSG.Quasithin.SzN32

private theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (L : Subgroup H) :
    Nat.card (L.comap f) = Nat.card f.ker * Nat.card L := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (f.subgroupComap_surjective L hf)
  have hle : f.ker ≤ L.comap f := fun x hx => by
    simp [MonoidHom.mem_ker.1 hx]
  have h2 : Nat.card (f.subgroupComap L).ker = Nat.card f.ker := by
    have : (f.subgroupComap L).ker = f.ker.subgroupOf (L.comap f) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subtype.ext_iff]
      rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← h1, h2]

private theorem cm_eq_one_of_mul_comm {G : Type*} [Group G] {x y : G} (h : x * y = y * x) :
    cm x y = 1 := by
  have : x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by simp only [mul_assoc]
  rw [cm, this, h]
  simp [mul_assoc]

private theorem isE27_map_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup G} (hE : IsE27 E) : IsE27 (E.map f) := by
  obtain ⟨h1, h2, h3⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf]
    exact h1
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h2 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h3 x hx y hy]

private theorem theoremA_aux {S : Type} [Group S] {a σ : S} (hT : TData a σ) (n : ℕ) :
    ∀ (G : Type) [Group G] [Finite G], IsPGroup 3 G → ∀ π : G →* S, Function.Surjective π →
      π.ker ≤ frattini G → Nat.card π.ker = n → n ≠ 1 →
      ∃ E : Subgroup G, E.Normal ∧ E ≤ frattini G ∧ IsE27 E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hG π hπ hker hn hn1
    by_cases h3 : n = 3
    · exact base hT hG π hπ hker (hn.trans h3)
    · have hK : π.ker ≠ ⊥ := fun h => hn1 (by rw [← hn, h, Subgroup.card_bot])
      obtain ⟨Z, hZK, hZc, hZ3⟩ := exists_central_card_three hG hK
      have hZn : Z.Normal := Subgroup.normal_of_le_center hZc
      have hZfr : Z ≤ frattini G := hZK.trans hker
      obtain ⟨π1, hπ1⟩ : ∃ π1 : G ⧸ Z →* S, π1.comp (QuotientGroup.mk' Z) = π :=
        ⟨QuotientGroup.lift Z π hZK, QuotientGroup.lift_comp_mk' Z π hZK⟩
      have hπ1s : Function.Surjective π1 := by
        have h : Function.Surjective (π1 ∘ QuotientGroup.mk' Z) := by
          rw [← MonoidHom.coe_comp, hπ1]
          exact hπ
        exact h.of_comp
      have hm : Nat.card π.ker = 3 * Nat.card π1.ker := by
        have hk : π.ker = π1.ker.comap (QuotientGroup.mk' Z) := by
          rw [← hπ1, MonoidHom.comap_ker]
        rw [hk, card_comap_of_surjective _ (QuotientGroup.mk'_surjective Z), QuotientGroup.ker_mk',
          hZ3]
      have hpos : 0 < Nat.card π1.ker := Nat.card_pos
      have hker1 : π1.ker ≤ frattini (G ⧸ Z) := by
        intro y hy
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
        have hg : g ∈ π.ker := by
          rw [← hπ1]
          simpa using hy
        exact frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective Z) (hker hg)
      obtain ⟨Eb, hEn, hEfr, hE27⟩ := ih (Nat.card π1.ker) (by omega) (G ⧸ Z) (hG.to_quotient Z)
        π1 hπ1s hker1 rfl (by omega)
      let H : Subgroup G := Eb.comap (QuotientGroup.mk' Z)
      have : H.Normal := hEn.comap _
      have hZH : Z ≤ H := fun z hz => by
        show QuotientGroup.mk' Z z ∈ Eb
        rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]
        exact Eb.one_mem
      have h81 : Nat.card H = 81 := by
        rw [card_comap_of_surjective _ (QuotientGroup.mk'_surjective Z), QuotientGroup.ker_mk',
          hZ3, hE27.1]
      have hHfr : H ≤ frattini G :=
        (Subgroup.comap_mono hEfr).trans (comap_frattini_quotient_le Z hZfr)
      have hcube : ∀ x ∈ H, x ^ 3 ∈ Z := fun x hx => by
        have h1 : (QuotientGroup.mk' Z x) ^ 3 = 1 := hE27.2.1 _ hx
        rw [← map_pow, QuotientGroup.mk'_apply] at h1
        exact (QuotientGroup.eq_one_iff _).1 h1
      have hcomm : ∀ x ∈ H, ∀ y ∈ H, cm x y ∈ Z := fun x hx y hy => by
        have h1 := cm_eq_one_of_mul_comm (hE27.2.2 _ hx _ hy)
        rw [← map_cm, QuotientGroup.mk'_apply] at h1
        exact (QuotientGroup.eq_one_iff _).1 h1
      obtain ⟨E, hEn', hEH, hE⟩ := step hG Z H hZ3 hZc hZH hHfr h81 hcube hcomm
      exact ⟨E, hEn', hEH.trans hHfr, hE⟩

theorem theoremA_ne {S : Type} [Group S] {a σ : S} (hT : TData a σ) (G : Type) [Group G] [Finite G]
    (hG : IsPGroup 3 G) (π : G →* S) (hπ : Function.Surjective π) (hker : π.ker ≤ frattini G)
    (hne : π.ker ≠ ⊥) : ∃ E : Subgroup G, E.Normal ∧ E ≤ frattini G ∧ IsE27 E :=
  theoremA_aux hT (Nat.card π.ker) G hG π hπ hker rfl fun h => hne (Subgroup.card_eq_one.1 h)

private theorem exists_frattini_cover {T Γ : Type*} [Group T] [Finite T] [Group Γ] (ψ : T →* Γ)
    (X : Subgroup Γ) (hX : X ≤ ψ.range) :
    ∃ H : Subgroup T, X ≤ H.map ψ ∧ (ψ.comp H.subtype).ker ≤ frattini H := by
  have hne : {H : Subgroup T | X ≤ H.map ψ}.Nonempty :=
    ⟨⊤, show X ≤ (⊤ : Subgroup T).map ψ by rwa [← MonoidHom.range_eq_map]⟩
  obtain ⟨H, hH, hmin⟩ := (wellFounded_lt (α := Subgroup T)).has_min _ hne
  refine ⟨H, hH, ?_⟩
  simp only [frattini, Order.radical, le_iInf_iff, Set.mem_ofPred_eq]
  intro M hM
  by_contra hnot
  set K := (ψ.comp H.subtype).ker
  have hlt : M < M ⊔ K := lt_of_le_of_ne le_sup_left fun h =>
    hnot (le_sup_right.trans h.symm.le)
  have hsup : M ⊔ K = ⊤ := hM.2 _ hlt
  have hKmap : K.map (ψ.comp H.subtype) = ⊥ := (Subgroup.map_eq_bot_iff _).2 le_rfl
  have hMmap : M.map (ψ.comp H.subtype) = H.map ψ := by
    have h1 := congrArg (Subgroup.map (ψ.comp H.subtype)) hsup
    rw [Subgroup.map_sup, hKmap, sup_bot_eq, ← MonoidHom.range_eq_map,
      MonoidHom.range_comp, Subgroup.range_subtype] at h1
    exact h1
  have hgood : X ≤ (M.map H.subtype).map ψ := by
    rw [Subgroup.map_map, hMmap]
    exact hH
  refine hmin _ hgood ⟨Subgroup.map_subtype_le M, fun hle => ?_⟩
  have hM1 : M = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : H.subtype x ∈ M.map H.subtype := hle x.2
    rwa [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective M]
  exact hM.1 hM1

theorem no_E27_cover {S : Type} [Group S] {a σ : S} (hT : TData a σ) (Q : Type) [Group Q]
    [Finite Q] (hQ : IsPGroup 3 Q) (π : Q →* S) (hπ : Function.Surjective π) :
    ∃ E : Subgroup Q, IsE27 E := by
  obtain ⟨H, hH, hker⟩ := exists_frattini_cover π ⊤ (MonoidHom.range_eq_top.2 hπ).ge
  have hG : IsPGroup 3 H := hQ.to_subgroup H
  have hπ' : Function.Surjective (π.comp H.subtype) := fun s => by
    obtain ⟨h, hh, rfl⟩ := hH (Subgroup.mem_top s)
    exact ⟨⟨h, hh⟩, rfl⟩
  suffices ∃ E : Subgroup H, IsE27 E by
    obtain ⟨E, hE⟩ := this
    exact ⟨E.map H.subtype, isE27_map_of_injective H.subtype H.subtype_injective hE⟩
  by_cases hbot : (π.comp H.subtype).ker = ⊥
  · have hinj : Function.Injective (π.comp H.subtype) := (MonoidHom.ker_eq_bot_iff _).1 hbot
    obtain ⟨D, hD⟩ := hT.e27
    exact ⟨D.map (MulEquiv.ofBijective (π.comp H.subtype) ⟨hinj, hπ'⟩).symm.toMonoidHom,
      hD.map_mulEquiv _⟩
  · obtain ⟨E, -, -, hE⟩ := theoremA_ne hT H hG (π.comp H.subtype) hπ' hker hbot
    exact ⟨E, hE⟩

end CFSG.Quasithin.SzN32
