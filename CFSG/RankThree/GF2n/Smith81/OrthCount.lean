module

public import CFSG.RankThree.GF2n.Tim79Heis

public section

namespace CFSG.RankThree.GF2n.Smith81

section Counting

private theorem qm_pi_one {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) : M₀.π 1 = 0 := by
  have h := M₀.π_mul 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

private theorem qm_pi_inv {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {x : G} (hx : x ∈ Q) :
    M₀.π x⁻¹ = -M₀.π x := by
  have h := M₀.π_mul x hx x⁻¹ (Q.inv_mem hx)
  rw [mul_inv_cancel, qm_pi_one M₀] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem exists_preimage_subgroup {G : Type} [Group G] [Finite G] {K : Type} [Field K]
    {Q Z : Subgroup G} {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) {S : Subgroup G}
    (hSQ : S ≤ Q) (hZS : Z ≤ S) (T : Set M₀.E) (h0 : (0 : M₀.E) ∈ T)
    (hadd : ∀ a ∈ T, ∀ b ∈ T, a + b ∈ T) (hneg : ∀ a ∈ T, -a ∈ T)
    (hsurj : ∀ t ∈ T, ∃ v ∈ S, M₀.π v = t) :
    ∃ S' : Subgroup G, (∀ v : G, v ∈ S' ↔ v ∈ S ∧ M₀.π v ∈ T) ∧
      Nat.card S' = Nat.card Z * Nat.card T := by
  obtain ⟨S', hS'⟩ : ∃ S' : Subgroup G, ∀ v : G, v ∈ S' ↔ v ∈ S ∧ M₀.π v ∈ T :=
    ⟨{ carrier := {v | v ∈ S ∧ M₀.π v ∈ T}
       mul_mem' := fun {x y} hx hy => ⟨S.mul_mem hx.1 hy.1, by
         rw [M₀.π_mul x (hSQ hx.1) y (hSQ hy.1)]
         exact hadd _ hx.2 _ hy.2⟩
       one_mem' := ⟨S.one_mem, by
         rw [qm_pi_one M₀]
         exact h0⟩
       inv_mem' := fun {x} hx => ⟨S.inv_mem hx.1, by
         rw [qm_pi_inv M₀ (hSQ hx.1)]
         exact hneg _ hx.2⟩ }, fun v => Iff.rfl⟩
  have hQ : ∀ v : S', (v : G) ∈ Q := fun v => hSQ ((hS' (v : G)).1 v.2).1
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥S' →* Multiplicative M₀.E,
      ∀ v : S', φ v = Multiplicative.ofAdd (M₀.π (v : G)) :=
    ⟨{ toFun := fun v => Multiplicative.ofAdd (M₀.π (v : G))
       map_one' := by
         show Multiplicative.ofAdd (M₀.π ((1 : S') : G)) = 1
         rw [Subgroup.coe_one, qm_pi_one M₀, ofAdd_zero]
       map_mul' := fun x y => by
         show Multiplicative.ofAdd (M₀.π ((x * y : S') : G)) =
           Multiplicative.ofAdd (M₀.π (x : G)) * Multiplicative.ofAdd (M₀.π (y : G))
         rw [Subgroup.coe_mul, M₀.π_mul _ (hQ x) _ (hQ y), ofAdd_add] }, fun v => rfl⟩
  have hZS' : ∀ z ∈ Z, z ∈ S' := fun z hz => by
    refine (hS' z).2 ⟨hZS hz, ?_⟩
    rw [(M₀.π_ker z (hSQ (hZS hz))).2 hz]
    exact h0
  have hker : ∀ v : S', φ v = 1 ↔ (v : G) ∈ Z := fun v => by
    rw [hφ, ofAdd_eq_one]
    exact M₀.π_ker _ (hQ v)
  have hkerCard : Nat.card φ.ker = Nat.card Z :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), (hker x.1).1 (MonoidHom.mem_ker.1 x.2)⟩
        invFun := fun z => ⟨⟨(z : G), hZS' (z : G) z.2⟩,
          MonoidHom.mem_ker.2 ((hker ⟨(z : G), hZS' (z : G) z.2⟩).2 z.2)⟩
        left_inv := fun x => rfl
        right_inv := fun z => rfl }
  have hyT : ∀ y : φ.range, Multiplicative.toAdd (y : Multiplicative M₀.E) ∈ T := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    show Multiplicative.toAdd (φ x) ∈ T
    rw [hφ, toAdd_ofAdd]
    exact ((hS' (x : G)).1 x.2).2
  have hrangeCard : Nat.card φ.range = Nat.card T := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y : φ.range => (⟨Multiplicative.toAdd (y : Multiplicative M₀.E), hyT y⟩ : ↥T))
      ⟨?_, ?_⟩)
    · intro y₁ y₂ h
      have h' : Multiplicative.toAdd (y₁ : Multiplicative M₀.E) =
          Multiplicative.toAdd (y₂ : Multiplicative M₀.E) := by
        have h2 := congrArg Subtype.val h
        exact h2
      exact Subtype.ext (Multiplicative.toAdd.injective h')
    · rintro ⟨t, ht⟩
      obtain ⟨v, hv, hπv⟩ := hsurj t ht
      have hvS' : v ∈ S' := (hS' v).2 ⟨hv, by rw [hπv]; exact ht⟩
      refine ⟨⟨φ ⟨v, hvS'⟩, MonoidHom.mem_range.2 ⟨⟨v, hvS'⟩, rfl⟩⟩, Subtype.ext ?_⟩
      show Multiplicative.toAdd (φ ⟨v, hvS'⟩) = t
      rw [hφ, toAdd_ofAdd]
      exact hπv
  refine ⟨S', hS', ?_⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hkerCard, hrangeCard] at h1
  exact h1.symm

theorem card_pairLine {K : Type} [Field K] [Finite K] {ι : Type} (u : ι → K) (hu : u ≠ 0) :
    Nat.card ↥{p : (ι → K) × (ι → K) | ∃ s t : K, p = (s • u, t • u)} = Nat.card K ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  have hi0 : u i ≠ 0 := hi
  let g : K × K → ↥{p : (ι → K) × (ι → K) | ∃ s t : K, p = (s • u, t • u)} :=
    fun st => ⟨(st.1 • u, st.2 • u), st.1, st.2, rfl⟩
  have hg : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · rintro ⟨s, t⟩ ⟨s', t'⟩ h
      have h' : (s • u, t • u) = (s' • u, t' • u) := congrArg Subtype.val h
      have hs : s * u i = s' * u i := congrFun (congrArg Prod.fst h') i
      have ht : t * u i = t' * u i := congrFun (congrArg Prod.snd h') i
      rw [mul_right_cancel₀ hi0 hs, mul_right_cancel₀ hi0 ht]
    · rintro ⟨p, s, t, hp⟩
      exact ⟨(s, t), Subtype.ext hp.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_prod, sq]
end Counting

end CFSG.RankThree.GF2n.Smith81
