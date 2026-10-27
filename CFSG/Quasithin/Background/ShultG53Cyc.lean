module

public import CFSG.Quasithin.Background.ShultG53Quot
public import CFSG.Quasithin.Background.ShultG53Lattice

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51

theorem card_eq_mul_of_quot {A M : Type} [AddCommGroup A] [AddCommGroup M] {N K : AddSubgroup A}
    (hKN : K ≤ N) (ψ : ↥N →+ M) (hs : Function.Surjective ψ)
    (hk : ∀ n : ↥N, ψ n = 0 ↔ (n : A) ∈ K) : Nat.card N = Nat.card K * Nat.card M := by
  have h1 := AddSubgroup.card_ker_mul_card_of_surjective hs
  have h2 : Nat.card ψ.ker = Nat.card K := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1.1, (hk x.1).mp (AddMonoidHom.mem_ker.mp x.2)⟩
        invFun := fun y => ⟨⟨y.1, hKN y.2⟩, AddMonoidHom.mem_ker.mpr ((hk _).mpr y.2)⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
  rw [← h1, h2]

@[expose] def permRep {X : Type} [Group X] (V : Md X) :
    Representation (ZMod 2) X (V.carrier → ZMod 2) where
  toFun g :=
    { toFun := permAct V g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext u w
    show u (V.ρ (1 : X)⁻¹ w) = u w
    simp
  map_mul' := by
    intro g h
    ext u w
    show u (V.ρ (g * h)⁻¹ w) = u (V.ρ h⁻¹ (V.ρ g⁻¹ w))
    rw [mul_inv_rev, map_mul]
    rfl

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
  (ρ : Representation (ZMod 2) ↥(alternatingGroup (Fin 6)) A)

theorem hom_eq_of_cyclic {M : Type} [AddCommGroup M]
    (τ : ↥(alternatingGroup (Fin 6)) → M → M) {N : AddSubgroup A}
    (hN : InvSub (fun g a => ρ g a) N) {u : A} (hu : u ∈ N)
    (hgen : ∀ n ∈ N, n ∈ AddSubgroup.closure (Set.range fun g => ρ g u))
    (ψ ψ' : ↥N →+ M)
    (hψ : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥N), ψ ⟨ρ g n, hN g n n.2⟩ = τ g (ψ n))
    (hψ' : ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥N), ψ' ⟨ρ g n, hN g n n.2⟩ = τ g (ψ' n))
    (h : ψ ⟨u, hu⟩ = ψ' ⟨u, hu⟩) : ψ = ψ' := by
  have hsub : AddSubgroup.closure (Set.range fun g => ρ g u) ≤ N := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact hN g u hu
  ext ⟨n, hn⟩
  have key : ∀ a ∈ AddSubgroup.closure (Set.range fun g => ρ g u),
      ∃ ha : a ∈ N, ψ ⟨a, ha⟩ = ψ' ⟨a, ha⟩ := by
    intro a ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      refine ⟨hN g u hu, ?_⟩
      have h1 := hψ g ⟨u, hu⟩
      have h2 := hψ' g ⟨u, hu⟩
      exact h1.trans ((congrArg (τ g) h).trans h2.symm)
    | zero =>
      refine ⟨N.zero_mem, ?_⟩
      have : (⟨0, N.zero_mem⟩ : ↥N) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      obtain ⟨hxN, hx'⟩ := ihx
      obtain ⟨hyN, hy'⟩ := ihy
      refine ⟨N.add_mem hxN hyN, ?_⟩
      have : (⟨x + y, N.add_mem hxN hyN⟩ : ↥N) = ⟨x, hxN⟩ + ⟨y, hyN⟩ := rfl
      rw [this, map_add, map_add, hx', hy']
    | neg x hx ihx =>
      obtain ⟨hxN, hx'⟩ := ihx
      refine ⟨N.neg_mem hxN, ?_⟩
      have : (⟨-x, N.neg_mem hxN⟩ : ↥N) = -⟨x, hxN⟩ := rfl
      rw [this, map_neg, map_neg, hx']
  obtain ⟨_, h1⟩ := key n (hgen n hn)
  exact h1

theorem isTop_of_cyclic [Finite A]
    {N N' : AddSubgroup A} (hN : InvSub (fun g a => ρ g a) N)
    (hN' : InvSub (fun g a => ρ g a) N') (hlt : N' < N)
    (i₀ : Fin 4) (m₀ : D i₀) (hcard : Nat.card N = Nat.card N' * Nat.card (D i₀))
    {u : A} (hu : u ∈ N)
    (hgen : ∀ n ∈ N, n ∈ AddSubgroup.closure (Set.range fun g => ρ g u))
    (H : Set ↥(alternatingGroup (Fin 6))) (hH : ∀ h ∈ H, ρ h u = u)
    (hsmall : Nat.card N < 2 ^ 16)
    (hfixA : ∀ m : D i₀, m ≠ 0 → (∀ h ∈ H, a6BinaryRep i₀ h m = m) → m = m₀)
    (hfixB : ∀ i : Fin 4, i ≠ 3 → i ≠ i₀ → i ≠ 0 → ∀ m : D i, m ≠ 0 →
      ¬ ∀ h ∈ H, a6BinaryRep i h m = m)
    (hno0 : i₀ ≠ 0 → ∀ ψ : ↥N →+ D 0, Function.Surjective ψ →
      ¬ ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥N),
        ψ ⟨ρ g n, hN g n n.2⟩ = a6BinaryRep 0 g (ψ n)) :
    IsTop (fun g a => ρ g a) N N' := by
  have key : ∀ K, IsMaxInvSub (fun g a => ρ g a) N K →
      ∃ ψ : ↥N →+ D i₀, Function.Surjective ψ ∧ (∀ n : ↥N, ψ n = 0 ↔ (n : A) ∈ K) ∧
        (∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥N),
          ψ ⟨ρ g n, hN g n n.2⟩ = a6BinaryRep i₀ g (ψ n)) ∧ ψ ⟨u, hu⟩ = m₀ := by
    intro K hK
    obtain ⟨i, ψ, hs, hk, he⟩ := exists_simple_quot ρ hN hK
    have hne3 : i ≠ 3 := by
      rintro rfl
      have h1 := Nat.card_le_card_of_surjective ψ hs
      have h2 : Nat.card (D 3) = 2 ^ 16 := (card_D 3).trans (by decide)
      omega
    have hψu : ψ ⟨u, hu⟩ ≠ 0 := by
      intro h0
      have hzero : ψ = 0 := by
        refine hom_eq_of_cyclic ρ (fun g m => a6BinaryRep i g m) hN hu hgen ψ 0 he
          (fun g n => ?_) ?_
        · simp
        · simpa using h0
      obtain ⟨hnt, -⟩ := a6_irred i
      obtain ⟨d, hd⟩ := exists_ne (0 : D i)
      obtain ⟨n, rfl⟩ := hs d
      exact hd (by rw [hzero]; rfl)
    have hfixed : ∀ h ∈ H, a6BinaryRep i h (ψ ⟨u, hu⟩) = ψ ⟨u, hu⟩ := by
      intro h hh
      rw [← he h ⟨u, hu⟩]
      congr 1
      exact Subtype.ext (hH h hh)
    by_cases hi : i = i₀
    · subst hi
      exact ⟨ψ, hs, hk, he, hfixA _ hψu hfixed⟩
    · exfalso
      by_cases hi0 : i = 0
      · subst hi0
        exact hno0 (Ne.symm hi) ψ hs he
      · exact hfixB i hne3 hi hi0 _ hψu hfixed
  have huniq : ∀ K₁ K₂, IsMaxInvSub (fun g a => ρ g a) N K₁ →
      IsMaxInvSub (fun g a => ρ g a) N K₂ → K₁ = K₂ := by
    intro K₁ K₂ h₁ h₂
    obtain ⟨ψ₁, hs₁, hk₁, he₁, hu₁⟩ := key K₁ h₁
    obtain ⟨ψ₂, hs₂, hk₂, he₂, hu₂⟩ := key K₂ h₂
    have heq : ψ₁ = ψ₂ :=
      hom_eq_of_cyclic ρ (fun g m => a6BinaryRep i₀ g m) hN hu hgen ψ₁ ψ₂ he₁ he₂
        (hu₁.trans hu₂.symm)
    ext a
    constructor
    · intro ha
      have haN : a ∈ N := h₁.1.le ha
      exact (hk₂ ⟨a, haN⟩).mp (by rw [← heq]; exact (hk₁ ⟨a, haN⟩).mpr ha)
    · intro ha
      have haN : a ∈ N := h₂.1.le ha
      exact (hk₁ ⟨a, haN⟩).mp (by rw [heq]; exact (hk₂ ⟨a, haN⟩).mpr ha)
  obtain ⟨K, hKmax, hN'K⟩ := exists_isMaxInvSub_ge hN' hlt
  obtain ⟨ψ, hs, hk, he, hψu⟩ := key K hKmax
  have hcK : Nat.card N = Nat.card K * Nat.card (D i₀) :=
    card_eq_mul_of_quot hKmax.1.le ψ hs hk
  have hpos : 0 < Nat.card (D i₀) := Nat.card_pos
  have hKN' : Nat.card K = Nat.card N' := Nat.eq_of_mul_eq_mul_right hpos (hcK.symm.trans hcard)
  have hEq : N' = K := AddSubgroup.eq_of_le_of_card_ge hN'K hKN'.le
  refine ⟨hlt, hN', fun S hS hSN hne => ?_⟩
  obtain ⟨K'', hK''max, hSK''⟩ := exists_isMaxInvSub_ge hS (lt_of_le_of_ne hSN hne)
  have h3 := huniq K'' K hK''max hKmax
  rw [h3, ← hEq] at hSK''
  exact hSK''

end CFSG.Quasithin.ShultG53
