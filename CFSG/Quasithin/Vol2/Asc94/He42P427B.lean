module

public import CFSG.Quasithin.Vol2.Asc94.He42P427A3

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem p427_cover_gen (X Z B K Lx : Subgroup G) (hZX : Z ≤ X) (hBZ : B ≤ Z)
    (hX : Nat.card ↥X = 64) (hZ : Nat.card ↥Z = 16) (hB : Nat.card ↥B = 4)
    (hLX : Lx ≤ normalizer (X : Set G)) (hLB : ∀ l ∈ Lx, ∀ b ∈ B, l * b = b * l)
    (hKL : K ≤ Lx) (hidx : K.relIndex Lx = 5)
    (hsp : ∀ g ∈ Lx, g ∉ K → ∀ z ∈ Z, g * z * g⁻¹ ∈ Z → z ∈ B) :
    ∀ c ∈ X, c ∉ B → ∃ h ∈ Lx, h⁻¹ * c * h ∈ Z := by
  classical
  have hι : Nat.card (↥Lx ⧸ K.subgroupOf Lx) = 5 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  obtain ⟨rep, hrep⟩ : ∃ rep : (↥Lx ⧸ K.subgroupOf Lx) → ↥Lx,
      ∀ i, (QuotientGroup.mk (rep i) : ↥Lx ⧸ K.subgroupOf Lx) = i :=
    ⟨fun i => Quotient.out i, fun i => Quotient.out_eq i⟩
  have hfixB : ∀ l ∈ Lx, ∀ x ∈ B, l⁻¹ * x * l = x := by
    intro l hl x hx
    have hl' : l⁻¹ ∈ Lx := Lx.inv_mem hl
    have hc := hLB l⁻¹ hl' x hx
    calc l⁻¹ * x * l = x * l⁻¹ * l := by rw [← hc]
      _ = x := by group
  let D := (↥Lx ⧸ K.subgroupOf Lx) × ↥((Z : Set G) \ (B : Set G))
  let T' := ↥((X : Set G) \ (B : Set G))
  have hΦ : ∀ p : D, (rep p.1 : G) * (p.2 : G) * (rep p.1 : G)⁻¹ ∈ (X : Set G) \ (B : Set G) := by
    rintro ⟨i, w, hw⟩
    obtain ⟨hwZ, hwB⟩ := hw
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hLX (rep i).2) w).1 (hZX hwZ)
    · intro hxB
      apply hwB
      have h1 := hfixB (rep i : G) (rep i).2 _ hxB
      have h2 : (w : G) = (rep i : G)⁻¹ * ((rep i : G) * (w : G) * (rep i : G)⁻¹) * (rep i : G) := by
        group
      rw [h2, h1]
      exact hxB
  let Ψ : D → T' := fun p => ⟨(rep p.1 : G) * (p.2 : G) * (rep p.1 : G)⁻¹, hΦ p⟩
  have hinj : Function.Injective Ψ := by
    rintro ⟨i, w, hw⟩ ⟨j, w', hw'⟩ h
    have hxeq : (rep i : G) * (w : G) * (rep i : G)⁻¹ = (rep j : G) * (w' : G) * (rep j : G)⁻¹ :=
      congrArg Subtype.val h
    have hxB : (rep i : G) * (w : G) * (rep i : G)⁻¹ ∉ (B : Set G) := (hΦ ⟨i, w, hw⟩).2
    set g : G := (rep j : G)⁻¹ * (rep i : G) with hgdef
    have hgL : g ∈ Lx := Lx.mul_mem (Lx.inv_mem (rep j).2) (rep i).2
    have hgK : g ∈ K := by
      by_contra hgK
      have hz : g * (w : G) * g⁻¹ ∈ Z := by
        have e : g * (w : G) * g⁻¹ = (w' : G) := by
          calc g * (w : G) * g⁻¹ = (rep j : G)⁻¹ * ((rep i : G) * (w : G) * (rep i : G)⁻¹) * (rep j : G) := by
                rw [hgdef]; group
            _ = (rep j : G)⁻¹ * ((rep j : G) * (w' : G) * (rep j : G)⁻¹) * (rep j : G) := by rw [hxeq]
            _ = (w' : G) := by group
        rw [e]
        exact hw'.1
      exact hw.2 (hsp g hgL hgK w hw.1 hz)
    have hij : i = j := by
      have hmk : (QuotientGroup.mk (rep i) : ↥Lx ⧸ K.subgroupOf Lx) = QuotientGroup.mk (rep j) := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have e : ((rep i : G))⁻¹ * (rep j : G) = g⁻¹ := by rw [hgdef]; group
        show (((rep i : Lx) : G))⁻¹ * ((rep j : Lx) : G) ∈ K
        rw [e]
        exact K.inv_mem hgK
      calc i = QuotientGroup.mk (rep i) := (hrep i).symm
        _ = QuotientGroup.mk (rep j) := hmk
        _ = j := hrep j
    subst hij
    have hw2 : (w : G) = (w' : G) := by
      have h3 := congrArg (fun y => (rep i : G)⁻¹ * y * (rep i : G)) hxeq
      simpa using h3
    exact Prod.ext rfl (Subtype.ext hw2)
  have hZdiff : Nat.card ↥((Z : Set G) \ (B : Set G)) = 12 := by
    have h := Set.ncard_sdiff_add_ncard_of_subset (show (B : Set G) ⊆ (Z : Set G) from hBZ)
    have hB' : (B : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hB
    have hZ' : (Z : Set G).ncard = 16 := by rw [← Nat.card_coe_set_eq]; exact hZ
    rw [Nat.card_coe_set_eq]
    omega
  have hXdiff : Nat.card T' = 60 := by
    have h := Set.ncard_sdiff_add_ncard_of_subset
      (show (B : Set G) ⊆ (X : Set G) from fun y hy => hZX (hBZ hy))
    have hB' : (B : Set G).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hB
    have hX' : (X : Set G).ncard = 64 := by rw [← Nat.card_coe_set_eq]; exact hX
    show Nat.card ↥((X : Set G) \ (B : Set G)) = 60
    rw [Nat.card_coe_set_eq]
    omega
  have hDcard : Nat.card D = 60 := by
    rw [Nat.card_prod, hι, hZdiff]
  have hbij : Function.Bijective Ψ :=
    hinj.bijective_of_nat_card_le (le_of_eq (by rw [hXdiff, hDcard]))
  intro c hcX hcB
  obtain ⟨p, hp⟩ := hbij.2 ⟨c, ⟨hcX, hcB⟩⟩
  refine ⟨(rep p.1 : G), (rep p.1).2, ?_⟩
  have hc : (rep p.1 : G) * (p.2 : G) * (rep p.1 : G)⁻¹ = c := congrArg Subtype.val hp
  have e : (rep p.1 : G)⁻¹ * c * (rep p.1 : G) = (p.2 : G) := by
    rw [← hc]
    group
  rw [e]
  exact p.2.2.1


end CFSG.Quasithin.A94.He42
