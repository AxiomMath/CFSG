module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier

theorem mem_centralizer_GA_iff {t g : GA} :
    g ∈ Subgroup.centralizer ({t} : Set GA) ↔ (g : GL24) ∈ Subgroup.centralizer {(t : GL24)} := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [Subgroup.coe_mul, Subgroup.coe_mul] at this
  · intro h
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact h

theorem map_centralizer_GA (t : GA) :
    (Subgroup.centralizer ({t} : Set GA)).map GA.subtype =
      GA ⊓ Subgroup.centralizer {(t : GL24)} := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Subgroup.mem_inf.2 ⟨g.2, mem_centralizer_GA_iff.1 hg⟩
  · intro hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
    exact ⟨⟨g, hgA⟩, mem_centralizer_GA_iff.2 hgC, rfl⟩

theorem card_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({e x} : Set H)) := by
  have h : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have := congrArg e hy
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · intro hy
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy
  rw [← h, Subgroup.card_map_of_injective e.injective]

theorem card_centralizer_GA (t : GA) :
    Nat.card (Subgroup.centralizer ({t} : Set GA)) =
      Nat.card (GA ⊓ Subgroup.centralizer {(t : GL24)} : Subgroup GL24) := by
  rw [← map_centralizer_GA, Subgroup.card_map_of_injective GA.subtype_injective]

theorem selfCentralizing_of_GL {t : GA} {Q : Subgroup GL24} {n : ℕ}
    (hQC : Q ≤ GA ⊓ Subgroup.centralizer {(t : GL24)})
    (hnorm : ∀ g ∈ GA ⊓ Subgroup.centralizer {(t : GL24)}, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hcen : ∀ g ∈ GA ⊓ Subgroup.centralizer {(t : GL24)}, (∀ q ∈ Q, g * q = q * g) → g ∈ Q)
    (hcard : Nat.card Q = 2 ^ n) :
    ∃ Q' : Subgroup (Subgroup.centralizer ({t} : Set GA)), Q'.Normal ∧ Nat.card Q' = 2 ^ n ∧
      Subgroup.centralizer (Q' : Set (Subgroup.centralizer ({t} : Set GA))) ≤ Q' ∧
      ∀ B : Subgroup (Subgroup.centralizer ({t} : Set GA)), ¬ CFSG.IsComponent B := by
  set C := Subgroup.centralizer ({t} : Set GA)
  set f : C →* GL24 := GA.subtype.comp C.subtype
  have hf : Function.Injective f := GA.subtype_injective.comp C.subtype_injective
  have hfmem : ∀ c : C, f c ∈ GA ⊓ Subgroup.centralizer {(t : GL24)} := fun c =>
    Subgroup.mem_inf.2 ⟨(c : GA).2, mem_centralizer_GA_iff.1 c.2⟩
  have hsurj : ∀ q ∈ Q, ∃ c : C, f c = q := by
    intro q hq
    obtain ⟨hqA, hqC⟩ := Subgroup.mem_inf.1 (hQC hq)
    exact ⟨⟨⟨q, hqA⟩, mem_centralizer_GA_iff.2 hqC⟩, rfl⟩
  refine ⟨Q.comap f, ⟨fun q hq c => ?_⟩, ?_, ?_, ?_⟩
  · show f (c * q * c⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hfmem c) _ hq
  · have hmap : (Q.comap f).map f = Q := by
      rw [Subgroup.map_comap_eq]
      refine inf_eq_right.2 fun q hq => ?_
      obtain ⟨c, rfl⟩ := hsurj q hq
      exact ⟨c, rfl⟩
    calc Nat.card (Q.comap f) = Nat.card ((Q.comap f).map f) :=
          (Subgroup.card_map_of_injective hf).symm
      _ = 2 ^ n := by rw [hmap, hcard]
  · intro c hc
    show f c ∈ Q
    refine hcen _ (hfmem c) fun q hq => ?_
    obtain ⟨d, rfl⟩ := hsurj q hq
    have := Subgroup.mem_centralizer_iff.1 hc d hq
    rw [← map_mul, ← map_mul, this]
  · intro B
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hlift : ∀ q ∈ Q, ∃ g : GA, (g : GL24) = q := fun q hq =>
      ⟨⟨q, (Subgroup.mem_inf.1 (hQC hq)).1⟩, rfl⟩
    have hcardQ : Nat.card (Q.comap GA.subtype) = 2 ^ n := by
      have hmap : (Q.comap GA.subtype).map GA.subtype = Q := by
        rw [Subgroup.map_comap_eq]
        refine inf_eq_right.2 fun q hq => ?_
        obtain ⟨g, rfl⟩ := hlift q hq
        exact ⟨g, rfl⟩
      calc Nat.card (Q.comap GA.subtype) = Nat.card ((Q.comap GA.subtype).map GA.subtype) :=
            (Subgroup.card_map_of_injective GA.subtype_injective).symm
        _ = 2 ^ n := by rw [hmap, hcard]
    refine CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_le (C := C)
      (Q := Q.comap GA.subtype) (fun g hg => ?_) (IsPGroup.of_card hcardQ)
      (fun c hc q hq => ?_) (fun c hc hcq => ?_) B
    · exact mem_centralizer_GA_iff.2 (Subgroup.mem_inf.1 (hQC hg)).2
    · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hnorm _ (Subgroup.mem_inf.2 ⟨c.2, mem_centralizer_GA_iff.1 hc⟩) _ hq
    · rw [Subgroup.mem_comap]
      refine hcen _ (Subgroup.mem_inf.2 ⟨c.2, mem_centralizer_GA_iff.1 hc⟩) fun q hq => ?_
      obtain ⟨g, rfl⟩ := hlift q hq
      have := congrArg GA.subtype (hcq g hq)
      rwa [map_mul, map_mul] at this

end CFSG.Sporadic.Co1Block
