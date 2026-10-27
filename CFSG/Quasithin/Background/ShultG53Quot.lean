module

public import CFSG.Quasithin.Background.RonanG51Basic
public import CFSG.Quasithin.Background.ShultG53Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
  (ρ : Representation (ZMod 2) ↥(alternatingGroup (Fin 6)) A)

theorem exists_simple_quot [Finite A]
    {N K : AddSubgroup A} (hN : InvSub (fun g a => ρ g a) N)
    (hK : IsMaxInvSub (fun g a => ρ g a) N K) :
    ∃ (i : Fin 4) (ψ : ↥N →+ D i), Function.Surjective ψ ∧ (∀ n : ↥N, ψ n = 0 ↔ (n : A) ∈ K) ∧
      ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥N),
        ψ ⟨ρ g n, hN g n n.2⟩ = a6BinaryRep i g (ψ n) := by
  obtain ⟨hKN, hKinv, hKmax⟩ := hK
  let Nm : Submodule (ZMod 2) A := AddSubgroup.toZModSubmodule 2 N
  have hle : ∀ g, Nm ≤ Nm.comap (ρ g) := fun g m hm => hN g m hm
  let ρN := ρ.subrepresentation Nm hle
  let Km : Submodule (ZMod 2) ↥Nm :=
    (AddSubgroup.toZModSubmodule 2 K).comap Nm.subtype
  have hle' : ∀ g, Km ≤ Km.comap (ρN g) := fun g m hm => hKinv g m hm
  let ρQ := ρN.quotient Km hle'
  haveI : Finite ↥Nm := Subtype.finite
  haveI : Finite (↥Nm ⧸ Km) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective Km)
  haveI : Nontrivial (↥Nm ⧸ Km) := by
    obtain ⟨n, hnN, hnK⟩ : ∃ n ∈ N, n ∉ K := by
      by_contra hcon
      push Not at hcon
      exact hKN.not_ge (fun n hn => hcon n hn)
    refine ⟨⟨Submodule.Quotient.mk ⟨n, hnN⟩, 0, fun h => hnK ?_⟩⟩
    exact (Submodule.Quotient.mk_eq_zero Km).mp h
  have hirr : ∀ S : AddSubgroup (↥Nm ⧸ Km),
      (∀ (g : ↥(alternatingGroup (Fin 6))) (m : ↥Nm ⧸ Km), m ∈ S → ρQ g m ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
    intro S hS
    let S₁ : AddSubgroup A :=
      { carrier := {a | ∃ h : a ∈ N, (Submodule.Quotient.mk ⟨a, h⟩ : ↥Nm ⧸ Km) ∈ S}
        add_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          exact ⟨N.add_mem ha hb, by
            have : (⟨a + b, N.add_mem ha hb⟩ : ↥Nm) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
            rw [this, Submodule.Quotient.mk_add]
            exact S.add_mem ha' hb'⟩
        zero_mem' := ⟨N.zero_mem, by
          have : (⟨0, N.zero_mem⟩ : ↥Nm) = 0 := rfl
          rw [this, Submodule.Quotient.mk_zero]
          exact S.zero_mem⟩
        neg_mem' := by
          rintro a ⟨ha, ha'⟩
          exact ⟨N.neg_mem ha, by
            have : (⟨-a, N.neg_mem ha⟩ : ↥Nm) = -⟨a, ha⟩ := rfl
            rw [this, Submodule.Quotient.mk_neg]
            exact S.neg_mem ha'⟩ }
    have hS₁N : S₁ ≤ N := fun a ⟨h, _⟩ => h
    have hKS₁ : K ≤ S₁ := by
      intro k hk
      have hkN : k ∈ N := hKN.le hk
      refine ⟨hkN, ?_⟩
      have : (Submodule.Quotient.mk ⟨k, hkN⟩ : ↥Nm ⧸ Km) = 0 :=
        (Submodule.Quotient.mk_eq_zero Km).mpr hk
      rw [this]
      exact S.zero_mem
    have hS₁inv : InvSub (fun g a => ρ g a) S₁ := by
      intro g a ⟨ha, ha'⟩
      refine ⟨hN g a ha, ?_⟩
      have := hS g _ ha'
      have h2 : ρQ g (Submodule.Quotient.mk ⟨a, ha⟩) =
          (Submodule.Quotient.mk ⟨ρ g a, hN g a ha⟩ : ↥Nm ⧸ Km) := rfl
      rw [h2] at this
      exact this
    rcases hKmax S₁ hS₁inv hKS₁ hS₁N with h | h
    · left
      refine (AddSubgroup.eq_bot_iff_forall S).mpr fun q hq => ?_
      obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.Quotient.mk_surjective Km q
      have : n ∈ S₁ := ⟨hn, hq⟩
      rw [h] at this
      exact (Submodule.Quotient.mk_eq_zero Km).mpr this
    · right
      refine (AddSubgroup.eq_top_iff' S).mpr fun q => ?_
      obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.Quotient.mk_surjective Km q
      have : n ∈ S₁ := by rw [h]; exact hn
      exact this.2
  obtain ⟨i, f, hf⟩ := a6_complete ρQ hirr
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · exact
      { toFun := fun n => f (Submodule.Quotient.mk ⟨n.1, n.2⟩)
        map_zero' := by
          have : (Submodule.Quotient.mk ⟨(0 : ↥N).1, (0 : ↥N).2⟩ : ↥Nm ⧸ Km) = 0 :=
            (Submodule.Quotient.mk_eq_zero Km).mpr (by exact Km.zero_mem)
          show f (Submodule.Quotient.mk ⟨(0 : ↥N).1, (0 : ↥N).2⟩) = 0
          rw [this, map_zero]
        map_add' := fun a b => by
          have : (Submodule.Quotient.mk ⟨(a + b : ↥N).1, (a + b : ↥N).2⟩ : ↥Nm ⧸ Km) =
              Submodule.Quotient.mk ⟨a.1, a.2⟩ + Submodule.Quotient.mk ⟨b.1, b.2⟩ := rfl
          show f (Submodule.Quotient.mk ⟨(a + b : ↥N).1, (a + b : ↥N).2⟩) = _
          rw [this, map_add] }
  · intro d
    obtain ⟨q, rfl⟩ := f.surjective d
    obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.Quotient.mk_surjective Km q
    exact ⟨⟨n, hn⟩, rfl⟩
  · intro n
    show f (Submodule.Quotient.mk ⟨n.1, n.2⟩) = 0 ↔ _
    rw [map_eq_zero_iff f f.injective, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  · intro g n
    show f (Submodule.Quotient.mk ⟨ρ g n, _⟩) = _
    have h2 : (Submodule.Quotient.mk ⟨ρ g n, hN g n n.2⟩ : ↥Nm ⧸ Km) =
        ρQ g (Submodule.Quotient.mk ⟨n.1, n.2⟩) := rfl
    rw [h2, hf]
    rfl

theorem exists_quot_md [Finite A] {N K : AddSubgroup A} (hN : InvSub (fun g a => ρ g a) N)
    (hK : InvSub (fun g a => ρ g a) K) (hKN : K ≤ N) :
    ∃ (C : Md ↥(alternatingGroup (Fin 6))) (π : ↥N →+ C.carrier), Function.Surjective π ∧
      (∀ n : ↥N, π n = 0 ↔ (n : A) ∈ K) ∧
      ∀ (g : ↥(alternatingGroup (Fin 6))) (n : ↥N),
        π ⟨ρ g n, hN g n n.2⟩ = C.ρ g (π n) := by
  let Nm : Submodule (ZMod 2) A := AddSubgroup.toZModSubmodule 2 N
  have hle : ∀ g, Nm ≤ Nm.comap (ρ g) := fun g m hm => hN g m hm
  let ρN := ρ.subrepresentation Nm hle
  let Km : Submodule (ZMod 2) ↥Nm :=
    (AddSubgroup.toZModSubmodule 2 K).comap Nm.subtype
  have hle' : ∀ g, Km ≤ Km.comap (ρN g) := fun g m hm => hK g m hm
  let ρQ := ρN.quotient Km hle'
  haveI : Finite ↥Nm := Subtype.finite
  haveI : Finite (↥Nm ⧸ Km) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective Km)
  refine ⟨⟨↥Nm ⧸ Km, ρQ⟩, ?_, ?_, ?_, ?_⟩
  · exact
      { toFun := fun n => Submodule.Quotient.mk ⟨n.1, n.2⟩
        map_zero' := (Submodule.Quotient.mk_eq_zero Km).mpr (by exact Km.zero_mem)
        map_add' := fun a b => rfl }
  · intro d
    obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.Quotient.mk_surjective Km d
    exact ⟨⟨n, hn⟩, rfl⟩
  · intro n
    exact Submodule.Quotient.mk_eq_zero Km
  · intro g n
    rfl

end CFSG.Quasithin.ShultG53
