module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5

variable {G : Type} [Group G]

@[expose] def CosetTrans (H A B : Subgroup G) : Prop := ∀ g ∈ A, ∃ n ∈ H ⊓ A, n⁻¹ * g ∈ B

@[expose] def nbrKernel (A B : Subgroup G) : Subgroup G :=
  A ⊓ ⨅ g : A, (A ⊓ B).map (MulAut.conj (g : G)).toMonoidHom

abbrev normIn (X H : Subgroup G) : Subgroup G := normalizer (X : Set G) ⊓ H

structure IsArcClass (A₀ A₁ A₂ K : Subgroup G) (y : G) (X : Subgroup G) : Prop where
  ne_bot : X ≠ ⊥
  le : X ≤ A₀ ⊓ A₁ ⊓ A₂
  K_le : K ≤ normalizer (X : Set G)
  trans₀ : CosetTrans (normalizer (X : Set G)) A₀ A₁
  trans₂ : CosetTrans (normalizer (X : Set G)) A₂ A₁
  pair : ∀ g ∈ normIn X A₁, g ∈ A₀ ⊓ A₂ ∨ y⁻¹ * g ∈ A₀ ⊓ A₂
  swap : ∃ g ∈ normIn X A₁, y⁻¹ * g ∈ A₀ ⊓ A₂

@[expose] def IsArcClassMax (A₀ A₁ A₂ K : Subgroup G) (y : G) (X : Subgroup G) : Prop :=
  IsArcClass A₀ A₁ A₂ K y X ∧ IsPGroup 2 X ∧
    ∀ Y : Subgroup G, IsArcClass A₀ A₁ A₂ K y Y → IsPGroup 2 Y →
      normIn X A₀ ≤ normIn Y A₀ → normIn Y A₀ ≤ normIn X A₀

theorem CosetTrans.mono {H H' A B : Subgroup G} (h : CosetTrans H A B) (hH : H ≤ H') :
    CosetTrans H' A B := by
  intro g hg
  obtain ⟨n, hn, hnb⟩ := h g hg
  exact ⟨n, ⟨hH hn.1, hn.2⟩, hnb⟩

theorem cosetTrans_self (A B : Subgroup G) : CosetTrans A A B := by
  intro g hg
  exact ⟨g, ⟨hg, hg⟩, by simpa using B.one_mem⟩

theorem CosetTrans.map_conj {H A B : Subgroup G} (h : CosetTrans H A B) (g : G) :
    CosetTrans (H.map (MulAut.conj g).toMonoidHom) (A.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom) := by
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨n, hn, hnb⟩ := h a ha
  refine ⟨g * n * g⁻¹, ⟨⟨n, hn.1, rfl⟩, ⟨n, hn.2, rfl⟩⟩, ?_⟩
  show (g * n * g⁻¹)⁻¹ * (g * a * g⁻¹) ∈ B.map (MulAut.conj g).toMonoidHom
  have hval : (g * n * g⁻¹)⁻¹ * (g * a * g⁻¹) = g * (n⁻¹ * a) * g⁻¹ := by group
  rw [hval]
  exact ⟨n⁻¹ * a, hnb, rfl⟩

theorem mem_nbrKernel_iff {A B : Subgroup G} {x : G} :
    x ∈ nbrKernel A B ↔ x ∈ A ∧ ∀ g ∈ A, g⁻¹ * x * g ∈ A ⊓ B := by
  unfold nbrKernel
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨hxA, hxall⟩
    refine ⟨hxA, fun g hg => ?_⟩
    obtain ⟨y, hy, hgy⟩ := hxall ⟨g, hg⟩
    have hgy' : g * y * g⁻¹ = x := by simpa using hgy
    have hconj : g⁻¹ * x * g = y := by
      rw [← hgy']
      group
    rw [hconj]
    exact hy
  · rintro ⟨hxA, hxall⟩
    refine ⟨hxA, fun g => ⟨(g : G)⁻¹ * x * (g : G), hxall (g : G) g.2, ?_⟩⟩
    have hconj : (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x := by group
    simpa using hconj

theorem nbrKernel_le (A B : Subgroup G) : nbrKernel A B ≤ A ⊓ B := by
  intro x hx
  rw [mem_nbrKernel_iff] at hx
  simpa using hx.2 (1 : G) A.one_mem

theorem IsArcClassMax.isArcClass {A₀ A₁ A₂ K : Subgroup G} {y : G} {X : Subgroup G}
    (h : IsArcClassMax A₀ A₁ A₂ K y X) : IsArcClass A₀ A₁ A₂ K y X :=
  h.1

theorem IsArcClassMax.isPGroup {A₀ A₁ A₂ K : Subgroup G} {y : G} {X : Subgroup G}
    (h : IsArcClassMax A₀ A₁ A₂ K y X) : IsPGroup 2 X :=
  h.2.1

variable [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

abbrev ArcL (X : Subgroup G) : Prop := IsArcClass (t.Gv 1) (t.Gv 0) (t.Gv (-1)) t.K t.x₁ X

abbrev ArcSz (X : Subgroup G) : Prop := IsArcClass (t.Gv 0) (t.Gv 1) (t.Gv 2) t.K t.x₂ X

abbrev ArcLMax (X : Subgroup G) : Prop := IsArcClassMax (t.Gv 1) (t.Gv 0) (t.Gv (-1)) t.K t.x₁ X

abbrev ArcSzMax (X : Subgroup G) : Prop := IsArcClassMax (t.Gv 0) (t.Gv 1) (t.Gv 2) t.K t.x₂ X

abbrev MX (X : Subgroup G) (i : ℤ) : Subgroup G := normIn X (t.Gv i)

abbrev EX (X : Subgroup G) (i : ℤ) : Subgroup G := t.Qv i ⊓ normalizer (X : Set G)

abbrev LX (X : Subgroup G) (i : ℤ) : Subgroup G := oTwoPrime (t.MX X i)

abbrev YX (X : Subgroup G) (i : ℤ) : Subgroup G := oTwoRes (t.LX X i)

abbrev PX (X : Subgroup G) : Subgroup G := t.Qv 0 ⊓ t.MX X 1

abbrev QT : Subgroup G := pCoreOf 2 t.GT

abbrev Gnbr (i : ℤ) : Subgroup G := nbrKernel (t.Gv i) (t.Gv (i + 1))

end Track

end CFSG.Quasithin.Stroth.Rq

end
