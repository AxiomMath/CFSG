module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HDefs
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Types

variable {G : Type} [Group G] [Finite G]

@[expose] def Typ129IIIcType (L Y : Subgroup G) : Prop :=
  (∃ q : TauCeti.PrimePower, Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q.card) ∧
  ((∃ (p e : ℕ) (_ : Fact p.Prime), Sec4.IsoLThreePi (Y ⧸ CFSG.pCore 2 Y) p e) ∨
    ∃ (q₀ : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid),
      Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q₀, hq⟩).Group)) ∧
  Subgroup.center (Y ⧸ CFSG.pCore 2 Y) = ⊥

@[expose] def Typ129IIIcE (A : Subgroup G) (c : G) (Y : Subgroup G) (x : G) (E : Subgroup G) :
    Prop :=
  Late.IsE27 E ∧ E = Subgroup.zpowers x ⊔ (E ⊓ Y) ∧ c ∈ E ⊓ Y ∧
    ¬ Y ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
    (∃ Z U : Subgroup G, E ⊔ A = Z ⊔ U ∧ Z ⊓ U = ⊥ ∧ Nat.card Z = 3 ∧
      (∀ z ∈ Z, ∀ u ∈ U, z * u = u * z) ∧ Sec4.IsHeisThree U) ∧
    Nonempty (Sec4.autIn (Y ⊔ A) E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

theorem typ129IIIcMinus_iff {A : Subgroup G} {c : G} {L Y : Subgroup G} {x : G} :
    Typ129IIIcMinus A c L Y x ↔ Typ129IIIcType L Y ∧ ∃ E, Typ129IIIcE A c Y x E :=
  ⟨fun ⟨h1, h2, h3, E, hE⟩ => ⟨⟨h1, h2, h3⟩, E, hE⟩,
    fun ⟨⟨h1, h2, h3⟩, E, hE⟩ => ⟨h1, h2, h3, E, hE⟩⟩

end Types

@[expose] def NoLieParamInRange {G : Type} [Group G] [Finite G] (Y : Subgroup G) : Prop :=
  ∀ (r : TauCeti.PrimePower) (δ : ℕ),
    ((δ = 1 ∧ Sec4.IsoGTwo (Y ⧸ CFSG.pCore 2 Y) r) ∨
      (δ = 3 ∧ ∃ hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid,
        Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group))) →
    ¬ (4 ≤ r.card ∧ r.p ≠ 3 ∧ (δ = 3 → r.p = 2))

@[expose] def Gap129EndE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
    GTwoType129At L K q →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b → x ∉ L →
      ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y → NoLieParamInRange Y →
        Typ129IIIcType L Y → ∀ E : Subgroup G, Typ129IIIcE A c Y x E →
      ∀ d ∈ D129 a b, d ∉ Subgroup.zpowers b → d ∈ L → ∀ Y' J : Subgroup G,
        Core129 A c d Y' → resCent K d ≤ Y' → JData129 A c L Y' J → b ∈ J →
        ∀ r : TauCeti.PrimePower,
          Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card →
          ¬ PiModNine r.card → ¬ PiModNine q.card →
          ∃ F : Subgroup G, Late.IsE27 F ∧ c ∈ F ∧ F ≤ lcBar c L ∧
            ¬ Subgroup.normalizer (F : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

section End

variable {G : Type} [Group G] [Finite G]

theorem not_mem_of_center_pCore_eq_bot {x : G} {Y : Subgroup G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hYx : Y ≤ Subgroup.centralizer ({x} : Set G))
    (hZY : Subgroup.center (Y ⧸ CFSG.pCore 2 Y) = ⊥) : x ∉ Y := by
  intro hxY
  have hc : QuotientGroup.mk' (CFSG.pCore 2 Y) ⟨x, hxY⟩ ∈
      Subgroup.center (Y ⧸ CFSG.pCore 2 Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
      have hg : (g : G) * x = x * (g : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hYx g.2)
      change ((g * ⟨x, hxY⟩ : Y) : Y ⧸ CFSG.pCore 2 Y) =
        ((⟨x, hxY⟩ * g : Y) : Y ⧸ CFSG.pCore 2 Y)
      rw [show (g * ⟨x, hxY⟩ : Y) = ⟨x, hxY⟩ * g from Subtype.ext hg]
  rw [hZY, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
  have hp : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨⟨x, hxY⟩, hc⟩
  have hord : orderOf (⟨x, hxY⟩ : Y) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx3 hx1
  have hk' : orderOf (⟨x, hxY⟩ : Y) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨⟨x, hxY⟩, hc⟩ : CFSG.pCore 2 Y)).trans hk
  have h3 : (3 : ℕ) = 2 ^ k := hord.symm.trans hk'
  have : Even (2 ^ k) ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (Nat.even_pow.mpr ⟨even_two, h0.ne'⟩)
  rcases this with h | h
  · rw [← h3] at h
    exact absurd h (by decide)
  · rw [h] at h3
    exact absurd h3 (by norm_num)

end End

end CFSG.RankThree.PartTwo.Sec12
