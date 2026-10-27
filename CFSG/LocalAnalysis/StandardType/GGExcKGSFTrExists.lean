module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTr
import CFSG.LocalAnalysis.StandardType.GGExcKGSFTransport
import CFSG.LocalAnalysis.StandardType.GGExcKGSFFinite
import CFSG.LocalAnalysis.StandardType.GGExcKGSFCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Helpers

open CFSG.Open

open scoped IsMulCommutative

variable {p : ℕ}

private theorem isElemAbelian_map_iff {H A : Type*} [Group H] [Group A] {φ : H →* A}
    (hφ : Function.Injective φ) {X : Subgroup H} :
    IsElemAbelian p (X.map φ) ↔ IsElemAbelian p X := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨?_, fun x hx => ?_⟩
    · rw [isMulCommutative_iff] at hc ⊢
      intro a b
      apply Subtype.ext
      apply hφ
      have := congrArg Subtype.val (hc ⟨φ a, ⟨a, a.2, rfl⟩⟩ ⟨φ b, ⟨b, b.2, rfl⟩⟩)
      simpa using this
    · apply hφ
      rw [map_pow, map_one]
      exact hp (φ x) ⟨x, hx, rfl⟩
  · rintro ⟨hc, hp⟩
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff] at hc ⊢
      rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      have := congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
      simpa [← map_mul] using congrArg φ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hp x hx, map_one]

private theorem transport_sylow {G A : Type*} [Group G] [Group A] [Finite G] [Fact p.Prime]
    {Nn : Subgroup G} (c : Nn →* A) (hc : Function.Injective c) {Bs : Subgroup G} (hBs : Bs ≤ Nn)
    (P : Sylow p Nn) (hBP : Bs ≤ (P : Subgroup Nn).map Nn.subtype)
    (huniq : ∀ E : Subgroup G, E ≤ (P : Subgroup Nn).map Nn.subtype → IsElemAbelian p E →
      Nat.card E = Nat.card Bs → E = Bs) :
    ∃ P' : Sylow p c.range,
      (Bs.subgroupOf Nn).map c ≤ (P' : Subgroup c.range).map c.range.subtype ∧
      ∀ E' : Subgroup A, E' ≤ (P' : Subgroup c.range).map c.range.subtype → IsElemAbelian p E' →
        Nat.card E' = Nat.card ((Bs.subgroupOf Nn).map c) → E' = (Bs.subgroupOf Nn).map c := by
  haveI : Finite Nn := inferInstance
  refine ⟨Sylow.mapSurjective c.rangeRestrict_surjective P, ?_⟩
  have hmap : ((Sylow.mapSurjective c.rangeRestrict_surjective P : Sylow p c.range) :
      Subgroup c.range).map c.range.subtype = (P : Subgroup Nn).map c := by
    show ((P : Subgroup Nn).map c.rangeRestrict).map c.range.subtype = _
    rw [Subgroup.map_map]
    rfl
  rw [hmap]
  have hBsP : Bs.subgroupOf Nn ≤ (P : Subgroup Nn) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hBP hx
    obtain rfl : y = x := Subtype.ext hyx
    exact hy
  have hcardBs : Nat.card (Bs.subgroupOf Nn) = Nat.card Bs :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBs).toEquiv
  refine ⟨Subgroup.map_mono hBsP, ?_⟩
  intro E' hE'P hE'ab hE'card
  have hE'range : E' ≤ c.range := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hE'P hx
    exact ⟨y, rfl⟩
  have hcomapP : E'.comap c ≤ (P : Subgroup Nn) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hE'P hx
    obtain rfl : y = x := hc hyx
    exact hy
  have hmapcomap : (E'.comap c).map c = E' := Subgroup.map_comap_eq_self hE'range
  have hab1 : IsElemAbelian p (E'.comap c) := by
    rw [← isElemAbelian_map_iff hc, hmapcomap]
    exact hE'ab
  have hab2 : IsElemAbelian p ((E'.comap c).map Nn.subtype) :=
    (isElemAbelian_map_iff Nn.subtype_injective).2 hab1
  have hcard2 : Nat.card ((E'.comap c).map Nn.subtype) = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective Nn.subtype_injective, ← hcardBs,
      ← Subgroup.card_map_of_injective hc, hmapcomap, hE'card,
      Subgroup.card_map_of_injective hc]
  have heq : (E'.comap c).map Nn.subtype = Bs :=
    huniq _ (Subgroup.map_mono hcomapP) hab2 hcard2
  have hcomap_eq : E'.comap c = Bs.subgroupOf Nn := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBs] at heq
    exact Subgroup.map_injective Nn.subtype_injective heq
  rw [← hmapcomap, hcomap_eq]

end Helpers

section Universal

theorem exists_ggSFTr (hCI : GGKGInndiagCI) {t : StatedLieTag} {n f : ℕ} (ht : GGExcFive t)
    {G : Type} [Group G] [Finite G] {ψ : (ggU t n f).K →* G} (hset : GGKnownSetting t n f ψ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) (M : GGKGModel t n f p)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (h4 : p ^ 4 ≤ Nat.card Bs)
    (hN : Bs ≤ Subgroup.normalizer (ψ.range : Set G))
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b)
    (hP : ∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
      Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype →
        IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs) :
    Nonempty (GGSFTr t n f p M ψ Bs) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ggU t n f).K := ggU_finite_exc ht hset.1
  obtain ⟨c, hcinj, hcpsi, hciff⟩ := ggTransportHom hset
  obtain ⟨P, hBP, huniq⟩ := hP
  obtain ⟨P', hEP, huniq'⟩ := transport_sylow c hcinj hN P hBP huniq
  have hcardE : Nat.card ((Bs.subgroupOf (Subgroup.normalizer (ψ.range : Set G))).map c) =
      Nat.card Bs := by
    rw [Subgroup.card_map_of_injective hcinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hBsab : IsElemAbelian p (Bs.subgroupOf (Subgroup.normalizer (ψ.range : Set G))) := by
    rw [← isElemAbelian_map_iff (Subgroup.normalizer (ψ.range : Set G)).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hN]
    exact hBs
  have hEab : IsElemAbelian p
      ((Bs.subgroupOf (Subgroup.normalizer (ψ.range : Set G))).map c) :=
    (isElemAbelian_map_iff hcinj).2 hBsab
  have hEdiag : ∀ b ∈ (Bs.subgroupOf (Subgroup.normalizer (ψ.range : Set G))).map c,
      GGInnDiagU t n f b := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hciff x).1 (hdiag x hx)
  have hNle : (ggPsiU t n f).range ≤ c.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨ψ k, Subgroup.le_normalizer ⟨k, rfl⟩⟩, hcpsi k⟩
  obtain ⟨κ, hκ, himg⟩ := ggSF_core hCI ht hset.1 hp hp2 hreg M hNle P' hEab
    (by rw [hcardE]; exact h4) hEP hEdiag huniq'
  refine ⟨{
    N := Subgroup.normalizer (ψ.range : Set G), psi_le := Subgroup.le_normalizer,
    bs_le := hN, hom := (MulAut.conj κ).toMonoidHom.comp c,
    hom_inj := fun a b h => hcinj ((MulAut.conj κ).injective h), kappa := κ,
    kappa_diag := hκ, hom_psi := fun k => ?_, img := ?_ }⟩
  · rw [MonoidHom.comp_apply, hcpsi k]
    simp [MulAut.conj_apply]
  · rw [← Subgroup.map_map]
    exact himg

end Universal

end CFSG.StandardType
