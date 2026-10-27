module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreEvenM
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreLift
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreOdd

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem core_odd (hK : PiField π p f K) (hp : p ≠ 2) {X : Type} [Group X] [Finite X]
    (M : LModel π p f K X) {H : Subgroup X} {T : Type} [Group T] [Finite T] {F : Subgroup T}
    (hF : ∀ x ∈ F, x ^ 2 = 1) (hFc : 16 < Nat.card F) (φ : ↥H →* T)
    (hφ : Function.Surjective φ) : False := by
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  have := hK.charP
  have hF2 : IsPGroup 2 F := fun x => ⟨1, Subtype.ext (by simpa using hF x x.2)⟩
  obtain ⟨B, hB2, hBF⟩ := exists_isPGroup_map_eq φ hφ hF2
  set R : Subgroup X := B.map H.subtype with hRdef
  have hR2 : IsPGroup 2 R := hB2.map H.subtype
  set L := slPi π 3 (p ^ f) K with hL
  obtain ⟨hker, hcen⟩ := lmodel_ker hK M
  obtain ⟨S, hS2, hSR, hSinj, -⟩ := exists_lift M.μ M.surjective hker hcen R hR2
  set Hc : Subgroup ↥L := H.comap M.μ with hHc
  let μH : ↥Hc →* ↥H := (M.μ.comp Hc.subtype).codRestrict H fun g => g.2
  let φ' : ↥Hc →* T := φ.comp μH
  have hRH : R ≤ H := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hSc : S ≤ Hc := by
    intro s hs
    rw [hHc, Subgroup.mem_comap]
    exact hRH (hSR ▸ ⟨s, hs, rfl⟩)
  let ψ₀ : ↥S →* T := φ'.comp (Subgroup.inclusion hSc)
  have hψ₀ : ∀ s : ↥S, ψ₀ s ∈ F := fun s => by
    have hs : M.μ (s : ↥L) ∈ S.map M.μ := ⟨s, s.2, rfl⟩
    rw [hSR] at hs
    obtain ⟨b, hb, hbs⟩ := hs
    rw [← hBF]
    refine ⟨b, hb, ?_⟩
    show φ b = φ ⟨M.μ (s : ↥L), _⟩
    congr 1
    exact Subtype.ext hbs
  let ψ : ↥S →* ↥F := ψ₀.codRestrict F hψ₀
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : T) ∈ B.map φ := by rw [hBF]; exact x.2
    obtain ⟨b, hb, hbx⟩ := hx
    have hbR : (b : X) ∈ S.map M.μ := by rw [hSR]; exact ⟨b, hb, rfl⟩
    obtain ⟨s, hs, hsb⟩ := hbR
    refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
    show φ ⟨M.μ s, _⟩ = (x : T)
    rw [← hbx]
    congr 1
    exact Subtype.ext hsb
  have hbound := card_elem_quotient_le_of_odd (K := K) (p := p) hp
    (L.subtype.comp S.subtype) (Subtype.val_injective.comp Subtype.val_injective) hS2
    (E := ↥F) (fun x => Subtype.ext (hF x x.2)) ψ hψ
  omega

end CFSG.RankThree.PartTwo.Sec15.KS1424
