module
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmall
import CFSG.Goldschmidt.Steps.Sec82Tools
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Timmesfeld.Bridge.Asc72

theorem isOddTransp_of_embedding (G : Type) [Group G] [Finite G] {V H E : Subgroup G}
    (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {Y : Type} [Group Y] {ι : Y →* X}
    (hι : Function.Injective ι) {s : Y} (hsV : ι s ∈ barSub (kSub V H E) φ V) (hs1 : s ≠ 1) :
    IsOddTransp {x : Y | IsConj s x} := by
  have hne : ι s ≠ 1 := fun hh => hs1 (hι (by simpa using hh))
  obtain ⟨-, hodd, -⟩ := seven_eleven_small_hyps h hφ hS hsV hne
  have hmem : ∀ x ∈ {x : Y | IsConj s x}, ι x ∈ {x : X | IsConj (ι s) x} :=
    fun x hx => (isConj_iff.mpr (by
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      exact ⟨ι c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩ ))
  refine ⟨fun d hd => ?_, fun d hd e he => ?_⟩
  · rw [← orderOf_injective ι hι d]
    exact hodd.1 _ (hmem d hd)
  · have := hodd.2 _ (hmem d hd) _ (hmem e he)
    rwa [← map_mul, orderOf_injective ι hι] at this

theorem commute_of_commute_fitting {Y : Type} [Group Y] [Finite Y] {X T : Subgroup Y}
    (hX : Odd (Nat.card X)) (hsol : IsSolvable X) (hT : IsPGroup 2 T)
    (hTX : T ≤ Subgroup.normalizer (X : Set Y))
    (hF : ∀ t ∈ T, ∀ f ∈ (CFSG.fittingSubgroup X).map X.subtype, Commute t f) :
    ∀ t ∈ T, ∀ x ∈ X, Commute t x := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hcop : Nat.Coprime (Nat.card T) (Nat.card X) := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hX)
  have hle := CFSG.Goldschmidt.Sec82.le_centralizer_of_coprime_of_fitting hsol hTX hcop
    (fun f hf => Subgroup.mem_centralizer_iff.mpr fun t ht => (hF t ht f hf).eq)
  intro t ht x hx
  exact Subgroup.mem_centralizer_iff.mp (hle hx) t ht

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
