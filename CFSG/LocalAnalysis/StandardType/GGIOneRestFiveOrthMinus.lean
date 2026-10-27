module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndMain

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneOrthMinusOddRootInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 4 ≤ m →
    Even m → p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGEndNodeRootEltBig p m (OrthRest.RMinus K m b c)

section Certs

theorem ggEndNodeIOne_orthMinus_of_root (hE : GGIOneOrthMinusOddRootInput) {K : Type} [Field K]
    [Finite K] {n m p : ℕ} {b c : K} (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hme : Even m)
    (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGEndNodeIOne p m (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hC⟩ := ggOrthRestCenterInput_holds.1 K n m p b c hK (by omega) hp hpn hbc
  exact ggEndNodeIOne_of_rootEltBig (fun _ hφ _ => hφ) hZ hC
    (hE K n m p b c hK hm hme hp hpn hbc)

theorem largeEvenLabelAll_endNodeIOne_orthMinusOddField (hE : GGIOneOrthMinusOddRootInput)
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (h : GGIOneMoreOrthMinusOddFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hlo, hpn, -⟩ := h
  dsimp only at ht hl hlo hpn
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
    have hme : Even (l - 1) := by
      obtain ⟨k, hk⟩ := hlo
      exact ⟨k, by omega⟩
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, ggOutdiagOdd_innSet _ _, l - 1,
      ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc,
      ggEndNodeIOne_orthMinus_of_root hE hK (by omega) hme hp hpn hbc⟩

theorem ggStdSubIOneProperInputOn_orthMinusOddField (ha₀ : GGLNoncyclicInput)
    (hE : GGIOneOrthMinusOddRootInput) :
    GGStdSubIOneProperInputOn GGIOneMoreOrthMinusOddFieldLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ hp _ h _ =>
    largeEvenLabelAll_endNodeIOne_orthMinusOddField hE hp h

end Certs

end CFSG.StandardType
