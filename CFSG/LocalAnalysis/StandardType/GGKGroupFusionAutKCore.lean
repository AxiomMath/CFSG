module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestOuter
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.RankThree.PartOne.OutStructure

@[expose] def GGLieOutRankTwoAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  Finite (TauCeti.CFSGIndex.lie d).Group → IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group →
    (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) → d.1.characteristic ≠ 2 →
      ∀ E : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
        IsElemAbelian d.1.characteristic E → Nat.card E = d.1.characteristic ^ 2 →
          E ⊓ (MulAut.conj : (TauCeti.CFSGIndex.lie d).Group →* MulAut _).range = ⊥ →
            ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.p = 3 ∧ 3 ∣ q.exponent

theorem ggLieOutRankTwoInput_of_forall (h : ∀ d, GGLieOutRankTwoAt d) : GGLieOutRankTwoInput :=
  fun d => h d

theorem ggNot_outerPlane_of_outPChain {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hO : OutPChain p X) (E : Subgroup (MulAut X)) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) (hEI : E ⊓ (MulAut.conj : X →* MulAut X).range = ⊥) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hno
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  have hcyc : ∀ c ∈ E, c ≠ 1 → Nat.card (Subgroup.zpowers c) = p := fun c hc hc1 => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE.2 c hc) hc1
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers a := fun b hb => hno b hb
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard, hcyc a haE ha1] at h1
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp1 one_lt_two
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hab : a * b = b * a := by
    have := hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩
    exact congrArg Subtype.val this
  have hinn : ∀ c ∈ E, c ^ (p ^ 1) ∈ Inn X := fun c hc => by
    rw [pow_one, hE.2 c hc]
    exact Subgroup.one_mem _
  have htriv : ∀ c ∈ E, c ∈ Inn X → c = 1 := fun c hc hcI => by
    have hmem : c ∈ E ⊓ (MulAut.conj : X →* MulAut X).range := ⟨hc, hcI⟩
    rw [hEI] at hmem
    exact (Subgroup.mem_bot).mp hmem
  rcases hO.comparable hab (hinn a haE) (hinn b hbE) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have h1 : a * b ^ m = 1 := htriv _ (mul_mem haE (zpow_mem hbE m)) hm
    have h2 : a ∈ Subgroup.zpowers b := by
      have : a = b ^ (-m) := by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _
    have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b :=
      (Subgroup.zpowers_le (G := MulAut X)).mpr h2
    have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcyc a haE ha1, hcyc b hbE hb1])
    exact hba (heq ▸ Subgroup.mem_zpowers b)
  ·
    have h1 : b * a ^ m = 1 := htriv _ (mul_mem hbE (zpow_mem haE m)) hm
    apply hba
    have : b = a ^ (-m) := by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _

theorem ggLieOutRankTwoAt_of_outPChain {d : TauCeti.ValidLieTypeIndex}
    (h : OutPChain d.1.characteristic (TauCeti.CFSGIndex.lie d).Group) : GGLieOutRankTwoAt d :=
  fun _ _ _ _ E hE hcard hEI =>
    (ggNot_outerPlane_of_outPChain (TauCeti.LieTypeIndex.characteristic_prime d.1) h E hE hcard
      hEI).elim

@[expose] def GGNoOuterPlane (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ E : Subgroup (MulAut X), IsElemAbelian p E → Nat.card E = p ^ 2 →
    E ⊓ (MulAut.conj : X →* MulAut X).range = ⊥ → False

theorem GGNoOuterPlane.of_mulEquiv {X Y : Type} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (h : GGNoOuterPlane p Y) : GGNoOuterPlane p X := by
  intro E hE hcard hEI
  set φ : MulAut X ≃* MulAut Y := MulAut.congr e with hφ
  have hinner := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  refine h (E.map φ.toMonoidHom) (ggIsElemAbelian_map hE _) ?_ ?_
  · rw [Subgroup.card_map_of_injective φ.injective, hcard]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨α, hα, rfl⟩, hαI⟩
    have hαI' : φ.toMonoidHom α ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner X).map
        φ.toMonoidHom := by
      rw [hinner]
      exact hαI
    obtain ⟨β, hβ, hβα⟩ := hαI'
    have hβα' : β = α := φ.injective hβα
    subst hβα'
    have hmem : β ∈ E ⊓ (MulAut.conj : X →* MulAut X).range := ⟨hα, hβ⟩
    rw [hEI, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
    exact Subgroup.one_mem _

theorem ggLieOutRankTwoAt_of_noOuterPlane {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (hd : d.1.characteristic = p)
    (h : p ≠ 2 → GGNoOuterPlane p (TauCeti.CFSGIndex.lie d).Group) : GGLieOutRankTwoAt d := by
  subst hd
  exact fun _ _ _ hp2 E hE hcard hEI => (h hp2 E hE hcard hEI).elim

theorem ggLieOutRankTwoAt_of_char {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (hd : d.1.characteristic = p) (h : p ≠ 2 → OutPChain p (TauCeti.CFSGIndex.lie d).Group) :
    GGLieOutRankTwoAt d := by
  subst hd
  exact fun hfin hs hnab hp2 => ggLieOutRankTwoAt_of_outPChain (h hp2) hfin hs hnab hp2

end CFSG.StandardType
