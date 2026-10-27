module

public import CFSG.Quasithin.Background.RonanE68Sp4
public import CFSG.Quasithin.Background.RonanE611Comp
public import CFSG.Quasithin.Background.ONanE68S8

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE68

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.E68Proof
  CFSG.Quasithin.RonanE611 CFSG.Assembly.LowTwoRank

section Sp4

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem card_commutator_eq_of_decomp (h : HypE61 T M V) {C X : Subgroup G} (hCV : C ≤ V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hinf : ⁅V, X⁆ ⊓ C = ⊥)
    (hsup : ⁅V, X⁆ ⊔ C = V) : Nat.card ↥⁅V, X⁆ = 2 ^ E3.mQuot V C := by
  have hV := h.isElemAbelian
  have hWV := commutator_le_left (V := V) hXN
  have h1 := card_mul_eq_of_inf_sup (U := ⁅V, X⁆) (W := C) hinf hsup
    (fun w hw c hc => B2F.isElemAbelian_comm hV (hWV hw) (hCV hc))
  have h2 := E3.card_eq_two_pow_mul h.isPGroup_V hCV
  rw [h1] at h2
  have hpos : 0 < Nat.card ↥C := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h2

theorem rootClause_sp4 (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {n : ℕ} (hn : 2 ≤ n)
    (hm : StatedClassicalModel ↥L .PSp 2 2 n)
    (hdec : ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V)
    (hPS : L ⊓ Subgroup.normalizer
      (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) : Set G) ≤ L ⊓ M)
    (hPlt : L ⊓ M < L)
    (hPmax : ∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L)
    (hmq : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n) :
    E6.IsMarkedSp4Root n (autSubInduced L (L ⊔ V)) (autSubInduced L V) := by
  classical
  have hV := h.isElemAbelian
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer (U : Set G) with hHdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set S : Subgroup G := Q ⊓ L with hSdef
  set P := L ⊓ M with hPdef
  set C := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hLH : L ≤ H := hL.1
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  have hSL : IsSylowTwoOf S L := RankOneRecog.isSylowTwoOf_inf_of_subnormal hQH hLH hL.2.2
  have hHMN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := (e6_5_three h hU).2
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := fun y hy => hHMN ⟨hLH hy.1, hy.2⟩
  have hVN : V ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_component h hU hL
  have hVN' : ∀ v ∈ V, v ∈ Subgroup.normalizer (L : Set G) := fun v hv => hVN hv
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hs : IsSimpleGroup ↥L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n hm
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_simple_quasisimple hq hs
  have hVPL : ⁅V, P⁆ ≤ L :=
    CFSG.Quasithin.RonanE611.commutator_le_of_normalizes hVN' inf_le_left
  have hWV : ⁅V, P⁆ ≤ V := commutator_le_left hPN
  have hWS : ⁅V, P⁆ ≤ S := le_inf (hWV.trans h.le_inf_centralizer) hVPL
  have hWc : ∀ w ∈ ⁅V, P⁆, ∀ s ∈ S, w * s = s * w := fun w hw s hs' =>
    Subgroup.mem_centralizer_iff.1 (hs'.1.2 : s ∈ Subgroup.centralizer (V : Set G)) w (hWV hw)
  have hW2 : ∀ w ∈ ⁅V, P⁆, w * w = 1 := fun w hw => by
    have := F7.isElemAbelian_pow_eq_one hV (hWV hw)
    rwa [pow_two] at this
  have hWcard : Nat.card ↥⁅V, P⁆ = 2 ^ n := by
    rw [card_commutator_eq_of_decomp h inf_le_left hPN hdec.1 hdec.2, hmq]
  have hWn : ∀ p ∈ P, ∀ w ∈ ⁅V, P⁆, p * w * p⁻¹ ∈ ⁅V, P⁆ := fun p hp w hw =>
    (Subgroup.mem_normalizer_iff.1
      (mem_normalizer_commutator (hPN hp) (Subgroup.le_normalizer hp)) w).1 hw
  obtain ⟨K, _, _, _, φ, hK, hφ⟩ := Sp4G.exists_adapted hn hm hSL
  obtain ⟨i, hWi, -⟩ := Sp4G.parabolic hn hK hφ hSL inf_le_left hPS (ne_of_lt hPlt) hPmax hWS hWc
    hWn hW2 hWcard
  have hCN : C ≤ Subgroup.normalizer ((⁅V, P⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun c hc w hw => by
      have := hVPL hw
      exact (Subgroup.mem_centralizer_iff.1 hc.2 w this).symm
  have hdec' : ∀ v ∈ V, ∃ w ∈ ⁅V, P⁆, ∀ x ∈ L, v * x * v⁻¹ = w * x * w⁻¹ := by
    intro v hv
    have hv' : v ∈ ((⁅V, P⁆ : Subgroup G) : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (⁅V, P⁆ : Subgroup G) C hCN, hdec.2]
      exact hv
    obtain ⟨w, hw, c, hc, rfl⟩ := hv'
    refine ⟨w, hw, fun x hx => ?_⟩
    have hcx : (c : G) * x = x * c := (Subgroup.mem_centralizer_iff.1 hc.2 x hx).symm
    calc w * c * x * (w * c)⁻¹ = w * (c * x * c⁻¹) * w⁻¹ := by group
      _ = w * x * w⁻¹ := by rw [hcx]; group
  exact isMarkedSp4Root_of_root hK hZ φ i hWi hVN hWV hdec'

end Sp4

end CFSG.Quasithin.RonanE68
