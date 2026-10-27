module

public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E6Gamma

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239

section Dich

variable {G : Type} [Group G] [Finite G] {T M V U K : Subgroup G}

omit [Finite G] in
theorem cgsIn_mono_left {K H Q : Subgroup G} (hKH : K ≤ H) : cgsIn K Q ≤ cgsIn H Q :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    inf_le_inf_right _ hKH

theorem block_dichotomy (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hKH : K ≤ Subgroup.centralizer (U : Set G))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hK : CharTwo K) :
    K ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) ≤ M ∨
      ∃ B : Subgroup G, IsChi0Block (K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) B ∧ ¬ B ≤ M ∧
        IsBorelOfBlock B (B ⊓ ((K ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⊓ M)) ∧
        ⁅B, thompsonJ (T ⊓ Subgroup.centralizer (V : Set G))⁆ = B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set H := Subgroup.centralizer (U : Set G) with hHdef
  have hQH : IsSylowTwoOf Q H := e6_5_one h hU
  set K' := K ⊔ Q with hK'def
  have hQK' : Q ≤ K' := le_sup_right
  have hK'H : K' ≤ H := sup_le hKH hQH.1
  have hK'c : CharTwo K' := Vol2Native.L239.charTwo_sup_of_le_normalizer hK h.isPGroup_Q hQN
  have hQsyl : IsSylowTwoOf Q K' := A4.isSylowTwoOf_mono hQH hQK' hK'H
  have hcgs : cgsIn K' Q ≤ K' ⊓ M := by
    refine le_inf (iSup_le fun C => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      inf_le_left) ?_
    exact (cgsIn_mono_left hK'H).trans ((e6_5_two h hU).1.trans inf_le_right)
  have hO2 : pCoreOf 2 K' ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hK'c
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQK'.trans h1)
  have hsq : IsSQTKIn K' :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ := hC129 G K' Q (K' ⊓ M) hsq hK'c hQsyl hcgs inf_le_left
  by_cases hall : ∀ i, Lb i ≤ M
  · left
    intro y hy
    obtain ⟨m, hm, z, hz, rfl⟩ := hprod y hy
    refine M.mul_mem hm.2 (Subgroup.list_prod_mem (K := M) fun w hw => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hw
    exact hall j (hz j)
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨hchi, hBor, hJ⟩ := hLb i
    exact ⟨Lb i, hchi, hi, hBor, hJ⟩

theorem dich (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) (hKH : K ≤ Subgroup.centralizer (U : Set G))
    (hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hK : CharTwo K) : K ≤ M ∨ HasChi0Block K := by
  rcases block_dichotomy hC129 h hU hKH hQN hK with hle | ⟨B, hB, -⟩
  · exact Or.inl (le_sup_left.trans hle)
  · exact Or.inr ⟨B, Vol2Native.L239.isChi0Block_of_isChi0Block_sup h.isPGroup_Q hQN hB⟩

end Dich

end E68Proof

end E6

end CFSG.Quasithin
