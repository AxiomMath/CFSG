module

public import CFSG.Quasithin.Background.E6SevenThree
public import CFSG.Quasithin.Background.E6SevenTwo
public import CFSG.Quasithin.Background.E6SevenTwoA5
public import CFSG.Quasithin.Background.E6SixSeven
public import CFSG.Quasithin.Background.E6Nine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Fstar
public import CFSG.Quasithin.H13.VolIC129Holds

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem mQuot_le_one_of_relIndex_le_two {V U : Subgroup G} (hV : IsPGroup 2 V)
    (h : U.relIndex V ≤ 2) : E3.mQuot V U ≤ 1 := by
  rw [E3.relIndex_eq_two_pow hV U] at h
  by_contra hm
  push Not at hm
  have : 2 ^ 2 ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem one_le_mQuot {V U : Subgroup G} (hV : IsPGroup 2 V) (hUV : U ≤ V) (hne : U ≠ V) :
    1 ≤ E3.mQuot V U := by
  by_contra h
  push Not at h
  exact hne ((E3.mQuot_eq_zero_iff hV hUV).1 (by omega))

@[expose] def E611ComponentCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G), HypE61 T M V → U ∈ gammaE64 V M →
    (∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M) →
    1 < E3.mQuot V U → oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥ →
    IsComponentIn L (Subgroup.centralizer (U : Set G)) →
    ∃ x ∈ M ⊓ Subgroup.centralizer (U : Set G), ∀ j : ℕ,
      x ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ E3.mQuot V U - 1) ∣ j

theorem exists_torus_of_charTwo
    {T M V U K : Subgroup G} (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M)
    (hn : 1 < E3.mQuot V U) (hQK : T ⊓ Subgroup.centralizer (V : Set G) ≤ K)
    (hKU : K ≤ Subgroup.centralizer (U : Set G)) (hK : CharTwo K) (hKM : ¬ K ≤ M) :
    ∃ x ∈ K ⊓ M, ∀ j : ℕ,
      x ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ E3.mQuot V U - 1) ∣ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hQsyl : IsSylowTwoOf Q K := A4.isSylowTwoOf_mono (e6_5_one h hU) hQK hKU
  have hcgs : cgsIn K Q ≤ K ⊓ M := by
    refine le_inf (iSup_le fun C => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      inf_le_left) ?_
    exact (cgsIn_mono hKU).trans ((e6_5_two h hU).1.trans inf_le_right)
  have hO2 : pCoreOf 2 K ≠ ⊥ := by
    intro h0
    apply h.Q_ne_bot
    have h1 := hK
    unfold CharTwo at h1
    rw [h0, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp), inf_top_eq]
      at h1
    exact le_bot_iff.1 (hQK.trans h1)
  have hsq : IsSQTKIn K :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hO2,
      kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2⟩
  obtain ⟨r, Lb, -, hLb, hprod⟩ :=
    H13.VolI.asc129Statement_holds G K Q (K ⊓ M) hsq hK hQsyl hcgs inf_le_left
  obtain ⟨i, hiM⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    apply hKM
    intro k hk
    obtain ⟨m, hm, x, hx, rfl⟩ := hprod k hk
    refine M.mul_mem hm.2 (Subgroup.list_prod_mem (K := M) fun y hy => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    exact hall j (hx j)
  obtain ⟨⟨hL, htype⟩, hBor, hJ⟩ := hLb i
  have hLK : Lb i ≤ K := hL.2.1
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hUC : U ≤ V ⊓ Subgroup.centralizer (Lb i : Set G) :=
    le_inf hU.1 fun u hu => Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_iff.1 (hKU (hLK hl)) u hu).symm
  have hCV : V ⊓ Subgroup.centralizer (Lb i : Set G) = U := by
    by_contra hne
    have hlt : U < V ⊓ Subgroup.centralizer (Lb i : Set G) := lt_of_le_of_ne hUC (Ne.symm hne)
    apply hiM
    refine le_trans (fun l hl => ?_) (hmax _ hlt inf_le_left)
    exact Subgroup.mem_centralizer_iff.2 fun w hw =>
      (Subgroup.mem_centralizer_iff.1 hw.2 l hl).symm
  have hVL : ¬ V ≤ Subgroup.centralizer (Lb i : Set G) := by
    intro hVC
    rw [inf_eq_left.2 hVC] at hCV
    rw [hCV, E3.mQuot_self] at hn
    exact absurd hn (by norm_num)
  have hVQ : V ≤ Q := h.le_inf_centralizer
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_right
  have hKN : K ⊓ M ≤ Subgroup.normalizer (V : Set G) := fun g hg =>
    (e6_5_three h hU).2 ⟨hKU hg.1, hg.2⟩
  rcases htype with ⟨k, hk, hlin⟩ | h3 | h5
  · obtain ⟨hidx, x, hx, hxj⟩ := lin2_block_torus h.isElemAbelian h.le hQsyl
      (inf_le_left.trans h.inM.2) hKN hK hL hk hlin hBor hVL
    rw [hCV, E3.relIndex_eq_two_pow hV2] at hidx
    have hkn : E3.mQuot V U = k := Nat.pow_right_injective (le_refl 2) hidx
    refine ⟨x, hx.2, fun j => ?_⟩
    rw [hkn]
    exact hxj j
  · exfalso
    have h1 := relIndex_le_two_of_alt3 hK hL h3 hQsyl hJ.symm hVQ hQV
    rw [hCV] at h1
    have := mQuot_le_one_of_relIndex_le_two hV2 h1
    omega
  · exfalso
    have h1 := relIndex_le_two_of_alt5 hK hL h5 hQsyl hVQ hQV
    rw [hCV] at h1
    have := mQuot_le_one_of_relIndex_le_two hV2 h1
    omega

theorem e6_11_two
    (hComp : E611ComponentCase) {T M V U : Subgroup G} (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M)
    (hn : 1 < E3.mQuot V U) :
    ∃ x ∈ M ⊓ Subgroup.centralizer (U : Set G), ∀ j : ℕ,
      x ^ j ∈ Subgroup.centralizer (V : Set G) ↔ (2 ^ E3.mQuot V U - 1) ∣ j := by
  have hO : oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥ :=
    oddCoreIn_eq_bot_of_maximal h hU hmax hn
  by_cases hK : CharTwo (Subgroup.centralizer (U : Set G))
  · obtain ⟨x, hx, hxj⟩ :=
      exists_torus_of_charTwo h hU hmax hn (e6_5_one h hU).1 le_rfl hK hU.2.2.1
    exact ⟨x, ⟨hx.2, hx.1⟩, hxj⟩
  · obtain ⟨L, hL⟩ : ∃ L : Subgroup G, IsComponentIn L (Subgroup.centralizer (U : Set G)) := by
      by_contra hno
      push Not at hno
      exact hK (DoubleA3.charTwo_of_no_component hno hO)
    exact hComp G T M V U L h hU hmax hn hO hL

end E6
end CFSG.Quasithin
