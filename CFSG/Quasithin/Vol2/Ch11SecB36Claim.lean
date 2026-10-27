module

public import CFSG.Quasithin.Vol2.Ch11SecB36Sym

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem claim36 (hFV : FactsVM) (hPT : FactPointTrans) (hyp : Hyp11 G T L I n)
    {V₁ V₂ : Subgroup G} (hfl : Flag36 L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n)
    (hs : E3.sParam hfl.elemW = 2 * n)
    (hV3 : (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex (fsuV T I) = 2 ^ (3 * n))
    (hNV₁ : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G))
    {y : G} (hBT : conjSubgroup (VM T L I) y ≤ T)
    (hnc : ⁅VM T L I, conjSubgroup (VM T L I) y⁆ ≠ ⊥)
    (hWN : VM T L I ≤ Subgroup.normalizer (conjSubgroup (VM T L I) y : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hfl.two_le
  have hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (VM T L I : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hfl.T_le_W
  obtain ⟨k, hkT, hnck, -, hky⟩ :=
    exists_sym_gen hTS (B2F.isPGroup_of_isElemAbelian hfl.elemW) hBT hnc hWN
  have hrank := hFV.offender G L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n hfl _ hkT
    (E3.isElemAbelian_conjSubgroup hfl.elemW k) (aSet_VM hfl hs hkT hnck)
  have hcV := hfl.cV
  have hi2 := hfl.index₂
  set V := fsuV T I with hVdef
  set W := VM T L I with hWdef
  set B := conjSubgroup W y with hBdef
  have hmWB : E3.mQuot W (W ⊓ Subgroup.centralizer (B : Set G)) = 2 * n := by
    have := E3.mQuot_conjSubgroup (conjSubgroup W k)
      (conjSubgroup W k ⊓ Subgroup.centralizer (W : Set G)) k⁻¹
    rw [conjSubgroup_inf_centralizer, E3.conjSubgroup_conj_inv, hky, hrank] at this
    exact this
  obtain ⟨hCVB, hvB, hstab⟩ := hFV.r2 G L V W ⊤ T V₁ V₂ n hfl B hBT
    (E3.isElemAbelian_conjSubgroup hfl.elemW y) (aSet_VM hfl hs hBT hnc) hmWB
  rw [hcV] at hi2
  obtain ⟨v₀, hv₀V, hv₀2⟩ : ∃ v ∈ V, v ∉ V₂ := by
    by_contra hall
    push Not at hall
    have hVV2 : V₂ = V := le_antisymm hfl.le₂ hall
    rw [hVV2, ← hcV, hV3] at hi2
    have h2 : 3 * n = n * 2 := Nat.pow_right_injective (le_refl 2) hi2
    omega
  have hV2B : V₂ ≤ B := by
    rw [← hvB v₀ hv₀V hv₀2]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp
      (Subgroup.zpowers_le.mpr (hWN (hfl.le_W hv₀V)))
  have hVB : ⁅V, B⁆ ≠ ⊥ := by
    intro h0
    have hle : ⁅Subgroup.zpowers v₀, B⁆ ≤ ⁅V, B⁆ :=
      Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hv₀V) le_rfl
    rw [h0, hvB v₀ hv₀V hv₀2, le_bot_iff] at hle
    rw [hle, Subgroup.relIndex_self] at hi2
    have := Nat.one_lt_two_pow (by omega : n * 2 ≠ 0)
    omega
  have hMW : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_conjClosure _ _
  obtain ⟨m, hm, hm1⟩ : ∃ m ∈ Subgroup.normalizer (L : Set G),
      ⁅V, conjSubgroup V (m * y)⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hVB
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have h1 : W ≤ conjSubgroup (Subgroup.centralizer (V : Set G)) y⁻¹ := by
      refine conjClosure_le fun m hm v hv => ?_
      rw [E3.mem_conjSubgroup_inv_iff]
      have h2 := hall m⁻¹ (Subgroup.inv_mem _ hm)
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h2
      apply h2
      rw [mem_conjSubgroup_iff]
      convert hv using 1
      group
    have := E3.conjSubgroup_mono_left y h1
    rwa [E3.conjSubgroup_inv_conj] at this
  set y' := m * y with hy'def
  have hBy' : conjSubgroup W y' = B := by
    rw [hy'def, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr (hMW hm)]
  have hVy'B : conjSubgroup V y' ≤ B := hBy' ▸ E3.conjSubgroup_mono_left y' hfl.le_W
  set P := ⁅V, conjSubgroup V y'⁆ with hPdef
  have hPst := hstab _ hVy'B
  have hPV : P ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((hVy'B.trans hBT).trans hfl.T_le_V)
  have hWy' : conjSubgroup B y'⁻¹ = W := by rw [← hBy', E3.conjSubgroup_conj_inv]
  set E := conjSubgroup V y'⁻¹ with hEdef
  have hEN : E ≤ ⊤ ⊓ Subgroup.normalizer (W : Set G) := by
    refine le_inf le_top ?_
    have := E3.conjSubgroup_mono_left y'⁻¹ (hfl.le_W.trans hWN)
    rwa [E3.conjSubgroup_normalizer, hWy'] at this
  have hP'W : conjSubgroup V₂ y'⁻¹ ≤ W := by
    rw [← hWy']
    exact E3.conjSubgroup_mono_left _ hV2B
  have hP'm : E3.mQuot (conjSubgroup V₂ y'⁻¹) ⊥ = 2 * n := by
    have := E3.mQuot_conjSubgroup V₂ ⊥ y'⁻¹
    rw [E3.conjSubgroup_bot] at this
    rw [this]
    unfold E3.mQuot
    rw [hi2, padicValNat.prime_pow]
    ring
  have hEcomm : ∀ e ∈ E, e ∉ Subgroup.centralizer (W : Set G) →
      ⁅Subgroup.zpowers e, W⁆ = conjSubgroup V₂ y'⁻¹ := by
    intro e he heC
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ V, e = y' * v * y'⁻¹ :=
      ⟨y'⁻¹ * e * y', E3.mem_conjSubgroup_inv_iff.mp he, by group⟩
    have hv2 : v ∉ V₂ := by
      intro hv2
      apply heC
      have hvC : v ∈ V ⊓ Subgroup.centralizer (B : Set G) := by
        rw [hCVB]
        exact hv2
      have : y' * v * y'⁻¹ ∈ conjSubgroup (Subgroup.centralizer (B : Set G)) y'⁻¹ := by
        rw [E3.mem_conjSubgroup_inv_iff]
        simpa [mul_assoc] using hvC.2
      rwa [E3.conjSubgroup_centralizer, hWy'] at this
    have h1 : conjSubgroup ⁅Subgroup.zpowers v, B⁆ y'⁻¹ =
        ⁅Subgroup.zpowers (y' * v * y'⁻¹), W⁆ := by
      rw [E3.conjSubgroup_commutator, conjSubgroup_zpowers, hWy', inv_inv]
    rw [← h1, hvB v hv hv2]
  have hRE := hFV.rootElt G L V W ⊤ T V₁ V₂ n hfl E hEN
    (E3.isElemAbelian_conjSubgroup hfl.elem _) _ hP'W hP'm hEcomm
  have hVE : ⁅V, E⁆ = conjSubgroup P y'⁻¹ := by
    rw [hPdef, E3.conjSubgroup_commutator, E3.conjSubgroup_conj_inv, Subgroup.commutator_comm]
  have hVE1 : ⁅V, E⁆ ≠ ⊥ := by
    rw [hVE]
    exact fun h => hm1 (conjSubgroup_eq_bot_iff.mp h)
  obtain ⟨hVEV, hVEst, hVEidx⟩ := hRE.resolve_left hVE1
  have hcard : Nat.card ↥P = 2 ^ n := by
    rw [← E3.card_conjSubgroup P y'⁻¹, ← hVE, ← Subgroup.relIndex_bot_left, ← hcV, hVEidx]
  have hPidx : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex P = 2 ^ n := by
    rw [hcV, Subgroup.relIndex_bot_left, hcard]
  obtain ⟨l, hl, hlP⟩ := hPT G L V ⊤ T V₁ V₂ n hfl.toFlag24 P (by rw [hcV]; exact bot_le)
    hPV hPst hPidx
  obtain ⟨l', hl', hl'E⟩ := hPT G L V ⊤ T V₁ V₂ n hfl.toFlag24 ⁅V, E⁆
    (by rw [hcV]; exact bot_le) hVEV hVEst hVEidx
  have hPV1 : conjSubgroup V₁ l⁻¹ = P := by rw [← hlP, E3.conjSubgroup_conj_inv]
  have hP2 : conjSubgroup P (y'⁻¹ * l') = V₁ := by
    rw [← conjSubgroup_conjSubgroup, ← hVE, hl'E]
  have hx : conjSubgroup V₁ (l⁻¹ * (y'⁻¹ * l')) = V₁ := by
    rw [← conjSubgroup_conjSubgroup, hPV1, hP2]
  have hxN : l⁻¹ * (y'⁻¹ * l') ∈ Subgroup.normalizer (V : Set G) :=
    hNV₁ (conjSubgroup_eq_iff_mem_normalizer.mp hx)
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := hfl.le_normalizer hl
  have hl'N : l' ∈ Subgroup.normalizer (V : Set G) := hfl.le_normalizer hl'
  have hyN : y'⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    have e : y'⁻¹ = l * (l⁻¹ * (y'⁻¹ * l')) * l'⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hxN) (Subgroup.inv_mem _ hl'N)
  have hVy : conjSubgroup V y' = V := by
    have := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.inv_mem _ hyN)
    rwa [inv_inv] at this
  apply hm1
  rw [hPdef, hVy, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact B2F.isElemAbelian_comm hfl.elem hw hv

end CFSG.Quasithin.Vol2.Ch11.SecB
