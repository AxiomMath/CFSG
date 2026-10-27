module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108Calc
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
public import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem hstar_of_inU (D : Data G) {B : Subgroup G} (hU : UC6.InU D.M B) :
    ∀ g : G, (∀ b ∈ B, g⁻¹ * b * g ∈ D.M) → g ∈ D.M :=
  ((UC6.inU_iff_fixed (UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal)).1 hU).2

theorem exists_minimal_between {M N D₀ : Subgroup G} (hD₀N : D₀ ≤ N) (hNM : ¬ N ≤ M) :
    ∃ H : Subgroup G, D₀ ≤ H ∧ H ≤ N ∧ ¬ H ≤ M ∧
      ∀ H' : Subgroup G, D₀ ≤ H' → H' ≤ H → ¬ H' ≤ M → H' = H := by
  classical
  set S : Set (Subgroup G) := {H | D₀ ≤ H ∧ H ≤ N ∧ ¬ H ≤ M} with hS
  obtain ⟨H, ⟨hD₀H, hHN, hHM⟩, hmin⟩ :=
    Set.exists_min_image S (fun H => Nat.card H) (Set.toFinite S) ⟨N, hD₀N, le_rfl, hNM⟩
  refine ⟨H, hD₀H, hHN, hHM, fun H' hD₀H' hH'H hH'M => ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hH'H (hmin H' ⟨hD₀H', hH'H.trans hHN, hH'M⟩)

theorem exists_minimal_normal_above {H Y : Subgroup G} (hYH : Y < H) :
    ∃ X : Subgroup G, Y < X ∧ X ≤ H ∧ H ≤ normalizer (X : Set G) ∧
      ∀ W : Subgroup G, Y ≤ W → W ≤ X → H ≤ normalizer (W : Set G) → W = Y ∨ W = X := by
  classical
  set S : Set (Subgroup G) := {X | Y < X ∧ X ≤ H ∧ H ≤ normalizer (X : Set G)} with hS
  obtain ⟨X, ⟨hYX, hXH, hXn⟩, hmin⟩ :=
    Set.exists_min_image S (fun X => Nat.card X) (Set.toFinite S) ⟨H, hYH, le_rfl, le_normalizer⟩
  refine ⟨X, hYX, hXH, hXn, fun W hYW hWX hWn => ?_⟩
  by_cases hW : W = Y
  · exact Or.inl hW
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hWX
      (hmin W ⟨lt_of_le_of_ne hYW (Ne.symm hW), hWX.trans hXH, hWn⟩))

theorem le_kerM_of_normal {M H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hKM : K ≤ M) : K ≤ kerM M H := by
  intro k hk
  refine (RankThreeUC.WeakClosure.mem_kerIn (M := M) (H := H)).2 ⟨hKH hk, fun h hh => hKM ?_⟩
  exact (mem_normalizer_iff.1 (hHK hh) k).1 hk

theorem le_normalizer_kerM (M H : Subgroup G) : H ≤ normalizer (kerM M H : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  change x ∈ RankThreeUC.WeakClosure.kerIn M H ↔
    g * x * g⁻¹ ∈ RankThreeUC.WeakClosure.kerIn M H
  simp only [RankThreeUC.WeakClosure.mem_kerIn]
  constructor
  · rintro ⟨hxH, hx⟩
    refine ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), fun h hh => ?_⟩
    have := hx (h * g) (H.mul_mem hh hg)
    simpa [mul_assoc] using this
  · rintro ⟨hxH, hx⟩
    refine ⟨?_, fun h hh => ?_⟩
    · have := H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg
      simpa [mul_assoc] using this
    · have := hx (h * g⁻¹) (H.mul_mem hh (H.inv_mem hg))
      simpa [mul_assoc] using this

theorem inf_kerM_eq_bot {M H B : Subgroup G} {p : ℕ} (hp : p.Prime) (hBp : Nat.card B = p)
    (hBM : B ≤ M) (hBH : B ≤ H) (hstar : ∀ g : G, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M)
    (hHM : ¬ H ≤ M) : B ⊓ kerM M H = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hBY : B ≤ kerM M H := by
    have hcard : Nat.card (B ⊓ kerM M H : Subgroup G) ∣ p :=
      hBp ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hcard with h1 | hp'
    · exact absurd (Subgroup.card_eq_one.1 h1) hne
    · exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge (inf_le_left : B ⊓ kerM M H ≤ B)
        (by rw [hBp, hp']))
  have hYH : kerM M H ≤ H := RankThreeUC.WeakClosure.kerIn_le_left M H
  have hYM : kerM M H ≤ M := RankThreeUC.WeakClosure.kerIn_le_right M H
  have hYn : H ≤ normalizer (kerM M H : Set G) := le_normalizer_kerM M H
  have hBp' : IsPGroup p B := IsPGroup.of_card (n := 1) (by rw [hBp, pow_one])
  obtain ⟨Q, hQ⟩ := (hBp'.comap_subtype (K := kerM M H)).exists_le_sylow
  set P : Subgroup G := (Q : Subgroup (kerM M H)).map (kerM M H).subtype with hPdef
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P (kerM M H) := ⟨Q, rfl⟩
  have hPY : P ≤ kerM M H := Subgroup.map_subtype_le _
  have hBP : B ≤ P := fun b hb => ⟨⟨b, hBY hb⟩, hQ hb, rfl⟩
  have hNP : normalizer (P : Set G) ≤ M :=
    UC22.F10.k108Star_normalizer_le hstar hBP (hPY.trans hYM)
  apply hHM
  have hfr := CFSG.LocalAnalysis.RankThreeUC.le_sup_inf_normalizer_of_isSylowOf hYH hYn hPsyl
  exact hfr.trans (sup_le hYM (inf_le_right.trans hNP))

theorem mem_kerM_of_forall_commutator_mem {M H X : Subgroup G}
    (hXn : H ≤ normalizer (X : Set G)) (hHMX : H ≤ (H ⊓ M) ⊔ X) {c : G} (hcH : c ∈ H)
    (hcM : c ∈ M) (hc : ∀ x ∈ X, ⁅x, c⁆ ∈ kerM M H) : c ∈ kerM M H := by
  have hYM : kerM M H ≤ M := RankThreeUC.WeakClosure.kerIn_le_right M H
  refine (RankThreeUC.WeakClosure.mem_kerIn (M := M) (H := H)).2 ⟨hcH, fun h hh => ?_⟩
  have hmem : h ∈ ((H ⊓ M : Subgroup G) : Set G) * (X : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hXn)]
    exact hHMX hh
  obtain ⟨d, hd, x, hx, rfl⟩ := hmem
  have hdM : d ∈ M := (Subgroup.mem_inf.1 hd).2
  have hxc : x * c * x⁻¹ ∈ M := by
    have e : x * c * x⁻¹ = ⁅x, c⁆ * c := by rw [commutatorElement_def]; group
    rw [e]
    exact M.mul_mem (hYM (hc x hx)) hcM
  have e2 : d * x * c * (d * x)⁻¹ = d * (x * c * x⁻¹) * d⁻¹ := by group
  rw [e2]
  exact M.mul_mem (M.mul_mem hdM hxc) (M.inv_mem hdM)

theorem exists_calMOf_ne_of_r6_40_2 (D : Data G) (h640 : UC6.R6_40_2 D) {B : Subgroup G}
    (hB : B ≤ normalizer (D.T : Set G)) :
    ∃ N : Subgroup G, N ∈ calMOf (B ⊔ D.T) ∧ N ≠ D.M := by
  by_contra hcon
  push Not at hcon
  have hle : UC6.calCGS D.T ≤ D.M :=
    uc22p22p_calCGS_le_of_normalizes D le_rfl (sup_le hB le_normalizer) fun H hH hRH => by
      obtain ⟨N, hN, hHN⟩ := uc22p22p_exists_max_ge hH
      exact hHN.trans (le_of_eq (hcon N ⟨hN, hRH.trans hHN⟩))
  have := D.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
    (top_le_iff.1 (h640.1 ▸ hle))

theorem not_invertedIn_of_commutator_le {H T B Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T H) (hBH : B ≤ H)
    (hBp : Nat.card B = p) (hYn : H ≤ normalizer (Y : Set G)) (hBY : B ⊓ Y = ⊥)
    (hR : ⁅T, B⁆ ≤ Y) : ¬ UC22.F05.InvertedIn H B := by
  classical
  intro hInv
  obtain ⟨g, hgH, hg⟩ := hInv
  obtain ⟨m, a, hga, hgBpow⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne.exists_two_element_inverting
      hg
  set g₂ : G := g ^ m with hg₂
  have hg₂H : g₂ ∈ H := by
    rw [hg₂]
    exact H.pow_mem hgH m
  have hg₂F : ∀ b ∈ B, g₂ * b * g₂⁻¹ = b⁻¹ := by
    intro b hb
    rw [hg₂]
    exact hgBpow b hb
  have hg₂I : ∀ b ∈ B, g₂⁻¹ * b * g₂ = b⁻¹ := by
    intro b hb
    have h := hg₂F b hb
    have h' : b = g₂⁻¹ * b⁻¹ * g₂ := by
      calc b = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by group
        _ = g₂⁻¹ * b⁻¹ * g₂ := by rw [h]
    calc g₂⁻¹ * b * g₂ = (g₂⁻¹ * b⁻¹ * g₂)⁻¹ := by group
      _ = b⁻¹ := by rw [← h']
  let K : Subgroup G :=
    { carrier := {x : G | x ∈ H ∧ ∀ b ∈ B, ⁅x, b⁆ ∈ Y}
      one_mem' := by
        refine ⟨H.one_mem, fun b hb => ?_⟩
        simp
      mul_mem' := by
        rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨H.mul_mem hxH hyH, fun b hb => ?_⟩
        have hcomm : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
          simp only [commutatorElement_def]
          group
        rw [hcomm]
        exact Y.mul_mem ((Subgroup.mem_normalizer_iff.1 (hYn hxH) ⁅y, b⁆).1 (hy b hb))
          (hx b hb)
      inv_mem' := by
        rintro x ⟨hxH, hx⟩
        refine ⟨H.inv_mem hxH, fun b hb => ?_⟩
        have hcomm : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        rw [hcomm]
        have h := (Subgroup.mem_normalizer_iff.1 (hYn (H.inv_mem hxH)) ⁅x, b⁆⁻¹).1
          (Y.inv_mem (hx b hb))
        simpa using h }
  have hKleH : K ≤ H := fun x hx => hx.1
  have hTK : T ≤ K := by
    intro t ht
    exact ⟨hTsyl.le ht, fun b hb => hR (Subgroup.commutator_mem_commutator ht hb)⟩
  have hconj : ∀ u : G, u ∈ H → (∀ b ∈ B, u * b * u⁻¹ = b⁻¹) →
      (∀ b ∈ B, u⁻¹ * b * u = b⁻¹) → ∀ x ∈ K, u * x * u⁻¹ ∈ K := by
    intro u huH huF huI x hx
    obtain ⟨hxH, hxY⟩ := hx
    refine ⟨H.mul_mem (H.mul_mem huH hxH) (H.inv_mem huH), fun b hb => ?_⟩
    have hcomm : u * ⁅x, u⁻¹ * b * u⁆ * u⁻¹ = ⁅u * x * u⁻¹, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [← hcomm]
    exact (Subgroup.mem_normalizer_iff.1 (hYn huH) ⁅x, u⁻¹ * b * u⁆).1
      (hxY _ (by rw [huI b hb]; exact B.inv_mem hb))
  have hconj_inv : ∀ u : G, u ∈ H → (∀ b ∈ B, u * b * u⁻¹ = b⁻¹) →
      (∀ b ∈ B, u⁻¹ * b * u = b⁻¹) → ∀ x ∈ K, u⁻¹ * x * u ∈ K := by
    intro u huH huF huI x hx
    have huI' : ∀ b ∈ B, u⁻¹ * b * (u⁻¹)⁻¹ = b⁻¹ := by
      intro b hb
      simpa using huI b hb
    have huF' : ∀ b ∈ B, (u⁻¹)⁻¹ * b * u⁻¹ = b⁻¹ := by
      intro b hb
      simpa using huF b hb
    simpa using hconj u⁻¹ (H.inv_mem huH) huI' huF' x hx
  have hg₂norm : g₂ ∈ normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj g₂ hg₂H hg₂F hg₂I x
    · intro hx
      have hx' := hconj_inv g₂ hg₂H hg₂F hg₂I (g₂ * x * g₂⁻¹) hx
      have hxeq : g₂⁻¹ * (g₂ * x * g₂⁻¹) * g₂ = x := by group
      rwa [hxeq] at hx'
  have hzp : Subgroup.zpowers g₂ ≤ normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hg₂norm
  let L : Subgroup G := K ⊔ Subgroup.zpowers g₂
  have hKL : K ≤ L := le_sup_left
  have hZL : Subgroup.zpowers g₂ ≤ L := le_sup_right
  have hLH : L ≤ H := sup_le hKleH (Subgroup.zpowers_le.mpr hg₂H)
  have hLN : L ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hzp
  have hTsylL : CFSG.ABGLocalTools.IsSylowOf 2 T L := hTsyl.of_le (hTK.trans hKL) hLH
  have hg₂2 : IsPGroup 2 (Subgroup.zpowers g₂) := by
    have hdvd : orderOf g₂ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hga
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := c) (by rw [Nat.card_zpowers, hc])
  have hzp2L : IsPGroup 2 ((Subgroup.zpowers g₂).subgroupOf L) := hg₂2.comap_subtype
  obtain ⟨S, hSle⟩ := hzp2L.exists_le_sylow
  let Sg : Subgroup G := (S : Subgroup L).map L.subtype
  have hSg : CFSG.ABGLocalTools.IsSylowOf 2 Sg L := ⟨S, rfl⟩
  have hg₂L : g₂ ∈ L := hZL (Subgroup.mem_zpowers g₂)
  have hg₂Sg : g₂ ∈ Sg := by
    refine ⟨⟨g₂, hg₂L⟩, ?_, rfl⟩
    exact hSle (Subgroup.mem_zpowers g₂)
  obtain ⟨k, hkL, hkconj⟩ := hTsylL.exists_mem_conj hSg
  have hkg₂ : k⁻¹ * g₂ * k ∈ T := (hkconj g₂).1 hg₂Sg
  have hg₂K : g₂ ∈ K := by
    have hxk : k ∈ normalizer (K : Set G) := hLN hkL
    have hxK : k * (k⁻¹ * g₂ * k) * k⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 hxk (k⁻¹ * g₂ * k)).1 (hTK hkg₂)
    have hxeq : k * (k⁻¹ * g₂ * k) * k⁻¹ = g₂ := by group
    rwa [hxeq] at hxK
  have hBne : B ≠ ⊥ := by
    intro hbot
    have hp1 : p = 1 := by rw [← hBp, hbot, Subgroup.card_bot]
    exact hp.ne_one hp1
  have : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  obtain ⟨b, hbB, hbne⟩ := Subgroup.exists_ne_one_of_nontrivial B
  have hby : b⁻¹ * b⁻¹ ∈ Y := by
    have hcomm : ⁅g₂, b⁆ = b⁻¹ * b⁻¹ := by
      rw [commutatorElement_def, hg₂F b hbB]
    have := hg₂K.2 b hbB
    rwa [hcomm] at this
  have hbyB : b⁻¹ * b⁻¹ ∈ B :=
    B.mul_mem (B.inv_mem hbB) (B.inv_mem hbB)
  have hbot : b⁻¹ * b⁻¹ = 1 := by
    have hmem : b⁻¹ * b⁻¹ ∈ B ⊓ Y := ⟨hbyB, hby⟩
    rwa [hBY, Subgroup.mem_bot] at hmem
  have hb2 : b ^ 2 = 1 := by
    have h := congrArg (fun z : G => b * z * b) hbot
    simpa [pow_two, mul_assoc] using h.symm
  have hdvd2 : orderOf b ∣ 2 := by
    simpa [pow_two] using orderOf_dvd_of_pow_eq_one hb2
  have hdvdp : orderOf b ∣ p := by
    rw [← hBp]
    exact Subgroup.orderOf_dvd_natCard B hbB
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
  · exact hbne (orderOf_eq_one_iff.mp h1)
  · have h2p : 2 ∣ p := h2 ▸ hdvdp
    rcases (Nat.dvd_prime hp).1 h2p with h21 | h2p'
    · norm_num at h21
    · exact hp2 h2p'.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
