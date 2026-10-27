module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyUn
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim81 CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped commutatorElement Matrix

@[expose] def UnitaryRootAt {G : Type} [Group G] (M Q Z Z0 : Subgroup G)
    [(Q.subgroupOf M).Normal] (m : ℕ) : Prop :=
  ∃ f : ℕ, ∃ hf : 2 ≤ f, Nat.card Z = 2 ^ f ∧ ∃ hm : 4 ≤ m,
    ∃ Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* Hbar M Q Z,
      Φ.ker = Subgroup.center _ ∧
      ∃ x, (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) =
        (conjSub ((Unitary.rootDatum (card_galoisField_two_mul (by omega : 1 ≤ f)) m).rootGroup
          (unitaryLongRoot m (by omega))) x).map Φ

@[expose] def Tim81StrothUnRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0 →
    ∀ k : ℕ, Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k →
    (∃ m : ℕ, 2 * m - 3 = k ∧
      IsPSUModel m (Nat.card Z) ↥(generalizedFitting ↥(bar M Q (H0 M Z))) ∧
      UnitaryRootAt M Q Z Z0 m) ∨
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0

theorem tim81StrothUn_of_root (h : Tim81StrothUnRootStatement) : Tim81StrothUnStatement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0 hMA hElt hF hNL k hk
  rcases h G M Q Z B hc n t hs Z0 hZ0 hMA hElt hF hNL k hk with ⟨m, hmk, hU, -⟩ | hconj
  · exact Or.inl ⟨m, hmk, hU⟩
  · exact Or.inr hconj

@[expose] def Sec716NoLargeUnitaryRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ∀ m : ℕ, 6 < m → Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * m - 3) →
    ¬ UnitaryRootAt M Q Z Z0 m

@[expose] def Tim81StrothSpUnRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0 →
    ∀ k : ℕ, Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k →
    (∃ m : ℕ, 2 * m - 3 = k ∧
      IsPSUModel m (Nat.card Z) ↥(generalizedFitting ↥(bar M Q (H0 M Z))) ∧
      UnitaryRootAt M Q Z Z0 m) ∨
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0

@[expose] def Sec86NoLargeUnitaryRootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ∀ m : ℕ, 6 < m → Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (2 * m - 3) →
    ¬ UnitaryRootAt M Q Z Z0 m

theorem tim81StrothSp_of_root (h : Tim81StrothSpUnRootStatement)
    (hEx : Sec86NoLargeUnitaryRootStatement) (h83 : Stroth83Statement)
    (hirr : Sec86IrredStatement) : Tim81StrothSpStatement := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0 hMA hElt hF hNL
  rcases h83 G M Q Z B hc n t hs.toSec5 hs.sp with ⟨-, -, hN⟩ | ⟨-, -, hN⟩
  · rcases h G M Q Z B hc n t hs Z0 hZ0 hMA hElt hF hNL 9 hN with ⟨m, hm9, hU, -⟩ | hconj
    · have hm6 : m = 6 := by omega
      subst hm6
      exact Or.inl hU
    · exact Or.inr hconj
  · rcases h G M Q Z B hc n t hs Z0 hZ0 hMA hElt hF hNL 17 hN with ⟨m, hm17, -, hR⟩ | hconj
    · exact absurd hR (hEx G M Q Z B hc n t hs Z0 hZ0 (hirr G M Q Z B hc n t hs Z0 hZ0) hF m
        (by omega) (by rw [hm17]; exact hN))
    · exact Or.inr hconj

theorem stroth716Type_of_inputs_root (h78 : Stroth78Statement) (h79 : Stroth79Statement)
    (h711S : Stroth711StrongStatement) (h713 : Stroth713Statement)
    (h714 : Stroth714Statement) (h715 : Stroth715Statement) (hSign : OmegaSignStatement)
    (hNR : Sec7NormZ0Statement) (hZV : Sec7ZVStatement)
    (hNL : Sec7NormLB'Statement)
    (h27 : Tim81StrothUnRootStatement) (hEx : Sec716NoLargeUnitaryRootStatement)
    (hSub : Step7HypSub'Statement) : Stroth716TypeStatement := by
  have hMax := step716MaxAb_holds
  intro G _ _ M Q Z B _ hc n t h5 hlarge htype
  have hs : Sec7Hyp hc n t := by
    refine ⟨h5, ?_, ?_, hlarge⟩
    · intro hp2
      rcases htype with ⟨m, hm, hp⟩ | ⟨m, hm, hmn⟩
      · have := hp.eq_of_plus hp2
        omega
      · have h2 : 2 = m := omegaPlusNat_eq_omegaMinusNat (by omega) hp2 hmn
        subst h2
        exact hSign G M Q Z B hc t 2 le_rfl hp2 hmn
    · rcases htype with ⟨m, hm, hp⟩ | ⟨m, hm, hmn⟩
      · exact ⟨m, by omega, Or.inl hp⟩
      · exact ⟨m, hm, Or.inr hmn⟩
  have gen : ∀ k : ℕ, Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k →
      ((k = 9 ∧ OmegaMinusNat hc t 3) ∨ k = 17 ∨ k = 33) →
      ¬ OmegaMinusNat hc t 2 → ¬ OmegaPlusNat hc t 3 → ¬ OmegaPlusNat hc t 4 →
      SubConfig M Q Z (hc.CN t) ∨ (OmegaMinusNat hc t 3 ∧ FStarU6 M Q Z) := by
    intro k hk hkc hnom hn3 hn4
    rcases h79 G M Q Z B hc n t h5 hlarge hs.notPlus4 hs.orth with ⟨Z0, hZ0, hirr⟩ | h3 | ⟨h4, -⟩
    · have hN' := h711S G M Q Z B hc n t hs
      have hF := h713 G M Q Z B hc n t hs hn4 Z0 hZ0
      have hTI := Z0_normalizes_of_nat hNR hZV G M Q Z B hc n t hs hnom Z0 hZ0
      have hMA := hMax G M Q Z B hc n t hs Z0 hZ0 hirr hN' hF
      rcases h27 G M Q Z B hc n t hs Z0 hZ0 hMA hTI hF
          (hNL G M Q Z B hc n t hs Z0 hZ0 hMA hTI hF) k hk with
        ⟨m, hmk, hU, hR⟩ | ⟨g, hg, hle, hne⟩
      · rcases hkc with ⟨rfl, hm3⟩ | rfl | rfl
        · have hm6 : m = 6 := by omega
          subst hm6
          exact Or.inr ⟨hm3, hU⟩
        · exact absurd hR
            (hEx G M Q Z B hc n t hs Z0 hZ0 hirr hF m (by omega) (by rw [hmk]; exact hk))
        · exact absurd hR
            (hEx G M Q Z B hc n t hs Z0 hZ0 hirr hF m (by omega) (by rw [hmk]; exact hk))
      · exact Or.inl (hSub G M Q Z B hc n t hs Z0 hZ0 hMA hTI hF
          (invAbelian_of_irred hc hZ0 hirr) ⟨g, hg, hle, hne⟩).subConfig
    · exact absurd h3 hn3
    · exact absurd h4 hn4
  rcases htype with ⟨m, hm, hp⟩ | ⟨m, hm, hmn⟩
  · rcases h78 G M Q Z B hc n t h5 hlarge hs.notPlus4 m (by omega) (Or.inl hp) with
      ⟨h, -⟩ | ⟨h4, h16, -⟩ | ⟨h4, -, h12, -⟩ | ⟨h5', -, -, hN⟩ | ⟨h6, -, -, hN⟩
    · omega
    · subst h4
      exact Or.inl (h715 G M Q Z B hc n t hs hp)
    · subst h4
      have := h714 G M Q Z B hc n t hs hp
      omega
    · subst h5'
      exact gen 17 hN (Or.inr (Or.inl rfl))
        (fun h2 => by have := omegaPlusNat_eq_omegaMinusNat (by norm_num) hp h2; omega)
        (fun h3 => by have := hp.eq_of_plus h3; omega)
        (fun h4 => by have := hp.eq_of_plus h4; omega)
    · subst h6
      exact gen 33 hN (Or.inr (Or.inr rfl))
        (fun h2 => by have := omegaPlusNat_eq_omegaMinusNat (by norm_num) hp h2; omega)
        (fun h3 => by have := hp.eq_of_plus h3; omega)
        (fun h4 => by have := hp.eq_of_plus h4; omega)
  · rcases h78 G M Q Z B hc n t h5 hlarge hs.notPlus4 m hm (Or.inr hmn) with
      ⟨h3, -, hN⟩ | ⟨h4, -, hN⟩ | ⟨h4, hp, -⟩ | ⟨h5', hp, -⟩ | ⟨h6, hp, -⟩
    · subst h3
      exact gen 9 hN (Or.inl ⟨rfl, hmn⟩)
        (fun h2 => by have := OmegaMinusNat.eq_of_minus (by norm_num) (by norm_num) hmn h2
                      omega)
        (fun h3 => (hSign G M Q Z B hc t 3 (by norm_num) h3 hmn).elim)
        (fun h4 => by have := omegaPlusNat_eq_omegaMinusNat (by norm_num) h4 hmn; omega)
    · subst h4
      exact gen 17 hN (Or.inr (Or.inl rfl))
        (fun h2 => by have := OmegaMinusNat.eq_of_minus (by norm_num) (by norm_num) hmn h2
                      omega)
        (fun h3 => by have := omegaPlusNat_eq_omegaMinusNat (by norm_num) h3 hmn; omega)
        (fun h4 => (hSign G M Q Z B hc t 4 (by norm_num) h4 hmn).elim)
    · subst h4
      exact (hSign G M Q Z B hc t 4 (by norm_num) hp hmn).elim
    · subst h5'
      exact (hSign G M Q Z B hc t 5 (by norm_num) hp hmn).elim
    · subst h6
      exact (hSign G M Q Z B hc t 6 (by norm_num) hp hmn).elim

theorem stroth717_of_cases_root (h78 : Stroth78Statement) (hA : Step717CaseAStatement)
    (hInv : Sec717InvStatement)
    (hNU : Step717NotUnitaryStatement) (h711S : Stroth711StrongStatement)
    (h713 : Stroth713Statement) (hNR : Sec7NormZ0Statement)
    (hZV : Sec7ZVStatement) (hNL : Sec7NormLB'Statement) (h27 : Tim81StrothUnRootStatement)
    (hSub : Step7HypSub'Statement) : Stroth717Statement :=
  stroth717_of_cases_un h78 hA hInv hNU h711S h713 hNR hZV hNL (tim81StrothUn_of_root h27) hSub

end CFSG.RankThree.GF2n.Stroth80
