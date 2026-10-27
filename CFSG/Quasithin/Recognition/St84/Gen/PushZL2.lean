module

public import CFSG.Quasithin.Recognition.St84.PushUp

import CFSG.Quasithin.Recognition.St84.Gen.NatL2
import CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.Arithmetic

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Push

variable {G : Type} [Group G] {X P A : Subgroup G} {n : ℕ}

section Finite

variable [Finite G]

theorem isSylowTwoOf_ne_bot_L2 (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) : P ≠ ⊥ := by
  intro hbot
  have hXodd : ¬ 2 ∣ Nat.card X := by
    have h := hP.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    exact h
  obtain ⟨e⟩ := hquot
  have hq2 : 2 ∣ Nat.card (oTwoQuot ↥X) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.NearModels.PSLTwo.two_dvd_natCard_psl2 _
  exact hXodd (hq2.trans (Subgroup.card_quotient_dvd_card _))

theorem pushZ_ne_bot_L2 (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) : pushZ X P ≠ ⊥ := by
  intro hbot
  have hle : omegaOneCenterOf P ≤ pushZ X P := le_conjClosure _ _
  rw [hbot] at hle
  exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP.2.1
    (isSylowTwoOf_ne_bot_L2 hquot hP) (le_bot_iff.mp hle)

theorem pushZ_centralizer_eq_L2 (hn : 1 ≤ n) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X)) (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) :
    X ⊓ Subgroup.centralizer (pushZ X P : Set G) = pCoreOf 2 X := by
  rcases eq_or_lt_of_le hn with h1 | hgt
  · exact pushZ_centralizer_eq (Or.inl h1.symm) hchar hquot hP hnc
  have hn2 : 2 ≤ n := by omega
  have hPne : P ≠ ⊥ := isSylowTwoOf_ne_bot_L2 hquot hP
  obtain ⟨e⟩ := hquot
  have hcardF : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  haveI : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  haveI : IsSimpleGroup (oTwoQuot ↥X) := e.isSimpleGroup
  set K : Subgroup G := X ⊓ Subgroup.centralizer (pushZ X P : Set G) with hKdef
  have hKleX : K ≤ X := hKdef ▸ inf_le_left
  have hOle : pCoreOf 2 X ≤ K := by
    rw [hKdef]
    refine le_inf ?_ ?_
    · rintro x ⟨y, -, rfl⟩; exact y.2
    exact fun o ho => Subgroup.mem_centralizer_iff.mpr fun z hz =>
      ((Subgroup.mem_centralizer_iff.mp
        ((pushZ_le_centerOf_pCoreOf hchar hP).1 hz).2) o ho).symm
  refine le_antisymm ?_ hOle
  by_contra hcon
  have hKnorm : X ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKdef]
    exact A1a.le_normalizer_inf Subgroup.le_normalizer
      (A1a.le_normalizer_centralizer (le_normalizer_pushZ X P))
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleX).mpr hKnorm
  let π : ↥X →* oTwoQuot X := QuotientGroup.mk' (pCore 2 ↥X)
  let QK : Subgroup (oTwoQuot X) := (K.subgroupOf X).map π
  have hQKn : QK.Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  haveI : QK.Normal := hQKn
  have hcore_le : pCore 2 ↥X ≤ K.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hOle ⟨y, hy, rfl⟩)
  have hpre : ∀ y : ↥X, π y ∈ QK ↔ y ∈ K.subgroupOf X := by
    intro y
    constructor
    · rintro ⟨k, hk, hkπ⟩
      have h1 : k⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkπ]
        simp
      have h2 : k⁻¹ * y ∈ pCore 2 ↥X := by
        rwa [QuotientGroup.ker_mk'] at h1
      have h3 := hcore_le h2
      simpa using (K.subgroupOf X).mul_mem hk h3
    · intro hy
      exact ⟨y, hy, rfl⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top QK with hbot | htop
  · apply hcon
    intro x hx
    have hxX : x ∈ X := hKleX hx
    have hxK' : (⟨x, hxX⟩ : ↥X) ∈ K.subgroupOf X := hx
    have h1 : π ⟨x, hxX⟩ ∈ QK := Subgroup.mem_map_of_mem π hxK'
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxX⟩ : ↥X) ∈ pCore 2 ↥X := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥X), MonoidHom.mem_ker]
      exact h1
    exact ⟨⟨x, hxX⟩, h2, rfl⟩
  · have hXK : X ≤ K := by
      intro x hx
      have h1 : π ⟨x, hx⟩ ∈ QK := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (hpre ⟨x, hx⟩).mp h1
    have hXcent : X ≤ Subgroup.centralizer (omegaOneCenterOf P : Set G) := by
      intro x hx
      have hxK : x ∈ K := hXK hx
      exact Subgroup.mem_centralizer_iff.mpr fun z hz =>
        Subgroup.mem_centralizer_iff.mp hxK.2 z (le_conjClosure _ _ hz)
    exact hnc (omegaOneCenterOf P) (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le P)
      (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hP.2.1 hPne)
      (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf P)
      (hXcent.trans (Subgroup.centralizer_le_normalizer _))

theorem pushHyp_pushZ_L2 (hn : 1 ≤ n) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X)) (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) :
    PushHyp X P (pushZ X P) where
  sylow := hP
  normal := le_normalizer_pushZ X P
  elemAbelian := (pushZ_le_centerOf_pCoreOf hchar hP).2
  le_core := pushZ_le_pCoreOf hchar hP
  cent_eq := pushZ_centralizer_eq_L2 hn hchar hquot hP hnc

theorem not_thompsonJ_le_pCoreOf_L2 (hquot : IsL2Quot n (oTwoQuot ↥X))
    (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) : ¬ thompsonJ P ≤ pCoreOf 2 X := by
  intro hJ
  have hPne : P ≠ ⊥ := isSylowTwoOf_ne_bot_L2 hquot hP
  have hle : pCoreOf 2 X ≤ P := pCoreOf_le_of_isSylowTwoOf hP
  have heq : thompsonJ (pCoreOf 2 X) = thompsonJ P :=
    CFSG.QuasithinUnique.GammaExtra.thompsonJ_eq_of_le hJ hle
  have hN : X ≤ Subgroup.normalizer (thompsonJ P : Set G) := by
    rw [← heq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
      (normalizer_le_normalizer_thompsonJ (pCoreOf 2 X))
  exact hnc (thompsonJ P) (CFSG.Quasithin.B6.thompsonJ_le P)
    (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hP.2.1 hPne)
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ P) hN

theorem baumannC_pushZ_L2 (hn : 1 ≤ n) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X)) (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X) :
    BaumannC X (pushZ X P) := by
  rcases eq_or_lt_of_le hn with h1 | hgt
  · exact baumannC_pushZ (Or.inl h1.symm) hchar hquot hP hnc
  have hn2 : 2 ≤ n := by omega
  exact baumannC_of_isL2Quot (pushHyp_pushZ_L2 hn hchar hquot hP hnc) hn2 hquot
    (not_thompsonJ_le_pCoreOf_L2 hquot hP hnc) hnc

theorem conjJoinOf_pushZ_le_L2 (hn : 1 ≤ n) (hchar : CharTwo X)
    (hquot : IsL2Quot n (oTwoQuot ↥X)) (hP : IsSylowTwoOf P X) (hnc : NoCharNormal P X)
    (hA : A ≤ Subgroup.normalizer (P : Set G)) (hAo : Odd (Nat.card A)) :
    conjJoinOf A (pushZ X P) ≤ pCoreOf 2 X ∧
      X ≤ Subgroup.normalizer (conjJoinOf A (pushZ X P) : Set G) := by
  have hodd : Odd ((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ A).relIndex A) := by
    refine Odd.of_dvd_nat hAo
      ⟨Nat.card ↥((Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ A) ⊓ A), ?_⟩
    exact (Subgroup.relIndex_mul_card
      (Subgroup.normalizer (pCoreOf 2 X : Set G) ⊓ A) A).symm
  rcases eq_or_lt_of_le hn with h1 | hgt
  · exact conjJoinOf_pushZ_le (Or.inl h1.symm) hchar hquot hP hnc hA hAo
  have hn2 : 2 ≤ n := by omega
  have h := cor42_of_isL2Quot (pushHyp_pushZ_L2 hn hchar hquot hP hnc) hn2 hquot
    (not_thompsonJ_le_pCoreOf_L2 hquot hP hnc) hnc hA hodd
  exact ⟨h.2.1, h.2.2 (le_normalizer_conjJoinOf_pushZ hP.1 hA)⟩

end Finite

theorem pushUpFacts_L2 (hn : 1 ≤ n) : PushUpFacts n :=
  fun _ _ _ _ _ _ hchar hquot hP hnc hA hAo =>
    ⟨pushZ_ne_bot_L2 hquot hP, conjJoinOf_pushZ_le_L2 hn hchar hquot hP hnc hA hAo⟩

section LemmaR

variable {V : Type*} [MulAction G V] {Γ : SimpleGraph V}

theorem lemmaR_of_faithful_L2 (hconn : Γ.Connected)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1) (hnbr : ∀ v : V, ∃ w, Γ.Adj v w)
    {α β : V} (hαβ : Γ.Adj α β) (hfinα : Finite ↥(MulAction.stabilizer G α))
    (hfinβ : Finite ↥(MulAction.stabilizer G β)) {W T : Subgroup G}
    (hn : 1 ≤ n) (hWβ : W ≤ MulAction.stabilizer G β)
    (hWtr : ∀ a b : V, Γ.Adj β a → Γ.Adj β b → ∃ w ∈ W, w • a = b)
    (hchar : CharTwo W) (hquot : IsL2Quot n (oTwoQuot ↥W))
    (hT : IsSylowTwoOf T W) (hTα : T ≤ MulAction.stabilizer G α) (hnc : NoCharNormal T W)
    {x : G} (hxα : x ∈ MulAction.stabilizer G α) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxo : Odd (orderOf x))
    (hxtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b → ∃ k : ℤ, x ^ k • a = b) : False :=
  lemmaR_of_faithful_of_pushUpFacts hconn hadj hfaith hnbr hαβ hfinα hfinβ (pushUpFacts_L2 hn)
    hWβ hWtr hchar hquot hT hTα hnc hxα hxT hxo hxtr

theorem lemmaR_L2 (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) {W T : Subgroup G}
    (hn : 1 ≤ n) (hWβ : W ≤ MulAction.stabilizer G β)
    (hWtr : ∀ a b : V, Γ.Adj β a → Γ.Adj β b → ∃ w ∈ W, w • a = b)
    (hchar : CharTwo W) (hquot : IsL2Quot n (oTwoQuot ↥W))
    (hT : IsSylowTwoOf T W) (hTα : T ≤ MulAction.stabilizer G α) (hnc : NoCharNormal T W)
    {x : G} (hxα : x ∈ MulAction.stabilizer G α) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxo : Odd (orderOf x))
    (hxtr : ∀ a b : V, Γ.Adj α a → Γ.Adj α b → ∃ k : ℤ, x ^ k • a = b) : False :=
  lemmaR_of_pushUpFacts h hαβ (pushUpFacts_L2 hn) hWβ hWtr hchar hquot hT hTα hnc hxα hxT hxo
    hxtr

end LemmaR

end CFSG.Quasithin.St84
