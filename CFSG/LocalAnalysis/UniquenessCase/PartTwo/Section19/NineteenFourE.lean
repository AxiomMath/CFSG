module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_le_normalizer_conj_of_five_dvd_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) (hsp : IsStronglyPEmbedded 5 D.M) {g : G}
    (hg : g ∉ D.M) {X : Subgroup G} (hXM : X ≤ D.M) (h5 : 5 ∣ Nat.card X) :
    ¬ X ≤ normalizer (conjSubgroup V₀ g : Set G) := by
  intro hX
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub (by omega)
  have hV : InCalV D.M V₀ := S17.hyp125_inCalV h hne
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hNg : normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup D.M g := by
    rw [← conjSubgroup_normalizer, hN]
  have hXg : X ≤ D.M ⊓ conjSubgroup D.M g := le_inf hXM (hNg ▸ hX)
  have h5' : 5 ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M g) :=
    h5.trans (Subgroup.card_dvd_of_le hXg)
  have hg' : g⁻¹ ∉ D.M := fun hgi => hg (by simpa using D.M.inv_mem hgi)
  exact hsp.2.2 g⁻¹ hg' (by simpa [conjSubgroup] using h5')

theorem inf_centerOf_wClos_two_ne_bot_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) (hsp : IsStronglyPEmbedded 5 D.M)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M)
    {H Q A : Subgroup G} (hHM : H ≤ D.M) (hQH : Q ≤ H) (hHQ : H ≤ normalizer (Q : Set G))
    (hQT : Q ≤ D.T) (hAH : A ≤ H) (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAM : ¬ A ≤ pCoreOf 2 D.M) (hAQ : ¬ A ≤ Q) (hq : E3.mQuot A (A ⊓ Q) ≤ 2)
    (hC2 : E3.cClos V₀ 2 D.T ≤ H)
    (hP5 : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → ¬ N ≤ Q →
      5 ∣ Nat.card N) :
    A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ := by
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub (by omega)
  have hV : IsElemAbelian 2 V₀ := h.pairFacts.elemAbelian₀
  have hVp : IsPGroup 2 ↥V₀ := hV.isPGroup
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := S17.hyp125_isTI h hne
  obtain ⟨-, g, hAg, hmq⟩ := E3.mem_gammaSet_iff.mp hA
  have hVg : IsPGroup 2 ↥(conjSubgroup V₀ g) := E3.isPGroup_conjSubgroup hVp g
  have hAeq : A = conjSubgroup V₀ g := (E3.mQuot_eq_zero_iff hVg hAg).mp hmq
  have hAp : IsPGroup 2 ↥A := hAeq.symm ▸ hVg
  have hAm : 4 < mSub A := by
    rw [hAeq]
    show 4 < rk ↥(conjSubgroup V₀ g)
    rw [E3.rk_conjSubgroup]
    exact hm
  have hmq' : E3.mQuot A Q ≤ 2 := by
    have heq : E3.mQuot A Q = E3.mQuot A (A ⊓ Q) := by
      rw [E3.mQuot, E3.mQuot, inf_comm, Subgroup.inf_relIndex_right]
    rwa [heq]
  have hBne : A ⊓ Q ≠ ⊥ := s19c_inf_ne_bot_of_mQuot_le_two hAp hAm hmq'
  have hBW : A ⊓ Q ≤ E3.wClos V₀ 2 Q :=
    E3.le_wClos_of_mQuot_le (V := V₀) hV g inf_le_right
      (by rw [← hAeq]; exact inf_le_left)
      (k := 2) (by rw [← hAeq]; exact hq) (lt_trans (by norm_num) hm)
  have hNCX : ∀ X : Subgroup G, normalizer (X : Set G) ≤
      normalizer (centralizer (X : Set G) : Set G) := by
    intro X y hy
    rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr hy]
  have hHNW : H ≤ normalizer (E3.wClos V₀ 2 Q : Set G) :=
    hHQ.trans (E3.normalizer_le_normalizer_wClos (V := V₀) (i := 2) Q)
  have hHNC : H ≤ normalizer (centralizer (E3.wClos V₀ 2 Q : Set G) : Set G) :=
    hHNW.trans (hNCX (E3.wClos V₀ 2 Q))
  have hHNc : H ≤ normalizer (E3.cClos V₀ 2 Q : Set G) := by
    rw [E3.cClos]
    exact (le_inf hHQ hHNC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hHC : H ≤ normalizer (H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G) : Set G) :=
    (le_inf Subgroup.le_normalizer hHNC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCCB : H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G) ≤
      centralizer ((A ⊓ Q : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp (mem_inf.mp hy).2 b (hBW hb)
  obtain ⟨b, hb1⟩ := ne_bot_iff_exists_ne_one.mp hBne
  have hbB : (b : G) ∈ A ⊓ Q := b.2
  have hbA : (b : G) ∈ A := (mem_inf.mp hbB).1
  have hbne : (b : G) ≠ 1 := fun hh => hb1 (Subtype.ext hh)
  have hCNA : H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G) ≤
      normalizer (conjSubgroup V₀ g : Set G) :=
    hCCB.trans ((Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hbB)).trans (centralizer_le_normalizer_conj hTI g (hAeq ▸ hbA) hbne))
  have hCQ : H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G) ≤ Q := by
    by_contra hCQ
    have h5 : 5 ∣ Nat.card ↥(H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G)) :=
      hP5 _ inf_le_left hHC hCQ
    have hCM : H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G) ≤ D.M := inf_le_left.trans hHM
    have hgM : g ∉ D.M := by
      intro hg
      apply hAM
      have hV0 : conjSubgroup V₀ g = V₀ :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (h.pairFacts.le_normalizer₀ hg)
      rw [hAeq, hV0]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (h.pairFacts.le.trans h.pairFacts.le_M) h.pairFacts.le_normalizer₀ hVp
    exact (not_le_normalizer_conj_of_five_dvd_19 h hm hsp hgM hCM h5) hCNA
  have hCeq : H ⊓ centralizer (E3.wClos V₀ 2 Q : Set G) = E3.cClos V₀ 2 Q := by
    rw [E3.cClos]
    exact le_antisymm (le_inf hCQ inf_le_right)
      (le_inf (inf_le_left.trans hQH) inf_le_right)
  have hCNA' : E3.cClos V₀ 2 Q ≤ normalizer (A : Set G) := by
    rw [← hCeq, hAeq]
    exact hCNA
  have hC2Q : E3.cClos V₀ 2 D.T ≤ E3.cClos V₀ 2 Q := by
    rw [← hCeq]
    refine le_inf hC2 ?_
    exact inf_le_right.trans (Subgroup.centralizer_le (E3.wClos_mono hQT))
  have hcomm_ne : ⁅A, E3.cClos V₀ 2 Q⁆ ≠ ⊥ := by
    intro hbot
    have hAC : A ≤ centralizer (E3.cClos V₀ 2 Q : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    set K : Subgroup G := H ⊓ centralizer (E3.cClos V₀ 2 Q : Set G) with hK
    have hAK : A ≤ K := by rw [hK]; exact le_inf hAH hAC
    have hKH : K ≤ H := by rw [hK]; exact inf_le_left
    have hKK : K ≠ ⊥ := fun hbot' => hAQ ((hbot' ▸ hAK).trans bot_le)
    have hHK : H ≤ normalizer (K : Set G) := by
      rw [hK]
      refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      exact hHNc.trans (hNCX (E3.cClos V₀ 2 Q))
    have h5K : 5 ∣ Nat.card ↥K := hP5 K hKH hHK (fun hle => hAQ (hAK.trans hle))
    have hKM : K ≤ D.M := hKH.trans hHM
    have hKC2 : K ≤ centralizer (E3.cClos V₀ 2 D.T : Set G) := by
      refine (inf_le_right : K ≤ centralizer (E3.cClos V₀ 2 Q : Set G)).trans ?_
      exact Subgroup.centralizer_le hC2Q
    exact (not_le_centralizer_cClos_two_19 h hm hsp hN2 hKM h5K) hKC2
  have hleA : ⁅A, E3.cClos V₀ 2 Q⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hCNA'
  have hleC : ⁅A, E3.cClos V₀ 2 Q⁆ ≤ E3.cClos V₀ 2 Q :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hAH.trans hHNc)
  have hAC_center : A ⊓ E3.cClos V₀ 2 Q ≤ centerOf (E3.wClos V₀ 2 Q) := by
    intro x hx
    have hxA : x ∈ A := (mem_inf.mp hx).1
    have hxC : x ∈ E3.cClos V₀ 2 Q := (mem_inf.mp hx).2
    rw [E3.cClos] at hxC
    have hxQ : x ∈ Q := (mem_inf.mp hxC).1
    have hxCw : x ∈ centralizer (E3.wClos V₀ 2 Q : Set G) := (mem_inf.mp hxC).2
    rw [centerOf, mem_inf]
    exact ⟨hBW (mem_inf.mpr ⟨hxA, hxQ⟩), hxCw⟩
  intro hbot
  exact hcomm_ne (le_antisymm
    (hbot ▸ (le_inf hleA hleC).trans (le_inf inf_le_left hAC_center)) bot_le)

theorem exists_inCalO_two_not_one_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) {H Q A : Subgroup G}
    (hQH : Q ≤ H) (hHQ : H ≤ normalizer (Q : Set G)) (hAH : A ≤ H)
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hq : E3.mQuot A (A ⊓ Q) = 2)
    (hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥) {x : G} (hxH : x ∈ H)
    (hx : ∀ a ∈ A, a ∈ normalizer (conjSubgroup A x : Set G) → a ∈ Q)
    (hx' : ∀ a ∈ A, a ∈ normalizer (conjSubgroup A x⁻¹ : Set G) → a ∈ Q) :
    ∃ g : G, InCalO 2 D.M ⊥ V₀ g ∧ ¬ InCalO 1 D.M ⊥ V₀ g := by
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub (by omega)
  have hV : IsElemAbelian 2 V₀ := h.pairFacts.elemAbelian₀
  have hVp : IsPGroup 2 ↥V₀ := hV.isPGroup
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := S17.hyp125_isTI h hne
  obtain ⟨-, g, hAg, hmq⟩ := E3.mem_gammaSet_iff.mp hA
  have hVg : IsPGroup 2 ↥(conjSubgroup V₀ g) := E3.isPGroup_conjSubgroup hVp g
  have hAeq : A = conjSubgroup V₀ g := (E3.mQuot_eq_zero_iff hVg hAg).mp hmq
  have hNV0 : normalizer (V₀ : Set G) = D.M :=
    normalizer_eq_of_inCalV D (S17.hyp125_inCalV h hne)
  have hBQ : A ⊓ Q ≤ E3.wClos V₀ 2 Q :=
    E3.le_wClos_of_mQuot_le (V := V₀) hV g inf_le_right
      (by rw [← hAeq]; exact inf_le_left)
      (k := 2) (by rw [← hAeq]; exact le_of_eq hq) (lt_trans (by norm_num) hm)
  obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp hZ
  have hzA : (z : G) ∈ A := (mem_inf.mp z.2).1
  have hzW : (z : G) ∈ E3.wClos V₀ 2 Q := (mem_inf.mp (mem_inf.mp z.2).2).1
  have hzC : (z : G) ∈ centralizer (E3.wClos V₀ 2 Q : Set G) :=
    (mem_inf.mp (mem_inf.mp z.2).2).2
  have hzne : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hxN : x ∈ normalizer (E3.wClos V₀ 2 Q : Set G) :=
    E3.normalizer_le_normalizer_wClos (V := V₀) (i := 2) Q (hHQ hxH)
  have keyW : ∀ y : G, y ∈ normalizer (E3.wClos V₀ 2 Q : Set G) →
      y⁻¹ * (z : G) * y ∈ E3.wClos V₀ 2 Q := by
    intro y hy
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hy) (z : G)).mp hzW
  have keyC : ∀ y : G, y ∈ normalizer (E3.wClos V₀ 2 Q : Set G) →
      y⁻¹ * (z : G) * y ∈ centralizer (E3.wClos V₀ 2 Q : Set G) := by
    intro y hy
    have hCy : conjSubgroup (centralizer (E3.wClos V₀ 2 Q : Set G)) y =
        centralizer (E3.wClos V₀ 2 Q : Set G) := by
      rw [E3.conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.mpr hy]
    have hmem : y⁻¹ * (z : G) * y ∈
        conjSubgroup (centralizer (E3.wClos V₀ 2 Q : Set G)) y := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hzC
    rwa [hCy] at hmem
  have keyA : ∀ y : G, y⁻¹ * (z : G) * y ∈ conjSubgroup A y := by
    intro y
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hzA
  have keyne : ∀ y : G, y⁻¹ * (z : G) * y ≠ 1 := by
    intro y hh
    apply hzne
    have := congrArg (fun t => y * t * y⁻¹) hh
    simpa [mul_assoc] using this
  have hBNAx : A ⊓ Q ≤ normalizer (conjSubgroup A x : Set G) := by
    have hAxeq : conjSubgroup A x = conjSubgroup V₀ (g * x) := by
      rw [← conjSubgroup_conjSubgroup, hAeq]
    rw [hAxeq]
    have hC : A ⊓ Q ≤ centralizer ({(x⁻¹ * (z : G) * x)} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (Subgroup.mem_centralizer_iff.mp (keyC x hxN) a (hBQ ha)).symm
    exact hC.trans (centralizer_le_normalizer_conj hTI (g * x)
      (by rw [← hAxeq]; exact keyA x) (keyne x))
  have hBNAx' : A ⊓ Q ≤ normalizer (conjSubgroup A x⁻¹ : Set G) := by
    have hAxeq : conjSubgroup A x⁻¹ = conjSubgroup V₀ (g * x⁻¹) := by
      rw [← conjSubgroup_conjSubgroup, hAeq]
    rw [hAxeq]
    have hC : A ⊓ Q ≤ centralizer ({(x⁻¹)⁻¹ * (z : G) * x⁻¹} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (Subgroup.mem_centralizer_iff.mp (keyC x⁻¹ (inv_mem hxN)) a (hBQ ha)).symm
    exact hC.trans (centralizer_le_normalizer_conj hTI (g * x⁻¹)
      (by rw [← hAxeq]; exact keyA x⁻¹) (keyne x⁻¹))
  have hNAx : A ⊓ normalizer (conjSubgroup A x : Set G) = A ⊓ Q :=
    le_antisymm
      (fun a ha => mem_inf.mpr ⟨(mem_inf.mp ha).1, hx a (mem_inf.mp ha).1 (mem_inf.mp ha).2⟩)
      (le_inf inf_le_left hBNAx)
  have hNAx' : A ⊓ normalizer (conjSubgroup A x⁻¹ : Set G) = A ⊓ Q :=
    le_antisymm
      (fun a ha => mem_inf.mpr ⟨(mem_inf.mp ha).1, hx' a (mem_inf.mp ha).1 (mem_inf.mp ha).2⟩)
      (le_inf inf_le_left hBNAx')
  have hAinv : conjSubgroup A g⁻¹ = V₀ := by
    rw [hAeq, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hg' : conjSubgroup (conjSubgroup A x) g⁻¹ = conjSubgroup V₀ (g * x * g⁻¹) := by
    rw [conjSubgroup_conjSubgroup, hAeq, conjSubgroup_conjSubgroup,
      show g * (x * g⁻¹) = g * x * g⁻¹ by group]
  have hmqV : E3.mQuot V₀ (conjSubgroup D.M (g * x * g⁻¹)) = 2 := by
    have hNV : V₀ ⊓ normalizer (conjSubgroup V₀ (g * x * g⁻¹) : Set G) =
        conjSubgroup (A ⊓ Q) g⁻¹ := by
      have h1 : conjSubgroup (A ⊓ Q) g⁻¹ =
          conjSubgroup (A ⊓ normalizer (conjSubgroup A x : Set G)) g⁻¹ := by rw [hNAx]
      rw [h1, E3.conjSubgroup_inf, E3.conjSubgroup_normalizer, hAinv, ← hg']
    have hD : conjSubgroup D.M (g * x * g⁻¹) =
        normalizer (conjSubgroup V₀ (g * x * g⁻¹) : Set G) := by
      rw [← E3.conjSubgroup_normalizer, hNV0]
    have h1 : E3.mQuot V₀ (normalizer (conjSubgroup V₀ (g * x * g⁻¹) : Set G)) =
        E3.mQuot V₀ (V₀ ⊓ normalizer (conjSubgroup V₀ (g * x * g⁻¹) : Set G)) := by
      rw [E3.mQuot, E3.mQuot, inf_comm, Subgroup.inf_relIndex_right]
    rw [hD, h1, hNV, ← hAinv, E3.mQuot_conjSubgroup]
    exact hq
  have hNAx2 : E3.mQuot (conjSubgroup A x) (normalizer (A : Set G)) = 2 := by
    have hconj : E3.mQuot (conjSubgroup A x) (normalizer (A : Set G)) =
        E3.mQuot A (normalizer (conjSubgroup A x⁻¹ : Set G)) := by
      have h := E3.mQuot_conjSubgroup (V := A)
        (U := normalizer (conjSubgroup A x⁻¹ : Set G)) x
      have hL : conjSubgroup (normalizer (conjSubgroup A x⁻¹ : Set G)) x =
          normalizer (A : Set G) := by
        rw [← E3.conjSubgroup_normalizer (A := A) (g := x⁻¹), conjSubgroup_conjSubgroup,
          inv_mul_cancel, conjSubgroup_one]
      rwa [hL] at h
    have h2 : E3.mQuot A (normalizer (conjSubgroup A x⁻¹ : Set G)) =
        E3.mQuot A (A ⊓ normalizer (conjSubgroup A x⁻¹ : Set G)) := by
      rw [E3.mQuot, E3.mQuot, inf_comm, Subgroup.inf_relIndex_right]
    rw [hconj, h2, hNAx']
    exact hq
  have hmqV' : E3.mQuot (conjSubgroup V₀ (g * x * g⁻¹)) D.M = 2 := by
    have hNV' : conjSubgroup V₀ (g * x * g⁻¹) ⊓ D.M =
        conjSubgroup (conjSubgroup A x ⊓ normalizer (A : Set G)) g⁻¹ := by
      rw [← hg', ← hNV0, ← hAinv, ← E3.conjSubgroup_normalizer, ← E3.conjSubgroup_inf]
    have h1 : E3.mQuot (conjSubgroup V₀ (g * x * g⁻¹)) D.M =
        E3.mQuot (conjSubgroup V₀ (g * x * g⁻¹))
          (conjSubgroup V₀ (g * x * g⁻¹) ⊓ D.M) := by
      rw [E3.mQuot, E3.mQuot, inf_comm, Subgroup.inf_relIndex_right]
    have h2 : E3.mQuot (conjSubgroup A x)
        (conjSubgroup A x ⊓ normalizer (A : Set G)) =
        E3.mQuot (conjSubgroup A x) (normalizer (A : Set G)) := by
      rw [E3.mQuot, E3.mQuot, inf_comm, Subgroup.inf_relIndex_right]
    rw [h1, hNV', ← hg', E3.mQuot_conjSubgroup, h2]
    exact hNAx2
  have hzero : ∀ {U : Subgroup G}, conjSubgroup V₀ (g * x * g⁻¹) ≤ U →
      E3.mQuot (conjSubgroup V₀ (g * x * g⁻¹)) U = 0 := by
    intro U hU
    rw [E3.mQuot, Subgroup.relIndex_eq_one.mpr hU, padicValNat.one]
  refine ⟨g * x * g⁻¹, ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_⟩
  · intro hle
    rw [hzero hle] at hmqV'
    omega
  · exact le_of_eq hmqV
  · intro hbot
    exact absurd rfl hbot
  · intro hle
    rw [E3.mQuot, Subgroup.relIndex_eq_one.mpr hle, padicValNat.one] at hmqV
    omega
  · exact le_of_eq hmqV'
  · intro hbot
    exact absurd rfl hbot
  · intro h1
    have hle1 : E3.mQuot V₀ (conjSubgroup D.M (g * x * g⁻¹)) ≤ 1 := h1.1.2.1
    rw [hmqV] at hle1
    omega

theorem false_of_two_three_dvd_orderOf_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) {H Q A : Subgroup G}
    (hHQ : H ≤ normalizer (Q : Set G)) (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAO : ¬ A ≤ pCoreOf 2 H) (hZ : A ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥) {x d e : G}
    (hxH : x ∈ H) (hd : d ∈ A) (he : e ∈ conjSubgroup A x)
    (h2 : 2 ∣ orderOf (d * e)) (h3 : 3 ∣ orderOf (d * e)) : False := by
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub (by omega)
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := S17.hyp125_isTI h hne
  have hV : IsElemAbelian 2 V₀ := h.pairFacts.elemAbelian₀
  obtain ⟨-, g, hAg, hmq⟩ := E3.mem_gammaSet_iff.mp hA
  have hVg : IsPGroup 2 ↥(conjSubgroup V₀ g) := E3.isPGroup_conjSubgroup hV.isPGroup g
  have hAeq : A = conjSubgroup V₀ g := (E3.mQuot_eq_zero_iff hVg hAg).mp hmq
  have hEab : IsMulCommutative ↥(centerOf (E3.wClos V₀ 2 Q)) := by
    refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (mem_inf.mp hw).2 y (mem_inf.mp hy).1).symm
  obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp hZ
  have hzA : (z : G) ∈ A := (mem_inf.mp z.2).1
  have hzW : (z : G) ∈ E3.wClos V₀ 2 Q :=
    (mem_inf.mp (mem_inf.mp z.2).2).1
  have hzC : (z : G) ∈ centralizer (E3.wClos V₀ 2 Q : Set G) :=
    (mem_inf.mp (mem_inf.mp z.2).2).2
  have hzne : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hxN : x ∈ normalizer (E3.wClos V₀ 2 Q : Set G) :=
    E3.normalizer_le_normalizer_wClos (V := V₀) (i := 2) Q (hHQ hxH)
  have hzxW : x⁻¹ * (z : G) * x ∈ E3.wClos V₀ 2 Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) (z : G)).mp hzW
  have hzxC : x⁻¹ * (z : G) * x ∈ centralizer (E3.wClos V₀ 2 Q : Set G) := by
    have hCx : conjSubgroup (centralizer (E3.wClos V₀ 2 Q : Set G)) x =
        centralizer (E3.wClos V₀ 2 Q : Set G) := by
      rw [E3.conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.mpr hxN]
    have hmem : x⁻¹ * (z : G) * x ∈
        conjSubgroup (centralizer (E3.wClos V₀ 2 Q : Set G)) x := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hzC
    rwa [hCx] at hmem
  have hzxA : x⁻¹ * (z : G) * x ∈ conjSubgroup A x := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hzA
  have hzxne : x⁻¹ * (z : G) * x ≠ 1 := by
    intro hh
    apply hzne
    have := congrArg (fun t => x * t * x⁻¹) hh
    simpa [mul_assoc] using this
  have hZ' : conjSubgroup A x ⊓ centerOf (E3.wClos V₀ 2 Q) ≠ ⊥ := by
    refine ne_bot_iff_exists_ne_one.mpr
      ⟨⟨x⁻¹ * (z : G) * x, mem_inf.mpr ⟨hzxA, mem_inf.mpr ⟨hzxW, hzxC⟩⟩⟩, ?_⟩
    exact fun hh => hzxne (congrArg Subtype.val hh)
  have hAom : A ∈ omegaSet V₀ H (centerOf (E3.wClos V₀ 2 Q)) := by
    refine ⟨g, hAeq, ?_, hAO⟩
    rwa [inf_comm]
  have hxO : x ∈ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hxH
  have hAxeom : conjSubgroup A x ∈ omegaSet V₀ H (centerOf (E3.wClos V₀ 2 Q)) := by
    refine ⟨g * x, ?_, ?_, ?_⟩
    · rw [← conjSubgroup_conjSubgroup, hAeq]
    · rwa [inf_comm]
    · intro hle
      apply hAO
      have hconjO : conjSubgroup (pCoreOf 2 H) x⁻¹ = pCoreOf 2 H := by
        rw [conjSubgroup_eq_iff_mem_normalizer]
        simpa using inv_mem hxO
      have hAeqx : A = conjSubgroup (conjSubgroup A x) x⁻¹ := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      rw [hAeqx]
      calc conjSubgroup (conjSubgroup A x) x⁻¹ ≤ conjSubgroup (pCoreOf 2 H) x⁻¹ :=
            E3.conjSubgroup_mono_left x⁻¹ hle
        _ = pCoreOf 2 H := hconjO
  have hnot2 : ¬ IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set G)) := by
    intro hp
    have hde : d * e ∈ Subgroup.closure ({d, e} : Set G) := by
      apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have hdvd : orderOf (d * e) ∣ Nat.card ↥(Subgroup.closure ({d, e} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hde
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    have h3' : 3 ∣ Nat.card ↥(Subgroup.closure ({d, e} : Set G)) := h3.trans hdvd
    rw [hn] at h3'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
  exact (seven_three_A hV hTI hEab hAom hAxeom hd he hnot2).not_two_dvd_nat h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
