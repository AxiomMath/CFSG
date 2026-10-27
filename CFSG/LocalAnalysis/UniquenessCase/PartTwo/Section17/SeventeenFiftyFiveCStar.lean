module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStep
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def cStar1755 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) : Subgroup G :=
  (((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
    (Subgroup.inclusion hNL)).ker).map D.M.subtype

@[expose] noncomputable def T0_1755 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) : Subgroup G :=
  D.T ⊓ (L ⊔ cStar1755 D L hNL)

@[expose] noncomputable def Q0_1755 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) : Subgroup G :=
  (L ⊔ cStar1755 D L hNL) ⊓ normalizer (T0_1755 D L hNL : Set G)

@[expose] noncomputable def phi1755 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    ↥D.T →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L) :=
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
    ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
      (Subgroup.inclusion (D.sylowM.le.trans hNL)))

private theorem cStar1755_le_M (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) : cStar1755 D L hNL ≤ D.M :=
  Subgroup.map_subtype_le _

private theorem le_normalizer_cStar1755 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    D.M ≤ normalizer (cStar1755 D L hNL : Set G) := by
  let ρ : ↥D.M →* MulAut (Bar2 L) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion hNL)
  have hN : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hker : (⊤ : Subgroup ↥D.M) ≤ Subgroup.normalizer ((ρ.ker : Subgroup ↥D.M) : Set ↥D.M) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
  have h := CFSG.GroupTheory.map_subtype_le_normalizer (K := D.M) (X := ⊤) (L := ρ.ker) hker
  have htop : (⊤ : Subgroup ↥D.M).map D.M.subtype = D.M := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rwa [htop] at h

private theorem pCoreOf_le_cStar1755 (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) : pCoreOf 2 L ≤ cStar1755 D L hNL := by
  intro x hx
  have hxL : x ∈ L := (Subgroup.map_subtype_le (K := CFSG.pCore 2 ↥L)) hx
  have hxM : x ∈ D.M := hLM hxL
  refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  have hxcore : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hyx' : y = ⟨x, hxL⟩ := Subtype.ext hyx
    rwa [hyx'] at hy
  have hq : QuotientGroup.mk (⟨x, hxL⟩ : ↥L) = 1 :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) ⟨x, hxL⟩).2 hxcore
  have hincl : Subgroup.inclusion hNL ⟨x, hxM⟩ = ⟨x, Subgroup.le_normalizer hxL⟩ :=
    Subtype.ext rfl
  rw [hincl, CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L x hxL, hq]
  simp

private theorem pCoreOf_1755_le_T (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) : pCoreOf 2 L ≤ D.T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2M : pCoreOf 2 L ≤ D.M :=
    (Subgroup.map_subtype_le (K := CFSG.pCore 2 ↥L)).trans hLM
  have hO2n : D.M ≤ normalizer (pCoreOf 2 L : Set G) :=
    hNL.trans (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf L)
  have hsup : IsPGroup 2 ↥(D.T ⊔ pCoreOf 2 L) :=
    D.sylowM.isPGroup.to_sup_of_normal_right'
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L)
      (D.sylowM.le.trans hO2n)
  have heq : D.T ⊔ pCoreOf 2 L = D.T :=
    D.sylowM.eq_of_le le_sup_left (sup_le D.sylowM.le hO2M) hsup
  exact (le_sup_right : pCoreOf 2 L ≤ D.T ⊔ pCoreOf 2 L).trans heq.le

private theorem T_le_normalizer_T0_1755 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    D.T ≤ normalizer (T0_1755 D L hNL : Set G) := by
  have hMc : D.M ≤ normalizer (cStar1755 D L hNL : Set G) := le_normalizer_cStar1755 D L hNL
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hNL
  have hTc : D.T ≤ normalizer (cStar1755 D L hNL : Set G) := D.sylowM.le.trans hMc
  have hTS : D.T ≤ normalizer ((L ⊔ cStar1755 D L hNL : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_sup L (cStar1755 D L hNL) ⟨hTL ht, hTc ht⟩
  exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
    (H := D.T) (K := L ⊔ cStar1755 D L hNL) ⟨Subgroup.le_normalizer ht, hTS ht⟩

private theorem T0_le_Q0 (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) : T0_1755 D L hNL ≤ Q0_1755 D L hNL := by
  intro t ht
  exact Subgroup.mem_inf.mpr ⟨ht.2, Subgroup.le_normalizer ht⟩

private theorem T_le_normalizer_Q0 (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    D.T ≤ normalizer (Q0_1755 D L hNL : Set G) := by
  have hMc : D.M ≤ normalizer (cStar1755 D L hNL : Set G) := le_normalizer_cStar1755 D L hNL
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hNL
  have hTc : D.T ≤ normalizer (cStar1755 D L hNL : Set G) := D.sylowM.le.trans hMc
  have hTS : D.T ≤ normalizer ((L ⊔ cStar1755 D L hNL : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_sup L (cStar1755 D L hNL) ⟨hTL ht, hTc ht⟩
  have hTT0 : D.T ≤ normalizer (T0_1755 D L hNL : Set G) := T_le_normalizer_T0_1755 D L hNL
  have hTNN : D.T ≤ normalizer ((normalizer (T0_1755 D L hNL : Set G) : Subgroup G) : Set G) :=
    hTT0.trans Subgroup.le_normalizer
  exact fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
    (H := L ⊔ cStar1755 D L hNL) (K := normalizer (T0_1755 D L hNL : Set G))
    ⟨hTS ht, hTNN ht⟩

private theorem q0_1755_le_M (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) : Q0_1755 D L hNL ≤ D.M :=
  inf_le_left.trans (sup_le hLM (cStar1755_le_M D L hNL))

private theorem odd_relIndex_T0_Q0 (D : Data G) (L : Subgroup G) (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    Odd ((T0_1755 D L hNL).relIndex (Q0_1755 D L hNL)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcM : cStar1755 D L hNL ≤ D.M := cStar1755_le_M D L hNL
  have hMc : D.M ≤ normalizer (cStar1755 D L hNL : Set G) := le_normalizer_cStar1755 D L hNL
  have hMsup : D.M ≤ normalizer ((L ⊔ cStar1755 D L hNL : Subgroup G) : Set G) := fun m hm =>
    Subgroup.inf_normalizer_le_normalizer_sup L (cStar1755 D L hNL) ⟨hNL hm, hMc hm⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T0_1755 D L hNL)
      (L ⊔ cStar1755 D L hNL) :=
    D.sylowM.inf_of_le_normalizer (sup_le hLM hcM) hMsup
  have hSylQ : CFSG.ABGLocalTools.IsSylowOf 2 (T0_1755 D L hNL) (Q0_1755 D L hNL) :=
    hSyl.of_le (T0_le_Q0 D L hNL) inf_le_left
  have hnot := ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)
    (P := T0_1755 D L hNL) (K := Q0_1755 D L hNL)).1 hSylQ).2.2
  exact Nat.not_even_iff_odd.mp fun he => hnot (even_iff_two_dvd.mp he)

theorem cStar_T0_Q0_facts_1755 (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    cStar1755 D L hNL ≤ D.M ∧ D.M ≤ normalizer (cStar1755 D L hNL : Set G) ∧
      pCoreOf 2 L ≤ cStar1755 D L hNL ⊓ D.T ∧
      T0_1755 D L hNL ≤ D.T ∧ D.T ≤ normalizer (T0_1755 D L hNL : Set G) ∧
      T0_1755 D L hNL ≤ Q0_1755 D L hNL ∧
      Q0_1755 D L hNL ≤ normalizer (T0_1755 D L hNL : Set G) ∧
      D.T ≤ normalizer (Q0_1755 D L hNL : Set G) ∧ Q0_1755 D L hNL ≤ D.M ∧
      Odd ((T0_1755 D L hNL).relIndex (Q0_1755 D L hNL)) :=
  ⟨cStar1755_le_M D L hNL, le_normalizer_cStar1755 D L hNL,
    le_inf (pCoreOf_le_cStar1755 D L hLM hNL) (pCoreOf_1755_le_T D L hLM hNL),
    inf_le_left, T_le_normalizer_T0_1755 D L hNL, T0_le_Q0 D L hNL,
    inf_le_right, T_le_normalizer_Q0 D L hLM hNL, q0_1755_le_M D L hLM hNL,
    odd_relIndex_T0_Q0 D L hLM hNL⟩

theorem outer_finite_isCyclic_1755 {L : Subgroup G} {n : ℕ} (hL2 : IsL2 (Bar2 L) n) :
    Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) ∧
      IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
  ⟨CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_finite_outer (Bar2 L),
    CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.isCyclic_outer_of_isL2Ev
      (CFSG.LocalAnalysis.UniquenessCase.UC22.P22fin.isL2Ev_of_isL2 hL2).1⟩

theorem ker_phi_le_T0_1755 (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) (u : ↥D.T) (hu : phi1755 D L hNL u = 1) :
    (u : G) ∈ T0_1755 D L hNL := by
  refine Subgroup.mem_inf.2 ⟨u.2, ?_⟩
  have hin : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
      ⟨(u : G), D.sylowM.le.trans hNL u.2⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) :=
    (QuotientGroup.eq_one_iff _).1 hu
  obtain ⟨ybar, hy⟩ := MonoidHom.mem_range.1 hin
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ybar
  have hyN : (y : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer y.2
  have hrho := CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L (y : G) y.2
  have huM : (u : G) ∈ D.M := D.sylowM.le u.2
  have hyM : (y : G) ∈ D.M := hLM y.2
  have hc : (y : G)⁻¹ * u ∈ cStar1755 D L hNL := by
    have hker : (⟨(y : G)⁻¹ * u, D.M.mul_mem (D.M.inv_mem hyM) huM⟩ : ↥D.M) ∈
        ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
          (Subgroup.inclusion hNL)).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      have hsplit : Subgroup.inclusion hNL
            ⟨(y : G)⁻¹ * u, D.M.mul_mem (D.M.inv_mem hyM) huM⟩ =
          (⟨(y : G), hyN⟩ : ↥(normalizer (L : Set G)))⁻¹ *
            ⟨(u : G), D.sylowM.le.trans hNL u.2⟩ := rfl
      rw [hsplit, map_mul, map_inv, ← hy, hrho, inv_mul_cancel]
    exact Subgroup.mem_map.2 ⟨_, hker, rfl⟩
  have hu_eq : (u : G) = (y : G) * ((y : G)⁻¹ * u) := by group
  rw [hu_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.2) (Subgroup.mem_sup_right hc)

theorem T0_eq_sup_1755 (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) :
    T0_1755 D L hNL = (D.T ⊓ L) ⊔ (D.T ⊓ cStar1755 D L hNL) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcM, hMc, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  exact inf_sup_eq_sup_inf_of_isSylowOf D.sylowM hLM hcM hNL hMc

private theorem conj_mem_inf_T_cStar (D : Data G) (L : Subgroup G)
    (hNL : D.M ≤ normalizer (L : Set G)) (hO2C : pCoreOf 2 L ≤ cStar1755 D L hNL)
    (hO2T : pCoreOf 2 L ≤ D.T) {y z : G} (hyL : y ∈ L) (hz : z ∈ D.T ⊓ cStar1755 D L hNL) :
    y * z * y⁻¹ ∈ D.T ⊓ cStar1755 D L hNL := by
  have hzT : z ∈ D.T := hz.1
  have hzC : z ∈ cStar1755 D L hNL := hz.2
  have hzM : z ∈ D.M := D.sylowM.le hzT
  have hzN : z ∈ normalizer (L : Set G) := hNL hzM
  have hρz : (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
      (Subgroup.inclusion hNL) ⟨z, hzM⟩ = 1 := by
    obtain ⟨z', hz'ker, hz'val⟩ := Subgroup.mem_map.1 hzC
    have hz'eq : z' = ⟨z, hzM⟩ := Subtype.ext hz'val
    rwa [← hz'eq]
  have hρz' : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨z, hzN⟩ = 1 := by
    have hincl : Subgroup.inclusion hNL ⟨z, hzM⟩ = ⟨z, hzN⟩ := Subtype.ext rfl
    simpa [MonoidHom.comp_apply, hincl] using hρz
  have hcomm : z * y * z⁻¹ * y⁻¹ ∈ pCoreOf 2 L :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L ⟨z, hzN⟩ ⟨y, hyL⟩).1
      (by rw [hρz']; rfl)
  have hcomm' : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
    have := (pCoreOf 2 L).inv_mem hcomm
    simpa [mul_assoc] using this
  have hyzy : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
  rw [hyzy]
  exact Subgroup.mem_inf.mpr
    ⟨D.T.mul_mem (hO2T hcomm') hzT, (cStar1755 D L hNL).mul_mem (hO2C hcomm') hzC⟩

theorem exists_torus_mem_Q0_1755 (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) {n : ℕ} (hL2 : IsL2 (Bar2 L) n) {p : ℕ}
    (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    ∃ h ∈ L ⊓ Q0_1755 D L hNL, orderOf h = p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hO2, -, -, -, -, -, -, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  obtain ⟨hO2C, hO2T⟩ := le_inf_iff.1 hO2
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ D.T) L := by
    have hM' : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
      CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 D.sylowM
    have := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hM' hLM hNL
    rwa [inf_comm] at this
  have hdvd : p ∣ Nat.card ↥(L ⊓ Subgroup.normalizer ((L ⊓ D.T : Subgroup G) : Set G)) :=
    prime_dvd_card_inf_normalizer_of_isL2_bar2 hL2 hSyl hpn
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(L ⊓ Subgroup.normalizer ((L ⊓ D.T : Subgroup G) : Set G))) p hdvd
  have hyL : (y : G) ∈ L := y.2.1
  have hyNT : (y : G) ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hy' : ∀ w : G, w ∈ (L ⊓ D.T : Subgroup G) ↔
        (y : G) * w * (y : G)⁻¹ ∈ (L ⊓ D.T : Subgroup G) :=
      Subgroup.mem_normalizer_iff.1 y.2.2
    constructor
    · rintro ⟨hzT, hzL⟩
      obtain ⟨h1, h2⟩ := (hy' z).1 ⟨hzL, hzT⟩
      exact ⟨h2, h1⟩
    · rintro ⟨hzT, hzL⟩
      obtain ⟨h1, h2⟩ := (hy' z).2 ⟨hzL, hzT⟩
      exact ⟨h2, h1⟩
  have hyNC : (y : G) ∈ normalizer ((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G) := by
    have hkey : ∀ w : G, w ∈ D.T ⊓ cStar1755 D L hNL →
        (y : G) * w * (y : G)⁻¹ ∈ D.T ⊓ cStar1755 D L hNL := fun w hw =>
      conj_mem_inf_T_cStar D L hNL hO2C hO2T hyL hw
    have hkey' : ∀ w : G, w ∈ D.T ⊓ cStar1755 D L hNL →
        (y : G)⁻¹ * w * ((y : G)⁻¹)⁻¹ ∈ D.T ⊓ cStar1755 D L hNL := fun w hw =>
      conj_mem_inf_T_cStar D L hNL hO2C hO2T (L.inv_mem hyL) hw
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hkey w
    · intro hw
      have h := hkey' ((y : G) * w * (y : G)⁻¹) hw
      simpa [mul_assoc] using h
  have hyT0 : (y : G) ∈ normalizer (T0_1755 D L hNL : Set G) := by
    rw [T0_eq_sup_1755 D hLM hNL]
    exact Subgroup.inf_normalizer_le_normalizer_sup (D.T ⊓ L)
      (D.T ⊓ cStar1755 D L hNL) ⟨hyNT, hyNC⟩
  have hyQ0 : (y : G) ∈ Q0_1755 D L hNL :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hyL, hyT0⟩
  exact ⟨(y : G), Subgroup.mem_inf.mpr ⟨hyL, hyQ0⟩, by
    rw [Subgroup.orderOf_coe, hyord]⟩

theorem exists_X_1755 (D : Data G) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnc : ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S (Q0_1755 D L hNL) →
      ¬ IsCyclic ↥S) :
    ∃ X : Subgroup G, X ≤ Q0_1755 D L hNL ∧ IsPGroup p ↥X ∧ (∀ x ∈ X, x ^ p = 1) ∧
      ¬ IsCyclic ↥X ∧ D.T ≤ normalizer ((X ⊔ T0_1755 D L hNL : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, hT0T, hTT0, hT0Q, hQT0, hTQ, -, hodd⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  exact exists_noncyclic_exp_le_normalizer_sup hp hp2 D.sylowM.isPGroup
    (D.sylowM.isPGroup.to_le hT0T) hT0Q hQT0 hTQ hTT0 hodd hnc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
