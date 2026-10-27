module

public import CFSG.RankThree.GF2n.Tim78S43
public import CFSG.RankThree.GF2n.Tim78S44Aux

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem le_Q_of_conj_T_centralizes (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {g : G} (hBBg : B ⊓ conjSubgroup g B = ⊥) (hE : conjSubgroup g B ⊓ P ≠ ⊥)
    (hBgM : conjSubgroup g B ≤ M)
    (hTBg : ∀ t ∈ T, ∀ a ∈ conjSubgroup g B, t * a = a * t)
    (hBTg : B ⊓ conjSubgroup g T = ⊥)
    (hTgB : ∀ s ∈ conjSubgroup g T, ∀ b ∈ B, s * b = b * s)
    (hTgM : conjSubgroup g T ≤ M) :
    conjSubgroup g B ≤ Q := by
  set Bg := conjSubgroup g B with hBgdef
  set Tg := conjSubgroup g T with hTgdef
  set E := Bg ⊓ P with hEdef
  set C := P ⊓ Subgroup.centralizer (E : Set G) with hCdef
  have hEBg : E ≤ Bg := inf_le_left
  have hEP : E ≤ P := inf_le_right
  obtain ⟨⟨e₀, he₀⟩, he₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have he₀1' : e₀ ≠ 1 := fun h => he₀1 (Subtype.ext h)
  have hBgPg : Bg ≤ conjSubgroup g P := Subgroup.map_mono H.B_le_P
  have hCMg : C ≤ conjSubgroup g M := fun c hc =>
    H.centralizer_le_conj (g := g) (x := e₀) (hEBg he₀) he₀1'
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hc.2 e₀ he₀).symm)
  have hCNTg : ∀ c ∈ C, c ∈ Subgroup.normalizer (Tg : Set G) := fun c hc =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T (hCMg hc)
  have hCNBg : ∀ c ∈ C, c ∈ Subgroup.normalizer (Bg : Set G) := fun c hc =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_B (hCMg hc)
  have hTgPg := H.conj_T_le_centralizer_conj_P g
  have hTgNP : ∀ y ∈ Tg, y ∈ Subgroup.normalizer (P : Set G) := fun y hy =>
    H.M_le_normalizer_P (hTgM hy)
  have hTgC : ∀ u ∈ Tg, u ∈ C → ∀ c ∈ C, u * c = c * u := by
    intro u huT huC c hcC
    have h1 : ⁅c, u⁆ ∈ Tg := by
      have e : ⁅c, u⁆ = (c * u * c⁻¹) * u⁻¹ := rfl
      rw [e]
      exact Tg.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCNTg c hcC) u).mp huT) (Tg.inv_mem huT)
    have h2 : ⁅c, u⁆ ∈ B := H.commutator_mem (H.P_le_Q hcC.1) (H.P_le_Q huC.1)
    have h3 : ⁅c, u⁆ ∈ B ⊓ Tg := ⟨h2, h1⟩
    rw [hBTg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hTgP : ∀ y ∈ Tg, ∀ p ∈ P, ⁅y, p⁆ ∈ C := by
    intro y hy p hp
    have hyP : ⁅y, p⁆ ∈ P := by
      have e : ⁅y, p⁆ = (y * p * y⁻¹) * p⁻¹ := rfl
      rw [e]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTgNP y hy) p).mp hp) (P.inv_mem hp)
    refine ⟨hyP, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    have hey : e * y⁻¹ = y⁻¹ * e := by
      have := hTgPg y⁻¹ (Tg.inv_mem hy) e (hBgPg (hEBg he))
      exact this.symm
    have h1 : ⁅p, ⁅e⁻¹, y⁻¹⁆⁆ = 1 := by
      have : ⁅e⁻¹, y⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        have := hTgPg y⁻¹ (Tg.inv_mem hy) e⁻¹ ((conjSubgroup g P).inv_mem (hBgPg (hEBg he)))
        exact this.symm
      rw [this, commutatorElement_one_right]
    have h2 : ⁅y⁻¹, ⁅p⁻¹, e⁆⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hTgB y⁻¹ (Tg.inv_mem hy) _ (H.commutator_mem (H.P_le_Q (P.inv_mem hp))
        (H.P_le_Q (hEP he)))
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (commutator_eq_one_of_rotate (x := y) (y := p) (z := e) h1 h2)
  have hTgZ : ∀ y ∈ Tg, ∀ z ∈ C, (∀ c ∈ C, z * c = c * z) → y * z = z * y := by
    intro y hy z hz hzc
    have hwTg : ⁅y, z⁆ ∈ Tg := by
      have e : ⁅y, z⁆ = y * (z * y⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact Tg.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hCNTg z hz) y⁻¹).mp (Tg.inv_mem hy))
    have hwP : ⁅y, z⁆ ∈ P := by
      have e : ⁅y, z⁆ = (y * z * y⁻¹) * z⁻¹ := rfl
      rw [e]
      exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTgNP y hy) z).mp hz.1) (P.inv_mem hz.1)
    have hwcen : ∀ p ∈ P, p * ⁅y, z⁆ = ⁅y, z⁆ * p := by
      intro p hp
      have h1 : ⁅z, ⁅p⁻¹, y⁻¹⁆⁆ = 1 := by
        have hmem : ⁅p⁻¹, y⁻¹⁆ ∈ C := by
          have := C.inv_mem (hTgP y⁻¹ (Tg.inv_mem hy) p⁻¹ (P.inv_mem hp))
          rwa [commutatorElement_inv] at this
        exact commutatorElement_eq_one_iff_mul_comm.mpr (hzc _ hmem)
      have h2 : ⁅y⁻¹, ⁅z⁻¹, p⁆⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hTgB y⁻¹ (Tg.inv_mem hy) _ (H.commutator_mem (H.P_le_Q (P.inv_mem hz.1))
          (H.P_le_Q hp))
      exact commutatorElement_eq_one_iff_mul_comm.mp
        (commutator_eq_one_of_rotate (x := y) (y := z) (z := p) h1 h2)
    have hwB : ⁅y, z⁆ ∈ B := by
      have : ⁅y, z⁆ ∈ P ⊓ Subgroup.centralizer (P : Set G) :=
        ⟨hwP, Subgroup.mem_centralizer_iff.mpr hwcen⟩
      rwa [H.inf_centralizer_P] at this
    have : ⁅y, z⁆ ∈ B ⊓ Tg := ⟨hwB, hwTg⟩
    rw [hBTg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hCsq : ∀ y ∈ Tg, ∀ c ∈ C, c * y ^ 2 = y ^ 2 * c := by
    intro y hy c hc
    set κ := ⁅y, c⁆ with hκ
    have hκC : κ ∈ C := hTgP y hy c hc.1
    have hκTg : κ ∈ Tg := by
      have e : κ = y * (c * y⁻¹ * c⁻¹) := by rw [hκ]; simp only [commutatorElement_def]; group
      rw [e]
      exact Tg.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hCNTg c hc) y⁻¹).mp (Tg.inv_mem hy))
    have hyκ : y * κ = κ * y := hTgZ y hy κ hκC (hTgC κ hκTg hκC)
    have hκ2 : κ * κ ∈ B := by
      rw [← sq]
      exact H.sq_mem (H.P_le_Q hκC.1)
    have e : ⁅y ^ 2, c⁆ = κ * κ := by
      have e0 : ⁅y * y, c⁆ = y * κ * y⁻¹ * κ := by
        rw [hκ]; simp only [commutatorElement_def]; group
      rw [sq, e0, hyκ]
      group
    have hy2Bg : y ^ 2 ∈ Bg := by
      rw [hBgdef, mem_conjSubgroup]
      have hy' : g⁻¹ * y * g ∈ T := by
        have := hy
        rwa [hTgdef, mem_conjSubgroup] at this
      rw [show g⁻¹ * y ^ 2 * g = (g⁻¹ * y * g) ^ 2 by rw [sq, sq]; group]
      exact H.sq_mem (H.T_le_Q hy')
    have hκ2Bg : κ * κ ∈ Bg := by
      rw [← e]
      have e2 : ⁅y ^ 2, c⁆ = y ^ 2 * (c * (y ^ 2)⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e2]
      exact Bg.mul_mem hy2Bg ((Subgroup.mem_normalizer_iff.mp (hCNBg c hc) _).mp
        (Bg.inv_mem hy2Bg))
    have : κ * κ ∈ B ⊓ Bg := ⟨hκ2, hκ2Bg⟩
    rw [hBBg, Subgroup.mem_bot] at this
    have h3 : ⁅y ^ 2, c⁆ = 1 := by rw [e, this]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
  have hmhoT : CFSG.GroupTheory.HuppertProduct.mho T 2 = B :=
    H.mho_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  have hCBg : ∀ c ∈ C, ∀ a ∈ Bg, c * a = a * c := by
    intro c hc a ha
    have hmho : B ≤ Subgroup.centralizer ({g⁻¹ * c * g} : Set G) := by
      rw [← hmhoT]
      refine CFSG.GroupTheory.HuppertProduct.mho_le_of_forall fun t ht => ?_
      have hy : g * t * g⁻¹ ∈ Tg := by
        rw [hTgdef, mem_conjSubgroup, show g⁻¹ * (g * t * g⁻¹) * g = t by group]
        exact ht
      have h1 := hCsq _ hy c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t ^ 2 * (g⁻¹ * c * g) = g⁻¹ * ((g * t * g⁻¹) ^ 2 * c) * g := by
            rw [sq, sq]; group
        _ = g⁻¹ * (c * (g * t * g⁻¹) ^ 2) * g := by rw [h1]
        _ = (g⁻¹ * c * g) * t ^ 2 := by rw [sq, sq]; group
    have ha' : g⁻¹ * a * g ∈ B := by
      have := ha
      rwa [hBgdef, mem_conjSubgroup] at this
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hmho ha')
    calc c * a = g * ((g⁻¹ * c * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * (g⁻¹ * c * g)) * g⁻¹ := by rw [← h]
      _ = a * c := by group
  have hTP : T ≤ Subgroup.normalizer (P : Set G) := le_normalizer_of_comm fun t ht p hp =>
    (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) p hp).symm
  refine H.le_Q_of_root hCen hU hBgM hEBg (hEP.trans H.P_le_Q) hE ?_
  intro c hcQ hcN a ha
  have hcQ' := hcQ
  rw [H.Q_eq_sup] at hcQ'
  obtain ⟨p, hp, t, ht, rfl⟩ := exists_mul_of_mem_sup hTP hcQ'
  have htE : ∀ e ∈ E, t * e * t⁻¹ = e := fun e he => by
    have := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) e (hEP he)
    calc t * e * t⁻¹ = (t * e) * t⁻¹ := rfl
      _ = (e * t) * t⁻¹ := by rw [← this]
      _ = e := by group
  have hpC : p ∈ C := by
    refine ⟨hp, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    have h1 : p * e * p⁻¹ ∈ E := by
      have := hcN e he
      rwa [show p * t * e * (p * t)⁻¹ = p * (t * e * t⁻¹) * p⁻¹ by group, htE e he] at this
    have h2 : ⁅p, e⁆ ∈ E := by
      have : ⁅p, e⁆ = (p * e * p⁻¹) * e⁻¹ := rfl
      rw [this]
      exact E.mul_mem h1 (E.inv_mem he)
    have h3 : ⁅p, e⁆ ∈ B := H.commutator_mem (H.P_le_Q hp) (H.P_le_Q (hEP he))
    have h4 : ⁅p, e⁆ ∈ B ⊓ Bg := ⟨h3, hEBg h2⟩
    rw [hBBg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
    exact h4.symm
  have h1 := hCBg p hpC a ha
  have h2 := hTBg t ht a ha
  calc p * t * a = p * (t * a) := by group
    _ = p * (a * t) := by rw [h2]
    _ = (p * a) * t := by group
    _ = (a * p) * t := by rw [h1]
    _ = a * (p * t) := by group


theorem tim78_4_4 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∀ g : G, conjSubgroup g B ⊓ P ≠ ⊥ → conjSubgroup g B ≤ P := by
  intro g hE
  by_contra hBgP
  set Bg := conjSubgroup g B with hBgdef
  set Tg := conjSubgroup g T with hTgdef
  set Pg := conjSubgroup g P with hPgdef
  have hBgB : Bg ≠ B := fun h => hBgP (h ▸ H.B_le_P)
  have hBBg : B ⊓ Bg = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB
  obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heBg : e ∈ Bg := (Subgroup.mem_inf.mp heE).1
  have heP : e ∈ P := (Subgroup.mem_inf.mp heE).2
  have hTMg : T ≤ conjSubgroup g M := fun t ht =>
    H.centralizer_le_conj heBg he1' (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P ht) e heP).symm)
  have hBgM : Bg ≤ M := H.conj_le_M_of_le_conj (H.B_le_T.trans hTMg)
  have h43 := H.tim78_4_3 hCen hU
  have hBgT : Bg ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huBg, huT⟩ := Subgroup.mem_inf.mp hu
    have hu' : g⁻¹ * u * g ∈ B := by
      have := huBg
      rwa [hBgdef, mem_conjSubgroup] at this
    have h1 := h43 _ hu' g (by rwa [show g * (g⁻¹ * u * g) * g⁻¹ = u by group])
    rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group] at h1
    have : u ∈ B ⊓ Bg := ⟨h1, huBg⟩
    rwa [hBBg] at this
  have hBTg : B ⊓ Tg = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨hbB, hbTg⟩ := Subgroup.mem_inf.mp hb
    have hb' : g⁻¹ * b * g ∈ T := by
      have := hbTg
      rwa [hTgdef, mem_conjSubgroup] at this
    have h1 := h43 b hbB g⁻¹ (by rwa [inv_inv])
    rw [inv_inv] at h1
    have hbBg : b ∈ Bg := by
      rw [hBgdef, mem_conjSubgroup]
      exact h1
    have : b ∈ B ⊓ Bg := ⟨hbB, hbBg⟩
    rwa [hBBg] at this
  have hTNBg : ∀ t ∈ T, t ∈ Subgroup.normalizer (Bg : Set G) := fun t ht => by
    rw [hBgdef, H.normalizer_conj_eq]
    exact hTMg ht
  have hTBgc : ∀ t ∈ T, ∀ a ∈ Bg, t * a = a * t := by
    intro t ht a ha
    have h1 : ⁅t, a⁆ ∈ Bg := by
      have e : ⁅t, a⁆ = (t * a * t⁻¹) * a⁻¹ := rfl
      rw [e]
      exact Bg.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTNBg t ht) a).mp ha) (Bg.inv_mem ha)
    have h2 : ⁅t, a⁆ ∈ T := by
      have e : ⁅t, a⁆ = t * (a * t⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact T.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_T (hBgM ha)) t⁻¹).mp
        (T.inv_mem ht))
    have h3 : ⁅t, a⁆ ∈ Bg ⊓ T := ⟨h1, h2⟩
    rw [hBgT, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hTNTg : T ≤ Subgroup.normalizer (Tg : Set G) := fun t ht =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T (hTMg ht)
  have hTNPg : T ≤ Subgroup.normalizer (Pg : Set G) := fun t ht =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_P (hTMg ht)
  have hTgT : Tg ⊓ T = ⊥ := by
    by_contra hne
    have hne' : T ⊓ Tg ≠ ⊥ := by rwa [inf_comm]
    obtain ⟨b, hbD, hbB, hb1⟩ := H.exists_mem_B_of_normalizes H.T_le_Q H.B_le_T
      H.M_le_normalizer_T (inf_le_left : T ⊓ Tg ≤ T) hne'
      (fun t ht => mem_normalizer_inf (Subgroup.le_normalizer ht) (hTNTg ht))
    have : b ∈ B ⊓ Tg := ⟨hbB, hbD.2⟩
    rw [hBTg, Subgroup.mem_bot] at this
    exact hb1 this
  have hmhoT : CFSG.GroupTheory.HuppertProduct.mho T 2 = B :=
    H.mho_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  have hBMg : B ≤ conjSubgroup g M := H.B_le_T.trans hTMg
  by_cases hTPg : Pg ⊓ T = ⊥
  ·
    have hXP := fun {y : G} (hy : y ∈ T) =>
      H.comm_sq_mem_conj H.B_le_P H.P_le_Q hTNPg hTPg hy
    have hXT := fun {y : G} (hy : y ∈ T) =>
      H.comm_sq_mem_conj H.B_le_T H.T_le_Q hTNTg hTgT hy
    have hQg : conjSubgroup g Q = Pg ⊔ Tg := by
      rw [H.Q_eq_sup]
      exact Subgroup.map_sup _ _ _
    have hTgNPg : Tg ≤ Subgroup.normalizer (Pg : Set G) := le_normalizer_of_comm fun s hs a ha =>
      H.conj_T_le_centralizer_conj_P g s hs a ha
    have hBgNormal : ∀ m ∈ conjSubgroup g M, ∀ b ∈ Bg, m * b * m⁻¹ ∈ Bg := fun m hm b hb =>
      (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_conj_of_mem_conj H.M_le_normalizer_B hm) b).mp hb
    have hgen : ∀ y ∈ T, ∀ s ∈ conjSubgroup g Q, ⁅y ^ 2, s⁆ ∈ Bg := by
      intro y hy s hs
      have hPcomm : ∀ s' ∈ Pg, ⁅y ^ 2, s'⁆ ∈ Bg := by
        intro s' hs'
        have hw := hXP hy s' hs'
        have hs'M : s' ∈ conjSubgroup g M := by
          rw [hPgdef, mem_conjSubgroup] at hs'
          rw [mem_conjSubgroup]
          exact H.P_le_M hs'
        have e : ⁅y ^ 2, s'⁆ = s' * (s'⁻¹ * (y ^ 2 * s' * (y ^ 2)⁻¹)) * s'⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hBgNormal s' hs'M _ hw
      have hTcomm : ∀ s' ∈ Tg, ⁅y ^ 2, s'⁆ ∈ Bg := by
        intro s' hs'
        have hw := hXT hy s' hs'
        have hs'M : s' ∈ conjSubgroup g M := by
          rw [hTgdef, mem_conjSubgroup] at hs'
          rw [mem_conjSubgroup]
          exact H.Q_le_M (H.T_le_Q hs')
        have e : ⁅y ^ 2, s'⁆ = s' * (s'⁻¹ * (y ^ 2 * s' * (y ^ 2)⁻¹)) * s'⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hBgNormal s' hs'M _ hw
      rw [hQg] at hs
      obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := exists_mul_of_mem_sup hTgNPg hs
      have hs₁M : s₁ ∈ conjSubgroup g M := by
        rw [hPgdef, mem_conjSubgroup] at hs₁
        rw [mem_conjSubgroup]
        exact H.P_le_M hs₁
      have e : ⁅y ^ 2, s₁ * s₂⁆ = ⁅y ^ 2, s₁⁆ * (s₁ * ⁅y ^ 2, s₂⁆ * s₁⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Bg.mul_mem (hPcomm s₁ hs₁) (hBgNormal s₁ hs₁M _ (hTcomm s₂ hs₂))
    have hall : ∀ b ∈ B, ∀ s ∈ conjSubgroup g Q, ⁅b, s⁆ ∈ Bg := by
      intro b hb s hs
      rw [← hmhoT] at hb
      refine Subgroup.closure_induction (p := fun b _ => ∀ s ∈ conjSubgroup g Q, ⁅b, s⁆ ∈ Bg)
        ?_ ?_ ?_ ?_ hb s hs
      · rintro _ ⟨y, hy, rfl⟩
        exact fun s hs => hgen y hy s hs
      · intro s _
        rw [commutatorElement_one_left]
        exact Bg.one_mem
      · intro b₁ b₂ hb₁ hb₂ ih₁ ih₂ s hs
        have hb₁B : b₁ ∈ B := hmhoT ▸ hb₁
        have e : ⁅b₁ * b₂, s⁆ = b₁ * ⁅b₂, s⁆ * b₁⁻¹ * ⁅b₁, s⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Bg.mul_mem (hBgNormal b₁ (hBMg hb₁B) _ (ih₂ s hs)) (ih₁ s hs)
      · intro b hb ih s hs
        have hbB : b ∈ B := hmhoT ▸ hb
        have e : ⁅b⁻¹, s⁆ = b⁻¹ * ⁅b, s⁆⁻¹ * b := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := hBgNormal b⁻¹ (hBMg (B.inv_mem hbB)) _ (Bg.inv_mem (ih s hs))
        rwa [inv_inv] at this
    have hBQg := H.le_conj_Q_of_commutator_mem hBMg hall
    have h1 : conjSubgroup g⁻¹ B ≤ Q := by
      intro z hz
      rw [mem_conjSubgroup, inv_inv] at hz
      have := hBQg hz
      rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
    have h2 : Bg ≤ Q := by
      have := H.conj_inv_le_Q h1
      rwa [inv_inv] at this
    exact hBgP (H.conj_le_P h2)
  ·
    have hne' : T ⊓ Pg ≠ ⊥ := by rwa [inf_comm]
    obtain ⟨u, huD, huB, hu1⟩ := H.exists_mem_B_of_normalizes H.T_le_Q H.B_le_T
      H.M_le_normalizer_T (inf_le_left : T ⊓ Pg ≤ T) hne'
      (fun t ht => mem_normalizer_inf (Subgroup.le_normalizer ht) (hTNPg ht))
    have huPg : u ∈ Pg := huD.2
    have hTgM : Tg ≤ M := fun s hs =>
      H.normalizer_eq_and_centralizer_le.2 u huB hu1
        (Subgroup.mem_centralizer_singleton_iff.mpr (H.conj_T_le_centralizer_conj_P g s hs u huPg))
    have hTgB : ∀ s ∈ Tg, ∀ b ∈ B, s * b = b * s := by
      intro s hs b hb
      have hsM := hTgM hs
      have hle : B ≤ Subgroup.centralizer ({s} : Set G) := by
        rw [← hmhoT]
        refine CFSG.GroupTheory.HuppertProduct.mho_le_of_forall fun t ht => ?_
        have hw := H.comm_sq_mem_conj H.B_le_T H.T_le_Q hTNTg hTgT ht s hs
        have hw2 : s⁻¹ * (t ^ 2 * s * (t ^ 2)⁻¹) ∈ B := by
          have e : s⁻¹ * (t ^ 2 * s * (t ^ 2)⁻¹) = (s⁻¹ * t ^ 2 * s) * (t ^ 2)⁻¹ := by group
          have h5 : s⁻¹ * t ^ 2 * s ∈ B := by
            have := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B (M.inv_mem hsM))
              (t ^ 2)).mp (H.sq_mem (H.T_le_Q ht))
            rwa [inv_inv] at this
          rw [e]
          exact B.mul_mem h5 (B.inv_mem (H.sq_mem (H.T_le_Q ht)))
        have : s⁻¹ * (t ^ 2 * s * (t ^ 2)⁻¹) ∈ B ⊓ Bg := ⟨hw2, hw⟩
        rw [hBBg, Subgroup.mem_bot] at this
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h3 : t ^ 2 * s * (t ^ 2)⁻¹ = s := by
          calc t ^ 2 * s * (t ^ 2)⁻¹ = s * (s⁻¹ * (t ^ 2 * s * (t ^ 2)⁻¹)) := by group
            _ = s := by rw [this]; group
        calc t ^ 2 * s = (t ^ 2 * s * (t ^ 2)⁻¹) * t ^ 2 := by group
          _ = s * t ^ 2 := by rw [h3]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
      exact this.symm
    have hQ := H.le_Q_of_conj_T_centralizes hCen hU hBBg hE hBgM hTBgc hBTg hTgB hTgM
    exact hBgP (H.conj_le_P hQ)

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
