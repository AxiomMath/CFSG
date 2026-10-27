module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

theorem IrrOn.mono {N₁ N₂ E : Subgroup G} (hirr : IrrOn N₁ E) (h : N₁ ≤ N₂) :
    IrrOn N₂ E :=
  fun W hW hNW => hirr W hW (h.trans hNW)

theorem le_normalizer_inf_conjSubgroup {U₀ M₁ : Subgroup G} {y : G}
    (hU₀ : M₁ ≤ Subgroup.normalizer (U₀ : Set G))
    (hy : y ∈ Subgroup.normalizer (M₁ : Set G)) :
    M₁ ≤ Subgroup.normalizer (U₀ ⊓ conjSubgroup U₀ y : Set G) := by
  have hLmap : M₁.map (MulAut.conj y⁻¹).toMonoidHom = M₁ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer (M₁ : Set G)).inv_mem hy)
  have hmap := Subgroup.map_normalizer_eq_of_bijective U₀
    (f := (MulAut.conj y⁻¹).toMonoidHom) (MulAut.conj y⁻¹).bijective
  have hNVy : M₁ ≤ Subgroup.normalizer (conjSubgroup U₀ y : Set G) := by
    calc M₁ = M₁.map (MulAut.conj y⁻¹).toMonoidHom := hLmap.symm
      _ ≤ (Subgroup.normalizer (U₀ : Set G)).map (MulAut.conj y⁻¹).toMonoidHom :=
          Subgroup.map_mono hU₀
      _ = Subgroup.normalizer (conjSubgroup U₀ y : Set G) := hmap
  exact (le_inf hU₀ hNVy).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem conjClosure_le_normalizer {N E F : Subgroup G}
    (hN : N ≤ Subgroup.normalizer (F : Set G))
    (hE : E ≤ Subgroup.normalizer (F : Set G)) :
    conjClosure N E ≤ Subgroup.normalizer (F : Set G) :=
  uc22p22v_conjClosure_le (hN.trans Subgroup.le_normalizer) hE

theorem conjSubgroup_le_of_mem_normalizer {A B : Subgroup G} {y : G}
    (hAB : A ≤ B) (hy : y ∈ Subgroup.normalizer (B : Set G)) :
    conjSubgroup A y ≤ B := by
  have hB : conjSubgroup B y = B := conjSubgroup_eq_iff_mem_normalizer.mpr hy
  rw [← hB]
  exact Subgroup.map_mono hAB

theorem inf_conjSubgroup_eq_bot_of_irreducible {U₀ M₁ : Subgroup G} {y : G}
    (hirr : IrrOn M₁ U₀) (hU₀ : M₁ ≤ Subgroup.normalizer (U₀ : Set G))
    (hy : y ∈ Subgroup.normalizer (M₁ : Set G))
    (hyU₀ : conjSubgroup U₀ y ≠ U₀) :
    U₀ ⊓ conjSubgroup U₀ y = ⊥ := by
  have hInv : M₁ ≤ Subgroup.normalizer (U₀ ⊓ conjSubgroup U₀ y : Set G) :=
    le_normalizer_inf_conjSubgroup hU₀ hy
  rcases hirr (U₀ ⊓ conjSubgroup U₀ y) inf_le_left hInv with hbot | htop
  · exact hbot
  · exfalso
    have hle : U₀ ≤ conjSubgroup U₀ y := inf_eq_left.mp htop
    have hcard : Nat.card (conjSubgroup U₀ y) = Nat.card U₀ := E3.card_conjSubgroup _ _
    exact hyU₀ (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

theorem mem_normalizer_inf_conjClosure {M Y L : Subgroup G} {y : G}
    (hyM : y ∈ M) (hyY : y ∈ Y) :
    y ∈ Subgroup.normalizer (M ⊓ conjClosure Y L : Set G) := by
  have hmaps : M.map (MulAut.conj y).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hyM)
  have hcmaps : (conjClosure Y L).map (MulAut.conj y).toMonoidHom = conjClosure Y L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (uc22p22v_le_normalizer_conjClosure Y L hyY)
  have hMaps : (M ⊓ conjClosure Y L).map (MulAut.conj y).toMonoidHom =
      M ⊓ conjClosure Y L := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective, hmaps, hcmaps]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMaps

namespace Ctx23L

theorem inf_conjClosure_eq_U0 (c : Ctx23L D Ch) {L₁ N₂ : Subgroup G}
    (hL01 : c.L0 ≤ L₁) (hL1N : L₁ ≤ N₂)
    (hUV : D.U ⊓ conjClosure N₂ D.Z = c.U0)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) :
    D.U ⊓ conjClosure L₁ D.Z = c.U0 := by
  have hU0leV : c.U0 ≤ conjClosure L₁ D.Z := by
    rw [hU0]
    exact uc22p22v_conjClosure_mono (inf_le_left.trans hL01) D.Z
  refine le_antisymm ?_ (le_inf (hUV ▸ inf_le_left) hU0leV)
  calc D.U ⊓ conjClosure L₁ D.Z ≤ D.U ⊓ conjClosure N₂ D.Z :=
        inf_le_inf_left D.U (uc22p22v_conjClosure_mono hL1N D.Z)
    _ = c.U0 := hUV

private theorem eq_conjClosure_of_inf_U_ne_bot (c : Ctx23L D Ch) {L₁ X : Subgroup G}
    (hL01 : c.L0 ≤ L₁) (hV1U : D.U ⊓ conjClosure L₁ D.Z = c.U0)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z)
    (hirr : IrrOn (c.L0 ⊓ D.M) c.U0)
    (hX : X ≤ conjClosure L₁ D.Z)
    (hNX : L₁ ≤ Subgroup.normalizer (X : Set G))
    (hne : X ⊓ D.U ≠ ⊥) :
    X = conjClosure L₁ D.Z := by
  have hXU : X ⊓ D.U ≤ c.U0 := by
    refine (inf_le_inf hX le_rfl).trans ?_
    rw [inf_comm (conjClosure L₁ D.Z) D.U, hV1U]
  have hL0M_le_NX : c.L0 ⊓ D.M ≤ Subgroup.normalizer (X : Set G) :=
    (inf_le_left.trans hL01).trans hNX
  have hL0M_le_NU : c.L0 ⊓ D.M ≤ Subgroup.normalizer (D.U : Set G) :=
    inf_le_right.trans (le_normalizer_uCore D.M D.T)
  have hN : c.L0 ⊓ D.M ≤ Subgroup.normalizer (X ⊓ D.U : Set G) :=
    (le_inf hL0M_le_NX hL0M_le_NU).trans Subgroup.inf_normalizer_le_normalizer_inf
  rcases hirr (X ⊓ D.U) hXU hN with hbot | htop
  · exact absurd hbot hne
  · have hZleU0 : D.Z ≤ c.U0 := by
      rw [hU0]
      exact uc22p22v_le_conjClosure (c.L0 ⊓ D.M) D.Z
    have hZleXU : D.Z ≤ X ⊓ D.U := htop.symm ▸ hZleU0
    have hZleX : D.Z ≤ X := fun z hz => (Subgroup.mem_inf.mp (hZleXU hz)).1
    exact le_antisymm hX (uc22p22v_conjClosure_le hNX hZleX)

private theorem exists_conjSubgroup_eq_bot_of_moves (c : Ctx23L D Ch) {L₁ : Subgroup G} {y : G}
    (hL01 : c.L0 ≤ L₁) (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z)
    (hirr : IrrOn (c.L0 ⊓ D.M) c.U0)
    (hV1U : D.U ⊓ conjClosure L₁ D.Z = c.U0)
    (hU0leU : c.U0 ≤ D.U)
    (hyM : y ∈ D.M) (hyNL : y ∈ Subgroup.normalizer (L₁ : Set G))
    (hyV : conjSubgroup (conjClosure L₁ D.Z) y ≠ conjClosure L₁ D.Z) :
    ∃ y ∈ D.M, c.U0 ⊓ conjSubgroup c.U0 y = ⊥ ∧ conjSubgroup c.U0 y ≤ D.U := by
  have hU0leV1 : c.U0 ≤ conjClosure L₁ D.Z := by
    rw [hU0]
    exact uc22p22v_conjClosure_mono (inf_le_left.trans hL01) D.Z
  have hL1NV1 : L₁ ≤ Subgroup.normalizer (conjClosure L₁ D.Z : Set G) :=
    uc22p22v_le_normalizer_conjClosure L₁ D.Z
  have hL1NX : L₁ ≤ Subgroup.normalizer
      (conjClosure L₁ D.Z ⊓ conjSubgroup (conjClosure L₁ D.Z) y : Set G) :=
    le_normalizer_inf_conjSubgroup hL1NV1 hyNL
  have hX_ne : conjClosure L₁ D.Z ⊓ conjSubgroup (conjClosure L₁ D.Z) y ≠
      conjClosure L₁ D.Z := by
    intro hXeq
    have hle : conjClosure L₁ D.Z ≤ conjSubgroup (conjClosure L₁ D.Z) y := inf_eq_left.mp hXeq
    have hcard : Nat.card (conjSubgroup (conjClosure L₁ D.Z) y) =
        Nat.card (conjClosure L₁ D.Z) := E3.card_conjSubgroup _ _
    exact hyV (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
  have hXU_bot : conjClosure L₁ D.Z ⊓ conjSubgroup (conjClosure L₁ D.Z) y ⊓ D.U = ⊥ := by
    by_contra hne
    exact hX_ne (eq_conjClosure_of_inf_U_ne_bot c hL01 hV1U hU0 hirr inf_le_left hL1NX hne)
  refine ⟨y, hyM, ?_, conjSubgroup_le_of_mem_normalizer hU0leU
    (le_normalizer_uCore D.M D.T hyM)⟩
  refine le_bot_iff.mp ?_
  calc c.U0 ⊓ conjSubgroup c.U0 y
      ≤ (conjClosure L₁ D.Z ⊓ conjSubgroup (conjClosure L₁ D.Z) y) ⊓ D.U :=
        le_inf (inf_le_inf hU0leV1 (Subgroup.map_mono hU0leV1))
          (inf_le_left.trans hU0leU)
    _ = ⊥ := by rw [hXU_bot]

private theorem two_mul_le_rk_of_exists_conj (c : Ctx23L D Ch) {k : ℕ}
    (hcard : Nat.card c.U0 = 2 ^ k) (hlt : c.U0 < D.U)
    (hex : ∃ y ∈ D.M, c.U0 ⊓ conjSubgroup c.U0 y = ⊥ ∧
      conjSubgroup c.U0 y ≤ D.U) :
    2 * k ≤ rk ↥D.U := by
  obtain ⟨y, -, hbot, hyU⟩ := hex
  have hUel : IsElemAbelian 2 D.U :=
    (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2
  have hcomm : ∀ x ∈ c.U0, ∀ z ∈ conjSubgroup c.U0 y, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hUel.1.is_comm.comm ⟨x, hlt.le hx⟩ ⟨z, hyU hz⟩)
  have hcardUy : Nat.card (conjSubgroup c.U0 y) = 2 ^ k := by
    rw [E3.card_conjSubgroup, hcard]
  have hcard_sup : Nat.card ↥(c.U0 ⊔ conjSubgroup c.U0 y) = 2 ^ (2 * k) := by
    have hprod :=
      (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute c.U0 (conjSubgroup c.U0 y)
        hcomm).1
    rw [hbot, Subgroup.card_bot, mul_one, hcard, hcardUy, ← pow_add] at hprod
    rw [hprod]
    congr 1
    ring
  have hrk : rk ↥(c.U0 ⊔ conjSubgroup c.U0 y) = 2 * k := by
    rw [rk, hcard_sup, padicValNat.prime_pow]
  calc 2 * k = rk ↥(c.U0 ⊔ conjSubgroup c.U0 y) := hrk.symm
    _ ≤ rk ↥D.U := rk_mono (sup_le hlt.le hyU)

private theorem exists_normalizer_data_of_fixes (c : Ctx23L D Ch) {W L₁ : Subgroup G} {y : G}
    (hL01 : c.L0 ≤ L₁)
    (hL₁ : L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (W : Set G)))
    (hV1U : D.U ⊓ conjClosure L₁ D.Z = c.U0)
    (hyY : y ∈ D.M ⊓ Subgroup.normalizer (W : Set G))
    (hfix : ∀ z ∈ D.M ⊓ Subgroup.normalizer (W : Set G),
      z ∈ Subgroup.normalizer (L₁ : Set G) →
      conjSubgroup (conjClosure L₁ D.Z) z = conjClosure L₁ D.Z)
    (hN₁ : D.M ⊓ conjClosure (Subgroup.normalizer (W : Set G)) L₁ ≤
      Subgroup.normalizer (L₁ : Set G)) :
    ∃ M₁ : Subgroup G, M₁ ≤ Subgroup.normalizer (c.U0 : Set G) ∧
      c.L0 ⊓ D.M ≤ M₁ ∧ y ∈ Subgroup.normalizer (M₁ : Set G) := by
  let Y : Subgroup G := D.M ⊓ Subgroup.normalizer (W : Set G)
  let M₁ : Subgroup G := D.M ⊓ conjClosure Y L₁
  have hL1H : L₁ ≤ Subgroup.normalizer (W : Set G) :=
    CFSG.Quasithin.A3.subnormal_le hL₁.2
  have hM1_le_Y : M₁ ≤ Y := by
    have hconjY_le_NW : conjClosure Y L₁ ≤ Subgroup.normalizer (W : Set G) :=
      conjClosure_le_normalizer inf_le_right hL1H
    exact le_inf inf_le_left (inf_le_right.trans hconjY_le_NW)
  have hM1_le_NV1 : M₁ ≤ Subgroup.normalizer (conjClosure L₁ D.Z : Set G) := by
    intro m hm
    change m ∈ D.M ⊓ conjClosure Y L₁ at hm
    have hmH : m ∈ D.M ⊓ conjClosure (Subgroup.normalizer (W : Set G)) L₁ :=
      Subgroup.mem_inf.mpr ⟨hm.1, (uc22p22v_conjClosure_mono inf_le_right L₁) hm.2⟩
    exact (conjSubgroup_eq_iff_mem_normalizer).mp (hfix m (hM1_le_Y hm) (hN₁ hmH))
  have hM1_le_NU : M₁ ≤ Subgroup.normalizer (D.U : Set G) :=
    inf_le_left.trans (le_normalizer_uCore D.M D.T)
  have hM1_le_NU0 : M₁ ≤ Subgroup.normalizer (c.U0 : Set G) := by
    have hle := (le_inf hM1_le_NU hM1_le_NV1).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    rwa [hV1U] at hle
  have hL0M_le_conj : c.L0 ⊓ D.M ≤ conjClosure Y L₁ :=
    (inf_le_left.trans hL01).trans (uc22p22v_le_conjClosure Y L₁)
  have hL0M_le_M1 : c.L0 ⊓ D.M ≤ M₁ := le_inf inf_le_right hL0M_le_conj
  exact ⟨M₁, hM1_le_NU0, hL0M_le_M1,
    mem_normalizer_inf_conjClosure (M := D.M) (Y := Y) hyY.1 hyY⟩

private theorem exists_conjSubgroup_eq_bot_of_fixes (c : Ctx23L D Ch) {W L₁ : Subgroup G} {y : G}
    (hL01 : c.L0 ≤ L₁)
    (hL₁ : L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (W : Set G)))
    (hirr : IrrOn (c.L0 ⊓ D.M) c.U0)
    (hV1U : D.U ⊓ conjClosure L₁ D.Z = c.U0)
    (hU0leU : c.U0 ≤ D.U)
    (hyY : y ∈ D.M ⊓ Subgroup.normalizer (W : Set G))
    (hfix : ∀ z ∈ D.M ⊓ Subgroup.normalizer (W : Set G),
      z ∈ Subgroup.normalizer (L₁ : Set G) →
      conjSubgroup (conjClosure L₁ D.Z) z = conjClosure L₁ D.Z)
    (hyU0 : conjSubgroup c.U0 y ≠ c.U0)
    (hN₁ : D.M ⊓ conjClosure (Subgroup.normalizer (W : Set G)) L₁ ≤
      Subgroup.normalizer (L₁ : Set G)) :
    ∃ y ∈ D.M, c.U0 ⊓ conjSubgroup c.U0 y = ⊥ ∧ conjSubgroup c.U0 y ≤ D.U := by
  obtain ⟨M₁, hM1_le_NU0, hL0M_le_M1, hyM1⟩ :=
    exists_normalizer_data_of_fixes c hL01 hL₁ hV1U hyY hfix hN₁
  have hinter : c.U0 ⊓ conjSubgroup c.U0 y = ⊥ :=
    inf_conjSubgroup_eq_bot_of_irreducible (IrrOn.mono hirr hL0M_le_M1) hM1_le_NU0 hyM1 hyU0
  exact ⟨y, hyY.1, hinter,
    conjSubgroup_le_of_mem_normalizer hU0leU (le_normalizer_uCore D.M D.T hyY.1)⟩

theorem two_mul_le_rk_U (c : Ctx23L D Ch) {W L₁ N₂ : Subgroup G} {k : ℕ}
    (hL₁ : L₁ ∈ calLOf D.T D.M (Subgroup.normalizer (W : Set G))) (hL01 : c.L0 ≤ L₁)
    (hL1N : L₁ ≤ N₂)
    (hN₁ : D.M ⊓ conjClosure (Subgroup.normalizer (W : Set G)) L₁ ≤
      Subgroup.normalizer (L₁ : Set G))
    (hUY : D.U = conjClosure (D.M ⊓ Subgroup.normalizer (W : Set G)) D.Z)
    (hUV : D.U ⊓ conjClosure N₂ D.Z = c.U0)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hirr : IrrOn (c.L0 ⊓ D.M) c.U0)
    (hcard : Nat.card c.U0 = 2 ^ k) (hlt : c.U0 < D.U) :
    2 * k ≤ rk ↥D.U := by
  classical
  let Y : Subgroup G := D.M ⊓ Subgroup.normalizer (W : Set G)
  let V₁ : Subgroup G := conjClosure L₁ D.Z
  have hL1H : L₁ ≤ Subgroup.normalizer (W : Set G) := CFSG.Quasithin.A3.subnormal_le hL₁.2
  have hL0W : c.L0 ≤ Subgroup.normalizer (W : Set G) := hL01.trans hL1H
  have hL0M_le_Y : c.L0 ⊓ D.M ≤ Y := le_inf inf_le_right (inf_le_left.trans hL0W)
  have hU0leU : c.U0 ≤ D.U := by
    rw [hU0, hUY]
    exact uc22p22v_conjClosure_mono hL0M_le_Y D.Z
  have hV1U : D.U ⊓ V₁ = c.U0 := inf_conjClosure_eq_U0 c hL01 hL1N hUV hU0
  have hex_y : ∃ y ∈ Y, conjSubgroup c.U0 y ≠ c.U0 := by
    by_contra hcon
    push Not at hcon
    have hYleN : Y ≤ Subgroup.normalizer (c.U0 : Set G) := fun y hy =>
      (conjSubgroup_eq_iff_mem_normalizer).mp (hcon y hy)
    have hZleU0 : D.Z ≤ c.U0 := by
      rw [hU0]
      exact uc22p22v_le_conjClosure (c.L0 ⊓ D.M) D.Z
    have hDUle : D.U ≤ c.U0 := by
      rw [hUY]
      exact uc22p22v_conjClosure_le hYleN hZleU0
    exact (ne_of_lt hlt) (le_antisymm hDUle hlt.le).symm
  by_cases hcase : ∃ y ∈ Y ⊓ Subgroup.normalizer (L₁ : Set G),
      conjSubgroup V₁ y ≠ V₁
  · obtain ⟨y, hyY, hyV⟩ := hcase
    have hyM : y ∈ D.M := (show y ∈ D.M ⊓ Subgroup.normalizer (W : Set G) from hyY.1).1
    exact two_mul_le_rk_of_exists_conj c hcard hlt
      (exists_conjSubgroup_eq_bot_of_moves c hL01 hU0 hirr hV1U hU0leU hyM hyY.2 hyV)
  · push Not at hcase
    have hfix : ∀ z ∈ Y, z ∈ Subgroup.normalizer (L₁ : Set G) →
        conjSubgroup V₁ z = V₁ := fun z hz hzL =>
      hcase z (Subgroup.mem_inf.mpr ⟨hz, hzL⟩)
    obtain ⟨y, hyY, hyU0⟩ := hex_y
    exact two_mul_le_rk_of_exists_conj c hcard hlt
      (exists_conjSubgroup_eq_bot_of_fixes c hL01 hL₁ hirr hV1U hU0leU hyY hfix hyU0 hN₁)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
