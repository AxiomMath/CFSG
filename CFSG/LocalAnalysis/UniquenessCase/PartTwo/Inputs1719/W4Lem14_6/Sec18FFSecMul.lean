module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Quo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.K148
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open scoped commutatorElement

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}
variable {H : Subgroup G} {Y Z : Submodule (ZMod 2) V}

@[expose] noncomputable def secMul (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) :
    ↥H →* MulAut (Multiplicative (SecQ Y Z)) :=
  (CFSG.QuasithinUnique.Setup.Layer.binPsi
    (MulEquiv.refl (Multiplicative (SecQ Y Z)))).symm.toMonoidHom.comp (secHom hY hZ)

theorem secMul_apply (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) (h : ↥H)
    (q : Multiplicative (SecQ Y Z)) :
    secMul hY hZ h q = Multiplicative.ofAdd (secHom hY hZ h (Multiplicative.toAdd q)) := rfl

theorem binPsi_secMul (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) (h : ↥H) :
    CFSG.QuasithinUnique.Setup.Layer.binPsi (MulEquiv.refl (Multiplicative (SecQ Y Z)))
      (secMul hY hZ h) = secHom hY hZ h :=
  MulEquiv.apply_symm_apply _ _

@[expose] noncomputable def secMulImg (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    (D : Subgroup G) : Subgroup (MulAut (Multiplicative (SecQ Y Z))) :=
  (D.subgroupOf H).map (secMul hY hZ)

private theorem secImg_eq_map_secMulImg {hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y} {hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z}
    (D : Subgroup G) :
    secImg hY hZ D = (secMulImg hY hZ D).map
      (CFSG.QuasithinUnique.Setup.Layer.binPsi
        (MulEquiv.refl (Multiplicative (SecQ Y Z)))).toMonoidHom := by
  ext u
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨secMul hY hZ h, ⟨h, hh, rfl⟩, binPsi_secMul hY hZ h⟩
  · rintro ⟨x, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, hh, (binPsi_secMul hY hZ h).symm⟩

private theorem secMulImg_sup {hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y} {hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z}
    {L B : Subgroup G} (hLH : L ≤ H) (hBH : B ≤ H) :
    secMulImg hY hZ (L ⊔ B) = secMulImg hY hZ L ⊔ secMulImg hY hZ B := by
  simp only [secMulImg, Subgroup.subgroupOf_sup hLH hBH, Subgroup.map_sup]

theorem secMul_injective [Finite V] {L : Subgroup G} [IsSimpleGroup ↥L] (hLH : L ≤ H)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) :
    Function.Injective ((secMul hY hZ).comp (Subgroup.inclusion hLH)) := by
  let π : ↥L →* MulAut (Multiplicative (SecQ Y Z)) :=
    (secMul hY hZ).comp (Subgroup.inclusion hLH)
  have hker : π.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨l, hl, y, hy, hly⟩ := hnt
      have h1 : π ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      have h2 : secHom hY hZ (Subgroup.inclusion hLH ⟨l, hl⟩) = 1 := by
        rw [← binPsi_secMul hY hZ (Subgroup.inclusion hLH ⟨l, hl⟩)]
        simpa [π] using h1
      rw [secHom_eq_one_iff] at h2
      exact hly (by simpa using h2 y hy)
  exact (MonoidHom.ker_eq_bot_iff π).1 hker

@[expose] noncomputable def secMulEquiv [Finite V] {L : Subgroup G} [IsSimpleGroup ↥L]
    (hLH : L ≤ H) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z) : ↥L ≃* ↥(secMulImg hY hZ L) :=
  (MonoidHom.ofInjective (secMul_injective hLH hY hZ hnt)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, secMulImg, Subgroup.inclusion_range]))

theorem secMulEquiv_apply [Finite V] {L : Subgroup G} [IsSimpleGroup ↥L] (hLH : L ≤ H)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z)
    (l : ↥L) :
    ((secMulEquiv hLH hY hZ hnt l : ↥(secMulImg hY hZ L)) : MulAut (Multiplicative (SecQ Y Z))) =
      secMul hY hZ (Subgroup.inclusion hLH l) := rfl

theorem card_secMul_top [Finite V] (hZY : Z ≤ Y) :
    Nat.card (Multiplicative (SecQ Y Z)) = 2 ^ (finrank (ZMod 2) ↥Y - finrank (ZMod 2) ↥Z) := by
  rw [Nat.card_congr Multiplicative.toAdd, card_secQ hZY]

theorem card_fixV_secMulImg [Finite V] (hZY : Z ≤ Y) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y)
    (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) {D : Subgroup G} (hDH : D ≤ H) :
    Nat.card ↥(CFSG.Quasithin.fixV (secMulImg hY hZ D)) =
      2 ^ (finrank (ZMod 2) ↥(Y ⊓ P22x.modFix ρ Z D) - finrank (ZMod 2) ↥Z) := by
  have h1 : Nat.card ↥(CFSG.QuasithinUnique.Setup.Offender.fixGL (secImg hY hZ D)) =
      Nat.card ↥(CFSG.Quasithin.fixV (secMulImg hY hZ D)) := by
    have h := CFSG.QuasithinUnique.Setup.Layer.Actor.natCard_fixGL_map
      (θ := MulEquiv.refl (Multiplicative (SecQ Y Z))) (secMulImg hY hZ D)
    rwa [← secImg_eq_map_secMulImg D] at h
  rw [← h1]
  exact card_fix_secImg (hY := hY) (hZ := hZ) hZY hDH

theorem card_secMulImg_mul (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z) {D : Subgroup G}
    (hDH : D ≤ H) :
    Nat.card ↥(secMulImg hY hZ D) * Nat.card ↥(D ⊓ secKer ρ Y Z) = Nat.card ↥D := by
  have h1 : Nat.card ↥(secImg hY hZ D) = Nat.card ↥(secMulImg hY hZ D) := by
    rw [secImg_eq_map_secMulImg D]
    exact Subgroup.card_map_of_injective
      (CFSG.QuasithinUnique.Setup.Layer.binPsi
        (MulEquiv.refl (Multiplicative (SecQ Y Z)))).injective
  rw [← h1]
  exact card_secImg_mul (hY := hY) (hZ := hZ) hDH

theorem isIrrOn_secMulImg_sup {L B : Subgroup G} (hLH : L ≤ H) (hBH : B ≤ H) (hZY : Z ≤ Y)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    (hirr : ∀ W : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) W → Z ≤ W → W ≤ Y →
      W = Z ∨ W = Y) :
    CFSG.LocalAnalysis.RankThreeUC.IsIrrOn (secMulImg hY hZ L ⊔ secMulImg hY hZ B) := by
  intro W hW
  let U : Submodule (ZMod 2) (SecQ Y Z) :=
    { carrier := {q | Multiplicative.ofAdd q ∈ W}
      add_mem' := by
        intro a b ha hb
        have hm : Multiplicative.ofAdd a * Multiplicative.ofAdd b ∈ W :=
          W.mul_mem (show Multiplicative.ofAdd a ∈ W from ha)
            (show Multiplicative.ofAdd b ∈ W from hb)
        rwa [show Multiplicative.ofAdd a * Multiplicative.ofAdd b =
          Multiplicative.ofAdd (a + b) from rfl] at hm
      zero_mem' := W.one_mem
      smul_mem' := by
        intro c v hv
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with h0 | h1
        · rw [h0, zero_smul]
          exact W.one_mem
        · rw [h1, one_smul]
          exact hv }
  have hU : ∀ k : ↥(L ⊔ B), ∀ u ∈ U,
      secHom hY hZ (Subgroup.inclusion (sup_le hLH hBH) k) u ∈ U := by
    intro k u hu
    have hk : Subgroup.inclusion (sup_le hLH hBH) k ∈ (L ⊔ B).subgroupOf H :=
      Subgroup.mem_subgroupOf.2 k.2
    have hmem : secMul hY hZ (Subgroup.inclusion (sup_le hLH hBH) k) ∈
        secMulImg hY hZ L ⊔ secMulImg hY hZ B := by
      rw [← secMulImg_sup hLH hBH]
      exact Subgroup.mem_map_of_mem (secMul hY hZ) hk
    have hWu : secMul hY hZ (Subgroup.inclusion (sup_le hLH hBH) k)
        (Multiplicative.ofAdd u) ∈ W :=
      hW _ hmem _ (show Multiplicative.ofAdd u ∈ W from hu)
    have hstep : secMul hY hZ (Subgroup.inclusion (sup_le hLH hBH) k)
        (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd (secHom hY hZ (Subgroup.inclusion (sup_le hLH hBH) k) u) :=
      secMul_apply hY hZ _ _
    rw [hstep] at hWu
    exact hWu
  rcases secHom_irr (hY := hY) (hZ := hZ) (L := L ⊔ B) (sup_le hLH hBH) hZY hirr U hU with
    hbot | htop
  · left
    ext x
    constructor
    · intro hx
      have hx' : Multiplicative.toAdd x ∈ U := hx
      rw [hbot, Submodule.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact Multiplicative.toAdd.injective (by simpa using hx')
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact W.one_mem
  · right
    ext x
    constructor
    · intro _
      exact Subgroup.mem_top _
    · intro _
      have hx' : Multiplicative.toAdd x ∈ U := by rw [htop]; exact Submodule.mem_top
      exact hx'

theorem isElemAbelian2_secMulImg (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    {D : Subgroup G} (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    CFSG.Quasithin.IsElemAbelian2 (secMulImg hY hZ D) := by
  rw [CFSG.QuasithinUnique.Setup.Layer.Actor.isElemAbelian2_iff_map
    (θ := MulEquiv.refl (Multiplicative (SecQ Y Z))) (secMulImg hY hZ D)]
  rw [← secImg_eq_map_secMulImg D]
  exact secImg_isElementaryAbelian hD

theorem secMulImg_le_normalizer {L D : Subgroup G} (hLH : L ≤ H) (hDH : D ≤ H)
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    (hDN : D ≤ Subgroup.normalizer (L : Set G)) :
    secMulImg hY hZ D ≤
      Subgroup.normalizer (secMulImg hY hZ L : Set (MulAut (Multiplicative (SecQ Y Z)))) := by
  have hconj : ∀ b ∈ secMulImg hY hZ D, ∀ l ∈ secMulImg hY hZ L,
      b * l * b⁻¹ ∈ secMulImg hY hZ L := by
    rintro b ⟨d, hd, rfl⟩ l ⟨x, hx, rfl⟩
    have hmem : (d : G) * (x : G) * (d : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hDN (Subgroup.mem_subgroupOf.1 hd)) (x : G)).1
        (Subgroup.mem_subgroupOf.1 hx)
    let y : ↥L := ⟨(d : G) * (x : G) * (d : G)⁻¹, hmem⟩
    refine ⟨Subgroup.inclusion hLH y, Subgroup.mem_subgroupOf.2 y.2, ?_⟩
    have hy : Subgroup.inclusion hLH y = d * x * d⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hy, map_mul, map_mul, map_inv]
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact hconj a ha l hl
  · intro hl
    have h2 := hconj a⁻¹ ((secMulImg hY hZ D).inv_mem ha) (a * l * a⁻¹) hl
    rwa [show a⁻¹ * (a * l * a⁻¹) * (a⁻¹)⁻¹ = l from by group] at h2

theorem exists_noncomm_secMulImg [Finite V] {L B : Subgroup G} [IsSimpleGroup ↥L] (hLH : L ≤ H)
    (hBH : B ≤ H) (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Y) (hZ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H Z)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hnt : ∃ l ∈ L, ∃ y ∈ Y, ρ l y - y ∉ Z)
    (hBL : ¬ B ≤ Subgroup.centralizer (L : Set G)) :
    ∃ a ∈ secMulImg hY hZ B, ∃ l ∈ secMulImg hY hZ L, a * l ≠ l * a := by
  by_contra hcon
  have hcommAll : ∀ a ∈ secMulImg hY hZ B, ∀ l ∈ secMulImg hY hZ L, a * l = l * a := by
    intro a ha l hl
    by_contra hne
    exact hcon ⟨a, ha, l, hl, hne⟩
  apply hBL
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  let x : ↥H := ⟨b, hBH hb⟩
  let y : ↥H := ⟨l, hLH hl⟩
  have hx : x ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hb
  have hy : y ∈ L.subgroupOf H := Subgroup.mem_subgroupOf.2 hl
  have hcomm : secMul hY hZ x * secMul hY hZ y = secMul hY hZ y * secMul hY hZ x :=
    hcommAll _ (Subgroup.mem_map_of_mem (secMul hY hZ) hx) _
      (Subgroup.mem_map_of_mem (secMul hY hZ) hy)
  have hsec : secMul hY hZ (x * y * x⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hmemL : b * l * b⁻¹ * l⁻¹ ∈ L := by
    have h1 : b * l * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hBN hb) l).1 hl
    exact L.mul_mem h1 (L.inv_mem hl)
  let z : ↥L := ⟨b * l * b⁻¹ * l⁻¹, hmemL⟩
  have hz : Subgroup.inclusion hLH z = x * y * x⁻¹ * y⁻¹ := by
    apply Subtype.ext
    simp [z, x, y]
  have hz1 : z = 1 := by
    apply secMul_injective hLH hY hZ hnt
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hz, hsec]
    simp
  have hval : b * l * b⁻¹ * l⁻¹ = 1 := by
    have hcoe := congrArg Subtype.val hz1
    simpa [z] using hcoe
  calc l * b = (b * l * b⁻¹ * l⁻¹) * (l * b) := by rw [hval, one_mul]
    _ = b * l := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
