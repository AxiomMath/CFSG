module

public import CFSG.Quasithin.EmptyFaithful.Gap6Dec12Alg
public import CFSG.Quasithin.EmptyFaithful.Gap6Dec12Sec
public import CFSG.Quasithin.EmptyFaithful.S153Ofour

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] {Z U H : Subgroup G}

abbrev piN (Z : Subgroup G) : ↥(Subgroup.normalizer (Z : Set G)) →* Sec Z :=
  secMk (Subgroup.normalizer (Z : Set G)) Z

structure Dec12Data (Z U H H₀ H₁ H₂ : Subgroup G) : Prop where
  le : H₀ ≤ H
  index : H₀.relIndex H = 2
  Q₁ : centralizerMod Z H ⁅U, H⁆ ≤ H₁
  Q₂ : centralizerMod Z H ⁅U, H⁆ ≤ H₂
  le₁ : H₁ ≤ H₀
  le₂ : H₂ ≤ H₀
  sup : H₀ = H₁ ⊔ H₂
  inf : H₁ ⊓ H₂ = centralizerMod Z H ⁅U, H⁆
  comm : ⁅H₁, H₂⁆ ≤ centralizerMod Z H ⁅U, H⁆
  dihedral₁ : SecIso H₁ (centralizerMod Z H ⁅U, H⁆) (DihedralGroup 3)
  dihedral₂ : SecIso H₂ (centralizerMod Z H ⁅U, H⁆) (DihedralGroup 3)
  swap : ∀ t ∈ H, t ∉ H₀ → t ∉ Subgroup.normalizer (H₁ : Set G) ∧ H₂ = conjSub t H₁
  dir_inf : (⁅U, H₁⁆ ⊔ Z) ⊓ (⁅U, H₂⁆ ⊔ Z) = Z
  dir_sup : (⁅U, H₁⁆ ⊔ Z) ⊔ (⁅U, H₂⁆ ⊔ Z) = ⁅U, H⁆ ⊔ Z
  cent₁ : ⁅⁅U, H₁⁆ ⊔ Z, H₂⁆ ≤ Z
  cent₂ : ⁅⁅U, H₂⁆ ⊔ Z, H₁⁆ ≤ Z
  card₁ : Z.relIndex (⁅U, H₁⁆ ⊔ Z) = 4
  card₂ : Z.relIndex (⁅U, H₂⁆ ⊔ Z) = 4

namespace Dec12Ctx

variable (hc : Dec12Ctx Z U H)

abbrev OfourOn (L₁ L₂ : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) (t : MulAut ↥(tildeOf Z ⁅U, H⁆)) :
    Prop :=
  @OfourStruct ↥(tildeOf Z ⁅U, H⁆) (commGroupOfElemAbelian hc.helK) (actW hc).range L₁ L₂ t

@[expose] def commVs (L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) : Subgroup (Sec Z) :=
  (@commV ↥(tildeOf Z ⁅U, H⁆) (commGroupOfElemAbelian hc.helK) L).map (tildeOf Z ⁅U, H⁆).subtype

variable {hc}

theorem mem_commVs {L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} {y : Sec Z} :
    y ∈ commVs hc L ↔ ∃ a ∈ @commV ↥(tildeOf Z ⁅U, H⁆) (commGroupOfElemAbelian hc.helK) L,
      ((a : ↥(tildeOf Z ⁅U, H⁆)) : Sec Z) = y := by
  unfold commVs
  simp only [Subgroup.mem_map, Subgroup.subtype_apply]

theorem _root_.CFSG.Quasithin.Gap6.Dec12Ctx.OfourOn.symm {L₁ L₂ : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))}
    {t : MulAut ↥(tildeOf Z ⁅U, H⁆)} (hO : OfourOn hc L₁ L₂ t) : OfourOn hc L₂ L₁ t :=
  @OfourStruct.symm _ (commGroupOfElemAbelian hc.helK) _ _ _ _ hO

variable (hc)

theorem secImg_commutator_HL {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))}
    {t : MulAut ↥(tildeOf Z ⁅U, H⁆)} (hO : OfourOn hc L L' t) :
    tildeOf Z (⁅U, HL hc L⁆ ⊔ Z) = commVs hc L := by
  let _ : CommGroup ↥(tildeOf Z ⁅U, H⁆) := commGroupOfElemAbelian hc.helK
  let _ : CommGroup ↥(tildeOf Z U) := commGroupOfElemAbelian hc.helU
  have hM : ∀ m : ↥(tildeOf Z U), m * m = 1 := fun m =>
    Subtype.ext (by simpa [pow_two] using F7.isElemAbelian_pow_eq_one hc.helU m.2)
  have hHLU : HL hc L ≤ Subgroup.normalizer (U : Set G) := (HL_le L).trans hc.hHU
  have hHLN : HL hc L ≤ Subgroup.normalizer (Z : Set G) := (HL_le L).trans hc.hZ
  have hcomm : ⁅U, HL hc L⁆ ≤ Subgroup.normalizer (Z : Set G) :=
    (S145.commutator_le_of_le_normalizer hHLU).trans hc.hUZ
  have hLr : L ≤ (actW hc).range := hO.L₁_le
  rw [tildeOf_sup_self hcomm]
  have e0 : tildeOf Z ⁅U, HL hc L⁆ = ⁅tildeOf Z U, tildeOf Z (HL hc L)⁆ :=
    secImg_commutator hc.hUZ hHLN
  rw [e0]
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro m hm x hx
    obtain ⟨xN, hxHL, rfl⟩ := mem_secImg.1 hx
    have hxH : (xN : G) ∈ H := HL_le L hxHL
    have hh : actW hc ⟨xN, hxH⟩ ∈ L := (mem_HL_iff hxH).1 hxHL
    obtain ⟨a, ha, hae⟩ := apply_mul_inv_mem_commV hM (iota hc) (iota_injective hc) (actU hc)
      (actW hc) (fun g w => iota_actW hc g w) (actU_mul_inv_mem_range hc)
      (actU_eq_one_of_actW_eq_one hc) hO hh ⟨m, hm⟩
    have htT : toTilde hc.hZ ⟨(xN : G), hxH⟩ = piN Z xN := rfl
    have hae' : piN Z xN * m * (piN Z xN)⁻¹ * m⁻¹ =
        ((a : ↥(tildeOf Z ⁅U, H⁆)) : Sec Z) := by
      have := congrArg (fun y : ↥(tildeOf Z U) => (y : Sec Z)) hae
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, actU_coe, iota_coe, htT] at this
      exact this
    refine mem_commVs.2 ⟨a⁻¹, Subgroup.inv_mem _ ha, ?_⟩
    have e : ⁅m, piN Z xN⁆ = (piN Z xN * m * (piN Z xN)⁻¹ * m⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hae']
    rfl
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_commVs.1 hy
    clear hy
    induction ha using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨ℓ, hℓ, v, rfl⟩ := hw
      obtain ⟨h, rfl⟩ := hLr hℓ
      have hx : toTilde hc.hZ h ∈ tildeOf Z (HL hc L) :=
        secMk_mem_secImg (x := Subgroup.inclusion hc.hZ h) (mem_HL_of_mem hℓ)
      have hv : (v : Sec Z) ∈ tildeOf Z U := secImg_mono hc.comm_le v.2
      have := Subgroup.commutator_mem_commutator hx hv
      rw [Subgroup.commutator_comm] at this
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, actW_coe, commutatorElement_def]
    | one => exact Subgroup.one_mem _
    | mul a b _ _ iha ihb =>
      have := Subgroup.mul_mem _ iha ihb
      simpa using this
    | inv a _ iha =>
      have := Subgroup.inv_mem _ iha
      simpa using this

variable {hc}

section Blocks

variable {L₁ L₂ : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} {t : MulAut ↥(tildeOf Z ⁅U, H⁆)}

theorem Yle_N (L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) :
    ⁅U, HL hc L⁆ ⊔ Z ≤ Subgroup.normalizer (Z : Set G) :=
  sup_le ((S145.commutator_le_of_le_normalizer ((HL_le L).trans hc.hHU)).trans hc.hUZ)
    Subgroup.le_normalizer

theorem Yle_K (L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) : ⁅U, HL hc L⁆ ⊔ Z ≤ ⁅U, H⁆ ⊔ Z :=
  sup_le_sup_right (Subgroup.commutator_mono le_rfl (HL_le L)) Z

theorem mem_Y_iff {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} {t : MulAut ↥(tildeOf Z ⁅U, H⁆)}
    (hO : OfourOn hc L L' t) {y : G} (hy : y ∈ Subgroup.normalizer (Z : Set G)) :
    y ∈ ⁅U, HL hc L⁆ ⊔ Z ↔ piN Z ⟨y, hy⟩ ∈ commVs hc L := by
  rw [← secImg_commutator_HL hc hO]
  exact (secMk_mem_secImg_iff (A := Subgroup.normalizer (Z : Set G)) (B := Z)
    (X := ⁅U, HL hc L⁆ ⊔ Z) le_sup_right (x := ⟨y, hy⟩)).symm

theorem commVs_inf (hO : OfourOn hc L₁ L₂ t) : commVs hc L₁ ⊓ commVs hc L₂ = ⊥ := by
  let _ : CommGroup ↥(tildeOf Z ⁅U, H⁆) := commGroupOfElemAbelian hc.helK
  unfold commVs
  rw [← Subgroup.map_inf _ _ _ (Subgroup.subtype_injective _), hO.inf, Subgroup.map_bot]

theorem commVs_sup (hO : OfourOn hc L₁ L₂ t) : commVs hc L₁ ⊔ commVs hc L₂ = tildeOf Z ⁅U, H⁆ := by
  let _ : CommGroup ↥(tildeOf Z ⁅U, H⁆) := commGroupOfElemAbelian hc.helK
  unfold commVs
  rw [← Subgroup.map_sup, hO.sup, Subgroup.map_top, Subgroup.range_subtype]

theorem card_commVs (hO : OfourOn hc L₁ L₂ t) : Nat.card (commVs hc L₁) = 4 := by
  let _ : CommGroup ↥(tildeOf Z ⁅U, H⁆) := commGroupOfElemAbelian hc.helK
  unfold commVs
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hO.card_U₁

theorem Y_inf (hO : OfourOn hc L₁ L₂ t) :
    (⁅U, HL hc L₁⁆ ⊔ Z) ⊓ (⁅U, HL hc L₂⁆ ⊔ Z) = Z := by
  apply le_antisymm
  · rintro y ⟨h1, h2⟩
    have hyN : y ∈ Subgroup.normalizer (Z : Set G) := Yle_N L₁ h1
    have h1' := (mem_Y_iff hO hyN).1 h1
    have h2' := (mem_Y_iff hO.symm hyN).1 h2
    have : piN Z ⟨y, hyN⟩ ∈ commVs hc L₁ ⊓ commVs hc L₂ := ⟨h1', h2'⟩
    rw [commVs_inf hO, Subgroup.mem_bot] at this
    exact secMk_eq_one_iff.1 this
  · exact le_inf le_sup_right le_sup_right

theorem Y_sup (hO : OfourOn hc L₁ L₂ t) :
    (⁅U, HL hc L₁⁆ ⊔ Z) ⊔ (⁅U, HL hc L₂⁆ ⊔ Z) = ⁅U, H⁆ ⊔ Z := by
  apply le_antisymm
  · exact sup_le (Yle_K L₁) (Yle_K L₂)
  · intro y hy
    have hKN : ⁅U, H⁆ ≤ Subgroup.normalizer (Z : Set G) := hc.K_le_N
    have hyN : y ∈ Subgroup.normalizer (Z : Set G) := (sup_le hKN Subgroup.le_normalizer) hy
    have hZle : Z ≤ (⁅U, HL hc L₁⁆ ⊔ Z) ⊔ (⁅U, HL hc L₂⁆ ⊔ Z) := le_sup_right.trans le_sup_left
    refine (secMk_mem_secImg_iff (A := Subgroup.normalizer (Z : Set G)) (B := Z) hZle
      (x := ⟨y, hyN⟩)).1 ?_
    have e1 : tildeOf Z ((⁅U, HL hc L₁⁆ ⊔ Z) ⊔ (⁅U, HL hc L₂⁆ ⊔ Z)) = tildeOf Z ⁅U, H⁆ := by
      rw [tildeOf_sup (Yle_N L₁) (Yle_N L₂), secImg_commutator_HL hc hO,
        secImg_commutator_HL hc hO.symm, commVs_sup hO]
    have e2 : tildeOf Z (⁅U, H⁆ ⊔ Z) = tildeOf Z ⁅U, H⁆ := tildeOf_sup_self hKN
    have hmem : piN Z ⟨y, hyN⟩ ∈ tildeOf Z (⁅U, H⁆ ⊔ Z) :=
      secMk_mem_secImg (x := ⟨y, hyN⟩) hy
    rw [e2, ← e1] at hmem
    exact hmem

theorem Y_cent (hO : OfourOn hc L₁ L₂ t) : ⁅⁅U, HL hc L₁⁆ ⊔ Z, HL hc L₂⁆ ≤ Z := by
  let _ : CommGroup ↥(tildeOf Z ⁅U, H⁆) := commGroupOfElemAbelian hc.helK
  rw [Subgroup.commutator_le]
  intro y hy h hh
  have hyN : y ∈ Subgroup.normalizer (Z : Set G) := Yle_N L₁ hy
  have hhH : h ∈ H := HL_le L₂ hh
  have hhL : actW hc ⟨h, hhH⟩ ∈ L₂ := (mem_HL_iff hhH).1 hh
  obtain ⟨a, ha, hae⟩ := mem_commVs.1 ((mem_Y_iff hO hyN).1 hy)
  have hfix := hO.L₂_fix₁ hhL ha
  have hfix' := congrArg (fun w : ↥(tildeOf Z ⁅U, H⁆) => (w : Sec Z)) hfix
  simp only [actW_coe] at hfix'
  have hcomm : piN Z ⟨y, hyN⟩ * piN Z (Subgroup.inclusion hc.hZ ⟨h, hhH⟩) =
      piN Z (Subgroup.inclusion hc.hZ ⟨h, hhH⟩) * piN Z ⟨y, hyN⟩ := by
    rw [← hae]
    have := mul_inv_eq_iff_eq_mul.1 hfix'
    exact this.symm
  exact commutator_mem_of_secMk_commute (x := ⟨y, hyN⟩) (y := Subgroup.inclusion hc.hZ ⟨h, hhH⟩)
    hcomm

theorem Y_card (hO : OfourOn hc L₁ L₂ t) : Z.relIndex (⁅U, HL hc L₁⁆ ⊔ Z) = 4 := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z)
    (H := ⁅U, HL hc L₁⁆ ⊔ Z) le_rfl le_sup_right (Yle_N L₁)
  have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  rw [← h1]
  change Nat.card ↥(tildeOf Z (⁅U, HL hc L₁⁆ ⊔ Z)) = 4
  rw [secImg_commutator_HL hc hO]
  exact card_commVs hO

end Blocks

theorem exists_data (hc : Dec12Ctx Z U H)
    (hO : IsOFourPlusAction (tildeOf Z H) (tildeOf Z ⁅U, H⁆)) :
    ∃ H₀ H₁ H₂ : Subgroup G, Dec12Data Z U H H₀ H₁ H₂ := by
  obtain ⟨hcard, q, hq1, hq2, hq3, hq4⟩ := hO
  let _ : CommGroup ↥(tildeOf Z ⁅U, H⁆) := commGroupOfElemAbelian hc.helK
  have hexp : ∀ w : ↥(tildeOf Z ⁅U, H⁆), w * w = 1 := fun w =>
    Subtype.ext (by simpa [pow_two] using F7.isElemAbelian_pow_eq_one hc.helK w.2)
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
  have hrange : (actW hc).range = orthogonalGroupOf q := by rw [actW_range hc, hq4]
  have hO' : OfourOn hc L₁ L₂ t := by
    unfold OfourOn
    rw [hrange]
    exact hS
  have hL₁ : L₁ ≤ (actW hc).range := hO'.L₁_le
  have hL₂ : L₂ ≤ (actW hc).range := hO'.L₂_le
  obtain ⟨e₁, -, -⟩ := hO'.nat₁
  obtain ⟨e₂, -, -⟩ := hO'.nat₂
  refine ⟨HL hc (L₁ ⊔ L₂), HL hc L₁, HL hc L₂, ?_⟩
  exact
    { le := HL_le _
      index := by rw [relIndex_HL]; exact hO'.relIndex_sup
      Q₁ := centralizerMod_le_HL
      Q₂ := centralizerMod_le_HL
      le₁ := HL_mono le_sup_left
      le₂ := HL_mono le_sup_right
      sup := HL_sup hL₁ hL₂
      inf := by rw [← HL_inf, hO'.Linf, HL_bot]
      comm := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        have haH := HL_le _ ha
        have hbH := HL_le _ hb
        have habH : ⁅a, b⁆ ∈ H := by
          rw [commutatorElement_def]
          exact H.mul_mem (H.mul_mem (H.mul_mem haH hbH) (H.inv_mem haH)) (H.inv_mem hbH)
        rw [← HL_bot (hc := hc)]
        refine (mem_HL_iff habH).2 ?_
        have ha' := (mem_HL_iff haH).1 ha
        have hb' := (mem_HL_iff hbH).1 hb
        have e : (⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹ * ⟨b, hbH⟩⁻¹ : ↥H) = ⟨⁅a, b⁆, habH⟩ :=
          Subtype.ext rfl
        rw [← e, map_mul, map_mul, map_mul, map_inv, map_inv, hO'.comm _ ha' _ hb']
        simp
      dihedral₁ := secIso_HL hL₁ (e₁.trans sl2EquivDihedral3)
      dihedral₂ := secIso_HL hL₂ (e₂.trans sl2EquivDihedral3)
      swap := by
        intro t ht htH₀
        have htL : ¬ actW hc ⟨t, ht⟩ ∈ L₁ ⊔ L₂ := fun h => htH₀ ((mem_HL_iff ht).2 h)
        have hτX : actW hc ⟨t, ht⟩ ∈ (actW hc).range := ⟨_, rfl⟩
        have hconj : B1.conjAut (actW hc ⟨t, ht⟩) L₁ = L₂ := by
          rcases hO'.perm _ hτX with ⟨h1, -⟩ | ⟨h1, -⟩
          · exfalso
            apply htL
            refine (hO'.mem_sup_iff hτX).2 fun u hu => ?_
            exact OfourStruct.commV_apply_mem _ L₁ L₁ h1 hu
          · exact h1
        have hconj' : conjSub t (HL hc L₁) = HL hc L₂ := by
          refine conjSub_HL ht fun x => ?_
          rw [← hconj, B1.mem_conjAut]
        refine ⟨fun hN => ?_, hconj'.symm⟩
        have h1 := F7.conjSub_eq_of_mem_normalizer hN
        rw [hconj'] at h1
        exact hO'.L₁_ne_L₂ (HL_injective hL₂ hL₁ h1).symm
      dir_inf := Y_inf hO'
      dir_sup := Y_sup hO'
      cent₁ := Y_cent hO'
      cent₂ := Y_cent hO'.symm
      card₁ := Y_card hO'
      card₂ := Y_card hO'.symm }

end Dec12Ctx

end Gap6

end CFSG.Quasithin
