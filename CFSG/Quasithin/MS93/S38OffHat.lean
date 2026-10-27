module

public import CFSG.Quasithin.MS93.S38PU
public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.Quasithin.Background.D14Groups
public import CFSG.Quasithin.MS93.SkItems

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

namespace S38H

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem pCoreOf_le_centralizer_Uq (h : PUHyp M T L) :
    pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) := by
  rw [← Subgroup.le_centralizer_iff]
  exact h.Uq_le_Xq.trans ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right)

theorem mem_pCoreOf_of_mem_centralizer (h : PUHyp M T L) {t : G} (htT : t ∈ T)
    (htU : t ∈ Subgroup.centralizer (Uq M T L : Set G)) : t ∈ pCoreOf 2 M :=
  h.mem_pCoreOf_of_comm_Uq htT fun u hu => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp htU u hu)]
    exact Subgroup.one_mem _

theorem le_normalizer_Uq_T (h : PUHyp M T L) :
    T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
  h.le.trans (le_normalizer_Uq h.le_normalizer)

variable (hU : IsElemAbelian 2 (Uq M T L))

omit [Finite G] in
theorem autI_le_normalizer (hLn : M ≤ Subgroup.normalizer (L : Set G)) {K : Subgroup G}
    (hKM : K ≤ M) :
    autI hU K ≤ Subgroup.normalizer (autI hU L : Set (MulAut (IntMod (Uq M T L) hU))) := by
  have key : ∀ g : Subgroup.normalizer (Uq M T L : Set G), (g : G) ∈ M →
      ∀ ψ ∈ autI hU L, convI hU g * ψ * (convI hU g)⁻¹ ∈ autI hU L := by
    intro g hgM ψ hψ
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hU).1 hψ
    rw [← map_inv, ← map_mul, ← map_mul]
    refine convI_mem_autI hU ?_ _
    exact (Subgroup.mem_normalizer_iff.mp (hLn hgM) l).mp hlL
  intro φ hφ
  obtain ⟨g, hgK, rfl⟩ := (mem_autI hU).1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  refine ⟨key g (hKM hgK) ψ, fun hψ => ?_⟩
  have := key g⁻¹ (M.inv_mem (hKM hgK)) _ hψ
  simpa [mul_assoc] using this

theorem card_autI (h : PUHyp M T L) {F : Subgroup G} (hFT : F ≤ T) :
    Nat.card (autI hU F) = (pCoreOf 2 M).relIndex F := by
  rw [card_autI_eq hU (hFT.trans (le_normalizer_Uq_T h))]
  have he : F ⊓ Subgroup.centralizer (Uq M T L : Set G) = F ⊓ pCoreOf 2 M := by
    refine le_antisymm (fun x hx => ⟨hx.1, mem_pCoreOf_of_mem_centralizer h (hFT hx.1) hx.2⟩)
      fun x hx => ⟨hx.1, pCoreOf_le_centralizer_Uq h hx.2⟩
  rw [he, inf_comm, Subgroup.inf_relIndex_right]

theorem mem_sup_of_convI_mem (h : PUHyp M T L) {F : Subgroup G} (hFT : F ≤ T) {y : G}
    (hyT : y ∈ T)
    (hy : convI hU ⟨y, le_normalizer_Uq_T h hyT⟩ ∈ autI hU F) : y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨g, hgF, hgy⟩ := (mem_autI hU).1 hy
  have h1 : convI hU (g⁻¹ * ⟨y, le_normalizer_Uq_T h hyT⟩) = 1 := by
    rw [map_mul, map_inv, hgy, inv_mul_cancel]
  have h2 := (convI_eq_one_iff hU _).mp h1
  have hq : (g : G)⁻¹ * y ∈ pCoreOf 2 M :=
    mem_pCoreOf_of_mem_centralizer h (T.mul_mem (T.inv_mem (hFT hgF)) hyT) h2
  have e : y = (g : G) * ((g : G)⁻¹ * y) := by group
  rw [e]
  exact (F ⊔ pCoreOf 2 M).mul_mem (Subgroup.mem_sup_left hgF) (Subgroup.mem_sup_right hq)

theorem le_sup_of_autI_le (h : PUHyp M T L) {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ T) (h₂ : F₂ ≤ T)
    (he : autI hU F₂ ≤ autI hU F₁) : F₂ ≤ F₁ ⊔ pCoreOf 2 M := fun _ hy =>
  mem_sup_of_convI_mem hU h h₁ (h₂ hy)
    (he (convI_mem_autI hU hy (le_normalizer_Uq_T h (h₂ hy))))

omit [Finite G] in
theorem val_mem_commutator_of_mem_commV {F : Subgroup G} {w : IntMod (Uq M T L) hU}
    (hw : w ∈ commV (autI hU F)) : w.val ∈ ⁅Uq M T L, F⁆ := by
  have hle : commV (autI hU F) ≤ (⁅Uq M T L, F⁆).comap (intModVal hU) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨g, hgF, rfl⟩ := (mem_autI hU).1 hx
    show (convI hU g v * v⁻¹).val ∈ ⁅Uq M T L, F⁆
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hgF v.val_mem
  exact hle hw

theorem offender_facts (h : PUHyp M T L) (h6 : TripleA6Six (autI hU L) ⊤ ⊥) {F : Subgroup G}
    (hF : IsXOff M T F) :
    autI hU F ≤ autI hU L ∧ Nat.card (autI hU F) = 4 ∧ Nat.card (fixV (autI hU F)) = 16 ∧
      (pCoreOf 2 M).relIndex F = 4 ∧
      Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (F : Set G)) = 16 ∧
      Uq M T L ⊓ Subgroup.centralizer (F : Set G) ≤ ⁅Uq M T L, F⁆ ∧
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = 4 := by
  obtain ⟨hFT, hFe, hFQ, hoff⟩ := hF
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) := hFT.trans (le_normalizer_Uq_T h)
  have hHM := S38H.HatMod.of_tripleA6Six IntMod.sq_eq_one h6
  have hEN := autI_le_normalizer hU h.le_normalizer (hFT.trans h.le)
  have hE := isElemAbelian2_autI hU hFe hFN
  have hE1 : autI hU F ≠ ⊥ := by
    rw [Ne, autI_eq_bot_iff hU hFN]
    intro hle
    exact hFQ fun x hx => mem_pCoreOf_of_mem_centralizer h (hFT hx) (hle hx)
  have hcE := card_autI hU h hFT
  have hfix : Nat.card (fixV (autI hU F)) = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer
      (F : Set G)) := card_fixV_autI hU hFN
  have hUc : Nat.card ↥(Uq M T L) = 64 := by
    have := hHM.card
    rw [show Nat.card (IntMod (Uq M T L) hU) = Nat.card ↥(Uq M T L) from rfl] at this
    rw [this]
    norm_num
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (F : Set G)) (Uq M T L)
  have hle : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) ≤
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) :=
    Subgroup.relIndex_le_of_le_right h.Uq_le_Xq Subgroup.index_ne_zero_of_finite
  have hoff' : Nat.card (IntMod (Uq M T L) hU) ≤
      Nat.card (autI hU F) * Nat.card (fixV (autI hU F)) := by
    rw [show Nat.card (IntMod (Uq M T L) hU) = Nat.card ↥(Uq M T L) from rfl, ← hmul, hfix,
      inf_comm, hcE]
    exact Nat.mul_le_mul_right _ (hle.trans hoff)
  obtain ⟨hEH, hE4, hf16, hfc⟩ := hHM.offender hEN hE hE1 hoff'
  have hQ4 : (pCoreOf 2 M).relIndex F = 4 := hcE ▸ hE4
  have hC16 : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (F : Set G)) = 16 := hfix ▸ hf16
  refine ⟨hEH, hE4, hf16, hQ4, hC16, fun u hu => ?_, ?_⟩
  · have hmem : IntMod.mk hU ⟨u, hu.1⟩ ∈ fixV (autI hU F) :=
      (mem_fixV_autI hU hFN _).mpr hu.2
    exact val_mem_commutator_of_mem_commV hU (hfc hmem)
  · have h4 : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) = 4 := by
      rw [inf_comm, hC16, hUc] at hmul
      omega
    omega

theorem isPGroup_autI_T (h : PUHyp M T L) : IsPGroup 2 (autI hU T) := by
  exact (h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe (le_normalizer_Uq_T h)).symm).map
    (convI hU)

theorem sup_eq_of_isXOff (h : PUHyp M T L) (h6 : TripleA6Six (autI hU L) ⊤ ⊥)
    {F₁ F₂ : Subgroup G} (hF₁ : IsXOff M T F₁) (hF₂ : IsXOff M T F₂) :
    F₁ ⊔ pCoreOf 2 M = F₂ ⊔ pCoreOf 2 M := by
  have hHM := S38H.HatMod.of_tripleA6Six IntMod.sq_eq_one h6
  have hTN := le_normalizer_Uq_T h
  obtain ⟨h₁H, h₁4, hf₁, -, -, -, -⟩ := offender_facts hU h h6 hF₁
  obtain ⟨h₂H, h₂4, hf₂, -, -, -, -⟩ := offender_facts hU h h6 hF₂
  have heq := hHM.offender_unique (isPGroup_autI_T hU h) (autI_mono hU hF₁.1)
    (autI_mono hU hF₂.1) h₁H h₂H (isElemAbelian2_autI hU hF₁.2.1 (hF₁.1.trans hTN))
    (isElemAbelian2_autI hU hF₂.2.1 (hF₂.1.trans hTN)) h₁4 h₂4 hf₁ hf₂
  exact le_antisymm (sup_le (le_sup_of_autI_le hU h hF₂.1 hF₁.1 heq.le) le_sup_right)
    (sup_le (le_sup_of_autI_le hU h hF₁.1 hF₂.1 heq.ge) le_sup_right)

theorem mem_sup_of_mem_L (h : PUHyp M T L) (h6 : TripleA6Six (autI hU L) ⊤ ⊥)
    {F : Subgroup G} (hF : IsXOff M T F) {y : G} (hyT : y ∈ T)
    (hyF : y ∈ Subgroup.centralizer (F : Set G))
    (hyL : convI hU ⟨y, le_normalizer_Uq_T h hyT⟩ ∈ autI hU L) : y ∈ F ⊔ pCoreOf 2 M := by
  have hHM := S38H.HatMod.of_tripleA6Six IntMod.sq_eq_one h6
  obtain ⟨hEH, hE4, -, -, -, -, -⟩ := offender_facts hU h h6 hF
  have hE := isElemAbelian2_autI hU hF.2.1 (hF.1.trans (le_normalizer_Uq_T h))
  have hcomm : ∀ e ∈ autI hU F, e * convI hU ⟨y, le_normalizer_Uq_T h hyT⟩ =
      convI hU ⟨y, le_normalizer_Uq_T h hyT⟩ * e := by
    intro e he
    obtain ⟨g, hgF, rfl⟩ := (mem_autI hU).1 he
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyF g hgF)
  exact mem_sup_of_convI_mem hU h hF.1 hyT (hHM.mem_of_comm_of_mem (isPGroup_autI_T hU h)
    (autI_mono hU hF.1) hEH hE hE4 (convI_mem_autI hU hyT _) hyL hcomm)

theorem mem_sup_of_comm_mem (h : PUHyp M T L) (h6 : TripleA6Six (autI hU L) ⊤ ⊥)
    {F : Subgroup G} (hF : IsXOff M T F) {y : G} (hyT : y ∈ T)
    (hyF : y ∈ Subgroup.centralizer (F : Set G))
    (hyU : ∀ u ∈ Uq M T L, ⁅u, y⁆ ∈ Subgroup.centralizer (F : Set G)) :
    y ∈ F ⊔ pCoreOf 2 M := by
  have hHM := S38H.HatMod.of_tripleA6Six IntMod.sq_eq_one h6
  obtain ⟨hEH, -, hf16, -, -, -, -⟩ := offender_facts hU h h6 hF
  obtain ⟨zH, hcen, h3, hfp⟩ := hHM.exists_z
  have hFN : F ≤ Subgroup.normalizer (Uq M T L : Set G) := hF.1.trans (le_normalizer_Uq_T h)
  set y' := convI hU ⟨y, le_normalizer_Uq_T h hyT⟩ with hy'
  have hyN : y' ∈ Subgroup.normalizer (autI hU L : Set (MulAut (IntMod (Uq M T L) hU))) :=
    autI_le_normalizer hU h.le_normalizer h.le (convI_mem_autI hU hyT _)
  have hyv : ∀ v : IntMod (Uq M T L) hU, y' v * v⁻¹ ∈ fixV (autI hU F) := by
    intro v
    rw [mem_fixV_autI hU hFN, IntMod.val_mul, IntMod.val_inv, hy', convI_apply_val]
    have := Subgroup.inv_mem _ (hyU v.val v.val_mem)
    rwa [commutatorElement_inv, commutatorElement_def] at this
  have hz := hHM.comm_z_of_comm_mem hcen h3 hfp
    (fun b hb => HatMod.comm_z_of_mem hcen (hEH hb)) hf16 hyN hyv
  exact mem_sup_of_mem_L hU h h6 hF hyT hyF (hHM.mem_of_comm_z hcen hyN hz)

theorem exists_zc (h : PUHyp M T L) (h6 : TripleA6Six (autI hU L) ⊤ ⊥) {F : Subgroup G}
    (hF : IsXOff M T F) : ∃ Z : Subgroup G, Z ≤ Xq M ∧ ¬ Z ≤ Subgroup.centralizer (F : Set G) ∧
      ∀ Y : Subgroup G, Y ≤ T → Y ≤ Subgroup.centralizer (F : Set G) →
        ⁅Y, Z⁆ ≤ ⁅Xq M, F⁆ ⊔ ⁅Y, Xq M ⊓ Subgroup.centralizer (F : Set G)⁆ := by
  obtain ⟨-, -, -, -, -, hCU, -⟩ := offender_facts hU h h6 hF
  set U := Uq M T L with hUdef
  set W := U ⊓ Subgroup.centralizer (F : Set G) with hW
  set T' := (T ⊓ Subgroup.centralizer (F : Set G)) ⊔ U with hT'
  have hUT : U ≤ T := h.Uq_le_Xq.trans ((Xq_le_pCoreOf M).trans h.pCore_le)
  have hT'p : IsPGroup 2 T' := h.isPGroup.to_le (sup_le inf_le_left hUT)
  have hUF : ¬ U ≤ Subgroup.centralizer (F : Set G) := by
    intro hle
    rw [Subgroup.le_centralizer_iff] at hle
    exact hF.2.2.1 fun x hx => mem_pCoreOf_of_mem_centralizer h (hF.1 hx) (hle hx)
  have hWU : W < U := lt_of_le_of_ne inf_le_left fun he => hUF (he.symm.le.trans inf_le_right)
  have hTN := le_normalizer_Uq_T h
  have hT'U : T' ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (inf_le_left.trans hTN) Subgroup.le_normalizer
  have hUW : U ≤ Subgroup.normalizer (W : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hU.1.is_comm.comm ⟨w, hw.1⟩ ⟨u, hu⟩)
  have hT'W : T' ≤ Subgroup.normalizer (W : Set G) :=
    sup_le (le_normalizer_inf (inf_le_left.trans hTN) (inf_le_right.trans Subgroup.le_normalizer))
      hUW
  obtain ⟨x, hxU, hxW, hx⟩ := D14.exists_fixed_of_lt hT'p le_sup_right hWU hT'U hT'W
  have hxF : x ∉ Subgroup.centralizer (F : Set G) := fun hc => hxW ⟨hxU, hc⟩
  refine ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).mpr (h.Uq_le_Xq hxU),
    fun hle => hxF (hle (Subgroup.mem_zpowers x)), fun Y hYT hYF => le_sup_of_le_left ?_⟩
  refine le_trans ?_ (hCU.trans (Subgroup.commutator_mono h.Uq_le_Xq le_rfl))
  rw [Subgroup.commutator_le]
  intro y hy z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hx2 : x ^ 2 = 1 := hU.2 x hxU
  rw [zpow_eq_zpow_emod' k hx2]
  have hyT' : y ∈ T' := Subgroup.mem_sup_left ⟨hYT hy, hYF hy⟩
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [Nat.cast_ofNat, hk, zpow_zero, commutatorElement_one_right]
    exact W.one_mem
  · rw [Nat.cast_ofNat, hk, zpow_one, commutatorElement_def]
    exact hx y hyT'

end S38H

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

open S38H in
theorem PUHyp.xOffData_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L)
    (_hb : 2 < critDist (puAmalgam h.le)) (_hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (_h1 : ¬ IsSL3U M T L) (_h2 : ¬ IsSp4U M T L) : XOffData M T := by
  obtain ⟨-, -, hU, h6⟩ := hX
  refine ⟨fun F₁ F₂ h₁ h₂ => sup_eq_of_isXOff hU h h6 h₁ h₂, fun F hF => ?_,
    fun F hF => exists_zc hU h h6 hF⟩
  obtain ⟨-, -, -, hQ4, -, -, hX4⟩ := offender_facts hU h h6 hF
  rw [hX4, hQ4]

open S38H in
theorem PUHyp.relIndex_eq_four_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L)
    {F : Subgroup G} (hF : IsXOff M T F) : (pCoreOf 2 M).relIndex F = 4 := by
  obtain ⟨-, -, hU, h6⟩ := hX
  exact (offender_facts hU h h6 hF).2.2.2.1

open S38H in
theorem PUHyp.mem_sup_of_comm_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L)
    {F : Subgroup G} (hF : IsXOff M T F) {y : G} (hyT : y ∈ T)
    (hyF : y ∈ Subgroup.centralizer (F : Set G))
    (hyU : ∀ u ∈ Uq M T L, ⁅u, y⁆ ∈ Subgroup.centralizer (F : Set G)) :
    y ∈ F ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, hU, h6⟩ := hX
  exact mem_sup_of_comm_mem hU h h6 hF hyT hyF hyU

theorem PUHyp.xOffCentU_of_isHatA6U (h : PUHyp M T L) (hX : IsHatA6U M T L) :
    ∀ F : Subgroup G, IsXOff M T F → ∀ y ∈ T, y ∈ Subgroup.centralizer (F : Set G) →
      (∀ u ∈ Uq M T L, ⁅u, y⁆ ∈ Subgroup.centralizer (F : Set G)) →
        y ∈ F ⊔ pCoreOf 2 M :=
  fun _ hF _ hyT hyF hyU => h.mem_sup_of_comm_of_isHatA6U hX hF hyT hyF hyU

end CFSG.Quasithin.MS93
