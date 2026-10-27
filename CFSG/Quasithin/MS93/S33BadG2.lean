module

public import CFSG.Quasithin.MS93.S33BadEq
public import CFSG.Quasithin.MS93.S33BadHat
public import CFSG.Quasithin.MS93.S38G2Rep
public import CFSG.Quasithin.MS93.S38G2Model

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {f : IntMod (Uq M T L) h.isElemAbelian_Uq →* ModQ} {φ : ↥M →* ↥(quasithinG2 (ZMod 2))}

theorem card_map_g2 (hR : S38G.G2Rep h f φ) {F : Subgroup G} (hFT : F ≤ T) :
    Nat.card ((F.subgroupOf M).map φ) = (pCoreOf 2 M).relIndex F := by
  let φF : ↥F →* ↥(quasithinG2 (ZMod 2)) := φ.comp (Subgroup.inclusion (hFT.trans h.le))
  have hrange : φF.range = (F.subgroupOf M).map φ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_subgroupOf.2 k.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  have hker : φF.ker = (pCoreOf 2 M).subgroupOf F := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hR.eq_one_iff_mem_pCoreOf (m := Subgroup.inclusion (hFT.trans h.le) k) (hFT k.2)
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem card_modQ_le (hR : S38G.G2Rep h f φ) (F : Subgroup G) :
    Nat.card ModQ ≤ Nat.card (fixV (((F.subgroupOf M).map φ).map (g2QAct (ZMod 2)))) *
      (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) := by
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  set W := fixV (((F.subgroupOf M).map φ).map (g2QAct (ZMod 2))) with hW
  let e : ↥(Uq M T L) →* IntMod (Uq M T L) h.isElemAbelian_Uq :=
    { toFun := fun u => IntMod.mk _ u
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hfs : Function.Surjective (f.comp e) := fun q => by
    obtain ⟨v, rfl⟩ := hR.surj q
    exact ⟨v, rfl⟩
  have hle : (Subgroup.centralizer (F : Set G)).subgroupOf (Uq M T L) ≤ W.comap (f.comp e) := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    show f (e u) ∈ W
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have hmF : (m : G) ∈ F := Subgroup.mem_subgroupOf.1 hm
    have hc : S38G.convM h m (e u) = e u := by
      apply IntMod.val_injective
      rw [S38G.convM_apply_val]
      show (m : G) * u * (m : G)⁻¹ = u
      rw [Subgroup.mem_centralizer_iff.mp hu m hmF, mul_inv_cancel_right]
    show (g2QAct (ZMod 2) (φ m)) (f (e u)) = f (e u)
    rw [← hR.equiv, hc]
  have hidx : W.index ≤ (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) := by
    rw [← Subgroup.index_comap_of_surjective W hfs]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hle)
  calc Nat.card ModQ = Nat.card W * W.index := (Subgroup.card_mul_index W).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hidx

theorem isOffG2_of_isXOff (hR : S38G.G2Rep h f φ) {F : Subgroup G} (hF : IsXOff M T F) :
    S38G.IsOffG2 ((F.subgroupOf M).map φ) ∧
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F := by
  obtain ⟨hFT, hFe, hFQ, hFi⟩ := hF
  have hFM : F ≤ M := hFT.trans h.le
  have hcard := card_map_g2 hR hFT
  have h1 := card_modQ_le hR F
  have h2 : (Subgroup.centralizer (F : Set G)).relIndex (Uq M T L) ≤
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) :=
    Subgroup.relIndex_le_of_le_right h.Uq_le_Xq Subgroup.index_ne_zero_of_finite
  have hcomm := isMulCommutative_subgroup_iff.mp hFe.1
  have hBc : ∀ a ∈ (F.subgroupOf M).map φ, ∀ b ∈ (F.subgroupOf M).map φ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
  have hB2 : ∀ b ∈ (F.subgroupOf M).map φ, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow]
    have : b ^ 2 = 1 := Subtype.ext (by simpa using hFe.2 _ (Subgroup.mem_subgroupOf.1 hb))
    rw [this, map_one]
  have hB1 : (F.subgroupOf M).map φ ≠ ⊥ := by
    intro hbot
    apply hFQ
    intro x hx
    have hxM : x ∈ M := hFM hx
    have hφx : φ ⟨x, hxM⟩ = 1 := by
      have hmem : φ ⟨x, hxM⟩ ∈ (F.subgroupOf M).map φ :=
        ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [hbot] at hmem
      exact hmem
    exact (hR.eq_one_iff_mem_pCoreOf (m := ⟨x, hxM⟩) (hFT hx)).1 hφx
  have hle := S38G.card_mul_card_fixV_le hBc hB2
  have hoff : Nat.card ModQ ≤ Nat.card ((F.subgroupOf M).map φ) *
      Nat.card (fixV (((F.subgroupOf M).map φ).map (g2QAct (ZMod 2)))) := by
    rw [mul_comm, hcard]
    exact h1.trans (Nat.mul_le_mul_left _ (h2.trans hFi))
  refine ⟨⟨hB1, hBc, hB2, hoff⟩, ?_⟩
  have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  have hW0 : 0 < Nat.card (fixV (((F.subgroupOf M).map φ).map (g2QAct (ZMod 2)))) :=
    Nat.card_pos
  rw [hcard] at hle
  have h3 := h1.trans (Nat.mul_le_mul_left _ h2)
  have h4 : (pCoreOf 2 M).relIndex F ≤ (Subgroup.centralizer (F : Set G)).relIndex (Xq M) := by
    have := hle.trans h3
    rw [mul_comm] at this
    exact Nat.le_of_mul_le_mul_left this hW0
  exact le_antisymm hFi h4

theorem mem_sup_of_g2 (hR : S38G.G2Rep h f φ) {F : Subgroup G} (hF : IsXOff M T F) {y : G}
    (hyT : y ∈ T) (hyF : y ∈ Subgroup.centralizer (F : Set G)) : y ∈ F ⊔ pCoreOf 2 M := by
  have hFT := hF.1
  have hFM : F ≤ M := hFT.trans h.le
  have hyM : y ∈ M := h.le hyT
  have hB := (isOffG2_of_isXOff hR hF).1
  have hP := S38G.isPGroup_map_subgroupOf φ h.isPGroup
  have hBP : (F.subgroupOf M).map φ ≤ (T.subgroupOf M).map φ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2 (hFT (Subgroup.mem_subgroupOf.1 hx))
  have hyP : φ ⟨y, hyM⟩ ∈ (T.subgroupOf M).map φ := ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.2 hyT, rfl⟩
  have hyc : ∀ b ∈ (F.subgroupOf M).map φ, φ ⟨y, hyM⟩ * b = b * φ ⟨y, hyM⟩ := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyF _ (Subgroup.mem_subgroupOf.1 hb)).symm
  obtain ⟨b, hb, hby⟩ := S38G.mem_of_commute_off hP hBP hB hyP hyc
  have hbF : (b : G) ∈ F := Subgroup.mem_subgroupOf.1 hb
  have hk : φ (b⁻¹ * ⟨y, hyM⟩) = 1 := by rw [map_mul, map_inv, hby, inv_mul_cancel]
  have hkT : ((b⁻¹ * ⟨y, hyM⟩ : ↥M) : G) ∈ T := by
    show (b : G)⁻¹ * y ∈ T
    exact mul_mem (inv_mem (hFT hbF)) hyT
  have hkQ := (hR.eq_one_iff_mem_pCoreOf hkT).1 hk
  have e : y = (b : G) * ((b : G)⁻¹ * y) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hbF) (Subgroup.mem_sup_right hkQ)

theorem s33BadG2_holds :
    S33BadG2 := by
  intro G _ _ M T L h _ _ hG α' hc Y hY hYR hYX
  obtain ⟨-, -, ⟨_, hnat⟩, -⟩ := hG
  obtain ⟨f, φ, hR⟩ := S38G.PUHyp.exists_g2Rep h hnat
  exact le_sup_of_le_left (commutator_le_of_offEq h
    (fun F hF => (isOffG2_of_isXOff hR hF).2)
    (fun F hF _ _ _ _y hyT hyF _ => mem_sup_of_g2 hR hF hyT hyF) hc hY hYR hYX)

theorem s33Bad_holds :
    S33Bad :=
  s33Bad_of_g2 s33BadG2_holds

end CFSG.Quasithin.MS93.S33
