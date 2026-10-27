module

public import CFSG.Quasithin.Vol2.Ch10SecC8V1
public import CFSG.Quasithin.Vol2.Ch10SecD32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem V1_ne_V2 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ≠ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  intro heq
  have hC : fsuUL T L I ≤ Subgroup.centralizer (L : Set G) :=
    heq ▸ V2_le_centralizer_L h37 h38 h ht htn
  apply SecA.commutator_fsuVM_ne_bot h.fsu
  show fsuUL T L I = ⊥
  rw [← SecC.commutator_fsuUL_eq h]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hC

theorem mem_normalizer_V12_or (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ fsuM T L) :
    (x ∈ Subgroup.normalizer (fsuUL T L I : Set G) ∧
        x ∈ Subgroup.normalizer ((⁅fsuVM T L I, CFSG.conjugate L t⁆ : Subgroup G) : Set G)) ∨
      (CFSG.conjugate (fsuUL T L I) x = ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧
        CFSG.conjugate ⁅fsuVM T L I, CFSG.conjugate L t⁆ x = fsuUL T L I) := by
  have hne := V1_ne_V2 h37 h38 h ht htn
  have hinj : ∀ {X Y : Subgroup G}, CFSG.conjugate X x = CFSG.conjugate Y x → X = Y := by
    intro X Y hXY
    have := congrArg (fun Z => CFSG.conjugate Z x⁻¹) hXY
    simpa only [SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one] using this
  rcases conjugate_V1_eq_or h37 h38 h ht htn hx with h1 | h1
  · left
    refine ⟨SecA.conjugate_eq_self_iff.mp h1, SecA.conjugate_eq_self_iff.mp ?_⟩
    rcases conjugate_V2_eq_or h37 h38 h ht htn hx with h2 | h2
    · exact absurd (hinj (h2.trans h1.symm)).symm hne
    · exact h2
  · right
    refine ⟨h1, ?_⟩
    rcases conjugate_V2_eq_or h37 h38 h ht htn hx with h2 | h2
    · exact h2
    · exact absurd (hinj (h1.trans h2.symm)) hne

theorem card_le_two_mul_card_inf_normalizer_V1 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) {A : Subgroup G} (hA : A ≤ fsuM T L) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  refine card_le_two_mul_card_inf fun a ha b hb han hbn => ?_
  rcases mem_normalizer_V12_or h37 h38 h ht htn (hA ha) with h1 | h1
  · exact absurd h1.1 han
  rcases mem_normalizer_V12_or h37 h38 h ht htn (hA hb) with h2 | h2
  · exact absurd h2.1 hbn
  exact SecA.mul_inv_mem_normalizer_of_conjugate_eq (h1.1.trans h2.1.symm)

omit [Finite G] in
theorem conj_mem_centralizer_singleton {x z : G} (g : G)
    (hz : z ∈ Subgroup.centralizer ({x} : Set G)) :
    g * z * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
    _ = g * (x * z) * g⁻¹ := by rw [hz]
    _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group

theorem centralizer_le_conjSubgroup (h1029 : Stmt10_2_9) (h : Hyp10 G T L I) {K : Subgroup G}
    (hK : IsLi T L K) (g : G) {x : G} (hx : x ∈ conjSubgroup ⁅fsuVM T L I, K⁆ g) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup (fsuM T L) g := by
  rw [mem_conjSubgroup_iff] at hx
  have hy1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (by
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, h1]
    group)
  intro z hz
  rw [mem_conjSubgroup_iff]
  exact (h1029 G T L I h K hK).1 _ hx hy1 (conj_mem_centralizer_singleton g hz)

theorem centralizer_le_conjSubgroup_inf (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    {K : Subgroup G} (hK : IsLi T L K) (g : G) {x : G}
    (hx : x ∈ conjSubgroup ⁅fsuVM T L I, K⁆ g)
    (hxL : x ∉ conjSubgroup (Subgroup.centralizer (fsuL0 T L : Set G)) g) :
    Subgroup.centralizer ({x} : Set G) ≤
      conjSubgroup (fsuM T L ⊓
        Subgroup.normalizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G)) g := by
  rw [mem_conjSubgroup_iff] at hx
  rw [mem_conjSubgroup_iff] at hxL
  intro z hz
  rw [mem_conjSubgroup_iff]
  exact (h1029 G T L I h K hK).2.2 _ hx hxL (conj_mem_centralizer_singleton g hz)

omit [Finite G] in
theorem conjugate_inf_conjugate_eq_bot {X M : Subgroup G}
    (hX : ∀ g : G, g ∉ M → X ⊓ CFSG.conjugate X g = ⊥) {x y g : G} (hx : x ∈ M) (hy : y ∈ M)
    (hg : g ∉ M) : CFSG.conjugate X x ⊓ CFSG.conjugate X (y * g) = ⊥ := by
  have hg' : y * g * x⁻¹ ∉ M := fun h' => hg (by
    have e : g = y⁻¹ * (y * g * x⁻¹) * x := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (M.inv_mem hy) h') hx)
  have h1 := hX _ hg'
  have h2 : CFSG.conjugate X (y * g) = CFSG.conjugate (CFSG.conjugate X (y * g * x⁻¹)) x := by
    rw [SecA.conjugate_conjugate]
    group
  rw [h2]
  show conjSubgroup X x ⊓ conjSubgroup (CFSG.conjugate X (y * g * x⁻¹)) x = ⊥
  rw [← conjSubgroup_inf, show X ⊓ CFSG.conjugate X (y * g * x⁻¹) = ⊥ from h1, conjSubgroup_bot]

theorem V_inf_conjSubgroup_eq_bot (h10210 : Stmt10_2_10) (h : Hyp10 G T L I) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∉ fsuM T L)
    {X Y : Subgroup G} (hX : X = fsuUL T L I ∨ X = ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hY : Y = fsuUL T L I ∨ Y = ⁅fsuVM T L I, CFSG.conjugate L t⁆) :
    X ⊓ conjSubgroup Y g = ⊥ := by
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  set V2 := ⁅fsuVM T L I, CFSG.conjugate L t⁆ with hV2
  have hTI : ∀ g : G, g ∉ fsuM T L → V2 ⊓ CFSG.conjugate V2 g = ⊥ :=
    fun g hg => (h10210 G T L I h).1 t ht htn g hg
  have hV1 : fsuUL T L I = CFSG.conjugate V2 t⁻¹ := by
    rw [hV2, V2_eq_conjugate ht, SecA.conjugate_conjugate, mul_inv_cancel, SecA.conjugate_one]
  have hV2' : V2 = CFSG.conjugate V2 1 := (SecA.conjugate_one V2).symm
  obtain ⟨x, hxM, rfl⟩ : ∃ x ∈ fsuM T L, X = CFSG.conjugate V2 x := by
    rcases hX with rfl | rfl
    · exact ⟨t⁻¹, (fsuM T L).inv_mem htM, hV1⟩
    · exact ⟨1, (fsuM T L).one_mem, hV2'⟩
  obtain ⟨y, hyM, rfl⟩ : ∃ y ∈ fsuM T L, Y = CFSG.conjugate V2 y := by
    rcases hY with rfl | rfl
    · exact ⟨t⁻¹, (fsuM T L).inv_mem htM, hV1⟩
    · exact ⟨1, (fsuM T L).one_mem, hV2'⟩
  have : conjSubgroup (CFSG.conjugate V2 y) g = CFSG.conjugate V2 (y * g) :=
    SecA.conjugate_conjugate V2 y g
  rw [this]
  exact conjugate_inf_conjugate_eq_bot hTI hxM hyM hg

end CFSG.Quasithin.Vol2.Ch10.SecD
