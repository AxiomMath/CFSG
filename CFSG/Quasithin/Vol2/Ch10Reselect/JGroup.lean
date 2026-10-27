module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML
public import CFSG.Quasithin.Vol2.Ch10Reselect.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_sup_le_of_abelian {V J K L : Subgroup G}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hLV : ∀ l ∈ L, ∀ s ∈ V, l * s * l⁻¹ ∈ V)
    (hJV : J ≤ V) (hKV : K ≤ V) (hJL : ∀ j ∈ J, ∀ l ∈ L, ⁅j, l⁆ ∈ J)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, ⁅k, l⁆ = 1) :
    ⁅J ⊔ K, L⁆ ≤ J := by
  let H₀ : Subgroup G :=
    { carrier := {s | s ∈ V ∧ ∀ l ∈ L, ⁅s, l⁆ ∈ J}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨V.mul_mem ha hb, fun l hl => ?_⟩
        have hc := hV a ha ⁅b, l⁆ (hJV (hb' l hl))
        have e : ⁅a * b, l⁆ = (a * ⁅b, l⁆ * a⁻¹) * ⁅a, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hc, mul_inv_cancel_right]
        exact J.mul_mem (hb' l hl) (ha' l hl)
      one_mem' := ⟨V.one_mem, fun l _ => by
        rw [commutatorElement_def]
        simp [J.one_mem]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨V.inv_mem ha, fun l hl => ?_⟩
        have hc2 := hV a⁻¹ (V.inv_mem ha) (l * a * l⁻¹) (hLV l hl a ha)
        have e : ⁅a⁻¹, l⁆ = (⁅a, l⁆)⁻¹ := by
          calc ⁅a⁻¹, l⁆ = a⁻¹ * (l * a * l⁻¹) := by
                simp only [commutatorElement_def, inv_inv]
                group
            _ = (l * a * l⁻¹) * a⁻¹ := hc2
            _ = (⁅a, l⁆)⁻¹ := by
                simp only [commutatorElement_def]
                group
        rw [e]
        exact J.inv_mem (ha' l hl) }
  have hS : J ⊔ K ≤ H₀ :=
    sup_le (fun j hj => ⟨hJV hj, fun l hl => hJL j hj l hl⟩)
      (fun k hk => ⟨hKV hk, fun l hl => by rw [hKL k hk l hl]; exact J.one_mem⟩)
  exact Subgroup.commutator_le.mpr fun s hs l hl => (hS hs).2 l hl

structure JData (T L I J : Subgroup G) : Prop where
  fsu : FSU G T L I
  lt : L < fsuL0 T L
  hA : Concl326A T L I
  le_U : J ≤ fsuUL T L I
  perf : ⁅J, L⁆ = J
  norm : fsuML T L ≤ Subgroup.normalizer (J : Set G)

namespace JData

variable {T L I J : Subgroup G}

private theorem conj_inj {X Y : Subgroup G} {x : G}
    (h : CFSG.conjugate X x = CFSG.conjugate Y x) : X = Y := by
  have h' := congrArg (fun Z : Subgroup G => CFSG.conjugate Z x⁻¹) h
  simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_one] using h'

private theorem conj_sup_of_perm {P Q : Subgroup G} {x : G}
    (h1 : CFSG.conjugate P x = P ∨ CFSG.conjugate P x = Q)
    (h2 : CFSG.conjugate Q x = P ∨ CFSG.conjugate Q x = Q) :
    CFSG.conjugate (P ⊔ Q) x = P ⊔ Q := by
  have hsup : CFSG.conjugate (P ⊔ Q) x = CFSG.conjugate P x ⊔ CFSG.conjugate Q x := by
    simp only [conjugate_eq_map, Subgroup.map_sup]
  rw [hsup]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hPQ : P = Q := conj_inj (h1.trans h2.symm)
    rw [h1, h2, ← hPQ]
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]
  · have hPQ : P = Q := conj_inj (h1.trans h2.symm)
    rw [h1, h2, ← hPQ]

theorem le_fsuVM (hJ : JData T L I J) : J ≤ fsuVM T L I :=
  hJ.le_U.trans (fsuUL_le_fsuVM T L I)

theorem conjugate_eq_or (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hJ : JData T L I J) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ fsuM T L) :
    CFSG.conjugate J x = J ∨ CFSG.conjugate J x = CFSG.conjugate J t := by
  have hL := conjugate_eq_or_of_fsu h37 h38 hJ.fsu (not_le_normalizer_of_lt hJ.lt) ht htn hx
  rcases hL with h | h
  · have hxN : x ∈ Subgroup.normalizer (L : Set G) := conjugate_eq_self_iff.mp h
    exact Or.inl (conjugate_eq_self_iff.mpr (hJ.norm (Subgroup.mem_inf.mpr ⟨hx, hxN⟩)))
  · have hs : x * t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_inv_mem_normalizer_of_conjugate_eq h
    have hsM : x * t⁻¹ ∈ fsuM T L :=
      (fsuM T L).mul_mem hx ((fsuM T L).inv_mem (le_fsuM T L ht))
    have hJs : CFSG.conjugate J (x * t⁻¹) = J :=
      conjugate_eq_self_iff.mpr (hJ.norm (Subgroup.mem_inf.mpr ⟨hsM, hs⟩))
    right
    calc CFSG.conjugate J x = CFSG.conjugate J (x * t⁻¹ * t) := by rw [inv_mul_cancel_right]
      _ = CFSG.conjugate (CFSG.conjugate J (x * t⁻¹)) t := by rw [conjugate_conjugate]
      _ = CFSG.conjugate J t := by rw [hJs]

theorem fsuV_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hJ : JData T L I J) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) : fsuV T J = J ⊔ CFSG.conjugate J t := by
  refine le_antisymm (conjClosure_le fun y hy z hz => ?_) (sup_le (le_conjClosure J T) ?_)
  · have hc : y * z * y⁻¹ ∈ CFSG.conjugate J y⁻¹ := by
      have h := conj_mem_conjugate (X := J) y⁻¹ hz
      rwa [inv_inv] at h
    rcases conjugate_eq_or h37 h38 hJ ht htn (le_fsuM T L (T.inv_mem hy)) with h | h
    · rw [h] at hc
      exact Subgroup.mem_sup_left hc
    · rw [h] at hc
      exact Subgroup.mem_sup_right hc
  · intro x hx
    exact Subgroup.subset_closure ⟨t⁻¹, T.inv_mem ht, t * x * t⁻¹, mem_conjugate_iff.mp hx,
      by group⟩

theorem fsuM_le_normalizer_sup (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hJ : JData T L I J) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuM T L ≤ Subgroup.normalizer ((J ⊔ CFSG.conjugate J t : Subgroup G) : Set G) := by
  intro x hx
  refine conjugate_eq_self_iff.mp ?_
  have h1 := conjugate_eq_or h37 h38 hJ ht htn hx
  have htx : t * x ∈ fsuM T L := (fsuM T L).mul_mem (le_fsuM T L ht) hx
  have h2 : CFSG.conjugate (CFSG.conjugate J t) x = J ∨
      CFSG.conjugate (CFSG.conjugate J t) x = CFSG.conjugate J t := by
    rw [conjugate_conjugate]
    exact conjugate_eq_or h37 h38 hJ ht htn htx
  exact conj_sup_of_perm h1 h2

theorem fsuVM_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hJ : JData T L I J) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) : fsuVM T L J = fsuV T J := by
  have hN : ∀ m ∈ fsuM T L, m ∈ Subgroup.normalizer (fsuV T J : Set G) := by
    intro m hm
    have he : CFSG.conjugate (fsuV T J) m = fsuV T J := by
      rw [fsuV_eq h37 h38 hJ ht htn]
      exact conjugate_eq_self_iff.mpr (fsuM_le_normalizer_sup h37 h38 hJ ht htn hm)
    exact conjugate_eq_self_iff.mp he
  exact le_antisymm (conjClosure_le fun m hm z hz => (Subgroup.mem_normalizer_iff.mp (hN m hm) z).mp hz)
    (le_conjClosure _ _)

theorem conjugate_le_centralizer (hJ : JData T L I J) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    CFSG.conjugate J t ≤ Subgroup.centralizer (L : Set G) :=
  (conjugate_mono hJ.le_U t).trans
    (conjugate_UL_le_centralizer h37 h38 hJ.fsu hJ.lt hJ.hA ht htn)

theorem conjugate_le_fsuVM (hJ : JData T L I J) {t : G} (ht : t ∈ T) :
    CFSG.conjugate J t ≤ fsuVM T L I :=
  (conjugate_mono hJ.le_U t).trans (conjugate_UL_le_fsuVM T L I (le_fsuM T L ht))

theorem sup_le_fsuVM (hJ : JData T L I J) {t : G} (ht : t ∈ T) :
    J ⊔ CFSG.conjugate J t ≤ fsuVM T L I :=
  sup_le hJ.le_fsuVM (conjugate_le_fsuVM hJ ht)

theorem fsuUL_eq
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    [IsMulCommutative ↥(fsuVM T L I)] (hJ : JData T L I J) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) : fsuUL T L J = J := by
  have hJV : J ≤ fsuVM T L I := le_fsuVM hJ
  have hKV : CFSG.conjugate J t ≤ fsuVM T L I := conjugate_le_fsuVM hJ ht
  have hKL : CFSG.conjugate J t ≤ Subgroup.centralizer (L : Set G) :=
    conjugate_le_centralizer hJ ht htn h37 h38
  have hV : ∀ x ∈ fsuVM T L I, ∀ y ∈ fsuVM T L I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(fsuVM T L I)) ⟨y, hy⟩)
  have hLV : ∀ l ∈ L, ∀ s ∈ fsuVM T L I, l * s * l⁻¹ ∈ fsuVM T L I := fun l hl s hs =>
    (Subgroup.mem_normalizer_iff.mp (fsuL0_le_normalizer_fsuVM T L I (le_fsuL0 T L hl)) s).mp hs
  have hJL : ∀ j ∈ J, ∀ l ∈ L, ⁅j, l⁆ ∈ J := fun j hj l hl => by
    have h := Subgroup.commutator_mem_commutator hj hl
    rwa [hJ.perf] at h
  have hKL : ∀ k ∈ CFSG.conjugate J t, ∀ l ∈ L, ⁅k, l⁆ = 1 := fun k hk l hl => by
    have h := Subgroup.mem_centralizer_iff.mp (hKL hk) l hl
    rw [commutatorElement_def, ← h, mul_inv_cancel_right, mul_inv_cancel]
  show ⁅fsuVM T L J, L⁆ = J
  rw [fsuVM_eq h37 h38 hJ ht htn, fsuV_eq h37 h38 hJ ht htn]
  apply le_antisymm
  · exact commutator_sup_le_of_abelian hV hLV hJV hKV hJL hKL
  · calc J = ⁅J, L⁆ := hJ.perf.symm
      _ ≤ ⁅J ⊔ CFSG.conjugate J t, L⁆ := Subgroup.commutator_mono le_sup_left le_rfl

end JData

end CFSG.Quasithin.Vol2.Ch10Reselect
