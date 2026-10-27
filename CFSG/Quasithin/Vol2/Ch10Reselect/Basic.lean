module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Statements
public import CFSG.Quasithin.Vol2.Ch8Sec3L0Cent

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_le_normalizer_of_lt (hlt : L < fsuL0 T L) :
    ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hT =>
  hlt.ne (le_antisymm (le_conjClosure L T) (conjClosure_le fun _ hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (hT hg) z).mp hz))

theorem pRank_fsuM_le_two (hfsu : FSU G T L I) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (fsuM T L) ≤ 2 :=
  pRank_le_two_of_pCoreOf_ne_bot hfsu.qtke (pCoreOf_fsuM_ne_bot hfsu.faithful) hr hr2

theorem mem_normalizer_of_odd_orderOf (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) {s : G}
    (hs : s ∈ fsuM T L) (hodd : Odd (orderOf s)) : s ∈ Subgroup.normalizer (L : Set G) := by
  have hnn := not_le_normalizer_of_lt hlt
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  by_contra hsn
  have h1 : CFSG.conjugate L (s * s) = L ∨ CFSG.conjugate L (s * s) = CFSG.conjugate L t :=
    conjugate_eq_or_of_fsu h37 h38 hfsu hnn ht htn ((fsuM T L).mul_mem hs hs)
  have h2 : CFSG.conjugate L s = L ∨ CFSG.conjugate L s = CFSG.conjugate L t :=
    conjugate_eq_or_of_fsu h37 h38 hfsu hnn ht htn hs
  have h3 : s * s ∈ Subgroup.normalizer (L : Set G) := by
    rcases h1 with h | h
    · exact conjugate_eq_self_iff.mp h
    · rcases h2 with h' | h'
      · exact absurd (conjugate_eq_self_iff.mp h') hsn
      · have := mul_inv_mem_normalizer_of_conjugate_eq (h.trans h'.symm)
        rw [mul_inv_cancel_right] at this
        exact absurd this hsn
  obtain ⟨k, hk⟩ := hodd
  have hpow : s ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one s
  have hss : s = (s * s) ^ (k + 1) := by
    calc s = s ^ (2 * k + 1) * s := by rw [hpow, one_mul]
      _ = s ^ (2 * (k + 1)) := by rw [← pow_succ]; congr 1
      _ = (s * s) ^ (k + 1) := by rw [pow_mul, sq]
  exact hsn (hss ▸ Subgroup.pow_mem _ h3 _)

theorem mem_normalizer_conjugate_of_mem_normalizer
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {s : G} (hs : s ∈ fsuM T L) (hsL : s ∈ Subgroup.normalizer (L : Set G)) :
    s ∈ Subgroup.normalizer ((CFSG.conjugate L t : Subgroup G) : Set G) := by
  have hnn := not_le_normalizer_of_lt hlt
  have h1 : CFSG.conjugate L (t * s) = L ∨ CFSG.conjugate L (t * s) = CFSG.conjugate L t :=
    conjugate_eq_or_of_fsu h37 h38 hfsu hnn ht htn ((fsuM T L).mul_mem (le_fsuM T L ht) hs)
  rcases h1 with h | h
  · exfalso
    have h' : t * s ∈ Subgroup.normalizer (L : Set G) := conjugate_eq_self_iff.mp h
    have := (Subgroup.normalizer (L : Set G)).mul_mem h' ((Subgroup.normalizer (L : Set G)).inv_mem hsL)
    rw [mul_inv_cancel_right] at this
    exact htn this
  · exact conjugate_eq_self_iff.mp (by rw [conjugate_conjugate]; exact h)

theorem conjugate_le_centralizer_conjugate {X Y : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Y : Set G)) (g : G) :
    CFSG.conjugate X g ≤ Subgroup.centralizer ((CFSG.conjugate Y g : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, mem_conjugate_iff] at hy
  rw [mem_conjugate_iff] at hx
  have h1 := Subgroup.mem_centralizer_iff.mp (h hx) _ hy
  calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
    _ = x * y := by group

theorem conjugate_UL_le_centralizer (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate (fsuUL T L I) t ≤ Subgroup.centralizer (L : Set G) := by
  have h1 := conjugate_le_centralizer_conjugate (hA t ht htn).2.2 t
  rwa [conjugate_conjugate, conjugate_eq_self_iff.mpr
    (mul_self_mem_normalizer_of_fsu h37 h38 hfsu (not_le_normalizer_of_lt hlt) ht htn)] at h1

theorem fsuVM_eq_sup_of_A (hA : Concl326A T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuVM T L I = fsuUL T L I ⊔ CFSG.conjugate (fsuUL T L I) t ⊔ fsuCVM T L I :=
  (hA t ht htn).1.symm

theorem mem_centralizer_of_le_centralizer_singleton {x : G} {A : Subgroup G}
    (h : A ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ Subgroup.centralizer (A : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (h ha) x (Set.mem_singleton x)).symm

theorem mem_centralizer_fsuVM_of_UL (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    (hA : Concl326A T L I) {x : G} (hx : x ∈ L)
    (hxU : x ∈ Subgroup.centralizer (fsuUL T L I : Set G)) :
    x ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  rw [fsuVM_eq_sup_of_A hA ht htn]
  refine mem_centralizer_of_le_centralizer_singleton (sup_le (sup_le ?_ ?_) ?_)
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp hxU u hu).symm
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp
      (conjugate_UL_le_centralizer h37 h38 hfsu hlt hA ht htn hu) x hx
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hc.2 x (le_fsuL0 T L hx)

end CFSG.Quasithin.Vol2.Ch10Reselect
