module

public import CFSG.Quasithin.EmptyFaithful.S153Odd
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS13

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem mem_normalizer_conjugate {X : Subgroup G} {g y : G}
    (h : g * y * g⁻¹ ∈ Subgroup.normalizer (X : Set G)) :
    y ∈ Subgroup.normalizer (CFSG.conjugate X g : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [SecA.mem_conjugate_iff, SecA.mem_conjugate_iff,
    Subgroup.mem_normalizer_iff.mp h (g * x * g⁻¹)]
  have e : g * y * g⁻¹ * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * x * y⁻¹) * g⁻¹ := by group
  rw [e]

theorem conjugate_ne_bot {X : Subgroup G} (hX : X ≠ ⊥) (g : G) : CFSG.conjugate X g ≠ ⊥ := by
  obtain ⟨⟨x, hx⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  intro hb
  have h1 : g⁻¹ * x * g ∈ CFSG.conjugate X g := SecA.conj_mem_conjugate g hx
  rw [hb, Subgroup.mem_bot] at h1
  apply hx1
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem T1_le_normalizer_fsuUL (T L I : Subgroup G) :
    Ch10.T1 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  SecA.le_normalizer_commutator (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)) inf_le_right

variable [Finite G]

structure S5Data (T L I H K : Subgroup G) (q t : G) : Prop where
  hyp : Hyp10 G T L I
  two : Ch10.Case10_1_1Two T L I
  block : IsShort2 L ∧ IsAltType L 5
  ht : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set G)
  hTH : T ≤ H
  hK : K ∈ cComp H
  hKs : IsShort2 K
  hKa : IsAltType K 5
  hqK : q ∈ K
  hqL : q ∈ L
  hq3 : orderOf q = 3
  hT1K : Ch10.T1 T L ≤ Subgroup.normalizer (K : Set G)
  hKM : ¬ K ≤ fsuM T L

namespace S5Data

variable {T L I H K : Subgroup G} {q t : G} (D : S5Data T L I H K q t)
include D

theorem fsuUL_le_T1 : fsuUL T L I ≤ Ch10.T1 T L := by
  have hVV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  exact le_inf (hVV.trans (SecA.fsuVM_le_T D.hyp))
    (((SecE.fsuUL_le_pCoreOf_L D.hyp).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans
      Subgroup.le_normalizer)

theorem R_le_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    CFSG.conjugate (fsuUL T L I ⊓ K) t ≤ Ch10.T1 T L := by
  intro x hx
  have h1 : t * x * t⁻¹ ∈ Ch10.T1 T L := D.fsuUL_le_T1 (SecA.mem_conjugate_iff.mp hx).1
  have h2 := (Subgroup.mem_normalizer_iff.mp
    (SecE.le_normalizer_T1 h37 h38 D.hyp (T.inv_mem D.ht))
    (t * x * t⁻¹)).mp h1
  have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem T1_le_normalizer_R (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    Ch10.T1 T L ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I ⊓ K) t : Set G) := by
  intro y hy
  have hy' : t * y * t⁻¹ ∈ Ch10.T1 T L :=
    (Subgroup.mem_normalizer_iff.mp (SecE.le_normalizer_T1 h37 h38 D.hyp D.ht) y).mp hy
  exact mem_normalizer_conjugate (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨T1_le_normalizer_fsuUL T L I hy', D.hT1K hy'⟩)

theorem L_le_centralizer_R (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    L ≤ Subgroup.centralizer (CFSG.conjugate (fsuUL T L I ⊓ K) t : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  refine SecA.conjugate_fsuUL_le_centralizer h37 h38 D.hyp D.ht D.htn ?_
  rw [SecA.mem_conjugate_iff] at hx ⊢
  exact hx.1

theorem q2_mem_normalizer_R :
    t⁻¹ * q * t ∈ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I ⊓ K) t : Set G) := by
  refine mem_normalizer_conjugate ?_
  have e : t * (t⁻¹ * q * t) * t⁻¹ = q := by group
  rw [e]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨SecC.le_normalizer_fsuUL T L I D.hqL, Subgroup.le_normalizer D.hqK⟩

theorem exists_moved : ∃ w ∈ CFSG.conjugate (fsuUL T L I ⊓ K) t,
    (t⁻¹ * q * t) * w * (t⁻¹ * q * t)⁻¹ ≠ w := by
  have hq3' : q ^ 3 = 1 := by rw [← D.hq3]; exact pow_orderOf_eq_one q
  obtain ⟨v, hv, hvq⟩ := Set.not_subset.mp (not_le_centralizer_of_three D.hyp D.two D.hqL D.hq3)
  have hvq' : q * v * q⁻¹ * v⁻¹ ≠ 1 := by
    intro h
    apply hvq
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    calc v * q = q * v * q⁻¹ * v⁻¹ * v * q * (q⁻¹ * q) := by rw [h]; group
      _ = q * v := by group
  have hLV := SecC.le_normalizer_fsuUL T L I
  have huV : q * v * q⁻¹ * v⁻¹ ∈ fsuUL T L I :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hLV D.hqL) v).mp hv)
      (Subgroup.inv_mem _ hv)
  have huK : q * v * q⁻¹ * v⁻¹ ∈ K := by
    have h1 : v * q⁻¹ * v⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (D.hT1K (D.fsuUL_le_T1 hv)) _).mp (K.inv_mem D.hqK)
    have e : q * v * q⁻¹ * v⁻¹ = q * (v * q⁻¹ * v⁻¹) := by group
    rw [e]
    exact K.mul_mem D.hqK h1
  have hsq : (q * v * q⁻¹ * v⁻¹) * (q * v * q⁻¹ * v⁻¹) = 1 := by
    have hVV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
    rw [← pow_two]
    exact (SecA.isElemAbelian_fsuVM D.hyp).2 _ (hVV huV)
  refine ⟨t⁻¹ * (q * v * q⁻¹ * v⁻¹) * t, ?_, fun h => hvq' ?_⟩
  · rw [SecA.mem_conjugate_iff]
    have e : t * (t⁻¹ * (q * v * q⁻¹ * v⁻¹) * t) * t⁻¹ = q * v * q⁻¹ * v⁻¹ := by group
    rw [e]
    exact ⟨huV, huK⟩
  · refine eq_one_of_conj_fixed hq3' ?_ hsq
    have e : t⁻¹ * q * t * (t⁻¹ * (q * v * q⁻¹ * v⁻¹) * t) * (t⁻¹ * q * t)⁻¹ =
        t⁻¹ * (q * (q * v * q⁻¹ * v⁻¹) * q⁻¹) * t := by group
    rw [e] at h
    calc q * (q * v * q⁻¹ * v⁻¹) * q⁻¹
        = t * (t⁻¹ * (q * (q * v * q⁻¹ * v⁻¹) * q⁻¹) * t) * t⁻¹ := by group
      _ = t * (t⁻¹ * (q * v * q⁻¹ * v⁻¹) * t) * t⁻¹ := by rw [h]
      _ = q * v * q⁻¹ * v⁻¹ := by group

theorem R_ne_bot : CFSG.conjugate (fsuUL T L I ⊓ K) t ≠ ⊥ := by
  obtain ⟨w, hw, hmov⟩ := D.exists_moved
  intro hb
  rw [hb, Subgroup.mem_bot] at hw
  apply hmov
  rw [hw]
  group

theorem isSylowTwoOf_of_le_normalizer
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) {X : Subgroup G}
    (hT1X : Ch10.T1 T L ≤ X)
    (hXR : X ≤ Subgroup.normalizer (CFSG.conjugate (fsuUL T L I ⊓ K) t : Set G)) :
    IsSylowTwoOf (Ch10.T1 T L) X := by
  by_contra hns
  obtain ⟨m, hmN, hTm⟩ := exists_conj_of_not_isSylowTwoOf D.hyp.fsu.sylow inf_le_left
    (SecA.index_T1 h37 h38 D.hyp) (SecE.le_normalizer_T1 h37 h38 D.hyp) hT1X hns
  have hmM : m ∈ fsuM T L :=
    SecE.normalizer_T1_le h311 h331 h37 h38 hshape D.hyp (Or.inr D.two) hmN
  have hTR' : T ≤ Subgroup.normalizer
      (CFSG.conjugate (CFSG.conjugate (fsuUL T L I ⊓ K) t) m⁻¹ : Set G) := fun x hx =>
    mem_normalizer_conjugate (by rw [inv_inv]; exact hXR (B6.mem_conjSub.mp (hTm hx)))
  have hR'V : ∀ y ∈ CFSG.conjugate (CFSG.conjugate (fsuUL T L I ⊓ K) t) m⁻¹,
      y ∈ fsuUL T L I ∨ y ∈ CFSG.conjugate (fsuUL T L I) t := by
    intro y hy
    have h1 := (SecA.mem_conjugate_iff.mp (SecA.mem_conjugate_iff.mp hy)).1
    have hmem : y ∈ CFSG.conjugate (fsuUL T L I) (t * m⁻¹) := by
      rw [SecA.mem_conjugate_iff]
      have e : t * m⁻¹ * y * (t * m⁻¹)⁻¹ = t * (m⁻¹ * y * m⁻¹⁻¹) * t⁻¹ := by group
      rw [e]
      exact h1
    have hsM : t * m⁻¹ ∈ fsuM T L :=
      (fsuM T L).mul_mem (SecA.le_fsuM T L D.ht) ((fsuM T L).inv_mem hmM)
    rcases conjugate_fsuUL_eq_or h37 h38 D.hyp D.ht D.htn hsM with h | h
    · exact Or.inl (h ▸ hmem)
    · exact Or.inr (h ▸ hmem)
  have hR'T : CFSG.conjugate (CFSG.conjugate (fsuUL T L I ⊓ K) t) m⁻¹ ≤ T := by
    intro y hy
    rcases hR'V y hy with h | h
    · exact (D.fsuUL_le_T1 h).1
    · have h1 := (D.fsuUL_le_T1 (SecA.mem_conjugate_iff.mp h)).1
      have e : y = t⁻¹ * (t * y * t⁻¹) * t := by group
      rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem D.ht) h1) D.ht
  obtain ⟨z, hzR', hz1, hzc⟩ := exists_ne_one_mem_center_of_normalized D.hyp.fsu.sylow.1 hR'T
    (conjugate_ne_bot D.R_ne_bot m⁻¹) hTR'
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc y hy)
  exact hz1 (eq_one_of_le_centralizer h37 h38 D.hyp D.two D.ht D.htn (hR'V z hzR') hTc)

end S5Data

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
