module

public import CFSG.Monster.GMS.Leech.Data
public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.Facts.Section4Coh
import CFSG.Monster.GMS.Leech.Pairs
import CFSG.Monster.GMS.Griess13.ChecksUniqueness
import CFSG.Sporadic.Co1.Module.Pairs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act
open scoped commutatorElement

namespace LeechCoh

section Linear

theorem co1_eq_one_of_forall_act (A : Co1) (h : ∀ v, co1Act A v = v) : A = 1 := by
  refine Units.ext (Subtype.ext ?_)
  rw [Matrix.ext_iff_mulVec]
  intro v
  simp only [Units.val_one, Submonoid.coe_one, Matrix.one_mulVec]
  exact h v

theorem eq_zero_or_eq_of_forall_perp
    {u x : Fin 24 → ZMod 2} (hu : u ≠ 0)
    (hx : ∀ h, bil₀ h u = 0 → bil₀ x h = 0) : x = 0 ∨ x = u := by
  by_contra hne
  push Not at hne
  obtain ⟨hx0, hxu⟩ := hne
  have hind : LinearIndependent (ZMod 2) ![u, x] :=
    Leech.linearIndependent_fin_two hu hx0 (Ne.symm hxu)
  obtain ⟨h, hh⟩ := Leech.exists_bil₀_eq hind ![0, 1]
  have h0 : bil₀ h u = 0 := by simpa using hh 0
  have h1 : bil₀ h x = 1 := by simpa using hh 1
  have h2 := hx h h0
  rw [bil₀_comm, h1] at h2
  exact one_ne_zero h2

theorem eq_one_of_fix_perp
    {u : Fin 24 → ZMod 2} (hu : u ≠ 0) (hq : q₀ u = 0) (A : Co1)
    (hA : ∀ v, bil₀ v u = 0 → co1Act A v = v) : A = 1 := by
  refine co1_eq_one_of_forall_act A fun v => ?_
  have horth : ∀ h, bil₀ h u = 0 → bil₀ (co1Act A v + v) h = 0 := by
    intro h hh
    rw [Leech.bil₀_add_left]
    have e1 : bil₀ (co1Act A v) h = bil₀ v h := by
      have := Leech.bil₀_co1Act A v h
      rwa [hA h hh] at this
    rw [e1]
    exact CharTwo.add_self_eq_zero _
  rcases eq_zero_or_eq_of_forall_perp hu horth with h0 | h1
  · exact (eq_neg_of_add_eq_zero_left h0).trans (Leech.neg_eq_self v)
  · exfalso
    have hAv : co1Act A v = u + v := by
      calc co1Act A v = (co1Act A v + v) + v := by rw [add_assoc, vec_add_self, add_zero]
        _ = u + v := by rw [h1]
    have hq1 : q₀ (co1Act A v) = q₀ v := CFSG.Sporadic.Co1.Module.q₀_co1Act A v
    rw [hAv, q₀_add, hq, zero_add] at hq1
    have hb : bil₀ v u = 0 := by
      rw [bil₀_comm]
      simpa using hq1
    have h2 := hA v hb
    rw [h2, vec_add_self] at h1
    exact hu h1.symm

end Linear

section Group

variable {G : Type*} [Group G] {t' : G}

theorem mem_of_forall_comm
    (L : LeechSystem t') {t : G} (htL : t ∈ L.typeSet 0) {g : G}
    (hg : g ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'})
    (hgn : ∀ n ∈ leechQ t' ⊓ Subgroup.centralizer {t}, g * n = n * g) :
    g = 1 ∨ g = t ∨ g = t' ∨ g = t * t' := by
  have htQ : t ∈ leechQ t' := htL.1
  have hu : L.vec t ≠ 0 := L.vec_ne_zero_of_mem_typeSet htL
  have hq : q₀ (L.vec t) = 0 := Leech.q₀_eq_zero_of_mem_co1Orbit_zero htL.2
  have hperp : ∀ p ∈ leechQ t', bil₀ (L.vec p) (L.vec t) = 0 → g * p = p * g := by
    intro p hp hb
    have hpC : p ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp ((L.comm_eq_one_iff hp htQ).2 hb))
    exact hgn p ⟨hp, hpC⟩
  have hfix : ∀ v, bil₀ v (L.vec t) = 0 → co1Act (L.φ ⟨g, hg.2⟩) v = v := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := L.vec_surj v
    have h1 := L.vec_conj ⟨g, hg.2⟩ p hp
    have h2 : g * p * g⁻¹ = p := by rw [hperp p hp hv]; group
    rw [show ((⟨g, hg.2⟩ : Subgroup.centralizer ({t'} : Set G)) : G) = g from rfl, h2] at h1
    exact h1.symm
  have hgQ : g ∈ leechQ t' :=
    (L.φ_ker ⟨g, hg.2⟩).1 (eq_one_of_fix_perp hu hq _ hfix)
  have hvg : L.vec g = 0 ∨ L.vec g = L.vec t := by
    refine eq_zero_or_eq_of_forall_perp hu fun v hv => ?_
    obtain ⟨p, hp, rfl⟩ := L.vec_surj v
    have hc : ⁅g, p⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hperp p hp hv)
    exact (L.comm_eq_one_iff hgQ hp).1 hc
  rcases hvg with h0 | h1
  · rcases (L.vec_eq_zero g hgQ).1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases L.eq_or_eq_mul_z hgQ htQ h1 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

theorem exists_mem_typeSet_zero_comm
    (hP : Co1PairFacts) (L : LeechSystem t') {t : G}
    (htL : t ∈ L.typeSet 0) :
    ∃ y ∈ L.typeSet 0, y ∈ Subgroup.centralizer ({t} : Set G) ∧ y ≠ t ∧ y ≠ t * t' := by
  have htQ : t ∈ leechQ t' := htL.1
  obtain ⟨v, hv, huv, -⟩ := hP.1 (L.vec t) htL.2
  obtain ⟨y, hyQ, hyv⟩ := L.vec_surj v
  have hyL : y ∈ L.typeSet 0 := ⟨hyQ, by rw [hyv]; exact hv⟩
  have hb : bil₀ (L.vec y) (L.vec t) = 0 := by
    have h := q₀_add (L.vec t) v
    rw [Leech.q₀_eq_zero_of_mem_co1Orbit_zero huv, Leech.q₀_eq_zero_of_mem_co1Orbit_zero htL.2,
      Leech.q₀_eq_zero_of_mem_co1Orbit_zero hv, zero_add, zero_add] at h
    rw [hyv, bil₀_comm]
    exact h.symm
  have hne : L.vec y ≠ L.vec t := by
    intro h
    rw [hyv] at h
    rw [h, vec_add_self] at huv
    exact Leech.ne_zero_of_mem_co1Orbit huv rfl
  refine ⟨y, hyL, Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp ((L.comm_eq_one_iff hyQ htQ).2 hb)), ?_, ?_⟩
  · intro h
    exact hne (by rw [h])
  · intro h
    exact hne (by rw [h, L.vec_mul_z htQ])

end Group

end LeechCoh

section Main

variable {G : Type*} [Group G]

@[expose] def CoTwoPerfect (a z₀ : G) : Prop :=
  ∀ t t' : G, IsConj a t → IsConj z₀ t' → t * t' = t' * t → IsConj a (t * t') →
    ⁅Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'},
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'}⁆ =
        Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer {t'}

end Main

theorem coTwoStructure_of
    {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hperf : CoTwoPerfect a z₀) :
    CoTwoStructure a z₀ := by
  intro t t' ht ht' hcomm hmul
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness (h.gms t' ht')
  have htQ : t ∈ leechQ t' := h.mem_leechQ_of_isConj_mul ht ht' hcomm hmul
  have htL : t ∈ L.typeSet 0 := L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem ht' htQ ht)
  refine ⟨hperf t t' ht ht' hcomm hmul,
    fun g hg hgn => LeechCoh.mem_of_forall_comm L htL hg hgn, ?_⟩
  obtain ⟨y, hyL, hyC, hyt, hyt'⟩ := LeechCoh.exists_mem_typeSet_zero_comm co1PairFacts L htL
  obtain ⟨c, -, hcy⟩ := L.exists_conj_of_mem_typeSet htL hyL
  exact ⟨y, Subgroup.mem_inf.mpr ⟨hyL.1, hyC⟩, ht.trans (isConj_iff.mpr ⟨c, hcy⟩), hyt, hyt'⟩

end CFSG.Monster.GMS
