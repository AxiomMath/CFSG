module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2Cyc
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut

open Matrix
open scoped commutatorElement

variable {F : Type*} [Field F]

theorem NormScalar.mul_self_eq_one {T g : GL (Fin 2) F} {a : F}
    (h : NormScalar (T : Matrix (Fin 2) (Fin 2) F) g a) : a * a = 1 := by
  have hdg : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]; exact (GeneralLinearGroup.det g).ne_zero
  have hdt : (T : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]; exact (GeneralLinearGroup.det T).ne_zero
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at this
  have h4 : (a ^ 2 - 1) * ((T : Matrix (Fin 2) (Fin 2) F).det *
      (g : Matrix (Fin 2) (Fin 2) F).det) = 0 := by linear_combination (-1 : F) * this
  rcases mul_eq_zero.mp h4 with h5 | h5
  · linear_combination h5
  · exact absurd h5 (mul_ne_zero hdt hdg)

theorem anticommute_of_involutions {x y : GL (Fin 2) F} (h2 : (2 : F) ≠ 0)
    (hxx : ProjGenLinGroup.mk x ^ 2 = 1) (hyy : ProjGenLinGroup.mk y ^ 2 = 1)
    (hx1 : ProjGenLinGroup.mk x ≠ 1) (hy1 : ProjGenLinGroup.mk y ≠ 1)
    (hne : ProjGenLinGroup.mk x ≠ ProjGenLinGroup.mk y)
    (hcomm : ProjGenLinGroup.mk x * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk x) :
    (y : Matrix (Fin 2) (Fin 2) F) * x = -((x : Matrix (Fin 2) (Fin 2) F) * y) := by
  obtain ⟨a, ha⟩ := exists_normScalar_of_commute hcomm.symm
  rcases mul_self_eq_one_iff.mp (NormScalar.mul_self_eq_one ha) with h1 | h1
  · exfalso
    rw [h1] at ha
    have hxy := NormScalar.one_iff.mp ha
    exact hne (eq_of_involutions_of_commute h2 (nonscalar_of_ne_one hx1) rfl hxy.symm hxx hyy
      hx1 hy1)
  · rw [h1] at ha
    unfold NormScalar at ha
    rw [ha, neg_one_smul]

theorem eq_mul_of_commuting_involutions {a b c : GL (Fin 2) F} (h2 : (2 : F) ≠ 0)
    (ha2 : ProjGenLinGroup.mk a ^ 2 = 1) (hb2 : ProjGenLinGroup.mk b ^ 2 = 1)
    (hc2 : ProjGenLinGroup.mk c ^ 2 = 1)
    (ha1 : ProjGenLinGroup.mk a ≠ 1) (hb1 : ProjGenLinGroup.mk b ≠ 1)
    (hc1 : ProjGenLinGroup.mk c ≠ 1)
    (hab : ProjGenLinGroup.mk a ≠ ProjGenLinGroup.mk b)
    (hac : ProjGenLinGroup.mk a ≠ ProjGenLinGroup.mk c)
    (hbc : ProjGenLinGroup.mk b ≠ ProjGenLinGroup.mk c)
    (hab' : ProjGenLinGroup.mk a * ProjGenLinGroup.mk b =
      ProjGenLinGroup.mk b * ProjGenLinGroup.mk a)
    (hac' : ProjGenLinGroup.mk a * ProjGenLinGroup.mk c =
      ProjGenLinGroup.mk c * ProjGenLinGroup.mk a)
    (hbc' : ProjGenLinGroup.mk b * ProjGenLinGroup.mk c =
      ProjGenLinGroup.mk c * ProjGenLinGroup.mk b) :
    ProjGenLinGroup.mk c = ProjGenLinGroup.mk a * ProjGenLinGroup.mk b := by
  have hca := anticommute_of_involutions h2 ha2 hc2 ha1 hc1 hac hac'
  have hcb := anticommute_of_involutions h2 hb2 hc2 hb1 hc1 hbc hbc'
  have hab2 : ProjGenLinGroup.mk (a * b) ^ 2 = 1 := by
    rw [map_mul, Commute.mul_pow hab', ha2, hb2, one_mul]
  have hab1 : ProjGenLinGroup.mk (a * b) ≠ 1 := by
    intro h
    rw [map_mul] at h
    apply hab
    have h3 : ProjGenLinGroup.mk b = (ProjGenLinGroup.mk a)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h3]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact ha2)
  have hcomm : (c : Matrix (Fin 2) (Fin 2) F) * ((a * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ((a * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * c := by
    rw [Units.val_mul]
    calc (c : Matrix (Fin 2) (Fin 2) F) * ((a : Matrix (Fin 2) (Fin 2) F) * b)
        = ((c : Matrix (Fin 2) (Fin 2) F) * a) * b := (Matrix.mul_assoc _ _ _).symm
      _ = -((a : Matrix (Fin 2) (Fin 2) F) * (c * b)) := by rw [hca, neg_mul, Matrix.mul_assoc]
      _ = ((a : Matrix (Fin 2) (Fin 2) F) * b) * c := by
        rw [hcb, mul_neg, neg_neg, Matrix.mul_assoc]
  have := eq_of_involutions_of_commute h2 (nonscalar_of_ne_one hc1) (g := c) (g' := a * b) rfl
    hcomm hc2 hab2 hc1 hab1
  rw [this, map_mul]


theorem isSolvable_perm_of_card_le_three {α : Type*} [Finite α] (h : Nat.card α ≤ 3) :
    Group.IsSolvable (Equiv.Perm α) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hcomm : IsMulCommutative (alternatingGroup α) :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mpr h
  have h1 : Group.IsSolvable (⊤ : Subgroup (Equiv.Perm α)) :=
    isSolvable_of_commutator_le_comm (⊤ : Subgroup (Equiv.Perm α)) (alternatingGroup α)
      (fun a ha b hb => congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      (fun a _ b _ => by
        rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _)
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup (Equiv.Perm α)) ≃* Equiv.Perm α).toMonoidHom)
    (MulEquiv.surjective _)

theorem isSolvable_of_conj_action {G : Type*} [Group G] (S : Subgroup G) (I : Set G) [Finite I]
    (hcard : Nat.card I ≤ 3) (hSI : ∀ s ∈ S, ∀ z ∈ I, s * z * s⁻¹ ∈ I) {z₀ : G} (hz₀ : z₀ ∈ I)
    (hsolv : Group.IsSolvable ↥(S ⊓ Subgroup.centralizer ({z₀} : Set G))) :
    Group.IsSolvable S := by
  let ρ : S →* Equiv.Perm I :=
    { toFun := fun s =>
        { toFun := fun z => ⟨s * z * s⁻¹, hSI s s.2 z z.2⟩
          invFun := fun z => ⟨(s : G)⁻¹ * z * s, by
            simpa using hSI ((s : G)⁻¹) (S.inv_mem s.2) z z.2⟩
          left_inv := fun z => Subtype.ext (by simp [mul_assoc])
          right_inv := fun z => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by ext z; simp
      map_mul' := fun s t => by ext z; simp [mul_assoc] }
  have hperm := isSolvable_perm_of_card_le_three (α := I) hcard
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (inf_le_left : S ⊓ Subgroup.centralizer ({z₀} : Set G) ≤ S)) ρ ?_
  intro s hs
  have hs1 : ρ s = 1 := hs
  have h1 := congrArg (fun e : Equiv.Perm I => (e ⟨z₀, hz₀⟩ : G)) hs1
  simp only [Equiv.Perm.coe_one, id_eq] at h1
  have h2 : (s : G) * z₀ * (s : G)⁻¹ = z₀ := h1
  have h3 : (s : G) ∈ Subgroup.centralizer ({z₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  exact ⟨⟨s, Subgroup.mem_inf.mpr ⟨s.2, h3⟩⟩, rfl⟩

theorem exists_finset_of_commuting_involutions (h2 : (2 : F) ≠ 0)
    (s : Set (ProjGenLinGroup (Fin 2) F)) (hs : ∀ z ∈ s, z ^ 2 = 1 ∧ z ≠ 1)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    ∃ t : Finset (ProjGenLinGroup (Fin 2) F), s ⊆ ↑t ∧ t.card ≤ 3 := by
  classical
  by_cases h : ∃ a ∈ s, ∃ b ∈ s, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    refine ⟨{a, b, a * b}, ?_, Finset.card_le_three⟩
    intro c hcs
    by_cases hca : c = a
    · simp [hca]
    by_cases hcb : c = b
    · simp [hcb]
    have : c = a * b := by
      obtain ⟨a', rfl⟩ := ProjGenLinGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := ProjGenLinGroup.mk_surjective b
      obtain ⟨c', rfl⟩ := ProjGenLinGroup.mk_surjective c
      exact eq_mul_of_commuting_involutions h2 (hs _ ha).1 (hs _ hb).1 (hs _ hcs).1
        (hs _ ha).2 (hs _ hb).2 (hs _ hcs).2 hab (Ne.symm hca) (Ne.symm hcb)
        (hc _ ha _ hb) (hc _ ha _ hcs) (hc _ hb _ hcs)
    simp [this]
  · push Not at h
    by_cases hne : s.Nonempty
    · obtain ⟨a, ha⟩ := hne
      refine ⟨{a}, ?_, by simp⟩
      intro c hcs
      have := h a ha c hcs
      simp [this]
    · refine ⟨∅, ?_, by simp⟩
      intro c hcs
      exact absurd ⟨c, hcs⟩ hne

theorem exists_central_involution {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    ∃ z ∈ Q, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ y ∈ Q, y * z = z * y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  haveI : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center Q) :=
    hQ.of_injective (Subgroup.center Q).subtype Subtype.val_injective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := Subgroup.center Q)
    rw [hn] at this
    simp at this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hxo : orderOf (((x : Q) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  refine ⟨((x : Q) : G), (x : Q).2, ?_, ?_, ?_⟩
  · rw [← hxo]; exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at hxo
    omega
  · intro y hy
    have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
    exact congrArg Subtype.val this

theorem isSolvable_of_normalizes_isPGroup_two [Finite F] (h2 : (2 : F) ≠ 0)
    {Q S : Subgroup (ProjGenLinGroup (Fin 2) F)} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hSN : ∀ s ∈ S, ∀ q : ProjGenLinGroup (Fin 2) F, q ∈ Q ↔ s * q * s⁻¹ ∈ Q) :
    Group.IsSolvable S := by
  classical
  have hfin : Finite (ProjGenLinGroup (Fin 2) F) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  obtain ⟨z₀, hz₀Q, hz₀2, hz₀1, hz₀c⟩ := exists_central_involution hQ hQ1
  set I : Set (ProjGenLinGroup (Fin 2) F) :=
    {z | z ∈ Q ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ y ∈ Q, y * z = z * y} with hI
  have hz₀I : z₀ ∈ I := ⟨hz₀Q, hz₀2, hz₀1, hz₀c⟩
  have hcomm : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x := fun x hx y hy => hy.2.2.2 x hx.1
  have hSI : ∀ s ∈ S, ∀ z ∈ I, s * z * s⁻¹ ∈ I := by
    intro s hs z hz
    refine ⟨(hSN s hs z).mp hz.1, ?_, ?_, ?_⟩
    · rw [conj_pow, hz.2.1, mul_one, mul_inv_cancel]
    · intro h
      exact hz.2.2.1 (conj_eq_one_iff.mp h)
    · intro y hy
      have hy' : s⁻¹ * y * s ∈ Q := by
        have := (hSN s⁻¹ (S.inv_mem hs) y).mp hy
        simpa using this
      have hcz := hz.2.2.2 _ hy'
      calc y * (s * z * s⁻¹) = s * ((s⁻¹ * y * s) * z) * s⁻¹ := by group
        _ = s * (z * (s⁻¹ * y * s)) * s⁻¹ := by rw [hcz]
        _ = (s * z * s⁻¹) * y := by group
  obtain ⟨t, hIt, htc⟩ :=
    exists_finset_of_commuting_involutions h2 I (fun z hz => ⟨hz.2.1, hz.2.2.1⟩) hcomm
  have hcard : Nat.card I ≤ 3 := by
    calc Nat.card I = I.ncard := Nat.card_coe_set_eq I
      _ ≤ (↑t : Set _).ncard := Set.ncard_le_ncard hIt t.finite_toSet
      _ = t.card := Set.ncard_coe_finset t
      _ ≤ 3 := htc
  haveI : Finite I := Set.toFinite I
  have hsolv : Group.IsSolvable ↥(S ⊓ Subgroup.centralizer ({z₀} : Set _)) := by
    refine isSolvable_of_le_centralizer_ne_one hz₀1 (fun s hs => ?_)
    have := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hs).2) z₀ rfl
    exact this.symm
  exact isSolvable_of_conj_action S I hcard hSI hz₀I hsolv

end CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut
