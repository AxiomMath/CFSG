module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.SzVB

open scoped Pointwise symmDiff

namespace PermAux

theorem even_natCard_of_involution {α : Type*} [Finite α] (σ : α → α) (hσ : ∀ a, σ (σ a) = a)
    (hne : ∀ a, σ a ≠ a) : Even (Nat.card α) := by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, ← ZMod.natCast_eq_zero_iff_even]
  have h := Finset.sum_involution (s := (Finset.univ : Finset α)) (f := fun _ => (1 : ZMod 2))
    (fun a _ => σ a) (fun a _ => by show (1 : ZMod 2) + 1 = 0; decide) (fun a _ _ => hne a)
    (fun a _ => Finset.mem_univ _) (fun a _ => hσ a)
  simpa using h

section SymmDiff

variable {Ω : Type*} [DecidableEq Ω]

theorem card_symmDiff_add_two_mul_card_inter (I J : Finset Ω) :
    (I ∆ J).card + 2 * (I ∩ J).card = I.card + J.card := by
  have h1 := Finset.card_sdiff_add_card_inter I J
  have h2 := Finset.card_sdiff_add_card_inter J I
  rw [Finset.inter_comm J I] at h2
  have h3 : (I ∆ J).card = (I \ J).card + (J \ I).card := by
    rw [Finset.symmDiff_def]
    exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  omega

theorem even_card_symmDiff {I J : Finset Ω} (hI : Even I.card) (hJ : Even J.card) :
    Even (I ∆ J).card := by
  have h := card_symmDiff_add_two_mul_card_inter I J
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb⟩ := hJ
  exact ⟨a + b - (I ∩ J).card, by omega⟩

theorem even_card_symmDiff_of_card_eq {I J : Finset Ω} (h : I.card = J.card) :
    Even (I ∆ J).card := by
  have h1 := card_symmDiff_add_two_mul_card_inter I J
  exact ⟨I.card - (I ∩ J).card, by omega⟩

end SymmDiff

end PermAux

section Subsets

variable {X Ω : Type*} [Group X] [MulAction X Ω] [Fintype Ω] [DecidableEq Ω]

structure IsInvFamily (X : Type*) [Group X] [MulAction X Ω] (N : Set (Finset Ω)) : Prop where
  empty_mem : (∅ : Finset Ω) ∈ N
  symmDiff_mem : ∀ I ∈ N, ∀ J ∈ N, I ∆ J ∈ N
  smul_mem : ∀ (g : X) (I : Finset Ω), I ∈ N → g • I ∈ N

namespace PermAux

theorem exists_smul_ne (htrans : MulAction.IsPretransitive X Ω) {I : Finset Ω} (hne : I ≠ ∅)
    (hu : I ≠ Finset.univ) : ∃ g : X, g • I ≠ I := by
  by_contra h
  have h' : ∀ g : X, g • I = I := fun g => by_contra fun hg => h ⟨g, hg⟩
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  refine hu (Finset.eq_univ_iff_forall.mpr fun b => ?_)
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq a b
  have h1 : g • a ∈ g • I := Finset.smul_mem_smul_finset ha
  rw [h' g, hg] at h1
  exact h1

theorem exists_fixed_even {N : Set (Finset Ω)} (hN : IsInvFamily X N) (R : Subgroup X)
    (hR : IsPGroup 2 R) {J : Finset Ω} (hJ : J ∈ N) (hJe : Even J.card) (hJne : J ≠ ∅) :
    ∃ K ∈ N, Even K.card ∧ K ≠ ∅ ∧ ∀ r ∈ R, r • K = K := by
  obtain ⟨S, hS⟩ : ∃ S : SubMulAction R (Finset Ω), ∀ K, K ∈ S ↔ K ∈ N ∧ Even K.card :=
    ⟨{ carrier := {K | K ∈ N ∧ Even K.card}
       smul_mem' := fun c {K} hK =>
         ⟨hN.smul_mem (c : X) K hK.1, by
           change Even ((c : X) • K).card
           rw [Finset.card_smul_finset]
           exact hK.2⟩ },
      fun K => Iff.rfl⟩
  let σ : S → S := fun K =>
    ⟨K.1 ∆ J, (hS _).2 ⟨hN.symmDiff_mem _ ((hS _).1 K.2).1 _ hJ,
      even_card_symmDiff ((hS _).1 K.2).2 hJe⟩⟩
  have hσ : ∀ K, σ (σ K) = K := fun K => Subtype.ext (symmDiff_symmDiff_cancel_right _ _)
  have hne : ∀ K, σ K ≠ K := by
    intro K h
    have h2 : K.1 ∆ J = K.1 := congrArg Subtype.val h
    exact hJne (by simpa using symmDiff_eq_left.mp h2)
  have heven : 2 ∣ Nat.card S := even_iff_two_dvd.mp (even_natCard_of_involution σ hσ hne)
  have h0 : (⟨∅, (hS _).2 ⟨hN.empty_mem, by simp⟩⟩ : S) ∈ MulAction.fixedPoints R S := by
    rw [MulAction.mem_fixedPoints]
    intro r
    exact Subtype.ext (Finset.smul_finset_empty _)
  obtain ⟨b, hb, hab⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point S heven h0
  obtain ⟨hbN, hbe⟩ := (hS _).1 b.2
  refine ⟨b.1, hbN, hbe, ?_, ?_⟩
  · intro h
    exact hab (Subtype.ext h.symm)
  · intro r hr
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨r, hr⟩)

theorem eq_erase_of_fixed {R : Subgroup X} {o : Ω}
    (hRtrans : ∀ a b : Ω, a ≠ o → b ≠ o → ∃ r ∈ R, r • a = b)
    (hodd : Odd (Fintype.card Ω)) {K : Finset Ω} (hKe : Even K.card) (hKne : K ≠ ∅)
    (hKfix : ∀ r ∈ R, r • K = K) : K = Finset.univ.erase o := by
  have hclose : ∀ a ∈ K, a ≠ o → ∀ b, b ≠ o → b ∈ K := by
    intro a ha hao b hbo
    obtain ⟨r, hr, hra⟩ := hRtrans a b hao hbo
    have h1 : r • a ∈ r • K := Finset.smul_mem_smul_finset ha
    rw [hKfix r hr, hra] at h1
    exact h1
  have hoK : o ∉ K := by
    intro hoK
    by_cases h : ∃ a ∈ K, a ≠ o
    · obtain ⟨a, ha, hao⟩ := h
      have hKu : K = Finset.univ := by
        refine Finset.eq_univ_iff_forall.mpr fun b => ?_
        by_cases hb : b = o
        · rw [hb]
          exact hoK
        · exact hclose a ha hao b hb
      rw [hKu, Finset.card_univ] at hKe
      exact (Nat.not_even_iff_odd.mpr hodd) hKe
    · have h' : ∀ a ∈ K, a = o := fun a ha => by_contra fun hao => h ⟨a, ha, hao⟩
      have hKo : K = {o} := by
        ext b
        rw [Finset.mem_singleton]
        exact ⟨fun hb => h' b hb, fun hb => by rw [hb]; exact hoK⟩
      rw [hKo, Finset.card_singleton] at hKe
      exact Nat.not_even_one hKe
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hKne
  have hao : a ≠ o := fun h => hoK (by rw [← h]; exact ha)
  ext b
  rw [Finset.mem_erase]
  exact ⟨fun hb => ⟨fun h => hoK (by rw [← h]; exact hb), Finset.mem_univ b⟩,
    fun hb => hclose a ha hao b hb.1⟩

theorem smul_erase (g : X) (o : Ω) :
    g • (Finset.univ.erase o) = Finset.univ.erase (g • o) := by
  ext y
  rw [Finset.mem_smul_finset, Finset.mem_erase]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun h => (Finset.mem_erase.mp hw).1 (MulAction.injective g h), Finset.mem_univ _⟩
  · rintro ⟨hy, -⟩
    refine ⟨g⁻¹ • y, Finset.mem_erase.mpr ⟨fun h => hy ?_, Finset.mem_univ _⟩,
      smul_inv_smul g y⟩
    rw [← h, smul_inv_smul]

theorem pair_eq_symmDiff_erase {a b : Ω} (hab : a ≠ b) :
    ({a, b} : Finset Ω) = (Finset.univ.erase a) ∆ (Finset.univ.erase b) := by
  ext c
  rw [Finset.mem_symmDiff]
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ,
    and_true]
  by_cases hca : c = a
  · subst hca
    simp [hab]
  · by_cases hcb : c = b
    · subst hcb
      simp [hca]
    · simp [hca, hcb]

end PermAux

theorem pair_mem_of_not_const {N : Set (Finset Ω)} (hN : IsInvFamily X N)
    (htrans : MulAction.IsPretransitive X Ω) (R : Subgroup X) (hR : IsPGroup 2 R) (o : Ω)
    (hRfix : ∀ r ∈ R, r • o = o)
    (hRtrans : ∀ a b : Ω, a ≠ o → b ≠ o → ∃ r ∈ R, r • a = b)
    (hodd : Odd (Fintype.card Ω)) {I : Finset Ω} (hI : I ∈ N) (hne : I ≠ ∅)
    (hu : I ≠ Finset.univ) :
    ∀ a b : Ω, a ≠ b → ({a, b} : Finset Ω) ∈ N := by
  have _ := hRfix
  obtain ⟨g, hg⟩ := PermAux.exists_smul_ne htrans hne hu
  have hJ : I ∆ (g • I) ∈ N := hN.symmDiff_mem I hI _ (hN.smul_mem g I hI)
  have hJne : I ∆ (g • I) ≠ ∅ := fun h => hg (Finset.symmDiff_eq_empty.mp h).symm
  have hJe : Even (I ∆ (g • I)).card :=
    PermAux.even_card_symmDiff_of_card_eq (Finset.card_smul_finset g I).symm
  obtain ⟨K, hKN, hKe, hKne, hKfix⟩ := PermAux.exists_fixed_even hN R hR hJ hJe hJne
  have hK : K = Finset.univ.erase o := PermAux.eq_erase_of_fixed hRtrans hodd hKe hKne hKfix
  subst hK
  have hE : ∀ x : Ω, Finset.univ.erase x ∈ N := by
    intro x
    obtain ⟨h, hh⟩ := htrans.exists_smul_eq o x
    have h1 := hN.smul_mem h _ hKN
    rwa [PermAux.smul_erase, hh] at h1
  intro a b hab
  rw [PermAux.pair_eq_symmDiff_erase hab]
  exact hN.symmDiff_mem _ (hE a) _ (hE b)

end Subsets

section TFamily

variable {X Ω A : Type*} [Group X] [MulAction X Ω] [Fintype Ω] [DecidableEq Ω] [CommGroup A]

structure TData (ρ : X →* MulAut A) (t : Ω → A) (z : A) : Prop where
  t_sq : ∀ a, t a * t a = 1
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  z_fix : ∀ g : X, ρ g z = z
  act : ∀ (g : X) (a : Ω), ρ g (t a) = t (g • a) ∨ ρ g (t a) = t (g • a) * z
  distinct : ∀ a b : Ω, a ≠ b → t a * t b ≠ 1 ∧ t a * t b ≠ z

@[expose] def KerProp (t : Ω → A) (z : A) : Prop :=
  ∀ I : Finset Ω, ((∏ a ∈ I, t a) = 1 ∨ (∏ a ∈ I, t a) = z) → I = ∅ ∨ I = Finset.univ

@[expose] def commMap (ρ : X →* MulAut A) (s : X) : A →* A :=
  (ρ s).toMonoidHom * (MonoidHom.id A)⁻¹

theorem commMap_apply (ρ : X →* MulAut A) (s : X) (a : A) : commMap ρ s a = ρ s a * a⁻¹ := by
  simp [commMap]

variable {ρ : X →* MulAut A} {t : Ω → A} {z : A}

namespace PermAux

omit [Fintype Ω] in
theorem prod_symmDiff_of_mul_self (ht : ∀ a, t a * t a = 1) (I J : Finset Ω) :
    ∏ a ∈ I ∆ J, t a = (∏ a ∈ I, t a) * ∏ a ∈ J, t a := by
  have h1 := Finset.prod_inter_mul_prod_sdiff I J t
  have h2 := Finset.prod_inter_mul_prod_sdiff J I t
  rw [Finset.inter_comm J I] at h2
  have h3 : ∏ a ∈ I ∆ J, t a = (∏ a ∈ I \ J, t a) * ∏ a ∈ J \ I, t a := by
    rw [Finset.symmDiff_def]
    exact Finset.prod_union disjoint_sdiff_sdiff
  have h4 : (∏ a ∈ I ∩ J, t a) * ∏ a ∈ I ∩ J, t a = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => ht a
  rw [h3, ← h1, ← h2]
  calc (∏ a ∈ I \ J, t a) * ∏ a ∈ J \ I, t a
      = ((∏ a ∈ I ∩ J, t a) * ∏ a ∈ I ∩ J, t a) * ((∏ a ∈ I \ J, t a) * ∏ a ∈ J \ I, t a) := by
        rw [h4, one_mul]
    _ = _ := by ac_rfl

theorem pair_mul_mem (hzz : z * z = 1) {a b : A} (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) :
    a * b = 1 ∨ a * b = z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, hzz]

omit [Fintype Ω] in
theorem exists_rho_prod (hT : TData ρ t z) (g : X) (I : Finset Ω) :
    ∃ ε : A, (ε = 1 ∨ ε = z) ∧ ρ g (∏ a ∈ I, t a) = (∏ a ∈ I, t (g • a)) * ε := by
  refine Finset.induction_on I ⟨1, Or.inl rfl, by simp⟩ ?_
  intro a s ha ih
  obtain ⟨ε, hε, h⟩ := ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, h]
  rcases hT.act g a with h1 | h1
  · exact ⟨ε, hε, by rw [h1]; ac_rfl⟩
  · exact ⟨z * ε, pair_mul_mem hT.z_sq (Or.inr rfl) hε, by rw [h1]; ac_rfl⟩

omit [Fintype Ω] in
theorem prod_smul_finset_eq (g : X) (I : Finset Ω) :
    ∏ b ∈ g • I, t b = ∏ a ∈ I, t (g • a) := by
  rw [Finset.smul_finset_def, Finset.prod_image]
  exact fun x _ y _ hxy => MulAction.injective g hxy

omit [Fintype Ω] in
theorem prod_smul_mem_pair (hT : TData ρ t z) (g : X) (I : Finset Ω)
    (hI : (∏ a ∈ I, t a) = 1 ∨ (∏ a ∈ I, t a) = z) :
    (∏ b ∈ g • I, t b) = 1 ∨ (∏ b ∈ g • I, t b) = z := by
  obtain ⟨ε, hε, h⟩ := exists_rho_prod hT g I
  have hεε : ε * ε = 1 := by
    rcases hε with hε | hε <;> rw [hε]
    · exact mul_one 1
    · exact hT.z_sq
  have hρ : ρ g (∏ a ∈ I, t a) = 1 ∨ ρ g (∏ a ∈ I, t a) = z := by
    rcases hI with hI | hI
    · exact Or.inl (by rw [hI, map_one])
    · exact Or.inr (by rw [hI, hT.z_fix g])
  have h2 : ∏ a ∈ I, t (g • a) = ρ g (∏ a ∈ I, t a) * ε := by
    rw [h, mul_assoc, hεε, mul_one]
  rw [prod_smul_finset_eq, h2]
  exact pair_mul_mem hT.z_sq hρ hε

omit [Fintype Ω] in
theorem isInvFamily_prod_mem (hT : TData ρ t z) :
    IsInvFamily X {I : Finset Ω | (∏ a ∈ I, t a) = 1 ∨ (∏ a ∈ I, t a) = z} where
  empty_mem := Or.inl (by simp)
  symmDiff_mem I hI J hJ := by
    show (∏ a ∈ I ∆ J, t a) = 1 ∨ (∏ a ∈ I ∆ J, t a) = z
    rw [prod_symmDiff_of_mul_self hT.t_sq]
    exact pair_mul_mem hT.z_sq hI hJ
  smul_mem g I hI := prod_smul_mem_pair hT g I hI

end PermAux

theorem kerProp_of_tData (hT : TData ρ t z) (htrans : MulAction.IsPretransitive X Ω)
    (R : Subgroup X) (hR : IsPGroup 2 R) (o : Ω) (hRfix : ∀ r ∈ R, r • o = o)
    (hRtrans : ∀ a b : Ω, a ≠ o → b ≠ o → ∃ r ∈ R, r • a = b)
    (hodd : Odd (Fintype.card Ω)) : KerProp t z := by
  intro I hI
  by_contra hcon
  have hne : I ≠ ∅ := fun h => hcon (Or.inl h)
  have hu : I ≠ Finset.univ := fun h => hcon (Or.inr h)
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨b, hb⟩ : ∃ b, b ∉ I := by
    by_contra h
    exact hu (Finset.eq_univ_iff_forall.mpr fun b => by_contra fun hb => h ⟨b, hb⟩)
  have hab : a ≠ b := fun h => hb (by rw [← h]; exact ha)
  have hpair : (∏ c ∈ ({a, b} : Finset Ω), t c) = 1 ∨ (∏ c ∈ ({a, b} : Finset Ω), t c) = z :=
    pair_mem_of_not_const (PermAux.isInvFamily_prod_mem hT) htrans R hR o hRfix hRtrans hodd
      hI hne hu a b hab
  rw [Finset.prod_pair hab] at hpair
  obtain ⟨h1, h2⟩ := hT.distinct a b hab
  rcases hpair with h | h
  · exact h1 h
  · exact h2 h

end TFamily

end CFSG.Quasithin.SzVB
