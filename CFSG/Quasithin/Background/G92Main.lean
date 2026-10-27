module

public import CFSG.Quasithin.Background.G92Assemble
public import CFSG.Quasithin.Background.G92Orth
public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpA
public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpB
public import CFSG.Quasithin.Background.G8Dihedral
public import CFSG.Quasithin.Background.G92Group

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.G92

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.SzN31 CFSG.Open

section Numerics

theorem gFun_eq_two {p : ℕ} (h : gFun p = 2) : p = 3 := by
  unfold gFun at h
  split_ifs at h with h3 h5
  · exact h3
  · omega
  · omega

theorem gFun_ne_five {p : ℕ} (h3 : p ≠ 3) (h5 : p ≠ 5) : gFun p = 6 := by
  unfold gFun
  simp [h3, h5]

theorem sum_gFun_ge {m : ℕ} (p : Fin m → ℕ) (hg : ∀ i, 2 ≤ gFun (p i)) (i₀ : Fin m) :
    gFun (p i₀) + 2 * (m - 1) ≤ ∑ i, gFun (p i) := by
  classical
  rw [← Finset.add_sum_erase Finset.univ (fun i => gFun (p i)) (Finset.mem_univ i₀)]
  have h1 : ∑ i ∈ Finset.univ.erase i₀, 2 ≤ ∑ i ∈ Finset.univ.erase i₀, gFun (p i) :=
    Finset.sum_le_sum fun i _ => hg i
  have h2 : ∑ i ∈ Finset.univ.erase i₀, 2 = 2 * (m - 1) := by
    simp [Finset.sum_const, Finset.card_erase_of_mem, mul_comm]
  omega

theorem eq_two_of_sum_le {m : ℕ} (p : Fin m → ℕ) (hg : ∀ i, 2 ≤ gFun (p i)) (i₀ : Fin m)
    (hs : ∑ i, gFun (p i) ≤ gFun (p i₀) + 2 * (m - 1)) : ∀ i, i ≠ i₀ → gFun (p i) = 2 := by
  classical
  intro i hi
  by_contra hne
  have hlt : 2 < gFun (p i) := lt_of_le_of_ne (hg i) (Ne.symm hne)
  rw [← Finset.add_sum_erase Finset.univ (fun i => gFun (p i)) (Finset.mem_univ i₀)] at hs
  have h1 : ∑ j ∈ Finset.univ.erase i₀, 2 < ∑ j ∈ Finset.univ.erase i₀, gFun (p j) :=
    Finset.sum_lt_sum (fun j _ => hg j) ⟨i, Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩, hlt⟩
  have h2 : ∑ j ∈ Finset.univ.erase i₀, 2 = 2 * (m - 1) := by
    simp [Finset.sum_const, Finset.card_erase_of_mem, mul_comm]
  omega

end Numerics

section Frames

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem frame_of_family {m : ℕ} {Hs : Fin m → Subgroup (GLV V)} {p : Fin m → ℕ}
    (hD : IsDihedralFamily Hs p) {A : Subgroup (GLV V)} (hA : IsElemAbelian 2 A)
    (hAle : A ≤ ⨆ i, Hs i) (hcard : Nat.card A = 2 ^ m) :
    ∃ F : Frame V (Fin m), F.p = p ∧ (∀ j, Hs j = Subgroup.closure {F.x j, F.a j}) ∧
      (∀ i, F.x i ≠ 1) ∧ ∑ i, gFun (p i) ≤ Module.finrank (ZMod 2) V := by
  have hrot : ∀ i, ∃ x ∈ Hs i, orderOf x = p i := by
    intro i
    obtain ⟨e⟩ := hD.iso i
    haveI : NeZero (p i) := ⟨(hD.prime i).ne_zero⟩
    refine ⟨(e.symm (DihedralGroup.r 1) : GLV V), (e.symm (DihedralGroup.r 1)).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  choose x hxH hxo using hrot
  obtain ⟨F, hFx, hFp, hFa⟩ := exists_frame_of_dihedralFamily hD hA hAle hcard x hxH hxo
  have hx1 : ∀ i, F.x i ≠ 1 := by
    intro i h1
    have h2 := hxo i
    rw [← congrFun hFx i, h1, orderOf_one] at h2
    exact (hD.prime i).one_lt.ne h2
  refine ⟨F, hFp, fun j => ?_, hx1, ?_⟩
  · obtain ⟨e⟩ := hD.iso j
    have hxj : F.x j ∈ Hs j := by
      rw [congrFun hFx j]
      exact hxH j
    have hxoj : orderOf (F.x j) = p j := by
      rw [congrFun hFx j]
      exact hxo j
    have hF := F.asq j
    have hc := F.conj j
    exact dihedral_eq_closure (hD.prime j) (hD.odd j) e hxj (hFa j).2 hxoj hF hc
  · have hadm : Adm F ⊤ Finset.univ := adm_top F Finset.univ fun i _ => hx1 i
    have := dim_lemma F Finset.univ ⊤ hadm
    rw [finrank_top] at this
    simpa [hFp] using this

theorem isPGroup_two_of_elem {G : Type*} [Group G] {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩

theorem g81_of {X A : Subgroup (GLV V)} {m : ℕ} (hm : 0 < m) (hAelem : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ m) (hXn : Group.IsNilpotent ↥X) (hXodd : Odd (Nat.card ↥X))
    (hAN : A ≤ Subgroup.normalizer (X : Set (GLV V)))
    (hAf : A ⊓ Subgroup.centralizer (X : Set (GLV V)) = ⊥) : G81 X A A := by
  refine ⟨hAelem, le_rfl, isPGroup_two_of_elem hAelem, hAN, hXn, hXodd, ?_⟩
  rintro rfl
  have hA1 : A = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hmem : a ∈ A ⊓ Subgroup.centralizer (((⊥ : Subgroup (GLV V)) : Set (GLV V))) := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have : h = 1 := hh
      rw [this, one_mul, mul_one]
    rw [hAf] at hmem
    exact hmem
  rw [hA1, Subgroup.card_bot] at hAcard
  have := Nat.one_lt_two_pow (n := m) hm.ne'
  omega

theorem frame_g86 {X A : Subgroup (GLV V)} {m : ℕ} (hm : 0 < m) (hAelem : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ m) (hXn : Group.IsNilpotent ↥X) (hXodd : Odd (Nat.card ↥X))
    (hAN : A ≤ Subgroup.normalizer (X : Set (GLV V)))
    (hAf : A ⊓ Subgroup.centralizer (X : Set (GLV V)) = ⊥) :
    ∃ (Hs : Fin m → Subgroup (GLV V)) (F : Frame V (Fin m)), IsDihedralFamily Hs F.p ∧
      (∀ j, Hs j = Subgroup.closure {F.x j, F.a j}) ∧ (∀ i, F.x i ≠ 1) ∧
      A ≤ ⨆ i, Hs i ∧ (⨆ i, Hs i) ≤ X ⊔ A ∧
      ∑ i, gFun (F.p i) ≤ Module.finrank (ZMod 2) V := by
  have h81 := g81_of hm hAelem hAcard hXn hXodd hAN hAf
  obtain ⟨Hs, p, hD, hAle, hHle, -⟩ := g8_6 h81 hm hAcard hAf
  obtain ⟨F, hFp, hclos, hx1, hsum⟩ := frame_of_family hD hAelem hAle hAcard
  subst hFp
  exact ⟨Hs, F, hD, hclos, hx1, hAle, hHle, hsum⟩

theorem frame_g88 {X A : Subgroup (GLV V)} {m : ℕ} (hm : 0 < m) (hAelem : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ m) (hXn : Group.IsNilpotent ↥X) (hXodd : Odd (Nat.card ↥X))
    (hAN : A ≤ Subgroup.normalizer (X : Set (GLV V)))
    (hAf : A ⊓ Subgroup.centralizer (X : Set (GLV V)) = ⊥) {q : ℕ} (hq : q.Prime)
    (hnot : ¬ A ≤ Subgroup.centralizer (pCoreOf q X : Set (GLV V))) :
    ∃ (Hs : Fin m → Subgroup (GLV V)) (F : Frame V (Fin m)), IsDihedralFamily Hs F.p ∧
      (∀ j, Hs j = Subgroup.closure {F.x j, F.a j}) ∧ (∀ i, F.x i ≠ 1) ∧
      A ≤ ⨆ i, Hs i ∧ (⨆ i, Hs i) ≤ X ⊔ A ∧ F.p ⟨0, hm⟩ = q ∧
      ∑ i, gFun (F.p i) ≤ Module.finrank (ZMod 2) V := by
  have h81 := g81_of hm hAelem hAcard hXn hXodd hAN hAf
  obtain ⟨Hs, p, hD, hAle, hHle, hp0⟩ := g8_8 h81 hq hAcard hAf hnot
  obtain ⟨F, hFp, hclos, hx1, hsum⟩ := frame_of_family hD hAelem hAle hAcard
  subst hFp
  exact ⟨Hs, F, hD, hclos, hx1, hAle, hHle, hp0 ⟨0, hm⟩ rfl, hsum⟩

end Frames

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem orthHyp_G92 : OrthHyp (V := V) IsOrth4ModuleG92 :=
  fun x₁ a₁ x₂ a₂ K hK U hdim hx₁ hx₂ ha₁ ha₂ hax₁ hax₂ hxx hxa hax haa hU hfp₁ hfp₂ hfaith =>
    isOrth4ModuleG92_of_pairs x₁ a₁ x₂ a₂ K hK U hdim hx₁ hx₂ ha₁ ha₂ hax₁ hax₂ hxx hxa hax haa
      hU hfp₁ hfp₂ hfaith

theorem g92_main (A : Subgroup (GLV V)) (m : ℕ) (hAelem : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ m) (hbound : Module.finrank (ZMod 2) V ≤ 2 * (m + 1))
    (X : Subgroup (GLV V)) (hXn : Group.IsNilpotent ↥X) (hXodd : Odd (Nat.card ↥X))
    (hAN : A ≤ Subgroup.normalizer (X : Set (GLV V)))
    (hAf : A ⊓ Subgroup.centralizer (X : Set (GLV V)) = ⊥)
    (hd : ⁅piPrimeCoreG92 {3} X, A⁆ = ⊥ → Module.finrank (ZMod 2) V ≤ 2 * m) :
    ⁅piPrimeCoreG92 {3, 5} X, A⁆ = ⊥ ∧
    ∃ (r : ℕ) (Gs : Fin r → Subgroup (GLV V)),
      (⨆ i, Gs i) ≤ X ⊔ A ∧ A ≤ ⨆ i, Gs i ∧ iSupIndep Gs ∧
      (∀ i j, i ≠ j → ∀ x ∈ Gs i, ∀ y ∈ Gs j, x * y = y * x) ∧
      (iSupIndep (fun i => commSpace (Gs i) ⊤) ∧ (⨆ i, commSpace (Gs i) ⊤) = ⊤) ∧
      (⁅piPrimeCoreG92 {3} X, A⁆ ≠ ⊥ → ∃ h : 0 < r,
        Nonempty (↥(Gs ⟨0, h⟩) ≃* DihedralGroup 5) ∧
          Module.finrank (ZMod 2) ↥(commSpace (Gs ⟨0, h⟩) ⊤) = 4) ∧
      (∀ i : Fin r, (⁅piPrimeCoreG92 {3} X, A⁆ ≠ ⊥ → 1 ≤ i.val) →
        ((Nonempty (↥(Gs i) ≃* DihedralGroup 3) ∧
            Module.finrank (ZMod 2) ↥(commSpace (Gs i) ⊤) = 2) ∨
          IsOrth4ModuleG92 (Gs i) (commSpace (Gs i) ⊤))) ∧
      (⁅piPrimeCoreG92 {3} X, A⁆ = ⊥ → Module.finrank (ZMod 2) V = 2 * m) ∧
      (⁅piPrimeCoreG92 {3} X, A⁆ ≠ ⊥ → Module.finrank (ZMod 2) V = 2 * (m + 1)) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    have hA1 : A = ⊥ := Subgroup.card_eq_one.1 (by simpa using hAcard)
    have hcomm3 : ⁅piPrimeCoreG92 {3} X, A⁆ = ⊥ := by
      rw [hA1]
      exact Subgroup.commutator_bot_right _
    have hV : Module.finrank (ZMod 2) V = 0 := by
      have := hd hcomm3
      omega
    haveI : Subsingleton V := Module.finrank_zero_iff.1 hV
    refine ⟨by rw [hA1]; exact Subgroup.commutator_bot_right _, 0, fun i => i.elim0, ?_⟩
    refine ⟨by simp, by rw [hA1]; exact bot_le, iSupIndep_def.2 fun i => i.elim0,
      fun i => i.elim0, ⟨iSupIndep_def.2 fun i => i.elim0, ?_⟩, fun h => absurd hcomm3 h,
      fun i => i.elim0, fun _ => by omega, fun h => absurd hcomm3 h⟩
    simp only [iSup_of_empty]
    exact Submodule.eq_bot_of_subsingleton.trans Submodule.eq_bot_of_subsingleton.symm
  · by_cases hI : ⁅piPrimeCoreG92 {3} X, A⁆ = ⊥
    ·
      have hd2 := hd hI
      obtain ⟨Hs, F, hD, hclos, hx1, hAle, hHle, hsum⟩ :=
        frame_g86 hm hAelem hAcard hXn hXodd hAN hAf
      have hg : ∀ i, 2 ≤ gFun (F.p i) := fun i => gFun_ge_two (F.prime i) (F.odd i)
      have hs1 := sum_gFun_ge F.p hg ⟨0, hm⟩
      have hg0 := hg ⟨0, hm⟩
      have hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j) := by omega
      have hg2 : ∀ i, gFun (F.p i) = 2 := by
        intro i
        by_cases hi : i = ⟨0, hm⟩
        · rw [hi]
          omega
        · exact eq_two_of_sum_le F.p hg ⟨0, hm⟩ (by omega) i hi
      have hp3 : ∀ i, F.p i = 3 := fun i => gFun_eq_two (hg2 i)
      have hP : PrimeShape F ⟨0, hm⟩ := ⟨fun j _ => hp3 j, Or.inl (hp3 _)⟩
      obtain ⟨r, Gs, h1, h2, h3, h4, h5, -, hlast⟩ :=
        assemble IsOrth4ModuleG92 orthHyp_G92 F Hs hD hclos hx1 hdim ⟨0, hm⟩ hP X A hAle hHle
      refine ⟨?_, r, Gs, h1, h2, h3, h4, h5, fun h => absurd hI h,
        fun i _ => hlast i (Or.inl (hp3 _)), fun _ => by omega, fun h => absurd hI h⟩
      refine le_bot_iff.1 ?_
      rw [← hI]
      exact Subgroup.commutator_mono (piPrimeCoreG92_anti
        (Set.singleton_subset_iff.2 (by simp)) X) le_rfl
    ·
      have hq : ∃ q, q.Prime ∧ q ∉ ({3} : Set ℕ) ∧
          ¬ A ≤ Subgroup.centralizer (pCoreOf q X : Set (GLV V)) := by
        by_contra hcon
        push Not at hcon
        exact hI (commutator_piPrimeCoreG92_eq_bot X A hXn {3} hcon)
      have hq5 : ∀ q : ℕ, q.Prime → q ∉ ({3, 5} : Set ℕ) →
          A ≤ Subgroup.centralizer (pCoreOf q X : Set (GLV V)) := by
        intro q hqp hq35
        by_contra hnot
        obtain ⟨Hs, F, hD, hclos, hx1, hAle, hHle, hF0, hsum⟩ :=
          frame_g88 hm hAelem hAcard hXn hXodd hAN hAf hqp hnot
        have hq3 : q ≠ 3 := fun h => hq35 (by simp [h])
        have hq5' : q ≠ 5 := fun h => hq35 (by simp [h])
        have h6 : gFun (F.p ⟨0, hm⟩) = 6 := by
          rw [hF0]
          exact gFun_ne_five hq3 hq5'
        have hg : ∀ i, 2 ≤ gFun (F.p i) := fun i => gFun_ge_two (F.prime i) (F.odd i)
        have := sum_gFun_ge F.p hg ⟨0, hm⟩
        omega
      have h5X : ¬ A ≤ Subgroup.centralizer (pCoreOf 5 X : Set (GLV V)) := by
        obtain ⟨q, hqp, hq3, hqnot⟩ := hq
        by_cases h : q = 5
        · rw [h] at hqnot
          exact hqnot
        · refine absurd (hq5 q hqp ?_) hqnot
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun h3 => hq3 (by simpa using h3), h⟩
      obtain ⟨Hs, F, hD, hclos, hx1, hAle, hHle, hF0, hsum⟩ :=
        frame_g88 hm hAelem hAcard hXn hXodd hAN hAf Nat.prime_five h5X
      have hg : ∀ i, 2 ≤ gFun (F.p i) := fun i => gFun_ge_two (F.prime i) (F.odd i)
      have h5g : gFun (F.p ⟨0, hm⟩) = 4 := by
        rw [hF0]
        exact gFun_five
      have hs1 := sum_gFun_ge F.p hg ⟨0, hm⟩
      have hdim : Module.finrank (ZMod 2) V = ∑ j, gFun (F.p j) := by omega
      have hd2 : Module.finrank (ZMod 2) V = 2 * (m + 1) := by omega
      have hp3 : ∀ i, i ≠ ⟨0, hm⟩ → F.p i = 3 := fun i hi =>
        gFun_eq_two (eq_two_of_sum_le F.p hg ⟨0, hm⟩ (by omega) i hi)
      have hP : PrimeShape F ⟨0, hm⟩ := ⟨hp3, Or.inr hF0⟩
      obtain ⟨r, Gs, h1, h2, h3, h4, h5, hspec, hlast⟩ :=
        assemble IsOrth4ModuleG92 orthHyp_G92 F Hs hD hclos hx1 hdim ⟨0, hm⟩ hP X A hAle hHle
      exact ⟨commutator_piPrimeCoreG92_eq_bot X A hXn {3, 5} hq5, r, Gs, h1, h2, h3, h4, h5,
        fun _ => hspec hF0, fun i hi => hlast i (Or.inr (hi hI)), fun h => absurd h hI,
        fun _ => hd2⟩

end Main

end CFSG.Quasithin.G92
