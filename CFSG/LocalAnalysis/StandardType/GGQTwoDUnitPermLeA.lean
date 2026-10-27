module

import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat

public section

namespace CFSG.StandardType.QTwo

@[expose] noncomputable def qtwoDB33_supp (m : ℕ) (T : DVec m ≃ₗ[ZMod 3] DVec m) : Finset (Fin m) :=
  Finset.univ.filter fun k => T (dBasis m k) ≠ dBasis m k

lemma qtwoDB33_supp_dTau (m : ℕ) (s : Bool) {a b : Fin m} (hab : a ≠ b) :
    qtwoDB33_supp m (dTau m s a b) = {a, b} := by
  ext k
  simp only [qtwoDB33_supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hk
    by_cases hka : k = a
    · exact Or.inl hka
    · by_cases hkb : k = b
      · exact Or.inr hkb
      · rw [dTau_apply_of_ne m s hka hkb] at hk
        exact absurd rfl hk
  · rintro (hka | hkb)
    · rw [hka, dTau_apply_left m s hab]
      intro h
      have hb := congrFun h a
      simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply,
        Pi.single_eq_of_ne hab, Pi.single_eq_same, mul_zero] at hb
      exact zero_ne_one hb
    · rw [hkb, dTau_apply_right m s hab]
      intro h
      have hb := congrFun h b
      simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply,
        Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, mul_zero] at hb
      exact zero_ne_one hb

lemma qtwoDB33_dPerm_dSign_comm (m : ℕ) {a b : Fin m} (hab : a ≠ b) :
    dPerm m (Equiv.swap a b) * dSign m a b = dSign m a b * dPerm m (Equiv.swap a b) := by
  refine (dBasis m).ext' fun k => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dSign_apply, map_smul, dPerm_apply,
    dSign_apply]
  have h : Equiv.swap a b k = a ∨ Equiv.swap a b k = b ↔ k = a ∨ k = b := by
    constructor
    · rintro (hk | hk)
      · exact Or.inr (by
          have hh := congrArg (Equiv.swap a b) hk
          simpa [Equiv.swap_apply_self] using hh)
      · exact Or.inl (by
          have hh := congrArg (Equiv.swap a b) hk
          simpa [Equiv.swap_apply_self] using hh)
    · rintro (hk | hk)
      · exact Or.inr (by rw [hk, Equiv.swap_apply_left])
      · exact Or.inl (by rw [hk, Equiv.swap_apply_right])
  by_cases hk : k = a ∨ k = b
  · rw [if_pos hk, if_pos (h.mpr hk)]
  · rw [if_neg hk, if_neg (fun hh => hk (h.mp hh))]

lemma qtwoDB33_commute_mul_pair {G : Type*} [Group G] {P D : G} (hPD : Commute P D)
    (s s' : Bool) : Commute (P * (if s then D else 1)) (P * (if s' then D else 1)) := by
  have hE : ∀ s : Bool, Commute P (if s then D else 1) := by
    intro s
    cases s
    · simpa using Commute.one_right P
    · simpa using hPD
  have hEE : ∀ s s' : Bool, Commute (if s then D else 1) (if s' then D else 1) := by
    intro s s'
    cases s <;> cases s'
    · simpa using Commute.one_left (1 : G)
    · simpa using Commute.one_left D
    · simpa using Commute.one_right D
    · simpa using Commute.refl D
  exact ((Commute.refl P).mul_left (hE s).symm).mul_right ((hE s').mul_left (hEE s s'))

lemma qtwoDB33_dTau_commute_same (m : ℕ) (s s' : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m s a b * dTau m s' a b = dTau m s' a b * dTau m s a b := by
  have h := qtwoDB33_commute_mul_pair (P := dPerm m (Equiv.swap a b))
    (D := dSign m a b) (qtwoDB33_dPerm_dSign_comm m hab) s s'
  simpa only [dTau] using h.eq

lemma qtwoDB33_pair_eq_cases {α : Type*} [DecidableEq α] {a b a' b' : α}
    (hab : a ≠ b) (h : ({a, b} : Finset α) = {a', b'}) :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  have hb : b ∈ ({a', b'} : Finset α) :=
    h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  rw [Finset.mem_insert, Finset.mem_singleton] at hb
  have ha : a ∈ ({a', b'} : Finset α) := h ▸ Finset.mem_insert_self a {b}
  rw [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact absurd (by rw [ha, hb]) hab
    · exact Or.inl ⟨ha, hb⟩
  · rcases hb with hb | hb
    · exact Or.inr ⟨ha, hb⟩
    · exact absurd (by rw [ha, hb]) hab

lemma qtwoDB33_dTau_commute_of_supp_eq {m : ℕ} (s s' : Bool) {a b a' b' : Fin m}
    (hab : a ≠ b) (hab' : a' ≠ b') (heq : ({a, b} : Finset (Fin m)) = {a', b'}) :
    dTau m s a b * dTau m s' a' b' = dTau m s' a' b' * dTau m s a b := by
  rcases qtwoDB33_pair_eq_cases hab heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact qtwoDB33_dTau_commute_same m s s' hab'
  · rw [h1, h2]
    rw [dTau_symm m s b' a']
    exact qtwoDB33_dTau_commute_same m s s' hab'

lemma qtwoDB33_cross_of_disjoint {m : ℕ} {a b a' b' : Fin m}
    (h : Disjoint ({a, b} : Finset (Fin m)) {a', b'}) :
    a ≠ a' ∧ a ≠ b' ∧ b ≠ a' ∧ b ≠ b' := by
  have ha : a ∉ ({a', b'} : Finset (Fin m)) :=
    Finset.disjoint_left.mp h (Finset.mem_insert_self a {b})
  have hb : b ∉ ({a', b'} : Finset (Fin m)) :=
    Finset.disjoint_left.mp h (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh; exact ha (by rw [hh]; exact Finset.mem_insert_self a' {b'})
  · intro hh; exact ha (by rw [hh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b'))
  · intro hh; exact hb (by rw [hh]; exact Finset.mem_insert_self a' {b'})
  · intro hh; exact hb (by rw [hh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b'))

lemma qtwoDB33_dTau_commute_disjoint {m : ℕ} (s s' : Bool) {a b a' b' : Fin m}
    (hab : a ≠ b) (hab' : a' ≠ b') (haa : a ≠ a') (hab2 : a ≠ b') (hba : b ≠ a')
    (hbb : b ≠ b') :
    dTau m s a b * dTau m s' a' b' = dTau m s' a' b' * dTau m s a b := by
  refine (dBasis m).ext' fun k => ?_
  by_cases hka : k = a
  · subst hka
    simp only [LinearEquiv.mul_apply, dTau_apply_left m s hab, map_smul,
      dTau_apply_of_ne m s' haa hab2, dTau_apply_of_ne m s' hba hbb]
  · by_cases hkb : k = b
    · subst hkb
      simp only [LinearEquiv.mul_apply, dTau_apply_right m s hab, map_smul,
        dTau_apply_of_ne m s' hba hbb, dTau_apply_of_ne m s' haa hab2]
    · by_cases hka' : k = a'
      · subst hka'
        simp only [LinearEquiv.mul_apply, dTau_apply_of_ne m s (Ne.symm haa) (Ne.symm hba),
          dTau_apply_left m s' hab', map_smul,
          dTau_apply_of_ne m s (Ne.symm hab2) (Ne.symm hbb)]
      · by_cases hkb' : k = b'
        · subst hkb'
          simp only [LinearEquiv.mul_apply, dTau_apply_of_ne m s (Ne.symm hab2) (Ne.symm hbb),
            dTau_apply_right m s' hab', map_smul,
            dTau_apply_of_ne m s (Ne.symm haa) (Ne.symm hba)]
        · simp only [LinearEquiv.mul_apply, dTau_apply_of_ne m s hka hkb,
            dTau_apply_of_ne m s hka' hkb', dTau_apply_of_ne m s' hka hkb,
            dTau_apply_of_ne m s' hka' hkb']

lemma qtwoDB33_dSign_mul_self (m : ℕ) {a b : Fin m} (hab : a ≠ b) :
    dSign m a b * dSign m a b = 1 := by
  have hc : (fun k : Fin m => (if k = a ∨ k = b then (-1 : (ZMod 3)ˣ) else 1)) *
      (fun k : Fin m => (if k = a ∨ k = b then (-1 : (ZMod 3)ˣ) else 1)) = 1 := by
    funext k
    by_cases hk : k = a ∨ k = b <;> simp [Pi.mul_apply, hk]
  simp only [dSign, ZS.diagMap_mul, hc, ZS.diagMap_one]

lemma qtwoDB33_dTau_mul_self (m : ℕ) (s : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m s a b * dTau m s a b = 1 := by
  have hPP : dPerm m (Equiv.swap a b) * dPerm m (Equiv.swap a b) = 1 := by
    rw [← dPerm_mul, Equiv.swap_mul_self, dPerm_one]
  have hDD : dSign m a b * dSign m a b = 1 := qtwoDB33_dSign_mul_self m hab
  have hPD : dPerm m (Equiv.swap a b) * dSign m a b
      = dSign m a b * dPerm m (Equiv.swap a b) := qtwoDB33_dPerm_dSign_comm m hab
  cases s
  · simp only [dTau, Bool.false_eq_true, if_false, mul_one]
    exact hPP
  · simp only [dTau, if_true]
    calc dPerm m (Equiv.swap a b) * dSign m a b *
          (dPerm m (Equiv.swap a b) * dSign m a b)
        = dPerm m (Equiv.swap a b) * (dSign m a b *
            (dPerm m (Equiv.swap a b) * dSign m a b)) := by rw [mul_assoc]
      _ = dPerm m (Equiv.swap a b) * ((dSign m a b * dPerm m (Equiv.swap a b)) *
            dSign m a b) := by rw [mul_assoc]
      _ = dPerm m (Equiv.swap a b) * ((dPerm m (Equiv.swap a b) * dSign m a b) *
            dSign m a b) := by rw [hPD]
      _ = dPerm m (Equiv.swap a b) * (dPerm m (Equiv.swap a b) *
            (dSign m a b * dSign m a b)) := by rw [mul_assoc]
      _ = dPerm m (Equiv.swap a b) * (dPerm m (Equiv.swap a b) * 1) := by rw [hDD]
      _ = dPerm m (Equiv.swap a b) * dPerm m (Equiv.swap a b) := by rw [mul_one]
      _ = 1 := hPP

lemma qtwoDB33_bad_ne' {m : ℕ} {R B A : DVec m ≃ₗ[ZMod 3] DVec m}
    {s s' s'' : Bool} {u a d b : Fin m}
    (hua : u ≠ a) (hud : u ≠ d) (hub : u ≠ b) (had : a ≠ d)
    (hR : R = dTau m s u a) (hB : B = dTau m s' u d) (hA : A = dTau m s'' u b) :
    R * B * R⁻¹ ≠ A := by
  subst hR; subst hB; subst hA
  intro hrel
  have hAA : dTau m s u a * dTau m s u a = 1 := qtwoDB33_dTau_mul_self m s hua
  have hinv : (dTau m s u a)⁻¹ = dTau m s u a := inv_eq_of_mul_eq_one_right hAA
  rw [hinv] at hrel
  have hBA : dTau m s' u d (dTau m s u a (dBasis m u)) = dTau m s u a (dBasis m u) := by
    rw [dTau_apply_left m s hua, map_smul, dTau_apply_of_ne m s' (Ne.symm hua) had]
  have hL : (dTau m s u a * dTau m s' u d * dTau m s u a) (dBasis m u) = dBasis m u := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hBA, ← LinearEquiv.mul_apply, hAA]
    rw [LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
  have heval := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (dBasis m u)) hrel
  rw [hL, dTau_apply_left m s'' hub] at heval
  have hthis := congrFun heval u
  simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hub, mul_zero] at hthis
  exact one_ne_zero hthis

lemma qtwoDB33_swap_mul_ne {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    Equiv.swap i j * Equiv.swap i k ≠ Equiv.swap i k * Equiv.swap i j := by
  intro h
  have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => σ i) h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk),
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk] at h2
  exact hjk h2.symm

lemma qtwoDB33_swap_mul_ne' {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j)
    (hik : i ≠ k) :
    Equiv.swap i j * Equiv.swap k j ≠ Equiv.swap k j * Equiv.swap i j := by
  have h := qtwoDB33_swap_mul_ne (i := j) (j := i) (k := k) (Ne.symm hij)
    (Ne.symm hkj) hik
  rwa [Equiv.swap_comm j i, Equiv.swap_comm j k] at h

lemma qtwoDB33_map_swap_mul_ne {n m : ℕ}
    {φ : Equiv.Perm (Fin n) →* (DVec m ≃ₗ[ZMod 3] DVec m)} (hinj : Function.Injective φ)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    φ (Equiv.swap i j) * φ (Equiv.swap i k) ≠ φ (Equiv.swap i k) * φ (Equiv.swap i j) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  exact qtwoDB33_swap_mul_ne hij hik hjk (hinj h)

lemma qtwoDB33_map_swap_mul_ne' {n m : ℕ}
    {φ : Equiv.Perm (Fin n) →* (DVec m ≃ₗ[ZMod 3] DVec m)} (hinj : Function.Injective φ)
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k) :
    φ (Equiv.swap i j) * φ (Equiv.swap k j) ≠ φ (Equiv.swap k j) * φ (Equiv.swap i j) := by
  intro h
  rw [← map_mul, ← map_mul] at h
  exact qtwoDB33_swap_mul_ne' hij hkj hik (hinj h)

lemma qtwoDB33_triangle {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2)
    (hAC : (A ∩ C).card = 1) (hBC : (B ∩ C).card = 1)
    {x : α} (hx : A ∩ B = {x}) (hxC : x ∉ C) :
    C = (A.erase x) ∪ (B.erase x) := by
  have hxA : x ∈ A := by
    have h : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_inter.mp h).1
  have hxB : x ∈ B := by
    have h : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_inter.mp h).2
  have hAcard : (A.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxA, hA]
  have hBcard : (B.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxB, hB]
  have hAeq : A ∩ C = A.erase x := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      rw [Finset.mem_inter] at hy
      exact Finset.mem_erase.mpr ⟨fun hyx => hxC (hyx ▸ hy.2), hy.1⟩
    · rw [hAC, hAcard]
  have hBeq : B ∩ C = B.erase x := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      rw [Finset.mem_inter] at hy
      exact Finset.mem_erase.mpr ⟨fun hyx => hxC (hyx ▸ hy.2), hy.1⟩
    · rw [hBC, hBcard]
  have hAsub : A.erase x ⊆ C := by rw [← hAeq]; exact Finset.inter_subset_right
  have hBsub : B.erase x ⊆ C := by rw [← hBeq]; exact Finset.inter_subset_right
  have hsub : (A.erase x) ∪ (B.erase x) ⊆ C := Finset.union_subset hAsub hBsub
  have hdisj : Disjoint (A.erase x) (B.erase x) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rw [Finset.mem_inter, Finset.mem_erase, Finset.mem_erase] at hy
    obtain ⟨⟨hyx, hyA⟩, -, hyB⟩ := hy
    have hyAB : y ∈ ({x} : Finset α) := by
      rw [← hx]; exact Finset.mem_inter.mpr ⟨hyA, hyB⟩
    exact hyx (Finset.mem_singleton.mp hyAB)
  have hcard : ((A.erase x) ∪ (B.erase x)).card = 2 := by
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hC, hcard])).symm

lemma qtwoDB33_three_common {α : Type*} [DecidableEq α] {A B C D : Finset α}
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 2)
    (hAB : (A ∩ B).card = 1) (hAC : (A ∩ C).card = 1) (hBC : (B ∩ C).card = 1)
    (hAD : (A ∩ D).card = 1) (hBD : (B ∩ D).card = 1) (hCD : (C ∩ D).card = 1)
    {x : α} (hx : A ∩ B = {x}) : x ∈ C := by
  have hxA : x ∈ A := by
    have h : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_inter.mp h).1
  have hxB : x ∈ B := by
    have h : x ∈ A ∩ B := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_inter.mp h).2
  by_contra hxC
  have hCeq := qtwoDB33_triangle hA hB hC hAC hBC hx hxC
  by_cases hxD : x ∈ D
  · have hADx : A ∩ D = {x} := by
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hAD
      have hxAD : x ∈ A ∩ D := Finset.mem_inter.mpr ⟨hxA, hxD⟩
      rw [hy, Finset.mem_singleton] at hxAD
      rw [hy, hxAD]
    have hBDx : B ∩ D = {x} := by
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hBD
      have hxBD : x ∈ B ∩ D := Finset.mem_inter.mpr ⟨hxB, hxD⟩
      rw [hy, Finset.mem_singleton] at hxBD
      rw [hy, hxBD]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hxD, hD])
    have hDins : D = {x, w} := by rw [← Finset.insert_erase hxD, hw]
    have hwx : w ≠ x := by
      have hw' : w ∈ D.erase x := by rw [hw]; exact Finset.mem_singleton_self w
      exact (Finset.mem_erase.mp hw').1
    have hwA : w ∉ A := by
      intro hwA
      have hwAD : w ∈ ({x} : Finset α) := by
        rw [← hADx]
        refine Finset.mem_inter.mpr ⟨hwA, ?_⟩
        rw [hDins]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w)
      exact hwx (Finset.mem_singleton.mp hwAD)
    have hwB : w ∉ B := by
      intro hwB
      have hwBD : w ∈ ({x} : Finset α) := by
        rw [← hBDx]
        refine Finset.mem_inter.mpr ⟨hwB, ?_⟩
        rw [hDins]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w)
      exact hwx (Finset.mem_singleton.mp hwBD)
    have hwC : w ∉ C := by
      rw [hCeq]
      intro hw
      rw [Finset.mem_union] at hw
      rcases hw with hw | hw
      · exact hwA (Finset.mem_of_mem_erase hw)
      · exact hwB (Finset.mem_of_mem_erase hw)
    have hCDempty : C ∩ D = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter] at hy
      have hyD := hy.2
      rw [hDins, Finset.mem_insert, Finset.mem_singleton] at hyD
      rcases hyD with hyD | hyD
      · exact hxC (hyD ▸ hy.1)
      · exact hwC (hyD ▸ hy.1)
    rw [hCDempty] at hCD
    simpa using hCD
  · have hDeq := qtwoDB33_triangle hA hB hD hAD hBD hx hxD
    rw [hDeq, ← hCeq, Finset.inter_self, hC] at hCD
    omega

lemma qtwoDB33_four_index {n : ℕ} (hn : 5 ≤ n) (i : Fin n) :
    ∃ j : Fin 4 → Fin n, Function.Injective j ∧ ∀ t, i ≠ j t := by
  have hT : 4 ≤ (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hT
  let e := Finset.orderIsoOfFin T hTcard
  refine ⟨fun t => (e t : Fin n), ?_, ?_⟩
  · intro t t' htt
    exact EquivLike.injective e (Subtype.val_injective htt)
  · intro t
    exact Ne.symm (Finset.mem_erase.mp (hTsub (e t).2)).1

end CFSG.StandardType.QTwo

end
