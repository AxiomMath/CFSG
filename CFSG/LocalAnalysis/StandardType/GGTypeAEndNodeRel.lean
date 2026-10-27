module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal CFSG.LieType.RootSystem SpecialLinear
open scoped commutatorElement

section Perm

variable {n : ℕ} {F : Type} [Field F]

theorem weylRep_conj_transvection_of_two (h2 : (2 : F) = 0) (k : Fin n) {i j : Fin (n + 1)}
    (hij : i ≠ j) (c : F) :
    weylRep n F k * Matrix.SpecialLinearGroup.transvection hij c * (weylRep n F k)⁻¹ =
      Matrix.SpecialLinearGroup.transvection
        ((Equiv.swap k.castSucc k.succ).injective.ne hij) c := by
  have key := conj_transvection_of_coe_eq_signedPerm (coe_weylRep_of_two n h2 k)
    (fun _ => by simp) hij c
  simpa using key

theorem weylRep_commute_transvection_of_two (h2 : (2 : F) = 0) (k : Fin n) {i j : Fin (n + 1)}
    (hij : i ≠ j) (hi : i ≠ k.castSucc) (hi' : i ≠ k.succ) (hj : j ≠ k.castSucc)
    (hj' : j ≠ k.succ) (c : F) :
    Commute (weylRep n F k) (Matrix.SpecialLinearGroup.transvection hij c) := by
  have key := weylRep_conj_transvection_of_two h2 k hij c
  rw [transvection_eq_of_eq _ hij (Equiv.swap_apply_of_ne_of_ne hi hi')
    (Equiv.swap_apply_of_ne_of_ne hj hj') c, mul_inv_eq_iff_eq_mul] at key
  exact key

end Perm

theorem commute_commutatorElement_of_commute {X : Type*} [Group X] {t u v : X} (hu : Commute t u)
    (hv : Commute t v) : Commute t ⁅u, v⁆ := by
  rw [commutatorElement_def]
  exact ((hu.mul_right hv).mul_right hu.inv_right).mul_right hv.inv_right

theorem commute_mul_mul_inv_of_commute {X : Type*} [Group X] {t s u : X} (hs : Commute t s)
    (hu : Commute t u) :
    Commute t (s * u * s⁻¹) :=
  (hs.mul_right hu).mul_right hs.inv_right

section Compat

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]
  {φ₁ φ₂ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X}

theorem slCompat_transvection (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    {a b a' b' : Fin (n + 1)} (hab : a ≠ b) (hab' : a' ≠ b') {i j : Fin n} (hij : i ≠ j)
    (ha : a = i.succ) (hb : b = j.succ) (ha' : a' = i.castSucc) (hb' : b' = j.castSucc) (c : F) :
    φ₁ (Matrix.SpecialLinearGroup.transvection hab c) =
      φ₂ (Matrix.SpecialLinearGroup.transvection hab' c) := by
  subst ha hb ha' hb'
  have h := DFunLike.congr_fun hc (Matrix.SpecialLinearGroup.transvection hij c)
  simp only [MonoidHom.comp_apply, slLowerBlockHom_transvection, slUpperBlockHom_transvection]
    at h
  exact h

theorem slCompat_weylRep (hn : 2 ≤ n)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F)) :
    φ₁ (weylRep n F ⟨n - 1, by omega⟩) = φ₂ (weylRep n F ⟨n - 2, by omega⟩) := by
  have hij : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
    rw [Ne, Fin.mk.injEq]
    omega
  have e1 : ∀ c : F, φ₁ (Matrix.SpecialLinearGroup.transvection
        (show (⟨n - 1, by omega⟩ : Fin n).castSucc < (⟨n - 1, by omega⟩ : Fin n).succ from
          Fin.castSucc_lt_succ).ne c) =
      φ₂ (Matrix.SpecialLinearGroup.transvection
        (show (⟨n - 2, by omega⟩ : Fin n).castSucc < (⟨n - 2, by omega⟩ : Fin n).succ from
          Fin.castSucc_lt_succ).ne c) := fun c =>
    slCompat_transvection hc _ _ hij (Fin.ext (by simp; omega)) (Fin.ext (by simp))
      (Fin.ext (by simp)) (Fin.ext (by simp; omega)) c
  have e2 : ∀ c : F, φ₁ (Matrix.SpecialLinearGroup.transvection
        (show (⟨n - 1, by omega⟩ : Fin n).castSucc < (⟨n - 1, by omega⟩ : Fin n).succ from
          Fin.castSucc_lt_succ).ne' c) =
      φ₂ (Matrix.SpecialLinearGroup.transvection
        (show (⟨n - 2, by omega⟩ : Fin n).castSucc < (⟨n - 2, by omega⟩ : Fin n).succ from
          Fin.castSucc_lt_succ).ne' c) := fun c =>
    slCompat_transvection hc _ _ (Ne.symm hij) (Fin.ext (by simp)) (Fin.ext (by simp; omega))
      (Fin.ext (by simp; omega)) (Fin.ext (by simp)) c
  simp only [weylRep, map_mul]
  rw [e1, e2]

variable (h2 : (2 : F) = 0)
include h2

theorem slCompat_commute_inner (hn : 1 ≤ n)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    {a b : Fin (n + 1)} (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : a.val < n)
    (hb : b.val < n) (c : F) :
    Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩))
      (φ₁ (Matrix.SpecialLinearGroup.transvection hab c)) := by
  obtain ⟨a', rfl⟩ := Fin.exists_succ_eq.mpr ha0
  obtain ⟨b', rfl⟩ := Fin.exists_succ_eq.mpr hb0
  have hab' : a' ≠ b' := fun e => hab (by rw [e])
  have hab'' : a'.castSucc ≠ b'.castSucc := (Fin.castSucc_injective _).ne hab'
  rw [slCompat_transvection hc hab hab'' hab' rfl rfl rfl rfl c]
  have ha' : a'.val + 1 < n := by simpa using ha
  have hb' : b'.val + 1 < n := by simpa using hb
  refine (weylRep_commute_transvection_of_two h2 _ hab'' ?_ ?_ ?_ ?_ c).map φ₂
  all_goals
    intro e
    have := congrArg Fin.val e
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega

theorem slCompat_commute (hn : 3 ≤ n)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hfar : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩)) (φ₁ (weylRep n F ⟨0, by omega⟩)))
    {a b : Fin (n + 1)} (hab : a ≠ b) (ha : a.val < n) (hb : b.val < n) (c : F) :
    Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩))
      (φ₁ (Matrix.SpecialLinearGroup.transvection hab c)) := by
  set T := φ₂ (weylRep n F ⟨n - 1, by omega⟩) with hT
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let i2 : Fin (n + 1) := ⟨2, by omega⟩
  let k0 : Fin n := ⟨0, by omega⟩
  have hk0c : k0.castSucc = 0 := Fin.ext rfl
  have hk0s : k0.succ = i1 := Fin.ext rfl
  have hi10 : i1 ≠ 0 := by simp [i1, Fin.ext_iff]
  have hi20 : i2 ≠ 0 := by simp [i2, Fin.ext_iff]
  have hi21 : i2 ≠ i1 := by simp [i1, i2, Fin.ext_iff]
  have hin : ∀ {a b : Fin (n + 1)} (hab : a ≠ b), a ≠ 0 → b ≠ 0 → a.val < n → b.val < n →
      ∀ c : F, Commute T (φ₁ (Matrix.SpecialLinearGroup.transvection hab c)) :=
    fun hab ha0 hb0 ha hb c => slCompat_commute_inner h2 (by omega) hc hab ha0 hb0 ha hb c
  have hconj : ∀ {a b : Fin (n + 1)} (hab : a ≠ b) (c : F),
      φ₁ (Matrix.SpecialLinearGroup.transvection
        ((Equiv.swap k0.castSucc k0.succ).injective.ne hab) c) =
      φ₁ (weylRep n F k0) * φ₁ (Matrix.SpecialLinearGroup.transvection hab c) *
        (φ₁ (weylRep n F k0))⁻¹ := by
    intro a b hab c
    rw [← map_inv, ← map_mul, ← map_mul, weylRep_conj_transvection_of_two h2]
  have hT0 : Commute T (φ₁ (weylRep n F k0)) := hfar
  have hrow : ∀ (b : Fin (n + 1)) (h : (0 : Fin (n + 1)) ≠ b), 2 ≤ b.val → b.val < n →
      ∀ c : F, Commute T (φ₁ (Matrix.SpecialLinearGroup.transvection h c)) := by
    intro b h hb2 hb c
    have h1b : i1 ≠ b := fun e => by rw [← e] at hb2; simp [i1] at hb2
    have hb0 : b ≠ 0 := Ne.symm h
    have e := hconj h1b c
    rw [transvection_eq_of_eq _ h (by rw [hk0c, hk0s, Equiv.swap_apply_right])
      (Equiv.swap_apply_of_ne_of_ne (by rw [hk0c]; exact hb0) (by rw [hk0s]; exact Ne.symm h1b))
      c] at e
    rw [e]
    exact commute_mul_mul_inv_of_commute hT0 (hin h1b hi10 hb0 (by simp [i1]; omega) hb c)
  have hcol : ∀ (a : Fin (n + 1)) (h : a ≠ 0), 2 ≤ a.val → a.val < n →
      ∀ c : F, Commute T (φ₁ (Matrix.SpecialLinearGroup.transvection h c)) := by
    intro a h ha2 ha c
    have ha1 : a ≠ i1 := fun e => by rw [e] at ha2; simp [i1] at ha2
    have e := hconj ha1 c
    rw [transvection_eq_of_eq _ h
      (Equiv.swap_apply_of_ne_of_ne (by rw [hk0c]; exact h) (by rw [hk0s]; exact ha1))
      (by rw [hk0c, hk0s, Equiv.swap_apply_right]) c] at e
    rw [e]
    exact commute_mul_mul_inv_of_commute hT0 (hin ha1 h hi10 ha (by simp [i1]; omega) c)
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := fun e => hab (ha0.trans e.symm)
    have h0b : (0 : Fin (n + 1)) ≠ b := fun e => hb0 e.symm
    rw [transvection_eq_of_eq hab h0b ha0 rfl c]
    by_cases hb1 : b = i1
    · have h01 : (0 : Fin (n + 1)) ≠ i1 := Ne.symm hi10
      rw [transvection_eq_of_eq h0b h01 rfl hb1 c]
      have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
        (Ne.symm hi20) hi21 h01 c (1 : F)
      rw [mul_one] at e
      rw [← e, map_commutatorElement]
      exact commute_commutatorElement_of_commute
        (hrow i2 (Ne.symm hi20) (by simp [i2]) (by simp [i2]; omega) c)
        (hin hi21 hi20 hi10 (by simp [i2]; omega) (by simp [i1]; omega) 1)
    · have hb2 : 2 ≤ b.val := by
        have h0 : b.val ≠ 0 := fun e => hb0 (Fin.ext e)
        have h1 : b.val ≠ 1 := fun e => hb1 (Fin.ext e)
        omega
      exact hrow b h0b hb2 hb c
  · by_cases hb0 : b = 0
    · have ha0' : a ≠ 0 := ha0
      rw [transvection_eq_of_eq hab ha0' rfl hb0 c]
      by_cases ha1 : a = i1
      · rw [transvection_eq_of_eq ha0' hi10 ha1 rfl c]
        have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
          (Ne.symm hi21) hi20 hi10 c (1 : F)
        rw [mul_one] at e
        rw [← e, map_commutatorElement]
        exact commute_commutatorElement_of_commute
          (hin (Ne.symm hi21) hi10 hi20 (by simp [i1]; omega) (by simp [i2]; omega) c)
          (hcol i2 hi20 (by simp [i2]) (by simp [i2]; omega) 1)
      · have ha2 : 2 ≤ a.val := by
          have h0 : a.val ≠ 0 := fun e => ha0 (Fin.ext e)
          have h1 : a.val ≠ 1 := fun e => ha1 (Fin.ext e)
          omega
        exact hcol a ha0' ha2 ha c
    · exact hin hab ha0 hb0 ha hb c

theorem ggTypeAEndNode_of_compat (hn : 3 ≤ n)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F))
    (hfar : Commute (φ₂ (weylRep n F ⟨n - 1, by omega⟩)) (φ₁ (weylRep n F ⟨0, by omega⟩))) :
    GGTypeAEndNode φ₁ (φ₂ (weylRep n F ⟨n - 1, by omega⟩)) := by
  refine ⟨?_, ?_, fun a b hab ha hb c => (slCompat_commute h2 hn hc hfar hab ha hb c).eq⟩
  · rw [← map_mul, weylRep_mul_self n h2, map_one]
  · rintro ⟨j, hjn⟩ hj
    simp only at hj
    obtain rfl : j = n - 1 := by omega
    rw [slCompat_weylRep (by omega) hc, ← map_mul, ← map_pow]
    have hW : (coxeterMatrix (isFiniteType_A n)).IsLiftable (weylRep n F) :=
      isLiftable_of_braid _ (weylRep_mul_self n h2) (isCTGroupDatum n F).braid
    have hne : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := by
      rw [Ne, Fin.mk.injEq]
      omega
    have h3 := hW ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩
    rw [coxeterMatrix_A_adj hne (Or.inr (by simp only; omega))] at h3
    rw [h3, map_one]

theorem slCompat_range_le (hn : 2 ≤ n)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F)) :
    φ₂.range ≤ φ₁.range ⊔
      φ₁.range.map (MulAut.conj (φ₂ (weylRep n F ⟨n - 1, by omega⟩))).toMonoidHom := by
  set T := φ₂ (weylRep n F ⟨n - 1, by omega⟩) with hT
  set M := φ₁.range ⊔ φ₁.range.map (MulAut.conj T).toMonoidHom with hM
  let k1 : Fin n := ⟨n - 1, by omega⟩
  let j1 : Fin (n + 1) := ⟨n - 1, by omega⟩
  have hk1c : k1.castSucc = j1 := Fin.ext rfl
  have hk1s : k1.succ = Fin.last n := Fin.ext (by simp [k1]; omega)
  have hj1l : j1 ≠ Fin.last n := by simp [j1, Fin.ext_iff]; omega
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by simp [Fin.ext_iff]; omega
  have h0j1 : (0 : Fin (n + 1)) ≠ j1 := by simp [j1, Fin.ext_iff]; omega
  have hL : ∀ {a b : Fin (n + 1)} (hab : a ≠ b), a.val < n → b.val < n → ∀ c : F,
      φ₂ (Matrix.SpecialLinearGroup.transvection hab c) ∈ φ₁.range := by
    intro a b hab ha hb c
    obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr
      (show a ≠ Fin.last n from Fin.ne_of_val_ne (by simp; omega))
    obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr
      (show b ≠ Fin.last n from Fin.ne_of_val_ne (by simp; omega))
    have hab' : a' ≠ b' := fun e => hab (by rw [e])
    rw [← slCompat_transvection hc ((Fin.succ_injective _).ne hab') hab hab' rfl rfl rfl rfl c]
    exact ⟨_, rfl⟩
  have hcomm : ∀ {u v : X}, u ∈ M → v ∈ M → ⁅u, v⁆ ∈ M := fun hu hv => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hu hv) (M.inv_mem hu)) (M.inv_mem hv)
  have hLM : ∀ {g : X}, g ∈ φ₁.range → g ∈ M := fun hg => Subgroup.mem_sup_left hg
  have hTM : ∀ {g : X}, g ∈ φ₁.range → T * g * T⁻¹ ∈ M := fun {g} hg =>
    Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨g, hg, by simp [MulAut.conj_apply]⟩)
  have hconjT : ∀ {a b : Fin (n + 1)} (hab : a ≠ b) (c : F),
      φ₂ (Matrix.SpecialLinearGroup.transvection
        ((Equiv.swap k1.castSucc k1.succ).injective.ne hab) c) =
      T * φ₂ (Matrix.SpecialLinearGroup.transvection hab c) * T⁻¹ := by
    intro a b hab c
    rw [hT, ← map_inv, ← map_mul, ← map_mul, weylRep_conj_transvection_of_two h2]
  have hrow : ∀ (b : Fin (n + 1)) (h : Fin.last n ≠ b), b.val < n - 1 → ∀ c : F,
      φ₂ (Matrix.SpecialLinearGroup.transvection h c) ∈ M := by
    intro b h hb c
    have hjb : j1 ≠ b := fun e => by rw [← e] at hb; simp [j1] at hb
    have e := hconjT hjb c
    rw [transvection_eq_of_eq _ h (by rw [hk1c, hk1s, Equiv.swap_apply_left])
      (Equiv.swap_apply_of_ne_of_ne (by rw [hk1c]; exact Ne.symm hjb)
        (by rw [hk1s]; exact Ne.symm h)) c] at e
    rw [e]
    exact hTM (hL hjb (by simp [j1]; omega) (by omega) c)
  have hcol : ∀ (a : Fin (n + 1)) (h : a ≠ Fin.last n), a.val < n - 1 → ∀ c : F,
      φ₂ (Matrix.SpecialLinearGroup.transvection h c) ∈ M := by
    intro a h ha c
    have haj : a ≠ j1 := fun e => by rw [e] at ha; simp [j1] at ha
    have e := hconjT haj c
    rw [transvection_eq_of_eq _ h
      (Equiv.swap_apply_of_ne_of_ne (by rw [hk1c]; exact haj) (by rw [hk1s]; exact h))
      (by rw [hk1c, hk1s, Equiv.swap_apply_left]) c] at e
    rw [e]
    exact hTM (hL haj (by omega) (by simp [j1]; omega) c)
  have htrans : ∀ {i j : Fin (n + 1)} (hij : i ≠ j) (c : F),
      φ₂ (Matrix.SpecialLinearGroup.transvection hij c) ∈ M := by
    intro i j hij c
    by_cases hi : i = Fin.last n
    · have hjl : j ≠ Fin.last n := fun e => hij (hi.trans e.symm)
      rw [transvection_eq_of_eq hij (fun e => hjl e.symm : Fin.last n ≠ j) hi rfl c]
      by_cases hj : j = j1
      · rw [transvection_eq_of_eq _ (Ne.symm hj1l) rfl hj c]
        have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
          (Ne.symm h0l) h0j1 (Ne.symm hj1l) c (1 : F)
        rw [mul_one] at e
        rw [← e, map_commutatorElement]
        exact hcomm (hrow 0 (Ne.symm h0l) (by simp; omega) c)
          (hLM (hL h0j1 (by simp; omega) (by simp [j1]; omega) 1))
      · have hjv : j.val < n - 1 := by
          have h1 : j.val ≠ n - 1 := fun e => hj (Fin.ext e)
          have h2' : j.val ≠ n := fun e => hjl (Fin.ext (by simp [e]))
          have := j.isLt
          omega
        exact hrow j _ hjv c
    · by_cases hj : j = Fin.last n
      · rw [transvection_eq_of_eq hij hi rfl hj c]
        by_cases hi' : i = j1
        · rw [transvection_eq_of_eq _ hj1l hi' rfl c]
          have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
            (Ne.symm h0j1) h0l hj1l c (1 : F)
          rw [mul_one] at e
          rw [← e, map_commutatorElement]
          exact hcomm (hLM (hL (Ne.symm h0j1) (by simp [j1]; omega)
            (by simp; omega) c)) (hcol 0 h0l (by simp; omega) 1)
        · have hiv : i.val < n - 1 := by
            have h1 : i.val ≠ n - 1 := fun e => hi' (Fin.ext e)
            have h2' : i.val ≠ n := fun e => hi (Fin.ext (by simp [e]))
            have := i.isLt
            omega
          exact hcol i _ hiv c
      · have hiv : i.val < n := by
          have h2' : i.val ≠ n := fun e => hi (Fin.ext (by simp [e]))
          have := i.isLt
          omega
        have hjv : j.val < n := by
          have h2' : j.val ≠ n := fun e => hj (Fin.ext (by simp [e]))
          have := j.isLt
          omega
        exact hLM (hL hij hiv hjv c)
  have htop : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F)) ≤ M.comap φ₂ := by
    rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact htrans hij c
  rintro _ ⟨g, rfl⟩
  exact htop (Subgroup.mem_top g)

end Compat

end CFSG.StandardType
