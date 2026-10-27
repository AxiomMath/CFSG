module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem entry_eq_zero_of_commute_diagonal {n : ℕ} {d : Fin n → K} {M : Matrix (Fin n) (Fin n) K}
    (h : M * diagonal d = diagonal d * M) {i j : Fin n} (hij : d i ≠ d j) : M i j = 0 := by
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  have : M i j * (d j - d i) = 0 := by rw [mul_sub, e, mul_comm, sub_self]
  exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hij))

section CommHom

variable {n : ℕ} (L : Subgroup (GL (Fin n) K)) (y : GL (Fin n) K)

@[expose] noncomputable def commHom : centMod L y →* StatedScalars (Fin n) K where
  toFun l := ⟨(l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹ * y⁻¹, by
    obtain ⟨-, z, hz, hzy⟩ := mem_centMod_iff_scalar.mp l.2
    rw [hzy, mul_inv_cancel_right]
    exact hz⟩
  map_one' := Subtype.ext (by simp)
  map_mul' l₁ l₂ := by
    obtain ⟨-, z₂, hz₂, hzy₂⟩ := mem_centMod_iff_scalar.mp l₂.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    set a := (l₁ : GL (Fin n) K)
    set b := (l₂ : GL (Fin n) K)
    have hc : b * y * b⁻¹ * y⁻¹ = z₂ := by rw [hzy₂, mul_inv_cancel_right]
    rw [hc]
    have hz := commute_of_mem_statedScalars hz₂
    calc a * b * y * (a * b)⁻¹ * y⁻¹ = a * (b * y * b⁻¹) * a⁻¹ * y⁻¹ := by group
      _ = a * (z₂ * y) * a⁻¹ * y⁻¹ := by rw [hzy₂]
      _ = (a * z₂) * y * a⁻¹ * y⁻¹ := by group
      _ = (z₂ * a) * y * a⁻¹ * y⁻¹ := by rw [hz a]
      _ = z₂ * (a * y * a⁻¹ * y⁻¹) := by group
      _ = (a * y * a⁻¹ * y⁻¹) * z₂ := (hz _).symm

theorem coe_commHom (l : centMod L y) :
    (commHom L y l : GL (Fin n) K) = (l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹ * y⁻¹ :=
  rfl

theorem centralizer_le_centMod :
    L ⊓ Subgroup.centralizer {y} ≤ centMod L y := by
  intro l hl
  obtain ⟨hl, hly⟩ := Subgroup.mem_inf.mp hl
  rw [Subgroup.mem_centralizer_singleton_iff] at hly
  refine mem_centMod_iff_scalar.mpr ⟨hl, 1, one_mem _, ?_⟩
  rw [one_mul, hly, mul_inv_cancel_right]

theorem ker_commHom :
    (commHom L y).ker = (L ⊓ Subgroup.centralizer {y}).subgroupOf (centMod L y) := by
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [coe_commHom, OneMemClass.coe_one] at h'
    refine ⟨(mem_centMod_iff_scalar.mp l.2).1, ?_⟩
    have : (l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹ = y := by
      calc (l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹
          = (l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹ * y⁻¹ * y := by group
        _ = y := by rw [h', one_mul]
    calc (l : GL (Fin n) K) * y = (l : GL (Fin n) K) * y * (l : GL (Fin n) K)⁻¹ * l := by
          group
      _ = y * (l : GL (Fin n) K) := by rw [this]
  · rintro ⟨-, hly⟩
    apply Subtype.ext
    rw [coe_commHom, OneMemClass.coe_one, hly, mul_inv_cancel_right, mul_inv_cancel]

end CommHom

section Torus

@[expose] def qSubPi (π : Bool) (q : ℕ) : ℕ := cond π (q - 1) (q + 1)

@[expose] def diagUnits (a b c : Kˣ) : GL (Fin 3) K :=
  ⟨diagonal ![(a : K), b, c], diagonal ![((a⁻¹ : Kˣ) : K), (b⁻¹ : Kˣ), (c⁻¹ : Kˣ)],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem coe_diagUnits (a b c : Kˣ) :
    ((diagUnits a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(a : K), b, c] :=
  rfl

theorem diagUnits_mul (a b c a' b' c' : Kˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits (a * a') (b * b') (c * c') := by
  apply Units.ext
  rw [Units.val_mul, coe_diagUnits, coe_diagUnits, coe_diagUnits, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] def torusHom : Kˣ × Kˣ →* GL (Fin 3) K where
  toFun ab := diagUnits ab.1 ab.2 (ab.1 * ab.2)⁻¹
  map_one' := by
    apply Units.ext
    rw [coe_diagUnits, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' ab ab' := by
    rw [diagUnits_mul]
    congr 1
    simp only [Prod.fst_mul, Prod.snd_mul]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

theorem coe_torusHom (ab : Kˣ × Kˣ) :
    ((torusHom ab : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(ab.1 : K), ab.2, ((ab.1 * ab.2)⁻¹ : Kˣ)] :=
  rfl

theorem torusHom_injective : Function.Injective (torusHom (K := K)) := by
  intro ab ab' h
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_torusHom] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

variable {p f : ℕ}

theorem mem_rootsOfUnity_of_card [Finite K] {q : ℕ} (hK : Nat.card K = q) (u : Kˣ) :
    u ∈ rootsOfUnity (q - 1) K := by
  have := Fintype.ofFinite K
  rw [mem_rootsOfUnity]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero

theorem torusHom_mem_slPi {π : Bool} (hK : PiField π p f K) {a b : Kˣ}
    (ha : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hb : b ∈ rootsOfUnity (qSubPi π (p ^ f)) K) :
    torusHom (a, b) ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((torusHom (a, b) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_torusHom, det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have hnorm : ∀ u : Kˣ, u ∈ rootsOfUnity (p ^ f + 1) K → h.bar (u : K) * u = 1 := by
      intro u hu
      rw [mem_rootsOfUnity] at hu
      rw [h.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
    have hab : (a * b)⁻¹ ∈ rootsOfUnity (p ^ f + 1) K := inv_mem (mul_mem ha hb)
    rw [coe_torusHom, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · exact hnorm a ha
    · exact hnorm b hb
    · exact hnorm _ hab
  · rw [mem_slPi_true]
    exact hdet

theorem coe_diagTau_eq_diagonal {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![τ, τ ^ 2, 1] := by
  rw [coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem centralizer_diagTau_eq {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ} =
      (torusHom.comp ((rootsOfUnity (qSubPi π (p ^ f)) K).subtype.prodMap
        (rootsOfUnity (qSubPi π (p ^ f)) K).subtype)).range := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  ext l
  constructor
  · intro hl
    obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
    rw [Subgroup.mem_centralizer_singleton_iff] at hlC
    have hc := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hlC
    simp only [Units.val_mul, coe_diagTau_eq_diagonal] at hc
    have z := fun i j (hij : (![τ, τ ^ 2, 1] : Fin 3 → K) i ≠ ![τ, τ ^ 2, 1] j) =>
      entry_eq_zero_of_commute_diagonal hc hij
    have l01 := z 0 1 (by simpa using hττ2)
    have l02 := z 0 2 (by simpa using hτ1)
    have l10 := z 1 0 (by simpa using hττ2.symm)
    have l12 := z 1 2 (by simpa using hτ2)
    have l20 := z 2 0 (by simpa using hτ1.symm)
    have l21 := z 2 1 (by simpa using hτ2.symm)
    set M := (l : Matrix (Fin 3) (Fin 3) K) with hM
    have hMd : M = diagonal ![M 0 0, M 1 1, M 2 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [l01, l02, l10, l12, l20, l21]
    have hdet : M 0 0 * M 1 1 * M 2 2 = 1 := by
      have := ((mem_slPi_iff (p := p) (f := f) hπ).mp hlL).2
      rw [← hM, hMd, det_diagonal, Fin.prod_univ_three] at this
      simpa using this
    have h0 : M 0 0 ≠ 0 := fun h => by rw [h, zero_mul, zero_mul] at hdet; exact zero_ne_one hdet
    have h1 : M 1 1 ≠ 0 := fun h => by rw [h, mul_zero, zero_mul] at hdet; exact zero_ne_one hdet
    set a := Units.mk0 (M 0 0) h0
    set b := Units.mk0 (M 1 1) h1
    have hroot : ∀ i, M i i ≠ 0 → M i i ^ qSubPi π (p ^ f) = 1 := by
      intro i hi
      cases π
      · have h := hK.unitary
        have hu := (mem_glPi_false h).mp (slPi_le_glPi hπ hlL)
        have := congrFun (congrFun hu i) i
        rw [← hM, hMd] at this
        simp only [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
          diagonal_apply_eq, one_apply_eq] at this
        change M i i ^ (p ^ f + 1) = 1
        rw [pow_succ, ← h.bar_apply]
        fin_cases i <;> simpa [mul_comm] using this
      · have hcard : Nat.card K = p ^ f := by simpa [piCard] using hK.card
        have := hK.finite
        have hu := mem_rootsOfUnity_of_card hcard (Units.mk0 (M i i) hi)
        rw [mem_rootsOfUnity] at hu
        have := congrArg Units.val hu
        change M i i ^ (p ^ f - 1) = 1
        simpa using this
    refine ⟨(⟨a, (mem_rootsOfUnity _ _).mpr (Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hroot 0 h0))⟩,
      ⟨b, (mem_rootsOfUnity _ _).mpr (Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hroot 1 h1))⟩), ?_⟩
    apply Units.ext
    change ((torusHom (a, b) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = M
    rw [coe_torusHom]
    have h22' : (M 1 1)⁻¹ * (M 0 0)⁻¹ = M 2 2 := by
      calc (M 1 1)⁻¹ * (M 0 0)⁻¹ = (M 0 0 * M 1 1)⁻¹ := by rw [mul_inv, mul_comm]
        _ = M 2 2 := by rw [inv_eq_iff_eq_inv]; exact eq_inv_of_mul_eq_one_left hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, b, l01, l02, l10, l12, l20, l21, h22']
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨torusHom_mem_slPi hK a.2 b.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    simp only [MonoidHom.comp_apply, MonoidHom.coe_prodMap, Prod.map, Subgroup.coe_subtype,
      Units.val_mul, coe_torusHom, coe_diagTau_eq_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

theorem qSubPi_ne_zero {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    qSubPi π (p ^ f) ≠ 0 := by
  cases π
  · exact Nat.succ_ne_zero _
  · change p ^ f % 3 = 1 at hq
    change p ^ f - 1 ≠ 0
    have : 1 < p ^ f := Nat.one_lt_pow (by have := hK.one_le; omega) hK.prime.one_lt
    omega

theorem qSubPi_dvd {π : Bool} (hK : PiField π p f K) :
    qSubPi π (p ^ f) ∣ Nat.card K - 1 := by
  rw [hK.card]
  cases π
  · change p ^ f + 1 ∣ (p ^ f) ^ 2 - 1
    have h1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
    refine ⟨p ^ f - 1, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hk]
    simp only [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  · exact dvd_refl _

theorem card_rootsOfUnity_qSubPi {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f)) :
    Nat.card (rootsOfUnity (qSubPi π (p ^ f)) K) = qSubPi π (p ^ f) := by
  have := hK.finite
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  exact CFSG.LinearGroups.card_rootsOfUnity_of_dvd (qSubPi_dvd hK)

theorem centralizer_diagTau_mulEquiv {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Nonempty (↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) ≃*
      Multiplicative (ZMod (qSubPi π (p ^ f))) × Multiplicative (ZMod (qSubPi π (p ^ f)))) := by
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  set T := rootsOfUnity (qSubPi π (p ^ f)) K
  set φ : T × T →* GL (Fin 3) K := torusHom.comp (T.subtype.prodMap T.subtype) with hφdef
  have hφ : Function.Injective φ := by
    intro x y h
    have h' := torusHom_injective h
    simp only [MonoidHom.coe_prodMap, Prod.map, Subgroup.coe_subtype] at h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have e2 : φ.range ≃* ↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}) :=
    MulEquiv.subgroupCongr (centralizer_diagTau_eq hK hq hτ hτ1).symm
  have hcard := card_rootsOfUnity_qSubPi hK hq
  have e3 : Multiplicative (ZMod (Nat.card T)) ≃* T :=
    zmodCyclicMulEquiv (rootsOfUnity.isCyclic K (qSubPi π (p ^ f)))
  have e4 : Multiplicative (ZMod (qSubPi π (p ^ f))) ≃* Multiplicative (ZMod (Nat.card T)) :=
    AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard.symm).toAddEquiv
  exact ⟨e2.symm.trans ((MonoidHom.ofInjective hφ).symm.trans
    ((e4.trans e3).prodCongr (e4.trans e3)).symm)⟩

theorem cycThree_conj_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((cycThree * diagTau hτ * cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ ^ 2 • ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have h3 : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
  have h4 : τ ^ 2 * τ ^ 2 = τ := by
    calc τ ^ 2 * τ ^ 2 = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  simp only [Units.val_mul]
  rw [show ((cycThree⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![0, 1, 0; 0, 0, 1; 1, 0, 0] from rfl, coe_cycThree, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h3, h4]

@[expose] noncomputable def scalarHom : Kˣ →* StatedScalars (Fin 3) K :=
  (GeneralLinearGroup.scalar (Fin 3)).rangeRestrict

theorem coe_scalarHom (c : Kˣ) :
    ((scalarHom c : StatedScalars (Fin 3) K) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c :=
  rfl

theorem det_scalar (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (c : K) ^ 3 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal, Fin.prod_const]

theorem mem_rootsOfUnity_of_det_scalar {c : Kˣ}
    (h : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      1) : c ∈ rootsOfUnity 3 K := by
  rw [det_scalar] at h
  rw [mem_rootsOfUnity]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)

theorem range_commHom_le {L : Subgroup (GL (Fin 3) K)} (y : GL (Fin 3) K)
    (hL : ∀ l ∈ L, ((l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) :
    (commHom L y).range ≤ (rootsOfUnity 3 K).map scalarHom := by
  rintro _ ⟨l, rfl⟩
  obtain ⟨c, hc⟩ := (commHom L y l).2
  refine ⟨c, ?_, Subtype.ext hc⟩
  have hdet : ((commHom L y l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_commHom]
    simp only [Units.val_mul, det_mul]
    have hl := hL _ (mem_centMod_iff_scalar.mp l.2).1
    have hli : (((l : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel (l : GL (Fin 3) K)))
      rw [Units.val_mul, det_mul, hl, one_mul, Units.val_one, det_one] at this
      exact this
    have hyi : (y : Matrix (Fin 3) (Fin 3) K).det * ((y⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    rw [hl, hli, one_mul, mul_one, hyi]
  rw [← hc] at hdet
  exact mem_rootsOfUnity_of_det_scalar hdet

theorem card_range_commHom_le {L : Subgroup (GL (Fin 3) K)} (y : GL (Fin 3) K)
    (hL : ∀ l ∈ L, ((l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) [Finite K] :
    Nat.card (commHom L y).range ≤ 3 := by
  have := Fintype.ofFinite K
  calc Nat.card (commHom L y).range ≤ Nat.card ((rootsOfUnity 3 K).map scalarHom) :=
        Subgroup.card_le_of_le (range_commHom_le y hL)
    _ ≤ Nat.card (rootsOfUnity 3 K) :=
        Nat.card_le_card_of_surjective _ (scalarHom.subgroupMap_surjective _)
    _ ≤ 3 := card_rootsOfUnity K 3

theorem relindex_centralizer_diagTau {π : Bool} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagTau hτ}).relIndex
      (centMod (slPi π 3 (p ^ f) K) (diagTau hτ)) = 3 := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  set L := slPi π 3 (p ^ f) K
  set D := diagTau hτ
  set u : Kˣ := Units.mk0 (τ ^ 2) (pow_ne_zero 2 hτ0)
  have hcyc : cycThree ∈ centMod L D := by
    refine mem_centMod_iff_scalar.mpr ⟨cycThree_mem_slPi hπ, GeneralLinearGroup.scalar (Fin 3) u,
      ⟨u, rfl⟩, Units.ext ?_⟩
    rw [cycThree_conj_diagTau, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hs : commHom L D ⟨cycThree, hcyc⟩ = scalarHom u := by
    apply Subtype.ext
    rw [coe_commHom, coe_scalarHom]
    apply Units.ext
    rw [Units.val_mul, cycThree_conj_diagTau, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    rfl
  have hord : orderOf (scalarHom u : StatedScalars (Fin 3) K) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have hu3 : u ^ 3 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ← pow_mul,
          show 2 * 3 = 3 * 2 by norm_num, pow_mul, hτ, one_pow])
      rw [hu3, map_one]
    · intro h
      have h' := congrArg (fun z : StatedScalars (Fin 3) K =>
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
      simp only [coe_scalarHom, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        diagonal_apply_eq, OneMemClass.coe_one, Units.val_one, one_apply_eq, Units.val_mk0,
        u] at h'
      exact hτ2 h'
  have hle : Nat.card (commHom L D).range ≤ 3 :=
    card_range_commHom_le D fun l hl => ((mem_slPi_iff hπ).mp hl).2
  have hge : 3 ≤ Nat.card (commHom L D).range :=
    calc 3 = orderOf (scalarHom u : StatedScalars (Fin 3) K) := hord.symm
      _ = Nat.card (Subgroup.zpowers (scalarHom u : StatedScalars (Fin 3) K)) :=
          (Nat.card_zpowers _).symm
      _ ≤ Nat.card (commHom L D).range :=
          Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr ⟨_, hs⟩)
  rw [Subgroup.relIndex, ← ker_commHom, Subgroup.index_ker]
  omega

end Torus

section Block

@[expose] def blockMat (a : K) (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![a, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

theorem blockMat_mul (a a' : K) (B B' : Matrix (Fin 2) (Fin 2) K) :
    blockMat a B * blockMat a' B' = blockMat (a * a') (B * B') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockMat_one : blockMat (1 : K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem det_blockMat (a : K) (B : Matrix (Fin 2) (Fin 2) K) :
    (blockMat a B).det = a * B.det := by
  rw [blockMat, det_fin_three, det_fin_two]
  simp
  ring

theorem blockMat_map (φ : K → K) (h0 : φ 0 = 0) (a : K) (B : Matrix (Fin 2) (Fin 2) K) :
    (blockMat a B).map φ = blockMat (φ a) (B.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, h0]

theorem blockMat_transpose (a : K) (B : Matrix (Fin 2) (Fin 2) K) :
    (blockMat a B)ᵀ = blockMat a Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockMat_det_inv_mul (B : GL (Fin 2) K) :
    blockMat (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) (B : Matrix (Fin 2) (Fin 2) K) *
      blockMat ((GeneralLinearGroup.det B : Kˣ) : K) ((B⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [blockMat_mul, Units.inv_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockMat_one]

theorem blockMat_det_mul_inv (B : GL (Fin 2) K) :
    blockMat ((GeneralLinearGroup.det B : Kˣ) : K) ((B⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *
      blockMat (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [blockMat_mul, Units.mul_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockMat_one]

@[expose] noncomputable def blockHom : GL (Fin 2) K →* GL (Fin 3) K where
  toFun B := ⟨blockMat (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) (B : Matrix (Fin 2) (Fin 2) K),
    blockMat ((GeneralLinearGroup.det B : Kˣ) : K) ((B⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), blockMat_det_inv_mul B, blockMat_det_mul_inv B⟩
  map_one' := Units.ext (by
    change blockMat (((GeneralLinearGroup.det (1 : GL (Fin 2) K))⁻¹ : Kˣ) : K)
      ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [map_one, inv_one, Units.val_one, Units.val_one]
    exact blockMat_one)
  map_mul' B B' := Units.ext (by
    change blockMat (((GeneralLinearGroup.det (B * B'))⁻¹ : Kˣ) : K)
      ((B * B' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blockMat (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) (B : Matrix (Fin 2) (Fin 2) K) *
        blockMat (((GeneralLinearGroup.det B')⁻¹ : Kˣ) : K) (B' : Matrix (Fin 2) (Fin 2) K)
    rw [blockMat_mul, map_mul, mul_inv, Units.val_mul, Units.val_mul])

theorem coe_blockHom (B : GL (Fin 2) K) :
    ((blockHom B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat (((GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) B :=
  rfl

theorem blockHom_injective : Function.Injective (blockHom (K := K)) := by
  intro B B' h
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_blockHom] at h'
  apply Units.ext
  ext i j
  have := congrFun (congrFun h' i.succ) j.succ
  fin_cases i <;> fin_cases j <;> simpa [blockMat] using this

@[expose] def diagE (e : Kˣ) : GL (Fin 3) K := diagUnits e 1 1

theorem coe_diagE (e : Kˣ) :
    ((diagE e : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(e : K), 1, 1] := by
  rw [diagE, coe_diagUnits]
  rfl

variable {p f : ℕ}

theorem blockHom_mem_slPi {π : Bool} (hK : PiField π p f K) {B : GL (Fin 2) K}
    (hB : B ∈ glPi π 2 (p ^ f) K) : blockHom B ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((blockHom B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_blockHom, det_blockMat, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]
    exact inv_mul_cancel₀ (by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _)
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have hBu := (mem_glPi_false h).mp hB
    have hd : h.bar ((GeneralLinearGroup.det B : Kˣ) : K) * (GeneralLinearGroup.det B : Kˣ) =
        1 := by
      have := congrArg Matrix.det hBu
      rw [det_mul, det_transpose, show ((B : Matrix (Fin 2) (Fin 2) K).map h.bar).det =
        h.bar (B : Matrix (Fin 2) (Fin 2) K).det from (RingHom.map_det h.bar _).symm,
        det_one] at this
      simpa [GeneralLinearGroup.val_det_apply] using this
    rw [coe_blockHom, blockMat_map _ (map_zero _), blockMat_transpose, blockMat_mul, hBu,
      Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hd, inv_one, blockMat_one]
  · rw [mem_slPi_true]
    exact hdet

theorem blockHom_commute (e : Kˣ) (B : GL (Fin 2) K) :
    blockHom B * diagE e = diagE e * blockHom B := by
  apply Units.ext
  simp only [Units.val_mul, coe_blockHom, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, Matrix.mul_diagonal, Matrix.diagonal_mul,
    mul_comm]

theorem centralizer_diagE_eq {π : Bool} (hK : PiField π p f K) {e : Kˣ} (he : e ≠ 1) :
    slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE e} =
      (glPi π 2 (p ^ f) K).map blockHom := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have he' : (e : K) ≠ 1 := fun h => he (Units.ext h)
  ext l
  constructor
  · intro hl
    obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
    rw [Subgroup.mem_centralizer_singleton_iff] at hlC
    have hc := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hlC
    simp only [Units.val_mul, coe_diagE] at hc
    have z := fun i j (hij : (![(e : K), 1, 1] : Fin 3 → K) i ≠ ![(e : K), 1, 1] j) =>
      entry_eq_zero_of_commute_diagonal hc hij
    have l01 := z 0 1 (by simpa using he')
    have l02 := z 0 2 (by simpa using he')
    have l10 := z 1 0 (by simpa using he'.symm)
    have l20 := z 2 0 (by simpa using he'.symm)
    set M := (l : Matrix (Fin 3) (Fin 3) K) with hM
    set B : Matrix (Fin 2) (Fin 2) K := !![M 1 1, M 1 2; M 2 1, M 2 2] with hBdef
    have hMB : M = blockMat (M 0 0) B := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blockMat, hBdef, l01, l02, l10, l20]
    have hdet : M 0 0 * B.det = 1 := by
      have := ((mem_slPi_iff (p := p) (f := f) hπ).mp hlL).2
      rw [← hM, hMB, det_blockMat] at this
      exact this
    have hBdet : B.det ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
    set B' := GeneralLinearGroup.mkOfDetNeZero B hBdet
    have hB'v : (B' : Matrix (Fin 2) (Fin 2) K) = B := GeneralLinearGroup.val_mkOfDetNeZero _ _
    have hB'mem : B' ∈ glPi π 2 (p ^ f) K := by
      cases π
      · have h := hK.unitary
        rw [mem_glPi_false h, hB'v]
        have hu := (mem_glPi_false h).mp (slPi_le_glPi hπ hlL)
        rw [← hM, hMB, blockMat_map _ (map_zero _), blockMat_transpose, blockMat_mul,
          ← blockMat_one] at hu
        ext i j
        have := congrFun (congrFun hu i.succ) j.succ
        fin_cases i <;> fin_cases j <;> simpa [blockMat] using this
      · exact mem_glPi_true _ _
    refine ⟨B', hB'mem, Units.ext ?_⟩
    rw [coe_blockHom, hB'v, ← hM, hMB, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply,
      hB'v, eq_inv_of_mul_eq_one_left hdet]
  · rintro ⟨B, hB, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨blockHom_mem_slPi hK hB, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact blockHom_commute e B

theorem centralizer_diagE_mulEquiv {π : Bool} (hK : PiField π p f K) {e : Kˣ} (he : e ≠ 1) :
    Nonempty (↥(slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE e}) ≃* glPi π 2 (p ^ f) K) :=
  ⟨(MulEquiv.subgroupCongr (centralizer_diagE_eq hK he)).trans
    (Subgroup.equivMapOfInjective _ _ blockHom_injective).symm⟩

theorem centMod_diagE_eq (π : Bool) {e : Kˣ} (he3 : (e : K) ^ 3 = 1)
    (h3 : (3 : K) ≠ 0) :
    centMod (slPi π 3 (p ^ f) K) (diagE e) =
      slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {diagE e} := by
  refine le_antisymm (fun l hl => ?_) (centralizer_le_centMod _ _)
  obtain ⟨hlL, z, ⟨c, rfl⟩, hz⟩ := mem_centMod_iff_scalar.mp hl
  have he2 : (e : K) + 2 ≠ 0 := by
    intro h
    have : (e : K) = -2 := by linear_combination h
    rw [this] at he3
    apply h3
    have h9 : (3 : K) * 3 = 0 := by linear_combination -he3
    exact (mul_self_eq_zero.mp h9)
  have htr := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K).trace) hz
  simp only [Units.val_mul] at htr
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, coe_diagE] at htr
  simp only [trace_diagonal, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul] at htr
  have hc1 : (c : K) = 1 := by
    have : ((c : K) - 1) * ((e : K) + 2) = 0 := by linear_combination -htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right he2)
  have hc : c = 1 := Units.ext hc1
  subst hc
  refine Subgroup.mem_inf.mpr ⟨hlL, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [map_one, one_mul] at hz
  calc l * diagE e = l * diagE e * l⁻¹ * l := by group
    _ = diagE e * l := by rw [hz]

end Block

end CFSG.RankThree.PartTwo.Sec4
