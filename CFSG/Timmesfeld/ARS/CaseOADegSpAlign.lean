module

public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.ARS.CaseMSkeleton

public section

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
open CaseM

variable {n : ℕ} {F : Type} [Field F]

abbrev longC2 : Fin 2 → Fin 2 → ℤ := ![![2, 1], ![0, 1]]

theorem toStd_longC2 (i : Fin 2) : toStd 2 (longC2 i) = 2 • Pi.single i 1 := by
  ext a
  fin_cases i <;> fin_cases a <;> simp [toStd]

theorem toStd_neg_longC2 (i : Fin 2) : toStd 2 (-longC2 i) = -(2 • Pi.single i 1) := by
  rw [SpExtras.toStd_neg', toStd_longC2]

theorem longC2_one : longC2 1 = Pi.single 1 1 := by
  ext a; fin_cases a <;> rfl

theorem isTransGroup_pos₂ (i : Fin 2) :
    IsTransGroup (Pi.single (Sum.inl i) 1) (Symplectic.rootGroup 2 F (longC2 i)) := by
  refine ⟨mem_rootGroup_pos_iff (toStd_longC2 i), fun c => ?_⟩
  exact ⟨SpExtras.elt (TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong i) c, by
    rw [SpExtras.mat_elt, spTrans, spNil_inl]; rfl⟩

theorem isTransGroup_neg₂ (i : Fin 2) :
    IsTransGroup (Pi.single (Sum.inr i) 1) (Symplectic.rootGroup 2 F (-longC2 i)) := by
  refine ⟨mem_rootGroup_neg_iff (toStd_neg_longC2 i), fun c => ?_⟩
  exact ⟨SpExtras.elt (TauCeti.GLSymplecticFin.RootSubgroupIndex.negativeLong i) (-c), by
    rw [SpExtras.mat_elt, spTrans, spNil_inr, smul_neg, neg_smul]; rfl⟩

theorem mat_mulVec_ne_zero' (g : StatedSp n F) {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) :
    SpExtras.mat n F g *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (SpExtras.mat n F g⁻¹ *ᵥ ·) h
  simp only [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec, mulVec_zero] at this
  exact this

theorem spForm_smul_right' (u v : Fin n ⊕ Fin n → F) (l : F) :
    spForm u (l • v) = l * spForm u v := by
  simp [spForm, mulVec_smul, dotProduct_smul]

theorem spForm_smul_left' (u v : Fin n ⊕ Fin n → F) (l : F) :
    spForm (l • u) v = l * spForm u v := by
  simp [spForm, smul_dotProduct]

theorem isTransGroup_smul {v : Fin n ⊕ Fin n → F} {l : F} (hl : l ≠ 0)
    {X : Subgroup (StatedSp n F)} (h : IsTransGroup v X) : IsTransGroup (l • v) X :=
  IsTransGroup.of_smul (v := l • v) (inv_ne_zero hl) (by rwa [smul_smul, inv_mul_cancel₀ hl,
    one_smul])

theorem exists_aligned_sp₂ {G : Type*} [Group G] (Φ : StatedSp 2 F →* G)
    (hΦ : Function.Injective Φ) {P Q : Fin 2 → Subgroup G}
    (hP : ∀ i, ∃ g, P i = (CFSG.Timmesfeld.ARS.conjSub
      (Symplectic.rootGroup 2 F (Pi.single 1 1)) g).map Φ)
    (hQ : ∀ i, ∃ g, Q i = (CFSG.Timmesfeld.ARS.conjSub
      (Symplectic.rootGroup 2 F (Pi.single 1 1)) g).map Φ)
    (hopp : ∀ i, ¬ Commuting (P i) (Q i))
    (hcomm : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)) :
    ∃ g : StatedSp 2 F, ∀ i,
      (Symplectic.rootGroup 2 F (longC2 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) = P i ∧
      (Symplectic.rootGroup 2 F (-longC2 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) =
        Q i := by
  choose h hh using hP
  choose k hk using hQ
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀, X₀ = Symplectic.rootGroup 2 F (Pi.single 1 1) := ⟨_, rfl⟩
  rw [← hX₀def] at hh hk
  obtain ⟨e, hedef⟩ : ∃ e : Fin 2 ⊕ Fin 2 → F, e = Pi.single (Sum.inl 1) 1 := ⟨_, rfl⟩
  have he0 : e ≠ 0 := fun h0 => by
    have := congrFun h0 (Sum.inl 1)
    simp [hedef] at this
  have hX₀ : IsTransGroup e X₀ := by
    rw [hX₀def, hedef, ← longC2_one]
    exact isTransGroup_pos₂ 1
  obtain ⟨p, hpdef⟩ : ∃ p : Fin 2 → Fin 2 ⊕ Fin 2 → F,
      p = fun i => SpExtras.mat 2 F (h i) *ᵥ e := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : Fin 2 → Fin 2 ⊕ Fin 2 → F,
      q = fun i => SpExtras.mat 2 F (k i) *ᵥ e := ⟨_, rfl⟩
  have hpT : ∀ i, IsTransGroup (p i) (CFSG.Timmesfeld.ARS.conjSub X₀ (h i)) := fun i => by
    rw [hpdef]; exact hX₀.conjSub (h i)
  have hqT : ∀ i, IsTransGroup (q i) (CFSG.Timmesfeld.ARS.conjSub X₀ (k i)) := fun i => by
    rw [hqdef]; exact hX₀.conjSub (k i)
  have hp0 : ∀ i, p i ≠ 0 := fun i => by rw [hpdef]; exact mat_mulVec_ne_zero' (h i) he0
  have hq0 : ∀ i, q i ≠ 0 := fun i => by rw [hqdef]; exact mat_mulVec_ne_zero' (k i) he0
  have hc : ∀ {X Y : Subgroup G}, Commuting X Y → ∀ {A B : Subgroup (StatedSp 2 F)},
      X = A.map Φ → Y = B.map Φ → Commuting A B := fun hXY A B hA hB =>
    (commuting_map_iff hΦ).1 (hA ▸ hB ▸ hXY)
  have hprop : ∀ {v w : Fin 2 ⊕ Fin 2 → F} {X Y : Subgroup (StatedSp 2 F)}, IsTransGroup v X →
      IsTransGroup w Y → w ≠ 0 → (∃ l : F, w = l • v) → Y = X := by
    rintro v w X Y hX hY hw ⟨l, rfl⟩
    have hl : l ≠ 0 := fun hl => hw (by rw [hl, zero_smul])
    exact (hY.of_smul hl).eq hX
  have hBpq : ∀ i, spForm (p i) (q i) ≠ 0 := fun i hB =>
    hopp i (by rw [hh i, hk i]; exact (commuting_map_iff hΦ).2 ((hpT i).commuting (hqT i) hB))
  have hBpp : ∀ i j, spForm (p i) (p j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact spForm_self _
    rcases (hpT i).spForm_eq_zero (hpT j) (hp0 i)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_left) (hh i) (hh j)) with h0 | hl
    · exact h0
    · exfalso
      have hPji : P j = P i := by rw [hh i, hh j, hprop (hpT i) (hpT j) (hp0 j) hl]
      exact hopp i (by rw [← hPji]; exact ((hcomm i j hij).mono le_sup_right le_sup_left).symm)
  have hBqq : ∀ i j, spForm (q i) (q j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact spForm_self _
    rcases (hqT i).spForm_eq_zero (hqT j) (hq0 i)
        (hc ((hcomm i j hij).mono le_sup_right le_sup_right) (hk i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQji : Q j = Q i := by rw [hk i, hk j, hprop (hqT i) (hqT j) (hq0 j) hl]
      exact hopp i (by rw [← hQji]; exact ((hcomm i j hij).mono le_sup_left le_sup_right))
  have hBpq' : ∀ i j, i ≠ j → spForm (p i) (q j) = 0 := by
    intro i j hij
    rcases (hpT i).spForm_eq_zero (hqT j) (hp0 i)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_right) (hh i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQP : Q j = P i := by rw [hh i, hk j, hprop (hpT i) (hqT j) (hq0 j) hl]
      exact hopp j (by rw [hQP]; exact ((hcomm i j hij).mono le_sup_left le_sup_left).symm)
  have hq'T : ∀ i, IsTransGroup ((spForm (p i) (q i))⁻¹ • q i)
      (CFSG.Timmesfeld.ARS.conjSub X₀ (k i)) := fun i =>
    isTransGroup_smul (inv_ne_zero (hBpq i)) (hqT i)
  obtain ⟨g, hg⟩ := exists_mem_statedSp_mulVec (p := p)
    (q := fun i => (spForm (p i) (q i))⁻¹ • q i) hBpp
    (fun i j => by rw [spForm_smul_left', spForm_smul_right', hBqq, mul_zero, mul_zero])
    (fun i j => by
      rw [spForm_smul_right']
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left_iff.2 (fun h => absurd rfl h), inv_mul_cancel₀ (hBpq i)]
      · rw [ite_eq_right_iff.2 (fun h => absurd h hij), hBpq' i j hij, mul_zero])
  refine ⟨g, fun i => ⟨?_, ?_⟩⟩
  · rw [← Subgroup.map_map, hh i]
    congr 1
    have := (isTransGroup_pos₂ (F := F) i).conjSub g
    rw [(hg i).1] at this
    exact this.eq (hpT i)
  · rw [← Subgroup.map_map, hk i]
    congr 1
    have := (isTransGroup_neg₂ (F := F) i).conjSub g
    rw [(hg i).2] at this
    exact this.eq (hq'T i)

end CFSG.Timmesfeld.ARS.CaseOADeg
