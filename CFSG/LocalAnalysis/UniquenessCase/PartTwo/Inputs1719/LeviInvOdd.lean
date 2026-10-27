module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvDynkin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem injective_of_isLeviFamily {P : Subgroup G} {d : ℕ} {L : Fin d → Subgroup G}
    (hL : IsLeviFamily P d L) : Function.Injective L := by
  intro i j hij
  by_contra hne
  have hle : ⁅L i, L j⁆ ≤ pCoreOf 2 P := hL.commutator_le i j hne
  rw [hij] at hle
  have hb : ⁅barSub P (L j), barSub P (L j)⁆ = ⊥ := by
    rw [← barSub_commutator (hL.le j) (hL.le j)]
    exact (barSub_eq_bot_iff (commutator_le_of_le (hL.le j) (hL.le j))).mpr hle
  have : (barSub P (L j)).Normal := barSub_normal (hL.normal j)
  have h2 : Opp 2 (barSub P (L j)) = barSub P (L j) := by
    rw [← barSub_opp (hL.le j), hL.opp_eq j]
  have hbot := hO2_bar2 _ this (isPGroup_of_opp_eq_of_commutator_eq_bot h2 hb)
  exact hL.ne j (le_antisymm ((barSub_eq_bot_iff (hL.le j)).mp hbot) (hL.pCoreOf_le j))

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {P : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) : P.map (MulAut.conj x).toMonoidHom = P := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx p).mp hp
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {X : Subgroup G} {x : G}
    (h : X.map (MulAut.conj x).toMonoidHom = X) : x ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ X.map (MulAut.conj x).toMonoidHom := ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      exact mul_left_cancel (mul_right_cancel hzy)
    rwa [← this]

theorem exists_equiv_map_conj {M Dsub : Subgroup G} {d : ℕ} {L : Fin d → Subgroup G}
    (hL : IsLeviFamily (Dsub ⊓ M) d L) {x : G}
    (hx : x ∈ Subgroup.normalizer ((Dsub ⊓ M : Subgroup G) : Set G)) :
    ∃ f : Fin d ≃ Fin d, ∀ i, (L i).map (MulAut.conj x).toMonoidHom = L (f i) := by
  have hL' := hL.map (φ := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
  rw [map_conj_eq_of_mem_normalizer hx] at hL'
  obtain ⟨σ, hσ⟩ := exists_equiv_of_isDynkinFamilyIn_gen hL (isDynkinFamilyIn_of_isLeviFamily hL')
  exact ⟨σ, hσ⟩

theorem perm_mul_self_of_le_two {d : ℕ} (hd : d ≤ 2) (f : Equiv.Perm (Fin d)) : f * f = 1 := by
  interval_cases d <;> revert f <;> decide

omit [Finite G] in
theorem map_conj_pow_eq {d : ℕ} {L : Fin d → Subgroup G} {x : G} {f : Equiv.Perm (Fin d)}
    (hf : ∀ i, (L i).map (MulAut.conj x).toMonoidHom = L (f i)) (n : ℕ) (i : Fin d) :
    (L i).map (MulAut.conj (x ^ n)).toMonoidHom = L ((f ^ n) i) := by
  induction n generalizing i with
  | zero =>
    have : (MulAut.conj (x ^ 0)).toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    rw [this, Subgroup.map_id, pow_zero, Equiv.Perm.one_apply]
  | succ n ih =>
    have : (MulAut.conj (x ^ (n + 1))).toMonoidHom =
        (MulAut.conj (x ^ n)).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
      ext g
      simp [MulAut.conj_apply, pow_succ, mul_assoc]
    rw [this, ← Subgroup.map_map, hf i, ih (f i), pow_succ, Equiv.Perm.mul_apply]

theorem mem_normalizer_of_odd_of_le_two {M Dsub : Subgroup G} {d : ℕ}
    {L : Fin d → Subgroup G} (hL : IsLeviFamily (Dsub ⊓ M) d L) (hd : d ≤ 2) {x : G}
    (hx : x ∈ Subgroup.normalizer ((Dsub ⊓ M : Subgroup G) : Set G))
    (hodd : Odd (orderOf x)) (i : Fin d) : x ∈ Subgroup.normalizer (L i : Set G) := by
  obtain ⟨f, hf⟩ := exists_equiv_map_conj hL hx
  have hm : (f ^ orderOf x) i = i := by
    apply injective_of_isLeviFamily hL
    rw [← map_conj_pow_eq hf, pow_orderOf_eq_one]
    have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    rw [this, Subgroup.map_id]
  have hff : f * f = 1 := perm_mul_self_of_le_two hd f
  obtain ⟨k, hk⟩ := hodd
  have hfm : f ^ orderOf x = f := by
    rw [hk, pow_succ, pow_mul, sq, hff, one_pow, one_mul]
  apply mem_normalizer_of_map_conj_eq
  rw [hf i, ← hfm, hm]

theorem le_normalizer_of_odd_of_le_two {M Dsub : Subgroup G} {d : ℕ}
    {L : Fin d → Subgroup G} (hL : IsLeviFamily (Dsub ⊓ M) d L) (hd : d ≤ 2) {d' : ℕ}
    {K J : Fin d' → Subgroup G} (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J) {X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer ((Dsub ⊓ M : Subgroup G) : Set G)) (hXo : Odd (Nat.card X))
    (k : Fin d') : X ≤ Subgroup.normalizer (K k : Set G) := by
  obtain ⟨σ, hσ⟩ := exists_equiv_of_isDynkinFamilyIn_gen hL hKJ
  intro x hxX
  rw [hσ k]
  exact mem_normalizer_of_odd_of_le_two hL hd (hX hxX)
    (Odd.of_dvd_nat hXo (Subgroup.orderOf_dvd_natCard X hxX)) (σ k)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
