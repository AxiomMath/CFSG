module

public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem cj_zpowers (g a : LGL 2 V) :
    cj g (Subgroup.zpowers a) = Subgroup.zpowers (g * a * g⁻¹) := by
  unfold cj
  rw [MonoidHom.map_zpowers]
  rfl

theorem zpowers_conj_mem (h : Assumption131 G Γ VA i) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) (y : ↥G) :
    Subgroup.zpowers ((y * a * y⁻¹ : ↥G) : LGL 2 V) ∈ Γ := by
  have := h.invariant _ ha (y : LGL 2 V) y.2
  rwa [cj_zpowers] at this

theorem Assumption131.orbit (h : Assumption131 G Γ VA i) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) :
    Assumption131 G
      {B | ∃ y : ↥G, B = Subgroup.zpowers ((y * a * y⁻¹ : ↥G) : LGL 2 V)} VA i := by
  have hsub : ∀ B ∈ {B | ∃ y : ↥G, B = Subgroup.zpowers ((y * a * y⁻¹ : ↥G) : LGL 2 V)},
      B ∈ Γ := by
    rintro B ⟨y, rfl⟩
    exact zpowers_conj_mem h ha y
  refine
    { pos_i := h.pos_i
      le_G := fun A hA => h.le_G A (hsub A hA)
      isElemAb := fun A hA => h.isElemAb A (hsub A hA)
      invariant := ?_
      ne_bot := fun A hA => h.ne_bot A (hsub A hA)
      inf_pCore := fun A hA => h.inf_pCore A (hsub A hA)
      normalizer_eq := fun A hA => h.normalizer_eq A (hsub A hA)
      disjoint := fun A hA B hB => h.disjoint A (hsub A hA) B (hsub B hB)
      cond2 := fun A hA => h.cond2 A (hsub A hA)
      quadratic := fun A hA => h.quadratic A (hsub A hA)
      equivariant := fun A hA => h.equivariant A (hsub A hA) }
  rintro A ⟨y, rfl⟩ g hg
  refine ⟨(⟨g, hg⟩ : ↥G) * y, ?_⟩
  rw [cj_zpowers]
  simp [mul_assoc]

theorem commute_or_exists_conj_of_isConj (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A) {a : ↥G}
    (ha : Subgroup.zpowers (a : LGL 2 V) ∈ Γ) (ha2 : orderOf a = 2) {c d : ↥G}
    (hc : IsConj a c) (hd : IsConj a d) :
    c * d = d * c ∨ ∃ z ∈ Subgroup.closure ({c, d} : Set ↥G), d = z * c * z⁻¹ := by
  have hord : ∀ {e : ↥G}, IsConj a e → orderOf e = 2 := by
    intro e he
    obtain ⟨y, rfl⟩ := isConj_iff.mp he
    exact (SemiconjBy.orderOf_eq y (by simp [SemiconjBy, mul_assoc])).symm.trans ha2
  have hmem : ∀ {e : ↥G}, IsConj a e → Subgroup.zpowers (e : LGL 2 V) ∈ Γ := by
    intro e he
    obtain ⟨y, rfl⟩ := isConj_iff.mp he
    exact zpowers_conj_mem h ha y
  obtain ⟨yc, hyc⟩ := isConj_iff.mp hc
  obtain ⟨yd, hyd⟩ := isConj_iff.mp hd
  have hA := hmem hc
  have hB := hmem hd
  have hAB : ∃ g ∈ G, Subgroup.zpowers (d : LGL 2 V) = cj g (Subgroup.zpowers (c : LGL 2 V)) := by
    refine ⟨((yd * yc⁻¹ : ↥G) : LGL 2 V), (yd * yc⁻¹).2, ?_⟩
    rw [cj_zpowers]
    congr 1
    rw [← hyc, ← hyd]
    simp [mul_assoc]
  rcases thirteen_two_two h hrank hVAle hA hB hAB with hcomm | ⟨y, hy, hBy⟩
  · left
    have h1 : (SemidirectProduct.inr c : VG G) ∈ UAOf G VA (Subgroup.zpowers (c : LGL 2 V)) :=
      Subgroup.mem_sup_right (mem_aHat.mpr ⟨c, Subgroup.mem_zpowers _, rfl⟩)
    have h2 : (SemidirectProduct.inr d : VG G) ∈ UAOf G VA (Subgroup.zpowers (d : LGL 2 V)) :=
      Subgroup.mem_sup_right (mem_aHat.mpr ⟨d, Subgroup.mem_zpowers _, rfl⟩)
    have h3 := hcomm _ h1 _ h2
    rw [← map_mul, ← map_mul] at h3
    exact SemidirectProduct.inr_injective h3
  · right
    rw [cj_zpowers] at hBy
    have hdmem : (d : LGL 2 V) ∈ Subgroup.zpowers (y * (c : LGL 2 V) * y⁻¹) :=
      hBy ▸ Subgroup.mem_zpowers _
    have hordc : orderOf (c : LGL 2 V) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hord hc
    have hordy : orderOf (y * (c : LGL 2 V) * y⁻¹) = 2 :=
      (SemiconjBy.orderOf_eq y (by simp [SemiconjBy, mul_assoc])).symm.trans hordc
    have hd1 : (d : LGL 2 V) ≠ 1 := by
      intro h1
      have hd1' : d = 1 := Subtype.ext h1
      have := hord hd
      rw [hd1', orderOf_one] at this
      omega
    have hdy : (d : LGL 2 V) = y * c * y⁻¹ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdmem
      rw [← hk, ← zpow_mod_orderOf, hordy] at hd1 ⊢
      rcases Int.emod_two_eq_zero_or_one k with h2 | h2
      · rw [Nat.cast_ofNat, h2, zpow_zero] at hd1
        exact absurd rfl hd1
      · rw [Nat.cast_ofNat, h2, zpow_one]
    have hyG : y ∈ (Subgroup.closure ({c, d} : Set ↥G)).map G.subtype := by
      have hle : Subgroup.zpowers (c : LGL 2 V) ⊔ Subgroup.zpowers (d : LGL 2 V) ≤
          (Subgroup.closure ({c, d} : Set ↥G)).map G.subtype := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact ⟨c, Subgroup.subset_closure (by simp), rfl⟩
        · rw [Subgroup.zpowers_le]
          exact ⟨d, Subgroup.subset_closure (by simp), rfl⟩
      exact hle hy
    obtain ⟨z, hz, rfl⟩ := hyG
    refine ⟨z, hz, Subtype.ext ?_⟩
    simpa using hdy

end CFSG.LocalAnalysis.WeakClosure81

end
