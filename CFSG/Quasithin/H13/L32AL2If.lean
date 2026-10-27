module

public import CFSG.Quasithin.H13.L32AL2Ic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartOne.KF.SymNormalizer

public section

namespace CFSG.Quasithin.H13.L32A.L2

structure GoodModel (M : Type*) [Group M] : Prop where
  center : ∀ a : M, (∀ b, a * b = b * a) → a = 1
  inner : ∀ α : MulAut M, α ^ 3 = 1 → ∃ r : M, ∀ x, α x = r * x * r⁻¹
  card : ¬ 9 ∣ Nat.card M
  inv : ∃ t r : M, t ^ 2 = 1 ∧ r ^ 3 = 1 ∧ r ≠ 1 ∧ t * r * t⁻¹ = r⁻¹

structure GoodK {X : Type*} [Group X] (K : Subgroup X) : Prop where
  center : ∀ a ∈ K, (∀ b ∈ K, a * b = b * a) → a = 1
  inner : ∀ g ∈ Subgroup.normalizer (K : Set X), g ^ 3 = 1 →
    ∃ k ∈ K, ∀ n ∈ K, g * n * g⁻¹ = k * n * k⁻¹
  card : ¬ 9 ∣ Nat.card K
  inv : ∃ t ∈ K, ∃ r ∈ K, t ^ 2 = 1 ∧ r ^ 3 = 1 ∧ r ≠ 1 ∧ t * r * t⁻¹ = r⁻¹

theorem GoodModel.of_mulEquiv {M M' : Type*} [Group M] [Group M'] (e : M ≃* M')
    (h : GoodModel M') : GoodModel M where
  center a ha := by
    refine e.injective ((h.center (e a) fun b => ?_).trans (map_one e).symm)
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, ha b']
  inner α hα := by
    set β : MulAut M' := (e.symm.trans α).trans e with hβ
    have hβ3 : β ^ 3 = 1 := by
      ext x
      have h1 := congrArg (fun φ : MulAut M => φ (e.symm x)) hα
      simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h1
      simp only [pow_three, MulAut.mul_apply, MulAut.one_apply, hβ, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, h1, MulEquiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := h.inner β hβ3
    refine ⟨e.symm r, fun x => e.injective ?_⟩
    have h1 := hr (e x)
    simp only [hβ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  card := by rw [Nat.card_congr e.toEquiv]; exact h.card
  inv := by
    obtain ⟨t, r, ht, hr, hr1, htr⟩ := h.inv
    refine ⟨e.symm t, e.symm r, ?_, ?_, ?_, ?_⟩
    · rw [← map_pow, ht, map_one]
    · rw [← map_pow, hr, map_one]
    · intro h1
      exact hr1 (by rw [← e.apply_symm_apply r, h1, map_one])
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, htr]

theorem GoodK.of_goodModel {X : Type*} [Group X] {K : Subgroup X} (h : GoodModel ↥K) :
    GoodK K where
  center a ha hc := by
    have := h.center ⟨a, ha⟩ fun b => Subtype.ext (hc b b.2)
    exact congrArg Subtype.val this
  inner g hg hg3 := by
    set α : MulAut ↥K := K.normalizerMonoidHom ⟨g, hg⟩ with hα
    have hα3 : α ^ 3 = 1 := by
      rw [hα, ← map_pow]
      have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hg3)
      rw [this, map_one]
    obtain ⟨r, hr⟩ := h.inner α hα3
    refine ⟨r, r.2, fun n hn => ?_⟩
    have h1 := congrArg Subtype.val (hr ⟨n, hn⟩)
    simpa [hα] using h1
  card := h.card
  inv := by
    obtain ⟨t, r, ht, hr, hr1, htr⟩ := h.inv
    refine ⟨t, t.2, r, r.2, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg Subtype.val ht
    · simpa using congrArg Subtype.val hr
    · exact fun h1 => hr1 (Subtype.ext h1)
    · simpa using congrArg Subtype.val htr

theorem GoodK.of_mulEquiv {X M : Type*} [Group X] [Group M] {K : Subgroup X} (e : ↥K ≃* M)
    (h : GoodModel M) : GoodK K :=
  GoodK.of_goodModel (h.of_mulEquiv e)

theorem goodModel_perm_three : GoodModel (Equiv.Perm (Fin 3)) where
  center := by decide
  inner α _ := by
    obtain ⟨π, hπ⟩ := RankThree.PartOne.KFU.perm_three_aut_inner α.toMonoidHom α.injective
    exact ⟨π, hπ⟩
  card := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  inv := ⟨Equiv.swap 0 1, finRotate 3, by decide, by decide, by decide, by decide⟩

theorem goodModel_alt_five : GoodModel (alternatingGroup (Fin 5)) where
  center a ha := by
    have hc : a ∈ Subgroup.center (alternatingGroup (Fin 5)) :=
      Subgroup.mem_center_iff.mpr fun b => (ha b).symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    exact hc
  inner α hα := by
    obtain ⟨π, rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by norm_num) (by norm_num)).2 α
    have hπ3 : π ^ 3 = 1 :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num)).1 (by rw [map_pow, hα, map_one])
    have hsign : Equiv.Perm.sign π = 1 := by
      have h1 : Equiv.Perm.sign π ^ 3 = 1 := by rw [← map_pow, hπ3, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
      · exact h
      · rw [h] at h1
        exact absurd h1 (by decide)
    refine ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, fun x => Subtype.ext ?_⟩
    simp [MulAut.conjNormal_apply]
  card := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  inv := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 3 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      ⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
      Subtype.ext (by decide), Subtype.ext (by decide), fun h => ?_, Subtype.ext (by decide)⟩
    have := congrArg Subtype.val h
    revert this
    decide

theorem goodModel_GL32 : GoodModel (GL (Fin 3) (ZMod 2)) where
  center a ha := by
    have hc : a ∈ Subgroup.center (GL (Fin 3) (ZMod 2)) :=
      Subgroup.mem_center_iff.mpr fun b => (ha b).symm
    rw [QuasithinUnique.Setup.Family.center_GL32, Subgroup.mem_bot] at hc
    exact hc
  inner α hα := by
    obtain ⟨r, hr⟩ := exists_sq_eq_conj_of_GL32 (MulEquiv.refl _) (α * α)
    refine ⟨r, fun x => ?_⟩
    have h4 : α * α * (α * α) = α := by
      calc α * α * (α * α) = α ^ 3 * α := by rw [pow_three]; group
        _ = α := by rw [hα, one_mul]
    rw [← hr x]
    exact (congrArg (fun φ : MulAut (GL (Fin 3) (ZMod 2)) => φ x) h4).symm
  card := by
    rw [LieType.SteinbergBR.AutGL32.card_GL32]
    decide
  inv := by
    refine ⟨LieType.SteinbergBR.AutGL32.wGL,
      ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide, by decide⟩,
      ?_, ?_, ?_, ?_⟩
    · rw [pow_two]
      exact LieType.SteinbergBR.AutGL32.wGL_sq
    · rw [pow_three]
      exact Units.ext (by decide)
    · intro h
      have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
      revert this
      decide
    · exact Units.ext (by decide)

end CFSG.Quasithin.H13.L32A.L2
