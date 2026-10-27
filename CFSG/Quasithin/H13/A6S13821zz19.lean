module

public import CFSG.Quasithin.H13.A6S13821zz18
public import CFSG.Quasithin.Background.HSL3PairM

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair Matrix
open scoped Matrix

section Count

theorem card_le_two_of_injective {ι X : Type} [Zero X] {f : ι → X} (hf : Function.Injective f)
    {α : X} (h : ∀ i, f i = 0 ∨ f i = α) : Nat.card ι ≤ 2 := by
  classical
  have hg : Function.Injective fun i => decide (f i = 0) := by
    intro i j hij
    apply hf
    by_cases hi : f i = 0 <;> by_cases hj : f j = 0
    · rw [hi, hj]
    · simp [hi, hj] at hij
    · simp [hi, hj] at hij
    · rw [(h i).resolve_left hi, (h j).resolve_left hj]
  calc Nat.card ι ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hg
    _ = 2 := by simp

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem exists_eq_smul_cross {φ₁ φ₂ u : Fin 3 → K} (hn : crossProduct φ₁ φ₂ ≠ 0)
    (h₁ : φ₁ ⬝ᵥ u = 0) (h₂ : φ₂ ⬝ᵥ u = 0) : ∃ a : K, u = a • crossProduct φ₁ φ₂ := by
  have h := cross_cross_eq_smul_sub_smul φ₁ φ₂ u
  rw [h₁, h₂, zero_smul, zero_smul, sub_zero] at h
  by_contra hne
  push Not at hne
  have hli : LinearIndependent K ![crossProduct φ₁ φ₂, u] :=
    (LinearIndependent.pair_iff' hn).mpr fun a ha => hne a ha.symm
  exact (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h

theorem card_mul_card_lt (hK : Nat.card K = 4) {ι Y : Type} [Finite ι] [Finite Y]
    {c : Fin 3 → K} (hc : c ≠ 0) {φ : ι → Fin 3 → K} (hφ : Function.Injective φ)
    (hφc : ∀ i, c ⬝ᵥ φ i = 0) (hι : 4 < Nat.card ι) {τ : Y → (Fin 3 → K) × (Fin 3 → K)}
    (hτ : Function.Injective τ) (α : (Fin 3 → K) × (Fin 3 → K))
    (hS : ∀ y i, ((φ i ⬝ᵥ (τ y).1) • c, (c ⬝ᵥ (τ y).2) • φ i) = 0 ∨
      ((φ i ⬝ᵥ (τ y).1) • c, (c ⬝ᵥ (τ y).2) • φ i) = α) :
    Nat.card Y * Nat.card ι < Nat.card K ^ 6 := by
  classical
  have hφ' : Function.Injective fun i => (⟨φ i, hφc i⟩ : {x : Fin 3 → K // c ⬝ᵥ x = 0}) :=
    fun i j h => hφ (congrArg Subtype.val h)
  have hι16 : Nat.card ι ≤ 16 := by
    have := Nat.card_le_card_of_injective _ hφ'
    rwa [card_orth hc, hK] at this
  have hw : ∀ y, c ⬝ᵥ (τ y).2 = 0 := by
    intro y
    by_contra hμ
    have hinj : Function.Injective fun i => ((φ i ⬝ᵥ (τ y).1) • c, (c ⬝ᵥ (τ y).2) • φ i) := by
      intro i j hij
      exact hφ (smul_right_injective _ hμ (congrArg Prod.snd hij))
    have := card_le_two_of_injective hinj (hS y)
    omega
  have hv : ∀ y i, (φ i ⬝ᵥ (τ y).1) • c = 0 ∨ (φ i ⬝ᵥ (τ y).1) • c = α.1 := by
    intro y i
    rcases hS y i with h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
  obtain ⟨i₁, hi₁⟩ : ∃ i, φ i ≠ 0 := by
    by_contra h
    push Not at h
    have : Nat.card ι ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr ⟨fun i j => hφ ((h i).trans (h j).symm)⟩
    omega
  obtain ⟨i₂, hn⟩ : ∃ i, crossProduct (φ i₁) (φ i) ≠ 0 := by
    by_contra h
    push Not at h
    have hdep : ∀ i, ∃ a : K, a • φ i₁ = φ i := by
      intro i
      by_contra hne
      push Not at hne
      exact (crossProduct_ne_zero_iff_linearIndependent.mpr
        ((LinearIndependent.pair_iff' hi₁).mpr hne)) (h i)
    choose a ha using hdep
    have hai : Function.Injective a := fun i i' h => hφ (by rw [← ha i, ← ha i', h])
    have := Nat.card_le_card_of_injective a hai
    omega
  obtain ⟨j, hj⟩ : ∃ j, crossProduct (φ i₁) (φ i₂) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have hkey : ∀ u : Fin 3 → K, u j = 0 → φ i₁ ⬝ᵥ u = 0 → φ i₂ ⬝ᵥ u = 0 → u = 0 := by
    intro u hu h₁ h₂
    obtain ⟨a, rfl⟩ := exists_eq_smul_cross hn h₁ h₂
    have ha : a * crossProduct (φ i₁) (φ i₂) j = 0 := hu
    rw [(mul_eq_zero.mp ha).resolve_right hj, zero_smul]
  have hK6 : Nat.card K ^ 6 = 4096 := by rw [hK]; norm_num
  rw [hK6]
  by_cases h16 : Nat.card ι = 16
  ·
    have hb := hφ'.bijective_of_nat_card_le (by rw [card_orth hc, hK, h16]; norm_num)
    have hzero : ∀ y i, φ i ⬝ᵥ (τ y).1 = 0 := by
      intro y i
      by_contra hμ
      have hk : ∀ κ : K, ∃ i', φ i' = κ • φ i := by
        intro κ
        obtain ⟨i', hi'⟩ := hb.2 ⟨κ • φ i, by rw [dotProduct_smul, hφc, smul_zero]⟩
        exact ⟨i', congrArg Subtype.val hi'⟩
      choose f hf using hk
      have hinj : Function.Injective fun κ : K => (φ (f κ) ⬝ᵥ (τ y).1) • c := by
        intro κ κ' h
        simp only [hf, smul_dotProduct, smul_eq_mul] at h
        exact mul_right_cancel₀ hμ (smul_left_injective K hc h)
      have := card_le_two_of_injective hinj fun κ => hv y (f κ)
      omega
    have hinj : Function.Injective fun y : Y =>
        ((τ y).1 j, (⟨(τ y).2, hw y⟩ : {x : Fin 3 → K // c ⬝ᵥ x = 0})) := by
      intro y y' h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply hτ
      refine Prod.ext (sub_eq_zero.mp (hkey _ ?_ ?_ ?_)) h2
      · rw [Pi.sub_apply, h1, sub_self]
      · rw [dotProduct_sub, hzero, hzero, sub_self]
      · rw [dotProduct_sub, hzero, hzero, sub_self]
    have hY := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, card_orth hc, hK] at hY
    rw [h16]
    omega
  ·
    let T := {κ : K // κ • c = 0 ∨ κ • c = α.1}
    have hT : Nat.card T ≤ 2 :=
      card_le_two_of_injective (f := fun κ : T => (κ : K) • c)
        (fun a b h => Subtype.ext (smul_left_injective K hc h)) fun κ => κ.2
    have hinj : Function.Injective fun y : Y =>
        ((τ y).1 j, (⟨φ i₁ ⬝ᵥ (τ y).1, hv y i₁⟩ : T), (⟨φ i₂ ⬝ᵥ (τ y).1, hv y i₂⟩ : T),
          (⟨(τ y).2, hw y⟩ : {x : Fin 3 → K // c ⬝ᵥ x = 0})) := by
      intro y y' h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      apply hτ
      refine Prod.ext (sub_eq_zero.mp (hkey _ ?_ ?_ ?_)) h4
      · rw [Pi.sub_apply, h1, sub_self]
      · rw [dotProduct_sub, h2, sub_self]
      · rw [dotProduct_sub, h3, sub_self]
    have hY := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_orth hc, hK] at hY
    change Nat.card Y ≤ 4 * (Nat.card T * (Nat.card T * 4 ^ 2)) at hY
    have hTT : Nat.card T * (Nat.card T * 4 ^ 2) ≤ 64 :=
      calc Nat.card T * (Nat.card T * 4 ^ 2) ≤ 2 * (2 * 4 ^ 2) :=
            Nat.mul_le_mul hT (Nat.mul_le_mul_right _ hT)
        _ = 64 := by norm_num
    have hY' : Nat.card Y ≤ 256 := by omega
    have hι15 : Nat.card ι ≤ 15 := by omega
    calc Nat.card Y * Nat.card ι ≤ 256 * 15 := Nat.mul_le_mul hY' hι15
      _ < 4096 := by norm_num

end Count

section Model

variable {K : Type} [Field K]

theorem toAdd_pairHom_comm {g : GL (Fin 3) K} (hg2 : g * g = 1) {c φ : Fin 3 → K}
    (hgφ : (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec c φ) (x : PairMod K) :
    (Multiplicative.toAdd (pairHom g x * x⁻¹).1, Multiplicative.toAdd (pairHom g x * x⁻¹).2) =
      ((φ ⬝ᵥ Multiplicative.toAdd x.1) • c, (c ⬝ᵥ Multiplicative.toAdd x.2) • φ) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hdual : ((dualGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec φ c := by
    rw [coe_dualGL, hginv, hgφ, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_vecMulVec]
  have h1 : Multiplicative.toAdd (pairHom g x * x⁻¹).1 =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.1 - Multiplicative.toAdd x.1 := by
    rw [Prod.fst_mul, Prod.fst_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rfl
  have h2 : Multiplicative.toAdd (pairHom g x * x⁻¹).2 =
      ((dualGL g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.2 -
        Multiplicative.toAdd x.2 := by
    rw [Prod.snd_mul, Prod.snd_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rfl
  rw [h1, h2, hgφ, hdual, one_add_vecMulVec_mulVec, one_add_vecMulVec_mulVec,
    add_sub_cancel_left, add_sub_cancel_left]

theorem eq_one_or_eq_of_mem_zpowers {V : Type} [Group V] {a y : V} (ha : a ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have e : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
    rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_two, ← sq, ha, _root_.one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [e, h, zpow_zero]
  · right
    rw [e, h, zpow_one]

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem sq_eq_one_pairMod (x : PairMod K) : x ^ 2 = 1 := by
  have h : ∀ y : StdMod (Fin 3) K, y ^ 2 = 1 := fun y => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero]
  exact Prod.ext (h x.1) (h x.2)

theorem sl34Quad_model (hK : Nat.card K = 4) {A : Subgroup (MulAut (PairMod K))}
    (hAN : A ≤ pairNorm K) (hA : IsElemAbelian2 A) {D : Subgroup (PairMod K)}
    (hD : D.index ≤ Nat.card A) (a₁ : PairMod K)
    (hDA : ∀ d ∈ D, ∀ a ∈ A, a d * d⁻¹ ∈ Subgroup.zpowers a₁) : A = ⊥ := by
  classical
  have : Finite (MulAut (PairMod K)) := MulEquiv.finite_left
  have hK' : Nat.card K = 2 ^ 2 := hK
  obtain ⟨hAc, hA2⟩ := hA
  have hW : Nat.card (PairMod K) = 4096 := by rw [card_pairMod, hK]; norm_num
  have hDW := D.card_mul_index
  rw [hW] at hDW
  have hA16 : Nat.card A ≤ 16 :=
    (card_le_two_pow_pRank le_rfl (isElemAbelian2_iff.mp ⟨hAc, hA2⟩)).trans
      ((Nat.pow_le_pow_right (by norm_num) (pRank_le le_rfl hK' hAN)).trans (by norm_num))
  have hfix : ∀ a ∈ A, 4096 ≤ 2 * Nat.card (fixV (Subgroup.zpowers a)) * D.index := by
    intro a ha
    rw [← hW]
    exact card_le_two_mul_card_fixV_mul_index sq_eq_one_pairMod a a₁ fun d hd => hDA d hd a ha
  by_contra hA1
  have hASL : ∀ a ∈ A, a ∈ pairSL K := by
    intro a ha
    by_contra haS
    have ha2 : a * a = 1 := by rw [← sq]; exact hA2 a ha
    have hc64 : Nat.card (fixV (Subgroup.zpowers a)) ≤ 64 := by
      by_cases hts : a ∈ pairSub K
      · obtain ⟨b₁, b₂, σ, hab, hb₁, hb₂⟩ := exists_semilinear_of_mem (hAN ha) hts
        by_cases hσ : σ = RingEquiv.refl K
        · exfalso
          apply haS
          refine mem_pairSL_of_two_pow (hAN ha) ?_ (j := 1) (by rw [pow_one]; exact hA2 a ha)
          rw [hab]
          exact mem_linPair_of (hab ▸ hAN ha) (hσ ▸ hb₁)
        · have hbb : b₁ * b₁ = 1 ∧ b₂ * b₂ = 1 := by
            have h2 := ha2
            rw [hab, pairAut_mul] at h2
            exact pairAut_injective (h2.trans pairAut_one.symm)
          have h1 := card_fix_sq_of_semilinear (by norm_num : 1 ≤ 2) hK' hb₁ hσ
            (by rw [sq]; exact hbb.1)
          have h2 := card_fix_sq_of_semilinear (by norm_num : 1 ≤ 2) hK' hb₂ hσ
            (by rw [sq]; exact hbb.2)
          rw [hK] at h1 h2
          have e1 : Nat.card {v : StdMod (Fin 3) K // b₁ v = v} ≤ 8 := by
            by_contra h
            push Not at h
            nlinarith
          have e2 : Nat.card {v : StdMod (Fin 3) K // b₂ v = v} ≤ 8 := by
            by_contra h
            push Not at h
            nlinarith
          have h3 := card_fix_pairAut_le b₁ b₂ (Subgroup.zpowers a)
            (by rw [← hab]; exact Subgroup.mem_zpowers a)
          calc Nat.card (fixV (Subgroup.zpowers a))
              ≤ Nat.card {v : StdMod (Fin 3) K // b₁ v = v} *
                  Nat.card {w : StdMod (Fin 3) K // b₂ w = w} := h3
            _ ≤ 8 * 8 := Nat.mul_le_mul e1 e2
            _ = 64 := by norm_num
      ·
        have hV₂ := SL3One.map_V₁_eq_V₂ (hAN ha) hts
        have hinj : Function.Injective
            (fun x : ↥(fixV (Subgroup.zpowers a)) => ((x : PairMod K)).2) := by
          intro x y hxy
          have hx := H.mem_fixV_zpowers_iff.mp x.2
          have hy := H.mem_fixV_zpowers_iff.mp y.2
          set z : PairMod K := (x : PairMod K) * (y : PairMod K)⁻¹ with hzdef
          have hz : a z = z := by rw [hzdef, map_mul, map_inv, hx, hy]
          have hz1 : z ∈ V₁ K := by
            rw [mem_V₁, hzdef, Prod.snd_mul, Prod.snd_inv]
            exact mul_inv_eq_one.mpr hxy
          have hz2 : z ∈ V₂ K := by
            have : a z ∈ (V₁ K).map a.toMonoidHom := ⟨z, hz1, rfl⟩
            rw [hV₂, hz] at this
            exact this
          have hz' : z = 1 := by
            have : z ∈ V₁ K ⊓ V₂ K := ⟨hz1, hz2⟩
            rwa [V₁_inf_V₂, Subgroup.mem_bot] at this
          apply Subtype.ext
          exact mul_inv_eq_one.mp hz'
        calc Nat.card ↥(fixV (Subgroup.zpowers a)) ≤ Nat.card (StdMod (Fin 3) K) :=
              Nat.card_le_card_of_injective _ hinj
          _ = Nat.card K ^ 3 := by rw [card_stdMod, Fintype.card_fin]
          _ = 64 := by rw [hK]; norm_num
    have := hfix a ha
    have : 4096 ≤ 2 * 64 * D.index :=
      this.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc64))
    omega
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    push Not at h
    exact hA1 (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (h a ha))
  have hA8 : 8 ≤ Nat.card A := by
    have h256 := card_fixV_le_of_involution (by norm_num : 1 ≤ 2) hK' (hAN ha₀)
      (by rw [← sq]; exact hA2 a₀ ha₀) ha₀1
    rw [hK] at h256
    have := hfix a₀ ha₀
    have : 4096 ≤ 2 * 4 ^ 4 * D.index :=
      this.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h256))
    omega
  set E : Subgroup (GL (Fin 3) K) := A.comap pairHom with hEdef
  have hEA : E.map pairHom = A := Subgroup.map_comap_eq_self fun a ha => by
    obtain ⟨γ, -, hγ⟩ := hASL a ha
    exact ⟨γ, hγ⟩
  have hEcard : Nat.card E = Nat.card A := by
    rw [← hEA, Subgroup.card_map_of_injective pairHom_injective]
  have hEsq : ∀ g ∈ E, g * g = 1 := fun g hg => pairHom_injective (by
    rw [map_mul, map_one, ← sq]
    exact hA2 _ hg)
  have hEcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh => pairHom_injective (by
    rw [map_mul, map_mul]
    exact hAc _ hg _ hh)
  have hE4 : Nat.card K < Nat.card E := by rw [hEcard, hK]; omega
  have hι : 4 < Nat.card E := by rw [hEcard]; omega
  have ha₁ := sq_eq_one_pairMod a₁
  have hfin : ∀ (τ : D → (Fin 3 → K) × (Fin 3 → K)), Function.Injective τ →
      Nat.card D * Nat.card E < Nat.card K ^ 6 → False := by
    intro τ _ hlt
    rw [hEcard, hK] at hlt
    have : Nat.card D * D.index ≤ Nat.card D * Nat.card A := Nat.mul_le_mul_left _ hD
    norm_num at hlt
    omega
  rcases center_or_axis E hEsq hEcomm hE4 with ⟨c, hc, hall⟩ | ⟨ψ, hψ, hall⟩
  ·
    have hall' : ∀ g : E, ∃ φ : Fin 3 → K, φ ⬝ᵥ c = 0 ∧
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec c φ :=
      fun g => hall g g.2
    choose φ hφc hφ using hall'
    have hφi : Function.Injective φ := by
      intro g h hgh
      apply Subtype.ext
      apply Units.ext
      rw [hφ g, hφ h, hgh]
    let τ : D → (Fin 3 → K) × (Fin 3 → K) := fun d =>
      (Multiplicative.toAdd (d : PairMod K).1, Multiplicative.toAdd (d : PairMod K).2)
    have hτ : Function.Injective τ := by
      intro d d' h
      simp only [τ, Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h.1)
        (Multiplicative.toAdd.injective h.2))
    refine hfin τ hτ (card_mul_card_lt hK hc hφi (fun g => by rw [dotProduct_comm]; exact hφc g)
      hι hτ (Multiplicative.toAdd a₁.1, Multiplicative.toAdd a₁.2) fun d g => ?_)
    have hcomm := toAdd_pairHom_comm (hEsq g g.2) (hφ g) (d : PairMod K)
    rcases eq_one_or_eq_of_mem_zpowers ha₁ (hDA d d.2 (pairHom g) g.2) with h | h
    · left
      rw [← hcomm, h]
      rfl
    · right
      rw [← hcomm, h]
  ·
    have hall' : ∀ g : E, ∃ w : Fin 3 → K, ψ ⬝ᵥ w = 0 ∧
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ :=
      fun g => hall g g.2
    choose w hwψ hw using hall'
    have hwi : Function.Injective w := by
      intro g h hgh
      apply Subtype.ext
      apply Units.ext
      rw [hw g, hw h, hgh]
    let τ : D → (Fin 3 → K) × (Fin 3 → K) := fun d =>
      (Multiplicative.toAdd (d : PairMod K).2, Multiplicative.toAdd (d : PairMod K).1)
    have hτ : Function.Injective τ := by
      intro d d' h
      simp only [τ, Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h.2)
        (Multiplicative.toAdd.injective h.1))
    refine hfin τ hτ (card_mul_card_lt hK hψ hwi hwψ hι hτ
      (Multiplicative.toAdd a₁.2, Multiplicative.toAdd a₁.1) fun d g => ?_)
    have hcomm := toAdd_pairHom_comm (hEsq g g.2) (hw g) (d : PairMod K)
    have hswap : ((w g ⬝ᵥ (τ d).1) • ψ, (ψ ⬝ᵥ (τ d).2) • w g) =
        (Multiplicative.toAdd (pairHom (g : GL (Fin 3) K) d * (d : PairMod K)⁻¹).2,
          Multiplicative.toAdd (pairHom (g : GL (Fin 3) K) d * (d : PairMod K)⁻¹).1) := by
      have h1 := congrArg Prod.fst hcomm
      have h2 := congrArg Prod.snd hcomm
      simp only at h1 h2
      rw [h1, h2]
    rcases eq_one_or_eq_of_mem_zpowers ha₁ (hDA d d.2 (pairHom g) g.2) with h | h
    · left
      rw [hswap, h]
      rfl
    · right
      rw [hswap, h]

end Model

theorem sl34_quad {V : Type} [CommGroup V] [Finite V] {Q : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL Q V₁ ⊥ 3 2) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (Q : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod Q V₁ (V₁.map φ.toMonoidHom)) {A : Subgroup (MulAut V)}
    (hAN : A ≤ Subgroup.normalizer (Q : Set (MulAut V))) (hA : IsElemAbelian2 A)
    {D : Subgroup V} (hD : D.index ≤ Nat.card A) (a₁ : V)
    (hDA : ∀ d ∈ D, ∀ a ∈ A, a d * d⁻¹ ∈ Subgroup.zpowers a₁) : A = ⊥ := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num : 1 ≤ 2) hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have h2 : A.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (Q : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((Q.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq Q (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hAN
  have hA' := sl34Quad_model (by rw [hK]; norm_num) h2 ((isElemAbelian2_map_congrHom e).mpr hA)
    (D := D.map e.toMonoidHom)
    (by
      rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective, card_map_congrHom]
      exact hD) (e a₁) (by
      rintro _ ⟨d, hd, rfl⟩ _ ⟨a, ha, rfl⟩
      have h1 : (congrHom e a) (e d) * (e d)⁻¹ = e (a d * d⁻¹) := by
        rw [congrHom_apply, MulEquiv.symm_apply_apply, map_mul, map_inv]
      refine (show (congrHom e a) (e d) * (e d)⁻¹ ∈ Subgroup.zpowers (e a₁) from ?_)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hDA d hd a ha)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [h1, ← map_zpow, hk]⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e)).mp hA'

end CFSG.Quasithin.H13.A6.A6S20
