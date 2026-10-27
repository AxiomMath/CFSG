module

public import CFSG.RankThree.GF2n.L34TwoLocal
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.GF2n.L34

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n

section ElemAbelian

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_map_of_le {E Q : Subgroup G} (hEQ : E ≤ Q)
    (hQ : Assembly.IsElemAbelian 2 Q) (f : G →* H) : Assembly.IsElemAbelian 2 (E.map f) := by
  obtain ⟨hQc, hQ2⟩ := hQ
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have h := congrArg Subtype.val (hQc.is_comm.comm ⟨a', hEQ ha'⟩ ⟨b', hEQ hb'⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg f h
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hQ2 x' (hEQ hx'), map_one]

theorem isElemAbelian_of_map {E : Subgroup G} {f : G →* H} (hf : Function.Injective f)
    (hE : Assembly.IsElemAbelian 2 (E.map f)) : Assembly.IsElemAbelian 2 E := by
  obtain ⟨hc, h2⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have h := congrArg Subtype.val (hc.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f a.2⟩
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h
  · rw [map_pow, map_one]
    exact h2 _ (Subgroup.mem_map_of_mem f hx)

end ElemAbelian

section Quotient

variable {Γ : Type} [Group Γ] {Z : Subgroup Γ} [Z.Normal]

omit [Z.Normal] in
theorem inf_eq_bot_of_twoFree (hZ2 : ∀ z ∈ Z, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    {X : Subgroup Γ} (hX : IsPGroup 2 X) : X ⊓ Z = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxX, hxZ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  exact Subgroup.mem_bot.mpr (hZ2 x hxZ k (by simpa using congrArg Subtype.val hk))

omit [Z.Normal] in
theorem normalizer_le_normalizer_of_forall {T' P : Subgroup Γ} (hP2 : IsPGroup 2 P)
    (hPT : P ≤ T') (hall : ∀ x ∈ T', (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P) :
    Subgroup.normalizer (T' : Set Γ) ≤ Subgroup.normalizer (P : Set Γ) := by
  have key : ∀ g ∈ Subgroup.normalizer (T' : Set Γ), ∀ h ∈ P, g * h * g⁻¹ ∈ P := by
    intro g hg h hh
    obtain ⟨k, hk⟩ := hP2 ⟨h, hh⟩
    have hk' : h ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine hall _ ((Subgroup.mem_normalizer_iff.mp hg h).mp (hPT hh)) ⟨k, ?_⟩
    rw [conj_pow, hk', mul_one, mul_inv_cancel]
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

variable [Finite Γ] (hZc : Z ≤ Subgroup.center Γ)
  (hZ2 : ∀ z ∈ Z, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
include hZc hZ2

theorem exists_twoPart {T : Subgroup (Γ ⧸ Z)} (hT2 : IsPGroup 2 T) :
    ∃ P : Subgroup Γ, P ≤ T.comap (QuotientGroup.mk' Z) ∧ IsPGroup 2 P ∧
      P.map (QuotientGroup.mk' Z) = T ∧
      ∀ x ∈ T.comap (QuotientGroup.mk' Z), (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : T.comap (QuotientGroup.mk' Z) →* T := (QuotientGroup.mk' Z).subgroupComap T
  have hf : Function.Surjective f :=
    MonoidHom.subgroupComap_surjective _ T (QuotientGroup.mk'_surjective Z)
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 (T.comap (QuotientGroup.mk' Z))) := inferInstance
  have hQ₀ : (Q₀ : Subgroup (T.comap (QuotientGroup.mk' Z))).map f = ⊤ :=
    ((Q₀.mapSurjective hf).3 (Q := ⊤) (hT2.of_equiv Subgroup.topEquiv.symm) le_top).symm
  set P := (Q₀ : Subgroup (T.comap (QuotientGroup.mk' Z))).map
    (T.comap (QuotientGroup.mk' Z)).subtype with hP
  have hPT : P ≤ T.comap (QuotientGroup.mk' Z) := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 P := Q₀.2.map _
  have hPmap : P.map (QuotientGroup.mk' Z) = T := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact hPT
    · intro t ht
      have : (⟨t, ht⟩ : T) ∈ (Q₀ : Subgroup (T.comap (QuotientGroup.mk' Z))).map f :=
        hQ₀ ▸ Subgroup.mem_top _
      obtain ⟨q, hq, hqt⟩ := Subgroup.mem_map.mp this
      exact Subgroup.mem_map.mpr
        ⟨(q : Γ), Subgroup.mem_map_of_mem _ hq, congrArg Subtype.val hqt⟩
  refine ⟨P, hPT, hP2, hPmap, fun x hx ⟨k, hk⟩ => ?_⟩
  have hxT : QuotientGroup.mk' Z x ∈ P.map (QuotientGroup.mk' Z) := hPmap ▸ hx
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxT
  have hz : p⁻¹ * x ∈ Z := QuotientGroup.eq.mp hpx
  have hxpz : x = p * (p⁻¹ * x) := by group
  have hcomm : Commute p (p⁻¹ * x) := Subgroup.mem_center_iff.mp (hZc hz) p
  have h1 : p ^ 2 ^ k * (p⁻¹ * x) ^ 2 ^ k = 1 := by rw [← hcomm.mul_pow, ← hxpz, hk]
  have h2 : (p⁻¹ * x) ^ 2 ^ k ∈ P := by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact P.inv_mem (P.pow_mem hp _)
  have h3 : (p⁻¹ * x) ^ 2 ^ k = 1 := by
    have : (p⁻¹ * x) ^ 2 ^ k ∈ P ⊓ Z := Subgroup.mem_inf.mpr ⟨h2, Z.pow_mem hz _⟩
    rw [inf_eq_bot_of_twoFree hZ2 hP2] at this
    exact Subgroup.mem_bot.mp this
  rw [hxpz, hZ2 _ hz k h3, mul_one]
  exact hp

theorem isElemAbelian_of_le_of_isMaximalTwoLocal_quotient
    (hΓ : ∀ M : Subgroup Γ, IsMaximalTwoLocal M →
      Assembly.IsElemAbelian 2 (inSubgroup (pCore 2) M))
    {M N : Subgroup (Γ ⧸ Z)} (hM : IsMaximalTwoLocal M) (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set (Γ ⧸ Z))) (hN2 : IsPGroup 2 N) :
    Assembly.IsElemAbelian 2 N := by
  have hs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  obtain ⟨R, hR1, hR2, hMR⟩ := hM.1
  obtain ⟨PR, hPRle, hPR2, hPRmap, hPRall⟩ := exists_twoPart hZc hZ2 hR2
  have hM'eq : M.comap (QuotientGroup.mk' Z) = Subgroup.normalizer (PR : Set Γ) := by
    apply le_antisymm
    · rw [hMR, Subgroup.comap_normalizer_eq_of_surjective _ hs]
      exact normalizer_le_normalizer_of_forall hPR2 hPRle hPRall
    · intro g hg
      rw [Subgroup.mem_comap, hMR, ← hPRmap]
      exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hg)
  have hPR1 : PR ≠ ⊥ := by
    rintro rfl
    exact hR1 (by rw [← hPRmap, Subgroup.map_bot])
  have hM'max : IsMaximalTwoLocal (M.comap (QuotientGroup.mk' Z)) := by
    refine ⟨⟨PR, hPR1, hPR2, hM'eq⟩, fun H hlt hH => ?_⟩
    obtain ⟨X, hX1, hX2, hHX⟩ := hH
    have hXmap1 : X.map (QuotientGroup.mk' Z) ≠ ⊥ := by
      intro h
      apply hX1
      rw [eq_bot_iff, ← inf_eq_bot_of_twoFree hZ2 hX2]
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      have h1 : QuotientGroup.mk' Z x ∈ X.map (QuotientGroup.mk' Z) :=
        Subgroup.mem_map_of_mem _ hx
      rw [h, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff x).mp h1
    have hHle : ∀ h ∈ H, QuotientGroup.mk' Z h ∈
        Subgroup.normalizer ((X.map (QuotientGroup.mk' Z) : Subgroup (Γ ⧸ Z)) : Set (Γ ⧸ Z)) := by
      intro h hh
      rw [hHX] at hh
      exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hh)
    have hMle : M ≤
        Subgroup.normalizer ((X.map (QuotientGroup.mk' Z) : Subgroup (Γ ⧸ Z)) : Set (Γ ⧸ Z)) := by
      intro m hm
      obtain ⟨g, rfl⟩ := hs m
      exact hHle g (hlt.le hm)
    have hne : M ≠
        Subgroup.normalizer ((X.map (QuotientGroup.mk' Z) : Subgroup (Γ ⧸ Z)) : Set (Γ ⧸ Z)) := by
      intro heq
      refine hlt.not_ge fun h hh => ?_
      rw [Subgroup.mem_comap, heq]
      exact hHle h hh
    exact hM.2 _ (lt_of_le_of_ne hMle hne) ⟨_, hXmap1, hX2.map _, rfl⟩
  obtain ⟨PN, hPNle, hPN2, hPNmap, hPNall⟩ := exists_twoPart hZc hZ2 hN2
  have hPNM : PN ≤ M.comap (QuotientGroup.mk' Z) := hPNle.trans (Subgroup.comap_mono hNM)
  have hMPN : M.comap (QuotientGroup.mk' Z) ≤ Subgroup.normalizer (PN : Set Γ) := by
    refine le_trans ?_ (normalizer_le_normalizer_of_forall hPN2 hPNle hPNall)
    rw [← Subgroup.comap_normalizer_eq_of_surjective _ hs]
    exact Subgroup.comap_mono hMN
  rw [← hPNmap]
  exact isElemAbelian_map_of_le (Tim78.le_inSubgroup_pCore hPNM hMPN hPN2) (hΓ _ hM'max) _

end Quotient

section SL3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem scalars_le_center :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) ≤ Subgroup.center (StatedSL 3 K) := by
  intro z hz
  have hz' : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Subgroup.mem_subgroupOf.mp hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hz' g)

omit [Finite K] in
theorem scalars_twoFree :
    ∀ z ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K), ∀ k : ℕ, z ^ 2 ^ k = 1 →
      z = 1 := by
  intro z hz k hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hz :
    (z : GL (Fin 3) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [map_pow, hc]
    exact this
  have h2 : (c : K) ^ 2 ^ k = 1 := by
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_apply_eq] at this
    exact this
  have h3 : ((c : K) - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow, h2, one_pow, sub_self]
  have hc1 : c = 1 :=
    Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h3))
  apply Subtype.ext
  rw [← hc, hc1, map_one, Subgroup.coe_one]

theorem isElemAbelian_of_le_of_isMaximalTwoLocal_statedProj
    {M N : Subgroup (StatedProj (StatedSL 3 K))} (hM : IsMaximalTwoLocal M) (hNM : N ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set (StatedProj (StatedSL 3 K)))) (hN2 : IsPGroup 2 N) :
    Assembly.IsElemAbelian 2 N :=
  isElemAbelian_of_le_of_isMaximalTwoLocal_quotient scalars_le_center scalars_twoFree
    (fun _ hM' => isElemAbelian_pCore_of_isMaximalTwoLocal hM') hM hNM hMN hN2

end SL3

theorem isElemAbelian_of_le_of_isMaximalTwoLocal_L3 {G : Type} [Group G] {f : ℕ}
    (hG : StatedClassicalModel G .PSL 3 2 f) {M N : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N) :
    Assembly.IsElemAbelian 2 N := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  refine isElemAbelian_of_map (f := e.toMonoidHom) e.injective ?_
  refine isElemAbelian_of_le_of_isMaximalTwoLocal_statedProj
    (PartTwo.Late.isMaximalTwoLocal_map hM e) (Subgroup.map_mono hNM) ?_ (hN2.map _)
  exact (Subgroup.map_mono hMN).trans (Subgroup.le_normalizer_map _)

end CFSG.RankThree.GF2n.L34
