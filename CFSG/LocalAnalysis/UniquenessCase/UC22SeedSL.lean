module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix (SpecialLinearGroup)
open CFSG.QuasithinUnique.Setup.Campbell CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization

section SL2Aux

variable {k : Type} [Field k]

theorem sl2_card_eq_two_pow [Finite k] [CharP k 2] : ∃ n : ℕ, 1 ≤ n ∧ Nat.card k = 2 ^ n := by
  classical
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem sl2_exists_point_mem_rootGrp_of_mul_self_eq_one [CharP k 2] {y : SpecialLinearGroup (Fin 2) k}
    (hy1 : y ≠ 1) (hy2 : y * y = 1) : ∃ p : ℙ k (Fin 2 → k), y ∈ rootGrp p := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin 2 → k, y • w₀ ≠ w₀ := by
    by_contra hall
    push Not at hall
    apply hy1
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.SpecialLinearGroup.smul_def] at this
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  have hv0 : y • w₀ - w₀ ≠ 0 := sub_ne_zero.mpr hw₀
  have hfix : y • (y • w₀ - w₀) = y • w₀ - w₀ := by
    rw [smul_sub, ← mul_smul, hy2, one_smul]
    ext i
    simp only [Pi.sub_apply]
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  exact ⟨_, mem_rootGrp_mk_of_smul_eq hv0 hfix⟩

@[expose] def sl2Diag (a : k) (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

theorem coe_sl2Diag (a : k) (ha : a ≠ 0) :
    ((sl2Diag a ha : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, a⁻¹] :=
  rfl

theorem sl2Diag_mul_unipotent (a : k) (ha : a ≠ 0) (t : k) :
    sl2Diag a ha * unipotent t = unipotent (a * a * t) * sl2Diag a ha := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Diag, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, ha] <;> field_simp

theorem rootGrp_smul_le_of_normal (N : Subgroup (SpecialLinearGroup (Fin 2) k)) [N.Normal]
    {p : ℙ k (Fin 2 → k)} (g : SpecialLinearGroup (Fin 2) k) (h : rootGrp p ≤ N) :
    rootGrp (g • p) ≤ N := by
  intro x hx
  rw [mem_rootGrp_smul_iff] at hx
  have := Subgroup.Normal.conj_mem ‹N.Normal› _ (h hx) g
  simpa [mul_assoc] using this

theorem rootGrp_pt0_le_of_unipotent_mem [Finite k] [CharP k 2] (N : Subgroup (SpecialLinearGroup (Fin 2) k))
    [N.Normal] {t : k} (ht : t ≠ 0) (hN : unipotent t ∈ N) :
    rootGrp (pt0 : ℙ k (Fin 2 → k)) ≤ N := by
  rw [rootGrp_pt0]
  rintro _ ⟨s, rfl⟩
  show unipotent s.toAdd ∈ N
  by_cases hs : s.toAdd = 0
  · rw [hs, unipotent_zero]
    exact N.one_mem
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) (s.toAdd / t)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact div_ne_zero hs ht (by simpa using ha)
    have h2 : a * a * t = s.toAdd := by rw [← ha]; field_simp
    have hconj := Subgroup.Normal.conj_mem ‹N.Normal› _ hN (sl2Diag a ha0)
    rwa [sl2Diag_mul_unipotent, mul_inv_cancel_right, h2] at hconj

theorem sl2_normal_eq_top_of_mem_rootGrp [Finite k] [CharP k 2] (N : Subgroup (SpecialLinearGroup (Fin 2) k))
    [N.Normal] {p : ℙ k (Fin 2 → k)} {y : SpecialLinearGroup (Fin 2) k} (hyN : y ∈ N) (hyp : y ∈ rootGrp p)
    (hy1 : y ≠ 1) : N = ⊤ := by
  obtain ⟨g, rfl⟩ := exists_smul_pt0 p
  have hy' : g⁻¹ * y * g ∈ rootGrp (pt0 : ℙ k (Fin 2 → k)) := mem_rootGrp_smul_iff.mp hyp
  have hyN' : g⁻¹ * y * g ∈ N := by
    simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ hyN g⁻¹
  rw [rootGrp_pt0] at hy'
  obtain ⟨t, ht⟩ := hy'
  have hut : unipotent t.toAdd = g⁻¹ * y * g := ht
  have ht0 : t.toAdd ≠ 0 := by
    intro h0
    apply hy1
    rw [h0, unipotent_zero] at hut
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [← hut]; group
  have h0 : rootGrp (pt0 : ℙ k (Fin 2 → k)) ≤ N :=
    rootGrp_pt0_le_of_unipotent_mem N ht0 (hut ▸ hyN')
  obtain ⟨g₁, hg₁⟩ := exists_smul_pt0 (pt1 : ℙ k (Fin 2 → k))
  have h1 : rootGrp (pt1 : ℙ k (Fin 2 → k)) ≤ N := hg₁ ▸ rootGrp_smul_le_of_normal N g₁ h0
  rw [eq_top_iff, ← rootGrp_sup_rootGrp_pt0_pt1]
  exact sup_le h0 h1

theorem sl2_eq_one_of_forall_smul_point_eq [CharP k 2] {n : SpecialLinearGroup (Fin 2) k}
    (h : ∀ q : ℙ k (Fin 2 → k), n • q = q) : n = 1 := by
  have key : ∀ v : Fin 2 → k, ∀ hv : v ≠ 0, ∃ c : k, c • v = n • v := by
    intro v hv
    have := h (Projectivization.mk k v hv)
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at this
    exact this
  obtain ⟨c0, hc0⟩ := key (Pi.single 0 1) (by simp [Pi.single_eq_zero_iff])
  obtain ⟨c1, hc1⟩ := key (Pi.single 1 1) (by simp [Pi.single_eq_zero_iff])
  obtain ⟨c2, hc2⟩ := key ![1, 1] (by
    intro h0
    have := congrFun h0 0
    simp at this)
  have h10 : (n : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    have := congrFun hc0 1
    simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this.symm
  have h01 : (n : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    have := congrFun hc1 0
    simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this.symm
  have h00 : (n : Matrix (Fin 2) (Fin 2) k) 0 0 = (n : Matrix (Fin 2) (Fin 2) k) 1 1 := by
    have e0 := congrFun hc2 0
    have e1 := congrFun hc2 1
    simp [Matrix.SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    rw [h01] at e0
    rw [h10] at e1
    linear_combination e1 - e0
  have hdet : (n : Matrix (Fin 2) (Fin 2) k) 0 0 * (n : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    have := n.2
    rw [Matrix.det_fin_two, h01, h10] at this
    rw [h00] at this ⊢
    linear_combination this
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  have ha : (n : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    have hsq : ((n : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (1 - (n : Matrix (Fin 2) (Fin 2) k) 0 0) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, ← h00, h01, h10, Matrix.one_apply]

theorem sl2_le_normalizer_of_rootGrp_le [Finite k] {p : ℙ k (Fin 2 → k)}
    {Y : Subgroup (SpecialLinearGroup (Fin 2) k)} (hpY : rootGrp p ≤ Y) (hY : Y ≠ ⊤) :
    Y ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) := by
  intro y hy
  rw [mem_normalizer_rootGrp_iff]
  by_contra hne
  apply hY
  have h1 : rootGrp (y • p) ≤ Y := by
    rw [rootGrp_smul_eq_map]
    rintro _ ⟨u, hu, rfl⟩
    exact Y.mul_mem (Y.mul_mem hy (hpY hu)) (Y.inv_mem hy)
  have h2 : rootGrp p ⊔ rootGrp (y • p) = ⊤ := rootGrp_sup_rootGrp (Ne.symm hne)
  exact top_le_iff.mp (h2 ▸ sup_le hpY h1)

theorem sl2_eq_bot_of_normal_le_normalizer_rootGrp [Finite k] [CharP k 2] {p : ℙ k (Fin 2 → k)}
    (N : Subgroup (SpecialLinearGroup (Fin 2) k)) [N.Normal]
    (h : N ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) k))) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  refine sl2_eq_one_of_forall_smul_point_eq fun q => ?_
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) k) p q
  have hg : g⁻¹ * n * g ∈ N := by simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ hn g⁻¹
  have := mem_normalizer_rootGrp_iff.mp (h hg)
  rwa [mul_smul, mul_smul, inv_smul_eq_iff] at this

theorem sl2_not_commutative_aux : ¬ ∀ a b : SpecialLinearGroup (Fin 2) k, a * b = b * a := by
  intro h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) k => (A : Matrix (Fin 2) (Fin 2) k) 0 0)
    (h (unipotent 1) (lowerElt 1))
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [unipotent, lowerElt, Matrix.mul_apply, Fin.sum_univ_two] at h1

end SL2Aux

section SL2

variable {k : Type} [Field k] [Finite k] [CharP k 2] {Q : Type} [Group Q]

theorem sl2_eq_top_of_map_eq_top (e : Q ≃* SpecialLinearGroup (Fin 2) k) {Y : Subgroup Q}
    (h : Y.map e.toMonoidHom = ⊤) : Y = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨g', hg', hgg'⟩ : e g ∈ Y.map e.toMonoidHom := h ▸ Subgroup.mem_top _
  exact e.injective hgg' ▸ hg'

theorem sl2_exists_rootGrp_eq_map_sylow (e : Q ≃* SpecialLinearGroup (Fin 2) k) (P : Sylow 2 Q) :
    ∃ p : ℙ k (Fin 2 → k), (P : Subgroup Q).map e.toMonoidHom = rootGrp p := by
  have : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨n, hn, hk⟩ := sl2_card_eq_two_pow (k := k)
  have hq1 : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by
    intro hd
    have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h3 : 0 < (2 ^ n) ^ 2 := by positivity
    omega
  have hfac : (2 ^ n * ((2 ^ n) ^ 2 - 1)).factorization 2 = n := by
    have hne1 : 2 ^ n ≠ 0 := by positivity
    have hne2 : (2 ^ n) ^ 2 - 1 ≠ 0 := by
      intro h0
      rw [h0] at hq1
      exact hq1 (dvd_zero 2)
    rw [Nat.factorization_mul hne1 hne2]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hq1]
  have hsyl : Nat.card ((Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P :
      Sylow 2 (SpecialLinearGroup (Fin 2) k)) : Subgroup (SpecialLinearGroup (Fin 2) k)) = Nat.card k := by
    rw [Sylow.card_eq_multiplicity, card_specialLinearGroup_fin_two, hk, hfac]
  rw [← Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P]
  exact exists_point_eq_rootGrp Nat.prime_two hk hsyl

theorem sl2_normal_eq_top_of_involution (e : Q ≃* SpecialLinearGroup (Fin 2) k) (N : Subgroup Q) [N.Normal]
    {x : Q} (hx : x ∈ N) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) : N = ⊤ := by
  have hNn : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map ‹N.Normal› e.toMonoidHom e.surjective
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (by simpa using h))
  have hex2 : e x * e x = 1 := by rw [← map_mul, ← sq, hx2, map_one]
  obtain ⟨p, hp⟩ := sl2_exists_point_mem_rootGrp_of_mul_self_eq_one hex1 hex2
  exact sl2_eq_top_of_map_eq_top e
    (sl2_normal_eq_top_of_mem_rootGrp (N.map e.toMonoidHom) (Subgroup.mem_map_of_mem _ hx) hp hex1)

theorem sl2_le_normalizer_of_sylow_le (e : Q ≃* SpecialLinearGroup (Fin 2) k) (P : Sylow 2 Q)
    {Y : Subgroup Q} (hPY : (P : Subgroup Q) ≤ Y) (hY : Y ≠ ⊤) :
    Y ≤ Subgroup.normalizer ((P : Subgroup Q) : Set Q) := by
  obtain ⟨p, hp⟩ := sl2_exists_rootGrp_eq_map_sylow e P
  have hle : rootGrp p ≤ Y.map e.toMonoidHom := hp ▸ Subgroup.map_mono hPY
  have hne : Y.map e.toMonoidHom ≠ ⊤ := fun h => hY (sl2_eq_top_of_map_eq_top e h)
  have h1 := sl2_le_normalizer_of_rootGrp_le hle hne
  intro y hy
  have hy' := h1 (Subgroup.mem_map_of_mem e.toMonoidHom hy)
  rw [← hp, ← Subgroup.map_equiv_normalizer_eq] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  exact e.injective hzy ▸ hz

theorem sl2_eq_bot_of_normal_le_normalizer (e : Q ≃* SpecialLinearGroup (Fin 2) k) (P : Sylow 2 Q)
    (N : Subgroup Q) [N.Normal] (h : N ≤ Subgroup.normalizer ((P : Subgroup Q) : Set Q)) : N = ⊥ := by
  obtain ⟨p, hp⟩ := sl2_exists_rootGrp_eq_map_sylow e P
  have hNn : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map ‹N.Normal› e.toMonoidHom e.surjective
  have hle : N.map e.toMonoidHom ≤ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) := by
    rw [← hp, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono h
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp
    (sl2_eq_bot_of_normal_le_normalizer_rootGrp (N.map e.toMonoidHom) hle)

theorem sl2_normal_sup_sylow_eq_top (e : Q ≃* SpecialLinearGroup (Fin 2) k) (P : Sylow 2 Q)
    (N : Subgroup Q) [N.Normal] (hN : N ≠ ⊥) : N ⊔ (P : Subgroup Q) = ⊤ := by
  by_contra hne
  have h1 := sl2_le_normalizer_of_sylow_le e P (le_sup_right : (P : Subgroup Q) ≤ N ⊔ P) hne
  exact hN (sl2_eq_bot_of_normal_le_normalizer e P N (le_sup_left.trans h1))

theorem sl2_sq_eq_one_of_pow_two_pow (e : Q ≃* SpecialLinearGroup (Fin 2) k) {x : Q} {a : ℕ}
    (hx : x ^ 2 ^ a = 1) : x ^ 2 = 1 := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← hm]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨p, hp'⟩ := sl2_exists_rootGrp_eq_map_sylow e S
  have hex : e x ∈ rootGrp p := hp' ▸ Subgroup.mem_map_of_mem e.toMonoidHom (hS (Subgroup.mem_zpowers x))
  rw [sq]
  apply e.injective
  rw [map_mul, map_one]
  exact mul_self_eq_one_of_mem_rootGrp hex

theorem sl2_exists_involution (e : Q ≃* SpecialLinearGroup (Fin 2) k) : ∃ x : Q, x ≠ 1 ∧ x ^ 2 = 1 := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_rootGrp (pt0 : ℙ k (Fin 2 → k))
  refine ⟨e.symm u, fun h => hu1 ?_, ?_⟩
  · simpa using congrArg e h
  · rw [sq, ← map_mul, mul_self_eq_one_of_mem_rootGrp hu, map_one]

theorem sl2_sylow_ne_bot (e : Q ≃* SpecialLinearGroup (Fin 2) k) (P : Sylow 2 Q) :
    (P : Subgroup Q) ≠ ⊥ := by
  obtain ⟨p, hp⟩ := sl2_exists_rootGrp_eq_map_sylow e P
  intro hbot
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_rootGrp p
  rw [← hp, hbot, Subgroup.map_bot] at hu
  exact hu1 (Subgroup.mem_bot.mp hu)

theorem sl2_not_commutative (e : Q ≃* SpecialLinearGroup (Fin 2) k) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  refine sl2_not_commutative_aux (k := k) fun a b => ?_
  simpa using congrArg e (hcomm (e.symm a) (e.symm b))

theorem sl2_normal_isPGroup_eq_bot (e : Q ≃* SpecialLinearGroup (Fin 2) k) (N : Subgroup Q) [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  by_contra hne
  obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
    obtain ⟨⟨x, hxN⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hxN, fun h => hx (Subtype.ext h)⟩
  have hsq : ∀ y ∈ N, y ^ 2 = 1 := fun y hy => by
    obtain ⟨m, hm⟩ := hN ⟨y, hy⟩
    exact sl2_sq_eq_one_of_pow_two_pow e (a := m) (by simpa using congrArg Subtype.val hm)
  have htop := sl2_normal_eq_top_of_involution e N hxN hx1 (hsq x hxN)
  obtain ⟨a, b, hab⟩ := sl2_not_commutative e
  have hall : ∀ y : Q, y * y = 1 := fun y => by
    rw [← sq]
    exact hsq y (htop ▸ Subgroup.mem_top y)
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hall a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hall b)
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hall (a * b))
  rw [mul_inv_rev, ha, hb] at hab'
  exact hab hab'.symm

end SL2

end CFSG.LocalAnalysis.UniquenessCase.UC22
