module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSURankOne

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Assembly CFSG.Blueprint

namespace InnerDiagSU

section Generation

theorem eq_top_of_rankOne_le {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {hA : TauCeti.IsFiniteType A} {D : Set (Fin r)} {K : Type*} [Group K]
    {X : (Fin r → ℤ) → Subgroup K} {w : Fin r → K} {H : Fin r → Subgroup K}
    (hCT : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix hA).toCoxeterSystem
      (weylAction hA) (roots hA D) X w H)
    (E : Subgroup K) (hE : ∀ k, CFSG.LieType.CurtisTits.rankOne X k ≤ E) : E = ⊤ := by
  have hw : ∀ i, w i ∈ E := fun i => hE i (hCT.n_mem i)
  have key : ∀ (ω : List (Fin r)) (v₀ : Fin r → ℤ), v₀ ∈ roots hA D → X v₀ ≤ E →
      X (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd ω) v₀) ≤ E := by
    intro ω v₀ hv₀ hX
    induction ω with
    | nil => simpa using hX
    | cons i ω ih =>
      set δ := weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd ω) v₀ with hδ
      have hδr : δ ∈ roots hA D := weylAction_mem_roots hA _ hv₀
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, ← hδ]
      intro y hy
      have h1 := hCT.conj_mem i _ (weylAction_mem_roots hA _ hδr) y hy
      rw [← weylAction_mul_apply, CoxeterSystem.simple_mul_simple_self, map_one,
        Module.End.one_apply] at h1
      have h2 : y = (w i)⁻¹ * (w i * y * (w i)⁻¹) * w i := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem (hw i)) (ih h1)) (hw i)
  have hroot : ∀ γ ∈ roots hA D, X γ ≤ E := by
    rintro γ (⟨v, j, rfl⟩ | ⟨v, j, hj, rfl⟩)
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective v
      exact key ω _ (Or.inl ⟨1, j, by simp⟩) ((le_sup_left).trans (hE j))
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective v
      rw [← map_nsmul]
      have hmem : 2 • Pi.single j (1 : ℤ) ∈ roots hA D := Or.inr ⟨1, j, hj, by simp⟩
      refine key ω _ hmem ((hCT.le_rankOne j _ hmem fun k hk => ?_).trans (hE j))
      simp [hk]
  rw [eq_top_iff, ← hCT.iSup_eq_top]
  exact iSup₂_le hroot

end Generation

section Ratio

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem conjSU_diagJ_eq_of_ratio (t d : Fin n → F) (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1)
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (x : SU σ n)
    (h : ∀ a b, a ≠ b → mat σ n x a b ≠ 0 → t a * (t b)⁻¹ = d a * (d b)⁻¹) :
    conjSU (diagJ t ht) (isJUnitary_diagJ t ht) x = conjSU (diagJ d hd) (isJUnitary_diagJ d hd) x := by
  apply mat_injective
  ext a b
  rw [mat_conjSU_diagJ, mat_conjSU_diagJ]
  by_cases hab : a = b
  · rw [hab]
    field_simp [ne_zero_of_unitary ht b, ne_zero_of_unitary hd b]
  · by_cases hx : mat σ n x a b = 0
    · rw [hx, mul_zero, zero_mul, mul_zero, zero_mul]
    · calc t a * mat σ n x a b * (t b)⁻¹ = (t a * (t b)⁻¹) * mat σ n x a b := by ring
        _ = (d a * (d b)⁻¹) * mat σ n x a b := by rw [h a b hab hx]
        _ = d a * mat σ n x a b * (d b)⁻¹ := by ring

theorem ratio_rev {t d : Fin n → F} (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1)
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) {a b : Fin n}
    (h : t a * (t b)⁻¹ = d a * (d b)⁻¹) :
    t (Fin.rev b) * (t (Fin.rev a))⁻¹ = d (Fin.rev b) * (d (Fin.rev a))⁻¹ := by
  have e1 : ∀ (u : Fin n → F), (∀ s, σ (u s) * u (Fin.rev s) = 1) →
      u (Fin.rev b) * (u (Fin.rev a))⁻¹ = σ (u a * (u b)⁻¹) := by
    intro u hu
    rw [eq_inv_of_mul_eq_one_right (hu b), eq_inv_of_mul_eq_one_right (hu a), map_mul, map_inv₀,
      inv_inv, mul_comm]
  rw [e1 t ht, e1 d hd, h]

end Ratio

section Construction

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] noncomputable def extU (n : ℕ) (lam : Fin (n / 2) → F) (μ : F) : Fin n → F := fun a =>
  if h : a.val < n / 2 then lam ⟨a.val, h⟩
  else if h' : n - 1 - a.val < n / 2 then (σ (lam ⟨n - 1 - a.val, h'⟩))⁻¹ else μ

variable {σ}

theorem extU_lowIdx (lam : Fin (n / 2) → F) (μ : F) (a : Fin (n / 2)) :
    extU σ n lam μ (lowIdx a) = lam a := by
  have h : (lowIdx (n := n) a).val < n / 2 := a.isLt
  simp only [extU, h, dite_true]
  rfl

theorem extU_rev_lowIdx (lam : Fin (n / 2) → F) (μ : F) (a : Fin (n / 2)) :
    extU σ n lam μ (Fin.rev (lowIdx a)) = (σ (lam a))⁻¹ := by
  have ha := a.isLt
  have h1 : ¬ (Fin.rev (lowIdx (n := n) a)).val < n / 2 := by
    simp only [Fin.val_rev, val_lowIdx]
    omega
  have h2 : n - 1 - (Fin.rev (lowIdx (n := n) a)).val < n / 2 := by
    simp only [Fin.val_rev, val_lowIdx]
    omega
  simp only [extU, h1, h2, dite_false, dite_true]
  congr 3
  ext
  simp only [Fin.val_rev, val_lowIdx]
  omega

theorem extU_of_rev_eq (lam : Fin (n / 2) → F) (μ : F) {s : Fin n} (hs : Fin.rev s = s) :
    extU σ n lam μ s = μ := by
  have h := congrArg Fin.val hs
  simp only [Fin.val_rev] at h
  have h1 : ¬ s.val < n / 2 := by omega
  have h2 : ¬ n - 1 - s.val < n / 2 := by omega
  simp only [extU, h1, h2, dite_false]

theorem extU_unitary (hσ : ∀ c, σ (σ c) = c) {lam : Fin (n / 2) → F} (hlam : ∀ a, lam a ≠ 0)
    {μ : F} (hμ : σ μ * μ = 1) (s : Fin n) :
    σ (extU σ n lam μ s) * extU σ n lam μ (Fin.rev s) = 1 := by
  by_cases hs : Fin.rev s = s
  · rw [hs, extU_of_rev_eq _ _ hs, hμ]
  · obtain ⟨a, rfl | rfl⟩ := exists_lowIdx (Ne.symm hs)
    · rw [extU_lowIdx, extU_rev_lowIdx, mul_inv_cancel₀ ((map_ne_zero σ).mpr (hlam a))]
    · rw [Fin.rev_rev, extU_lowIdx, extU_rev_lowIdx, map_inv₀, hσ, inv_mul_cancel₀ (hlam a)]

@[expose] noncomputable def lowRatio (n : ℕ) (T : Fin (n / 2) → Fin n → F) (i : ℕ) : F :=
  if h : i + 1 < n / 2 then
    T ⟨i, by omega⟩ (lowIdx ⟨i, by omega⟩) * (T ⟨i, by omega⟩ (lowIdx ⟨i + 1, h⟩))⁻¹
  else 1

@[expose] noncomputable def lowPart (n : ℕ) (T : Fin (n / 2) → Fin n → F) (c₀ : F)
    (a : Fin (n / 2)) : F :=
  c₀ * ∏ i ∈ Finset.Ico a.val (n / 2 - 1), lowRatio n T i

theorem lowPart_succ (T : Fin (n / 2) → Fin n → F) (c₀ : F) {a : Fin (n / 2)}
    (ha : a.val + 1 < n / 2) :
    lowPart n T c₀ a = lowRatio n T a.val * lowPart n T c₀ ⟨a.val + 1, ha⟩ := by
  simp only [lowPart]
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : a.val < n / 2 - 1)]
  ring

theorem lowPart_last (T : Fin (n / 2) → Fin n → F) (c₀ : F) {a : Fin (n / 2)}
    (ha : ¬ a.val + 1 < n / 2) : lowPart n T c₀ a = c₀ := by
  have := a.isLt
  simp only [lowPart]
  rw [show a.val = n / 2 - 1 by omega, Finset.Ico_self, Finset.prod_empty, mul_one]

theorem lowPart_ne_zero {T : Fin (n / 2) → Fin n → F} (hT : ∀ k s, T k s ≠ 0) {c₀ : F}
    (hc : c₀ ≠ 0) (a : Fin (n / 2)) : lowPart n T c₀ a ≠ 0 := by
  simp only [lowPart]
  refine mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
  simp only [lowRatio]
  split_ifs
  · exact mul_ne_zero (hT _ _) (inv_ne_zero (hT _ _))
  · exact one_ne_zero

theorem lowPart_ratio {T : Fin (n / 2) → Fin n → F} (hT : ∀ k s, T k s ≠ 0) {c₀ : F}
    (hc : c₀ ≠ 0) {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    T k (lowIdx k) * (T k (lowIdx ⟨k.val + 1, hk⟩))⁻¹ =
      lowPart n T c₀ k * (lowPart n T c₀ ⟨k.val + 1, hk⟩)⁻¹ := by
  rw [lowPart_succ T c₀ hk, mul_assoc, mul_inv_cancel₀ (lowPart_ne_zero hT hc _), mul_one]
  simp only [lowRatio, hk, dite_true]

end Construction

section Positions

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem ratio_of_mem_simple {k : Fin (n / 2)} {t d : Fin n → F}
    (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (hshort : ∀ hk : k.val + 1 < n / 2, t (lowIdx k) * (t (lowIdx ⟨k.val + 1, hk⟩))⁻¹ =
      d (lowIdx k) * (d (lowIdx ⟨k.val + 1, hk⟩))⁻¹)
    (hlast : ¬ k.val + 1 < n / 2 → t (lowIdx k) = d (lowIdx k) ∧
      ∀ s, Fin.rev s = s → t s = d s)
    {z : SU σ n} (hz : z ∈ rootGroup σ hσ n (Pi.single k 1)) (a b : Fin n) (hab : a ≠ b)
    (hzab : mat σ n z a b ≠ 0) : t a * (t b)⁻¹ = d a * (d b)⁻¹ := by
  have hw : weight n a - weight n b ∈ wt2 (toStd n (Pi.single k 1)) :=
    hasWt_of_mem_rootGroup hσ hz a b (by rwa [Matrix.sub_apply, one_apply_ne hab, sub_zero])
  rw [mem_wt2] at hw
  by_cases hk : k.val + 1 < n / 2
  · obtain ⟨h1, h2, h3, h4⟩ := short_facts (n := n) hk
    rcases hw with hw | hw
    · rw [toStd_short hk] at hw
      rcases eq_of_weight_sub_eq_sub h1 h2 h3 h4 hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hshort hk
      · exact ratio_rev ht hd (hshort hk)
    · exfalso
      obtain ⟨-, hwa⟩ := eq_rev_of_weight_sub_eq_two_smul hw (toStd_short_ne_zero hk)
      rw [toStd_short hk] at hwa
      exact weight_ne_weight_sub h1 h2 h3 h4 hwa
  · obtain ⟨hp, hmid⟩ := hlast hk
    have hp' : t (Fin.rev (lowIdx k)) = d (Fin.rev (lowIdx k)) := by
      rw [eq_inv_of_mul_eq_one_right (ht _), eq_inv_of_mul_eq_one_right (hd _), hp]
    by_cases he : Even n
    · rcases hw with hw | hw
      · rw [toStd_last_even hk he] at hw
        obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul (lowIdx_ne_rev k k) hw
        rw [hp, hp']
      · exfalso
        rw [toStd_last_even hk he, smul_smul] at hw
        exact weight_ne_zero (lowIdx_ne_rev k k)
          (eq_zero_of_weight_sub_eq_nsmul hw (by norm_num))
    · have hm := rev_midIdx he
      rcases hw with hw | hw
      · rw [toStd_last_odd hk he] at hw
        rcases eq_of_weight_sub_eq_weight (lowIdx_ne_rev k k) hm hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hp, hmid _ hm]
        · rw [hmid _ hm, hp']
      · rw [toStd_last_odd hk he] at hw
        obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul (lowIdx_ne_rev k k) hw
        rw [hp, hp']

end Positions

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

omit [Finite F] [CharP F 2] in
theorem conjSU_injective {σ : F ≃+* F} (A : GL (Fin n) F) (hA : IsJUnitary σ A) :
    Function.Injective (conjSU A hA) := by
  intro u v h
  have h1 := congrArg (fun w : SU σ n => (w : GL (Fin n) F)) h
  simp only [coe_conjSU] at h1
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))

omit [Finite F] [CharP F 2] in
theorem ker_comp_conjSU_le_center {σ : F ≃+* F} {G : Type*} [Group G] (ψ : SU σ n →* G)
    (hker : ψ.ker ≤ Subgroup.center _) (A : GL (Fin n) F) (hA : IsJUnitary σ A) :
    (ψ.comp (conjSU A hA)).ker ≤ Subgroup.center _ := by
  intro u hu
  have hc : conjSU A hA u ∈ Subgroup.center _ := hker hu
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro v
  apply conjSU_injective A hA
  rw [map_mul, map_mul, hc]

omit [Finite F] [CharP F 2] in
theorem longRootHom_congr {σ : F ≃+* F} {i : Fin n} (hi : i ≠ Fin.rev i) {z z' : traceZero σ}
    (h : (z : F) = z') :
    longRootHom σ hi (Multiplicative.ofAdd z) = longRootHom σ hi (Multiplicative.ofAdd z') := by
  rw [Subtype.ext h]

include hF in
theorem levelWeyl_agree_short (hn : 4 ≤ n) {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)
    {G : Type*} [Group G] (ψ β : SU (unitaryInvolution F 2 f) n →* G)
    (d : Fin n → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1)
    (hker : (ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd))).ker ≤ Subgroup.center _)
    (hpos : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1),
      β z = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z))
    (t : Fin n → F) (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1)
    (hneg : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1),
      β z = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z)) :
    β (levelWeyl (unitaryInvolution_involutive hF) oneTZ k) =
      ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)
        (levelWeyl (unitaryInvolution_involutive hF) oneTZ k)) := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  set γ' := ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  set e := t (lowIdx ⟨k.val + 1, hk⟩) * (t (lowIdx k))⁻¹ * d (lowIdx k) *
    (d (lowIdx ⟨k.val + 1, hk⟩))⁻¹ with he
  have h0t := ne_zero_of_unitary ht
  have h0d := ne_zero_of_unitary hd
  have hY : ∀ c, β (shortY hF hk c) = γ' (shortY hF hk (e * c)) := by
    intro c
    rw [hneg _ (shortY_mem hF hk c)]
    show ψ (conjSU (diagJ t ht) _ (shortY hF hk c)) =
      ψ (conjSU (diagJ d hd) _ (shortY hF hk (e * c)))
    simp only [shortY]
    rw [conjSU_diagJ_rootHom, conjSU_diagJ_rootHom]
    have hv : t (lowIdx ⟨k.val + 1, hk⟩) * c * (t (lowIdx k))⁻¹ =
        d (lowIdx ⟨k.val + 1, hk⟩) * (e * c) * (d (lowIdx k))⁻¹ := by
      rw [he]
      field_simp [h0t (lowIdx k), h0d (lowIdx k), h0d (lowIdx ⟨k.val + 1, hk⟩)]
    rw [hv]
  have hX : ∀ c, β (shortX hF hk c) = γ' (shortX hF hk c) := fun c =>
    hpos _ (shortX_mem hF hk c)
  have he1 : e = 1 := eq_one_of_rankOne_short hF (by omega) hnq hk β γ' hker e hX hY
  have hw : levelWeyl (unitaryInvolution_involutive hF) oneTZ k =
      shortX hF hk 1 * shortY hF hk (-1⁻¹) * shortX hF hk 1 := by
    unfold levelWeyl
    rw [dite_eq_left hk, shortWeyl_def]
    rfl
  rw [hw, map_mul, map_mul, hX, hY, he1, one_mul]
  show _ = γ' _
  rw [map_mul, map_mul]

include hF in
theorem longRootHom_mem_last {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2)
    (z : traceZero (unitaryInvolution F 2 f)) :
    longRootHom _ (lowIdx_ne_rev k k) (Multiplicative.ofAdd z) ∈
        rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1) ∧
      longRootHom _ (rev_ne_rev_rev (lowIdx_ne_rev k k)) (Multiplicative.ofAdd z) ∈
        rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1) := by
  have hσ := unitaryInvolution_involutive hF
  have hp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hp
  by_cases he : Even n
  · exact ⟨longRootHom_mem hσ hp (toStd_last_even hk he).symm _,
      longRootHom_mem hσ hp' (toStd_neg_last_even hk he).symm _⟩
  · have hm := rev_midIdx he
    have hpm : lowIdx k ≠ midIdx n he := fun h => hp (by rw [← h] at hm; exact hm.symm)
    have hpm' : Fin.rev (lowIdx k) ≠ midIdx n he := fun h => hp' (by
      rw [← h] at hm; exact hm.symm)
    have hz : (z : F) + unitaryInvolution F 2 f z + unitaryInvolution F 2 f 0 * 0 = 0 := by
      rw [mul_zero, add_zero]
      exact (mem_traceZero _).mp z.2
    refine ⟨heisenberg_le hσ hp hpm hm (toStd_last_odd hk he).symm ⟨0, z, hz, ?_⟩,
      heisenberg_le hσ hp' hpm' hm (toStd_neg_last_odd hk he).symm ⟨0, z, hz, ?_⟩⟩
    · rw [coe_longRootHom, toAdd_ofAdd, longRootMatrix, heisenbergMatrix]
      simp
    · rw [coe_longRootHom, toAdd_ofAdd, longRootMatrix, heisenbergMatrix]
      simp

include hF in
theorem levelWeyl_agree_last (hn : 4 ≤ n) {k : Fin (n / 2)} (hk : ¬ k.val + 1 < n / 2)
    {G : Type*} [Group G] (ψ β : SU (unitaryInvolution F 2 f) n →* G)
    (d : Fin n → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1)
    (hker : (ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd))).ker ≤ Subgroup.center _)
    (hpos : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1),
      β z = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) z))
    (t : Fin n → F) (ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1)
    (hneg : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1),
      β z = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z)) :
    β (levelWeyl (unitaryInvolution_involutive hF) oneTZ k) =
      ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)
        (levelWeyl (unitaryInvolution_involutive hF) oneTZ k)) := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hp := lowIdx_ne_rev (n := n) k k
  have hp' := rev_ne_rev_rev hp
  set γ' := ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  have h0t := ne_zero_of_unitary ht
  have h0d := ne_zero_of_unitary hd
  have hdi : ∀ s, unitaryInvolution F 2 f ((d s)⁻¹) * (d (Fin.rev s))⁻¹ = 1 := fun s => by
    rw [map_inv₀, ← mul_inv, hd s, inv_one]
  set p := lowIdx (n := n) k with hpdef
  set e := (d (Fin.rev p))⁻¹ * t (Fin.rev p) * (t (Fin.rev (Fin.rev p)))⁻¹ *
    d (Fin.rev (Fin.rev p)) with he
  have hX : ∀ z, β (longRootHom _ hp (Multiplicative.ofAdd z)) =
      γ' (longRootHom _ hp (Multiplicative.ofAdd z)) := fun z =>
    hpos _ (longRootHom_mem_last hF hk z).1
  have hY : ∀ z : traceZero (unitaryInvolution F 2 f), ∃ z' : traceZero (unitaryInvolution F 2 f),
      (z' : F) = e * z ∧ β (longRootHom _ hp' (Multiplicative.ofAdd z)) =
        γ' (longRootHom _ hp' (Multiplicative.ofAdd z')) := by
    intro z
    set w : traceZero (unitaryInvolution F 2 f) :=
      ⟨t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹, (mem_traceZero _).mpr
        (mul_mem_traceZero_of_unitary ht (Fin.rev p) ((mem_traceZero _).mp z.2))⟩ with hw
    refine ⟨⟨(d (Fin.rev p))⁻¹ * w * ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹, (mem_traceZero _).mpr
      (mul_mem_traceZero_of_unitary hdi (Fin.rev p) ((mem_traceZero _).mp w.2))⟩, ?_, ?_⟩
    · show (d (Fin.rev p))⁻¹ * (t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹) *
        ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹ = e * z
      rw [he, inv_inv]
      ring
    · rw [hneg _ (longRootHom_mem_last hF hk z).2]
      show ψ (conjSU (diagJ t ht) _ (longRootHom _ hp' (Multiplicative.ofAdd z))) =
        ψ (conjSU (diagJ d hd) _ (longRootHom _ hp' (Multiplicative.ofAdd _)))
      rw [conjSU_diagJ_longRootHom, conjSU_diagJ_longRootHom]
      congr 1
      apply longRootHom_congr
      show t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹ =
        d (Fin.rev p) * ((d (Fin.rev p))⁻¹ * (t (Fin.rev p) * z * (t (Fin.rev (Fin.rev p)))⁻¹) *
          ((d (Fin.rev (Fin.rev p)))⁻¹)⁻¹) * (d (Fin.rev (Fin.rev p)))⁻¹
      field_simp [h0d (Fin.rev p), h0d (Fin.rev (Fin.rev p)), h0t (Fin.rev (Fin.rev p))]
      rw [mul_div_mul_right _ _ (h0d _)]
  have he1 : e = 1 := eq_one_of_rankOne_long hF (by omega) hnq hp β γ' hker e hX hY
  have hY1 : ∀ z, β (longRootHom _ hp' (Multiplicative.ofAdd z)) =
      γ' (longRootHom _ hp' (Multiplicative.ofAdd z)) := by
    intro z
    obtain ⟨z', hz', h⟩ := hY z
    rw [h, longRootHom_congr hp' (by rw [hz', he1, one_mul] : (z' : F) = z)]
  show β (levelWeyl _ oneTZ k) = γ' (levelWeyl _ oneTZ k)
  unfold levelWeyl
  rw [dite_eq_right hk, longWeyl_def]
  simp only [map_mul, hX, hY1]

include hF in
theorem agree_neg_of_levelWeyl (hn : 2 ≤ n) {k : Fin (n / 2)} {G : Type*} [Group G]
    (β γ' : SU (unitaryInvolution F 2 f) n →* G)
    (hpos : ∀ z ∈ rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1), β z = γ' z)
    (hw : β (levelWeyl (unitaryInvolution_involutive hF) oneTZ k) =
      γ' (levelWeyl (unitaryInvolution_involutive hF) oneTZ k))
    (y : SU (unitaryInvolution F 2 f) n)
    (hy : y ∈ rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1)) : β y = γ' y := by
  have hCT := isCTGroupDatum hF n hn oneTZ one_ne_zero
  have h1 := hCT.conj_mem k _ (neg_single_mem_roots (D := rootDatum hF n) k) y hy
  have hs : weylAction (isFiniteType_cartan n)
      ((coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple k) (-Pi.single k 1) =
        Pi.single k 1 := by
    rw [map_neg, weylAction_simple_single, neg_neg]
  replace h1 : levelWeyl (unitaryInvolution_involutive hF) oneTZ k * y *
      (levelWeyl (unitaryInvolution_involutive hF) oneTZ k)⁻¹ ∈
        rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1) := by
    convert h1 using 2
    exact hs.symm
  obtain ⟨X, hX, rfl⟩ : ∃ X ∈ rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1),
      y = (levelWeyl (unitaryInvolution_involutive hF) oneTZ k)⁻¹ * X *
        levelWeyl (unitaryInvolution_involutive hF) oneTZ k :=
    ⟨_, h1, by group⟩
  simp only [map_mul, map_inv, hw, hpos X hX]

include hF in
theorem exists_diagJ_of_torus (hn : 4 ≤ n) {G : Type*} [Group G]
    (ψ : SU (unitaryInvolution F 2 f) n →* G) (hker : ψ.ker ≤ Subgroup.center _) (x : G)
    (hx : ∀ γ ∈ (rootDatum hF n).roots, ∃ h ∈ ggTorus (rootDatum hF n),
      ∀ z ∈ (rootDatum hF n).rootGroup γ, x⁻¹ * ψ z * x = ψ (h * z * h⁻¹)) :
    ∃ (d : Fin n → F) (hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1),
      ∀ u, x⁻¹ * ψ u * x = ψ (conjSU (diagJ d hd) (isJUnitary_diagJ d hd) u) := by
  have hσ := unitaryInvolution_involutive hF
  have hdiag : ∀ γ ∈ (rootDatum hF n).roots, ∃ t : Fin n → F,
      ∃ ht : ∀ s, unitaryInvolution F 2 f (t s) * t (Fin.rev s) = 1,
        ∀ z ∈ rootGroup _ hσ n γ,
          x⁻¹ * ψ z * x = ψ (conjSU (diagJ t ht) (isJUnitary_diagJ t ht) z) := by
    intro γ hγ
    obtain ⟨h, hh, hz⟩ := hx γ hγ
    obtain ⟨hd1, hd2⟩ := eq_diagonal_of_mem_ggTorus hF hh
    exact ⟨_, hd2, fun z hzm => by rw [hz z hzm, conj_eq_conjSU_diagJ hd1 hd2]⟩
  choose! T hT hTz using hdiag
  have hsr : ∀ k : Fin (n / 2), Pi.single k 1 ∈ (rootDatum hF n).roots := fun k =>
    single_mem_roots (D := rootDatum hF n) k
  have hnr : ∀ k : Fin (n / 2), -Pi.single k 1 ∈ (rootDatum hF n).roots := fun k =>
    neg_single_mem_roots (D := rootDatum hF n) k
  set Tp : Fin (n / 2) → Fin n → F := fun k => T (Pi.single k 1) with hTp
  have hTp0 : ∀ k s, Tp k s ≠ 0 := fun k s => ne_zero_of_unitary (hT _ (hsr k)) s
  set L : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩ with hL
  have hLlast : ¬ L.val + 1 < n / 2 := by simp only [hL]; omega
  set μ : F := if h : Even n then 1 else Tp L (midIdx n h) with hμ
  have hμu : unitaryInvolution F 2 f μ * μ = 1 := by
    rw [hμ]
    split_ifs with h
    · rw [map_one, one_mul]
    · have := hT _ (hsr L) (midIdx n h)
      rwa [rev_midIdx h] at this
  set lam := lowPart n Tp (Tp L (lowIdx L)) with hlam
  have hlam0 : ∀ a, lam a ≠ 0 := lowPart_ne_zero hTp0 (hTp0 L _)
  set d := extU (unitaryInvolution F 2 f) n lam μ with hddef
  have hd : ∀ s, unitaryInvolution F 2 f (d s) * d (Fin.rev s) = 1 :=
    extU_unitary hσ hlam0 hμu
  refine ⟨d, hd, ?_⟩
  set β : SU (unitaryInvolution F 2 f) n →* G := (MulAut.conj x⁻¹).toMonoidHom.comp ψ with hβ
  have hβx : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [hβ]
  set γ' := ψ.comp (conjSU (diagJ d hd) (isJUnitary_diagJ d hd)) with hγ'
  have hker' : γ'.ker ≤ Subgroup.center _ := ker_comp_conjSU_le_center ψ hker _ _
  have hA : ∀ k : Fin (n / 2), ∀ z ∈ rootGroup _ hσ n (Pi.single k 1), β z = γ' z := by
    intro k z hz
    rw [hβx, hTz _ (hsr k) z hz]
    show ψ _ = ψ _
    congr 1
    refine conjSU_diagJ_eq_of_ratio _ _ _ _ z (ratio_of_mem_simple hσ (hT _ (hsr k)) hd ?_ ?_ hz)
    · intro hk
      rw [hddef, extU_lowIdx, extU_lowIdx, hlam]
      exact lowPart_ratio hTp0 (hTp0 L _) hk
    · intro hk
      have hkL : k = L := Fin.ext (by simp only [hL]; omega)
      subst hkL
      refine ⟨?_, fun s hs => ?_⟩
      · rw [hddef, extU_lowIdx, hlam, lowPart_last _ _ hk]
        rfl
      · have hodd : ¬ Even n := fun he => rev_ne_self_of_even he s hs
        have hs' : s = midIdx n hodd := Fin.ext (by
          have h1 := congrArg Fin.val hs
          simp only [Fin.val_rev] at h1
          simp only [midIdx]
          omega)
        rw [hddef, extU_of_rev_eq _ _ hs, hμ, dite_eq_right hodd, hs']
        rfl
  have hW : ∀ k : Fin (n / 2), β (levelWeyl hσ oneTZ k) = γ' (levelWeyl hσ oneTZ k) := by
    intro k
    by_cases hk : k.val + 1 < n / 2
    · exact levelWeyl_agree_short hF hn hk ψ β d hd hker' (fun z hz => hA k z hz)
        (T (-Pi.single k 1)) (hT _ (hnr k)) (fun z hz => by rw [hβx]; exact hTz _ (hnr k) z hz)
    · exact levelWeyl_agree_last hF hn hk ψ β d hd hker' (fun z hz => hA k z hz)
        (T (-Pi.single k 1)) (hT _ (hnr k)) (fun z hz => by rw [hβx]; exact hTz _ (hnr k) z hz)
  have hE : β.eqLocus γ' = ⊤ :=
    eq_top_of_rankOne_le (isCTGroupDatum hF n (by omega) oneTZ one_ne_zero) _ fun k =>
      sup_le (fun z hz => hA k z hz)
        (fun y hy => agree_neg_of_levelWeyl hF (by omega) β γ' (hA k) (hW k) y hy)
  intro u
  have hu : u ∈ β.eqLocus γ' := by rw [hE]; exact Subgroup.mem_top u
  rw [← hβx]
  exact hu

end Main

section Conj

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem IsJUnitary.mul {A B : GL (Fin n) F} (hA : IsJUnitary σ A) (hB : IsJUnitary σ B) :
    IsJUnitary σ (A * B) := by
  unfold IsJUnitary at hA hB ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr σ (B : Matrix (Fin n) (Fin n) F) * conjTr σ (A : Matrix (Fin n) (Fin n) F) *
        antidiag n * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F))
      = conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
            (A : Matrix (Fin n) (Fin n) F)) * (B : Matrix (Fin n) (Fin n) F) := by
        simp only [Matrix.mul_assoc]
    _ = antidiag n := by rw [hA, hB]

theorem isJUnitary_of_mem_SU (s : SU σ n) : IsJUnitary σ (s : GL (Fin n) F) :=
  s.2.2

end Conj

section Input

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem suInnerDiagConj (hn : 4 ≤ n) : SUInnerDiagConj hF n := by
  intro G _ ψ hker c hc
  obtain ⟨g, ⟨s, rfl⟩, hγ⟩ := hc
  obtain ⟨d, hd, hD⟩ := exists_diagJ_of_torus hF hn ψ hker (c * ψ s) hγ
  refine ⟨(s : GL (Fin n) F) * diagJ d hd,
    (isJUnitary_of_mem_SU s).mul (isJUnitary_diagJ d hd), fun u => ?_⟩
  have h1 : c⁻¹ * ψ u * c = ψ s * ((c * ψ s)⁻¹ * ψ u * (c * ψ s)) * (ψ s)⁻¹ := by group
  rw [h1, hD u, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSU]
  group

end Input

end InnerDiagSU

section Genuine

theorem ggInnerDiagMarkingAt_PSU : GGInnerDiagMarkingAt .PSU :=
  ggInnerDiagMarkingAt_PSU_of fun f hf _ hn =>
    InnerDiagSU.suInnerDiagConj (card_galoisField_two_mul 2 f hf) hn

end Genuine

end CFSG.StandardType
