module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStruct
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreNat
public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreSec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_commutator_subgroupOf_le_of_normalizer {T H₁ H₂ H₃ N : Subgroup G}
    (hNT : N ≤ T) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (h1 : ⁅⁅H₂.subgroupOf T, H₃.subgroupOf T⁆, H₁.subgroupOf T⁆ ≤ N.subgroupOf T)
    (h2 : ⁅⁅H₃.subgroupOf T, H₁.subgroupOf T⁆, H₂.subgroupOf T⁆ ≤ N.subgroupOf T) :
    ⁅⁅H₁.subgroupOf T, H₂.subgroupOf T⁆, H₃.subgroupOf T⁆ ≤ N.subgroupOf T := by
  haveI : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr hTN
  let φ : ↥T →* ↥T ⧸ N.subgroupOf T := QuotientGroup.mk' (N.subgroupOf T)
  have hker : (N.subgroupOf T).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have h1q : ⁅⁅(H₂.subgroupOf T).map φ, (H₃.subgroupOf T).map φ⁆,
      (H₁.subgroupOf T).map φ⁆ = ⊥ := by
    have hle : (⁅⁅H₂.subgroupOf T, H₃.subgroupOf T⁆, H₁.subgroupOf T⁆).map φ ≤
        (N.subgroupOf T).map φ := Subgroup.map_mono h1
    rw [hker] at hle
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at hle
    exact le_bot_iff.mp hle
  have h2q : ⁅⁅(H₃.subgroupOf T).map φ, (H₁.subgroupOf T).map φ⁆,
      (H₂.subgroupOf T).map φ⁆ = ⊥ := by
    have hle : (⁅⁅H₃.subgroupOf T, H₁.subgroupOf T⁆, H₂.subgroupOf T⁆).map φ ≤
        (N.subgroupOf T).map φ := Subgroup.map_mono h2
    rw [hker] at hle
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at hle
    exact le_bot_iff.mp hle
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := (H₁.subgroupOf T).map φ) (H₂ := (H₂.subgroupOf T).map φ)
    (H₃ := (H₃.subgroupOf T).map φ) h1q h2q
  have hle2 : (⁅⁅H₁.subgroupOf T, H₂.subgroupOf T⁆, H₃.subgroupOf T⁆).map φ = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    exact hrot
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle2
  exact hle2

theorem commutator_commutator_le_of_normalizer {H₁ H₂ H₃ N : Subgroup G}
    (hN : H₁ ⊔ H₂ ⊔ H₃ ≤ Subgroup.normalizer (N : Set G))
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  let T : Subgroup G := H₁ ⊔ H₂ ⊔ H₃ ⊔ N
  have hH₁T : H₁ ≤ T := (le_sup_left.trans le_sup_left).trans le_sup_left
  have hH₂T : H₂ ≤ T := (le_sup_right.trans le_sup_left).trans le_sup_left
  have hH₃T : H₃ ≤ T := le_sup_right.trans le_sup_left
  have hNT : N ≤ T := le_sup_right
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := sup_le hN (Subgroup.le_normalizer (H := N))
  have h1' : ⁅⁅H₂.subgroupOf T, H₃.subgroupOf T⁆, H₁.subgroupOf T⁆ ≤ N.subgroupOf T := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := T)]
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH₂T, inf_eq_left.mpr hH₃T,
      inf_eq_left.mpr hH₁T, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNT]
    exact h1
  have h2' : ⁅⁅H₃.subgroupOf T, H₁.subgroupOf T⁆, H₂.subgroupOf T⁆ ≤ N.subgroupOf T := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := T)]
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH₃T, inf_eq_left.mpr hH₁T,
      inf_eq_left.mpr hH₂T, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNT]
    exact h2
  have hle2 := commutator_commutator_subgroupOf_le_of_normalizer hNT hTN h1' h2'
  have hle3 := (Subgroup.map_subtype_le_map_subtype (G' := T)).mpr hle2
  rwa [Subgroup.map_commutator, Subgroup.map_commutator,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH₁T, inf_eq_left.mpr hH₂T,
    inf_eq_left.mpr hH₃T, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNT] at hle3

theorem commutator_le_of_two_step {D Y Y₁ Y₂ : Subgroup G} (hperf : ⁅D, D⁆ = D)
    (hYn : Y ≤ Subgroup.normalizer (Y₂ : Set G)) (hDn : D ≤ Subgroup.normalizer (Y₂ : Set G))
    (h1 : ⁅Y, D⁆ ≤ Y₁) (h2 : ⁅Y₁, D⁆ ≤ Y₂) : ⁅Y, D⁆ ≤ Y₂ := by
  have hDY : ⁅⁅D, Y⁆, D⁆ ≤ Y₂ := by
    rw [Subgroup.commutator_comm D Y]
    exact (Subgroup.commutator_mono h1 le_rfl).trans h2
  have hYY : ⁅⁅Y, D⁆, D⁆ ≤ Y₂ := (Subgroup.commutator_mono h1 le_rfl).trans h2
  have hrot := commutator_commutator_le_of_normalizer (H₁ := D) (H₂ := D) (H₃ := Y)
    (N := Y₂) (sup_le (sup_le hDn hDn) hYn) hDY hYY
  rw [hperf, Subgroup.commutator_comm D Y] at hrot
  exact hrot

theorem commutator_le_of_series {D : Subgroup G} (hperf : ⁅D, D⁆ = D) (Y : ℕ → Subgroup G) :
    ∀ k, (∀ i ≤ k, D ≤ Subgroup.normalizer (Y i : Set G)) →
      (∀ i ≤ k, Y 0 ≤ Subgroup.normalizer (Y i : Set G)) →
      (∀ i < k, ⁅Y i, D⁆ ≤ Y (i + 1)) → ⁅Y 0, D⁆ ≤ Y k := by
  intro k
  induction k with
  | zero =>
      intro hDn _ _
      refine Subgroup.commutator_le.mpr fun y hy d hd => ?_
      have hconj : d * y⁻¹ * d⁻¹ ∈ Y 0 :=
        (Subgroup.mem_normalizer_iff.mp (hDn 0 le_rfl hd) y⁻¹).mp ((Y 0).inv_mem hy)
      simpa only [commutatorElement_def, mul_assoc] using (Y 0).mul_mem hy hconj
  | succ k ih =>
      intro hDn hY0n hstep
      exact commutator_le_of_two_step hperf (hY0n (k + 1) le_rfl) (hDn (k + 1) le_rfl)
        (ih (fun i hi => hDn i (hi.trans (Nat.le_succ k)))
          (fun i hi => hY0n i (hi.trans (Nat.le_succ k)))
          (fun i hi => hstep i (Nat.lt_succ_of_lt hi)))
        (hstep k (Nat.lt_succ_self k))

theorem exists_unique_of_prod_eq_64 (f : ℕ → ℕ) (m : ℕ)
    (hprod : ∏ i ∈ Finset.range m, f i = 64)
    (hdich : ∀ i ∈ Finset.range m, f i = 1 ∨ 64 ≤ f i) :
    ∃ k ∈ Finset.range m, f k = 64 ∧ ∀ j ∈ Finset.range m, j ≠ k → f j = 1 := by
  have h1le : ∀ i ∈ Finset.range m, 1 ≤ f i := by
    intro i hi
    rcases hdich i hi with h | h
    · exact h.ge
    · exact h.trans' (by norm_num)
  have hex : ∃ k ∈ Finset.range m, f k ≠ 1 := by
    by_contra h
    have h1 : ∏ i ∈ Finset.range m, f i = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      by_contra hne
      exact h ⟨i, hi, hne⟩
    omega
  obtain ⟨k, hk, hkne⟩ := hex
  have hk64 : f k = 64 := by
    have hkge : 64 ≤ f k := (hdich k hk).resolve_left hkne
    have hle := Finset.single_le_prod h1le hk
    rw [hprod] at hle
    omega
  refine ⟨k, hk, hk64, fun j hj hjk => ?_⟩
  have herase : ∏ i ∈ (Finset.range m).erase k, f i = 1 := by
    have h := Finset.prod_erase_mul (Finset.range m) f hk
    rw [hprod, hk64] at h
    omega
  exact (Finset.prod_eq_one_iff_of_one_le (s := (Finset.range m).erase k) (f := f)
    (fun i hi => h1le i (Finset.mem_of_mem_erase hi))).mp herase j
    (Finset.mem_erase.mpr ⟨hjk, hj⟩)

theorem wIdx_eq_one_of_commutator_le {Z N M : Subgroup G}
    (hMN : M ≤ N) (hNn : N ≤ Subgroup.normalizer (M : Set G))
    (hDN : Z ≤ Subgroup.normalizer (N : Set G)) (hDM : Z ≤ Subgroup.normalizer (M : Set G))
    (hcop : Nat.Coprime (Nat.card Z) (Nat.card N)) (hsolv : Group.IsSolvable ↥N)
    (hcomm : ⁅N, Z⁆ ≤ M) : wIdx Z N M = 1 := by
  rw [wIdx, Subgroup.relIndex_eq_one]
  intro n hn
  rw [← CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff hMN hNn hDN hDM hcop hsolv hn]
  intro d hd
  have hnd : ⁅n, d⁆ ∈ M := Subgroup.commutator_le.mp hcomm n hn d hd
  have hdn : ⁅d, n⁆ ∈ M := by
    rw [← commutatorElement_inv]
    exact M.inv_mem hnd
  simpa only [commutatorElement_def] using hdn

theorem le_normalizer_commutator {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hs),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hs)]

private theorem chief_series49_facts {H Q : Subgroup G} {m : ℕ} {N : ℕ → Subgroup G}
    (hQH : H ≤ Subgroup.normalizer (Q : Set G)) (hN0 : N 0 = Q)
    (hchief : ∀ i < m, HChief H (N i) (N (i + 1))) :
    (∀ i < m, N (i + 1) ≤ N i) ∧
      (∀ i < m, N i ≤ Subgroup.normalizer (N (i + 1) : Set G)) ∧
      (∀ i ≤ m, N i ≤ Q) ∧ (∀ i ≤ m, H ≤ Subgroup.normalizer (N i : Set G)) := by
  have hanti : ∀ i < m, N (i + 1) ≤ N i := fun i hi => (hchief i hi).1.le
  refine ⟨hanti, ?_, ?_, ?_⟩
  · intro i hi
    have hlt := (hchief i hi).1
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le]
    exact ⟨fun x hx g => (hchief i hi).2.2.2.1 g g.2 x hx⟩
  · intro i hi
    induction i with
    | zero => rw [hN0]
    | succ i ih =>
        exact (hanti i (Nat.lt_of_succ_le hi)).trans (ih (Nat.le_of_succ_le hi))
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hN0]; exact hQH
    · have hi' : i - 1 < m := by omega
      have h := (hchief (i - 1) hi').2.2.1
      rwa [Nat.sub_add_cancel hipos] at h

private theorem weight_product_eq_64 {H X L Q I : Subgroup G} (hI : Inputs49)
    (h : Setup49 H X L Q I) {x : G} {A : Subgroup G} {a n : G} (hK : KI49 X I)
    (hd : XAData X L I x A a n) {m : ℕ} {N : ℕ → Subgroup G} (hN0 : N 0 = Q)
    (hNm : N m = ⊥) (hanti : ∀ i < m, N (i + 1) ≤ N i)
    (hnorm : ∀ i < m, N i ≤ Subgroup.normalizer (N (i + 1) : Set G)) :
    ∏ i ∈ Finset.range m, wIdx (Z49 X A) (N i) (N (i + 1)) = 64 := by
  have hrel : (Q ⊓ Subgroup.centralizer (Z49 X A : Set G)).relIndex Q = 64 := by
    have hrc := Subgroup.relIndex_mul_card
      (H := Q ⊓ Subgroup.centralizer (Z49 X A : Set G)) (K := Q)
    rw [show Q ⊓ Subgroup.centralizer (Z49 X A : Set G) ⊓ Q
        = Q ⊓ Subgroup.centralizer (Z49 X A : Set G) from inf_eq_left.mpr inf_le_left] at hrc
    rw [(kfacts49 hI h hK hd.reg hd.A_le).2] at hrc
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) hrc
  rw [wprod49 (Z := Z49 X A) m N hN0 hNm hanti hnorm, hrel]

private theorem weight_one_or_large {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n) {m : ℕ} {N : ℕ → Subgroup G}
    (hx : X = Subgroup.zpowers x) (hQ2 : IsPGroup 2 ↥Q)
    (hanti : ∀ i < m, N (i + 1) ≤ N i)
    (hnorm : ∀ i < m, N i ≤ Subgroup.normalizer (N (i + 1) : Set G))
    (hNQ : ∀ i ≤ m, N i ≤ Q) (hHN : ∀ i ≤ m, H ≤ Subgroup.normalizer (N i : Set G))
    (hIH : I ≤ H) (hchief : ∀ i < m, HChief H (N i) (N (i + 1))) :
    (∀ i < m, ⁅N i, I⁆ ≤ N (i + 1) → wIdx (Z49 X A) (N i) (N (i + 1)) = 1) ∧
      (∀ i ∈ Finset.range m, wIdx (Z49 X A) (N i) (N (i + 1)) = 1 ∨
        64 ≤ wIdx (Z49 X A) (N i) (N (i + 1))) := by
  have hZcard : Nat.card ↥(Z49 X A) = 3 := hd.reg.2.2.2.2
  have hZ_le_I : Z49 X A ≤ I := (inf_le_left : Z49 X A ≤ A).trans hd.A_le
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hone : ∀ i < m, ⁅N i, I⁆ ≤ N (i + 1) →
      wIdx (Z49 X A) (N i) (N (i + 1)) = 1 := by
    intro i hi hIi
    have hNiQ : N i ≤ Q := hNQ i (le_of_lt hi)
    haveI : Group.IsNilpotent ↥(N i) := (hQ2.to_le hNiQ).isNilpotent
    refine wIdx_eq_one_of_commutator_le (hanti i hi) (hnorm i hi)
      (hZ_le_I.trans (hIH.trans (hHN i (le_of_lt hi))))
      (hZ_le_I.trans (hIH.trans (hHN (i + 1) hi)))
      (IsPGroup.coprime_card_of_ne 3 2 (by norm_num) (Z49 X A) (N i)
        (IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)) (hQ2.to_le hNiQ))
      (inferInstance : Group.IsSolvable ↥(N i))
      ((Subgroup.commutator_mono le_rfl hZ_le_I).trans hIi)
  refine ⟨hone, fun i hi => ?_⟩
  rw [Finset.mem_range] at hi
  by_cases hIi : ⁅N i, I⁆ ≤ N (i + 1)
  · exact Or.inl (hone i hi hIi)
  · exact Or.inr (chief_w49 h hx hd (hchief i hi) (hNQ i (le_of_lt hi)) hIi)

private theorem exists_unique_weight_index {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} {A : Subgroup G} {a n : G} (hd : XAData X L I x A a n) {m : ℕ}
    {N : ℕ → Subgroup G} (hx : X = Subgroup.zpowers x) (hNQ : ∀ i ≤ m, N i ≤ Q)
    (hchief : ∀ i < m, HChief H (N i) (N (i + 1)))
    (hprod : ∏ i ∈ Finset.range m, wIdx (Z49 X A) (N i) (N (i + 1)) = 64)
    (hone : ∀ i < m, ⁅N i, I⁆ ≤ N (i + 1) → wIdx (Z49 X A) (N i) (N (i + 1)) = 1)
    (hdich : ∀ i ∈ Finset.range m, wIdx (Z49 X A) (N i) (N (i + 1)) = 1 ∨
      64 ≤ wIdx (Z49 X A) (N i) (N (i + 1))) :
    ∃ k < m, wIdx (Z49 X A) (N k) (N (k + 1)) = 64 ∧ ¬ ⁅N k, I⁆ ≤ N (k + 1) ∧
      ∀ j < m, j ≠ k → ⁅N j, I⁆ ≤ N (j + 1) := by
  obtain ⟨k, hkrange, hk64, hkrest⟩ :=
    exists_unique_of_prod_eq_64 (fun i => wIdx (Z49 X A) (N i) (N (i + 1))) m hprod hdich
  have hkm : k < m := Finset.mem_range.mp hkrange
  refine ⟨k, hkm, hk64, ?_, ?_⟩
  · intro hIk
    have h1 := hone k hkm hIk
    omega
  · intro j hjm hjk
    by_contra hIj
    have h64 := chief_w49 h hx hd (hchief j hjm) (hNQ j (le_of_lt hjm)) hIj
    have h1 := hkrest j (Finset.mem_range.mpr hjm) hjk
    omega

private theorem commutator_below_and_above_trivial {H X L Q I : Subgroup G}
    (h : Setup49 H X L Q I) {k m : ℕ} {N : ℕ → Subgroup G} (hkm : k < m)
    (hN0 : N 0 = Q) (hNm : N m = ⊥) (hNQ : ∀ i ≤ m, N i ≤ Q)
    (hHN : ∀ i ≤ m, H ≤ Subgroup.normalizer (N i : Set G)) (hIH : I ≤ H) (hQleH : Q ≤ H)
    (hIothers : ∀ j < m, j ≠ k → ⁅N j, I⁆ ≤ N (j + 1)) :
    ⁅N (k + 1), I⁆ = ⊥ ∧ ⁅Q, I⁆ ≤ N k := by
  have hperfI : ⁅I, I⁆ = I := commutator_I_eq h
  constructor
  · have key := commutator_le_of_series (D := I) hperfI (fun i => N (k + 1 + i)) (m - k - 1)
      (fun i hi => hIH.trans (hHN (k + 1 + i) (by omega)))
      (fun i hi => (hNQ (k + 1) hkm).trans (hQleH.trans (hHN (k + 1 + i) (by omega))))
      (fun i hi => hIothers (k + 1 + i) (by omega) (by omega))
    rw [show k + 1 + (m - k - 1) = m by omega, hNm] at key
    exact le_bot_iff.mp key
  · have key := commutator_le_of_series (D := I) hperfI N k
      (fun i hi => hIH.trans (hHN i (by omega)))
      (fun i hi => (hN0.le.trans hQleH).trans (hHN i (by omega)))
      (fun i hi => hIothers i (hi.trans hkm) (by omega))
    rwa [hN0] at key

private theorem commutator_le_sup_of_chief {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {x : G} (hxX : x ∈ X) {k m : ℕ} {N : ℕ → Subgroup G} (hkm : k < m)
    (hHN : ∀ i ≤ m, H ≤ Subgroup.normalizer (N i : Set G)) (hIH : I ≤ H)
    (hQleH : Q ≤ H) (hQI : ⁅Q, I⁆ ≤ N k) {i : ℕ} {V : ℕ → Subgroup G}
    (hVi : V i = ⁅N k, Lc L x i⁆ ⊔ N (k + 1)) :
    ⁅Q, Lc L x i⁆ ≤ V i := by
  have hxiX : x ^ i ∈ X := X.pow_mem hxX i
  have hLiI : Lc L x i ≤ I := conjugate_le_I h hxiX
  have hLiH : Lc L x i ≤ H := hLiI.trans hIH
  have hperf : ⁅Lc L x i, Lc L x i⁆ = Lc L x i :=
    CFSG.RankThree.PartTwo.Sec18.commutator_eq_of_mem_oTwoComponentsIn
      (conjugate_mem_oTwoComponentsIn h.L_mem (h.X_le hxiX))
  have hQNL : Q ≤ Subgroup.normalizer (⁅N k, Lc L x i⁆ : Subgroup G) :=
    le_normalizer_commutator (hQleH.trans (hHN k (le_of_lt hkm)))
      (pCoreOf_le_normalizer_conjugate h hxiX)
  have hLNL : Lc L x i ≤ Subgroup.normalizer (⁅N k, Lc L x i⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := N k) (H₂ := Lc L x i)
  rw [hVi]
  refine commutator_le_of_two_step (D := Lc L x i) (Y := Q) (Y₁ := N k)
    (Y₂ := ⁅N k, Lc L x i⁆ ⊔ N (k + 1)) hperf ?_ ?_ ?_ ?_
  · exact (le_inf hQNL (hQleH.trans (hHN (k + 1) hkm))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  · refine (le_inf hLNL ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    exact hLiH.trans (hHN (k + 1) hkm)
  · exact (Subgroup.commutator_mono le_rfl hLiI).trans hQI
  · exact le_sup_left

theorem propM49 (hI : Inputs49) {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {x : G}
    (hx : X = Subgroup.zpowers x) (hK : KI49 X I) :
    ∃ N₀ N₁ : Subgroup G, N₁ ≤ N₀ ∧ N₀ ≤ Q ∧
      H ≤ Subgroup.normalizer (N₀ : Set G) ∧ H ≤ Subgroup.normalizer (N₁ : Set G) ∧
      ⁅N₁, I⁆ = ⊥ ∧ ⁅Q, I⁆ ≤ N₀ ∧ ⁅N₀, Q⁆ ≤ N₁ ∧
      ∀ V : ℕ → Subgroup G, (∀ i, V i = ⁅N₀, Lc L x i⁆ ⊔ N₁) →
        N₀ = V 0 ⊔ V 1 ⊔ V 2 ∧
        (V 0 ⊓ (V 1 ⊔ V 2) = N₁ ∧ V 1 ⊓ (V 0 ⊔ V 2) = N₁ ∧ V 2 ⊓ (V 0 ⊔ V 1) = N₁) ∧
        (∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ⁅V i, Lc L x j⁆ ≤ N₁) ∧
        (∀ i : ℕ, i < 3 → ⁅Q, Lc L x i⁆ ≤ V i ∧ NatA5Sec (Lc L x i) (V i) N₁) := by
  classical
  have hxX : x ∈ X := by rw [hx]; exact Subgroup.mem_zpowers x
  obtain ⟨A, a, n, hd⟩ := xaData_exists h hx
  have hQ2 : IsPGroup 2 ↥Q := by rw [h.Q_eq]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hQHn : H ≤ Subgroup.normalizer (Q : Set G) := by
    rw [h.Q_eq]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQleH : Q ≤ H := h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hIH : I ≤ H := I_le_H h
  obtain ⟨m, N, hN0, hNm, hchief⟩ := chief_series49 hQ2 hQHn
  obtain ⟨hanti, hnorm, hNQ, hHN⟩ := chief_series49_facts hQHn hN0 hchief
  have hprod := weight_product_eq_64 hI h hK hd hN0 hNm hanti hnorm
  obtain ⟨hone, hdich⟩ := weight_one_or_large h hd hx hQ2 hanti hnorm hNQ hHN hIH hchief
  obtain ⟨k, hkm, hk64, hIk, hIothers⟩ :=
    exists_unique_weight_index h hd hx hNQ hchief hprod hone hdich
  obtain ⟨hN1I, hQI⟩ :=
    commutator_below_and_above_trivial h hkm hN0 hNm hNQ hHN hIH hQleH hIothers
  have hNkQ : N k ≤ Q := hNQ k (le_of_lt hkm)
  have hfaithful := chief_faithful49 h (hchief k hkm) hNkQ hIk
  have hstruct := chief_struct49 h hx hd hI.1 (hchief k hkm) hNkQ hIk (le_of_eq hk64)
  have hnat := chief_nat49 hI h hx hK hd (hchief k hkm) hNkQ hIk hstruct
  refine ⟨N k, N (k + 1), hanti k hkm, hNkQ, hHN k (le_of_lt hkm),
    hHN (k + 1) hkm, hN1I, hQI, hfaithful.1, fun V hV => ?_⟩
  obtain ⟨hVshape, hVinf, hVcomm, _⟩ := hstruct V hV
  refine ⟨hVshape, hVinf, hVcomm, fun i hi3 => ⟨?_, hnat V hV i hi3⟩⟩
  exact commutator_le_sup_of_chief h hxX hkm hHN hIH hQleH hQI (hV i)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
