module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Q2Certificates
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Coord
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.StandardType.LieKnownR2.Link

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis CFSG.StandardType.LieKnownR2.Q2
  CFSG.StandardType.LieKnownR2.Coord

structure LinkData (τ : Tag) (d : ℕ) (L1 Γ : List (Fin τ.rank → ℤ)) (gens : List (List ℕ)) :
    Prop where
  len : L1.length = d
  nodup : L1.Nodup
  deg1 : ∀ α, α ∈ L1 ↔ α ∈ Deg1 τ
  gam : ∀ γ ∈ Γ, IsRoot τ γ ∧ γ (iθ τ) = 0
  glen : gens.length = Γ.length
  bits : ∀ k < Γ.length, ∀ i j : Fin d, bit ((gens.getD k []).getD j 0) i =
    (if i = j then 1 else 0) + (if L1.getD i 0 = Γ.getD k 0 + L1.getD j 0 then 1 else 0)

noncomputable def φ2 {K : Type} [Field K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

@[expose] noncomputable def cvec
    {τ : Tag} {K : Type} [Field K] (L1 : List (Fin τ.rank → ℤ)) (d : ℕ) (q : ModGL τ K) :
    Fin d → K :=
  fun i => heisCoord τ K q (L1.getD i 0)

@[expose] noncomputable def hword
    {τ : Tag} {K : Type} [Field K] (Γ : List (Fin τ.rank → ℤ)) (word : List ℕ) : ModGL τ K :=
  (word.map fun k => pinnedX τ K (Γ.getD k 0) 1).prod

noncomputable def wordK {K : Type} [Field K] [CharP K 2] (d : ℕ) (gens : List (List ℕ))
    (word : List ℕ) : Matrix (Fin d) (Fin d) K :=
  (word.map fun k => (toMat d (gens.getD k [])).map (φ2 (K := K))).prod

@[expose] def nilpMat {τ : Tag} {K : Type} [Field K] (L1 : List (Fin τ.rank → ℤ)) (d : ℕ)
    (γ : Fin τ.rank → ℤ) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => if L1.getD i 0 = γ + L1.getD j 0 then 1 else 0

private theorem getD_mem_of_lt {α : Type*} {l : List α} {k : ℕ} (hk : k < l.length) (a : α) :
    l.getD k a ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

private theorem getD_eq_getElem' {α : Type*} {l : List α} {k : ℕ} (hk : k < l.length) (a : α) :
    l.getD k a = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

theorem wordK_eq {K : Type} [Field K] [CharP K 2] {d : ℕ} (gens : List (List ℕ))
    (word : List ℕ) :
    wordK (K := K) d gens word = (wordProd d gens word).map (φ2 (K := K)) := by
  have := map_list_prod ((φ2 (K := K)).mapMatrix : Matrix (Fin d) (Fin d) (ZMod 2) →+* _)
    (word.map fun i => toMat d (gens.getD i []))
  rw [List.map_map] at this
  simpa [wordK, wordProd, RingHom.mapMatrix_apply, Function.comp_def] using this.symm

theorem hword_mem
    {τ : Tag} {K : Type} [Field K] {Γ : List (Fin τ.rank → ℤ)}
    (hgam : ∀ γ ∈ Γ, IsRoot τ γ ∧ γ (iθ τ) = 0) :
    ∀ word : List ℕ, (∀ k ∈ word, k < Γ.length) → hword (K := K) Γ word ∈ Pθ τ K
  | [], _ => by simp [hword, one_mem]
  | k :: w, hw => by
    have hγ := hgam _ (getD_mem_of_lt (hw k List.mem_cons_self) 0)
    simp only [hword, List.map_cons, List.prod_cons]
    exact mul_mem (pinnedX_mem_Pθ hγ.1 hγ.2 1)
      (hword_mem hgam w fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem cvec_conj_param
    {τ : Tag} {K : Type} [Field K] [CharP K 2] {d : ℕ} {L1 : List (Fin τ.rank → ℤ)}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hlen : L1.length = d) (hnd : L1.Nodup)
    (hdeg1 : ∀ α, α ∈ L1 ↔ α ∈ Deg1 τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ ∧ γ (iθ τ) = 0) (t : K) {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    cvec L1 d (pinnedX τ K γ t * q * (pinnedX τ K γ t)⁻¹) =
      ((1 : Matrix (Fin d) (Fin d) K) + t • (nilpMat L1 d γ : Matrix (Fin d) (Fin d) K)).mulVec
        (cvec L1 d q) := by
  classical
  have hmem : ∀ j : Fin d, L1.getD j 0 ∈ L1 := fun j => getD_mem_of_lt (hlen ▸ j.2) 0
  funext i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [cvec, Pi.add_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, nilpMat, Matrix.of_apply,
    smul_eq_mul]
  rw [heisCoord_conj_param hτ hγ.1 hγ.2 hq t]
  congr 1
  set ν := L1.getD i 0 with hν
  have hνD : ν ∈ Deg1 τ := (hdeg1 ν).1 (hmem i)
  by_cases h1 : ν - γ ∈ Deg1 τ
  · obtain ⟨n, hn, hjn⟩ := List.mem_iff_getElem.1 ((hdeg1 _).2 h1)
    let j0 : Fin d := ⟨n, hlen ▸ hn⟩
    have hj0 : L1.getD j0 0 = ν - γ := by rw [getD_eq_getElem' hn, hjn]
    rw [if_pos ⟨h1, (CoordAux.mem_Deg1.1 hνD).1⟩, Finset.sum_eq_single j0]
    · rw [if_pos (by rw [hj0]; abel), one_mul, hj0]
    · intro j _ hj
      rw [if_neg, zero_mul]
      intro he
      apply hj
      have e1 : L1.getD j 0 = L1.getD j0 0 := by rw [hj0, he]; abel
      rw [getD_eq_getElem' (hlen ▸ j.2), getD_eq_getElem' hn] at e1
      exact Fin.ext ((hnd.getElem_inj_iff).1 e1)
    · simp
  · rw [if_neg (fun h => h1 h.1)]
    symm
    rw [Finset.sum_eq_zero, mul_zero]
    intro j _
    rw [if_neg, zero_mul]
    intro he
    apply h1
    have : L1.getD j 0 = ν - γ := by rw [he]; abel
    rw [← this]
    exact (hdeg1 _).1 (hmem j)

theorem cvec_conj_gen
    {τ : Tag} {K : Type} [Field K] [CharP K 2] {d : ℕ} {L1 Γ : List (Fin τ.rank → ℤ)}
    {gens : List (List ℕ)} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (D : LinkData τ d L1 Γ gens) {k : ℕ} (hk : k < Γ.length) {q : ModGL τ K} (hq : q ∈ Qθ τ K) :
    cvec L1 d (pinnedX τ K (Γ.getD k 0) 1 * q * (pinnedX τ K (Γ.getD k 0) 1)⁻¹) =
      ((toMat d (gens.getD k [])).map (φ2 (K := K))).mulVec (cvec L1 d q) := by
  rw [cvec_conj_param hτ D.len D.nodup D.deg1 (D.gam _ (getD_mem_of_lt hk 0)) 1 hq]
  congr 1
  ext i j
  simp only [Matrix.map_apply, toMat, Matrix.of_apply, D.bits k hk, map_add, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, nilpMat, smul_eq_mul, one_mul]
  split_ifs <;> simp

structure LinkCore
    (τ : Tag) (d : ℕ) (L1 Γ : List (Fin τ.rank → ℤ)) (gens : List (List ℕ)) : Prop where
  len : L1.length = d
  deg1 : ∀ α, α ∈ L1 ↔ α ∈ Deg1 τ
  gam : ∀ γ ∈ Γ, IsRoot τ γ ∧ γ (iθ τ) = 0
  glen : gens.length = Γ.length
  conj : ∀ (K : Type) [Field K] [CharP K 2], ∀ k < Γ.length, ∀ q ∈ Qθ τ K,
    cvec L1 d (pinnedX τ K (Γ.getD k 0) 1 * q * (pinnedX τ K (Γ.getD k 0) 1)⁻¹) =
      ((toMat d (gens.getD k [])).map (φ2 (K := K))).mulVec (cvec L1 d q)

theorem LinkData.core
    {τ : Tag} {d : ℕ} {L1 Γ : List (Fin τ.rank → ℤ)} {gens : List (List ℕ)}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (D : LinkData τ d L1 Γ gens) :
    LinkCore τ d L1 Γ gens :=
  ⟨D.len, D.deg1, D.gam, D.glen, fun _ _ _ _ hk _ hq => cvec_conj_gen hτ D hk hq⟩

theorem cvec_conj_word
    {τ : Tag} {K : Type} [Field K] [CharP K 2] {d : ℕ} {L1 Γ : List (Fin τ.rank → ℤ)}
    {gens : List (List ℕ)} (C : LinkCore τ d L1 Γ gens) :
    ∀ word : List ℕ, (∀ k ∈ word, k < Γ.length) → ∀ q ∈ Qθ τ K,
      cvec L1 d (hword Γ word * q * (hword Γ word)⁻¹) =
        (wordK d gens word).mulVec (cvec L1 d q)
  | [], _, q, _ => by simp [hword, wordK]
  | k :: w, hw, q, hq => by
    have hw' : ∀ j ∈ w, j < Γ.length := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have e : hword (K := K) Γ (k :: w) * q * (hword Γ (k :: w))⁻¹ =
        pinnedX τ K (Γ.getD k 0) 1 * (hword Γ w * q * (hword Γ w)⁻¹) *
          (pinnedX τ K (Γ.getD k 0) 1)⁻¹ := by
      simp only [hword, List.map_cons, List.prod_cons]
      group
    rw [e, C.conj K k (hw k List.mem_cons_self) _ (conj_mem_Qθ (hword_mem C.gam w hw') hq),
      cvec_conj_word C w hw' q hq, Matrix.mulVec_mulVec]
    simp [wordK, List.map_cons, List.prod_cons]

theorem eq_zero_of_mulVec_two_pow {K : Type} [Field K] [CharP K 2] {d : ℕ}
    {W B : Matrix (Fin d) (Fin d) K} (hB : (W + 1) * B = 1) (k : ℕ) {v : Fin d → K}
    (hv : (W ^ 2 ^ k).mulVec v = v) : v = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hBc : B * (W + 1) = 1 := mul_eq_one_comm.mp hB
  have hcomm : Commute (W + 1) B := hB.trans hBc.symm
  have hfrob : (W + 1) ^ 2 ^ k = W ^ 2 ^ k + 1 := by
    simpa using add_pow_char_pow_of_commute (R := Matrix (Fin d) (Fin d) K) 2 k
      (Commute.one_right W)
  have h1 : ((W + 1) ^ 2 ^ k).mulVec v = 0 := by
    rw [hfrob, Matrix.add_mulVec, Matrix.one_mulVec, hv]
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  have h2 : B ^ 2 ^ k * (W + 1) ^ 2 ^ k = 1 := by
    rw [← (hcomm.pow_pow (2 ^ k) (2 ^ k)).eq, ← hcomm.mul_pow, hB, one_pow]
  calc v = (B ^ 2 ^ k * (W + 1) ^ 2 ^ k).mulVec v := by rw [h2, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

theorem exists_odd_fpf_of_conj
    {τ : Tag} {K : Type} [Field K] [CharP K 2] [Finite K] {d : ℕ} {L1 : List (Fin τ.rank → ℤ)}
    (hlen : L1.length = d) (hdeg1 : ∀ α, α ∈ L1 ↔ α ∈ Deg1 τ) {h0 : ModGL τ K}
    (hP : h0 ∈ Pθ τ K) (S : Subgroup (ModGL τ K)) (hS : h0 ∈ S)
    {W B : Matrix (Fin d) (Fin d) K} (hB : (W + 1) * B = 1)
    (hconj : ∀ q ∈ Qθ τ K, cvec L1 d (h0 * q * h0⁻¹) = W.mulVec (cvec L1 d q)) :
    ∃ h ∈ Pθ τ K ⊓ S, Odd (orderOf h) ∧
      ∀ q ∈ Qθ τ K, h * q * h⁻¹ * q⁻¹ ∈ Uθ τ K → q ∈ Uθ τ K := by
  classical
  haveI : Finite (ModGL τ K) := finite_modGL
  have hs := heisCoord_spec τ K
  have h0ne : orderOf h0 ≠ 0 := (orderOf_pos h0).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd h0ne
  have hpow : ∀ n : ℕ, ∀ q ∈ Qθ τ K,
      cvec L1 d (h0 ^ n * q * (h0 ^ n)⁻¹) = (W ^ n).mulVec (cvec L1 d q) := by
    intro n
    induction n with
    | zero => intro q hq; simp
    | succ n ih =>
      intro q hq
      have e : h0 ^ (n + 1) * q * (h0 ^ (n + 1))⁻¹ = h0 * (h0 ^ n * q * (h0 ^ n)⁻¹) * h0⁻¹ := by
        rw [pow_succ']
        group
      rw [e, hconj _ (conj_mem_Qθ (pow_mem hP n) hq), ih q hq, Matrix.mulVec_mulVec, ← pow_succ']
  refine ⟨h0 ^ (2 ^ k), Subgroup.mem_inf.2 ⟨pow_mem hP _, pow_mem hS _⟩, ?_, fun q hq hfix => ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  · have hcoord : heisCoord τ K (h0 ^ (2 ^ k) * q * (h0 ^ (2 ^ k))⁻¹) = heisCoord τ K q := by
      have e : h0 ^ (2 ^ k) * q * (h0 ^ (2 ^ k))⁻¹ =
          (h0 ^ (2 ^ k) * q * (h0 ^ (2 ^ k))⁻¹ * q⁻¹) * q := by group
      rw [e, hs.mul _ (Uθ_le_Qθ hfix) _ hq, (hs.eq_zero_iff _ (Uθ_le_Qθ hfix)).2 hfix, zero_add]
    have hv := hpow (2 ^ k) q hq
    rw [show cvec L1 d (h0 ^ (2 ^ k) * q * (h0 ^ (2 ^ k))⁻¹) = cvec L1 d q by
      unfold cvec; rw [hcoord]] at hv
    have h0v := eq_zero_of_mulVec_two_pow hB k hv.symm
    refine (hs.eq_zero_iff q hq).1 (funext fun ν => ?_)
    by_cases hν : ν ∈ Deg1 τ
    · obtain ⟨i, hi, hiν⟩ := List.mem_iff_getElem.1 ((hdeg1 ν).2 hν)
      have := congrFun h0v ⟨i, hlen ▸ hi⟩
      simp only [cvec, Pi.zero_apply] at this
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hiν] at this
    · exact hs.support q hq ν hν

theorem exists_odd_fpf_mem
    {τ : Tag} {K : Type} [Field K] [CharP K 2] [Finite K] {d : ℕ}
    {L1 Γ : List (Fin τ.rank → ℤ)} {gens : List (List ℕ)}
    (D : LinkCore τ d L1 Γ gens) {word : List ℕ} {n : ℕ} {inv : List ℕ}
    (hw : ∀ k ∈ word, k < Γ.length) (hc : cert d gens word n inv = true)
    (S : Subgroup (ModGL τ K)) (hS : hword (K := K) Γ word ∈ S) :
    ∃ h ∈ Pθ τ K ⊓ S, Odd (orderOf h) ∧
      ∀ q ∈ Qθ τ K, h * q * h⁻¹ * q⁻¹ ∈ Uθ τ K → q ∈ Uθ τ K := by
  obtain ⟨-, -, hB⟩ := cert_spec (D.glen ▸ hw) hc
  have hBK : (wordK (K := K) d gens word + 1) * (toMat d inv).map (φ2 (K := K)) = 1 := by
    have := congrArg ((φ2 (K := K)).mapMatrix) hB
    rwa [map_mul, map_add, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← wordK_eq] at this
  exact exists_odd_fpf_of_conj D.len D.deg1 (hword_mem D.gam word hw) S hS hBK
    (cvec_conj_word D word hw)

theorem exists_odd_fpf
    {τ : Tag} {K : Type} [Field K] [CharP K 2] [Finite K] {d : ℕ}
    {L1 Γ : List (Fin τ.rank → ℤ)} {gens : List (List ℕ)}
    (D : LinkCore τ d L1 Γ gens) {word : List ℕ} {n : ℕ} {inv : List ℕ}
    (hw : ∀ k ∈ word, k < Γ.length) (hc : cert d gens word n inv = true) :
    ∃ h ∈ Pθ τ K, Odd (orderOf h) ∧
      ∀ q ∈ Qθ τ K, h * q * h⁻¹ * q⁻¹ ∈ Uθ τ K → q ∈ Uθ τ K := by
  obtain ⟨h, hh, ho, hq⟩ := exists_odd_fpf_mem (K := K) D hw hc ⊤ (Subgroup.mem_top _)
  exact ⟨h, (Subgroup.mem_inf.1 hh).1, ho, hq⟩

theorem deg1_of_filter
    {τ : Tag} {L1 : List (Fin τ.rank → ℤ)}
    (h : (rootFinset τ).filter (fun α => α (iθ τ) = 1) = L1.toFinset) :
    ∀ α, α ∈ L1 ↔ α ∈ Deg1 τ := by
  intro α
  rw [← List.mem_toFinset, ← h, Finset.mem_filter, mem_rootFinset]
  exact Iff.rfl

theorem gam_of_check
    {τ : Tag} {Γ : List (Fin τ.rank → ℤ)}
    (h : ∀ γ ∈ Γ, γ ∈ rootFinset τ ∧ γ (iθ τ) = 0) : ∀ γ ∈ Γ, IsRoot τ γ ∧ γ (iθ τ) = 0 :=
  fun γ hγ => ⟨mem_rootFinset.1 (h γ hγ).1, (h γ hγ).2⟩

def L1E6 : List (Fin Tag.E6.rank → ℤ) := [![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1]]

@[expose] def gamE6 : List (Fin Tag.E6.rank → ℤ) := [![1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, -1]]

def L1E7 : List (Fin Tag.E7.rank → ℤ) := [![1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0, 0], ![1, 1, 1, 2, 1, 1, 0], ![1, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 1, 1], ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 1], ![1, 1, 2, 3, 2, 2, 1], ![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1]]

def gamE7 : List (Fin Tag.E7.rank → ℤ) := [![0, 1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, -1]]

def L1E8 : List (Fin Tag.E8.rank → ℤ) := [![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1, 1, 1], ![0, 1, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 2, 1, 1], ![0, 1, 1, 2, 2, 2, 2, 1], ![1, 0, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 2, 1, 1], ![1, 1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 1, 1, 1], ![1, 1, 2, 2, 2, 1, 1, 1], ![1, 1, 2, 2, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 1, 1], ![1, 1, 2, 3, 2, 2, 1, 1], ![1, 1, 2, 3, 2, 2, 2, 1], ![1, 1, 2, 3, 3, 2, 1, 1], ![1, 1, 2, 3, 3, 2, 2, 1], ![1, 1, 2, 3, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 1, 1, 1], ![1, 2, 2, 3, 2, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1, 1], ![1, 2, 2, 3, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1, 1], ![1, 2, 2, 4, 3, 2, 2, 1], ![1, 2, 2, 4, 3, 3, 2, 1], ![1, 2, 2, 4, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1, 1], ![1, 2, 3, 4, 3, 2, 2, 1], ![1, 2, 3, 4, 3, 3, 2, 1], ![1, 2, 3, 4, 4, 3, 2, 1], ![1, 2, 3, 5, 4, 3, 2, 1], ![1, 3, 3, 5, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1, 1], ![2, 2, 3, 4, 3, 2, 2, 1], ![2, 2, 3, 4, 3, 3, 2, 1], ![2, 2, 3, 4, 4, 3, 2, 1], ![2, 2, 3, 5, 4, 3, 2, 1], ![2, 2, 4, 5, 4, 3, 2, 1], ![2, 3, 3, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 3, 2, 1], ![2, 3, 4, 6, 5, 4, 2, 1], ![2, 3, 4, 6, 5, 4, 3, 1]]

def gamE8 : List (Fin Tag.E8.rank → ℤ) := [![1, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, -1, 0]]

theorem linkE6
    : LinkData .E6 20 L1E6 gamE6 gensE6 where
  len := by decide
  nodup := by decide +kernel
  deg1 := deg1_of_filter (by decide +kernel)
  gam := gam_of_check (by decide +kernel)
  glen := by decide
  bits := by decide +kernel

theorem E6_exists_odd_fpf
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ h ∈ Pθ .E6 K, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .E6 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .E6 K → q ∈ Uθ .E6 K :=
  exists_odd_fpf (linkE6.core (Or.inr (Or.inl rfl))) (by decide) certE6

theorem linkE7
    : LinkData .E7 32 L1E7 gamE7 gensE7 where
  len := by decide
  nodup := by decide +kernel
  deg1 := deg1_of_filter (by decide +kernel)
  gam := gam_of_check (by decide +kernel)
  glen := by decide
  bits := by decide +kernel

theorem E7_exists_odd_fpf
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ h ∈ Pθ .E7 K, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .E7 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .E7 K → q ∈ Uθ .E7 K :=
  exists_odd_fpf (linkE7.core (Or.inr (Or.inr (Or.inl rfl)))) (by decide) certE7

theorem linkE8
    : LinkData .E8 56 L1E8 gamE8 gensE8 where
  len := by decide
  nodup := by decide +kernel
  deg1 := deg1_of_filter (by decide +kernel)
  gam := gam_of_check (by decide +kernel)
  glen := by decide
  bits := by decide +kernel

theorem E8_exists_odd_fpf
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ h ∈ Pθ .E8 K, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .E8 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .E8 K → q ∈ Uθ .E8 K :=
  exists_odd_fpf (linkE8.core (Or.inr (Or.inr (Or.inr rfl)))) (by decide) certE8

end CFSG.StandardType.LieKnownR2.Link
