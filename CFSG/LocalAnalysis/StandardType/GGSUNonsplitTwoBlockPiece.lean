module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestBlock

public section

namespace CFSG.StandardType

namespace SUTB

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.RankThree.PartOne.OddIso

section General

variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem nondegOn_of_left (hB : B.IsSymm) {W : Submodule K V}
    (h : ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0) : NondegOn B W := by
  intro m hm hn
  refine h m hm fun w hw => ?_
  rw [← hB.eq w m, hn w hw, map_zero]

variable [CharP K 2] {y : Module.End K V} {p : ℕ}

theorem nondegOn_range (hB : B.IsSymm) (hBn : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hyB : ∀ v w, B (y v) (y w) = B v w) (hp : Odd p) (hyp : y ^ p = 1) :
    NondegOn B (LinearMap.range (y - 1)) :=
  nondegOn_of_left hB (range_sepH hBn hyB hp hyp)

theorem range_orth_eq_ker [FiniteDimensional K V] (hB : B.IsSymm)
    (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) (hyB : ∀ v w, B (y v) (y w) = B v w) (hp : Odd p)
    (hyp : y ^ p = 1) :
    (LinearMap.range (y - 1)).orthogonalBilin B = LinearMap.ker (y - 1) := by
  have hle : LinearMap.ker (y - 1) ≤ (LinearMap.range (y - 1)).orthogonalBilin B := by
    intro v hv
    have hv' : y v = v := sub_eq_zero.mp (LinearMap.mem_ker.mp hv)
    rw [Submodule.mem_orthogonalBilin]
    rintro _ ⟨u, rfl⟩
    exact B_range_fix B hyB hv' u
  have hc := isCompl_orthogonalBilin_of_sep (nondegOn_range hB hBn hyB hp hyp)
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  have h2 := LinearMap.finrank_range_add_finrank_ker (y - 1)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

omit [CharP K 2] in
theorem ker_aeval_le_range (hpK : (p : K) ≠ 0) (hpp : p.Prime) {g : K[X]}
    (hgd : g ∣ cyclotomic p K) : LinearMap.ker (aeval y g) ≤ LinearMap.range (y - 1) := by
  have : Fact p.Prime := ⟨hpp⟩
  have hcop1 : IsCoprime (X - C 1 : K[X]) (cyclotomic p K) := by
    refine (Polynomial.irreducible_X_sub_C (1 : K)).coprime_iff_not_dvd.mpr fun hd => hpK ?_
    have h1 := (Polynomial.dvd_iff_isRoot).mp hd
    rwa [IsRoot, Polynomial.eval_one_cyclotomic_prime] at h1
  have hcop : IsCoprime (X - C 1 : K[X]) g := hcop1.of_isCoprime_of_dvd_right hgd
  obtain ⟨a, b, hab⟩ := hcop
  intro v hv
  rw [LinearMap.mem_ker] at hv
  refine ⟨aeval y a v, ?_⟩
  have h1 : aeval y (a * (X - C 1) + b * g) v = v := by rw [hab, map_one, Module.End.one_apply]
  rw [map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
    hv, map_zero, add_zero, map_sub, aeval_X, aeval_C, map_one] at h1
  have hc : Commute (aeval y a) (y - 1) :=
    (OrdPNS.commute_aeval (Commute.refl y) a).sub_right (Commute.one_right _)
  calc (y - 1) (aeval y a v) = ((y - 1) * aeval y a) v := rfl
    _ = (aeval y a * (y - 1)) v := by rw [hc.eq]
    _ = v := h1

omit [CharP K 2] in
theorem finrank_range_sub_one_lt [FiniteDimensional K V] {U : Submodule K V} (hU : NondegOn B U)
    {z : Module.End K V} (hz1 : ∀ v ∈ U.orthogonalBilin B, z v = v)
    {v : V} (hv : v ∈ U) (hv0 : v ≠ 0) (hzv : z v = v) :
    finrank K (LinearMap.range (z - 1)) < finrank K U := by
  have hle : LinearMap.range (z - 1) ≤ U.map (z - 1) := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨m, hm, z', hz', rfl⟩ := exists_add_orth hU w
    refine ⟨m, hm, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, hz1 z' hz']
    abel
  have hker : LinearMap.ker ((z - 1).domRestrict U) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨v, hv⟩ : U) ∈ LinearMap.ker ((z - 1).domRestrict U) := by
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.sub_apply, hzv,
        Module.End.one_apply, sub_self]
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv0 (congrArg Subtype.val hmem)
  have hpos : 0 < finrank K (LinearMap.ker ((z - 1).domRestrict U)) :=
    Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.mp h0)
  have h1 := LinearMap.finrank_range_add_finrank_ker ((z - 1).domRestrict U)
  rw [LinearMap.range_domRestrict] at h1
  have h2 := Submodule.finrank_mono hle
  omega

omit [CharP K 2] in
theorem range_sub_one_le [FiniteDimensional K V] {W : Submodule K V} (hW : NondegOn B W)
    {g : Module.End K V} (hyW : ∀ w ∈ W, y w ∈ W) (hgW : ∀ w ∈ W, g w = y w)
    (hg1 : ∀ v ∈ W.orthogonalBilin B, g v = v) : LinearMap.range (g - 1) ≤ W := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, hm, z', hz', rfl⟩ := exists_add_orth hW v
  have : (g - 1) (m + z') = y m - m := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add, hgW m hm, hg1 z' hz']
    abel
  rw [this]
  exact W.sub_mem (hyW m hm) hm

omit [CharP K 2] in
theorem nondegOn_sup {X U : Submodule K V} (hX : NondegOn B X) (hU : NondegOn B U)
    (horth : ∀ u ∈ U, ∀ v ∈ X, B u v = 0 ∧ B v u = 0) : NondegOn B (X ⊔ U) := by
  intro m hm hn
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  have ha0 : a = 0 := hX a ha fun n hn' => by
    have h1 := hn n (Submodule.mem_sup_left hn')
    rwa [map_add, (horth b hb n hn').2, add_zero] at h1
  have hb0 : b = 0 := hU b hb fun n hn' => by
    have h1 := hn n (Submodule.mem_sup_right hn')
    rwa [map_add, ha0, map_zero, zero_add] at h1
  rw [ha0, hb0, add_zero]

end General

section Piece

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

noncomputable abbrev rng (y : ↥(unitarySU 2 f K n)) : Submodule K (Fin n → K) := LinearMap.range (lin y - 1)

structure IsPiece (p : ℕ) (A : Subgroup ↥(unitarySU 2 f K n)) (X : Submodule K (Fin n → K))
    (y : ↥(unitarySU 2 f K n)) : Prop where
  mem : y ∈ A
  ne_one : y ≠ 1
  triv : ∀ v ∈ X, lin y v = v
  rk_le : ∀ c ∈ A, c ≠ 1 → (∀ v ∈ X, lin c v = v) → finrank K (rng y) ≤ finrank K (rng c)
  cyc : ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ rng y, lin c u = lin (y ^ k) u
  minimal : ∀ W : Submodule K (Fin n → K), W ≤ rng y → W ≠ ⊥ → NondegOn (stdHermForm h n) W →
    (∀ a ∈ A, ∀ w ∈ W, lin a w ∈ W) → W = rng y

variable {h} {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

theorem MaxElemAb.odd (hA : MaxElemAb p A) : Odd p := hA.prime.odd_of_ne_two hA.ne_two

theorem MaxElemAb.natCast_ne_zero (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A) :
    (p : K) ≠ 0 := by
  have : CharP K 2 := h.charP
  rw [natCast_odd_eq_one hA.odd]
  exact one_ne_zero

theorem MaxElemAb.lin_pow (hA : MaxElemAb p A) {a : ↥(unitarySU 2 f K n)} (ha : a ∈ A) :
    lin a ^ p = 1 := by
  rw [← SUTB.lin_pow, hA.pow a ha, SUTB.lin_one]

theorem MaxElemAb.lin_comm (hA : MaxElemAb p A) {a b : ↥(unitarySU 2 f K n)} (ha : a ∈ A)
    (hb : b ∈ A) : Commute (lin a) (lin b) := by
  rw [Commute, SemiconjBy, ← SUTB.lin_mul, ← SUTB.lin_mul, hA.comm a ha b hb]

theorem nondegOn_rng (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) :
    NondegOn (stdHermForm h n) (rng y) :=
  have : CharP K 2 := h.charP
  nondegOn_range (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n) (isometry_lin h y)
    hA.odd (hA.lin_pow hy)

theorem rng_orth_eq_ker (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) :
    (rng y).orthogonalBilin (stdHermForm h n) = LinearMap.ker (lin y - 1) :=
  have : CharP K 2 := h.charP
  range_orth_eq_ker (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n) (isometry_lin h y)
    hA.odd (hA.lin_pow hy)

theorem rng_inv (hA : MaxElemAb p A) {y a : ↥(unitarySU 2 f K n)} (hy : y ∈ A) (ha : a ∈ A) :
    ∀ u ∈ rng y, lin a u ∈ rng y := by
  rintro _ ⟨v, rfl⟩
  refine ⟨lin a v, ?_⟩
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, mul_sub, sub_mul, mul_one, one_mul,
    (hA.lin_comm hy ha).eq]

theorem eq_zero_of_mem_rng (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A) {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A)
    {u : Fin n → K} (hu : u ∈ rng y) (hyu : lin y u = u) : u = 0 :=
  have : CharP K 2 := h.charP
  eq_zero_of_fixed_range hA.odd (hA.lin_pow hy) hu hyu

theorem rng_orth_of_triv {y : ↥(unitarySU 2 f K n)} {X : Submodule K (Fin n → K)}
    (hyX : ∀ v ∈ X, lin y v = v) :
    ∀ u ∈ rng y, ∀ v ∈ X, stdHermForm h n u v = 0 ∧ stdHermForm h n v u = 0 := by
  rintro _ ⟨w, rfl⟩ v hv
  exact ⟨B_range_fix _ (isometry_lin h y) (hyX v hv) w, B_fix_range _ (isometry_lin h y) (hyX v hv) w⟩

theorem exists_isPiece (hA : MaxElemAb p A) {X : Submodule K (Fin n → K)}
    (hne : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ X, lin c v = v) : ∃ y, IsPiece h p A X y := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hex : ∃ r, ∃ c ∈ A, c ≠ 1 ∧ (∀ v ∈ X, lin c v = v) ∧ finrank K (rng c) = r := by
    obtain ⟨c, hc, hc1, hcX⟩ := hne
    exact ⟨_, c, hc, hc1, hcX, rfl⟩
  obtain ⟨y, hyA, hy1, hyX, hyr⟩ := Nat.find_spec hex
  have hmin : ∀ c ∈ A, c ≠ 1 → (∀ v ∈ X, lin c v = v) →
      finrank K (rng y) ≤ finrank K (rng c) := by
    intro c hc hc1 hcX
    rw [hyr]
    exact Nat.find_min' hex ⟨c, hc, hc1, hcX, rfl⟩
  have hUnd := nondegOn_rng (h := h) hA hyA
  have hUA : ∀ a ∈ A, ∀ u ∈ rng y, lin a u ∈ rng y := fun a ha => rng_inv hA hyA ha
  have hUX := rng_orth_of_triv (h := h) hyX
  have hXo : ∀ W : Submodule K (Fin n → K), W ≤ rng y → ∀ v ∈ X,
      v ∈ W.orthogonalBilin (stdHermForm h n) :=
    fun W hW v hv => Submodule.mem_orthogonalBilin.mpr fun m hm => (hUX m (hW hm) v hv).1
  have hyp := hA.lin_pow hyA
  have hpK := hA.natCast_ne_zero h
  refine ⟨y, hyA, hy1, hyX, hmin, fun c hc => ?_, fun W hWU hW0 hWnd hWA => ?_⟩
  ·
    obtain ⟨c', hc'A, hc'U, hc'o⟩ := exists_mem_restrict h hA hUnd hUA hc
    by_contra hcon
    push Not at hcon
    have hy1' : lin y ≠ 1 := fun h1 => hy1 (lin_injective (h1.trans lin_one.symm))
    obtain ⟨g, hg, hgd, hgker⟩ := OrdPNS.exists_irreducible_ker_ne_bot hA.prime hyp hy1'
    have : Fact (Irreducible g) := ⟨hg⟩
    set Wg := LinearMap.ker (aeval (lin y) g) with hWg
    have hWgU : Wg ≤ rng y := ker_aeval_le_range hpK hA.prime hgd
    have hyW : ∀ v ∈ Wg, lin y v ∈ Wg := OrdPNS.mapsTo_ker_aeval (Commute.refl _) g
    have hcW : ∀ v ∈ Wg, lin c' v ∈ Wg := OrdPNS.mapsTo_ker_aeval (hA.lin_comm hyA hc'A) g
    set y₁ := (lin y).restrict hyW with hy₁
    set c₁ := (lin c').restrict hcW with hc₁
    have hgy₁ : aeval y₁ g = 0 := LinearMap.ext fun w => Subtype.ext (by
      rw [OrdPNS.coe_aeval_restrict_apply, LinearMap.zero_apply, Submodule.coe_zero]
      exact LinearMap.mem_ker.mp w.2)
    have hyc : Commute y₁ c₁ := OrdPNS.restrict_commute' (hA.lin_comm hyA hc'A) _ _
    obtain ⟨ι, _, Φ, hΦ⟩ := NSFrame.exists_lineFrame hA.prime hpK hgd hgy₁ {y₁, c₁}
      (by
        rintro x (rfl | rfl) x' (rfl | rfl)
        · exact Commute.refl _
        · exact hyc
        · exact hyc.symm
        · exact Commute.refl _)
      (by
        rintro x (rfl | rfl)
        · exact Commute.refl _
        · exact hyc.symm)
      (by
        rintro x (rfl | rfl)
        · exact OrdPNS.restrict_pow_eq_one hyp _
        · exact OrdPNS.restrict_pow_eq_one (hA.lin_pow hc'A) _)
    obtain ⟨k₁, hk₁⟩ := hΦ y₁ (by simp)
    obtain ⟨k₂, hk₂⟩ := hΦ c₁ (by simp)
    obtain ⟨i₀⟩ : Nonempty ι := by
      by_contra hne'
      rw [not_nonempty_iff] at hne'
      refine hgker ((Submodule.eq_bot_iff _).mpr fun w hw => ?_)
      have h1 : (⟨w, hw⟩ : Wg) = Φ (Φ.symm ⟨w, hw⟩) := (Φ.apply_symm_apply _).symm
      rw [Subsingleton.elim (Φ.symm ⟨w, hw⟩) 0, map_zero] at h1
      exact congrArg Subtype.val h1
    set e : ι → AdjoinRoot g := Pi.single i₀ 1 with he
    have hζ := NSFrame.root_isPrimitiveRoot hA.prime hpK hgd
    have hv0 : Φ e ≠ 0 := by
      intro hv
      have h1 := congrFun (Φ.injective (hv.trans (map_zero Φ).symm)) i₀
      simp [he] at h1
    have hpow : ∀ (s : ℕ) (u : ι → AdjoinRoot g),
        (y₁ ^ s) (Φ u) = Φ (fun i => AdjoinRoot.root g ^ (k₁ i * s) * u i) := by
      intro s
      induction s with
      | zero => intro u; simp
      | succ s ih =>
        intro u
        rw [pow_succ', Module.End.mul_apply, ih, hk₁]
        congr 1
        funext i
        rw [← mul_assoc, ← pow_add]
        ring_nf
    have hk₁p : ¬ p ∣ k₁ i₀ := by
      intro hd
      have h1 : y₁ (Φ e) = Φ e := by
        rw [hk₁]
        congr 1
        funext i
        by_cases hi : i = i₀
        · subst hi
          simp [he, (hζ.pow_eq_one_iff_dvd _).mpr hd]
        · simp [he, Pi.single_eq_of_ne hi]
      exact hv0 (Subtype.ext (eq_zero_of_mem_rng h hA hyA (hWgU (Φ e).2)
        (congrArg Subtype.val h1)))
    have hcop : (k₁ i₀).Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd hA.prime).mpr hk₁p).symm
    have : NeZero p := ⟨hA.prime.ne_zero⟩
    obtain ⟨s, -, hs⟩ := (hζ.pow_of_coprime _ hcop).eq_pow_of_pow_eq_one
      (ξ := AdjoinRoot.root g ^ (k₂ i₀ * (p - 1))) (by
        rw [← pow_mul, mul_comm, ← mul_assoc, pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow])
    have hroot : AdjoinRoot.root g ^ (k₁ i₀ * s) * AdjoinRoot.root g ^ k₂ i₀ = 1 := by
      rw [pow_mul, hs, ← pow_add, show k₂ i₀ * (p - 1) + k₂ i₀ = p * k₂ i₀ by
        have h1 : p = (p - 1) + 1 := by have := hA.prime.one_lt; omega
        conv_rhs => rw [h1]
        ring,
        pow_mul, hζ.pow_eq_one, one_pow]
    set z := y ^ s * c' with hz
    have hzA : z ∈ A := A.mul_mem (A.pow_mem hyA s) hc'A
    have hlinz : lin z = lin y ^ s * lin c' := by rw [hz, lin_mul, SUTB.lin_pow]
    have hzv : lin z (Φ e : Fin n → K) = Φ e := by
      have h1 : (y₁ ^ s) (c₁ (Φ e)) = Φ e := by
        rw [hk₂, hpow]
        congr 1
        funext i
        by_cases hi : i = i₀
        · subst hi
          simp only [he, Pi.single_eq_same, mul_one]
          exact hroot
        · simp [he, Pi.single_eq_of_ne hi]
      have h2 := congrArg Subtype.val h1
      rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply, hc₁,
        LinearMap.coe_restrict_apply] at h2
      rw [hlinz, Module.End.mul_apply]
      exact h2
    have hz1 : z ≠ 1 := by
      intro hz1
      have hc'eq : c' = y ^ (s * (p - 1)) := by
        rw [eq_inv_of_mul_eq_one_right hz1]
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_add, show s + s * (p - 1) = s * p by
          have h1 : p = (p - 1) + 1 := by have := hA.prime.one_lt; omega
          conv_rhs => rw [h1]
          ring,
          pow_mul', hA.pow y hyA, one_pow]
      obtain ⟨u, hu, hne⟩ := hcon (s * (p - 1))
      exact hne (by rw [← hc'U u hu, hc'eq])
    have hker := rng_orth_eq_ker (h := h) hA hyA
    have hz1o : ∀ v ∈ (rng y).orthogonalBilin (stdHermForm h n), lin z v = v := by
      intro v hv
      have hyv : lin y v = v := by
        have h1 := hker ▸ hv
        exact sub_eq_zero.mp (LinearMap.mem_ker.mp h1)
      have hyv' : ∀ m : ℕ, (lin y ^ m) v = v := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ, Module.End.mul_apply, hyv, ih]
      rw [hlinz, Module.End.mul_apply, hc'o v hv, hyv' s]
    have hzX : ∀ v ∈ X, lin z v = v := fun v hv => hz1o v (hXo _ le_rfl v hv)
    have hlt := finrank_range_sub_one_lt hUnd hz1o (hWgU (Φ e).2)
      (fun h0 => hv0 (Subtype.ext h0)) hzv
    exact absurd (hmin z hzA hz1 hzX) (not_le.mpr hlt)
  ·
    obtain ⟨g, hgA, hgW, hgo⟩ := exists_mem_restrict h hA hWnd hWA hyA
    have hgX : ∀ v ∈ X, lin g v = v := fun v hv => hgo v (hXo W hWU v hv)
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hg1 : g ≠ 1 := by
      intro hg
      have h1 := hgW w hwW
      rw [hg, lin_one, Module.End.one_apply] at h1
      exact hw0 (eq_zero_of_mem_rng h hA hyA (hWU hwW) h1.symm)
    have hle : rng g ≤ W := range_sub_one_le hWnd (hWA y hyA) hgW hgo
    exact Submodule.eq_of_le_of_finrank_le hWU
      ((hmin g hgA hg1 hgX).trans (Submodule.finrank_mono hle))

variable {X : Submodule K (Fin n → K)} {y : ↥(unitarySU 2 f K n)}

theorem IsPiece.orth (hy : IsPiece h p A X y) :
    ∀ u ∈ rng y, ∀ v ∈ X, stdHermForm h n u v = 0 ∧ stdHermForm h n v u = 0 :=
  rng_orth_of_triv hy.triv

theorem IsPiece.nondegOn (hA : MaxElemAb p A) (hy : IsPiece h p A X y) :
    NondegOn (stdHermForm h n) (rng y) :=
  nondegOn_rng hA hy.mem

theorem IsPiece.nondegOn_sup (hA : MaxElemAb p A) (hy : IsPiece h p A X y)
    (hX : NondegOn (stdHermForm h n) X) : NondegOn (stdHermForm h n) (X ⊔ rng y) :=
  SUTB.nondegOn_sup hX (hy.nondegOn hA) hy.orth

theorem IsPiece.inv_sup (hA : MaxElemAb p A) (hy : IsPiece h p A X y)
    (hXA : ∀ a ∈ A, ∀ v ∈ X, lin a v ∈ X) : ∀ a ∈ A, ∀ v ∈ X ⊔ rng y, lin a v ∈ X ⊔ rng y := by
  intro a ha v hv
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hXA a ha b hb) (rng_inv hA hy.mem ha c hc)

theorem IsPiece.finrank_sup (hy : IsPiece h p A X y) (hX : NondegOn (stdHermForm h n) X) :
    finrank K ↥(X ⊔ rng y) = finrank K X + finrank K (rng y) := by
  have hinf : X ⊓ rng y = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun v hv => hX v hv.1 fun m hm => ?_
    exact (hy.orth v hv.2 m hm).2
  have := Submodule.finrank_sup_add_finrank_inf_eq X (rng y)
  rw [hinf, finrank_bot, add_zero] at this
  exact this

theorem IsPiece.decomp (hy : IsPiece h p A X y) {c : ↥(unitarySU 2 f K n)}
    (hc : c ∈ A) (hcX : ∀ v ∈ X, lin c v = v) :
    ∃ k : ℕ, ∃ c' ∈ A, c = y ^ k * c' ∧ ∀ v ∈ X ⊔ rng y, lin c' v = v := by
  obtain ⟨k, hk⟩ := hy.cyc c hc
  refine ⟨k, (y ^ k)⁻¹ * c, A.mul_mem (A.inv_mem (A.pow_mem hy.mem k)) hc, by group, ?_⟩
  have hyk' : ∀ m : ℕ, ∀ v ∈ X, (lin y ^ m) v = v := by
    intro m v hv
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, Module.End.mul_apply, hy.triv v hv, ih]
  have hyk : ∀ v ∈ X, lin (y ^ k) v = v := fun v hv => by rw [SUTB.lin_pow]; exact hyk' k v hv
  have hinv : ∀ w, lin (y ^ k)⁻¹ (lin (y ^ k) w) = w := by
    intro w
    rw [← Module.End.mul_apply, ← SUTB.lin_mul, inv_mul_cancel, SUTB.lin_one]
    rfl
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [SUTB.lin_mul, Module.End.mul_apply, map_add, map_add, hcX a ha, hk b hb]
  congr 1
  · nth_rewrite 1 [← hyk a ha]
    exact hinv a
  · exact hinv b

end Piece

end SUTB

end CFSG.StandardType
