module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPiece

public section

namespace CFSG.StandardType

namespace NoOffOm

open Matrix Module Polynomial SUTB

section Gen

variable {K : Type} [Field K] {d : ℕ}

noncomputable abbrev glin (g : GL (Fin d) K) : Module.End K (Fin d → K) :=
  Matrix.toLinAlgEquiv' (g : Matrix (Fin d) (Fin d) K)

theorem glin_apply (g : GL (Fin d) K) (v : Fin d → K) :
    glin g v = (g : Matrix (Fin d) (Fin d) K) *ᵥ v :=
  Matrix.toLinAlgEquiv'_apply _ _

theorem glin_mul (g g' : GL (Fin d) K) : glin (g * g') = glin g * glin g' := by
  rw [glin, Units.val_mul, map_mul]

theorem glin_one : glin (1 : GL (Fin d) K) = 1 := by
  rw [glin, Units.val_one, map_one]

theorem glin_pow (g : GL (Fin d) K) (k : ℕ) : glin (g ^ k) = glin g ^ k := by
  rw [glin, Units.val_pow_eq_pow_val, map_pow]

theorem glin_injective : Function.Injective (glin : GL (Fin d) K → _) :=
  fun _ _ h => Units.ext (Matrix.toLinAlgEquiv'.injective h)

theorem glin_inv_apply (g : GL (Fin d) K) (v : Fin d → K) : glin g⁻¹ (glin g v) = v := by
  rw [← Module.End.mul_apply, ← glin_mul, inv_mul_cancel, glin_one]
  rfl

noncomputable abbrev grng (g : GL (Fin d) K) : Submodule K (Fin d → K) :=
  LinearMap.range (glin g - 1)

variable {σ : K →+* K}

structure GenMax (B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K) (Γ : Subgroup (GL (Fin d) K))
    (p : ℕ) (A : Subgroup (GL (Fin d) K)) : Prop where
  symm : B.IsSymm
  sep : ∀ v, (∀ w, B v w = 0) → v = 0
  prime : p.Prime
  ne_two : p ≠ 2
  le : A ≤ Γ
  pow : ∀ a ∈ A, a ^ p = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  max : ∀ g ∈ Γ, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A
  iso : ∀ g ∈ A, ∀ v w, B (glin g v) (glin g w) = B v w
  restr : ∀ (c : GL (Fin d) K) (hc : c ∈ A) (W : Submodule K (Fin d → K)) (hW : NondegOn B W)
    (hWA : ∀ a ∈ A, ∀ w ∈ W, glin a w ∈ W),
    ∃ g ∈ Γ, glin g = restrictElt hW (glin c) (hWA c hc)

variable {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

theorem GenMax.odd (hA : GenMax B Γ p A) : Odd p := hA.prime.odd_of_ne_two hA.ne_two

theorem GenMax.natCast_ne_zero [CharP K 2] (hA : GenMax B Γ p A) : (p : K) ≠ 0 := by
  rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one hA.odd]
  exact one_ne_zero

theorem GenMax.lin_pow (hA : GenMax B Γ p A) {a : GL (Fin d) K} (ha : a ∈ A) :
    glin a ^ p = 1 := by
  rw [← glin_pow, hA.pow a ha, glin_one]

theorem GenMax.lin_comm (hA : GenMax B Γ p A) {a b : GL (Fin d) K} (ha : a ∈ A) (hb : b ∈ A) :
    Commute (glin a) (glin b) := by
  rw [Commute, SemiconjBy, ← glin_mul, ← glin_mul, hA.comm a ha b hb]

theorem nondegOn_grng [CharP K 2] (hA : GenMax B Γ p A) {y : GL (Fin d) K} (hy : y ∈ A) :
    NondegOn B (grng y) :=
  nondegOn_range hA.symm hA.sep (hA.iso y hy) hA.odd (hA.lin_pow hy)

theorem grng_orth_eq_ker [CharP K 2] (hA : GenMax B Γ p A) {y : GL (Fin d) K} (hy : y ∈ A) :
    (grng y).orthogonalBilin B = LinearMap.ker (glin y - 1) :=
  range_orth_eq_ker hA.symm hA.sep (hA.iso y hy) hA.odd (hA.lin_pow hy)

theorem grng_inv (hA : GenMax B Γ p A) {y a : GL (Fin d) K} (hy : y ∈ A) (ha : a ∈ A) :
    ∀ u ∈ grng y, glin a u ∈ grng y := by
  rintro _ ⟨v, rfl⟩
  refine ⟨glin a v, ?_⟩
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, mul_sub, sub_mul, mul_one, one_mul,
    (hA.lin_comm hy ha).eq]

theorem eq_zero_of_mem_grng [CharP K 2] (hA : GenMax B Γ p A) {y : GL (Fin d) K} (hy : y ∈ A)
    {u : Fin d → K} (hu : u ∈ grng y) (hyu : glin y u = u) : u = 0 :=
  CFSG.RankThree.PartOne.OddIso.eq_zero_of_fixed_range hA.odd (hA.lin_pow hy) hu hyu

theorem grng_orth_of_triv (hA : GenMax B Γ p A) {y : GL (Fin d) K} (hy : y ∈ A)
    {X : Submodule K (Fin d → K)} (hyX : ∀ v ∈ X, glin y v = v) :
    ∀ u ∈ grng y, ∀ v ∈ X, B u v = 0 ∧ B v u = 0 := by
  rintro _ ⟨w, rfl⟩ v hv
  exact ⟨CFSG.RankThree.PartOne.OddIso.B_range_fix _ (hA.iso y hy) (hyX v hv) w,
    CFSG.RankThree.PartOne.OddIso.B_fix_range _ (hA.iso y hy) (hyX v hv) w⟩

theorem GenMax.exists_mem_restrict (hA : GenMax B Γ p A) {W : Submodule K (Fin d → K)}
    (hW : NondegOn B W) (hWA : ∀ a ∈ A, ∀ w ∈ W, glin a w ∈ W) {c : GL (Fin d) K}
    (hc : c ∈ A) :
    ∃ g ∈ A, (∀ w ∈ W, glin g w = glin c w) ∧ ∀ v ∈ W.orthogonalBilin B, glin g v = v := by
  obtain ⟨g, hgΓ, hg⟩ := hA.restr c hc W hW hWA
  have hp1 : 1 ≤ p := hA.prime.one_lt.le
  have horth : ∀ a ∈ A, ∀ z ∈ W.orthogonalBilin B, glin a z ∈ W.orthogonalBilin B := by
    intro a ha z hz
    exact CFSG.RankThree.PartOne.OddIso.orth_invariantH (hA.iso a ha) (hA.lin_pow ha) hp1
      (hWA a ha) hz
  refine ⟨g, hA.max g hgΓ ?_ ?_, ?_, ?_⟩
  · apply glin_injective
    rw [glin_pow, hg, restrictElt_pow_eq_one hW _ (hA.lin_pow hc), glin_one]
  · intro a ha
    apply glin_injective
    rw [glin_mul, glin_mul, hg]
    refine (restrictElt_comm hW _ (hWA a ha) (horth a ha) fun w _ => ?_).symm
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← glin_mul, ← glin_mul,
      hA.comm a ha c hc]
  · intro w hw
    rw [hg]
    exact restrictElt_apply_of_mem hW _ hw
  · intro v hv
    rw [hg]
    exact restrictElt_apply_of_mem_orth hW _ hv

end Gen

section Piece

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

structure GenIsPiece (B : (Fin d → K) →ₛₗ[σ] (Fin d → K) →ₗ[K] K) (p : ℕ)
    (A : Subgroup (GL (Fin d) K)) (X : Submodule K (Fin d → K)) (y : GL (Fin d) K) : Prop where
  mem : y ∈ A
  ne_one : y ≠ 1
  triv : ∀ v ∈ X, glin y v = v
  cyc : ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ grng y, glin c u = glin (y ^ k) u

omit [Finite K] [CharP K 2] in
theorem grng_ne_bot {y : GL (Fin d) K} (hy : y ≠ 1) : grng y ≠ ⊥ := by
  intro h0
  apply hy
  apply glin_injective
  rw [glin_one]
  exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp h0)

theorem exists_genIsPiece (hA : GenMax B Γ p A) {X : Submodule K (Fin d → K)}
    (hne : ∃ c ∈ A, c ≠ 1 ∧ ∀ v ∈ X, glin c v = v) : ∃ y, GenIsPiece B p A X y := by
  classical
  have hex : ∃ r, ∃ c ∈ A, c ≠ 1 ∧ (∀ v ∈ X, glin c v = v) ∧ finrank K (grng c) = r := by
    obtain ⟨c, hc, hc1, hcX⟩ := hne
    exact ⟨_, c, hc, hc1, hcX, rfl⟩
  obtain ⟨y, hyA, hy1, hyX, hyr⟩ := Nat.find_spec hex
  have hmin : ∀ c ∈ A, c ≠ 1 → (∀ v ∈ X, glin c v = v) →
      finrank K (grng y) ≤ finrank K (grng c) := by
    intro c hc hc1 hcX
    rw [hyr]
    exact Nat.find_min' hex ⟨c, hc, hc1, hcX, rfl⟩
  have hUnd := nondegOn_grng hA hyA
  have hUA : ∀ a ∈ A, ∀ u ∈ grng y, glin a u ∈ grng y := fun a ha => grng_inv hA hyA ha
  have hUX := grng_orth_of_triv hA hyA hyX
  have hXo : ∀ W : Submodule K (Fin d → K), W ≤ grng y → ∀ v ∈ X,
      v ∈ W.orthogonalBilin B :=
    fun W hW v hv => Submodule.mem_orthogonalBilin.mpr fun m hm => (hUX m (hW hm) v hv).1
  have hyp := hA.lin_pow hyA
  have hpK := hA.natCast_ne_zero
  refine ⟨y, hyA, hy1, hyX, fun c hc => ?_⟩
  obtain ⟨c', hc'A, hc'U, hc'o⟩ := hA.exists_mem_restrict hUnd hUA hc
  by_contra hcon
  push Not at hcon
  have hy1' : glin y ≠ 1 := fun h1 => hy1 (glin_injective (h1.trans glin_one.symm))
  obtain ⟨g, hg, hgd, hgker⟩ := OrdPNS.exists_irreducible_ker_ne_bot hA.prime hyp hy1'
  have : Fact (Irreducible g) := ⟨hg⟩
  set Wg := LinearMap.ker (aeval (glin y) g) with hWg
  have hWgU : Wg ≤ grng y := ker_aeval_le_range hpK hA.prime hgd
  have hyW : ∀ v ∈ Wg, glin y v ∈ Wg := OrdPNS.mapsTo_ker_aeval (Commute.refl _) g
  have hcW : ∀ v ∈ Wg, glin c' v ∈ Wg := OrdPNS.mapsTo_ker_aeval (hA.lin_comm hyA hc'A) g
  set y₁ := (glin y).restrict hyW with hy₁
  set c₁ := (glin c').restrict hcW with hc₁
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
    exact hv0 (Subtype.ext (eq_zero_of_mem_grng hA hyA (hWgU (Φ e).2)
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
  have hlinz : glin z = glin y ^ s * glin c' := by rw [hz, glin_mul, glin_pow]
  have hzv : glin z (Φ e : Fin d → K) = Φ e := by
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
  have hker := grng_orth_eq_ker hA hyA
  have hz1o : ∀ v ∈ (grng y).orthogonalBilin B, glin z v = v := by
    intro v hv
    have hyv : glin y v = v := by
      have h1 := hker ▸ hv
      exact sub_eq_zero.mp (LinearMap.mem_ker.mp h1)
    have hyv' : ∀ m : ℕ, (glin y ^ m) v = v := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ, Module.End.mul_apply, hyv, ih]
    rw [hlinz, Module.End.mul_apply, hc'o v hv, hyv' s]
  have hzX : ∀ v ∈ X, glin z v = v := fun v hv => hz1o v (hXo _ le_rfl v hv)
  have hlt := finrank_range_sub_one_lt hUnd hz1o (hWgU (Φ e).2)
    (fun h0 => hv0 (Subtype.ext h0)) hzv
  exact absurd (hmin z hzA hz1 hzX) (not_le.mpr hlt)

end Piece

end NoOffOm

end CFSG.StandardType
