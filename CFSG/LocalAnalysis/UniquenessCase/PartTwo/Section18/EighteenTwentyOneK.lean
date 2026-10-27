module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16QModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC

theorem le_of_mem_aSet_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H Y A : Subgroup (MulAut W)} {n : ℕ} (hNat : NatSUn H ⊤ ⊥ 4 n)
    (hYN : Y ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : A ∈ E3.aSet (2 * n) Y) :
    A ≤ H := by
  obtain ⟨F, hFld, hFfin, hFcard, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  letI := hFld
  letI := hFfin
  obtain ⟨hAY, -, hAab, hAfix⟩ := hA
  have hn : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hFcard
    simp at hFcard
    have hlt := Finite.one_lt_card (α := F)
    omega
  let e : W ≃ (Fin 4 → F) := ψ.toEquiv.trans Multiplicative.toAdd
  have he_mul : ∀ a b : W, e (a * b) = e a + e b := by
    intro a b
    simp [e, toAdd_mul]
  let ρ : ↥A →* Equiv.Perm (Fin 4 → F) :=
    { toFun := fun a => e.permCongr ((a : MulAut W).toEquiv)
      map_one' := by
        ext x
        simp [Equiv.permCongr_apply]
      map_mul' := by
        intro a b
        ext x
        simp [Equiv.permCongr_apply, MulAut.mul_apply] }
  have hρ : ∀ (a : ↥A) (w : W), ρ a (e w) = e ((a : MulAut W) w) := by
    intro a w
    simp [ρ, Equiv.permCongr_apply]
  have hH2 : ∀ h : ↥A, h * h = 1 := by
    intro h
    apply Subtype.ext
    show (h : MulAut W) * (h : MulAut W) = 1
    simpa [pow_two] using hAab.2 (h : MulAut W) h.2
  have hadd : ∀ (h : ↥A) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y := by
    intro h x y
    obtain ⟨v, rfl⟩ := e.surjective x
    obtain ⟨w, rfl⟩ := e.surjective y
    calc ρ h (e v + e w) = ρ h (e (v * w)) := by rw [he_mul]
      _ = e ((h : MulAut W) (v * w)) := hρ h (v * w)
      _ = e ((h : MulAut W) v * (h : MulAut W) w) := by rw [map_mul]
      _ = e ((h : MulAut W) v) + e ((h : MulAut W) w) := he_mul _ _
      _ = ρ h (e v) + ρ h (e w) := by rw [← hρ h v, ← hρ h w]
  have hN : ∀ h : ↥A, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F,
      ∀ x : Fin 4 → F,
        ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
          ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ x := by
    intro h g hg
    let l : ↥H := ε.symm ⟨g, hg⟩
    let φ : MulAut W := ((h⁻¹ : ↥A) : MulAut W)
    have hmem : φ * (l : MulAut W) * φ⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.1 (hYN (hAY (h⁻¹).2)) (l : MulAut W)).1 l.2
    refine ⟨((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : ↥(StatedSU 4 (2 ^ n) F)) :
      GL (Fin 4) F), (ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩).2, ?_⟩
    intro x
    obtain ⟨s, rfl⟩ := e.surjective x
    have hgl : ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      simp [l]
    have hls : e ((l : MulAut W) s) =
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s := by
      have h := hψ l s
      calc e ((l : MulAut W) s) = Multiplicative.toAdd (ψ ((l : MulAut W) s)) := rfl
        _ = Multiplicative.toAdd (Multiplicative.ofAdd
            (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s)) := by simp [e, h]
        _ = ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s := by simp
        _ = ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s := by rw [hgl]
    have harg : (φ * (l : MulAut W) * φ⁻¹) (φ s) = φ ((l : MulAut W) s) := by
      simp [MulAut.mul_apply]
    have hm : e ((φ * (l : MulAut W) * φ⁻¹) (φ s)) =
        ((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) *ᵥ e (φ s) := by
      have h := hψ ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ (φ s)
      rw [harg] at h
      calc e ((φ * (l : MulAut W) * φ⁻¹) (φ s)) =
          Multiplicative.toAdd (ψ ((φ * (l : MulAut W) * φ⁻¹) (φ s))) := rfl
        _ = Multiplicative.toAdd (ψ (φ ((l : MulAut W) s))) := by rw [harg]
        _ = Multiplicative.toAdd (Multiplicative.ofAdd
            (((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) *ᵥ Multiplicative.toAdd (ψ (φ s)))) := by rw [h]
        _ = ((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
              Matrix (Fin 4) (Fin 4) F) *ᵥ e (φ s) := by simp [e]
    calc ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s)
        = ρ h⁻¹ (e ((l : MulAut W) s)) := by rw [hls]
      _ = e (φ ((l : MulAut W) s)) := hρ h⁻¹ ((l : MulAut W) s)
      _ = e ((φ * (l : MulAut W) * φ⁻¹) (φ s)) := by rw [harg]
      _ = ((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) *ᵥ e (φ s) := hm
      _ = ((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
            Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ (e s) := by rw [← hρ h⁻¹ s]
  have hQ : ∀ K : Subgroup ↥A, K.index < Nat.card F → ∀ x : Fin 4 → F,
      (∀ k ∈ K, ρ k x = x) → ∀ h : ↥A, ρ h x = x := by
    intro K hK x hx h
    let K' : Subgroup (MulAut W) := K.map A.subtype
    have hK'le : K' ≤ A := Subgroup.map_subtype_le K
    have hrel : K'.relIndex A = K.index := by
      have h' := Subgroup.relIndex_map_map_of_injective (f := A.subtype) K ⊤ A.subtype_injective
      rwa [Subgroup.map_top, A.range_subtype, Subgroup.relIndex_top_right] at h'
    have hF2 : Nat.card F = 2 ^ (2 * n) := by
      rw [hFcard, ← pow_mul, mul_comm]
    have hmq : E3.mQuot A K' < 2 * n := by
      have hdvd : K.index ∣ Nat.card ↥A := Subgroup.index_dvd_card K
      have hcard : Nat.card ↥A = 2 ^ rk ↥A :=
        card_eq_two_pow_of_isPGroup (IsElemAbelian2.isPGroup hAab)
      have hdvd' : K.index ∣ 2 ^ rk ↥A := by rwa [← hcard]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
      have hjlt : j < 2 * n := by
        have h2 : (2 : ℕ) ^ j < 2 ^ (2 * n) := by
          rw [← hj, ← hF2]
          exact hK
        exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h2
      show padicValNat 2 (K'.relIndex A) < 2 * n
      rw [hrel, hj, padicValNat.prime_pow]
      exact hjlt
    have hfixA : fixV K' = fixV A := hAfix K' hK'le hmq
    have hw : e (ψ.symm (Multiplicative.ofAdd x)) = x := by simp [e]
    have hfixK : ψ.symm (Multiplicative.ofAdd x) ∈ fixV K' := by
      rw [mem_fixV]
      intro k hk
      obtain ⟨k₀, hk₀K, rfl⟩ := Subgroup.mem_map.1 hk
      have h1 : ρ k₀ x = x := hx k₀ hk₀K
      rw [← hw] at h1
      rw [hρ k₀ (ψ.symm (Multiplicative.ofAdd x))] at h1
      exact e.injective h1
    have hfixA' : ψ.symm (Multiplicative.ofAdd x) ∈ fixV A := hfixA ▸ hfixK
    rw [← hw]
    rw [hρ h (ψ.symm (Multiplicative.ofAdd x))]
    exact congrArg e ((mem_fixV.1 hfixA') h h.2)
  have hMQ := model_Q (n := n) hFcard hn hH2 ρ hadd hN hQ
  intro a ha
  obtain ⟨g, hg, hgx⟩ := hMQ ⟨a, ha⟩
  have haeq : a = ((ε.symm ⟨g, hg⟩ : ↥H) : MulAut W) := by
    apply MulEquiv.ext
    intro w
    apply e.injective
    rw [← hρ ⟨a, ha⟩ w, hgx]
    have h := hψ (ε.symm ⟨g, hg⟩) w
    have hgl : ((ε (ε.symm ⟨g, hg⟩) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by simp
    calc ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e w
        = ((ε (ε.symm ⟨g, hg⟩) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e w := by
            rw [hgl]
      _ = Multiplicative.toAdd (Multiplicative.ofAdd
            (((ε (ε.symm ⟨g, hg⟩) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e w)) := by
            simp [e]
      _ = Multiplicative.toAdd (ψ (((ε.symm ⟨g, hg⟩ : ↥H) : MulAut W) w)) := by
            rw [h]
            simp [e]
      _ = e (((ε.symm ⟨g, hg⟩ : ↥H) : MulAut W) w) := rfl
  rw [haeq]
  exact (ε.symm ⟨g, hg⟩).2

@[expose] def K_18_21_i2 : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H Y A : Subgroup (MulAut W)) (n : ℕ),
    2 ≤ n → IsSUn ↥H 4 n → NatSUn H ⊤ ⊥ 4 n →
    H ≤ Y → Y ≤ Subgroup.normalizer (H : Set (MulAut W)) →
    A ∈ E3.aSet (2 * n - 2) Y → 4 * n - 1 ≤ rk ↥A →
    A ≤ H ∧ rk ↥A ≤ 4 * n ∧
      (∃ a₁ a₂ : MulAut W,
        a₁ ∈ A ∧ a₂ ∈ A ∧
          rk ↥(commV (Subgroup.zpowers a₁)) = 2 * n ∧
          rk ↥(fixV (Subgroup.zpowers a₁)) = 6 * n ∧
          rk ↥(commV (Subgroup.zpowers a₂)) = 2 * n ∧
          rk ↥(fixV (Subgroup.zpowers a₂)) = 6 * n ∧
          fixV (Subgroup.zpowers a₁) ≠ fixV (Subgroup.zpowers a₂) ∧
          fixV (Subgroup.zpowers a₁) ⊔ fixV (Subgroup.zpowers a₂) = ⊤) ∧
      (rk ↥A = 4 * n → ∃ (N B₁ B₂ : Subgroup (MulAut W)),
        A = N ∧ N ≤ H ∧ IsElemAbelian2 N ∧ rk ↥N = 4 * n ∧
          B₁ ≤ N ∧ B₂ ≤ N ∧ rk ↥B₁ = n ∧ rk ↥B₂ = n ∧
          rk ↥(fixV B₁) = 6 * n ∧ rk ↥(fixV B₂) = 6 * n ∧
          fixV B₁ ≠ fixV B₂ ∧ fixV B₁ ⊔ fixV B₂ = ⊤)

theorem exists_rk_fixV_eq_two_mul_mul_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H Y : Subgroup (MulAut W)} {n : ℕ} (hNat : NatSUn H ⊤ ⊥ 4 n) (hYH : Y ≤ H) :
    ∃ k : ℕ, rk ↥(fixV Y) = 2 * n * k := by
  obtain ⟨F, hFld, hFfin, hFcard, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  letI := hFld
  letI := hFfin
  let S : Submodule F (Fin 4 → F) :=
    { carrier := {x | ψ.symm (Multiplicative.ofAdd x) ∈ fixV Y}
      add_mem' := by
        intro x y hx hy
        change ψ.symm (Multiplicative.ofAdd (x + y)) ∈ fixV Y
        have h : ψ.symm (Multiplicative.ofAdd (x + y)) =
            ψ.symm (Multiplicative.ofAdd x) * ψ.symm (Multiplicative.ofAdd y) := by
          simp [map_mul]
        rw [h]
        exact (fixV Y).mul_mem hx hy
      zero_mem' := by
        change ψ.symm (Multiplicative.ofAdd (0 : Fin 4 → F)) ∈ fixV Y
        rw [mem_fixV]
        intro y hy
        simp
      smul_mem' := by
        intro c x hx
        change ψ.symm (Multiplicative.ofAdd x) ∈ fixV Y at hx
        change ψ.symm (Multiplicative.ofAdd (c • x)) ∈ fixV Y
        rw [mem_fixV] at hx ⊢
        intro y hy
        let l : ↥H := ⟨y, hYH hy⟩
        have hxl : y (ψ.symm (Multiplicative.ofAdd x)) =
            ψ.symm (Multiplicative.ofAdd x) := hx y hy
        have hε : ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x = x := by
          have h := hψ l (ψ.symm (Multiplicative.ofAdd x))
          rw [hxl] at h
          simp at h
          exact (Multiplicative.ofAdd.injective h).symm
        have h2 : ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (c • x) = c • x := by
          rw [Matrix.mulVec_smul, hε]
        have h := hψ l (ψ.symm (Multiplicative.ofAdd (c • x)))
        apply ψ.injective
        rw [h]
        simp [h2] }
  have hcard : Nat.card ↥(fixV Y) = Nat.card S := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun w => ⟨Multiplicative.toAdd (ψ (w : W)), ?_⟩
        invFun := fun x => ⟨ψ.symm (Multiplicative.ofAdd (x : Fin 4 → F)), x.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · change ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (ψ (w : W)))) ∈ fixV Y
      have h : ψ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (ψ (w : W)))) = (w : W) := by
        simp
      rw [h]
      exact w.2
    · intro w
      apply Subtype.ext
      simp
    · intro x
      apply Subtype.ext
      simp
  refine ⟨Module.finrank F S, ?_⟩
  unfold rk
  rw [hcard, Module.natCard_eq_pow_finrank (K := F) (V := S), hFcard, ← pow_mul, ← pow_mul,
    padicValNat.prime_pow]
  ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
