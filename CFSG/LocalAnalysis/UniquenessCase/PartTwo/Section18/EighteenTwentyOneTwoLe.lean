module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneModelQTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin

private def toAddEquiv_T3J2 {W : Type} [CommGroup W] {F : Type} [Add F]
    (ψ : W ≃* Multiplicative (Fin 4 → F)) : W ≃ (Fin 4 → F) :=
  ψ.toEquiv.trans Multiplicative.toAdd

private lemma toAddEquiv_T3J2_mul {W : Type} [CommGroup W] {F : Type} [Add F]
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (a b : W) :
    toAddEquiv_T3J2 ψ (a * b) = toAddEquiv_T3J2 ψ a + toAddEquiv_T3J2 ψ b := by
  simp [toAddEquiv_T3J2, toAdd_mul]

private def permConj_T3J2 {W : Type} [CommGroup W] {F : Type}
    (e : W ≃ (Fin 4 → F)) (A : Subgroup (MulAut W)) : ↥A →* Equiv.Perm (Fin 4 → F) :=
  { toFun := fun a => e.permCongr ((a : MulAut W).toEquiv)
    map_one' := by
      ext x
      simp [Equiv.permCongr_apply]
    map_mul' := by
      intro a b
      ext x
      simp [Equiv.permCongr_apply, MulAut.mul_apply] }

private lemma permConj_T3J2_apply {W : Type} [CommGroup W] {F : Type}
    (e : W ≃ (Fin 4 → F)) (A : Subgroup (MulAut W)) (a : ↥A) (w : W) :
    permConj_T3J2 e A a (e w) = e ((a : MulAut W) w) := by
  simp [permConj_T3J2, Equiv.permCongr_apply]

private lemma permConj_T3J2_add {W : Type} [CommGroup W] {F : Type} [AddCommGroup F]
    (e : W ≃ (Fin 4 → F)) (he : ∀ a b : W, e (a * b) = e a + e b)
    (A : Subgroup (MulAut W)) (h : ↥A) (x y : Fin 4 → F) :
    permConj_T3J2 e A h (x + y) = permConj_T3J2 e A h x + permConj_T3J2 e A h y := by
  obtain ⟨v, rfl⟩ := e.surjective x
  obtain ⟨w, rfl⟩ := e.surjective y
  calc permConj_T3J2 e A h (e v + e w) = permConj_T3J2 e A h (e (v * w)) := by rw [he]
    _ = e ((h : MulAut W) (v * w)) := permConj_T3J2_apply e A h (v * w)
    _ = e ((h : MulAut W) v * (h : MulAut W) w) := by rw [map_mul]
    _ = e ((h : MulAut W) v) + e ((h : MulAut W) w) := he _ _
    _ = permConj_T3J2 e A h (e v) + permConj_T3J2 e A h (e w) := by
        rw [← permConj_T3J2_apply e A h v, ← permConj_T3J2_apply e A h w]

private lemma natCoords_e_T3J2 {W : Type} [CommGroup W] {F : Type} [Field F] {n : ℕ}
    {H : Subgroup (MulAut W)} (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F))
    (ψ : W ≃* Multiplicative (Fin 4 → F)) (hψ : NatCoordsSU4 H n F ε ψ) (l : ↥H) (s : W) :
    toAddEquiv_T3J2 ψ ((l : MulAut W) s) =
      ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ toAddEquiv_T3J2 ψ s := by
  have h := hψ l s
  calc toAddEquiv_T3J2 ψ ((l : MulAut W) s)
      = Multiplicative.toAdd (ψ ((l : MulAut W) s)) := rfl
    _ = Multiplicative.toAdd (Multiplicative.ofAdd
          (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
            Multiplicative.toAdd (ψ s))) := by rw [h]
    _ = ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ toAddEquiv_T3J2 ψ s := by
        simp [toAddEquiv_T3J2]

private lemma normalizer_transport_T3J2 {W : Type} [CommGroup W]
    {F : Type} [Field F] {n : ℕ} {H Y A : Subgroup (MulAut W)}
    (ε : ↥H ≃* ↥(StatedSU 4 (2 ^ n) F)) (ψ : W ≃* Multiplicative (Fin 4 → F))
    (hψ : NatCoordsSU4 H n F ε ψ) (hYN : Y ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hAY : A ≤ Y) :
    ∀ h : ↥A, ∀ g ∈ StatedSU 4 (2 ^ n) F, ∃ g' ∈ StatedSU 4 (2 ^ n) F,
      ∀ x : Fin 4 → F,
        permConj_T3J2 (toAddEquiv_T3J2 ψ) A h⁻¹
            (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
          ((g' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
            permConj_T3J2 (toAddEquiv_T3J2 ψ) A h⁻¹ x := by
  let e : W ≃ (Fin 4 → F) := toAddEquiv_T3J2 ψ
  let ρ : ↥A →* Equiv.Perm (Fin 4 → F) := permConj_T3J2 e A
  have hρ : ∀ (a : ↥A) (w : W), ρ a (e w) = e ((a : MulAut W) w) :=
    fun a w => permConj_T3J2_apply e A a w
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
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by simp [l]
  have hls : e ((l : MulAut W) s) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s := by
    rw [natCoords_e_T3J2 ε ψ hψ l s, hgl]
  have harg : (φ * (l : MulAut W) * φ⁻¹) (φ s) = φ ((l : MulAut W) s) := by
    simp [MulAut.mul_apply]
  calc ρ h⁻¹ (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s)
      = ρ h⁻¹ (e ((l : MulAut W) s)) := by rw [hls]
    _ = e (φ ((l : MulAut W) s)) := hρ h⁻¹ ((l : MulAut W) s)
    _ = e ((φ * (l : MulAut W) * φ⁻¹) (φ s)) := by rw [harg]
    _ = ((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) *ᵥ e (φ s) :=
        natCoords_e_T3J2 ε ψ hψ ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ (φ s)
    _ = ((ε ⟨φ * (l : MulAut W) * φ⁻¹, hmem⟩ : GL (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) *ᵥ ρ h⁻¹ (e s) := by rw [← hρ h⁻¹ s]

private lemma fixed_of_index_le_two_T3J2 {W : Type} [CommGroup W] [Finite W]
    {F : Type} {A : Subgroup (MulAut W)} {k : ℕ} (hAab : IsElemAbelian2 A)
    (hAfix : ∀ B : Subgroup (MulAut W), B ≤ A → E3.mQuot A B < k → fixV B = fixV A)
    (hk : 2 ≤ k) (e : W ≃ (Fin 4 → F)) (ρ : ↥A →* Equiv.Perm (Fin 4 → F))
    (hρ : ∀ (a : ↥A) (w : W), ρ a (e w) = e ((a : MulAut W) w)) :
    ∀ K : Subgroup ↥A, K.index ≤ 2 → ∀ x : Fin 4 → F,
      (∀ k ∈ K, ρ k x = x) → ∀ h : ↥A, ρ h x = x := by
  intro K hK x hx h
  let K' : Subgroup (MulAut W) := K.map A.subtype
  have hK'le : K' ≤ A := Subgroup.map_subtype_le K
  have hrel : K'.relIndex A = K.index := by
    have h' := Subgroup.relIndex_map_map_of_injective (f := A.subtype) K ⊤ A.subtype_injective
    rwa [Subgroup.map_top, A.range_subtype, Subgroup.relIndex_top_right] at h'
  have hmq : E3.mQuot A K' < k := by
    have hdvd : K.index ∣ Nat.card ↥A := Subgroup.index_dvd_card K
    have hcard : Nat.card ↥A = 2 ^ rk ↥A :=
      card_eq_two_pow_of_isPGroup (IsElemAbelian2.isPGroup hAab)
    have hdvd' : K.index ∣ 2 ^ rk ↥A := by rwa [← hcard]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd'
    have hjle : j ≤ 1 := by
      by_contra hjgt
      have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    show padicValNat 2 (K'.relIndex A) < k
    rw [hrel, hj, padicValNat.prime_pow]
    omega
  have hfixA : fixV K' = fixV A := hAfix K' hK'le hmq
  have hw : e (e.symm x) = x := e.apply_symm_apply x
  have hfixK : e.symm x ∈ fixV K' := by
    rw [mem_fixV]
    intro k hk
    obtain ⟨k₀, hk₀K, rfl⟩ := Subgroup.mem_map.1 hk
    have h1 : ρ k₀ x = x := hx k₀ hk₀K
    rw [← hw] at h1
    rw [hρ k₀ (e.symm x)] at h1
    exact e.injective h1
  have hfixA' : e.symm x ∈ fixV A := hfixA ▸ hfixK
  rw [← hw]
  rw [hρ h (e.symm x)]
  exact congrArg e ((mem_fixV.1 hfixA') h h.2)

private lemma one_le_of_card_eq_sq_T3J2 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hFcard : Nat.card F = (2 ^ n) ^ 2) : 1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  rw [h0] at hFcard
  simp at hFcard
  have hlt := Finite.one_lt_card (α := F)
  omega

theorem le_of_mem_aSet_of_two_le_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H Y A : Subgroup (MulAut W)} {n k : ℕ} (hk : 2 ≤ k) (hNat : NatSUn H ⊤ ⊥ 4 n)
    (hYN : Y ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : A ∈ E3.aSet k Y) :
    A ≤ H := by
  obtain ⟨F, hFld, hFfin, hFcard, ε, ψ, hψ⟩ := exists_natCoords_of_natSUn hNat
  letI := hFld
  letI := hFfin
  obtain ⟨hAY, -, hAab, hAfix⟩ := hA
  have hn1 : 1 ≤ n := one_le_of_card_eq_sq_T3J2 hFcard
  let e : W ≃ (Fin 4 → F) := toAddEquiv_T3J2 ψ
  let ρ : ↥A →* Equiv.Perm (Fin 4 → F) := permConj_T3J2 e A
  have hρ : ∀ (a : ↥A) (w : W), ρ a (e w) = e ((a : MulAut W) w) :=
    fun a w => permConj_T3J2_apply e A a w
  have hH2 : ∀ h : ↥A, h * h = 1 := by
    intro h
    apply Subtype.ext
    show (h : MulAut W) * (h : MulAut W) = 1
    simpa [pow_two] using hAab.2 (h : MulAut W) h.2
  have hadd : ∀ (h : ↥A) (x y : Fin 4 → F), ρ h (x + y) = ρ h x + ρ h y :=
    fun h x y => permConj_T3J2_add e (toAddEquiv_T3J2_mul ψ) A h x y
  have hN := normalizer_transport_T3J2 ε ψ hψ hYN hAY
  have hQ := fixed_of_index_le_two_T3J2 hAab hAfix hk e ρ hρ
  have hMQ := model_Q_two (n := n) hFcard hn1 hH2 ρ hadd hN hQ
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
            simp [e, toAddEquiv_T3J2]
      _ = Multiplicative.toAdd (ψ (((ε.symm ⟨g, hg⟩ : ↥H) : MulAut W) w)) := by
            rw [h]
            simp [e, toAddEquiv_T3J2]
      _ = e (((ε.symm ⟨g, hg⟩ : ↥H) : MulAut W) w) := rfl
  rw [haeq]
  exact (ε.symm ⟨g, hg⟩).2

theorem le_of_mem_aSet_two_of_natSUn {W : Type} [CommGroup W] [Finite W]
    {H Y A : Subgroup (MulAut W)} {n : ℕ} (hn : 2 ≤ n) (hNat : NatSUn H ⊤ ⊥ 4 n)
    (hYN : Y ≤ Subgroup.normalizer (H : Set (MulAut W))) (hA : A ∈ E3.aSet (2 * n - 2) Y) :
    A ≤ H :=
  le_of_mem_aSet_of_two_le_of_natSUn (k := 2 * n - 2) (by omega) hNat hYN hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
