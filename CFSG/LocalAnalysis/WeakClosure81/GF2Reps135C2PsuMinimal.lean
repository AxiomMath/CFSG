module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLabelData
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Finset Polynomial
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.HardMathSupport.GuralnickMalle
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MonoidAlgebra TensorProduct Polynomial

private theorem c2psumin_chiEps_iterate {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type}
    [Field k] {n f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 0 < f) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) (p : ℕ) {h : SU (unitaryInvolution F 2 f) n}
    (hh : h ∈ ⨆ i, levelTorus (unitaryInvolution F 2 f) i) :
    chiEps φ₀ ((rotEps hf)^[p] ε) h = chiEps φ₀ ε h ^ 2 ^ p := by
  have hHdiag : (⨆ i, levelTorus (unitaryInvolution F 2 f) i) ≤
      diagSubgroup (unitaryInvolution F 2 f) n :=
    iSup_le fun i => levelTorus_le_diagSubgroup i
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', ← chiEps_sq hF hf φ₀ ((rotEps hf)^[p] ε) (hHdiag hh), ih,
      ← pow_mul]
    congr 1

private theorem c2psumin_not_mem_zero {f n : ℕ} (hf : 0 < f) (hn : 0 < n)
    {ε : Fin f → Finset (Fin n)} (h0 : ∀ r, (⟨0, hn⟩ : Fin n) ∉ ε r) (p : ℕ) (r : Fin f) :
    (⟨0, hn⟩ : Fin n) ∉ ((rotEps hf)^[p] ε) r := by
  induction p generalizing r with
  | zero => simpa using h0 r
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    by_cases hr : (r : ℕ) = 0
    · rw [rotEps, dif_pos hr, mem_image_labelStar_iff]
      have hz : labelStar (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ := by
        ext
        simp [labelStar]
      rw [hz]
      exact ih _
    · rw [rotEps, dif_neg hr]
      exact ih _

private theorem c2psumin_isFullNode_iterate {f n : ℕ} (hf : 0 < f)
    (ε : Fin f → Finset (Fin n)) (p : ℕ) (r : Fin (n / 2)) :
    IsFullNode ((rotEps hf)^[p] ε) r ↔ IsFullNode ε r := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', isFullNode_rotEps_iff hf ((rotEps hf)^[p] ε) r, ih]

theorem w135c2_psu_zero_not_mem_of_hasUnitaryLabel {m f : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel hm hK ρ ε) :
    ∀ r, (⟨0, by omega⟩ : Fin m) ∉ ε r := by
  obtain ⟨k, _, _, _, φ₀, ζ, hζ, y, χ, μ, htype, h0, -⟩ := hε
  exact h0

theorem w135c2_psu_char_of_hasUnitaryLabel {m f : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel hm hK ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) = 2 ^ s) :
    ∃ (k : Type) (_ : Field k) (φ₀ : K →+* k),
      (∀ h ∈ ⨆ i, levelTorus (unitaryInvolution K 2 f) i,
        chiEps φ₀ ε h ^ 2 ^ s = chiEps φ₀ ε h) ∧
      ∀ p : ℕ, 0 < p → (∀ h ∈ ⨆ i, levelTorus (unitaryInvolution K 2 f) i,
        chiEps φ₀ ε h ^ 2 ^ p = chiEps φ₀ ε h) → s ≤ p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hchar, halg, φ₀, ζ, hζ, y, χ, μ, htype, h0, hχ, -⟩ := hε
  have hH : (curtisDatum hK m hm ζ hζ).H = ⨆ i, levelTorus (unitaryInvolution K 2 f) i := by
    unfold curtisDatum
    rfl
  have hχε : ∀ h ∈ ⨆ i, levelTorus (unitaryInvolution K 2 f) i, χ h = chiEps φ₀ ε h := by
    intro h hh
    rw [← hH] at hh
    exact hχ h hh
  refine ⟨k, hk, φ₀, ?_, ?_⟩
  · intro h hh
    have hh' : h ∈ (curtisDatum hK m hm ζ hζ).H := hH ▸ hh
    have h1 := isCurtisType_chi_pow_card (ρ := ρ) (D := curtisDatum hK m hm ζ hζ) (k := k)
      htype hh'
    rw [hE] at h1
    rw [← hχε h hh]
    exact h1
  · intro p hp0 hp
    let E := Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m)) ρ.asModule
    have hrange := isCurtisType_fieldRange_eq_closure (ρ := ρ)
      (D := curtisDatum hK m hm ζ hζ) (k := k) htype
    let C : Subfield k := TauCeti.frobeniusFixedSubfield k 2 p
    haveI : Finite C := TauCeti.finite_frobeniusFixedSubfield k 2 p hp0.ne'
    have hle : (algebraMap E k).fieldRange ≤ C := by
      rw [hrange]
      refine Subfield.closure_le.mpr ?_
      rintro x ⟨h, hh, rfl⟩
      have hh' : h ∈ ⨆ i, levelTorus (unitaryInvolution K 2 f) i := hH ▸ hh
      change χ h ∈ TauCeti.frobeniusFixedSubfield k 2 p
      rw [TauCeti.mem_frobeniusFixedSubfield, hχε h hh']
      exact hp h hh'
    have hmem : ∀ x : E, algebraMap E k x ∈ C :=
      fun x => hle (RingHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    have hcardE : Nat.card E ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun x : E => (⟨algebraMap E k x, hmem x⟩ : C))
        (fun x y hxy => (algebraMap E k).injective (Subtype.ext_iff.mp hxy))
    have hCroot : (C : Set k) = (X ^ 2 ^ p - X : k[X]).rootSet k :=
      TauCeti.coe_frobeniusFixedSubfield_eq_rootSet k 2 p hp0.ne'
    have hcardC : Nat.card C ≤ 2 ^ p := by
      change (C : Set k).ncard ≤ 2 ^ p
      rw [hCroot]
      calc (Set.ncard ((X ^ 2 ^ p - X : k[X]).rootSet k))
          ≤ (X ^ 2 ^ p - X : k[X]).natDegree :=
            Polynomial.ncard_rootSet_le (X ^ 2 ^ p - X : k[X]) k
        _ = 2 ^ p := FiniteField.X_pow_card_pow_sub_X_natDegree_eq k hp0.ne' (by norm_num)
    have hle2 : 2 ^ s ≤ 2 ^ p := by
      rw [← hE]
      exact hcardE.trans hcardC
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle2

theorem w135c2_psu_rotate_of_hasUnitaryLabel {m f : ℕ} (hm : 3 ≤ m) (hf : 0 < f) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel (by omega : 2 ≤ m) hK ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) = 2 ^ s) :
    (rotEps hf)^[s] ε = ε := by
  classical
  obtain ⟨k, hk, φ₀, hpow, -⟩ := w135c2_psu_char_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε hE
  have hn : 0 < m := by omega
  have h0 := w135c2_psu_zero_not_mem_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε
  symm
  refine eq_of_chiEps_eq hK hn φ₀ h0 (c2psumin_not_mem_zero hf hn h0 s) (fun h hh => ?_)
    (fun r => (c2psumin_isFullNode_iterate hf ε s r).symm)
  rw [c2psumin_chiEps_iterate hK hf φ₀ ε s hh]
  exact (hpow h hh).symm

theorem w135c2_psu_minimal_of_hasUnitaryLabel {m f : ℕ} (hm : 3 ≤ m) (hf : 0 < f) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel (by omega : 2 ≤ m) hK ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) = 2 ^ s) :
    ∀ p : ℕ, 0 < p → p < s → (rotEps hf)^[p] ε ≠ ε := by
  intro p hp0 hps hrotp
  obtain ⟨k, hk, φ₀, -, hmin⟩ := w135c2_psu_char_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε hE
  have hsp : s ≤ p := hmin p hp0 fun h hh => by
    have h1 := c2psumin_chiEps_iterate hK hf φ₀ ε p hh
    rw [hrotp] at h1
    exact h1.symm
  omega

theorem w135c2_psu_le_of_selfDual {m f : ℕ} (hm : 3 ≤ m) (hf : 0 < f) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel (by omega : 2 ≤ m) hK ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) = 2 ^ s) (hsd : ∀ r, (ε r).image labelStar = ε r) :
    s ≤ f := by
  classical
  obtain ⟨k, hk, φ₀, -, hmin⟩ := w135c2_psu_char_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε hE
  refine hmin f hf fun h hh => ?_
  have hHdiag : (⨆ i, levelTorus (unitaryInvolution K 2 f) i) ≤
      diagSubgroup (unitaryInvolution K 2 f) m :=
    iSup_le fun i => levelTorus_le_diagSubgroup i
  have h1 := chiEps_comp_unitaryInvolution hK φ₀ ε (hHdiag hh)
  have h2 : chiEps (φ₀.comp (unitaryInvolution K 2 f).toRingHom) ε h =
      chiEps φ₀ ε h ^ 2 ^ f := by
    simp only [chiEps, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      unitaryInvolution_apply, map_pow]
  have h3 : (fun r => (ε r).image labelStar) = ε := funext hsd
  rw [← h2, h1, h3]

end CFSG.LocalAnalysis.WeakClosure81
