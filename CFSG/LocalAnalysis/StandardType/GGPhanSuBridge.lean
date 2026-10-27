module

public import CFSG.RankThree.PartOne.CTP.PhanFour
public import CFSG.LieType.Universal.Catalog

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

@[expose] noncomputable def suidGLMap {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K')
    (n : ℕ) : GL (Fin n) K →* GL (Fin n) K' :=
  Units.map
    (e.mapMatrix : Matrix (Fin n) (Fin n) K ≃+* Matrix (Fin n) (Fin n) K').toRingHom.toMonoidHom

theorem coe_suidGLMap {K K' : Type*} [Field K] [Field K'] (e : K ≃+* K') {n : ℕ}
    (A : GL (Fin n) K) :
    ((suidGLMap e n A : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') =
      (A : Matrix (Fin n) (Fin n) K).map e :=
  rfl

theorem conjTr_map_ringEquiv {K K' : Type*} [Field K] [Field K'] {σ : K ≃+* K}
    {σ' : K' ≃+* K'} (e : K ≃+* K') (he : ∀ c, e (σ c) = σ' (e c)) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : conjTr σ' (A.map e) = (conjTr σ A).map e := by
  ext i j
  simp [conjTr, he]

theorem suidGLMap_mem_SUid {K K' : Type*} [Field K] [Field K'] {σ : K ≃+* K} {σ' : K' ≃+* K'}
    (e : K ≃+* K') (he : ∀ c, e (σ c) = σ' (e c)) {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ SUid σ n) : suidGLMap e n A ∈ SUid σ' n := by
  obtain ⟨hdet, hiso⟩ := hA
  refine ⟨?_, ?_⟩
  · rw [coe_suidGLMap, show (A : Matrix (Fin n) (Fin n) K).map e =
        (e : K →+* K').mapMatrix (A : Matrix (Fin n) (Fin n) K) from rfl, ← RingHom.map_det, hdet,
        map_one]
  · rw [coe_suidGLMap, conjTr_map_ringEquiv e he, ← Matrix.map_mul, hiso,
      Matrix.map_one _ (map_zero e) (map_one e)]

@[expose] noncomputable def suidCongr {K K' : Type*} [Field K] [Field K'] {σ : K ≃+* K}
    {σ' : K' ≃+* K'} (e : K ≃+* K') (he : ∀ c, e (σ c) = σ' (e c)) (n : ℕ) :
    SUid σ n ≃* SUid σ' n where
  toFun A := ⟨suidGLMap e n (A : GL (Fin n) K), suidGLMap_mem_SUid e he A.2⟩
  invFun B := ⟨suidGLMap e.symm n (B : GL (Fin n) K'),
    suidGLMap_mem_SUid e.symm (fun c => by
      apply e.injective
      rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]) B.2⟩
  left_inv A := Subtype.ext (Units.ext (by
    show Matrix.map (Matrix.map ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) e) e.symm = _
    ext i j
    simp))
  right_inv B := Subtype.ext (Units.ext (by
    show Matrix.map (Matrix.map ((B : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') e.symm) e = _
    ext i j
    simp))
  map_mul' A B := Subtype.ext (map_mul (suidGLMap e n) (A : GL (Fin n) K) (B : GL (Fin n) K))

theorem nonempty_su_equiv_lieUniversalPSU
    {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (K : Type) [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    Nonempty (Su K p f n ≃* (lieUniversal .PSU n p f hp).K) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · exfalso
      have : Nat.card K = 1 := by simpa using hK
      exact (Finite.one_lt_card (α := K)).ne' this
    · exact h
  have hG : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf
  haveI := Fintype.ofFinite K
  haveI : Finite (GaloisField p (2 * f)) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero 2 (pow_ne_zero f hp.ne_zero))
  haveI := Fintype.ofFinite (GaloisField p (2 * f))
  have hcard : Fintype.card K = Fintype.card (GaloisField p (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hG]
  let e : K ≃+* GaloisField p (2 * f) := FiniteField.ringEquivOfCardEq hcard
  have he : ∀ c, e (unitaryInvolution K p f c) =
      unitaryInvolution (GaloisField p (2 * f)) p f (e c) := fun c => by
    rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  obtain ⟨P, hP⟩ := exists_wittMatrix hG n
  have hL : lieUniversal .PSU n p f hp =
      ⟨Unitary.SU (unitaryInvolution (GaloisField p (2 * f)) p f) n,
        Unitary.rootDatum hG n⟩ := by
    simp only [lieUniversal, hf, ↓reduceDIte]
  rw [hL]
  exact ⟨(suidCongr e he n).trans (conjEquiv P hP).symm⟩

theorem weakPhanA_lieUniversalPSU
    {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (K : Type) [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : 4 ≤ p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    ∃ θ : (lieUniversal .PSU (n + 1) p f hp).K →* X, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (lieUniversal .PSU (n + 1) p f hp).K := by
  obtain ⟨θ, hθs, hθk⟩ :=
    CFSG.RankThree.PartOne.CTP.weakPhan_recognition_of_four_le K p f hK hq hn hW
  obtain ⟨e⟩ := nonempty_su_equiv_lieUniversalPSU hp K hK (n + 1)
  refine ⟨θ.comp e.symm.toMonoidHom, hθs.comp e.symm.surjective, fun g hg => ?_⟩
  have h1 : e.symm g ∈ Subgroup.center (Su K p f (n + 1)) := hθk hg
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro h
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact h1 (e.symm h)

end CFSG.ClassicalInvolution.Phan
