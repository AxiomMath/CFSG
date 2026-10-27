module

public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsSylowOf omegaOne)
open Matrix

section Uni

variable (K : Type*) [Field K]

def uniSL (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem uniSL_add (s t : K) : uniSL K (s + t) = uniSL K s * uniSL K t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def uniHomSL : Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun t := uniSL K (Multiplicative.toAdd t)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uniSL]
  map_mul' s t := uniSL_add K _ _

def uniPSL : Multiplicative K →* ProjectiveSpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))).comp (uniHomSL K)

theorem uniPSL_injective : Function.Injective (uniPSL K) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have hc : uniHomSL K t ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) :=
    (QuotientGroup.eq_one_iff _).mp ht
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
  obtain ⟨r, -, hr⟩ := hc
  have h01 : (Matrix.scalar (Fin 2) r) 0 1 = (uniSL K (Multiplicative.toAdd t)).1 0 1 :=
    congrFun (congrFun hr 0) 1
  simp [uniSL] at h01
  exact toAdd_eq_zero.mp h01.symm

theorem uniPSL_pow (p : ℕ) [CharP K p] (t : Multiplicative K) : (uniPSL K t) ^ p = 1 := by
  rw [← map_pow]
  have : t ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero]
  rw [this, map_one]

end Uni

section Aut

theorem subsingleton_ringEquiv_of_card_eq_prime {K : Type*} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p) : Subsingleton (K ≃+* K) := by
  have hord : addOrderOf (1 : K) = p := by
    have hdvd : addOrderOf (1 : K) ∣ p := hK ▸ addOrderOf_dvd_natCard (1 : K)
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · simp at h
    · exact h
  have htop : AddSubgroup.zmultiples (1 : K) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hK]
  refine ⟨fun σ τ => ?_⟩
  ext x
  have hx : x ∈ AddSubgroup.zmultiples (1 : K) := htop ▸ AddSubgroup.mem_top x
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  simp

end Aut

section Leaf

open CFSG.GorensteinWalter

theorem card_pGammaL2_primeField {p : ℕ} [Fact p.Prime] :
    Nat.card (PGammaL2 (GaloisField p 1)) = p * (p ^ 2 - 1) := by
  have hK : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 one_ne_zero
  have := subsingleton_ringEquiv_of_card_eq_prime hK
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    Nat.card_of_subsingleton (1 : GaloisField p 1 ≃+* GaloisField p 1), mul_one]
  have h := CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField (p := p) (m := 1) one_ne_zero
  simpa using h

theorem l2_charP {p a : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (ha : a ≠ 0)
    {H : Type} [Group H] [Finite H] (S : Subgroup H) [S.Normal]
    (e : S ≃* ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p a))
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hcard : Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) :
    a = 2 ∨ a = 3 := by
  have hp : p.Prime := Fact.out
  have hKcard : Nat.card (GaloisField p a) = p ^ a := GaloisField.card p a ha
  let ι : Multiplicative (GaloisField p a) →* H :=
    S.subtype.comp (e.symm.toMonoidHom.comp (uniPSL (GaloisField p a)))
  have hι : Function.Injective ι :=
    S.subtype_injective.comp (e.symm.injective.comp (uniPSL_injective _))
  have hwp : ∀ w : Multiplicative (GaloisField p a), w ^ p = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul, CharP.cast_eq_zero]
  have hιpow : ∀ w, ι w ^ p = 1 := fun w => by rw [← map_pow, hwp, map_one]
  have hQcard : Nat.card ι.range = p ^ a := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, ← hKcard]
    exact Nat.card_congr Multiplicative.toAdd
  have hQp : IsPGroup p ι.range := by
    rintro ⟨_, w, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hιpow w)⟩
  have hQexp : ∀ x ∈ ι.range, x ^ p = 1 := by
    rintro _ ⟨w, rfl⟩
    exact hιpow w
  have h1 := StrongP.card_le_card_omegaOne hP hQp hQexp
  have h3 : p ^ a ≤ p ^ 3 := by
    rw [← hQcard]
    refine h1.trans ?_
    rcases hcard with h | h <;> rw [h]
    · exact Nat.pow_le_pow_right hp.pos (by norm_num)
  have ha3 : a ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  by_contra hne
  push Not at hne
  have ha1 : a = 1 := by omega
  subst ha1
  have hdvdH : p ^ 2 ∣ Nat.card H := by
    have h2 : p ^ 2 ∣ Nat.card (omegaOne p P) := by
      rcases hcard with h | h <;> rw [h]
      exact pow_dvd_pow p (by norm_num)
    exact h2.trans (Subgroup.card_subgroup_dvd_card _)
  have hK1 : Nat.card (GaloisField p 1) = p := by simpa using hKcard
  have hodd : IsOddPrimePower (Nat.card (GaloisField p 1)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by simpa using hK1⟩
  have h4 : 3 < Nat.card (GaloisField p 1) := by omega
  have hsurj := pGammaL2ToMulAutPSL2_surjective (GaloisField p 1) hKcard hodd h4
  let eAut := pGammaL2EquivMulAutPSL2 (GaloisField p 1) hodd h4 hsurj
  have hφ : Function.Injective (normalPSL2ConjAction S (GaloisField p 1) e) :=
    (MulAut.congr e).injective.comp (conjNormal_injective_of_centralizer S hSc)
  have hHdvd : Nat.card H ∣ Nat.card (MulAut (PSL2 (GaloisField p 1))) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hAut : Nat.card (MulAut (PSL2 (GaloisField p 1))) = p * (p ^ 2 - 1) := by
    rw [← Nat.card_congr eAut.toEquiv]
    exact card_pGammaL2_primeField
  have h5 : p ^ 2 ∣ p * (p ^ 2 - 1) := hAut ▸ hdvdH.trans hHdvd
  have h6 : p ∣ p ^ 2 - 1 := by
    have : p * p ∣ p * (p ^ 2 - 1) := by simpa [sq] using h5
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
  have h7 : p ∣ (p ^ 2 - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
    exact dvd_pow_self p two_ne_zero
  exact hp.not_dvd_one ((Nat.dvd_add_right h6).mp h7)

end Leaf

end CFSG.RankThree.PartOne.CTP
