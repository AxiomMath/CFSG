module

public import CFSG.Quasithin.Vol2.Ch11SecGFacts2
public import CFSG.Quasithin.Vol2.Ch11SecO5B
public import CFSG.Quasithin.Vol2.Ch11SecO5C
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.GorensteinWalter

namespace O5

theorem ringEquiv_eq_one_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  let φ : ZMod p ≃+* K := ZMod.ringEquivOfPrime K hp (by rwa [← Nat.card_eq_fintype_card])
  have h := RingHom.ext_zmod (σ.toRingHom.comp φ.toRingHom) φ.toRingHom
  ext x
  have hx := DFunLike.congr_fun h (φ.symm x)
  simpa using hx

variable {K : Type} [Field K] [Finite K]

theorem exists_inverted_torus {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {t : PGL2 K} (ht1 : t ≠ 1)
    (ht2 : t * t = 1) (b : Bool) :
    ∃ U : Subgroup (PGL2 K), IsCyclic U ∧
      Nat.card U = (if b then Nat.card K - 1 else Nat.card K + 1) ∧
      ∀ y ∈ U, t * y * t⁻¹ = y⁻¹ := by
  have hodd : Odd (Nat.card K) := by
    obtain ⟨q, n, -, hq, -, hn⟩ := hK
    rw [hn]
    exact hq.pow
  obtain ⟨U, w, hUcyc, hUcard, hwU, hwsq, hwinv, hUJ⟩ : ∃ U : Subgroup (PGL2 K), ∃ w : PGL2 K,
      IsCyclic U ∧ Nat.card U = (if b then Nat.card K - 1 else Nat.card K + 1) ∧ w ∉ U ∧
      w * w = 1 ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    cases b
    · obtain ⟨U, w, h1, h2, h3, h4, h5, h6⟩ := pgl2_nonsplit_torus_reflection_data hKcard
      exact ⟨U, w, h1, by simpa using h2, h3, h4, h5, h6 hodd⟩
    · obtain ⟨U, w, h1, h2, h3, h4, h5, h6⟩ := pgl2_split_torus_reflection_data K
      exact ⟨U, w, h1, by simpa using h2, h3, h4, h5, h6 hodd⟩
  obtain ⟨g, hg⟩ := exists_inverted_conj_of_reflection hK hcard ht1 ht2 hUcyc hwU hwsq hwinv hUJ
  refine ⟨U.map (MulAut.conj g).toMonoidHom, ?_, ?_, hg⟩
  · exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap U)
      ((MulAut.conj g).toMonoidHom.subgroupMap_surjective U)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard]

end O5

open O5

theorem factL2pInvol_holds : FactL2pInvol := by
  intro X _ _ p hp h11 h17 hX α hα1 hα2
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hX
  have hKp : Nat.card K = p := by simpa using hK
  let e : X ≃* PSL2 K :=
    e₀.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hKp, pow_one]⟩
  have hcard : 3 < Nat.card K := by omega
  set α' : MulAut (PSL2 K) := MulAut.congr e α with hα'
  set Φ := pGammaL2ToMulAutPSL2 K hodd hcard
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 1) (by rw [hKp, pow_one])
    hodd hcard α'
  have hγg : γ = SemidirectProduct.inl γ.left := by
    rw [← SemidirectProduct.inl_left_mul_inr_right γ, ringEquiv_eq_one_of_card_prime hp hKp γ.right,
      map_one, mul_one, SemidirectProduct.left_inl]
  set g : PGL2 K := γ.left
  have hΦg : Φ (SemidirectProduct.inl g) = α' := hγg ▸ hγ
  have hinj : Function.Injective Φ := pGammaL2ToMulAutPSL2_injective K hodd hcard
  have hg1 : g ≠ 1 := by
    intro h
    apply hα1
    apply (MulAut.congr e).injective
    rw [← hα', ← hΦg, h, map_one, map_one, map_one]
  have hg2 : g * g = 1 := by
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
    apply hinj
    rw [map_one, map_mul, map_mul, hΦg, ← pow_two, hα', ← map_pow, hα2, map_one]
    exact (map_one Φ).symm
  have hact : ∀ x : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL (α' x) =
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL x * g⁻¹ := fun x => by
    rw [← hΦg, pGammaL2ToMulAutPSL2_inl, toPGL_pgl2InnerAutPSL2_apply]
  obtain ⟨r, hr, hr5, hrd⟩ := exists_prime_five_le_dvd hp h11 h17
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨U, -, hUcard, hUinv, hrU⟩ : ∃ U : Subgroup (PGL2 K), IsCyclic U ∧
      (Nat.card U = Nat.card K - 1 ∨ Nat.card U = Nat.card K + 1) ∧
      (∀ y ∈ U, g * y * g⁻¹ = y⁻¹) ∧ r ∣ Nat.card U := by
    rcases hrd with h | h
    · obtain ⟨U, h1, h2, h3⟩ := exists_inverted_torus (by rw [hKp, pow_one] : Nat.card K = p ^ 1)
        hodd hcard hg1 hg2 true
      exact ⟨U, h1, Or.inl (by simpa using h2), h3, by simpa [h2, hKp] using h⟩
    · obtain ⟨U, h1, h2, h3⟩ := exists_inverted_torus (by rw [hKp, pow_one] : Nat.card K = p ^ 1)
        hodd hcard hg1 hg2 false
      exact ⟨U, h1, Or.inr (by simpa using h2), h3, by simpa [h2, hKp] using h⟩
  clear hUcard
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrU
  have hyr : orderOf (y : PGL2 K) = r := by rw [Subgroup.orderOf_coe, hy]
  have hJi := pgl2_psl2Range_index_eq_two K hodd
  have hyJ : (y : PGL2 K) ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    have hodd_r : Odd r := hr.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ := hodd_r
    have : (y : PGL2 K) = ((y : PGL2 K) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul, show (k + 1) * 2 = r + 1 by omega, pow_succ, ← hyr, pow_orderOf_eq_one,
        one_mul]
    rw [this]
    exact Subgroup.sq_mem_of_index_two hJi _
  obtain ⟨x₀, hx₀⟩ := hyJ
  have hinjP := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)
  refine ⟨e.symm x₀, ?_, ?_, r, hr, hr5, ?_⟩
  · intro h
    have h1 : x₀ = 1 := by simpa using congrArg e h
    have : (y : PGL2 K) = 1 := by rw [← hx₀, h1, map_one]
    rw [this, orderOf_one] at hyr
    exact hr.one_lt.ne hyr
  · have h1 : α' x₀ = x₀⁻¹ := hinjP (by rw [hact, hx₀, hUinv _ y.2, map_inv, hx₀])
    have h2 : e (α (e.symm x₀)) = x₀⁻¹ := by rw [← h1, hα', MulAut.congr_apply]; rfl
    rw [← map_inv, ← h2, e.symm_apply_apply]
  · have h1 : x₀ ^ r = 1 := hinjP (by rw [map_pow, hx₀, map_one, ← hyr, pow_orderOf_eq_one])
    rw [← map_pow, h1, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecG
