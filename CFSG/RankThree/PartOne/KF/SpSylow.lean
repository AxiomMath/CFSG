module

public import CFSG.RankThree.PartOne.KF.SpRev
public import CFSG.GroupTheory.WeirSylow.Symplectic
public import CFSG.RankThree.PartOne.KF.D8Matrix
public import CFSG.RankThree.PartOne.KF.GramMat

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Universal.Unitary Matrix CFSG.Assembly.LowTwoRank

variable {p : ℕ} {K : Type} [Field K]

@[expose] def dvec4 (a b : Kˣ) : Fin 4 → Kˣ := ![a, b, b⁻¹, a⁻¹]

@[expose] def dvec4Hom : Kˣ × Kˣ →* (Fin 4 → Kˣ) where
  toFun x := dvec4 x.1 x.2
  map_one' := by
    funext i
    fin_cases i <;> simp [dvec4]
  map_mul' x y := by
    funext i
    fin_cases i <;> simp [dvec4, mul_comm]

theorem d8Vec_four (v : D8Mod p K) :
    d8Vec 4 v = dvec4 ((v.1 : rootsOfUnity p K) : Kˣ) ((v.2 : rootsOfUnity p K) : Kˣ) := by
  funext i
  fin_cases i <;> simp [d8Vec, d8Cls, d8Ev, dvec4]

theorem diagU_dvec4_mem_spRev [CharP K 2] (a b : Kˣ) :
    (diagU (dvec4 a b) : GL (Fin 4) K) ∈ spRev K := by
  rw [mem_spRev_iff]
  have := diagU_gram (RingEquiv.refl K) (d := dvec4 a b) (fun i => by
    fin_cases i <;> simp [dvec4])
  simpa [conjTr] using this

theorem exists_conj_le_sylow {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (P : Subgroup M) (hP : Nat.card P = p ^ (Nat.card M).factorization p)
    (X : Subgroup M) (hX : ∀ x ∈ X, x ^ p = 1) :
    ∃ g : M, ∀ x ∈ X, g * x * g⁻¹ ∈ P := by
  have hXp : IsPGroup p X := fun x => ⟨1, by simpa using Subtype.ext (hX x x.2)⟩
  obtain ⟨Q, hXQ⟩ := hXp.exists_le_sylow
  let P' : Sylow p M := Sylow.ofCard P hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P' Q
  refine ⟨g⁻¹, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup M) := hXQ hx
  rw [← hg] at hxQ
  rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at hxQ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  simpa [MulAut.smul_def] using hxQ

variable [CharP K 2]

@[expose] noncomputable def spDiag (K : Type) [Field K] [CharP K 2] : Kˣ × Kˣ →* ↥(spRev K) :=
  MonoidHom.codRestrict (diagUHom.comp dvec4Hom) (spRev K)
    (fun x => diagU_dvec4_mem_spRev x.1 x.2)

theorem coe_spDiag (x : Kˣ × Kˣ) :
    ((spDiag K x : ↥(spRev K)) : GL (Fin 4) K) = diagU (dvec4 x.1 x.2) := rfl

theorem spDiag_injective : Function.Injective (spDiag K) := by
  intro x y h
  have h1 : dvec4 x.1 x.2 = dvec4 y.1 y.2 :=
    diagU_injective (congrArg (fun z : ↥(spRev K) => (z : GL (Fin 4) K)) h)
  refine Prod.ext ?_ ?_
  · simpa [dvec4] using congrFun h1 0
  · simpa [dvec4] using congrFun h1 1

omit [CharP K 2] in
theorem factorization_card_spRev [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K - 1) :
    (Nat.card ↥(spRev K)).factorization p = 2 * (Nat.card Kˣ).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  rw [← Nat.card_congr (spRevEquiv K).toEquiv]
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hq1 : (Fintype.card K : ZMod p) = 1 := by
    have h1 : (((Nat.card K - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hq, sub_eq_zero] at h1
    rw [Fintype.card_eq_nat_card]
    simpa using h1
  have hpK : ¬ p ∣ Fintype.card K := by
    intro h
    have h1 : (Fintype.card K : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hq1] at h1
    exact one_ne_zero h1
  rw [CFSG.GroupTheory.WeirSylow.factorization_card_statedSp (hp.odd_of_ne_two hp2) K hpK 2,
    hq1, orderOf_one]
  have h2 : padicValNat p 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h3 : (Nat.card Kˣ).factorization p = padicValNat p (Fintype.card K - 1) := by
    rw [Nat.card_units, Nat.factorization_def _ hp, Fintype.card_eq_nat_card]
  simp [h2, h3, mul_comm]

theorem exists_conj_into_d8Tor_sp [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card K - 1) (X : Subgroup ↥(spRev K)) (hX : ∀ x ∈ X, x ^ p = 1) :
    ∃ g : ↥(spRev K), ∀ x ∈ X, g * x * g⁻¹ ∈ (d8Tor p K 4).subgroupOf (spRev K) := by
  have : Fact p.Prime := ⟨hp⟩
  let S : Sylow p Kˣ := default
  let Sg : Subgroup Kˣ := (S : Subgroup Kˣ)
  have hSg : Nat.card Sg = p ^ (Nat.card Kˣ).factorization p := Sylow.card_eq_multiplicity S
  let embS : ↥Sg × ↥Sg →* ↥(spRev K) :=
    (spDiag K).comp (Sg.subtype.prodMap Sg.subtype)
  have hembS : Function.Injective embS := by
    refine spDiag_injective.comp ?_
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hPcard : Nat.card embS.range = p ^ (Nat.card ↥(spRev K)).factorization p := by
    rw [factorization_card_spRev hp hp2 hdvd,
      Nat.card_congr (MonoidHom.ofInjective hembS).toEquiv.symm, Nat.card_prod, hSg, ← sq,
      ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := exists_conj_le_sylow embS.range hPcard X hX
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, hst⟩ := hg x hx
  have hxp : (g * x * g⁻¹) ^ p = 1 := by
    rw [conj_pow, hX x hx, mul_one, mul_inv_cancel]
  have hs : (s : Kˣ) ^ p = 1 ∧ (t : Kˣ) ^ p = 1 := by
    have h1 : embS (s, t) ^ p = 1 := by rw [hst]; exact hxp
    rw [← map_pow] at h1
    have h2 : (s, t) ^ p = 1 := hembS (h1.trans (map_one embS).symm)
    have h3 : s ^ p = 1 := congrArg Prod.fst h2
    have h4 : t ^ p = 1 := congrArg Prod.snd h2
    exact ⟨by simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h3,
      by simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h4⟩
  rw [Subgroup.mem_subgroupOf, ← hst]
  refine ⟨(⟨(s : Kˣ), (mem_rootsOfUnity p _).mpr hs.1⟩,
    ⟨(t : Kˣ), (mem_rootsOfUnity p _).mpr hs.2⟩), ?_⟩
  show diagU (d8Vec 4 _) = _
  rw [d8Vec_four]
  rfl

end CFSG.RankThree.PartOne.KFU
