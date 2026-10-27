module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
import CFSG.RankThree.GF2n.Stroth80.Sec123Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.exists_H0_rep_of_mem_Ebar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {τ : Mbar M Q} (hτ : τ ∈ Ebar M Q Z B) :
    ∃ e : ↥M, (QuotientGroup.mk e : Mbar M Q) = τ ∧ IsA2 Q Z (e : G) ∧ (e : G) ∈ H0 M Z := by
  obtain ⟨⟨e, rfl, hA⟩, x, hx⟩ := hτ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp hx
  have h1 : (QuotientGroup.mk (y * e * y⁻¹) : Mbar M Q) = QuotientGroup.mk l := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hle.symm
  have h2 := QuotientGroup.eq.mp h1
  rw [Subgroup.mem_subgroupOf] at h2 hl
  have h3 : ((y * e * y⁻¹ : ↥M) : G) ∈ LB M Q B := by
    have e1 : ((y * e * y⁻¹ : ↥M) : G) =
        (l : G) * (((y * e * y⁻¹ : ↥M) : G)⁻¹ * (l : G))⁻¹ := by group
    rw [e1]
    exact (LB M Q B).mul_mem hl ((LB M Q B).inv_mem (Subgroup.mem_sup_left h2))
  have h4 : (e : G) ∈ H0 M Z := by
    have h5 := hc.conj_mem_H0 (M.inv_mem y.2) (hc.LB_le_H0 h3)
    have e2 : (y : G)⁻¹ * ((y * e * y⁻¹ : ↥M) : G) * ((y : G)⁻¹)⁻¹ = (e : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e2] at h5
  exact ⟨e, rfl, hA, h4⟩

theorem isOrthA2_of_IsA2_of_mem_H0
    {K : Type} [Field K] [Finite K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (H : StrothHyp M Q Z) (hD : GlobalModelData M Q Z γ M₀)
    (hKZ : Nat.card K = Nat.card Z) {a : G} (haH : a ∈ H0 M Z) (hA : IsA2 Q Z a)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = T (M₀.π x)) :
    Smith81.IsOrthA2 M₀.toQuadraticForm T := by
  have haM : a ∈ M := haH.1
  have haz : ∀ z ∈ Z, a * z * a⁻¹ = z := fun z hz => by
    have hc := Subgroup.mem_centralizer_iff.mp haH.2 z hz
    rw [← hc]
    group
  obtain ⟨S, hSπ, hSQf, -⟩ := hD.linear_of_centralizes haM haz
  have hTS : ∀ e, T e = S e := by
    intro e
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    rw [← hT x hx, ← hSπ x hx]
  have hK : 1 < Nat.card K := by
    rw [hKZ]
    exact lt_of_lt_of_le (by norm_num) H.q4
  have ha : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hA.1 x).mp hx
  have ha' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := fun x hx => by
    have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set G)).inv_mem hA.1)
      x).mp hx
    simpa using h
  have hA2 := (isA2_iff M₀ hD.reg hKZ hK T ha ha' hT).mp hA
  refine ⟨?_, ?_, hA2.2.2.1, hA2.2.2.2⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun e => by
      rw [hTS e]
      exact hSQf e
  · refine LinearEquiv.ext fun e => ?_
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    have h2 : a * x * a⁻¹ ∈ Q := ha x hx
    have h3 : M₀.π (a * (a * x * a⁻¹) * a⁻¹) = T (T (M₀.π x)) := by
      rw [hT _ h2, hT x hx]
    have hsq : a * a ∈ Q := by simpa [pow_two] using hA.2.2.1
    have e1 : a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
    have h4 : M₀.π ((a * a) * x * (a * a)⁻¹) = M₀.π x :=
      Tim79.QuadModel.pi_conj_self (M₀ := M₀) hsq hx
    show T (T (M₀.π x)) = M₀.π x
    rw [← h3, e1, h4]

theorem Ctx.isOrthA2_of_mem_Ebar [Finite G]
    [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (hKZ : Nat.card K = Nat.card Z) {h : G} (hh : h ∈ H0 M Z)
    (hτ : (QuotientGroup.mk (⟨h, hh.1⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : ∀ x ∈ Q, M₀.π (h * x * h⁻¹) = T (M₀.π x)) :
    Smith81.IsOrthA2 M₀.toQuadraticForm T := by
  obtain ⟨e, he, hAe, heH⟩ := hc.exists_H0_rep_of_mem_Ebar hτ
  have hq' : ((e : G)⁻¹ * h) ∈ Q := by
    have h2 := QuotientGroup.eq.mp he
    simpa [Subgroup.mem_subgroupOf] using h2
  have hq : h⁻¹ * (e : G) ∈ Q := by
    have := Q.inv_mem hq'
    simpa [mul_inv_rev] using this
  set q : G := h⁻¹ * (e : G) with hqdef
  have hqQ : q ∈ Q := by rw [hqdef]; exact hq
  have hπ : ∀ x ∈ Q, M₀.π ((e : G) * x * (e : G)⁻¹) = T (M₀.π x) := by
    intro x hx
    have hex : (e : G) * x * (e : G)⁻¹ = h * (q * x * q⁻¹) * h⁻¹ := by
      rw [hqdef]
      group
    have hqxQ : q * x * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hqQ hx) (Q.inv_mem hqQ)
    rw [hex, hT _ hqxQ, Tim79.QuadModel.pi_conj_self (M₀ := M₀) hqQ hx]
  exact isOrthA2_of_IsA2_of_mem_H0 hc.hyp hD hKZ heH hAe hπ

theorem Ctx.orderOf_mul_of_mem_Ebar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {τ τ' : Mbar M Q}
    (hτ : τ ∈ Ebar M Q Z B) (hτ' : τ' ∈ Ebar M Q Z B) :
    orderOf (τ * τ') ∣ 4 ∨ Odd (orderOf (τ * τ')) := by
  obtain ⟨e, he, hAe, heH⟩ := hc.exists_H0_rep_of_mem_Ebar hτ
  obtain ⟨e', he', hAe', he'H⟩ := hc.exists_H0_rep_of_mem_Ebar hτ'
  obtain ⟨n, γ, M₀, hZn, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hD
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hZn
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    omega
  have hKZ : Nat.card (GaloisField 2 n) = Nat.card Z := by
    rw [GaloisField.card 2 n hn, ← hZn]
  set T : M₀.E ≃ₗ[GaloisField 2 n] M₀.E := φ ⟨(e : G), heH⟩ with hTdef
  set T' : M₀.E ≃ₗ[GaloisField 2 n] M₀.E := φ ⟨(e' : G), he'H⟩ with hT'def
  have hτe : (QuotientGroup.mk (⟨(e : G), heH.1⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [show (⟨(e : G), heH.1⟩ : ↥M) = e from Subtype.ext rfl, he]
    exact hτ
  have hτe' : (QuotientGroup.mk (⟨(e' : G), he'H.1⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
    rw [show (⟨(e' : G), he'H.1⟩ : ↥M) = e' from Subtype.ext rfl, he']
    exact hτ'
  have hTe : Smith81.IsOrthA2 M₀.toQuadraticForm T :=
    hc.isOrthA2_of_mem_Ebar hD hKZ heH hτe (fun x hx => hφπ ⟨(e : G), heH⟩ x hx)
  have hTe' : Smith81.IsOrthA2 M₀.toQuadraticForm T' :=
    hc.isOrthA2_of_mem_Ebar hD hKZ he'H hτe' (fun x hx => hφπ ⟨(e' : G), he'H⟩ x hx)
  have hord : orderOf ((QuotientGroup.mk e : Mbar M Q) * (QuotientGroup.mk e' : Mbar M Q)) =
      orderOf (T * T') := by
    refine orderOf_eq_orderOf_iff.mpr fun k => ?_
    have hcoe : ((((⟨(e : G), heH⟩ : ↥(H0 M Z)) * ⟨(e' : G), he'H⟩) ^ k :
        ↥(H0 M Z)) : G) = (((e * e') ^ k : ↥M) : G) := by simp
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, ← map_mul, ← map_pow,
      hφker (((⟨(e : G), heH⟩ : ↥(H0 M Z)) * ⟨(e' : G), he'H⟩) ^ k), hcoe]
  rw [← he, ← he', hord]
  rcases Smith81.orderOf_mul_isOrthA2 (polarBilin_toQuadraticForm_nondegenerate M₀) hTe hTe'
    with ⟨h4, -⟩ | hodd
  · exact Or.inl h4
  · exact Or.inr hodd

end CFSG.RankThree.GF2n.Stroth80
