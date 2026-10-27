module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFixE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

section Certs

theorem exists_inner_normalForm_E6
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K - 1)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (α : MulAut (adjointGroup .E6 K)) (hα : α ^ p = 1) :
    ∃ (x : adjointGroup .E6 K) (σ : K ≃+* K), σ ^ p = 1 ∧
      ∀ h : adjointGroup .E6 K, (α h : ModGL .E6 K) =
        (x : ModGL .E6 K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E6 K) *
          (x : ModGL .E6 K)⁻¹ := by
  obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgασε⟩ := exists_conj_mul_exactNormalAut (K := K) (Or.inl rfl) α
  have hexpr : ∀ h : adjointGroup .E6 K, (α h : ModGL .E6 K) = (g : ModGL .E6 K) *
      rootDiagUnit .E6 a * exactQ .E6 K (ε : ℕ) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E6 K) * (exactQ .E6 K (ε : ℕ))⁻¹ *
          (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹ := by
    intro h
    rw [hgασε, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_exactNormalAut, Subgroup.coe_inv]
    simp only [mul_assoc]
  obtain hθ := hΘ α g a σ ε hexpr
  have hθp : (Θ α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  have hσp : σ ^ p = 1 := by
    have h := congrArg (MonoidHom.fst (RingAut K) (Multiplicative (ZMod (exactE .E6)))) hθp
    rw [map_pow, map_one, hθ] at h
    simpa using h
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have he' : ((ε : ℕ) : ZMod (exactE .E6)) = 0 := by
    have h2 : Multiplicative.ofAdd (((ε : ℕ) : ZMod (exactE .E6))) ^ p = 1 := by
      have h := congrArg (MonoidHom.snd (RingAut K) (Multiplicative (ZMod (exactE .E6)))) hθp
      rw [map_pow, map_one, hθ] at h
      simpa using h
    have h3 : p • (((ε : ℕ) : ZMod (exactE .E6))) = 0 := by
      rw [← ofAdd_nsmul] at h2
      exact ofAdd_eq_one.mp h2
    have h4 : ((p : ℕ) : ZMod (exactE .E6)) * ((ε : ℕ) : ZMod (exactE .E6)) = 0 := by
      simpa [nsmul_eq_mul] using h3
    have hpcast : ((p : ℕ) : ZMod (exactE .E6)) = 1 := hpodd.natCast_zmod_two
    rw [hpcast, one_mul] at h4
    exact h4
  have hε0 : (ε : ℕ) = 0 := by
    have he : ((ε : ℕ) : ZMod 2) = 0 := he'
    have hdvd : 2 ∣ (ε : ℕ) := (ZMod.natCast_eq_zero_iff (ε : ℕ) 2).mp he
    have hlt : (ε : ℕ) < 2 := by simpa [exactE] using ε.isLt
    omega
  have hq : exactQ .E6 K (ε : ℕ) = 1 := by
    rw [hε0]
    exact exactQ_zero .E6 K
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  let b : Fin Tag.E6.rank → Kˣ := fun l => (powCoprime hcop).symm (a l)
  have hb3 : a = fun l => b l ^ 3 := by
    funext l
    rw [← powCoprime_apply hcop (b l)]
    exact (Equiv.apply_symm_apply _ _).symm
  have hd : rootDiagUnit .E6 a ∈ torusGroup .E6 K := by
    rw [hb3]
    exact TableBExc.rootDiagUnit_cube_mem_torusGroup_E6 b
  have hdC : rootDiagUnit .E6 a ∈ adjointGroup .E6 K := torusGroup_le_adjointGroup hd
  refine ⟨⟨(g : ModGL .E6 K) * rootDiagUnit .E6 a,
    Subgroup.mul_mem (H := adjointGroup .E6 K) g.2 hdC⟩, σ, hσp, ?_⟩
  intro h
  rw [hexpr h, hq]
  simp only [inv_one, mul_one, mul_inv_rev, mul_assoc]

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
