module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.RankThree.GF2n.Stroth80.FieldModelFinal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem gamma_pow_conj {V : Subgroup G} {K : Type} [Field K] {γ : G → K} {τ : G} {a : K}
    (hτV : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V) (hγ : ∀ v ∈ V, γ (τ * v * τ⁻¹) = a * γ v) {v : G}
    (hv : v ∈ V) (k : ℕ) : γ (τ ^ k * v * (τ ^ k)⁻¹) = a ^ k * γ v := by
  have hws : ∀ i : ℕ, τ ^ i * v * (τ ^ i)⁻¹ ∈ V := by
    intro i
    induction i with
    | zero => simpa using hv
    | succ i ih =>
      have := hτV _ ih
      rwa [show τ * (τ ^ i * v * (τ ^ i)⁻¹) * τ⁻¹ = τ ^ (i + 1) * v * (τ ^ (i + 1))⁻¹ by
        rw [pow_succ']; group] at this
  induction k with
  | zero => simp
  | succ k ih =>
    have e : τ ^ (k + 1) * v * (τ ^ (k + 1))⁻¹ = τ * (τ ^ k * v * (τ ^ k)⁻¹) * τ⁻¹ := by
      rw [pow_succ']; group
    rw [e, hγ _ (hws k), ih, pow_succ]
    ring

theorem stroth_frobClause [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) : FrobClause M Z := by
  classical
  have H79 := H.toHyp79
  obtain ⟨g, hgV, hgQ⟩ := H79.exists_opposite
  obtain ⟨n, hVn, D, τ, a, hτM, hτH, hτU, hτo, hao, hγ, hψ, -⟩ :=
    H79.exists_mulData_torus hgV hgQ
  have hh := H79.toHyp218 hgV hgQ
  have hMZ : ∀ m ∈ M, m ∈ Subgroup.normalizer (Z : Set G) := fun m hm => hh.M_le_normalizer hm
  have hγ1 : D.γ 1 = 0 := (H79.modelCtx D).γ_one
  let f : ↥Z →* Multiplicative (GaloisField 2 n) :=
    { toFun := fun z => Multiplicative.ofAdd (D.γ (z : G))
      map_one' := by simp [hγ1]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (D.γ ((x : G) * (y : G))) =
          Multiplicative.ofAdd (D.γ (x : G)) * Multiplicative.ofAdd (D.γ (y : G))
        rw [D.γ_add _ x.2 _ y.2, ofAdd_add] }
  have hfb : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (D.eq_of_γ_eq x.2 y.2 (Multiplicative.ofAdd.injective hxy)),
      fun s => ?_⟩
    obtain ⟨a', ha', hs⟩ := D.γ_surj (Multiplicative.toAdd s)
    exact ⟨⟨a', ha'⟩, Multiplicative.toAdd.injective hs⟩
  refine ⟨⟨GaloisField 2 n, inferInstance, inferInstance, D.natCard_V.symm,
    MulEquiv.ofBijective f hfb, ?_⟩, ?_⟩
  · intro m hm
    obtain ⟨c, σ, hc, hcσ⟩ := FieldModel.semilinear_of_mem_M H79 hgV hgQ hVn D hm
    refine ⟨Units.mk0 c hc, σ, fun z w hw => ?_⟩
    show D.γ (w : G) = c * σ (D.γ (z : G))
    rw [hw]
    exact hcσ z z.2
  · have hN : ((H0 M Z).subgroupOf M).Normal := by
      refine ⟨fun x hx m => ?_⟩
      have hx' : (x : G) ∈ H0 M Z := hx
      show ((m * x * m⁻¹ : ↥M) : G) ∈ H0 M Z
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      · exact M.mul_mem (M.mul_mem m.2 x.2) (M.inv_mem m.2)
      · have hzm : (m : G)⁻¹ * z * (m : G) ∈ Z :=
          (Tim79.mem_iff_conj_inv_of_normalizer (hMZ m m.2) z).mp hz
        have h1 := Subgroup.mem_centralizer_iff.mp hx'.2 _ hzm
        calc z * ((m : G) * (x : G) * (m : G)⁻¹)
            = (m : G) * ((m : G)⁻¹ * z * (m : G) * (x : G)) * (m : G)⁻¹ := by group
          _ = (m : G) * ((x : G) * ((m : G)⁻¹ * z * (m : G))) * (m : G)⁻¹ := by rw [h1]
          _ = ((m : G) * (x : G) * (m : G)⁻¹) * z := by group
    haveI := hN
    let τ' : ↥M := ⟨τ, hτM⟩
    have hτN : τ ^ (2 ^ n - 1) = 1 := by rw [← hτo]; exact pow_orderOf_eq_one τ
    have hord : orderOf (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M) = 2 ^ n - 1 := by
      apply Nat.dvd_antisymm
      · apply orderOf_dvd_of_pow_eq_one
        rw [← QuotientGroup.mk_pow, show τ' ^ (2 ^ n - 1) = 1 from Subtype.ext hτN,
          QuotientGroup.mk_one]
      · rw [← hao]
        apply orderOf_dvd_of_pow_eq_one
        have hk : (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M) ^
            orderOf (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M) = 1 :=
          pow_orderOf_eq_one _
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
        have hk' : τ ^ orderOf (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M) ∈ H0 M Z := hk
        obtain ⟨z₀, hz₀, hz₀1⟩ := D.γ_surj 1
        have e1 := gamma_pow_conj (fun v hv =>
          (Tim79.mem_iff_conj_of_normalizer (hMZ τ hτM) v).mp hv) hγ hz₀
          (orderOf (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M))
        have e2 : τ ^ orderOf (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M) * z₀ *
            (τ ^ orderOf (QuotientGroup.mk τ' : ↥M ⧸ (H0 M Z).subgroupOf M))⁻¹ = z₀ := by
          have := Subgroup.mem_centralizer_iff.mp hk'.2 z₀ hz₀
          rw [← this]; group
        rw [e2, hz₀1, mul_one] at e1
        exact e1.symm
    rw [hVn]
    show 2 ^ n - 1 ∣ Nat.card (↥M ⧸ (H0 M Z).subgroupOf M)
    rw [← hord]
    exact orderOf_dvd_natCard _

end CFSG.RankThree.GF2n.Stroth80
