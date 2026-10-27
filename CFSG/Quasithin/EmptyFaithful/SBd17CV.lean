module

public import CFSG.Quasithin.EmptyFaithful.SBd14Glue
public import CFSG.Quasithin.EmptyFaithful.SBd16B4

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.centralizer_I_V₁ (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    (hidx : L.relIndex I = 12) {τ σ : G} (hτS : τ ∈ Sgp153 T V₁) (hτ2 : τ * τ = 1)
    (hτm : ∃ v ∈ V₁, τ * v ≠ v * τ) (hσS : σ ∈ Sgp153 T V₁)
    (hσc : ∀ v ∈ V₁, σ * v = v * σ) (hσL : σ ∉ L) :
    I ⊓ Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers σ := by
  classical
  have D0 := r.ctx.hyp.decomp
  have hLI : L ≤ I := le_of_mem_cComp r.ctx.c33.mem
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans r.ctx.inH.1.1
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hIN : I ≤ Subgroup.normalizer (V₁ : Set G) := SBd14.le_normalizer_of_eq_center r.hNL hV₁
  set C : Subgroup G := I ⊓ Subgroup.centralizer (V₁ : Set G) with hC
  have hCI : C ≤ I := inf_le_left
  have hLC : L ≤ C := le_inf hLI fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => (Subgroup.mem_centralizer_iff.mp (r.h1 hv) x hx).symm
  have hσC : σ ∈ C := ⟨hSI hσS, Subgroup.mem_centralizer_iff.mpr fun v hv => (hσc v hv).symm⟩
  have hAC : L ⊔ Subgroup.zpowers σ ≤ C := sup_le hLC ((Subgroup.zpowers_le).2 hσC)
  obtain ⟨d, hdY, hd3, hd1, -, v₀, hv₀, hv₀ne⟩ := r.exists_d_V₁ h113
  have hdI : d ∈ I := (le_sup_left.trans r.ctx.inH.1.1) hdY
  let Φ : ↥I →* MulAut ↥V₁ := (conjAct V₁).comp (Subgroup.inclusion hIN)
  have hΦ : ∀ (g : ↥I) (v : ↥V₁), ((Φ g v : ↥V₁) : G) = (g : G) * (v : G) * (g : G)⁻¹ := fun g v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V₁
      (Subgroup.inclusion le_rfl (Subgroup.inclusion hIN g)) v
  have hker : Φ.ker = C.subgroupOf I := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨v, hv⟩ : ↥V₁) : G)) h
      simp only [hΦ, MulAut.one_apply] at h1
      calc v * (g : G) = ((g : G) * v * (g : G)⁻¹) * (g : G) := by rw [h1]
        _ = (g : G) * v := by group
    · intro h
      ext v
      rw [hΦ, MulAut.one_apply]
      have h2 := Subgroup.mem_centralizer_iff.mp h.2 v v.2
      calc (g : G) * v * (g : G)⁻¹ = v * (g : G) * (g : G)⁻¹ := by rw [h2]
        _ = v := by group
  have hindex : C.relIndex I = Nat.card Φ.range := by
    rw [Subgroup.relIndex, ← hker]
    exact Subgroup.index_ker Φ
  have hdord : orderOf (Φ ⟨d, hdI⟩) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨d, hdI⟩ : ↥I) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      rw [this, map_one]
    · intro h
      apply hv₀ne
      have := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨v₀, hv₀⟩ : ↥V₁) : G)) h
      simpa [hΦ] using this
  have hτ1 : τ ≠ 1 := by
    obtain ⟨v, hv, hne⟩ := hτm
    intro h
    exact hne (by rw [h]; simp)
  have hτord : orderOf (Φ ⟨τ, hSI hτS⟩) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : (⟨τ, hSI hτS⟩ : ↥I) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hτ2)
      rw [this, map_one]
    · intro h
      obtain ⟨v, hv, hne⟩ := hτm
      apply hne
      have h1 := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨v, hv⟩ : ↥V₁) : G)) h
      simp only [hΦ, MulAut.one_apply] at h1
      calc τ * v = ((τ * v * τ⁻¹) * τ) := by group
        _ = v * τ := by rw [h1]
  have h2dvd : 2 ∣ Nat.card Φ.range := hτord ▸ Subgroup.orderOf_dvd_natCard Φ.range ⟨_, rfl⟩
  have h3dvd : 3 ∣ Nat.card Φ.range := hdord ▸ Subgroup.orderOf_dvd_natCard Φ.range ⟨_, rfl⟩
  have h6dvd : 6 ∣ Nat.card Φ.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
  have h6le : 6 ≤ C.relIndex I := by
    rw [hindex]
    exact Nat.le_of_dvd Nat.card_pos h6dvd
  have hmul := Subgroup.relIndex_mul_relIndex L C I hLC hCI
  rw [hidx] at hmul
  have hLCle : L.relIndex C ≤ 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hrel_pos : ∀ H K : Subgroup G, 0 < H.relIndex K := fun H K => by
    have h := Subgroup.relIndex_mul_card H K
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  set A : Subgroup G := L ⊔ Subgroup.zpowers σ with hA
  have hLA : L ≤ A := le_sup_left
  have hσA : σ ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  have hmul2 := Subgroup.relIndex_mul_relIndex L A C hLA hAC
  have hLA2 : 2 ≤ L.relIndex A := by
    have h1 : L.relIndex A ≠ 1 := by
      intro h
      exact hσL (Subgroup.relIndex_eq_one.mp h hσA)
    have := hrel_pos L A
    omega
  have hAC1 : A.relIndex C = 1 := by
    have hpos : 0 < A.relIndex C := hrel_pos A C
    nlinarith
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hAC1) hAC

end CFSG.Quasithin.SBd14
