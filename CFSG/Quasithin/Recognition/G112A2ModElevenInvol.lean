module

public import CFSG.Quasithin.Recognition.G112A2ModElevenRank
public import CFSG.Milestones.ASVolI.G11
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut

public section

noncomputable section

namespace CFSG.Quasithin.G112A2.Eleven

open scoped MatrixGroups

theorem congr_mulAutConj_eleven {G H : Type*} [Group G] [Group H] (e : G ≃* H) (y : G) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext m
  simp [MulAut.congr_apply, map_mul, map_inv]

theorem exists_conj_of_involutive_SL28 (θ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F8))
    (hθ : θ * θ = 1) : ∃ y : Matrix.SpecialLinearGroup (Fin 2) F8, θ = MulAut.conj y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F8 ≃* Matrix.SpecialLinearGroup (Fin 2) F8 :=
    CFSG.Walter.psl2MulEquivSL2OfCharTwo
  let θP : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F8) := MulAut.congr f.symm θ
  have hθP : θP * θP = 1 := by
    rw [← map_mul, hθ, map_one]
  have hpow : θP ^ 2 = 1 := by rw [pow_two]; exact hθP
  have hcop : Nat.Coprime 3 (orderOf θP) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow) (by norm_num)
  obtain ⟨x, hx⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.exists_conj_of_coprime_orderOf
    Nat.prime_three θP hcop
  refine ⟨f x, ?_⟩
  have hθ' : θ = MulAut.congr f θP := by
    ext m
    simp [θP, MulAut.congr_apply]
  rw [hθ', hx, congr_mulAutConj_eleven]

theorem fStarIn_le_self {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Γ : Subgroup (CFSG.Quasithin.G11.GLV V)) :
    CFSG.ASVolI.ChG.fStarIn Γ ≤ Γ :=
  Subgroup.map_subtype_le _

theorem fStarIn_normal {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Γ : Subgroup (CFSG.Quasithin.G11.GLV V)) {g : CFSG.Quasithin.G11.GLV V} (hg : g ∈ Γ)
    {n : CFSG.Quasithin.G11.GLV V} (hn : n ∈ CFSG.ASVolI.ChG.fStarIn Γ) :
    g * n * g⁻¹ ∈ CFSG.ASVolI.ChG.fStarIn Γ := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hn
  have hnorm : (CFSG.Open.genFittingFStar ↥Γ).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal ↥Γ
  have hc := hnorm.conj_mem y hy ⟨g, hg⟩
  have := Subgroup.mem_map_of_mem Γ.subtype hc
  simpa [CFSG.ASVolI.ChG.fStarIn] using this

theorem fStarIn_mem_of_comm {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ : Subgroup (CFSG.Quasithin.G11.GLV V)} {x : CFSG.Quasithin.G11.GLV V} (hx : x ∈ Γ)
    (hcomm : ∀ n ∈ CFSG.ASVolI.ChG.fStarIn Γ, x * n = n * x) :
    x ∈ CFSG.ASVolI.ChG.fStarIn Γ := by
  haveI : Finite (CFSG.Quasithin.G11.GLV V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  have hc : (⟨x, hx⟩ : ↥Γ) ∈
      Subgroup.centralizer ((CFSG.Open.genFittingFStar ↥Γ : Subgroup ↥Γ) : Set ↥Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply Subtype.ext
    have hmem : (h : CFSG.Quasithin.G11.GLV V) ∈ CFSG.ASVolI.ChG.fStarIn Γ :=
      Subgroup.mem_map_of_mem Γ.subtype hh
    exact (hcomm _ hmem).symm
  have := CFSG.Adapters.generalized_fitting_self_centralizing ↥Γ hc
  exact Subgroup.mem_map_of_mem Γ.subtype this

theorem mem_of_invol_of_normal_selfcent {G : Type} [Group G] {Γ N : Subgroup G} (hNΓ : N ≤ Γ)
    (hN : ∀ g ∈ Γ, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hC : ∀ x ∈ Γ, (∀ n ∈ N, x * n = n * x) → x ∈ N)
    {S : Type} [Group S] (e : ↥N ≃* S)
    (hinv : ∀ θ : MulAut S, θ * θ = 1 → ∃ y : S, θ = MulAut.conj y)
    {s : G} (hs : s ∈ Γ) (hs2 : s * s = 1) : s ∈ N := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  let τ : ↥N ≃* ↥N :=
    { toFun := fun n => ⟨s * n * s⁻¹, hN s hs n n.2⟩
      invFun := fun n => ⟨s * n * s⁻¹, hN s hs n n.2⟩
      left_inv := fun n => by
        apply Subtype.ext
        show s * (s * n * s⁻¹) * s⁻¹ = n
        rw [hsinv]
        calc s * (s * n * s) * s = (s * s) * n * (s * s) := by group
          _ = n := by rw [hs2, one_mul, mul_one]
      right_inv := fun n => by
        apply Subtype.ext
        show s * (s * n * s⁻¹) * s⁻¹ = n
        rw [hsinv]
        calc s * (s * n * s) * s = (s * s) * n * (s * s) := by group
          _ = n := by rw [hs2, one_mul, mul_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        show s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹)
        group }
  have hτ2 : τ * τ = 1 := by
    ext n
    show s * (s * (n : G) * s⁻¹) * s⁻¹ = (n : G)
    rw [hsinv]
    calc s * (s * n * s) * s = (s * s) * n * (s * s) := by group
      _ = n := by rw [hs2, one_mul, mul_one]
  let θ : MulAut S := MulAut.congr e τ
  have hθ2 : θ * θ = 1 := by
    rw [← map_mul, hτ2, map_one]
  obtain ⟨y, hy⟩ := hinv θ hθ2
  have hτ : τ = MulAut.conj (e.symm y) := by
    have h1 : MulAut.congr e.symm θ = τ := by
      ext n
      simp [θ, MulAut.congr_apply]
    rw [← h1, hy, congr_mulAutConj_eleven]
  have hconj : ∀ n : ↥N, s * (n : G) * s⁻¹ =
      ((e.symm y : ↥N) : G) * n * ((e.symm y : ↥N) : G)⁻¹ := by
    intro n
    have h2 : ((τ n : ↥N) : G) = ((e.symm y : ↥N) : G) * n * ((e.symm y : ↥N) : G)⁻¹ := by
      rw [hτ]
      rfl
    exact h2
  have hx : ((e.symm y : ↥N) : G)⁻¹ * s ∈ Γ :=
    Γ.mul_mem (Γ.inv_mem (hNΓ (e.symm y).2)) hs
  have hxC : ∀ n ∈ N, (((e.symm y : ↥N) : G)⁻¹ * s) * n = n * (((e.symm y : ↥N) : G)⁻¹ * s) := by
    intro n hn
    have h := hconj ⟨n, hn⟩
    calc (((e.symm y : ↥N) : G)⁻¹ * s) * n
        = ((e.symm y : ↥N) : G)⁻¹ * (s * n * s⁻¹) * s := by group
      _ = ((e.symm y : ↥N) : G)⁻¹ * (((e.symm y : ↥N) : G) * n *
            ((e.symm y : ↥N) : G)⁻¹) * s := by rw [h]
      _ = n * (((e.symm y : ↥N) : G)⁻¹ * s) := by group
  have hxN := hC _ hx hxC
  have hs_eq : s = ((e.symm y : ↥N) : G) * (((e.symm y : ↥N) : G)⁻¹ * s) := by group
  rw [hs_eq]
  exact N.mul_mem (e.symm y).2 hxN

theorem involution_mem_fStarIn {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ : Subgroup (CFSG.Quasithin.G11.GLV V)}
    (hL : CFSG.Quasithin.G11.IsL28TwistedTensorModule (CFSG.ASVolI.ChG.fStarIn Γ))
    {t : CFSG.Quasithin.G11.GLV V} (ht : t ∈ Γ) (ht2 : t * t = 1) :
    t ∈ CFSG.ASVolI.ChG.fStarIn Γ := by
  obtain ⟨φ', _, _⟩ := exists_model_iso hL
  exact mem_of_invol_of_normal_selfcent (fStarIn_le_self Γ)
    (fun g hg n hn => fStarIn_normal Γ hg hn)
    (fun x hx hc => fStarIn_mem_of_comm hx hc) φ'
    (fun θ hθ => exists_conj_of_involutive_SL28 θ hθ) ht ht2

end CFSG.Quasithin.G112A2.Eleven

end

end
