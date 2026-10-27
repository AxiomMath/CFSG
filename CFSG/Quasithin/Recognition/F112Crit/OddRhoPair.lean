module

public import CFSG.Quasithin.Recognition.F112Crit.OddRho
public import CFSG.Quasithin.Recognition.F112Crit.OddRhoCrit
public import CFSG.Quasithin.Recognition.F112Crit.PermModOdd
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorusEdge
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Transport
public import CFSG.Quasithin.Recognition.F112Crit.APrime.ConcreteA

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁ Vv)

variable {G : Type} [Group G] [Finite G]

section Crit

variable {G₀ G₁ G₂ T Z : Subgroup G}

theorem exists_pCoreOf_moves_pair_of_nonconst (hc : CritAmalgam G₀ G₁ G₂ T Z)
    {μ : CosetGeom G₀ G₁ G₂} (hμ : vtype μ = false) {L : Subgroup G} (hL : BenderLocal μ L)
    (h3 : ∀ δ ∈ nbrs μ, (nbrs δ).ncard = 3) {x : G} (hx : x ∈ pCoreOf 2 (stab μ))
    {δ₁ δ₂ : CosetGeom G₀ G₁ G₂} (hδ₁ : δ₁ ∈ nbrs μ) (hδ₂ : δ₂ ∈ nbrs μ)
    (hx₁ : x ∉ ballStab 1 δ₁) (hx₂ : x ∈ ballStab 1 δ₂)
    {δ' δ'' : CosetGeom G₀ G₁ G₂} (hδ' : δ' ∈ nbrs μ) (hδ'' : δ'' ∈ nbrs μ) (hne : δ' ≠ δ'') :
    ∃ k ∈ pCoreOf 2 (stab μ), k ∉ ballStab 1 δ' ∧ k ∉ ballStab 1 δ'' ∧
      ∀ δ ∈ nbrs μ, δ ≠ δ' → δ ≠ δ'' → k ∈ ballStab 1 δ := by
  classical
  let Ω := ↥(nbrs μ)
  haveI : Fintype Ω := Fintype.ofFinite Ω
  letI : MulAction ↥(stab μ) Ω := T723.instMulActionNbrs μ
  have hsmul_coe : ∀ (g : ↥(stab μ)) (ω : Ω),
      ((g • ω : Ω) : CosetGeom G₀ G₁ G₂) =
        T723.stabToG₀ μ g • (ω : CosetGeom G₀ G₁ G₂) := fun g ω => rfl
  have hodd : Odd (Fintype.card Ω) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_card_nbrs hc hμ
  have htrans : ∀ α β : Ω, ∃ g : ↥(stab μ), g • α = β := by
    intro α β
    obtain ⟨g, -, hg⟩ := T723.exists_mem_smul_eq hL α β
    exact ⟨g, hg⟩
  obtain ⟨U, -, hU2, hUfix, hUtr, -, -⟩ := T723.exists_unipotentH hL hδ₁
  have hfix : ∀ (y : G), y ∈ pCoreOf 2 (stab μ) →
      ∀ ω : Ω, y ∈ stab (ω : CosetGeom G₀ G₁ G₂) := by
    intro y hy ω
    exact CosetGeom.ballStab_le_stab_of_dist_le (n := 1) (γ := μ)
      (δ := (ω : CosetGeom G₀ G₁ G₂))
      (CosetGeom.dist_eq_one_iff_adj.mpr ω.2).le
      (CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam μ hy)
  let M : AddSubgroup (Ω → ZMod 2) :=
    { carrier := {f | ∃ y ∈ pCoreOf 2 (stab μ),
        f = fun ω : Ω => rhoNbrs y (ω : CosetGeom G₀ G₁ G₂)}
      zero_mem' := by
        refine ⟨1, Subgroup.one_mem (pCoreOf 2 (stab μ)), ?_⟩
        funext ω
        exact (rhoNbrs_eq_zero_iff.mpr
          (Subgroup.one_mem (ballStab 1 (ω : CosetGeom G₀ G₁ G₂)))).symm
      add_mem' := by
        rintro f g ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
        refine ⟨y * z, Subgroup.mul_mem (pCoreOf 2 (stab μ)) hy hz, ?_⟩
        funext ω
        exact (rhoNbrs_mul hc.amalgam.gen (h3 (ω : CosetGeom G₀ G₁ G₂) ω.2)
          (CosetGeom.mem_nbrs_symm ω.2) ⟨hfix y hy ω, pCoreOf_le 2 (stab μ) hy⟩
          ⟨hfix z hz ω, pCoreOf_le 2 (stab μ) hz⟩).symm
      neg_mem' := by
        rintro f ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        funext ω
        exact ZMod.neg_eq_self_mod_two _ }
  have hMinv : ∀ (g : ↥(stab μ)) (f : Ω → ZMod 2), f ∈ M →
      (fun ω => f (g⁻¹ • ω)) ∈ M := by
    rintro g f ⟨y, hy, rfl⟩
    refine ⟨(g : G) * y * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab μ) g.2) y).mp hy, ?_⟩
    funext ω
    have hcoe : T723.stabToG₀ μ g • (((g⁻¹ • ω : Ω)) : CosetGeom G₀ G₁ G₂) =
        (ω : CosetGeom G₀ G₁ G₂) := by
      have h := congrArg Subtype.val (smul_inv_smul g ω : g • (g⁻¹ • ω : Ω) = ω)
      rwa [hsmul_coe] at h
    change rhoNbrs y (((g⁻¹ • ω : Ω)) : CosetGeom G₀ G₁ G₂) =
      rhoNbrs ((g : G) * y * (g : G)⁻¹) ((ω : Ω) : CosetGeom G₀ G₁ G₂)
    rw [← rhoNbrs_conj (T723.stabToG₀ μ g) y (((g⁻¹ • ω : Ω)) : CosetGeom G₀ G₁ G₂), hcoe]
    rfl
  have hmem : (fun ω : Ω => rhoNbrs x (ω : CosetGeom G₀ G₁ G₂)) ∈ M := ⟨x, hx, rfl⟩
  have hxne : (fun ω : Ω => rhoNbrs x (ω : CosetGeom G₀ G₁ G₂)) ⟨δ₁, hδ₁⟩ ≠
      (fun ω : Ω => rhoNbrs x (ω : CosetGeom G₀ G₁ G₂)) ⟨δ₂, hδ₂⟩ := by
    have h₁ : rhoNbrs x δ₁ = 1 := rhoNbrs_eq_one_iff.mpr hx₁
    have h₂ : rhoNbrs x δ₂ = 0 := rhoNbrs_eq_zero_iff.mpr hx₂
    show rhoNbrs x δ₁ ≠ rhoNbrs x δ₂
    rw [h₁, h₂]
    exact one_ne_zero
  obtain ⟨k, hk, hkf⟩ := single_add_single_mem_of_nonconst hodd htrans hU2 hUfix hUtr hMinv
    hmem hxne ⟨δ', hδ'⟩ ⟨δ'', hδ''⟩
  have hne' : (⟨δ', hδ'⟩ : Ω) ≠ ⟨δ'', hδ''⟩ := fun h => hne (Subtype.ext_iff.mp h)
  refine ⟨k, hk, ?_, ?_, ?_⟩
  ·
    have h1 : rhoNbrs k δ' = 1 := by
      have h := congrFun hkf ⟨δ', hδ'⟩
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne', add_zero] at h
      exact h.symm
    exact rhoNbrs_eq_one_iff.mp h1
  ·
    have h1 : rhoNbrs k δ'' = 1 := by
      have h := congrFun hkf ⟨δ'', hδ''⟩
      rw [Pi.add_apply, Pi.single_eq_of_ne hne'.symm, Pi.single_eq_same, zero_add] at h
      exact h.symm
    exact rhoNbrs_eq_one_iff.mp h1
  ·
    intro δ hδ hne₁ hne₂
    have h0 : rhoNbrs k δ = 0 := by
      have h := congrFun hkf ⟨δ, hδ⟩
      rw [Pi.add_apply, Pi.single_eq_of_ne (fun hh => hne₁ (congrArg Subtype.val hh)),
        Pi.single_eq_of_ne (fun hh => hne₂ (congrArg Subtype.val hh)), add_zero] at h
      exact h.symm
    exact rhoNbrs_eq_zero_iff.mp h0

end Crit

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

theorem exists_pCoreOf_moves_pair (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hS3 : VS3 L₁)
    (hb : Odd (critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z))
    {μ δ' δ'' : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hμ : vtype μ = false)
    (hδ' : δ' ∈ nbrs μ) (hδ'' : δ'' ∈ nbrs μ) (hne : δ' ≠ δ'') :
    ∃ k ∈ pCoreOf 2 (stab μ), k ∉ ballStab 1 δ' ∧ k ∉ ballStab 1 δ'' ∧
      ∀ x ∈ nbrs μ, x ≠ δ' → x ≠ δ'' → k ∈ ballStab 1 x := by
  have hc : CritAmalgam (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) S Z := hs.toCritAmalgam
  obtain ⟨L, hL⟩ := hs.exists_benderLocal hK hμ
  have hA := APrime.amalgamS3_of_setting hs.hyp hS3 hs.S_le
  have hLoc := APrime.LocalS3.of_s3Point_γ₁ hA.hyp hA.s3Point_γ₁
  have h3 : ∀ δ ∈ nbrs μ, (nbrs δ).ncard = 3 := fun δ hδ =>
    (hLoc.point δ (vtype_eq_true_of_mem_nbrs hμ hδ)).ncard_nbrs
  obtain ⟨x, hx, δ₁, hδ₁, δ₂, hδ₂, hx₁, hx₂⟩ := exists_pCoreOf_nonconst hc hb hμ
  exact exists_pCoreOf_moves_pair_of_nonconst hc hμ hL h3 hx hδ₁ hδ₂ hx₁ hx₂ hδ' hδ'' hne

end Setting

end CFSG.Quasithin.F112Crit

end
