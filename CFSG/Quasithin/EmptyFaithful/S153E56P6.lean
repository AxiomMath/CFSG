module

public import CFSG.Quasithin.EmptyFaithful.S153E56P5

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Rho

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}

omit [Finite G] in
open scoped Classical in
theorem comm153_conj (n u v : G) : comm153 (n * u * n⁻¹) (n * v * n⁻¹) = comm153 u v := by
  have h : (⁅n * u * n⁻¹, n * v * n⁻¹⁆ = 1) ↔ (⁅u, v⁆ = 1) := by
    rw [← conj_commutator, conj_eq_one_iff]
  unfold comm153
  exact if_congr h rfl rfl

variable (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem exists_zp : ∃ zp ∈ conjSubgroup (quasithinOmegaOneCenter T) y, zp ≠ 1 ∧
    ∀ z ∈ conjSubgroup (quasithinOmegaOneCenter T) y, z = 1 ∨ z = zp := by
  obtain ⟨x, hx1, hx⟩ := (Nat.card_eq_two_iff' (1 : ↥(conjSubgroup (quasithinOmegaOneCenter T) y))).1
    (exPair_U' S).card_Z
  refine ⟨(x : G), x.2, fun h => hx1 (Subtype.ext h), fun z hz => ?_⟩
  by_cases hz1 : z = 1
  · exact Or.inl hz1
  · right
    have := hx ⟨z, hz⟩ (fun h => hz1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

noncomputable def zp : G := Classical.choose (exists_zp S)

theorem zp_mem : zp S ∈ conjSubgroup (quasithinOmegaOneCenter T) y :=
  (Classical.choose_spec (exists_zp S)).1

theorem zp_ne_one : zp S ≠ 1 := (Classical.choose_spec (exists_zp S)).2.1

theorem mem_Z'_iff {z : G} : z ∈ conjSubgroup (quasithinOmegaOneCenter T) y ↔ z = 1 ∨ z = zp S :=
  ⟨(Classical.choose_spec (exists_zp S)).2.2 z, by
    rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact zp_mem S⟩

theorem zp_mem_U : zp S ∈ UH153 T M V₁ Mc := S.hG.Z'_le_U (zp_mem S)

theorem zp_mem_E : zp S ∈ Egp153 T M V₁ Mc y := Z'_le_E S (zp_mem S)

theorem zp_not_mem_Z : zp S ∉ quasithinOmegaOneCenter T := by
  intro h
  have : zp S ∈ quasithinOmegaOneCenter T ⊓ conjSubgroup (quasithinOmegaOneCenter T) y :=
    ⟨h, zp_mem S⟩
  rw [S.hG.Z_inf_Z', Subgroup.mem_bot] at this
  exact zp_ne_one S this

@[expose] noncomputable def aa : Ut T M V₁ Mc := pi S.cx ⟨zp S, zp_mem_U S⟩

theorem aa_eq : aa S = pi S.cx ⟨zp S, zp_mem_U S⟩ := rfl

theorem aa_mem_Et1 : aa S ∈ Et1 T M V₁ Mc y := (mem_Et1 S).2 ⟨⟨zp S, zp_mem_U S⟩, zp_mem_E S, rfl⟩

theorem aa_ne_one : aa S ≠ 1 := fun h => zp_not_mem_Z S ((pi_eq_one_iff S.cx _).1 h)

theorem exists_w₀ : ∃ w₀ ∈ Et2 T M V₁ Mc y t₁, bet S.cx w₀ (aa S) = 1 :=
  (split_model S).exists_w₀ (aa_mem_Et1 S) (aa_ne_one S)

@[expose] noncomputable def rhoX {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) : MulAut (Ut T M V₁ Mc) :=
  rho S.cx ⟨x, X_le_NZ S hx⟩

theorem rhoX_pi {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) (u : ↥(UH153 T M V₁ Mc)) :
    rhoX S hx (pi S.cx u) = pi S.cx ⟨x * u * x⁻¹, U_conj_mem (X_le_Mc S hx) u.2⟩ :=
  (pi_conj S.cx ⟨x, X_le_NZ S hx⟩ (X_le_Mc S hx) u).symm

theorem bet_rho {n : NZ T} (hn : (n : G) ∈ Mc) (q q' : Ut T M V₁ Mc) :
    bet S.cx (rho S.cx n q) (rho S.cx n q') = bet S.cx q q' := by
  obtain ⟨u, rfl⟩ := pi_surj S.cx q
  obtain ⟨v, rfl⟩ := pi_surj S.cx q'
  rw [← pi_conj S.cx n hn, ← pi_conj S.cx n hn, bet_pi S, bet_pi S]
  exact comm153_conj _ _ _

theorem rhoX_isOO {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) :
    IsOO (bet S.cx) (Et1 T M V₁ Mc y) (Et2 T M V₁ Mc y t₁) (rhoX S hx) where
  iso := bet_rho S (X_le_Mc S hx)
  map₁ := fun q hq => by
    obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 hq
    rw [rhoX_pi]
    exact (mem_Et1 S).2 ⟨_, X_conj_E S hx hu, rfl⟩
  map₂ := fun q hq => by
    obtain ⟨u, hu, rfl⟩ := (mem_Et2 S).1 hq
    rw [rhoX_pi]
    exact (mem_Et2 S).2 ⟨_, X_conj_E' S hx hu, rfl⟩

theorem rhoX_fix_aa {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) : rhoX S hx (aa S) = aa S := by
  unfold aa
  rw [rhoX_pi]
  congr 1
  apply Subtype.ext
  show x * zp S * x⁻¹ = zp S
  have h := (exPair_U' S).central (zp S) (zp_mem S) x (X_le_U' S hx)
  rw [← h]
  group

theorem rhoX_tr₁ {x : G} (hx : x ∈ Xgp153 T M V₁ Mc y) :
    ∀ e ∈ Et1 T M V₁ Mc y, rhoX S hx e = e ∨ rhoX S hx e = e * aa S := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := (mem_Et1 S).1 he
  rw [rhoX_pi]
  have hc := comm_XE S hx hu
  have e1 : x * (u : G) * x⁻¹ = ⁅x, (u : G)⁆ * u := by
    simp only [commutatorElement_def]
    group
  rcases (mem_Z'_iff S).1 hc with h1 | h1
  · left
    congr 1
    apply Subtype.ext
    show x * (u : G) * x⁻¹ = u
    rw [e1, h1, one_mul]
  · right
    have e2 : (⟨x * (u : G) * x⁻¹, U_conj_mem (X_le_Mc S hx) u.2⟩ : ↥(UH153 T M V₁ Mc)) =
        ⟨zp S, zp_mem_U S⟩ * u := by
      apply Subtype.ext
      show x * (u : G) * x⁻¹ = zp S * u
      rw [e1, h1]
    rw [e2, map_mul, Ut_comm S.cx]
    rfl

end Rho

end S153E56p

end CFSG.Quasithin
