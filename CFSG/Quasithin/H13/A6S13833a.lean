module

public import CFSG.Quasithin.H13.A6S13834P

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Case1

variable (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
  (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
include hF s hDH hDγ

theorem comm_UH_Uγ_case1 {u x : G} (hu : u ∈ conjClosure S.V3 S.G1)
    (hx : x ∈ F8.Uγ S.V3 S.G1 (g : G)) : u * x * u⁻¹ * x⁻¹ = 1 := by
  have hu' : u ∈ F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) := hDH ▸ hu
  have hx' : x ∈ F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) := hDγ ▸ hx
  have h1 : u * x * u⁻¹ * x⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) := hu'.2.2 x hx
  have h2 : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := hx'.2.2 u hu
  have h3 : u * x * u⁻¹ * x⁻¹ ∈ fsuV1 T V := by
    have := (fsuV1 T V).inv_mem h2
    rwa [show (x * u * x⁻¹ * u⁻¹)⁻¹ = u * x * u⁻¹ * x⁻¹ by group] at this
  have h4 : u * x * u⁻¹ * x⁻¹ ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := ⟨h3, h1⟩
  rwa [hF.F913_5b s, Subgroup.mem_bot] at h4

omit hDH in
theorem Uγ_le_QH_case1 : F8.Uγ S.V3 S.G1 (g : G) ≤ pCoreOf 2 S.G1 := by
  intro x hx
  have : x ∈ F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) := hDγ ▸ hx
  rw [hF.Dγ_eq_inf_pCoreOf s] at this
  exact this.2

theorem Uγ_le_centralizer_V3 : F8.Uγ S.V3 S.G1 (g : G) ≤ Subgroup.centralizer (S.V3 : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h := S.comm_UH_Uγ_case1 hF s hDH hDγ (le_conjClosure S.V3 S.G1 hv) hx
  calc v * x = (v * x * v⁻¹ * x⁻¹) * (x * v) := by group
    _ = x * v := by rw [h, one_mul]

end Case1

theorem ballStab_γ₁_le_QH (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) {K : Subgroup G}
    (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K) (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hβ : UHCoords S ρ) : ballStab 1 (F8.γ₁ T L S.G1) ≤ pCoreOf 2 S.G1 := by
  obtain ⟨τ, ρ', -, hN', hker', -, honto', -, -⟩ :=
    S.exists_coords hF hKT hL1K ρ hker hKA honto hβ
  have hG : (L ⊔ T) ⊔ S.G1 = (L ⊔ T) ⊔ S.G1 := rfl
  have hcore := (ballStab_one_γ₁ hG).1
  change ballStab 1 (CosetGeom.γ₁ ((L ⊔ T) ⊔ S.G1) (L ⊔ T) S.G1) ≤ _
  rw [hcore]
  set N := coreIn ((L ⊔ T) ⊓ S.G1) S.G1 with hNdef
  intro x hx
  by_contra hxQ
  set M := (N.subgroupOf S.G1).map ρ' with hM
  have hNH : N ≤ S.G1 := coreIn_le_left _ _
  have hMne : M ≠ ⊥ := by
    intro hbot
    apply hxQ
    have h1 : ρ' ⟨x, hNH hx⟩ ∈ M := Subgroup.mem_map_of_mem ρ' (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact (hker' _).mp h1
  have hMN : ∀ σ ∈ alternatingGroup (Fin 6), ∀ m ∈ M, σ * m * σ⁻¹ ∈ M := by
    intro σ hσ m hm
    obtain ⟨k, -, rfl⟩ := honto' σ hσ
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hm
    refine Subgroup.mem_map.mpr ⟨k * n * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ k.2) n).mp hn
  have hAM := alt6_le_of_normalized hMne hMN
  obtain ⟨n, hn, hnσ⟩ := Subgroup.mem_map.mp
    (hAM (Perm.mem_alternatingGroup.mpr cert_pts.1))
  have hnL : (n : G) ∈ S.L1 ⊔ T := by
    have h1 : (n : G) ∈ (L ⊔ T) ⊓ S.G1 := coreIn_le_right _ _ (Subgroup.mem_subgroupOf.mp hn)
    rw [hF.toHypF91.LT_inf_H] at h1
    exact h1
  have hc := (hN' n).2 (S.L1T_le_NV3 hnL)
  rw [hnσ] at hc
  exact cert_pts.2.1 (cList_comm _ hc)

section Symm

variable (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)

include hF s in
theorem case1_symm (hn : ¬ F8.Uγ V S.G1 (g : G) ≤ ballStab 1 (F8.γ₁ T L S.G1))
    (h3 : ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
      (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∨
        F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1) →
      F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1 ∧
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) ∧
        IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V) ∧
        fsuV1 T V ≤ F8.Uγ S.V3 S.G1 (g : G) ∧ ¬ F8.Uγ V S.G1 (g : G) ≤ pCoreOf 2 S.G1)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1) :
    F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1 ∧
      ∃ y : G, conjSub y⁻¹ V ≤ F8.Uγ V S.G1 (g : G) ∧
        ⁅conjSub y⁻¹ V, conjClosure S.V3 S.G1⁆ = F8.A₁ (fsuV1 T V) (g : G) := by
  obtain ⟨δ, δ', k, y, sk, hyγ, -, eU, -, -, eDγ⟩ := hF.exists_symmetric_setup s hn
  have hDδ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (k : G) = F8.Uγ S.V3 S.G1 (k : G) := by
    rw [eDγ, hDH, eU]
  obtain ⟨-, -, htr, hV1δ, -⟩ := h3 δ δ' k sk (Or.inl hDδ)
  have hyg : (y : G) * (g : G) ∈ S.G1 := by
    have h1 : (y * g) • F8.γ₁ T L S.G1 = F8.γ₁ T L S.G1 := by
      rw [mul_smul, s.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hF.amalgamHypV.le₂] at this
    simpa using this
  have eA : conjSub (y : G)⁻¹ (fsuV1 T V) = F8.A₁ (fsuV1 T V) (g : G) := by
    have e : (y : G)⁻¹ = (g : G) * ((y : G) * (g : G))⁻¹ := by group
    rw [F8.A₁, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer
      (hF.H_normalizes_V₁ (S.G1.inv_mem hyg))]
  have eUH : conjSub (y : G)⁻¹ (F8.Uγ S.V3 S.G1 (k : G)) = conjClosure S.V3 S.G1 := by
    rw [eU, conjSub_conjSub_inv]
  refine ⟨?_, (y : G), ?_, ?_⟩
  · rw [← eA, ← eUH]
    exact conjSub_mono _ hV1δ
  · have e : (y : G)⁻¹ = (g : G) * ((y : G) * (g : G))⁻¹ := by group
    rw [e, conjSub_mul, F8.Uγ]
    refine conjSub_mono _ fun x hx => ?_
    rw [mem_conjSub, inv_inv] at hx
    have := mem_conjClosure (S.G1.inv_mem hyg) hx
    rwa [show ((y : G) * (g : G))⁻¹ * ((y : G) * (g : G) * x * ((y : G) * (g : G))⁻¹) *
      ((y : G) * (g : G))⁻¹⁻¹ = x by group] at this
  · rw [← eA, ← eUH, conjSub_commutator, htr.2.2]

end Symm

end Setting4

theorem relIndex_centralizer_eq_two {G : Type} [Group G] [Finite G] {U A : Subgroup G}
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {x : G} (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hA : Nat.card A = 2) (hcomm : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ A) {u₀ : G} (hu₀ : u₀ ∈ U)
    (hne : x * u₀ * x⁻¹ * u₀⁻¹ ≠ 1) :
    (U ⊓ Subgroup.centralizer ({x} : Set G)).relIndex U = 2 := by
  let φ : ↥U →* ↥A :=
    { toFun := fun u => ⟨x * (u : G) * x⁻¹ * (u : G)⁻¹, hcomm u u.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hc := hUab _ (U.inv_mem u.2) _
          (U.mul_mem (hxU _ v.2) (U.inv_mem v.2))
        calc x * ((u : G) * v) * x⁻¹ * ((u : G) * v)⁻¹ =
            (x * u * x⁻¹) * (((x * v * x⁻¹) * (v : G)⁻¹) * (u : G)⁻¹) := by group
          _ = (x * u * x⁻¹) * ((u : G)⁻¹ * ((x * v * x⁻¹) * (v : G)⁻¹)) := by
              rw [show ((x * v * x⁻¹) * (v : G)⁻¹) * (u : G)⁻¹ =
                (u : G)⁻¹ * ((x * v * x⁻¹) * (v : G)⁻¹) from hc.symm]
          _ = x * u * x⁻¹ * (u : G)⁻¹ * (x * v * x⁻¹ * (v : G)⁻¹) := by group }
  have hker : φ.ker = (U ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨u.2, ?_⟩
      calc (u : G) * x = (x * u * x⁻¹ * (u : G)⁻¹)⁻¹ * (x * u) := by group
        _ = x * u := by rw [h1, inv_one, one_mul]
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show x * (u : G) * x⁻¹ * (u : G)⁻¹ = 1
      rw [← h]; group
  have hidx : (U ⊓ Subgroup.centralizer ({x} : Set G)).relIndex U = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [hidx]
  have hle : Nat.card φ.range ≤ 2 := hA ▸ Subgroup.card_le_card_group _
  have hne1 : Nat.card φ.range ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    apply hne
    have : φ ⟨u₀, hu₀⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  omega

theorem cA6_line_weight : ∀ a b : Fin 6 → ZMod 2, ∑ i, a i = 0 → ∑ i, b i = 0 → a ≠ 0 → b ≠ 0 →
    a ≠ b → (∀ σ ∈ cList, Perm.sign σ = 1 → InL a b (vp σ a) ∧ InL a b (vp σ b)) →
    wtv a = 4 := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Transp

variable (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  {ρ ρ' : ↥S.G1 →* Perm (Fin 6)} {R : G → (Fin 6 → ZMod 2) → Prop} (hR : S.RepRel ρ R)
  {τ : Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
  (hE8 : ∀ y : ↥S.G1, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' y ∈ e8List)
include hF s hR hρ' hker' hE8

theorem case1_transp {c : G} (hc : c ∈ S.G1)
    (hcV : conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T)) {X : Subgroup G}
    (hXV : X ≤ F8.Uγ V S.G1 (g : G))
    (hXA : ⁅X, conjClosure S.V3 S.G1⁆ = F8.A₁ (fsuV1 T V) (g : G)) :
    ∃ x : ↥S.G1, (x : G) ∈ conjSub c X ∧
      (ρ' x = swap 0 1 ∨ ρ' x = swap 2 3 ∨ ρ' x = swap 4 5) ∧
      (∀ u ∈ conjClosure S.V3 S.G1,
        (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ conjSub c (F8.A₁ (fsuV1 T V) (g : G))) ∧
      ∃ u₀ ∈ conjClosure S.V3 S.G1, (x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹ ∉ fsuV1 T V := by
  set U := conjClosure S.V3 S.G1 with hU
  set A := conjSub c (F8.A₁ (fsuV1 T V) (g : G)) with hAdef
  have hUc : conjSub c U = U := F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure _ _ hc)
  have hXA' : ⁅conjSub c X, U⁆ = A := by
    rw [← hUc, conjSub_commutator, hXA]
  have hcardA : Nat.card A = 2 := (card_conjSub _ _).trans (hF.card_A₁ (g := g))
  have hAV1 : ∀ a ∈ A, a ∈ fsuV1 T V → a = 1 := by
    intro a ha haV
    have h1 : c⁻¹ * a * c ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := by
      refine ⟨?_, mem_conjSub.mp ha⟩
      have := (Subgroup.mem_normalizer_iff.mp
        (hF.H_normalizes_V₁ (S.G1.inv_mem hc)) a).mp haV
      rwa [inv_inv] at this
    rw [hF.F913_5b s, Subgroup.mem_bot] at h1
    calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨x, hx, u₀, hu₀, hne⟩ : ∃ x ∈ conjSub c X, ∃ u₀ ∈ U,
      x * u₀ * x⁻¹ * u₀⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : ⁅conjSub c X, U⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx u hu
      rw [commutatorElement_def, hall x hx u hu]
      exact Subgroup.one_mem _
    rw [hXA'] at hbot
    have : Nat.card A = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hxO : x ∈ pCoreOf 2 (S.L1 ⊔ T) := hcV (conjSub_mono c hXV hx)
  have hxH : x ∈ S.G1 := hF.toHypF91.L₁T_le_H (pCoreOf_le 2 _ hxO)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    isElemAbelian_comm hF.F911_3 ha hb
  have hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hxH) u).mp hu
  have hcomm : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ A := fun u hu => by
    have := Subgroup.commutator_mem_commutator hx hu
    rw [hXA', commutatorElement_def] at this
    exact this
  have hidx := relIndex_centralizer_eq_two hUab hxU hcardA hcomm hu₀ hne
  have h8 : ρ' ⟨x, hxH⟩ ∈ e8List := hE8 ⟨x, hxH⟩ hxO
  have hcent : ∀ d ∈ U ⊓ Subgroup.centralizer ({x} : Set G), x * d * x⁻¹ = d := by
    intro d hd
    have := Subgroup.mem_centralizer_singleton_iff.mp hd.2
    rw [← this, mul_inv_cancel_right]
  have htv := S.rho_tv_of_centralizes hR hρ' hF.F911_3 h8 hidx hcent
  have hu₀V : x * u₀ * x⁻¹ * u₀⁻¹ ∉ fsuV1 T V := fun h => hne (hAV1 _ (hcomm u₀ hu₀) h)
  refine ⟨⟨x, hxH⟩, hx, ?_, hcomm, u₀, hu₀, hu₀V⟩
  rcases htv with h1 | h1
  · exfalso
    have hxQ := (hker' _).1 h1
    apply hu₀V
    have := hF.toHypF91.commutator_conjClosure_le u₀ hu₀ x hxQ
    have := (fsuV1 T V).inv_mem this
    rwa [show (u₀ * x * u₀⁻¹ * x⁻¹)⁻¹ = x * u₀ * x⁻¹ * u₀⁻¹ by group] at this
  · exact h1

end Transp

end Setting4

theorem wtv_transp : ∀ t ∈ [swap (0 : Fin 6) 1, swap 2 3, swap 4 5], ∀ w : Fin 6 → ZMod 2,
    wtv (vp t w + w) = 0 ∨ wtv (vp t w + w) = 2 := by
  decide +kernel

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section CoverB

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hβk hβe hρ' hN' honto'

theorem cover_V3_weight {v : G} (hv : v ∈ S.V3) (hv1 : v ∉ fsuV1 T V) :
    wtv ((Multiplicative.toAdd (β ⟨v, S.V3_le_UH hv⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2) = 4 := by
  have h12 : S.u1 * S.u2 ∈ S.V3 := S.V3.mul_mem S.u1_mem_V3 S.u2_mem_V3
  set a : Fin 6 → ZMod 2 := ((Multiplicative.toAdd (β ⟨S.u1, S.V3_le_UH S.u1_mem_V3⟩) :
    ↥(evenWeight 6)) : Fin 6 → ZMod 2) with ha_def
  set b : Fin 6 → ZMod 2 := ((Multiplicative.toAdd (β ⟨S.u2, S.V3_le_UH S.u2_mem_V3⟩) :
    ↥(evenWeight 6)) : Fin 6 → ZMod 2) with hb_def
  have hvec0 : ∀ (u : G) (hu : u ∈ S.V3), u ∉ fsuV1 T V →
      ((Multiplicative.toAdd (β ⟨u, S.V3_le_UH hu⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) ≠ 0 := by
    intro u hu hn h
    apply hn
    refine (hβk ⟨u, S.V3_le_UH hu⟩).1 (Multiplicative.toAdd.injective ?_)
    rw [toAdd_one]
    exact Subtype.ext h
  have ha0 : a ≠ 0 := hvec0 _ S.u1_mem_V3 S.u1_not_V1
  have hb0 : b ≠ 0 := hvec0 _ S.u2_mem_V3 S.u2_not_V1
  have hab0 : a + b ≠ 0 := by
    rw [← S.cover_mul _ _ S.u1_mem_V3 S.u2_mem_V3]; exact hvec0 _ h12 S.u12_not_V1
  have hba : b ≠ a := fun h => S.u21_not_V1 (S.mem_V1_of_beta_eq hβk (S.cover_coe_eq h))
  have hstab := S.cover_mem_stabSub_iff hβk hβe
  have hinv : ∀ x y : Fin 6 → ZMod 2, (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (x = a + b ∧ y = a) →
      ∀ σ ∈ cList, Perm.sign σ = 1 →
        InL (vp τ⁻¹ x) (vp τ⁻¹ y) (vp σ (vp τ⁻¹ x)) ∧
          InL (vp τ⁻¹ x) (vp τ⁻¹ y) (vp σ (vp τ⁻¹ y)) := by
    intro x y hxy σ hσ hs
    obtain ⟨k, -, hk⟩ := honto' σ (Perm.mem_alternatingGroup.mpr hs)
    have hkN : (k : G) ∈ Subgroup.normalizer (S.V3 : Set G) := (hN' k).1 (by rw [hk]; exact hσ)
    obtain ⟨hka, hkb⟩ := (hstab k).2 hkN
    have hρk : ρ k = τ * σ * τ⁻¹ := by rw [← hk, hρ']; group
    have key : ∀ w : Fin 6 → ZMod 2, InL a b (vp (ρ k) w) → InL a b w →
        InL (vp τ⁻¹ x) (vp τ⁻¹ y) (vp σ (vp τ⁻¹ w)) := by
      intro w hw _
      have h1 : vp σ (vp τ⁻¹ w) = vp τ⁻¹ (vp (ρ k) w) := by
        rw [hρk, ← vp_mul, ← vp_mul]; congr 1; group
      rw [h1]
      have hl : InL a b (vp (ρ k) w) := hw
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact inL_maps (vp_add τ⁻¹) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl))) hl
      · exact inL_maps (vp_add τ⁻¹) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl)) hl
      · refine inL_maps (vp_add τ⁻¹) (Or.inr (Or.inr (Or.inl rfl)))
          (Or.inr (Or.inr (Or.inr ?_))) hl
        rw [← vp_add]
        congr 1
        rw [add_comm a b, add_assoc, vadd_self, add_zero]
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨key _ hka (Or.inr (Or.inl rfl)), key _ hkb (Or.inr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨key _ hkb (Or.inr (Or.inr (Or.inl rfl))), key _ hka (Or.inr (Or.inl rfl))⟩
    · refine ⟨key _ ?_ (Or.inr (Or.inr (Or.inr rfl))), key _ hka (Or.inr (Or.inl rfl))⟩
      rw [vp_add]
      exact inL_add hka hkb
  have hsum : ∀ w : Fin 6 → ZMod 2, ∑ i, w i = 0 → ∑ i, vp τ⁻¹ w i = 0 := fun w hw => by
    rw [sum_vp]; exact hw
  have sa : ∑ i, a i = 0 := sum_eq_zero _
  have sb : ∑ i, b i = 0 := sum_eq_zero _
  have sab : ∑ i, (a + b) i = 0 := by
    simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, sa, sb, add_zero]
  have hne : ∀ w : Fin 6 → ZMod 2, w ≠ 0 → vp τ⁻¹ w ≠ 0 := fun w hw h =>
    hw (vp_injective τ⁻¹ (by rw [h, vp_zero]))
  have hinj : ∀ w w' : Fin 6 → ZMod 2, w ≠ w' → vp τ⁻¹ w ≠ vp τ⁻¹ w' := fun w w' h e =>
    h (vp_injective τ⁻¹ e)
  have wa : wtv a = 4 := by
    rw [← wtv_vp τ⁻¹]
    exact cA6_line_weight _ _ (hsum a sa) (hsum b sb) (hne a ha0) (hne b hb0)
      (hinj a b (Ne.symm hba)) (hinv a b (Or.inl ⟨rfl, rfl⟩))
  have wb : wtv b = 4 := by
    rw [← wtv_vp τ⁻¹]
    exact cA6_line_weight _ _ (hsum b sb) (hsum a sa) (hne b hb0) (hne a ha0)
      (hinj b a hba) (hinv b a (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have wab : wtv (a + b) = 4 := by
    rw [← wtv_vp τ⁻¹]
    refine cA6_line_weight _ _ (hsum _ sab) (hsum a sa) (hne _ hab0) (hne a ha0) ?_
      (hinv (a + b) a (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    refine hinj _ _ fun h => hb0 ?_
    calc b = a + (a + b) := by rw [← add_assoc, vadd_self, zero_add]
      _ = 0 := by rw [h, vadd_self]
  rcases S.cover_inL_of_V3 hβk hv with h | h | h | h
  · exact absurd h (hvec0 _ hv hv1)
  · rw [h]; exact wa
  · rw [h]; exact wb
  · rw [h]; exact wab

end CoverB

section CoverB3

variable (hNS : ¬ LieModel G .PSp 3 2 1)
  (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (hG1 : S.G1 ∈ S.Hz) (h13314 : Stmt13_3_14)
  (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {τ : Perm (Fin 6)} {ρ' : ↥S.G1 →* Perm (Fin 6)} (hρ' : ∀ g, ρ' g = τ⁻¹ * ρ g * τ)
  (hN' : ∀ g : ↥S.G1, ρ' g ∈ cList ↔ (g : G) ∈ Subgroup.normalizer (S.V3 : Set G))
  {K : Subgroup G}
  (honto' : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ' k = σ)
include hNS h13315 h1356two hG1 h13314 hF s hβk hβe hρ' hN' honto'

theorem cover_b_ne_three {R : G → (Fin 6 → ZMod 2) → Prop} (hR : S.RepRel ρ R)
    (hker' : ∀ h : ↥S.G1, ρ' h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hE8 : ∀ y : ↥S.G1, (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) → ρ' y ∈ e8List)
    {c : G} (hc : c ∈ S.G1) (hcV : conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T))
    {X : Subgroup G} (hXV : X ≤ F8.Uγ V S.G1 (g : G))
    (hXA : ⁅X, conjClosure S.V3 S.G1⁆ = F8.A₁ (fsuV1 T V) (g : G))
    (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1) : F8.b T V L S.G1 ≠ 3 := by
  intro hb
  obtain ⟨x, -, ht, hxA, u₀, hu₀, hu₀V⟩ :=
    S.case1_transp hF s hR hρ' hker' hE8 hc hcV hXV hXA
  obtain ⟨k, hk, hAk⟩ := S.exists_A1_le_of_b_eq_three hF s hb
  have hUN : ∀ h ∈ S.G1, ∀ u ∈ conjClosure S.V3 S.G1, h * u * h⁻¹ ∈ conjClosure S.V3 S.G1 :=
    fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 hh) u).mp hu
  set a := (x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹ with ha_def
  have haU : a ∈ conjClosure S.V3 S.G1 :=
    (conjClosure S.V3 S.G1).mul_mem (hUN _ x.2 _ hu₀) ((conjClosure S.V3 S.G1).inv_mem hu₀)
  have hcA : c⁻¹ * a * c ∈ F8.A₁ (fsuV1 T V) (g : G) := mem_conjSub.mp (hxA u₀ hu₀)
  have hv3 : k * (c⁻¹ * a * c) * k⁻¹ ∈ S.V3 := by
    have h1 := hAk hcA
    have h2 := hA1 hcA
    rw [mem_conjSub, inv_inv] at h1
    rw [← S.V_inf_UH hNS h13315 h1356two hG1 h13314]
    exact ⟨h1, hUN _ hk _ h2⟩
  set v := k * (c⁻¹ * a * c) * k⁻¹ with hv_def
  have hav : a = (c * k⁻¹) * v * (c * k⁻¹)⁻¹ := by rw [hv_def]; group
  have hhH : c * k⁻¹ ∈ S.G1 := S.G1.mul_mem hc (S.G1.inv_mem hk)
  have hv1 : v ∉ fsuV1 T V := by
    intro h
    apply hu₀V
    rw [hav]
    exact (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ hhH) v).mp h
  have hw4 := S.cover_V3_weight hβk hβe hρ' hN' honto' hv3 hv1
  have e1 := hβe ⟨c * k⁻¹, hhH⟩ ⟨v, S.V3_le_UH hv3⟩ ⟨a, haU⟩ hav
  have hwa : wtv ((Multiplicative.toAdd (β ⟨a, haU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = 4 := by
    rw [e1]
    exact (wtv_vp _ _).trans hw4
  have hxu : (x : G) * u₀ * (x : G)⁻¹ ∈ conjClosure S.V3 S.G1 := hUN _ x.2 _ hu₀
  have e2 := hβe x ⟨u₀, hu₀⟩ ⟨_, hxu⟩ rfl
  have hprod : β ⟨a, haU⟩ = β ⟨_, hxu⟩ * (β ⟨u₀, hu₀⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]; rfl
  have hval : ((Multiplicative.toAdd (β ⟨a, haU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) =
      vp τ (vp (ρ' x) (vp τ⁻¹
        ((Multiplicative.toAdd (β ⟨u₀, hu₀⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)) +
        vp τ⁻¹ ((Multiplicative.toAdd (β ⟨u₀, hu₀⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2)) := by
    have hr : τ * ρ' x * τ⁻¹ = ρ x := by rw [hρ']; group
    rw [vp_add, vp_vp_inv, ← vp_mul, ← vp_mul, hr, hprod, toAdd_mul, toAdd_inv, e2]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    have hneg : ∀ w : Fin 6 → ZMod 2, -w = w := fun w => neg_eq_of_add_eq_zero_left (vadd_self w)
    congr 1
    exact hneg _
  have hmem : ρ' x ∈ [swap (0 : Fin 6) 1, swap 2 3, swap 4 5] := by
    rcases ht with h | h | h <;> rw [h] <;> simp
  rw [hval, wtv_vp] at hwa
  rcases wtv_transp _ hmem (vp τ⁻¹ ((Multiplicative.toAdd (β ⟨u₀, hu₀⟩) : ↥(evenWeight 6)) :
      Fin 6 → ZMod 2)) with h | h <;> omega

end CoverB3

section Swap45

variable (h13315 : Stmt13_3_15) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
  {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
  (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
  (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
include h13315 hF s hDH hDγ

theorem exists_Uγ_swap45 (htr : IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V)) :
    ∃ x : ↥(Subgroup.normalizer (V : Set G)), (x : G) ∈ F8.Uγ S.V3 S.G1 (g : G) ∧
      S.frame.ρ x = swap 4 5 := by
  by_contra hall
  push Not at hall
  have hcen : ∀ x ∈ F8.Uγ S.V3 S.G1 (g : G), ∀ v ∈ V, x * v * x⁻¹ = v := by
    intro x hx v hv
    have hxC := S.Uγ_le_centralizer_V3 hF s hDH hDγ hx
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := S.centralizer_V3_le h13315 hxC
    have h1 : S.frame.ρ ⟨x, hxN⟩ = 1 := by
      rcases fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨x, hxN⟩) hxC) with h | h
      · exact h
      · exact absurd h (hall ⟨x, hxN⟩ hx)
    have := (S.conj_eq_iff ⟨x, hxN⟩ ⟨v, hv⟩).2 (by rw [h1, map_one]; rfl)
    exact this
  have hbot : ⁅V, F8.Uγ S.V3 S.G1 (g : G)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def, Subgroup.mem_bot]
    have h1 := hcen x hx v hv
    calc v * x * v⁻¹ * x⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel, inv_one]
  have h2 := htr.2.1
  rw [← htr.2.2, hbot, Subgroup.card_bot] at h2
  exact absurd h2 (by norm_num)

end Swap45

end Setting4

end CFSG.Quasithin.H13.A6
