module

public import CFSG.Quasithin.H13.A6S13833h
public import CFSG.Quasithin.H13.A6S13833i

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem perm_eq_one_of_fix_ev : ∀ σ : Perm (Fin 6),
    (∀ j : Fin 6, vp σ (Pi.single 0 1 + Pi.single j 1) = Pi.single 0 1 + Pi.single j 1) →
    σ = 1 := by
  decide +kernel

theorem mem_normalizer_centralizer {G : Type} [Group G] {X : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : x⁻¹ * v * x ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) v).mp hv
      simpa using this
    have h := hc _ hv'
    calc v * (x * c * x⁻¹) = x * ((x⁻¹ * v * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * v * x)) * x⁻¹ := by rw [h]
      _ = x * c * x⁻¹ * v := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : x * v * x⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hx v).mp hv
    have h := hc _ hv'
    calc v * c = x⁻¹ * ((x * v * x⁻¹) * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * c * x⁻¹) * (x * v * x⁻¹)) * x := by rw [h]
      _ = c * v := by group

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem cent_UH_le_QH {ρ : ↥S.G1 →* Perm (Fin 6)}
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)} (hβs : Function.Surjective β)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))) :
    S.G1 ⊓ Subgroup.centralizer (conjClosure S.V3 S.G1 : Set G) ≤ pCoreOf 2 S.G1 := by
  intro x hx
  refine (hker ⟨x, hx.1⟩).1 (perm_eq_one_of_fix_ev _ fun j => ?_)
  have hw : ∑ i, (Pi.single 0 1 + Pi.single j 1 : Fin 6 → ZMod 2) i = 0 := by
    revert j; decide
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd ⟨_, mem_ev_of_sum_zero hw⟩)
  have hcu : (u : G) = x * u * x⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.mp hx.2 u u.2
    calc (u : G) = (u : G) * x * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [h1]
  have he := hβe ⟨x, hx.1⟩ u u hcu
  rw [hu] at he
  have := congrArg Subtype.val he
  exact this.symm

theorem false_coverEq (h13315 : Stmt13_3_15)
    (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1) (hhat : ¬ IsHatA6 L)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1) (hL1K : S.L1 ≤ K)
    {ρ : ↥S.G1 →* Perm (Fin 6)} (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)} (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) = conjClosure S.V3 S.G1)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G))
    (htr : IsTransvectionGroupOn V (F8.Uγ S.V3 S.G1 (g : G)) (fsuV1 T V))
    (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1)
    (hUL : IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L))
    (hEq : S.U0c β = conjClosure (conjClosure S.V3 S.G1) L)
    (hZ : conjClosure S.V3 S.G1 ⊓ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) ≤ S.U1c β) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H : S.L1 ≤ S.G1 := hL1K.trans (hKT ▸ le_sup_left)
  have hTH : T ≤ S.G1 := hKT ▸ le_sup_right
  obtain ⟨τ, ρ', hρ', hN', hker', -, honto', -, -⟩ :=
    S.exists_coords hF hKT hL1K ρ hker hKA honto (Or.inr ⟨β, hβs, hβk, hβe⟩)
  have hQT : pCoreOf 2 S.G1 ≤ T := isSylowTwoOf_pCoreOf_le hF.toHypF91.sylow_H
  have hT8 : 8 ∣ Nat.card ((T.subgroupOf S.G1).map ρ') :=
    eight_dvd_card_map hF.toHypF91.sylow_H ρ' (fun h h1 => hQT ((hker' h).1 h1))
      fun σ hσ => (honto' σ hσ).elim fun k hk => ⟨k, hk.2⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  have hcL1 : c ∈ S.L1 := S.cL1_mem hhat
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcH : c ∈ S.G1 := hL1H hcL1
  have hc1 : c ≠ 1 := by
    intro h
    have h1 : S.cL1 hhat = 1 := Subtype.ext h
    have := S.cL1_rho hhat
    rw [h1, map_one] at this
    exact absurd this.symm (by decide)
  have hfp : ∀ i, ρ ⟨c, hcH⟩ i ≠ i := by
    set C' : ↥S.G1 := ⟨c, hcH⟩ with hC'
    have hC3 : C' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    have hC1 : C' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have hcl : ρ' C' ∈ cList := (hN' C').2 (S.L1T_le_NV3 (Subgroup.mem_sup_left hcL1))
    have hc3' : ρ' C' ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
    have hc1' : ρ' C' ≠ 1 := S.rho_ne_one_of_cube hker' hC3 hC1
    have hfp' := cList_fpf _ hcl hc3' hc1'
    intro i hi
    apply hfp' (τ⁻¹ i)
    rw [hρ']
    simp [Perm.mul_apply, hi]
  obtain ⟨u₁, hu₁, hu₁V⟩ : ∃ u₁ ∈ S.U1c β, u₁ ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show S.U1c β ≤ fsuV1 T V from h)
    rw [S.card_U1c hβs hβk, S.card_V1] at this
    omega
  obtain ⟨ε, hε, hrel⟩ := S.exists_rel hker hβk hβe hu₁ hu₁V hUL h13315 hF s hDH hDγ htr hA1
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  set QH := pCoreOf 2 S.G1 with hQHdef
  set QC := QH ⊓ Subgroup.centralizer (conjClosure S.V3 S.G1 : Set G) with hQCdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set C := Q ⊓ Subgroup.centralizer (S.U0c β : Set G) with hCdef
  have hUHab : IsElemAbelian 2 (conjClosure S.V3 S.G1) :=
    F7.isElemAbelian_mono hUL (le_conjClosure _ L)
  have hQHN : S.G1 ≤ Subgroup.normalizer (QH : Set G) := le_normalizer_pCoreOf 2 S.G1
  have hUHN : S.G1 ≤ Subgroup.normalizer (conjClosure S.V3 S.G1 : Set G) :=
    le_normalizer_conjClosure S.V3 S.G1
  have hRT : R ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  have hQLT : Q ≤ T := pCoreOf_le_of_sylow S.h13.sylow le_sup_right
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLTU0 := S.LT_le_normalizer_U0c hβe hβk
  have hLTC : L ⊔ T ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    mem_normalizer_inf_of (hLTQ hy) (mem_normalizer_centralizer (hLTU0 hy))
  have hH1 : 4 * nu c QH ≤ nu c R :=
    S.four_mul_nu_QH_le_nu_R hN' hker' hL1H hTH hT8 hcL1 hc3 hc1
  have hNQC : cfix c QH ≤ Subgroup.normalizer (QC : Set G) := fun y hy => by
    have hyH : y ∈ S.G1 := pCoreOf_le 2 S.G1 hy.1
    exact mem_normalizer_inf_of (hQHN hyH) (mem_normalizer_centralizer (hUHN hyH))
  have hH2 := nu_mul c (inf_le_left : QC ≤ QH) hNQC
  rw [S.relIndex_QH_QC_eq hβs hβk hβe hF hUHab hcH hc3 hfp hZ] at hH2
  have hQR : Q ≤ R := le_pCoreOf_of_le_normalizer 2 (hQLT.trans le_sup_right)
    ((sup_le_sup_right S.L1_le_L T).trans hLTQ) (pCoreOf_isPGroup 2 _)
  have hNQ : cfix c R ≤ Subgroup.normalizer (Q : Set G) := fun y hy =>
    hLTQ (Subgroup.mem_sup_right (hRT hy.1))
  have hL1 := nu_mul c hQR hNQ
  have hL1' : (cfix c R ⊔ Q).relIndex R ≤ 4 := S.relIndex_R_Q_le_four hhat
  have hNC : cfix c Q ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    hLTC (Subgroup.mem_sup_right (hQLT hy.1))
  have hL2 := nu_mul c (inf_le_left : C ≤ Q) hNC
  have hL2' : (cfix c Q ⊔ C).relIndex Q ≤ 4 :=
    S.relIndex_Q_C_le_four hβk hβe hu₁ hu₁V hhat hε hrel
  have hCQC : C ≤ QC := by
    intro y hy
    have hyH : y ∈ S.G1 := hTH (hQLT hy.1)
    have hyC : y ∈ Subgroup.centralizer (conjClosure S.V3 S.G1 : Set G) := by
      have h1 : y ∈ Subgroup.centralizer (conjClosure (conjClosure S.V3 S.G1) L : Set G) := by
        rw [← hEq]; exact hy.2
      exact Subgroup.centralizer_le (le_conjClosure _ L) h1
    exact ⟨S.cent_UH_le_QH hker hβs hβe ⟨hyH, hyC⟩, hyC⟩
  have hNC' : cfix c QC ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    hLTC (Subgroup.mem_sup_right (hQT hy.1.1))
  have hle := nu_le_nu hCQC hNC'
  have hpos : 0 < nu c QC := by
    unfold nu
    exact Nat.pos_of_ne_zero (by
      show ((cfix c QC).subgroupOf QC).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite)
  have hR1 : nu c R ≤ 16 * nu c QC := by
    rw [hL1, hL2]
    calc (cfix c R ⊔ Q).relIndex R * ((cfix c Q ⊔ C).relIndex Q * nu c C) ≤
        4 * (4 * nu c QC) := Nat.mul_le_mul hL1' (Nat.mul_le_mul hL2' hle)
      _ = 16 * nu c QC := by ring
  have hR2 : 64 * nu c QC ≤ nu c R := by
    calc 64 * nu c QC = 4 * (16 * nu c QC) := by ring
      _ = 4 * nu c QH := by rw [hH2]
      _ ≤ nu c R := hH1
  omega

end Setting4

@[expose] def Input13833CoverZH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L →
      ∀ K : Subgroup G, S.G1 ≤ Subgroup.normalizer (K : Set G) → K ⊔ T = S.G1 → S.L1 ≤ K →
        (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) →
      ∀ ρ : ↥S.G1 →* Perm (Fin 6), (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) →
        (∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6)) →
        (∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ) →
      ∀ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6), Function.Surjective β →
        (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) →
        (∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
          Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))) →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) →
        IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L) →
        conjClosure S.V3 S.G1 ⊓ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) ≤ S.U1c β

@[expose] def Input13833CoverLt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → HypF98 T V L (fsuV1 T V) S.V3 S.G1 →
      S.Struct13827 → ¬ IsHatA6 L →
      ∀ K : Subgroup G, S.G1 ≤ Subgroup.normalizer (K : Set G) → K ⊔ T = S.G1 → S.L1 ≤ K →
        (∀ h ∈ S.G1, (∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ pCoreOf 2 S.G1) → h ∈ pCoreOf 2 S.G1) →
      ∀ ρ : ↥S.G1 →* Perm (Fin 6), (∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1) →
        (∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6)) →
        (∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ) →
      ∀ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6), Function.Surjective β →
        (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) →
        (∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
          Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))) →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) = F8.Uγ S.V3 S.G1 (g : G) →
        IsElemAbelian 2 (conjClosure (conjClosure S.V3 S.G1) L) →
        S.U0c β ≠ conjClosure (conjClosure S.V3 S.G1) L → False

theorem input13833AbCover_of (h13315 : Stmt13_3_15)
    (hZH : Input13833CoverZH) (hLt : Input13833CoverLt) : Input13833AbCover := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat K hKN hKT hL1K hFs ρ hker hKA honto β hβs hβk
    hβe γ γ' g s hDγ hUL
  by_cases hEq : S.U0c β = conjClosure (conjClosure S.V3 S.G1) L
  · have hZ := hZH G T L V S hNS hNU hG1 hab hF hst hhat K hKN hKT hL1K hFs ρ hker hKA honto β hβs
      hβk hβe γ γ' g s hDγ hUL
    obtain ⟨-, -, -, -, -, -, h3⟩ := hst
    obtain ⟨hDH, -, htr, -, hnQ⟩ := h3 γ γ' g s (Or.inl hDγ)
    have hn : ¬ F8.Uγ V S.G1 (g : G) ≤ ballStab 1 (F8.γ₁ T L S.G1) := fun h =>
      hnQ (h.trans (S.ballStab_γ₁_le_QH hF hKT hL1K ρ hker hKA honto
        (Or.inr ⟨β, hβs, hβk, hβe⟩)))
    obtain ⟨hA1, -⟩ := S.case1_symm hF s hn h3 hDH
    exact S.false_coverEq h13315 hF hhat hKT hL1K hker hKA honto hβs hβk hβe s hDH hDγ htr hA1
      hUL hEq hZ
  · exact hLt G T L V S hNS hNU hG1 hab hF hst hhat K hKN hKT hL1K hFs ρ hker hKA honto β hβs hβk
      hβe γ γ' g s hDγ hUL hEq

end CFSG.Quasithin.H13.A6
