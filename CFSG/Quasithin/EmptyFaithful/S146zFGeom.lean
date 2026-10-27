module

public import CFSG.Quasithin.EmptyFaithful.S146zFNoFF
public import CFSG.Quasithin.EmptyFaithful.S146zRank2
public import CFSG.Quasithin.EmptyFaithful.S146F16

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Comm

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem commutator_U_le (S : Setting146 G T M) (c23 : Conc14623 T M) {E : Subgroup G}
    (hEH : E ≤ mcOf T) :
    ⁅uOfL22 T M, E⁆ ≤ ⁅uOfL22 T M, perfectCore (mcOf T)⁆ ⊔ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hcommU : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure ha hb
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hHZ : mcOf T ≤ Subgroup.normalizer (Zz : Set G) := fun x hx => by
    rw [S.normalizer_Z]; exact hx
  have hcperf : perfectCore (mcOf T) ≤ mcOf T := perfectCore_le _
  have hHnorm : mcOf T ≤ Subgroup.normalizer ((perfectCore (mcOf T) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcperf).mp (perfectCore_normal _)
  set P := perfectCore (mcOf T) with hP
  set W : Subgroup G := ⁅uOfL22 T M, P⁆ ⊔ Zz with hW
  have hWU : W ≤ uOfL22 T M :=
    sup_le (S145.commutator_le_of_le_normalizer (hcperf.trans hHU)) (Z_le_conjClosure_VZ T M (mcOf T))
  have hZW : Zz ≤ W := le_sup_right
  have hcuN : cuOf T M ≤ Subgroup.normalizer (Zz : Set G) := (cuOf_le T M).trans hUN
  have hWN : W ≤ Subgroup.normalizer (Zz : Set G) := hWU.trans hUN
  have h3 := c23.2.2.1
  have hle1 : (⨆ K' ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K'⁆) ≤ tildeOf Zz W := by
    refine iSup₂_le fun K' hK' => secImg_mono ?_
    exact (Subgroup.commutator_mono le_rfl
      (le_perfectCore_of_perfect (le_of_mem_cComp hK') (perfect_of_mem_cComp hK'))).trans le_sup_left
  have h4 : tildeOf Zz (uOfL22 T M) ≤ tildeOf Zz (W ⊔ cuOf T M) := by
    rw [tildeOf_sup hWN hcuN, h3]
    exact sup_le_sup_right hle1 _
  have hdec : ∀ u ∈ uOfL22 T M, ∃ p ∈ W, ∃ c ∈ cuOf T M, u = p * c := by
    intro u hu
    have huN : u ∈ Subgroup.normalizer (Zz : Set G) := hUN hu
    have h5 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨u, huN⟩ ∈ tildeOf Zz (W ⊔ cuOf T M) :=
      h4 (secMk_mem_secImg (x := ⟨u, huN⟩) hu)
    have h6 : u ∈ W ⊔ cuOf T M :=
      (secMk_mem_secImg_iff (x := ⟨u, huN⟩) (hZW.trans le_sup_left)).mp h5
    have hN : W ≤ Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) :=
      le_normalizer_of_forall_commute fun x hx y hy => hcommU x (hWU hx) y (cuOf_le T M hy)
    have h7 : u ∈ ((W ⊔ cuOf T M : Subgroup G) : Set G) := h6
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at h7
    obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.mp h7
    exact ⟨p, hp, c, hc, rfl⟩
  rw [Subgroup.commutator_le]
  intro u hu e he
  have heH : e ∈ mcOf T := hEH he
  obtain ⟨p, hp, c, hc, rfl⟩ := hdec u hu
  have hpU := hWU hp
  have hcU := cuOf_le T M hc
  have hepW : e * p * e⁻¹ ∈ W := by
    have hN : e ∈ Subgroup.normalizer (W : Set G) :=
      mem_normalizer_commutator_sup (hHnorm heH) (hHU heH) (hHZ heH)
    exact (Subgroup.mem_normalizer_iff.mp hN p).mp hp
  have hecU : e * c * e⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp (hHU heH) c).mp hcU
  have hepU : e * p * e⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp (hHU heH) p).mp hpU
  have h1 : c * e * c⁻¹ * e⁻¹ ∈ Zz := (mem_cuOf.mp hc).2.2 e heH
  have key : (p * c) * e * (p * c)⁻¹ * e⁻¹ =
      (p * (e * p * e⁻¹)⁻¹) * (c * e * c⁻¹ * e⁻¹) := by
    have e1 : (p * c) * e * (p * c)⁻¹ * e⁻¹ = (p * c) * (e * (p * c) * e⁻¹)⁻¹ := by group
    rw [e1]
    have e2 : e * (p * c) * e⁻¹ = (e * p * e⁻¹) * (e * c * e⁻¹) := by group
    rw [e2]
    have e3 : (p * c) * ((e * p * e⁻¹) * (e * c * e⁻¹))⁻¹ =
        p * c * (e * c * e⁻¹)⁻¹ * (e * p * e⁻¹)⁻¹ := by group
    rw [e3]
    have hcomm : c * (e * c * e⁻¹)⁻¹ * (e * p * e⁻¹)⁻¹ = (e * p * e⁻¹)⁻¹ * (c * (e * c * e⁻¹)⁻¹) :=
      hcommU _ ((uOfL22 T M).mul_mem hcU ((uOfL22 T M).inv_mem hecU)) _ ((uOfL22 T M).inv_mem hepU)
    calc p * c * (e * c * e⁻¹)⁻¹ * (e * p * e⁻¹)⁻¹
        = p * (c * (e * c * e⁻¹)⁻¹ * (e * p * e⁻¹)⁻¹) := by group
      _ = p * ((e * p * e⁻¹)⁻¹ * (c * (e * c * e⁻¹)⁻¹)) := by rw [hcomm]
      _ = (p * (e * p * e⁻¹)⁻¹) * (c * e * c⁻¹ * e⁻¹) := by group
  rw [commutatorElement_def, key]
  exact W.mul_mem (W.mul_mem hp (W.inv_mem hepW)) (hZW h1)

end Comm


section Main

theorem mIdx_le_of_relIndex_le {G : Type} [Group G] [Finite G] {X Y X' Y' : Subgroup G}
    (hX : IsPGroup 2 X) (hX' : IsPGroup 2 X') (h : Y.relIndex X ≤ Y'.relIndex X') :
    mIdx X Y ≤ mIdx X' Y' := by
  rw [HypF98.relIndex_eq_two_pow_mIdx hX, HypF98.relIndex_eq_two_pow_mIdx hX'] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem input14624Geom_of (hNo : NoFaithfulFFInput) (h21 : Stage14621) (h22 : Stage14622) :
    Input14624Geom := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx
  classical
  obtain ⟨c19, c20, c23, hK, c21, c22, hdec, hch⟩ := hctx
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  obtain ⟨hF81, hF98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hG)
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUp : IsPGroup 2 (uOfL22 T M) := isPGroup_of_isElemAbelian hUab
  have hnoFF : ∀ B : Subgroup G, B ≤ mcOf T → IsElemAbelian 2 B → ¬ B ≤ pCoreOf 2 (mcOf T) →
      mIdx B (B ⊓ pCoreOf 2 (mcOf T)) <
        mIdx (uOfL22 T M) (centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M) B) :=
    fun B hBH hBel hnt => noFF_ctx hNo h21 h22 S hB c19 c20 c23 hK c21 hdec hBH hBel hnt
  have hcontra : ∀ B : Subgroup G, B ≤ mcOf T → IsElemAbelian 2 B → ¬ B ≤ pCoreOf 2 (mcOf T) →
      (centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M) B).relIndex (uOfL22 T M) ≤
        (B ⊓ pCoreOf 2 (mcOf T)).relIndex B → False := by
    intro B hBH hBel hnt hr
    have h1 := hnoFF B hBH hBel hnt
    have h2 := mIdx_le_of_relIndex_le hUp (isPGroup_of_isElemAbelian hBel) hr
    omega
  obtain ⟨γ₀, γ₀', g₀, s₀⟩ := hF98.exists_F8Setup
  have hlt₀ : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g₀ : G) <
      F8.Uγ (VZ T M) (mcOf T) (g₀ : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
    rcases hF98.F916_1 s₀ hD.symm with ⟨-, -, -, hT⟩ | ⟨-, -, -, -, hT⟩
    · obtain ⟨B, hBH, hBel, hnt, hr⟩ := hF98.exists_ffOffender_of_transvection s₀ hF98.F911_3
        (hF98.V₁_le_Vp.trans (le_conjClosure _ _)) le_rfl hT
      exact hcontra B hBH hBel hnt hr
    · obtain ⟨B, hBH, hBel, hnt, hr⟩ := hF98.exists_ffOffender_of_transvection s₀ hF98.elemAbelian
        hF98.V₁_le_V (le_conjClosure _ _) hT
      exact hcontra B hBH hBel hnt hr
  obtain ⟨δ, δ', k, sk, hposr, hle, -⟩ := hF98.lemma_14_5_18_four s₀ hlt₀
  have hpos : 0 < mIdx (conjClosure (VZ T M) (mcOf T))
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G)) :=
    mIdx_pos_of_lt_of_isPGroup hUp (hF98.lemma_14_5_17 sk)
  have hDeq := hF98.Dγ_eq_inf_pCoreOf sk
  have hDlt : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G) <
      F8.Uγ (VZ T M) (mcOf T) (k : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
    rw [hD] at hposr
    unfold mIdx at hposr
    rw [Subgroup.relIndex_self] at hposr
    simp at hposr
  have hUγH := hF98.Uγ_le_H sk
  have hnt : ¬ F8.Uγ (VZ T M) (mcOf T) (k : G) ≤ pCoreOf 2 (mcOf T) := fun h => by
    have : F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G) =
        F8.Uγ (VZ T M) (mcOf T) (k : G) := by rw [hDeq]; exact inf_eq_left.mpr h
    exact hDlt.ne this
  have hlt : mIdx (F8.Uγ (VZ T M) (mcOf T) (k : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (k : G)) <
      mIdx (conjClosure (VZ T M) (mcOf T)) (centralizerMod (quasithinOmegaOneCenter T)
        (conjClosure (VZ T M) (mcOf T)) (F8.Uγ (VZ T M) (mcOf T) (k : G))) := by
    have := hnoFF _ hUγH hF98.isElemAbelian_Uγ hnt
    rwa [← hDeq] at this
  have hA₁ := A₁_le_commutator_strict S hle hlt
  exact ⟨δ, δ', k, sk, hDlt, hpos, hle, hlt, hA₁.trans (commutator_U_le S c23 hUγH)⟩

end Main

end CFSG.Quasithin
