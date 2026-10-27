module

public import CFSG.Quasithin.EmptyFaithful.S143ED
public import CFSG.Quasithin.EmptyFaithful.S143EB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Counting

variable {G : Type*} [Group G]

theorem card_map_mul_card_inf_ker {H X : Subgroup G} (hXH : X ≤ H) {B : Type*} [Group B]
    (f : ↥H →* B) :
    Nat.card ↥((X.subgroupOf H).map f) * Nat.card ↥(X ⊓ f.ker.map H.subtype) =
      Nat.card X := by
  set S : Subgroup ↥H := X.subgroupOf H with hS
  have hSX : S.map H.subtype = X := by
    rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXH]
  have h1 := Subgroup.card_ker_mul_card_range (f.comp S.subtype)
  have hrange : (f.comp S.subtype).range = S.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : (f.comp S.subtype).ker = f.ker.subgroupOf S := rfl
  have hcardS : Nat.card ↥S = Nat.card X := by
    rw [← hSX]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  have hkerc : Nat.card (f.ker.subgroupOf S) = Nat.card ↥(X ⊓ f.ker.map H.subtype) := by
    have e1 : Nat.card (f.ker.subgroupOf S) = Nat.card ↥(S ⊓ f.ker) := by
      have := Subgroup.card_map_of_injective (f := S.subtype) S.subtype_injective
        (K := f.ker.subgroupOf S)
      rw [Subgroup.subgroupOf_map_subtype] at this
      rw [← this, inf_comm]
    rw [e1, ← Subgroup.card_map_of_injective H.subtype_injective (K := S ⊓ f.ker),
      Subgroup.map_inf_eq _ _ _ H.subtype_injective, hSX]
  rw [hker, hrange, hcardS, hkerc] at h1
  rw [mul_comm]
  exact h1

theorem card_imageOTwoQuot_mul {H X : Subgroup G} (hXH : X ≤ H) :
    Nat.card ↥(imageOTwoQuot H X) * Nat.card ↥(X ⊓ pCoreOf 2 H) = Nat.card X := by
  have := card_map_mul_card_inf_ker hXH (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  rw [QuotientGroup.ker_mk'] at this
  exact this

end Counting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section VEq

theorem inf_rconj_uOfL22_le_rconj_wOfU {g : G} (c : Counter T M g) :
    mcOf T ⊓ rconj (uOfL22 T M) g ≤ rconj (Hyp1281Two.wOfU T M) g := by
  have h := c.h1281
  have hg := c.goodElt
  obtain ⟨z, a, hzZ, hz1, rfl, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  intro y hy
  obtain ⟨hyH, hyU'⟩ := Subgroup.mem_inf.mp hy
  have hyU : g * y * g⁻¹ ∈ uOfL22 T M := mem_rconj.mp hyU'
  refine mem_rconj.mpr ⟨hyU, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hu : g * y * g⁻¹ ∈ mcOf T := h.uOfL22_le_g1 hyU
  have hyz : z * y = y * z := Subgroup.mem_centralizer_iff.mp hyH z hzZ
  have huz : z * (g * y * g⁻¹) = (g * y * g⁻¹) * z := Subgroup.mem_centralizer_iff.mp hu z hzZ
  have hua : (g * z * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * z * g⁻¹) := by
    have e1 : (g * z * g⁻¹) * (g * y * g⁻¹) = g * (z * y) * g⁻¹ := by group
    have e2 : (g * y * g⁻¹) * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
    rw [e1, e2, hyz]
  rcases hcases w hw with rfl | rfl | rfl | rfl
  · simp
  · exact huz
  · exact hua
  · calc (z * (g * z * g⁻¹)) * (g * y * g⁻¹)
        = z * ((g * z * g⁻¹) * (g * y * g⁻¹)) := mul_assoc _ _ _
      _ = z * ((g * y * g⁻¹) * (g * z * g⁻¹)) := by rw [hua]
      _ = (z * (g * y * g⁻¹)) * (g * z * g⁻¹) := (mul_assoc _ _ _).symm
      _ = ((g * y * g⁻¹) * z) * (g * z * g⁻¹) := by rw [huz]
      _ = (g * y * g⁻¹) * (z * (g * z * g⁻¹)) := mul_assoc _ _ _

theorem v_eq_of {g : G} (c : Counter T M g) :
    VZ T M = qOf T ⊓ conjSubgroup (uOfL22 T M) g := by
  have h := c.h1281
  have hg := c.goodElt
  apply le_antisymm
  · intro v hv
    refine ⟨uOfL22_le_qOf c (Hyp1281Two.VZ_le_uOfL22 T M hv), ?_⟩
    have hgLT : g ∈ yOfL22 T M ⊔ T := Subgroup.mem_sup_left hg.mem
    have hgV : g ∈ Subgroup.normalizer (VZ T M : Set G) := h.LT_le_normalizer_VZ hgLT
    exact mem_conjSubgroup_iff.mpr
      (Hyp1281Two.VZ_le_uOfL22 T M ((Subgroup.mem_normalizer_iff.mp hgV v).mp hv))
  · rintro y ⟨hyQ, hyU⟩
    have hyH : y ∈ mcOf T := pCoreOf_le 2 _ hyQ
    have hyW : y ∈ rconj (Hyp1281Two.wOfU T M) g :=
      inf_rconj_uOfL22_le_rconj_wOfU c ⟨hyH, hyU⟩
    rw [← qOf_inf_rconj c]
    exact ⟨hyQ, hyW⟩

end VEq

section Orders

variable {g : G} (c : Counter T M g)

include c

theorem rOf_le_mcOf : rOf T M ≤ mcOf T :=
  (rOf_le_T_of_hyp c.h1281).trans c.h1281.almostSpecialHyp_g1.T_le_H

theorem rstar_card_of : Nat.card ↥(imageOTwoQuot (mcOf T) (rOf T M)) = 4 := by
  have h1 := card_imageOTwoQuot_mul (rOf_le_mcOf c)
  have h2 : rOf T M ⊓ pCoreOf 2 (mcOf T) = Hyp1281Two.wOfU T M := rOf_inf_qOf c
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  rw [h2, hW, card_rOf c] at h1
  omega

theorem M_le_normalizer_rOf : M ≤ Subgroup.normalizer (rOf T M : Set G) :=
  (normal_i2_of_hyp c.h1281).trans (normalizer_le_normalizer_pCoreOf 2 (iTwo T M))

theorem qOf_le_normalizer_rOf : qOf T ≤ Subgroup.normalizer (rOf T M : Set G) :=
  (qOf_le_T_of_hyp c.h1281).trans (c.hyp.m_max.1.2.trans (M_le_normalizer_rOf c))

theorem card_rOf_sup_qOf : Nat.card ↥(rOf T M ⊔ qOf T) = 4 * Nat.card ↥(qOf T) := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer (qOf_le_normalizer_rOf c)
  have h2 : rOf T M ⊓ qOf T = Hyp1281Two.wOfU T M := rOf_inf_qOf c
  have hW : Nat.card (Hyp1281Two.wOfU T M) = 16 := card_wOf c
  rw [h2, hW, card_rOf c] at h1
  omega

end Orders

section Action

variable {g : G} (c : Counter T M g)

include c

theorem ker_actTilde_map
    (hHN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    (hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) :
    (actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) hHN hHU).ker.map
        (mcOf T).subtype = qOf T := by
  rw [← centralizerMod_eq_qOf c]
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hHN h.2, (actTilde_eq_one_iff _ _ _ hHN hHU hUN h).mp (MonoidHom.mem_ker.mp hh)⟩
  · intro hx
    exact ⟨⟨x, hx.1⟩, MonoidHom.mem_ker.mpr
      ((actTilde_eq_one_iff _ _ _ hHN hHU hUN ⟨x, hx.1⟩).mpr hx.2.2), rfl⟩

theorem card_T_eq : Nat.card T = 8 * Nat.card ↥(qOf T) := by
  have h := c.h1281
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  have hHN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    h.uOfL22_le_g1.trans hHN
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M)) :=
    { (inferInstance : Group ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) with
      mul_comm := fun a b => (tilde_isMulCommutative h).is_comm.comm a b }
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType
    (W := ↥(tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M))) (q := q)
    (tilde_mul_self h) hq4 hq1 hq2 hq3
  set ρ := actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) hHN hHU with hρ
  have hrange : ρ.range = orthogonalGroupOf q :=
    (range_actTilde _ _ _ hHN hHU).trans hq6
  have hT' : IsSylowTwoOf ((T.subgroupOf (mcOf T)).map ρ) (orthogonalGroupOf q) := by
    have := isSylowTwoOf_map_range' (sylow_G1_of_hyp h) ρ
    rwa [hrange] at this
  have h8 : Nat.card ↥((T.subgroupOf (mcOf T)).map ρ) = 8 := hS.card_T hT'
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have h1 := card_map_mul_card_inf_ker hTH ρ
  rw [ker_actTilde_map c hHN hHU hUN, inf_eq_right.mpr (qOf_le_T_of_hyp h), h8] at h1
  exact h1.symm

theorem rq_index_of : (rOf T M ⊔ qOf T).relIndex T = 2 := by
  have h1 := Subgroup.relIndex_mul_card (rOf T M ⊔ qOf T) T
  rw [inf_eq_left.mpr (rq_le_of_hyp c.h1281), card_rOf_sup_qOf c, card_T_eq c] at h1
  have hpos : 0 < Nat.card ↥(qOf T) := Nat.card_pos
  nlinarith

end Action

end S143

end CFSG.Quasithin
