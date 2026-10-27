module

public import CFSG.Quasithin.H13.A6S13834Q
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_transv_mem_of_comm {H X A : Subgroup G} {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hA2 : ∀ b ∈ A, b = 1 ∨ b = a)
    (hAV : fsuV1 T V ⊓ A = ⊥) (hc : ⁅X, conjClosure S.V3 H⁆ = A) :
    ∃ x ∈ X, InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V) := by
  obtain ⟨x, hx, u, hu, hxu⟩ : ∃ x ∈ X, ∃ u ∈ conjClosure S.V3 H, x * u * x⁻¹ * u⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : ⁅X, conjClosure S.V3 H⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro x hx u hu
      rw [commutatorElement_def, Subgroup.mem_bot]
      exact hcon x hx u hu
    rw [hc, le_bot_iff] at hle
    exact ha1 (by rw [hle] at haA; exact (Subgroup.mem_bot.mp haA))
  have hmem : ∀ u ∈ conjClosure S.V3 H, x * u * x⁻¹ * u⁻¹ ∈ A := by
    intro u hu
    rw [← hc]
    exact Subgroup.commutator_mem_commutator hx hu
  refine ⟨x, hx, fun hall => ?_, a, fun u hu => ?_⟩
  · have h1 : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V ⊓ A := ⟨hall u hu, hmem u hu⟩
    rw [hAV, Subgroup.mem_bot] at h1
    exact hxu h1
  · rcases hA2 _ (hmem u hu) with h | h
    · left
      rw [h]
      exact (fsuV1 T V).one_mem
    · right
      rw [h, mul_inv_cancel]
      exact (fsuV1 T V).one_mem

theorem inducesTransvMod_conj {H : Subgroup G} (hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G))
    {x c : G} (hc : c ∈ H) (hx : InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) :
    InducesTransvMod (c * x * c⁻¹) (conjClosure S.V3 H) (fsuV1 T V) := by
  obtain ⟨hnot, z, hz⟩ := hx
  have hcU : ∀ u ∈ conjClosure S.V3 H, c⁻¹ * u * c ∈ conjClosure S.V3 H := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (H.inv_mem hc))
      u).mp hu
    simpa using this
  have hcV : ∀ v ∈ fsuV1 T V, c * v * c⁻¹ ∈ fsuV1 T V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (hV₁ hc) v).mp hv
  have e : ∀ u : G, c * x * c⁻¹ * u * (c * x * c⁻¹)⁻¹ * u⁻¹ =
      c * (x * (c⁻¹ * u * c) * x⁻¹ * (c⁻¹ * u * c)⁻¹) * c⁻¹ := fun u => by group
  refine ⟨fun hall => hnot fun u hu => ?_, c * z * c⁻¹, fun u hu => ?_⟩
  · have h1 := hall (c * u * c⁻¹) (by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hc) u).mp hu
      exact this)
    rw [e] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp (hV₁ (H.inv_mem hc)) _).mp h1
    have e2 : c⁻¹ * (c * (x * (c⁻¹ * (c * u * c⁻¹) * c) * x⁻¹ *
        (c⁻¹ * (c * u * c⁻¹) * c)⁻¹) * c⁻¹) * c⁻¹⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
    rwa [e2] at h2
  · rcases hz _ (hcU u hu) with h | h
    · left
      rw [e]
      exact hcV _ h
    · right
      have e2 : c * x * c⁻¹ * u * (c * x * c⁻¹)⁻¹ * u⁻¹ * (c * z * c⁻¹)⁻¹ =
          c * (x * (c⁻¹ * u * c) * x⁻¹ * (c⁻¹ * u * c)⁻¹ * z⁻¹) * c⁻¹ := by group
      rw [e2]
      exact hcV _ h

section F98

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hF : HypF98 T V L (fsuV1 T V) S.V3 H)

include hF in
theorem conjSub_VH_le_R {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) :
    conjSub (g : G)⁻¹ (conjClosure V H) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hstab' : stab γ' = conjSub (g : G) (L ⊔ T) := by
    rw [← s.edge₀, stab_smul, stab_γ₀ hF.amalgamHypV.le₁]
  have h1 := conjSub_mono (g : G)⁻¹ (hF.F913_2 s).1
  rw [← pCoreOf_conjSub, hstab, hstab', ← conjSub_inf, conjSub_conjSub_inv,
    hF.toHypF91.LT_inf_H] at h1
  exact h1

include hF in
theorem Dγ_lt_of_no_transv_loc
    (hnt : ∀ x ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T),
      ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V))
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) := by
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
  have hUγ : conjSub (g : G)⁻¹ (F8.Uγ S.V3 H (g : G)) = conjClosure S.V3 H := by
    rw [F8.Uγ, conjSub_conjSub_inv]
  have hR := S.conjSub_VH_le_R hF s
  set a : G := (g : G)⁻¹ * S.z * (g : G)⁻¹⁻¹ with ha
  have haA : a ∈ conjSub (g : G)⁻¹ (fsuV1 T V) := mul_mem_conjSub (S.mem_V1_iff.2 (Or.inr rfl))
  have ha1 : a ≠ 1 := by
    intro h1
    apply S.z_ne_one
    calc S.z = (g : G) * a * (g : G)⁻¹ := by rw [ha]; group
      _ = 1 := by rw [h1]; group
  have hA2 : ∀ b ∈ conjSub (g : G)⁻¹ (fsuV1 T V), b = 1 ∨ b = a := by
    intro b hb
    rw [mem_conjSub, inv_inv] at hb
    rcases S.mem_V1_iff.1 hb with h | h
    · left
      calc b = (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) * (g : G) := by group
        _ = 1 := by rw [h]; group
    · right
      calc b = (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) * (g : G) := by group
        _ = a := by rw [h, ha]; group
  have hAV : fsuV1 T V ⊓ conjSub (g : G)⁻¹ (fsuV1 T V) = ⊥ := by
    have := congrArg (conjSub (g : G)⁻¹) (hF.F913_5b s)
    rwa [conjSub_inf, F8.A₁, conjSub_conjSub_inv, conjSub_bot, inf_comm] at this
  rcases hF.F916_1 s hD.symm with ⟨-, htr⟩ | ⟨-, -, htr⟩
  · have hc : ⁅conjSub (g : G)⁻¹ (conjClosure S.V3 H), conjClosure S.V3 H⁆ =
        conjSub (g : G)⁻¹ (fsuV1 T V) := by
      rw [← htr.2.2, ← conjSub_commutator, hUγ]
    obtain ⟨x, hx, hxt⟩ := S.exists_transv_mem_of_comm haA ha1 hA2 hAV hc
    exact hnt x (hR (conjSub_mono _ (conjClosure_mono S.V3_le_V le_rfl) hx)) hxt
  · have hc : ⁅conjSub (g : G)⁻¹ V, conjClosure S.V3 H⁆ = conjSub (g : G)⁻¹ (fsuV1 T V) := by
      rw [← htr.2.2, ← conjSub_commutator, hUγ]
    obtain ⟨x, hx, hxt⟩ := S.exists_transv_mem_of_comm haA ha1 hA2 hAV hc
    exact hnt x (hR (conjSub_mono _ (le_conjClosure V H) hx)) hxt

include hF in
theorem case2_of_no_transv_loc
    (hnt : ∀ x ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T),
      ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) :
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g ∧
      F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) ∧
      F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H ∧
      0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
      mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
        mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', k, sk, hpos, hle, -⟩ := hF.F916_4 s (S.Dγ_lt_of_no_transv_loc hF hnt s)
  refine ⟨δ, δ', k, sk, S.Dγ_lt_of_no_transv_loc hF hnt sk, ?_, hpos, hle⟩
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDH => ?_
  have hlt := S.Dγ_lt_of_no_transv_loc hF hnt sk
  obtain ⟨ε, ε', m, y, sm, -, -, hUm, -, -, hDγm⟩ :=
    hF.exists_symmetric_setup sk (hF.not_Vγ_le_ballStab_of_lt sk hlt)
  have := S.Dγ_lt_of_no_transv_loc hF hnt sm
  rw [hDγm, hDH, hUm] at this
  exact lt_irrefl _ this

include hNS h13315 h1356two hH hF in
theorem lem13818Four_loc (h13314 : Stmt13_3_14)
    (hnt : ∀ x ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T),
      ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V))
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ')) :
    1 < mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) := by
  have hF1 := hF.toHypF91
  by_cases hD : ⁅conjClosure S.V3 H, F8.Dγ S.V3 (fsuV1 T V) H (g : G)⁆ = ⊥
  swap
  · exact S.lemma13_8_11_two hNS h13315 h1356two hH hF h13314 s hDγ hgen hle hDH hD
  set Q := pCoreOf 2 H with hQ
  set U := F8.Uγ S.V3 H (g : G) with hUdef
  set W := F8.Uγ V H (g : G) with hWdef
  have hUW : U ≤ W := hF.Uγ_le_Vγ
  have hU2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hW2 : IsPGroup 2 W := isPGroup_of_isElemAbelian hF.isElemAbelian_Vγ
  have hDQ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) = U ⊓ Q := hF.Dγ_eq_inf_pCoreOf s
  have iU : (U ⊓ Q).relIndex U = 2 ^ mIdx U (U ⊓ Q) := HypF98.relIndex_eq_two_pow_mIdx hU2
  have iW : (W ⊓ Q).relIndex W = 2 ^ mIdx W (W ⊓ Q) := HypF98.relIndex_eq_two_pow_mIdx hW2
  rw [Subgroup.inf_relIndex_left] at iU iW
  have hmono : mIdx U (U ⊓ Q) ≤ mIdx W (W ⊓ Q) := by
    have h1 := Subgroup.relIndex_le_of_le_right hUW (relIndex_ne_zero' Q W)
    rw [iU, iW] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hmU : mIdx U (U ⊓ Q) ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Subgroup.relIndex_eq_one] at iU
    rw [hDQ] at hDγ
    exact hDγ.ne (le_antisymm inf_le_left (le_inf le_rfl iU))
  by_cases h2 : 2 ≤ mIdx U (U ⊓ Q)
  · omega
  exfalso
  have hm1 : mIdx U (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by rw [hDQ]; omega
  obtain ⟨δ, δ', k, y, sk, -, -, hUδ, hUHy, hDHk, hDγk⟩ :=
    hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s hDγ)
  have hUδH : F8.Uγ S.V3 H (k : G) ≤ H := hF.Uγ_le_H sk
  have hDγk' : F8.Dγ S.V3 (fsuV1 T V) H (k : G) < F8.Uγ S.V3 H (k : G) := by
    rw [hDγk, hUδ]
    exact lt_of_le_of_ne (conjSub_mono _ hDH.le) fun e => hDH.ne ((conjSub_inj _).1 e)
  obtain ⟨x, hxU, hxD⟩ := IsConcreteLE.exists_of_lt hDγk'
  have hxH : x ∈ H := hUδH hxU
  have hxc : ∀ u ∈ F8.DH S.V3 (fsuV1 T V) H (k : G), x * u = u * x := by
    intro u hu
    rw [hDHk, mem_conjSub] at hu
    rw [hUδ, mem_conjSub] at hxU
    have h1 := Subgroup.commutator_mem_commutator hxU hu
    rw [hD, Subgroup.mem_bot, commutatorElement_def] at h1
    have e : x * u = (y : G) * ((((y : G)⁻¹ * x * y) * ((y : G)⁻¹ * u * y) *
        ((y : G)⁻¹ * x * y)⁻¹ * ((y : G)⁻¹ * u * y)⁻¹) * (((y : G)⁻¹ * u * y) *
        ((y : G)⁻¹ * x * y))) * (y : G)⁻¹ := by group
    rw [e, h1, one_mul]
    group
  have hUH2 : IsPGroup 2 (conjClosure S.V3 H) :=
    (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
  have hidx : (F8.DH S.V3 (fsuV1 T V) H (k : G)).relIndex (conjClosure S.V3 H) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUH2, ← hUHy, hDHk, F9.mIdx_conjSub, hm1, pow_one]
  have hidx' : ((F8.DH S.V3 (fsuV1 T V) H (k : G)).subgroupOf (conjClosure S.V3 H)).index = 2 :=
    hidx
  have hDHlt : F8.DH S.V3 (fsuV1 T V) H (k : G) < conjClosure S.V3 H := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun e => ?_
    rw [e, Subgroup.relIndex_self] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨u₀, hu₀U, hu₀D⟩ := IsConcreteLE.exists_of_lt hDHlt
  have hxt : InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V) := by
    refine ⟨fun hall => hxD ⟨hxU, hF1.H_normalizes_V₁ hxH, hall⟩, x * u₀ * x⁻¹ * u₀⁻¹,
      fun u hu => ?_⟩
    by_cases huD : u ∈ F8.DH S.V3 (fsuV1 T V) H (k : G)
    · left
      rw [hxc u huD, mul_inv_cancel_right, mul_inv_cancel]
      exact (fsuV1 T V).one_mem
    · right
      have hd : u₀⁻¹ * u ∈ F8.DH S.V3 (fsuV1 T V) H (k : G) := by
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx'
          (a := (⟨u₀, hu₀U⟩ : ↥(conjClosure S.V3 H))⁻¹) (b := ⟨u, hu⟩)).2
          ⟨fun h => absurd (by simpa using (Subgroup.mem_subgroupOf.1 h)) (fun h' => hu₀D
            (by simpa using (F8.DH S.V3 (fsuV1 T V) H (k : G)).inv_mem h')),
            fun h => absurd (Subgroup.mem_subgroupOf.1 h) huD⟩
        simpa using Subgroup.mem_subgroupOf.1 h1
      have hcd := hxc _ hd
      have e : x * u * x⁻¹ * u⁻¹ * (x * u₀ * x⁻¹ * u₀⁻¹)⁻¹ =
          (x * u₀ * x⁻¹) * ((x * (u₀⁻¹ * u)) * x⁻¹ * (u₀⁻¹ * u)⁻¹) * (x * u₀ * x⁻¹)⁻¹ := by
        group
      rw [e, hcd]
      convert (fsuV1 T V).one_mem using 1
      group
  obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF sk
  exact hnt _ (hcR (mul_mem_conjSub (hF.Uγ_le_Vγ hxU)))
    (S.inducesTransvMod_conj hF1.H_normalizes_V₁ hcH hxt)

end F98

end Setting4

end CFSG.Quasithin.H13.A6
