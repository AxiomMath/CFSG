module

public import CFSG.Quasithin.H13.A6S1384a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_transv_of_comm {H X A : Subgroup G} {a : G} (hXH : X ≤ H) (haA : a ∈ A)
    (ha1 : a ≠ 1) (hA2 : ∀ b ∈ A, b = 1 ∨ b = a)
    (hAV : fsuV1 T V ⊓ A = ⊥) (hc : ⁅X, conjClosure S.V3 H⁆ = A) :
    ∃ h ∈ H, InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V) := by
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
  refine ⟨x, hXH hx, fun hall => ?_, a, fun u hu => ?_⟩
  ·
    have h1 : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V ⊓ A := ⟨hall u hu, hmem u hu⟩
    rw [hAV, Subgroup.mem_bot] at h1
    exact hxu h1
  · rcases hA2 _ (hmem u hu) with h | h
    · left
      rw [h]
      exact (fsuV1 T V).one_mem
    · right
      rw [h, mul_inv_cancel]
      exact (fsuV1 T V).one_mem

section F98

variable {H : Subgroup G} (hF : HypF98 T V L (fsuV1 T V) S.V3 H)
include hF

theorem Dγ_lt_of_no_transv
    (hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V))
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) := by
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
  have hUγ : conjSub (g : G)⁻¹ (F8.Uγ S.V3 H (g : G)) = conjClosure S.V3 H := by
    rw [F8.Uγ, conjSub_conjSub_inv]
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hVst : conjClosure V H ≤ stab γ :=
    (hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans inf_le_right)
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
  ·
    have hXH : conjSub (g : G)⁻¹ (conjClosure S.V3 H) ≤ H := by
      rw [conjSub_le_iff, inv_inv, ← hstab]
      exact (conjClosure_mono S.V3_le_V le_rfl).trans hVst
    have hc : ⁅conjSub (g : G)⁻¹ (conjClosure S.V3 H), conjClosure S.V3 H⁆ =
        conjSub (g : G)⁻¹ (fsuV1 T V) := by
      rw [← htr.2.2, ← conjSub_commutator, hUγ]
    obtain ⟨h, hh, hht⟩ := S.exists_transv_of_comm hXH haA ha1 hA2 hAV hc
    exact hnt h hh hht
  ·
    have hXH : conjSub (g : G)⁻¹ V ≤ H := by
      rw [conjSub_le_iff, inv_inv, ← hstab]
      exact (le_conjClosure V H).trans hVst
    have hc : ⁅conjSub (g : G)⁻¹ V, conjClosure S.V3 H⁆ = conjSub (g : G)⁻¹ (fsuV1 T V) := by
      rw [← htr.2.2, ← conjSub_commutator, hUγ]
    obtain ⟨h, hh, hht⟩ := S.exists_transv_of_comm hXH haA ha1 hA2 hAV hc
    exact hnt h hh hht

theorem case2_of_no_transv
    (hnt : ∀ h ∈ H, ¬ InducesTransvMod h (conjClosure S.V3 H) (fsuV1 T V)) :
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g ∧
      F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G) ∧
      F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H ∧
      0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
      mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
        mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) ∧
      autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 H (g : G)))
          (tildeOf (fsuV1 T V) (conjClosure S.V3 H)) ∈
        @Qset ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 H))
          (commGroupOfElemAbelian hF.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) := by
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', k, sk, hpos, hle, hQ⟩ := hF.F916_4 s (S.Dγ_lt_of_no_transv hF hnt s)
  refine ⟨δ, δ', k, sk, S.Dγ_lt_of_no_transv hF hnt sk, ?_, hpos, hle, hQ⟩
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDH => ?_
  have hlt := S.Dγ_lt_of_no_transv hF hnt sk
  obtain ⟨ε, ε', m, y, sm, -, -, hUm, -, -, hDγm⟩ :=
    hF.exists_symmetric_setup sk (hF.not_Vγ_le_ballStab_of_lt sk hlt)
  have := S.Dγ_lt_of_no_transv hF hnt sm
  rw [hDγm, hDH, hUm] at this
  exact lt_irrefl _ this

end F98

end Setting4

end CFSG.Quasithin.H13.A6
