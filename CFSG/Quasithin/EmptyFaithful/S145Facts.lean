module

public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

section Fifteen

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.lemma_14_5_15_one (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H) ≤
        omegaOneCenterOf (tildeOf (quasithinOmegaOneCenter T) (pCoreOf 2 H)) ∧
      IsTwoReducedIn (tildeOf (quasithinOmegaOneCenter T) H)
        (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) H)) :=
  S.hyp1281.lemma_12_8_4_two (S.isHz_iff.mpr hH)

theorem Setting146.lemma_14_5_15_two (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    IsElemAbelian 2 (conjClosure (VZ T M) H) :=
  (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.F911_3

theorem Setting146.lemma_14_5_15_four (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
  S.hyp1281.lemma_12_8_4_four (S.isHz_iff.mpr hH)

end Fifteen

section Seventeen

variable {G : Type} [Group G] [Finite G] {T V L V₁ H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

theorem HypF98.lemma_14_5_17 (h : HypF98 T V L V₁ V H) (s : F8Setup T V L H γ γ' g) :
    F8.DH V V₁ H (g : G) < conjClosure V H := by
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun heq => ?_
  apply h.F913_5a s
  have hV : V ≤ F8.DH V V₁ H (g : G) := heq ▸ le_conjClosure V H
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have h1 : v * u * v⁻¹ * u⁻¹ ∈ F8.A₁ V₁ (g : G) := (hV hv).2.2 u hu
  have h2 := (F8.A₁ V₁ (g : G)).inv_mem h1
  have e : (v * u * v⁻¹ * u⁻¹)⁻¹ = u * v * u⁻¹ * v⁻¹ := by group
  rwa [e] at h2

theorem mIdx_pos_of_lt_of_isPGroup {X Y : Subgroup G} (hX : IsPGroup 2 X) (hlt : Y < X) :
    0 < mIdx X Y := by
  have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := Y) hX
  have h2 : Y.relIndex X ≠ 1 := fun e => absurd (Subgroup.relIndex_eq_one.mp e) (not_le_of_gt hlt)
  rcases Nat.eq_zero_or_pos (mIdx X Y) with h0 | h0
  · exact absurd (by rw [h1, h0]; rfl) h2
  · exact h0

theorem HypF98.lemma_14_5_18_one (h : HypF98 T V L V₁ V H) (s : F8Setup T V L H γ γ' g)
    (hD : F8.Uγ V H (g : G) = F8.Dγ V V₁ H (g : G)) :
    IsTransvectionGroupOn (conjClosure V H) (F8.Uγ V H (g : G)) V₁ := by
  rcases h.F916_1 s hD with h1 | h2
  · exact h1.2
  · exact absurd h2.1 (h.lemma_14_5_17 s).ne

theorem HypF98.lemma_14_5_18_two (h : HypF98 T V L V₁ V H) (s : F8Setup T V L H γ γ' g)
    (hle : mIdx (conjClosure V H) (F8.DH V V₁ H (g : G)) ≤
      mIdx (F8.Uγ V H (g : G)) (F8.Dγ V V₁ H (g : G))) :
    0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V V₁ H (g : G)) ∧
      autOn (tildeOf V₁ (F8.Uγ V H (g : G))) (tildeOf V₁ (conjClosure V H)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure V H))
            (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))) ∧
        (2 * mIdx (F8.Uγ V H (g : G)) (F8.Dγ V V₁ H (g : G)) =
            mIdx (conjClosure V H) (centralizerMod V₁ (conjClosure V H) (F8.Uγ V H (g : G))) →
          mIdx (F8.Uγ V H (g : G)) (F8.Dγ V V₁ H (g : G)) =
              mIdx (conjClosure V H) (F8.DH V V₁ H (g : G)) ∧
            centralizerMod V₁ (F8.Uγ V H (g : G)) (F8.DH V V₁ H (g : G)) =
              F8.Dγ V V₁ H (g : G) ∧
            ⁅F8.Uγ V H (g : G), F8.DH V V₁ H (g : G)⁆ ≤ F8.A₁ V₁ (g : G) ∧
            Nat.card (F8.A₁ V₁ (g : G)) = 2 ∧ F8.A₁ V₁ (g : G) ⊓ V₁ = ⊥ ∧
            F8.Dγ V V₁ H (g : G) < F8.Uγ V H (g : G)) := by
  have hpos : 0 < mIdx (conjClosure V H) (F8.DH V V₁ H (g : G)) :=
    mIdx_pos_of_lt_of_isPGroup (isPGroup_of_isElemAbelian h.F911_3) (h.lemma_14_5_17 s)
  have hpos' : 0 < mIdx (F8.Uγ V H (g : G)) (F8.Dγ V V₁ H (g : G)) := lt_of_lt_of_le hpos hle
  exact ⟨hpos', h.F916_2 s hpos' hle⟩

theorem HypF98.lemma_14_5_18_three (h : HypF98 T V L V₁ V H) :
    qInt (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H)) h.toHypF91.isElemAbelian_tilde ≤ 2 ∧
      ∃ B : Subgroup G, B ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) ∧
        autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure V H)) ∈
          @Qset ↥(tildeOf V₁ (conjClosure V H))
            (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))) :=
  h.F916_3

theorem HypF98.lemma_14_5_18_four (h : HypF98 T V L V₁ V H) (s : F8Setup T V L H γ γ' g)
    (hlt : F8.Dγ V V₁ H (g : G) < F8.Uγ V H (g : G)) :
    ∃ (δ δ' : F8.Geom T L H) (k : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H δ δ' k ∧
      0 < mIdx (F8.Uγ V H (k : G)) (F8.Dγ V V₁ H (k : G)) ∧
      mIdx (conjClosure V H) (F8.DH V V₁ H (k : G)) ≤
        mIdx (F8.Uγ V H (k : G)) (F8.Dγ V V₁ H (k : G)) ∧
      autOn (tildeOf V₁ (F8.Uγ V H (k : G))) (tildeOf V₁ (conjClosure V H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure V H))
          (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))) :=
  h.F916_4 s hlt

end Seventeen

end CFSG.Quasithin
