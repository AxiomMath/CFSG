module

public import CFSG.Literature.GL52Basic
public import CFSG.Quasithin.Vol2.KGFactMinParL52Inputs
import CFSG.Quasithin.Vol2.KGFactL52Parabolics

namespace Certificates

open CFSG.Quasithin.H13

noncomputable def l52SLEquiv :
    Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) ≃* CFSG.Literature.GL52.G :=
  MulEquiv.ofBijective _ CFSG.Literature.GL52.bijective_toGL

theorem l52_cuts_incl : ∀ i < 15, ∀ j < 15,
    (L52Par.cuts j ⊆ L52Par.cuts i ↔ j ∈ KGMinPar.l52Incl.getD i []) := by
  decide +kernel

theorem l52_ordIdx : ∀ j < 15, L52Par.ordIdx.getD j 0 * 1024 =
    [1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3].getD j 0 * 2 ^ 10 := by
  decide +kernel

public section

theorem certificate7156 : ∃ Y : ℕ → Subgroup CFSG.Literature.GL52.G,
    Nat.card (Y 0) = 2 ^ 10 ∧
    (∀ j < 15, Y 0 ≤ Y j ∧
      Nat.card (Y j) = [1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3].getD j 0 * 2 ^ 10) ∧
    (∀ i < 15, ∀ j < 15, Y i ≤ Y j ↔ j ∈ CFSG.Quasithin.H13.KGMinPar.l52Incl.getD i []) ∧
    ∀ Z : Subgroup CFSG.Literature.GL52.G, Y 0 ≤ Z → Z = ⊤ ∨ ∃ j < 15, Z = Y j := by
  set e := l52SLEquiv
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hcard : ∀ j < 15, Nat.card ((L52Par.Yq j).map e.toMonoidHom) =
      [1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3].getD j 0 * 2 ^ 10 := fun j hj => by
    rw [Subgroup.card_map_of_injective hinj, L52Par.card_Yq j hj, l52_ordIdx j hj]
  have hle0 : ∀ j, L52Par.Yq 0 ≤ L52Par.Yq j := fun j => by
    rw [L52Par.Yq_zero]
    exact L52Par.U_le_Yq j
  refine ⟨fun j => (L52Par.Yq j).map e.toMonoidHom, hcard 0 (by norm_num), fun j hj =>
    ⟨Subgroup.map_mono (hle0 j), hcard j hj⟩, fun i hi j hj => ?_, fun Z hZ => ?_⟩
  · rw [Subgroup.map_le_map_iff_of_injective hinj, L52Par.Yq_le_iff hj, l52_cuts_incl i hi j hj]
  · have hle : L52Par.Yq 0 ≤ Z.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.1 hZ
    have hZ' : Z = (Z.comap e.toMonoidHom).map e.toMonoidHom :=
      (Subgroup.map_comap_eq_self_of_surjective e.surjective Z).symm
    rw [L52Par.Yq_zero] at hle
    rcases L52Par.eq_top_or_Yq hle with h | ⟨j, hj, h⟩
    · left
      rw [hZ', h, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    · right
      exact ⟨j, hj, by rw [hZ', h]⟩

end

end Certificates
