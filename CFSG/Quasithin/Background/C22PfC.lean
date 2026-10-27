module

public import CFSG.Quasithin.Background.C22PfB
public import CFSG.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace C22Pf

variable {G : Type} [Group G] [Finite G]

theorem asc22Two_of (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y) :
    ASC22Two G := by
  intro H R L hH hR hL
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  have hRL2 : IsPGroup 2 ↥(R ⊓ L) := hR2.to_le inf_le_left
  have hLN : L ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) :
      Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hx.2, Subgroup.le_normalizer hx.1⟩
  have hRLN : R ⊓ L ≤ L ⊓ Subgroup.normalizer (R : Set G) :=
    le_inf inf_le_right (inf_le_left.trans Subgroup.le_normalizer)
  have h1 : pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) ≤ R := by
    refine le_of_le_cComp_of_sqtk hA37 hH hR hL ((pCoreOf_le 2 _).trans inf_le_left)
      (pCoreOf_isPGroup 2 _) fun g hg => ?_
    refine normalizer_le_normalizer_pCoreOf 2 _ ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, Subgroup.le_normalizer hg.1.2⟩
  have h2 : pCoreOf 2 (L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) ≤ R := by
    refine le_of_le_cComp_of_sqtk hA37 hH hR hL ((pCoreOf_le 2 _).trans inf_le_left)
      (pCoreOf_isPGroup 2 _) fun g hg => ?_
    refine normalizer_le_normalizer_pCoreOf 2 _ ?_
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, ?_⟩
    have hgRL : g ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.1.2, hg.2⟩
    exact Subgroup.le_normalizer hgRL
  have e1 : R ⊓ L = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set G)) := by
    refine le_antisymm (le_pCoreOf_of_le_normalizer 2 hRLN (fun x hx => hLN hx) hRL2) ?_
    exact le_inf h1 ((pCoreOf_le 2 _).trans inf_le_left)
  have e2 : R ⊓ L = pCoreOf 2 (L ⊓ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) := by
    refine le_antisymm (le_pCoreOf_of_le_normalizer 2
      (le_inf inf_le_right Subgroup.le_normalizer) inf_le_right hRL2) ?_
    exact le_inf h2 ((pCoreOf_le 2 _).trans inf_le_left)
  exact ⟨e1, e2, fun hne => ⟨inf_le_right, hne, e2⟩⟩

theorem asc22Three_of (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y) :
    ASC22Three G := by
  intro H R L hH hR hL
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  set NR := R ⊓ Subgroup.normalizer (L : Set G) with hNR
  set X := L ⊔ NR with hX
  set W := pCoreOf 2 (X ⊓ Subgroup.normalizer (NR : Set G)) with hW
  have hNR2 : IsPGroup 2 ↥NR := hR2.to_le inf_le_left
  have hNRL : NR ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hNRW : NR ≤ W :=
    le_pCoreOf_of_le_normalizer 2 (le_inf le_sup_right Subgroup.le_normalizer) inf_le_right hNR2
  have hWL : W ⊓ L ≤ R := by
    refine le_of_le_cComp_of_sqtk hA37 hH hR hL inf_le_right
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left) fun g hg => ?_
    have hgNR : g ∈ Subgroup.normalizer (NR : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.1.2, Subgroup.le_normalizer hg.2⟩
    have hgX : g ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup L NR ⟨hg.2, hgNR⟩
    have hgY : g ∈ Subgroup.normalizer ((X ⊓ Subgroup.normalizer (NR : Set G) : Subgroup G) :
        Set G) := Subgroup.inf_normalizer_le_normalizer_inf ⟨hgX, Subgroup.le_normalizer hgNR⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizer_le_normalizer_pCoreOf 2 _ hgY, hg.2⟩
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hNRL
  have hWNR : W ≤ NR := by
    intro w hw
    have hwX : w ∈ X := (pCoreOf_le 2 _ hw).1
    have hwX' := hwX
    rw [hX, sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right NR L hNRL] at hwX'
    obtain ⟨n, hn, l, hl, hnl⟩ := Set.mem_mul.mp hwX'
    have hlW : l ∈ W := by
      have e : l = n⁻¹ * w := by rw [← hnl]; group
      rw [e]
      exact W.mul_mem (W.inv_mem (hNRW hn)) hw
    have hlR : l ∈ R := hWL ⟨hlW, hl⟩
    refine ⟨?_, hXL hwX⟩
    rw [← hnl]
    exact R.mul_mem (inf_le_left (a := R) hn) hlR
  have e : NR = W := le_antisymm hNRW hWNR
  exact ⟨e, fun hne => ⟨le_sup_right, hne, e⟩⟩

end C22Pf

end CFSG.Quasithin
