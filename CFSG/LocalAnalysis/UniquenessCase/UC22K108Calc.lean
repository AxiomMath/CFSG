module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108Rows
import CFSG.Milestones.ASVolI.A3L3.StepsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)

variable {Gh : Type} [Group Gh]

theorem k108Star_normalizer_le {X M : Subgroup Gh} (hstar : ∀ g : Gh, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M)
    {A : Subgroup Gh} (hXA : X ≤ A) (hAM : A ≤ M) : normalizer (A : Set Gh) ≤ M := by
  intro g hg
  refine hstar g fun x hx => hAM ?_
  simpa using (mem_normalizer_iff.1 (inv_mem hg) x).1 (hXA hx)

variable [Finite Gh]

theorem k108_le_normalizer_of_inf {S T Y : Subgroup Gh} (hSn : S.Normal) (hT : IsSylowOf 2 T ⊤) (hTS : T ≤ S)
    (hTY : T ≤ Y) (h : Y ⊓ S ≤ normalizer (T : Set Gh)) : Y ≤ normalizer (T : Set Gh) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy
  set P := T.map (MulAut.conj y).toMonoidHom
  have hPYS : P ≤ Y ⊓ S := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨Y.mul_mem (Y.mul_mem hy (hTY ht)) (Y.inv_mem hy), hSn.conj_mem t (hTS ht) y⟩
  have hPT : P ⊔ T = T :=
    hT.eq_of_le le_sup_right le_top ((hT.isPGroup.map _).to_sup_of_normal_right' hT.isPGroup (hPYS.trans h))
  have hP : P = T := eq_of_le_of_card_ge (hPT ▸ le_sup_left)
    (card_map_of_injective (MulAut.conj y).injective).ge
  rw [mem_normalizer_iff]
  intro t
  refine ⟨fun ht => hP ▸ ⟨t, ht, rfl⟩, fun ht => ?_⟩
  rw [← hP] at ht
  obtain ⟨s, hs, hst⟩ := ht
  have : s = t := by simpa using hst
  exact this ▸ hs

theorem k108_inf_le_normalizer_of_bt {F : (S : Type) → [Group S] → Prop} (hBT : K108BT F) {S T H : Subgroup Gh}
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hF : F ↥S) (hT : IsSylowOf 2 T ⊤) (hTS : T ≤ S)
    (hTH : T ≤ H) (hH : Group.IsSolvable ↥H) : H ⊓ S ≤ normalizer (T : Set Gh) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowOf 2 (T.subgroupOf S) ⊤ := by
    refine (isSylowOf_map_subtype_iff S).1 ?_
    rw [subgroupOf_map_subtype, inf_eq_left.2 hTS, ← MonoidHom.range_eq_map, range_subtype]
    exact hT.of_le hTS le_top
  let f : ↥(H.subgroupOf S) →* ↥H :=
    { toFun := fun x => ⟨((x : ↥S) : Gh), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥H => (z : Gh)) hxy))
  haveI := hH
  have h := hBT ↥S hS hnab hF (T.subgroupOf S) hT' (H.subgroupOf S) (fun x hx => hTH hx)
    (Group.isSolvable_of_isSolvable_injective hf)
  rw [← subgroupOf_normalizer_eq hTS] at h
  exact fun x hx => h (show (⟨x, hx.2⟩ : ↥S) ∈ H.subgroupOf S from hx.1)

theorem k108RowH_of_rowX {F : (S : Type) → [Group S] → Prop}
    (hinv : ∀ {A A' : Type} [Group A] [Group A'], A ≃* A' → F A → F A') (hR : K108RowX F) (hBT : K108BT F) :
    K108RowH F := by
  intro Gh _ _ S hSn hS hnab hC hF T B hB hSB X M hXB hX hXodd hTM hXM hstar
  obtain ⟨hT, hBab, hBodd, hperm, -⟩ := hB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hSn
  have hTS : T ≤ S :=
    CFSG.Semidihedral.Principal.le_of_le_sup_of_odd S B T (hSB ▸ le_top) hT.isPGroup hBodd
  have hBN : B ≤ normalizer (T : Set Gh) :=
    le_sup_left.trans (k108_le_normalizer_of_inf hSn hT hTS le_sup_right
      (k108_inf_le_normalizer_of_bt hBT hS hnab hF hT hTS le_sup_right
        (CFSG.ASVolI.burnsideA315y_sup_solvable hBab hBodd hT.isPGroup hperm)))
  set Y := S ⊔ X with hY
  have hSY : S ≤ Y := le_sup_left
  have hXY : X ≤ Y := le_sup_right
  have hTY : T ≤ Y := hTS.trans hSY
  let eS : ↥(S.subgroupOf Y) ≃* ↥S := subgroupOfEquivOfLe hSY
  have hcX : Nat.card ↥(X.subgroupOf Y) = Nat.card X := Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv
  have hnab' : ∃ a b : ↥(S.subgroupOf Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by simpa using congrArg eS h)⟩
  have hC' : centralizer ((S.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : (y : Gh) ∈ centralizer (S : Set Gh) := mem_centralizer_iff.2 fun s hs =>
      congrArg Subtype.val (mem_centralizer_iff.1 hy ⟨s, hSY hs⟩ hs)
    rw [hC] at hy'
    exact mem_bot.2 (Subtype.ext (mem_bot.1 hy'))
  have hT' : IsSylowOf 2 (T.subgroupOf Y) ⊤ := by
    refine (isSylowOf_map_subtype_iff Y).1 ?_
    rw [subgroupOf_map_subtype, inf_eq_left.2 hTY, ← MonoidHom.range_eq_map, range_subtype]
    exact hT.of_le hTY le_top
  have htop : S.subgroupOf Y ⊔ X.subgroupOf Y = ⊤ := by
    rw [← subgroupOf_sup hSY hXY]
    exact subgroupOf_self _
  have hN' : X.subgroupOf Y ≤ normalizer ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [← subgroupOf_normalizer_eq hTY]
    exact fun x hx => hBN (hXB hx)
  have hstar' : ∀ g : ↥Y, (∀ x ∈ X.subgroupOf Y, g⁻¹ * x * g ∈ M.subgroupOf Y) → g ∈ M.subgroupOf Y :=
    fun g hg => hstar g fun x hx => hg ⟨x, hXY hx⟩ hx
  have key := hR ↥Y (S.subgroupOf Y) inferInstance (eS.isSimpleGroup_congr.2 hS) hnab' hC' (hinv eS.symm hF)
    (T.subgroupOf Y) (X.subgroupOf Y) hT' (by rw [hcX]; exact hX) (by rw [hcX]; exact hXodd) htop hN'
    (M.subgroupOf Y) (fun x hx => hTM hx) (fun x hx => hXM hx) hstar'
  exact fun s hs => key (show (⟨s, hSY hs⟩ : ↥Y) ∈ S.subgroupOf Y from hs)

theorem k108H207_of_rows (h : K108Rows) : K108H207 := by
  intro Gh _ _ S hSn hS hnab hC hL T B hB hSB X M hXB hX hXodd hTM hXM hstar
  have key : ∀ {F : (S : Type) → [Group S] → Prop}, K108RowH F → F ↥S → S ≤ M :=
    fun hR hF => hR Gh S hSn hS hnab hC hF T B hB hSB X M hXB hX hXodd hTM hXM hstar
  have t : ∀ {A A' : Type} [Group A] [Group A'] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ},
      A ≃* A' → LieModel A t m 2 f → LieModel A' t m 2 f := fun e h => LieModel.of_mulEquiv e h
  rcases hL with hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF | hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.l2 h.bt_l2) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.sz h.bt_sz) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.u3 h.bt_u3) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.l3 h.bt_l3) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.sp4 h.bt_sp4) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.g2 h.bt_g2) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.d4 h.bt_d4) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.f4 h.bt_f4) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.u4 h.bt_u4) hF
  · exact key (k108RowH_of_rowX (fun e h => t e h) h.u5 h.bt_u5) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.l4 h.bt_l4) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.sp6 h.bt_sp6) hF
  · exact key (k108RowH_of_rowX (fun e ⟨n, hn, h⟩ => ⟨n, hn, t e h⟩) h.o8m h.bt_o8m) hF
  · exact key h.d4two hF

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
