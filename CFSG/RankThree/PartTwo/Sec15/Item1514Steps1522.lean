module

public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs
import CFSG.RankThree.PartTwo.Sec14.Item146General
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1522Hyp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
      ∀ (hYA : A ≤ Subgroup.normalizer (Y : Set G)), ∃ n : ℕ, 4 ≤ n ∧
        (letI := kerAO2_normal hYA
          ∃ T : Type, ∃ _ : Group T, Sec4.IsoLThreePi T 2 n ∧
            Nonempty (↥(A ⊔ Y) ⧸ kerAO2 A Y ≃* Multiplicative (ZMod 3) × T))

@[expose] noncomputable def Step1522Conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ (p : ℕ) (P : Subgroup G), Data1519 A (lB A) L p P →
        ∀ a ∈ A, a ∉ Subgroup.zpowers c → ∃ w ∈ Subgroup.normalizer (A : Set G),
          P.map (MulAut.conj w).toMonoidHom ≤ Subgroup.centralizer ({a} : Set G)

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_22_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1424 : Item14_24 A (lB A) c L) (h153 : Item153Main A (lB A))
    (h1517 : Step1517 A (lB A) c L) (hhyp : Step1522Hyp) (hconj : Step1522Conj) :
    Step1522 A (lB A) c L := by
  intro Y hctx p P hP
  have hY0 : Y ∈ scriptY0 A (lB A) := hctx.mem_y0Star.prop
  have hY3 : Y ∈ scriptY3 A (lB A) := ⟨hY0.2, hY0.1.2.2.1⟩
  have hYA : A ≤ Subgroup.normalizer (Y : Set G) := hY0.1.1.2
  obtain ⟨n, hn4, hiso⟩ := hhyp G A c L h Y hctx p P hP hYA
  obtain ⟨-, -, -, -, -, -, hYL, -, hΩ⟩ := hctx.concl1515
  have hF := (h153 Y hctx.mem_y0Star).2.2
  have hLs := (h1517 Y hctx).2.1
  obtain ⟨a, haA, hac, hne⟩ :=
    h1424 Y hY3 hYA n hn4 hiso (by rwa [inf_comm]) hF hLs hΩ
  obtain ⟨w, hw, hPw⟩ := hconj G A c L h Y hctx p P hP a haA hac
  set D := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hD
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ one_mem _)
  have hDY : D ∈ scriptY A := by
    refine ⟨fun htop => ?_, le_normalizer_delta _⟩
    apply centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian ha1
    exact eq_top_iff.mpr (htop ▸ delta_le _)
  have hDO : CFSG.Open.pCoreOf 2 D ≠ ⊥ := fun h0 => hne (by rw [h0, inf_bot_eq])
  have hPwQ : P.map (MulAut.conj w).toMonoidHom ∈ scriptQ A (lB A) :=
    (Sec17.HeadProof.map_conj_mem_scriptQPi hw hP.2.2.2.2.2.1).1.1
  have hPwD : P.map (MulAut.conj w).toMonoidHom ≤ D := le_delta hPwQ hPw
  refine ⟨D.map (MulAut.conj w⁻¹).toMonoidHom,
    ⟨Sec17.HeadProof.map_conj_mem_scriptY (inv_mem hw) hDY, ?_⟩, ?_⟩
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact fun h0 => hDO ((Subgroup.map_eq_bot_iff_of_injective _
      (MulAut.conj w⁻¹).injective).mp h0)
  · intro x hx
    refine ⟨w * x * w⁻¹, hPwD ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end CFSG.RankThree.PartTwo.Sec15
