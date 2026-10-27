module

public import CFSG.Quasithin.H13.L32ARuOne
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

structure Setting147 (G : Type) [Group G] [Finite G] (T L V H : Subgroup G) : Prop where
  hyp : Hyp147 G T L V
  hz : IsHzOne T L (fsuV1 T V) H

namespace Hyp147

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem isTSub_V1 (h : Hyp147 G T L V) (hMod : StmtL32NModule) : IsTSub T V (fsuV1 T V) 1 := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTZ : T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    have hZ : quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
      (Subgroup.closure_le _).mpr fun _ hz => hz.1
    exact (Subgroup.le_centralizer_iff.mp (hZ.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  refine ⟨inf_le_left, by rw [hV1]; norm_num, fun t ht => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) x).mp hxV,
      (Subgroup.mem_normalizer_iff.mp (hTZ ht) x).mp hxZ⟩
  · rintro ⟨hxV, hxZ⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hTV ht) x).mpr hxV,
      (Subgroup.mem_normalizer_iff.mp (hTZ ht) x).mpr hxZ⟩

omit [Finite G] in
theorem fsuU_eq_u128 (T V : Subgroup G) : fsuU T V = u128 V (fsuV1 T V) := rfl

theorem isHzOne_hz (h : Hyp147 G T L V) (h63 : Thm14_7_63) :
    IsHzOne T L (fsuV1 T V) (L32A.hz T V) := by
  obtain ⟨⟨hInH, hM, hG1⟩, -⟩ := h63 G T L V h
  exact ⟨hInH, hG1, hM⟩

end Hyp147

namespace Setting147

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem hypF98
    (S : Setting147 G T L V H) (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (h1222 : Stmt12_2_2) : HypF98 T V L (fsuV1 T V) V H :=
  L1286.hypF98_of_abelian h1222 (a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat (Vol2Native.a38ForSQTKCat_of_facts mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved))
    (a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved) (S.hyp.hyp1281One h13322 hMod)
    (S.hyp.isTSub_V1 hMod) S.hyp.abelian S.hz

theorem exists_F8Setup
    (S : Setting147 G T L V H) (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (h1222 : Stmt12_2_2) :
    ∃ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g :=
  (S.hypF98 h13322 hMod h1222).exists_F8Setup

end Setting147

end CFSG.Quasithin.H13
