module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829Coc

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

@[expose] def L3M22Nonsolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          Group.IsSolvable ↥H

@[expose] def L3M22Solv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          Group.IsSolvable ↥H → oTwoUpper H ≤ ch82I (fsuV T I) h ⊔ kerIn (H ⊓ fsuM T L) H

theorem step829L3M22_of (hmod : StmtFSUModule) (hP7 : Stmt8_2_2P7) (hns : L3M22Nonsolv)
    (hsolv : L3M22Solv) : Step829L3M22 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  obtain ⟨-, hhI, -⟩ := id hC
  have hsl := hns G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  have hY := hsolv G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' hsl
  exact T_normalizes_pCore_ch82I_829 hT hVT hTV hh hhI
    (hP7 G T L I hyp h731 h821 hc hrow H h k hH hh hC) hY

end CFSG.Quasithin.H13
