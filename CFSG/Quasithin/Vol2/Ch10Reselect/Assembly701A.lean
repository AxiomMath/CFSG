module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.Quasithin.EmptyFaithful.S153H30

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Vol2.Ch10
open scoped IsMulCommutative

structure Hyp7_0_2A (G : Type) [Group G] [Finite G] (T L I : Subgroup G) : Prop where
  fsu : FSU G T L I
  notFF : ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Concl701FF T L I
  notThree : ¬ (L < fsuL0 T L ∧ Concl326ThreeCA T L I)
  notOrth : ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Concl701Orth T L I

theorem Hyp7_0_2.toA {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (h : Hyp7_0_2 G T L I) : Hyp7_0_2A G T L I :=
  ⟨h.fsu, h.notFF, fun hc => h.notThree ⟨hc.1, concl326ThreeC_of_A hc.2⟩, h.notOrth⟩

@[expose] def Stmt9_omegaPlusA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2A G T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ∀ n : ℕ, ¬ Row711OmegaPlus T L I n

@[expose] def Stmt8_3_1A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2A G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), ¬ Row711L3Wreath T L I

theorem stmt9_omegaPlus_of_A (h : Stmt9_omegaPlusA) : Stmt9_omegaPlus :=
  fun G _ _ T L I hyp hc n => h G T L I hyp.toA hc n

theorem stmt8_3_1_of_A (h : Stmt8_3_1A) : Stmt8_3_1 :=
  fun G _ _ T L I hyp h731 hc => h G T L I hyp.toA h731 hc

theorem stmt7_0_1A_of (h701 : Stmt7_0_1) (h326 : Stmt3_2_6LtA) (h9 : Stmt9_omegaPlusA)
    (h831 : Stmt8_3_1A) : Stmt7_0_1A := by
  intro G _ _ T L I hfsu
  obtain ⟨hc, hab, hn, hcases⟩ := h701 G T L I hfsu
  refine ⟨hc, hab, hn, ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  rcases hcases with h | h | h | ⟨hlt, hsh, hC⟩
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · have hyp : Hyp7_0_2A G T L I :=
      { fsu := hfsu
        notFF := fun _ => h1
        notThree := fun h => h4 ⟨h.1, hsh, h.2⟩
        notOrth := fun _ => h3 }
    rcases h326 G T L I hfsu hlt with ⟨_, _, _, hrow⟩ | hCA
    · rcases hrow with ⟨n, hn⟩ | hw
      · exact h9 G T L I hyp hc n hn
      · exact h831 G T L I hyp (fun _ n hn => h9 G T L I hyp hc n hn) hc hw
    · exact h4 ⟨hlt, hsh, hCA⟩

theorem false_of_lieModel_psl_three_two_psl_two {X : Type} [Group X] {n : ℕ}
    (h3 : LieModel X .PSL 3 2 1) (h2 : LieModel X .PSL 2 2 n) : False :=
  (CFSG.Quasithin.S153H.not_iso_small
    (CFSG.Quasithin.H13.Ch4.T4213.isPSL_of_lieModel (by norm_num) h2)).1
    (CFSG.Quasithin.H13.Ch4.T4213.isPSL_of_lieModel (by norm_num) h3)

theorem stmt7_0_1A_of_C (h701 : Stmt7_0_1) (h326 : Stmt3_2_6C) (h9 : Stmt9_omegaPlusA) :
    Stmt7_0_1A := by
  intro G _ _ T L I hfsu
  obtain ⟨hc, hab, hn, hcases⟩ := h701 G T L I hfsu
  refine ⟨hc, hab, hn, ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  rcases hcases with h | h | h | ⟨hlt, hsh, hC⟩
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · have hyp : Hyp7_0_2A G T L I :=
      { fsu := hfsu
        notFF := fun _ => h1
        notThree := fun h => h4 ⟨h.1, hsh, h.2⟩
        notOrth := fun _ => h3 }
    obtain ⟨⟨hcV, _⟩, hcVM, _, hcases'⟩ := h326 G T L I hfsu hlt.ne
    rcases hcases' with ⟨n, K, _, _, hcard, hlie, hV0, hVVM, hreal⟩ | ⟨hlie3, hV0, hVVM, hreal⟩ |
      ⟨⟨ha, _, _⟩, _⟩
    ·
      refine h9 G T L I hyp hcV n ⟨hlt, two_le_of_lieModel_psl_two hlie, K, inferInstance,
        inferInstance, hcard, ?_⟩
      rw [← tensorNatModel_eq]
      exact realizesMod_of_eq hVVM _ _ hreal
    ·
      rcases hC with ⟨x, hx, h3x⟩ | ⟨_, n, K, _, _, _, hlie, _⟩
      · exact h4 ⟨hlt, hsh, Or.inl ⟨x, hx, h3x⟩⟩
      · exact false_of_lieModel_psl_three_two_psl_two hlie3 hlie
    ·
      exact h4 ⟨hlt, hsh, hC.imp_right fun ⟨hc', hiv⟩ => ⟨hc', ha, hiv⟩⟩

end CFSG.Quasithin.H13
