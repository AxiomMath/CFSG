module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3Flag

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

structure IsFlag (p L H : Submodule K (Fin 4 → K)) : Prop where
  p1 : finrank K p = 1
  L2 : finrank K L = 2
  H3 : finrank K H = 3
  pL : p ≤ L
  LH : L ≤ H

@[expose] def admSet (Adm : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) →
    Submodule K (Fin 4 → K) → Prop) : Set (FlagK K 4) :=
  {x | Adm (x.E 1) (x.E 2) (x.E 3)}

variable (Adm : Submodule K (Fin 4 → K) → Submodule K (Fin 4 → K) →
    Submodule K (Fin 4 → K) → Prop)

@[expose] def AdmCh (p L H : Submodule K (Fin 4 → K)) : Prop := IsFlag p L H ∧ Adm p L H

@[expose] def AdmAdj (p r : Submodule K (Fin 4 → K)) : Prop :=
  p ≠ r ∧ ∃ L H, AdmCh Adm p L H ∧ AdmCh Adm r L H

@[expose] def AdmPlanar (x y z : Submodule K (Fin 4 → K)) : Prop :=
  ∃ H L₁ L₂ L₃, AdmCh Adm x L₁ H ∧ AdmCh Adm y L₁ H ∧ AdmCh Adm y L₂ H ∧ AdmCh Adm z L₂ H ∧
    AdmCh Adm z L₃ H ∧ AdmCh Adm x L₃ H

@[expose] def AdmFibreConn : Prop :=
  ∀ p L H L' H', AdmCh Adm p L H → AdmCh Adm p L' H' →
    Relation.ReflTransGen (fun a b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) =>
      AdmCh Adm p a.1 a.2 ∧ AdmCh Adm p b.1 b.2 ∧ (a.2 = b.2 ∨ a.1 = b.1)) (L, H) (L', H')

@[expose] def AdmCommonNbr : Prop :=
  ∀ s : Finset (Submodule K (Fin 4 → K)), s.Nonempty → s.card ≤ 4 →
    (∀ p ∈ s, ∃ L H, AdmCh Adm p L H) → ∃ t, ∀ p ∈ s, AdmAdj Adm p t

@[expose] def AdmCommonNbrW : Prop :=
  (∀ u v : Submodule K (Fin 4 → K), (∃ L H, AdmCh Adm u L H) → (∃ L H, AdmCh Adm v L H) →
    ∃ t, AdmAdj Adm u t ∧ AdmAdj Adm v t) ∧
  (∀ a b c d : Submodule K (Fin 4 → K), AdmAdj Adm a b → AdmAdj Adm b c → AdmAdj Adm c d →
    AdmAdj Adm d a → ∃ t, AdmAdj Adm a t ∧ AdmAdj Adm b t ∧ AdmAdj Adm c t ∧ AdmAdj Adm d t) ∧
  (∀ u c d : Submodule K (Fin 4 → K), (∃ L H, AdmCh Adm u L H) → AdmAdj Adm c d →
    ∃ t, AdmAdj Adm u t ∧ AdmAdj Adm c t ∧ AdmAdj Adm d t)

@[expose] def AdmConeTri : Prop :=
  ∀ x y z, AdmAdj Adm x y → AdmAdj Adm y z → AdmAdj Adm z x →
    ∃ t, AdmAdj Adm x t ∧ AdmAdj Adm y t ∧ AdmAdj Adm z t ∧ AdmPlanar Adm x y t ∧
      AdmPlanar Adm y z t ∧ AdmPlanar Adm z x t

@[expose] def AdmCommonNbrD : Prop :=
  (∀ u v : Submodule K (Fin 4 → K), (∃ L H, AdmCh Adm u L H) → (∃ L H, AdmCh Adm v L H) →
    ∃ t, AdmAdj Adm u t ∧ AdmAdj Adm v t) ∧
  (∀ a b c d : Submodule K (Fin 4 → K), AdmAdj Adm a b → AdmAdj Adm b c → AdmAdj Adm c d →
    AdmAdj Adm d a → a ≠ c → ¬ AdmAdj Adm a c → b ≠ d → ¬ AdmAdj Adm b d →
    ∃ t, AdmAdj Adm a t ∧ AdmAdj Adm b t ∧ AdmAdj Adm c t ∧ AdmAdj Adm d t) ∧
  (∀ u c d : Submodule K (Fin 4 → K), (∃ L H, AdmCh Adm u L H) → AdmAdj Adm c d →
    ∃ t, AdmAdj Adm u t ∧ AdmAdj Adm c t ∧ AdmAdj Adm d t)

@[expose] def AdmConeTriD : Prop :=
  ∀ x y z, AdmAdj Adm x y → AdmAdj Adm y z → AdmAdj Adm z x → AdmPlanar Adm x y z ∨
    ∃ t, AdmAdj Adm x t ∧ AdmAdj Adm y t ∧ AdmAdj Adm z t ∧ AdmPlanar Adm x y t ∧
      AdmPlanar Adm y z t ∧ AdmPlanar Adm z x t

theorem hasCh_admSet_iff (p L H : Submodule K (Fin 4 → K)) :
    HasCh (admSet Adm) p L H ↔ AdmCh Adm p L H := by
  constructor
  · rintro ⟨x, hx, h1, h2, h3⟩
    have hx' : Adm (x.E 1) (x.E 2) (x.E 3) := by simpa only [admSet, Set.mem_setOf_eq] using hx
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [← h1]; exact FlagK.finrank_E_one x
    · rw [← h2]; exact FlagK.finrank_E_two x
    · rw [← h3]; exact FlagK.finrank_E_three x
    · rw [← h1, ← h2]; exact FlagK.E_one_le_two x
    · rw [← h2, ← h3]; exact FlagK.E_two_le_three x
    · exact h1 ▸ h2 ▸ h3 ▸ hx'
  · rintro ⟨⟨hp, hL, hH, hpL, hLH⟩, hAdm⟩
    refine ⟨FlagK.ofChain4 p L H hp hL hH hpL hLH, ?_,
      FlagK.ofChain4_E_one p L H hp hL hH hpL hLH,
      FlagK.ofChain4_E_two p L H hp hL hH hpL hLH,
      FlagK.ofChain4_E_three p L H hp hL hH hpL hLH⟩
    simp only [admSet, Set.mem_setOf_eq, FlagK.ofChain4_E_one, FlagK.ofChain4_E_two,
      FlagK.ofChain4_E_three]
    exact hAdm

private noncomputable def plh_flagOfAdm (p : Submodule K (Fin 4 → K))
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) (ha : AdmCh Adm p a.1 a.2) :
    FlagK K 4 :=
  FlagK.ofChain4 p a.1 a.2 ha.1.p1 ha.1.L2 ha.1.H3 ha.1.pL ha.1.LH

private lemma plh_flagOfAdm_E_one (p : Submodule K (Fin 4 → K))
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) (ha : AdmCh Adm p a.1 a.2) :
    (plh_flagOfAdm Adm p a ha).E 1 = p := by
  simp only [plh_flagOfAdm, FlagK.ofChain4_E_one]

private lemma plh_flagOfAdm_E_two (p : Submodule K (Fin 4 → K))
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) (ha : AdmCh Adm p a.1 a.2) :
    (plh_flagOfAdm Adm p a ha).E 2 = a.1 := by
  simp only [plh_flagOfAdm, FlagK.ofChain4_E_two]

private lemma plh_flagOfAdm_E_three (p : Submodule K (Fin 4 → K))
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) (ha : AdmCh Adm p a.1 a.2) :
    (plh_flagOfAdm Adm p a ha).E 3 = a.2 := by
  simp only [plh_flagOfAdm, FlagK.ofChain4_E_three]

private lemma plh_flagOfAdm_mem (p : Submodule K (Fin 4 → K))
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) (ha : AdmCh Adm p a.1 a.2) :
    plh_flagOfAdm Adm p a ha ∈ admSet Adm := by
  simp only [admSet, Set.mem_setOf_eq, plh_flagOfAdm, FlagK.ofChain4_E_one,
    FlagK.ofChain4_E_two, FlagK.ofChain4_E_three]
  exact ha.2

private lemma plh_flagOfAdm_congr (p : Submodule K (Fin 4 → K))
    (a : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)) (ha ha' : AdmCh Adm p a.1 a.2) :
    plh_flagOfAdm Adm p a ha = plh_flagOfAdm Adm p a ha' := by
  rw [Subsingleton.elim ha ha']

private lemma plh_ptAdj_admSet_iff (p r : Submodule K (Fin 4 → K)) :
    PtAdj (admSet Adm) p r ↔ AdmAdj Adm p r := by
  simp only [PtAdj, AdmAdj, hasCh_admSet_iff Adm]

private lemma plh_planarPts_admSet_iff (x y z : Submodule K (Fin 4 → K)) :
    PlanarPts (admSet Adm) x y z ↔ AdmPlanar Adm x y z := by
  simp only [PlanarPts, AdmPlanar, hasCh_admSet_iff Adm]

private lemma plh_fibreConn_admSet (h : AdmFibreConn Adm) : FibreConn (admSet Adm) := by
  intro x hx y hy hxy
  have hxch : AdmCh Adm (x.E 1) (x.E 2) (x.E 3) :=
    (hasCh_admSet_iff Adm (x.E 1) (x.E 2) (x.E 3)).mp ⟨x, hx, rfl, rfl, rfl⟩
  have hych : AdmCh Adm (x.E 1) (y.E 2) (y.E 3) := by
    have := (hasCh_admSet_iff Adm (y.E 1) (y.E 2) (y.E 3)).mp ⟨y, hy, rfl, rfl, rfl⟩
    rwa [← hxy] at this
  have hconn := h (x.E 1) (x.E 2) (x.E 3) (y.E 2) (y.E 3) hxch hych
  have aux : ∀ {b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K)},
      Relation.ReflTransGen
        (fun a b : Submodule K (Fin 4 → K) × Submodule K (Fin 4 → K) =>
          AdmCh Adm (x.E 1) a.1 a.2 ∧ AdmCh Adm (x.E 1) b.1 b.2 ∧
            (a.2 = b.2 ∨ a.1 = b.1))
        (x.E 2, x.E 3) b →
      ∀ hb : AdmCh Adm (x.E 1) b.1 b.2,
        Relation.ReflTransGen
          (fun u v : FlagK K 4 =>
            u ∈ admSet Adm ∧ v ∈ admSet Adm ∧ u.E 1 = v.E 1 ∧
              (u.E 3 = v.E 3 ∨ u.E 2 = v.E 2))
          (plh_flagOfAdm Adm (x.E 1) (x.E 2, x.E 3) hxch) (plh_flagOfAdm Adm (x.E 1) b hb) := by
    intro b hab
    induction hab with
    | refl =>
        intro hb
        rw [plh_flagOfAdm_congr Adm (x.E 1) (x.E 2, x.E 3) hxch hb]
    | tail hab hbc ih =>
        rename_i b c
        intro hc
        refine (ih hbc.1).tail ?_
        refine ⟨plh_flagOfAdm_mem Adm (x.E 1) b hbc.1, plh_flagOfAdm_mem Adm (x.E 1) c hc,
          ?_, ?_⟩
        · rw [plh_flagOfAdm_E_one, plh_flagOfAdm_E_one]
        · rcases hbc.2.2 with hp | hl
          · left; rw [plh_flagOfAdm_E_three, plh_flagOfAdm_E_three, hp]
          · right; rw [plh_flagOfAdm_E_two, plh_flagOfAdm_E_two, hl]
  have hres := aux hconn hych
  have hxflag : plh_flagOfAdm Adm (x.E 1) (x.E 2, x.E 3) hxch = x := by
    apply FlagK.ext4
    · rw [plh_flagOfAdm_E_one]
    · rw [plh_flagOfAdm_E_two]
    · rw [plh_flagOfAdm_E_three]
  have hyflag : plh_flagOfAdm Adm (x.E 1) (y.E 2, y.E 3) hych = y := by
    apply FlagK.ext4
    · rw [plh_flagOfAdm_E_one, hxy]
    · rw [plh_flagOfAdm_E_two]
    · rw [plh_flagOfAdm_E_three]
  rw [hxflag, hyflag] at hres
  exact hres

private lemma plh_commonNbr_admSet (h : AdmCommonNbr Adm) : CommonNbr (admSet Adm) := by
  intro s hsne hscard hpt
  obtain ⟨t, ht⟩ := h s hsne hscard (fun p hp => by
    obtain ⟨x, hx, hxp⟩ := hpt p hp
    exact ⟨x.E 2, x.E 3,
      (hasCh_admSet_iff Adm p (x.E 2) (x.E 3)).mp ⟨x, hx, hxp, rfl, rfl⟩⟩)
  exact ⟨t, fun p hp => (plh_ptAdj_admSet_iff Adm p t).mpr (ht p hp)⟩

private lemma plh_coneTri_admSet (h : AdmConeTri Adm) : ConeTri (admSet Adm) := by
  intro x y z hxy hyz hzx
  obtain ⟨t, hxt, hyt, hzt, hp1, hp2, hp3⟩ :=
    h x y z ((plh_ptAdj_admSet_iff Adm x y).mp hxy) ((plh_ptAdj_admSet_iff Adm y z).mp hyz)
      ((plh_ptAdj_admSet_iff Adm z x).mp hzx)
  exact ⟨t, (plh_ptAdj_admSet_iff Adm x t).mpr hxt, (plh_ptAdj_admSet_iff Adm y t).mpr hyt,
    (plh_ptAdj_admSet_iff Adm z t).mpr hzt, (plh_planarPts_admSet_iff Adm x y t).mpr hp1,
    (plh_planarPts_admSet_iff Adm y z t).mpr hp2,
    (plh_planarPts_admSet_iff Adm z x t).mpr hp3⟩

private lemma plh_commonNbrD_admSet (h : AdmCommonNbrD Adm) : CommonNbrD (admSet Adm) := by
  have hflag : ∀ {p : Submodule K (Fin 4 → K)}, (∃ x ∈ admSet Adm, x.E 1 = p) →
      ∃ L H, AdmCh Adm p L H := by
    intro p ⟨x, hx, hxp⟩
    exact ⟨x.E 2, x.E 3, (hasCh_admSet_iff Adm p (x.E 2) (x.E 3)).mp ⟨x, hx, hxp, rfl, rfl⟩⟩
  have hpt : ∀ {p r : Submodule K (Fin 4 → K)}, PtAdj (admSet Adm) p r ↔ AdmAdj Adm p r :=
    fun {p r} => plh_ptAdj_admSet_iff Adm p r
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    obtain ⟨t, htu, htv⟩ := h.1 u v (hflag hu) (hflag hv)
    exact ⟨t, hpt.mpr htu, hpt.mpr htv⟩
  · intro a b c d hab hbc hcd hda hac hnac hbd hnbd
    obtain ⟨t, ha, hb, hc, hd⟩ := h.2.1 a b c d (hpt.mp hab) (hpt.mp hbc) (hpt.mp hcd)
      (hpt.mp hda) hac (fun h => hnac (hpt.mpr h)) hbd (fun h => hnbd (hpt.mpr h))
    exact ⟨t, hpt.mpr ha, hpt.mpr hb, hpt.mpr hc, hpt.mpr hd⟩
  · intro u c d hu hcd
    obtain ⟨t, hu', hc, hd⟩ := h.2.2 u c d (hflag hu) (hpt.mp hcd)
    exact ⟨t, hpt.mpr hu', hpt.mpr hc, hpt.mpr hd⟩

private lemma plh_coneTriD_admSet (h : AdmConeTriD Adm) : ConeTriD (admSet Adm) := by
  intro x y z hxy hyz hzx
  rcases h x y z ((plh_ptAdj_admSet_iff Adm x y).mp hxy) ((plh_ptAdj_admSet_iff Adm y z).mp hyz)
      ((plh_ptAdj_admSet_iff Adm z x).mp hzx) with hpl | ⟨t, hxt, hyt, hzt, hp1, hp2, hp3⟩
  · exact Or.inl ((plh_planarPts_admSet_iff Adm x y z).mpr hpl)
  · exact Or.inr ⟨t, (plh_ptAdj_admSet_iff Adm x t).mpr hxt, (plh_ptAdj_admSet_iff Adm y t).mpr hyt,
      (plh_ptAdj_admSet_iff Adm z t).mpr hzt, (plh_planarPts_admSet_iff Adm x y t).mpr hp1,
      (plh_planarPts_admSet_iff Adm y z t).mpr hp2,
      (plh_planarPts_admSet_iff Adm z x t).mpr hp3⟩

theorem admSet_simplyTwoConnected (h1 : AdmFibreConn Adm) (h2 : AdmCommonNbr Adm)
    (h3 : AdmConeTri Adm) :
    ((flagSys K 3).restrict (admSet Adm)).Connected ∧
      ((flagSys K 3).restrict (admSet Adm)).SimplyTwoConnected := by
  exact flagSystem_simplyTwoConnected_of_criterion (admSet Adm)
    (plh_fibreConn_admSet Adm h1) (plh_commonNbr_admSet Adm h2) (plh_coneTri_admSet Adm h3)

theorem admSet_simplyTwoConnected_diag (h1 : AdmFibreConn Adm) (h2 : AdmCommonNbrD Adm)
    (h3 : AdmConeTriD Adm) :
    ((flagSys K 3).restrict (admSet Adm)).Connected ∧
      ((flagSys K 3).restrict (admSet Adm)).SimplyTwoConnected :=
  flagSystem_simplyTwoConnected_of_criterion_diag (admSet Adm)
    (plh_fibreConn_admSet Adm h1) (plh_commonNbrD_admSet Adm h2) (plh_coneTriD_admSet Adm h3)

theorem admCommonNbrD_of_admCommonNbrW (h : AdmCommonNbrW Adm) : AdmCommonNbrD Adm :=
  ⟨h.1, fun a b c d hab hbc hcd hda _ _ _ _ => h.2.1 a b c d hab hbc hcd hda, h.2.2⟩

theorem admConeTriD_of_admConeTri (h : AdmConeTri Adm) : AdmConeTriD Adm :=
  fun x y z hxy hyz hzx => Or.inr (h x y z hxy hyz hzx)

theorem admSet_simplyTwoConnected_weak (h1 : AdmFibreConn Adm) (h2 : AdmCommonNbrW Adm)
    (h3 : AdmConeTri Adm) :
    ((flagSys K 3).restrict (admSet Adm)).Connected ∧
      ((flagSys K 3).restrict (admSet Adm)).SimplyTwoConnected :=
  admSet_simplyTwoConnected_diag Adm h1 (admCommonNbrD_of_admCommonNbrW Adm h2)
    (admConeTriD_of_admConeTri Adm h3)

end CFSG.ClassicalInvolution.Phan.PhanE

end
