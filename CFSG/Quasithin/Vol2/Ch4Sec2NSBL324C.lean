module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

section Aux

variable {G : Type} [Group G] [Finite G]

theorem L_le_normalizer_V_nsb324c {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K) :
    L ≤ Subgroup.normalizer (vV T L : Set G) := by
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  intro g hg
  exact mem_normalizer_commutator (hRN (Subgroup.mem_sup_left hg)) (Subgroup.le_normalizer hg)

theorem pCoreOf_le_normalizer_V_nsb324c {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K) :
    pCoreOf 2 I ≤ Subgroup.normalizer (vV T L : Set G) := by
  intro g hg
  exact Subgroup.centralizer_le_normalizer (vV T L : Set G)
    (c.pCoreOf_le_centralizer_V c.R_le hg)

theorem lemma324One_core_nsb324c {T M L Mm I H K : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k)
    (hFI : ∀ y ∈ I, ∃ l ∈ I ⊓ L, ∃ c ∈ I ⊓ centralizerSection M L (pCoreOf 2 L), y = l * c)
    {N : Subgroup G} (hLN : L ≤ N) (hRN : pCoreOf 2 I ≤ N) :
    NoSumBigData G T M L Mm (I ⊓ N) H K m k ∧ pCoreOf 2 (I ⊓ N) = pCoreOf 2 I := by
  obtain ⟨hy, hIH, c, hm, hmk, hk4, hpsl, hsum⟩ := hd
  have hG : IsGammaStar M L Mm I := by
    have h := hy.gammaStar
    rw [c.conjClosure_eq] at h
    exact h
  have hIota : IsIota M L Mm I := hG.1.1
  have hsup : I ⊔ centralizerSection M L (pCoreOf 2 L) = Mm := hIota.2.1
  have hLIO : L ≤ I ⊔ pCoreOf 2 L := hIota.2.2.1
  have hIO : I ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (c.I_le.trans c.normal).trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hLI : ∀ x ∈ I ⊓ L, x ∈ I ⊓ N := fun x hx => ⟨hx.1, hLN hx.2⟩
  have hR' : pCoreOf 2 I ≤ pCoreOf 2 (I ⊓ N) :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 I) hRN)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 I)) (pCoreOf_isPGroup 2 I)
  have hIMm : I ⊓ N ≤ Mm := inf_le_left.trans hIota.1
  have hIsub : I ≤ (I ⊓ N) ⊔ centralizerSection M L (pCoreOf 2 L) := by
    intro y hy'
    obtain ⟨l, hl, c', hc', rfl⟩ := hFI y hy'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hLI l hl)) (Subgroup.mem_sup_right hc'.2)
  have hI'C : (I ⊓ N) ⊔ centralizerSection M L (pCoreOf 2 L) = Mm :=
    le_antisymm (sup_le hIMm (le_sup_right.trans hsup.le))
      (hsup.ge.trans (sup_le hIsub le_sup_right))
  have hLI' : L ≤ (I ⊓ N) ⊔ pCoreOf 2 L := by
    intro l hl
    obtain ⟨i, hi, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hIO).mp (hLIO hl)
    have hiL : i ∈ L := by
      have := L.mul_mem hl (L.inv_mem (pCoreOf_le 2 L ho))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hLI i ⟨hi, hiL⟩))
      (Subgroup.mem_sup_right ho)
  have hO2ne : pCoreOf 2 (I ⊓ N) ≠ ⊥ := by
    intro h
    exact hIota.2.2.2 (le_bot_iff.mp (hR'.trans h.le))
  have hIota' : IsIota M L Mm (I ⊓ N) := ⟨hIMm, hI'C, hLI', hO2ne⟩
  have hGam' : IsGamma M L Mm (I ⊓ N) :=
    ⟨hIota', H, ⟨inf_le_left.trans c.inH.1, c.inH.2⟩, c.not_le⟩
  have hOrd : OrdLE L I (I ⊓ N) := ⟨hR', fun x hx => ⟨hLI x hx, hx.2⟩⟩
  have hO2 : pCoreOf 2 (I ⊓ N) = pCoreOf 2 I := by
    have hns := hG.2 (I ⊓ N) hGam' hOrd
    by_contra hne
    exact hns (lt_of_le_of_ne hR' (Ne.symm hne))
  have hGS : IsGammaStar M L Mm (I ⊓ N) := by
    refine ⟨hGam', fun I₁ hI₁ hO₁ => ?_⟩
    have hOI : OrdLE L I I₁ :=
      ⟨(le_of_eq hO2.symm).trans hO₁.1, fun x hx => hO₁.2 ⟨hLI x hx, hx.2⟩⟩
    rw [hO2]
    exact hG.2 I₁ hI₁ hOI
  have hR_le : pCoreOf 2 (I ⊓ N) ≤ T ⊓ centralizerSection M L (pCoreOf 2 L) := by
    rw [hO2]
    have h := hy.R_le
    rw [c.conjClosure_eq] at h
    exact h
  have hY : Hyp4_2_3 G T M L Mm (I ⊓ N) :=
    { toHyp4_2_1 := hy.toHyp4_2_1
      sigma := hy.sigma
      conjT := hy.conjT
      conjMm := hy.conjMm
      gammaStar := by rw [c.conjClosure_eq]; exact hGS
      R_le := by rw [c.conjClosure_eq]; exact hR_le }
  have hIH' : InM (I ⊓ N) H := ⟨hIH.1, inf_le_left.trans hIH.2⟩
  have hC : Conf4212 G T M L (I ⊓ N) H K := by
    refine ⟨c.hyp421, inf_le_left.trans c.I_le, ⟨inf_le_left.trans c.inH.1, c.inH.2⟩, c.not_le,
      c.normal, c.conjClosure_eq, c.omega_eq, ?_, c.L_le, c.LH_mem, c.LH_normal, ?_, c.K_mem,
      c.K_quasisimple, c.LH_le, c.K_not_le, c.K_normal, ?_, ?_⟩
    · rw [hO2]; exact c.R_le
    · rw [hO2]; exact c.hypC28
    · rw [hO2]; exact c.described
    · rw [hO2]; exact c.cases
  refine ⟨⟨hY, hIH', hC, hm, hmk, hk4, hpsl, ?_⟩, hO2⟩
  rw [hO2]
  exact hsum

end Aux

theorem lemma324One_of_aux
    (hF : ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
      NoSumBigData G T M L Mm I H K m k →
        ∀ y ∈ I, ∃ l ∈ I ⊓ L, ∃ c ∈ I ⊓ centralizerSection M L (pCoreOf 2 L), y = l * c) :
    Lemma324One := by
  intro G _ _ T M L Mm I H K m k hd
  exact lemma324One_core_nsb324c hd (hF G T M L Mm I H K m k hd)
    (L_le_normalizer_V_nsb324c hd.2.2.1) (pCoreOf_le_normalizer_V_nsb324c hd.2.2.1)

end CFSG.Quasithin.H13.Ch4.NSB
