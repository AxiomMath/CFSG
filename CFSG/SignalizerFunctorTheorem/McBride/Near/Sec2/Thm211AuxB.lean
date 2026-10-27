module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211AuxC

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

variable {Γ : Type u} [Group Γ]

theorem mOf_eq_self_of_cenIn_eq_bot {A K : Subgroup Γ} (h : cenIn K A = ⊥) : mOf A K = K := by
  have hF : CFSG.fittingSubgroupOf (cenIn K A) = ⊥ :=
    le_bot_iff.mp ((Subgroup.map_subtype_le _).trans h.le)
  unfold mOf
  rw [hF]
  have h1 : cenIn K ((⊥ : Subgroup Γ) : Set Γ) = K := by
    unfold cenIn
    rw [centralizer_bot, inf_top_eq]
  rw [h1]
  exact inf_eq_left.mpr Subgroup.le_normalizer

theorem isSolvable_scalJoin
    {p : ℕ} (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] (A X : Subgroup Γ), Nat.card X = n →
      NearAsolvAction p A X → Group.IsSolvable (scalJoin X A (cenIn X A)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ _ _ A X hn h
    subst hn
    set D := cenIn X A with hD
    set T := scalJoin X A D with hT
    have hDX : D ≤ X := inf_le_left
    have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
    have hTX : T ≤ X := scalJoin_le_left _ _ _
    have hnormT : D ⊔ A ≤ Subgroup.normalizer (T : Set Γ) :=
      sup_le_normalizer_scalJoin hDA (hDX.trans Subgroup.le_normalizer) h.admits
    have hXD : X ⊓ D = D := inf_eq_right.mpr hDX
    by_cases hTX' : T = X
    · rcases eq_or_ne X ⊥ with hX | hX
      · have : T = ⊥ := le_bot_iff.mp (hX ▸ hTX)
        rw [this]
        infer_instance
      · by_cases hs : sol X = ⊥
        · exfalso
          set K := kOf X with hK
          have hKne : K ≠ ⊥ := kOf_ne_bot hs hX
          have hKss : IsSemisimple K := isSemisimple_kOf hs
          have hXAK : X ⊔ A ≤ Subgroup.normalizer (K : Set Γ) :=
            (sup_le Subgroup.le_normalizer h.admits).trans (normalizer_le_normalizer_kOf X)
          have hKX : K ≤ X := kOf_le X
          have hAK : Admits A K := le_sup_right.trans hXAK
          have hnearK : NearAsolvAction p A K := nearAsolvAction_of_le h hKX hAK
          have hSA : SemisimpleAction p A K := ⟨hnearK, hKss, hKne⟩
          have hMne := mOf_ne_bot hSA
          have ha := scalJoin_semisimple hnearK hKss
          have hF := frattini211 (p := p) (Nat.card X) A X K rfl h hKX
            ⟨hKX.trans le_sup_left, hXAK⟩
          have hcK : scalJoin K A (cenIn X A) = scalJoin K A (cenIn K A) :=
            scalJoin_congr ((inf_cenIn_eq hKX).trans (inf_eq_right.mpr inf_le_left).symm)
          have hSnorm : ∀ S ∈ scalSet X A D, S ≤ Subgroup.normalizer (mOf A K : Set Γ) := by
            intro S hS
            obtain ⟨hSX, hSE, hSs⟩ := hS
            rw [hXD] at hSE
            have := hF.2 S hSX hSE (isSolvable_of_le inf_le_left hSs)
            rw [hcK, ha.1] at this
            exact this
          have hXnorm : X ≤ Subgroup.normalizer (mOf A K : Set Γ) :=
            hTX' ▸ scalJoin_le hSnorm
          have hMs : Group.IsSolvable (mOf A K) := (thm210b hSA).1.2.2
          have h1 : X ⊓ mOf A K ≤ sol X := SolQuot.inf_le_sol hMs hXnorm
          rw [hs] at h1
          exact hMne (le_bot_iff.mp
            ((le_inf (inf_le_left.trans (kOf_le X)) le_rfl : mOf A K ≤ X ⊓ mOf A K).trans h1))
        ·
          set R := sol X with hR
          have hRs : Group.IsSolvable R := isSolvable_sol X
          have hRX : R ≤ X := sol_le X
          have hXn : X ≤ AChief.nrm R := SolQuot.le_nrm_sol X
          have hAn : A ≤ AChief.nrm R := h.admits.trans (SolQuot.normalizer_le_nrm_sol X)
          have hnear : NearAsolvAction p (AChief.qimg R A) (AChief.qimg R X) :=
            nearAsolvAction_qimg h hXn hAn
          have hcard := card_qimg_lt hRX hXn hs
          have hbar := ih _ hcard (AChief.qimg R A) (AChief.qimg R X) rfl hnear
          have hDbar : cenIn (AChief.qimg R X) ((AChief.qimg R A : Subgroup (AChief.QG R)) :
              Set (AChief.QG R)) = AChief.qimg R (cenIn X A) :=
            (AChief.qimg_inf_centralizer h.prime h.elemAbelian h.admits hAn hXn
              h.nearPSolvable.1).symm
          rw [hDbar, ← qimg_scalJoin hRs hRX hXn hAn, ← hT, hTX'] at hbar
          have hXs : Group.IsSolvable X := (SolQuot.isSolvable_qimg_iff hRs hXn).mp hbar
          rw [hTX']
          exact hXs
    · have hlt : Nat.card T < Nat.card X := card_lt_of_ne hTX hTX'
      have hnearT : NearAsolvAction p A T := nearAsolvAction_of_le h hTX (le_sup_right.trans hnormT)
      have hTT : scalJoin T A (cenIn T A) = T := by
        refine le_antisymm (scalJoin_le_left _ _ _) (scalJoin_le fun S hS => ?_)
        refine le_scalJoin ⟨le_scalJoin hS, ?_, hS.2.2⟩
        have hle : T ⊓ cenIn T A ≤ X ⊓ D :=
          le_inf (inf_le_left.trans hTX) (inf_le_right.trans (inf_le_inf_right _ hTX))
        exact (sup_le_sup_right hle A).trans hS.2.1
      have := ih _ hlt A T rfl hnearT
      rwa [hTT] at this

theorem scalJoin_cenIn_eq {A G X : Subgroup Γ} (hXG : X ≤ G) :
    scalJoin X A (cenIn G A) = scalJoin X A (cenIn X A) := by
  have h1 : X ⊓ cenIn X A = cenIn X A := inf_eq_right.mpr inf_le_left
  exact scalJoin_congr ((inf_cenIn_eq hXG).trans h1.symm)

theorem scalJoin_inf_eq
    [Finite Γ] {p : ℕ} {A G X : Subgroup Γ} (h : NearAsolvAction p A G)
    (hXG : X ≤ G) (hX : Admits (cenIn G A ⊔ A) X) :
    scalJoin X A (cenIn G A) = scalJoin G A (cenIn G A) ⊓ X ∧
      Group.IsSolvable (scalJoin X A (cenIn G A)) := by
  have hDA : cenIn G A ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hDG : cenIn G A ≤ G := inf_le_left
  have hDX : Admits (cenIn G A) X := le_sup_left.trans hX
  have hAX : Admits A X := le_sup_right.trans hX
  have hnearX : NearAsolvAction p A X := nearAsolvAction_of_le h hXG hAX
  have hsolX : Group.IsSolvable (scalJoin X A (cenIn G A)) := by
    rw [scalJoin_cenIn_eq hXG]
    exact isSolvable_scalJoin _ A X rfl hnearX
  have hsolG : Group.IsSolvable (scalJoin G A (cenIn G A)) := isSolvable_scalJoin _ A G rfl h
  have hnormG : cenIn G A ⊔ A ≤ Subgroup.normalizer (scalJoin G A (cenIn G A) : Set Γ) :=
    sup_le_normalizer_scalJoin hDA (hDG.trans Subgroup.le_normalizer) h.admits
  have hnormX : cenIn G A ⊔ A ≤ Subgroup.normalizer (scalJoin X A (cenIn G A) : Set Γ) :=
    sup_le_normalizer_scalJoin hDA hDX hAX
  refine ⟨le_antisymm (le_inf ?_ (scalJoin_le_left _ _ _)) ?_, hsolX⟩
  · refine le_scalJoin ⟨(scalJoin_le_left _ _ _).trans hXG, ?_, hsolX⟩
    rw [inf_eq_right.mpr hDG]
    exact hnormX
  · refine le_scalJoin ⟨inf_le_right, fun g hg => ?_, isSolvable_of_le inf_le_left hsolG⟩
    have hg' : g ∈ cenIn G A ⊔ A := sup_le_sup_right inf_le_right A hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hnormG hg', hX hg'⟩

theorem norIn_scalJoin_eq
    [Finite Γ] {p : ℕ} {A X : Subgroup Γ} (h : NearAsolvAction p A X) :
    norIn X (scalJoin X A (cenIn X A) : Set Γ) = scalJoin X A (cenIn X A) := by
  set D := cenIn X A with hD
  set T := scalJoin X A D with hT
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hTX : T ≤ X := scalJoin_le_left _ _ _
  have hXD : X ⊓ D = D := inf_eq_right.mpr hDX
  have hnormT : D ⊔ A ≤ Subgroup.normalizer (T : Set Γ) :=
    sup_le_normalizer_scalJoin hDA (hDX.trans Subgroup.le_normalizer) h.admits
  have hTs : Group.IsSolvable T := isSolvable_scalJoin _ A X rfl h
  have hDT : D ≤ T := by
    have := inf_le_scalJoin (X := X) (A := A) hDA (by rw [hXD]; exact h.solvable_cen)
    rwa [hXD] at this
  refine le_antisymm ?_ (le_inf hTX Subgroup.le_normalizer)
  set N := norIn X (T : Set Γ) with hN
  have hNX : N ≤ X := inf_le_left
  have hTN : T ≤ N := le_inf hTX Subgroup.le_normalizer
  have hNn : N ≤ AChief.nrm T := inf_le_right
  have hAT : A ≤ AChief.nrm T := le_sup_right.trans hnormT
  have hDN : D ≤ N := le_inf hDX (le_sup_left.trans hnormT)
  have hAN : Admits A N := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h.admits ha, Subgroup.le_normalizer (hAT ha)⟩
  have hnearN : NearAsolvAction p A N := nearAsolvAction_of_le h hNX hAN
  have hnearG : NearAsolvAction p (AChief.qimg T A) (AChief.qimg T N) :=
    nearAsolvAction_qimg hnearN hNn hAT
  have hsolG : sol (AChief.qimg T N) = ⊥ := by
    set S' := SolQuot.qpre T (sol (AChief.qimg T N)) with hS'
    have hS'N : S' ≤ N := by
      have := SolQuot.qpre_mono (R := T) (sol_le (AChief.qimg T N))
      rwa [SolQuot.qpre_qimg hNn, sup_eq_left.mpr hTN] at this
    have hq : AChief.qimg T S' = sol (AChief.qimg T N) := SolQuot.qimg_qpre _
    have hE : (X ⊓ D) ⊔ A ≤ AChief.nrm T := by
      rw [hXD]
      exact hnormT
    have hEN : (X ⊓ D) ⊔ A ≤ Subgroup.normalizer (N : Set Γ) := by
      rw [hXD]
      exact sup_le (hDN.trans Subgroup.le_normalizer) hAN
    have hS'mem : S' ∈ scalSet X A D := by
      refine ⟨hS'N.trans hNX, ?_, ?_⟩
      · refine (SolQuot.qimg_le_normalizer_iff (Y := AChief.nrm T) (SolQuot.qpre_le_nrm _)
          (inf_le_right.trans (SolQuot.le_qpre _)) le_rfl hE).mp ?_
        rw [hq]
        exact (AChief.qimg_le_normalizer hEN).trans (SolQuot.normalizer_le_nrm_sol _)
      · exact AChief.isSolvable_of_qimg (SolQuot.le_qpre _) (SolQuot.qpre_le_nrm _) hTs
          (by rw [hq]; exact isSolvable_sol _)
    have hS'T : S' ≤ T := le_scalJoin hS'mem
    rw [← hq]
    exact le_bot_iff.mp ((SolQuot.qimg_mono hS'T).trans SolQuot.qimg_self.le)
  have hcenG : cenIn (AChief.qimg T N)
      ((AChief.qimg T A : Subgroup (AChief.QG T)) : Set (AChief.QG T)) = ⊥ := by
    have himg := AChief.qimg_inf_centralizer h.prime h.elemAbelian hAN hAT hNn
      hnearN.nearPSolvable.1
    show AChief.qimg T N ⊓ Subgroup.centralizer
      ((AChief.qimg T A : Subgroup (AChief.QG T)) : Set (AChief.QG T)) = ⊥
    rw [← himg]
    have hle : N ⊓ Subgroup.centralizer (A : Set Γ) ≤ T :=
      ((inf_le_inf_right _ hNX : N ⊓ Subgroup.centralizer (A : Set Γ) ≤ D)).trans hDT
    exact le_bot_iff.mp ((SolQuot.qimg_mono hle).trans SolQuot.qimg_self.le)
  have hbot : AChief.qimg T N = ⊥ := by
    by_contra hne
    set G' := AChief.qimg T N with hG'
    set A' := AChief.qimg T A with hA'
    set K := kOf G' with hK
    have hKne : K ≠ ⊥ := kOf_ne_bot hsolG hne
    have hKss : IsSemisimple K := isSemisimple_kOf hsolG
    have hA'K : Admits A' K := hnearG.admits.trans (normalizer_le_normalizer_kOf G')
    have hnearK : NearAsolvAction p A' K := nearAsolvAction_of_le hnearG (kOf_le G') hA'K
    have hcen : cenIn K A' = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ (kOf_le G') : cenIn K A' ≤ cenIn G' A').trans hcenG.le)
    have ha := scalJoin_semisimple hnearK hKss
    rw [mOf_eq_self_of_cenIn_eq_bot hcen] at ha
    have hKs : Group.IsSolvable K := by
      rw [← ha.1]
      exact ha.2
    have hG'K : G' ≤ Subgroup.normalizer (K : Set (AChief.QG T)) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_kOf G')
    have h1 : G' ⊓ K ≤ sol G' := SolQuot.inf_le_sol hKs hG'K
    rw [hsolG] at h1
    exact hKne (le_bot_iff.mp ((le_inf (kOf_le G') le_rfl : K ≤ G' ⊓ K).trans h1))
  exact (SolQuot.qimg_eq_bot_iff hNn).mp hbot

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211
