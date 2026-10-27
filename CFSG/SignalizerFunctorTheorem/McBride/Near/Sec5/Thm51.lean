module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Signalizers
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Minimal
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm51dAux

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem completeBelow (h : Counterexample p A θ) :
    CompleteBelow p (nearClass.{u} p) (Nat.card G) (Nat.card A) := by
  intro H _ _ hlt A' θ' hA' hcard hθ' hC'
  exact h.ih H hlt A' θ' ⟨h.hyp.prime, h.hyp.odd, hA', hcard.trans h.hyp.card, hθ', hC'⟩

theorem exists_not_solvable (h : Counterexample p A θ) :
    ∃ a ∈ A, a ≠ 1 ∧ ¬ Group.IsSolvable (θ a) := by
  by_contra hcon
  push Not at hcon
  have hrank : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  obtain ⟨W, hWsol, hWA, hWcop, hWfix, hWmax⟩ := exists_greatest_signalizer_of_isFunctor
    h.hyp.prime h.hyp.elemAbelian hrank h.hyp.isFunctor hcon
  refine h.notComplete ⟨W, ⟨hWA, hWcop, fun a ha ha1 => (hWfix a ha ha1).le,
    nearASolvable_of_isSolvable hWsol hWcop⟩, fun X hX => hWmax X hX.1 hX.2.1 hX.2.2.1⟩

theorem isLocallyComplete (h : Counterexample p A θ) :
    IsLocallyCompleteIn (assoc p A θ) :=
  isLocallyCompleteIn_of_incomplete h.hyp.prime (isSigClass_nearClass h.hyp.prime)
    h.hyp.elemAbelian h.hyp.isFunctor h.hyp.near h.completeBelow h.notComplete

theorem sSup_sup_eq_top (h : Counterexample p A θ) : wsub p A θ ⊔ A = ⊤ := by
  have key := sSup_signalizers_sup_eq_top (Cl := nearClass.{u} p) (A := A) (θ := θ)
    h.hyp.prime (isSigClass_nearClass h.hyp.prime) h.hyp.elemAbelian h.hyp.isFunctor
    h.hyp.near h.completeBelow h.notComplete
  exact key

theorem center_sSup_eq_bot (h : Counterexample p A θ) :
    wsub p A θ ⊓ Subgroup.centralizer (wsub p A θ : Set G) = ⊥ := by
  by_contra hne
  have hG := h.sSup_sup_eq_top
  have hnormal : ∀ N : Subgroup G, N.Normal → N ∈ assoc p A θ → N = ⊥ := fun N _ hN =>
    eq_bot_of_normal_of_incomplete h.hyp.prime (isSigClass_nearClass h.hyp.prime)
      h.hyp.elemAbelian h.hyp.isFunctor h.hyp.near h.completeBelow h.notComplete hN
  have hWnormal : (wsub p A θ).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hG]
    exact sup_le Subgroup.le_normalizer Thm51d.admits_wsub
  have hcard : Nat.card (wsub p A θ ⊓ Subgroup.centralizer (wsub p A θ : Set G) :
      Subgroup G) ≠ 1 := fun h1 => hne ((Subgroup.eq_bot_iff_card _).mpr h1)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hcard
  have hZbot := Thm51d.omegaCenter_ne_bot hr hrdvd
  have : (Thm51d.omegaCenter r (wsub p A θ)).Normal := Thm51d.normal_omegaCenter hWnormal
  rcases eq_or_ne r p with hrp | hrp
  · subst hrp
    exact Thm51d.false_of_central_p h hZbot Thm51d.omegaCenter_le
      Thm51d.omegaCenter_le_centralizer Thm51d.isPGroup_omegaCenter
  · exact Thm51d.false_of_central_ne h h.exists_not_solvable hnormal hG hr hrp hZbot
      Thm51d.omegaCenter_le Thm51d.omegaCenter_le_centralizer Thm51d.isPGroup_omegaCenter

theorem not_dsub_le_of_mem_dset
    (hθ : NearFunctor p A θ) {Y : Subgroup G}
    (hY : Y ∈ dset p A θ) : ¬ dsub A θ ≤ Y := by
  obtain ⟨⟨X₁, X₂⟩, hP, rfl⟩ := hY
  intro hle
  have hX₂ : X₂ ∈ mhat p A θ := hP.2.1
  have hX₁ : X₁ ∈ mhat p A θ := hP.1
  have hX₂1 : X₂ < X₁ := hP.2.2.1.2.2.1
  have hnorm : ((dsub A θ ⊓ X₂).subgroupOf (dsub A θ)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (fun d hd => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hd,
        hX₂.2 hd⟩)
  have hnorm1 : ((dsub A θ ⊓ X₂).subgroupOf (dsub A θ ⊓ X₁)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_left _ hX₂1.le)).mpr
      (fun d hd => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hd.1, hX₂.2 hd.1⟩)
  obtain ⟨-, hchief, -⟩ := fitting_minimal_normal hθ hP
  have hlt := hchief.2.2.1
  have hleD := hchief.2.1.1
  exact lt_irrefl _ (lt_of_le_of_lt hle (lt_of_lt_of_le hlt hleD))

theorem thetaYFun_complete
    (h : Counterexample p A θ) {Y : Subgroup G}
    (hY : Y ∈ dset p A θ) :
    IsCompleteIn (signalizers p A (thetaYFun p A θ Y) (NearASolvable p A)) := by
  have hθ := h.hyp.nearFunctor
  have hrank : p ^ 3 ≤ Nat.card A := h.hyp.card.ge
  have hfun : IsFunctor p A (thetaYFun p A θ Y) := thetaY_isFunctor hθ hrank hY
  have hmem : ∀ a ∈ A, a ≠ 1 → thetaY p A θ Y (θ a) ∈ esetX p A θ Y (θ a) :=
    fun a ha ha1 => thetaY_mem_esetX_of_rank hθ hrank hY ha ha1
  have hnear : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (thetaYFun p A θ Y a) :=
    fun a ha ha1 => (hmem a ha ha1).1.1.1.2.2.2
  refine h.complete_of_size_lt ⟨h.hyp.prime, h.hyp.odd, h.hyp.elemAbelian, h.hyp.card, hfun,
    hnear⟩ (size_lt_size (fun a _ _ => thetaY_le Y (θ a)) ?_)
  obtain ⟨a, ha, ha1⟩ := exists_mem_ne_one hθ
  refine ⟨a, ha, ha1, fun heq => ?_⟩
  refine not_dsub_le_of_mem_dset hθ hY ?_
  have h1 := (hmem a ha ha1).1.2
  have h2 : thetaY p A θ Y (θ a) = θ a := heq
  rw [h2] at h1
  rw [← h1]
  exact le_inf (dsub_le_apply ha ha1) le_rfl

theorem thetaMG_mem_or_thetaLG_eq_bot
    (h : Counterexample p A θ) {Y : Subgroup G}
    (hY : Y ∈ dset p A θ) : thetaMG p A θ Y ∈ assoc p A θ ∨ thetaLG p A θ Y = ⊥ := by
  by_cases hL : thetaLG p A θ Y = ⊥
  · exact Or.inr hL
  refine Or.inl ?_
  have hθ := h.hyp.nearFunctor
  have hc := h.thetaYFun_complete hY
  have hLmem := thetaLG_mem_assoc hθ hY hc
  have hMle := thetaMG_le_normalizer_thetaLG hθ h.hyp.card hY hc
  obtain ⟨M', hM'mem, hM'N, hM'max⟩ := h.isLocallyComplete (thetaLG p A θ Y) hLmem hL
  have hadmM : ∀ X, Admits A (thetaM p A θ Y X) := fun X =>
    Admits.iSup fun P => Admits.iSup fun hP => hP.1.1.1.1.1
  have hle : thetaMG p A θ Y ≤ M' := by
    refine iSup₂_le fun X hX => ?_
    have hXle : thetaM p A θ Y X ≤ X := iSup₂_le fun P hP => hP.2
    have hXassoc : thetaM p A θ Y X ∈ assoc p A θ :=
      mem_assoc_of_le hθ.prime hX.1.1 hXle (hadmM X)
    exact hM'max _ hXassoc ((le_iSup₂ (f := fun X (_ : X ∈ cset p A θ Y) =>
      thetaM p A θ Y X) X hX).trans hMle)
  have hadm : Admits A (thetaMG p A θ Y) :=
    Admits.iSup fun X => Admits.iSup fun _ => hadmM X
  exact mem_assoc_of_le hθ.prime hM'mem hle hadm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
