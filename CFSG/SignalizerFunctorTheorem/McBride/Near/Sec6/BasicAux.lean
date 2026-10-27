module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.RF

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thetaLG_bot_eq_bot
    (h : Counterexample p A θ) : thetaLG p A θ ⊥ = ⊥ :=
  (h.thetaMG_mem_or_thetaLG_eq_bot h.bot_mem_dset).resolve_left h.thetaMG_not_mem_assoc

theorem thetaL_bot_eq_bot
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) : thetaL p A θ ⊥ X = ⊥ :=
  le_bot_iff.mp ((le_iSup₂_of_le (f := fun X (_ : X ∈ cset p A θ ⊥) => thetaL p A θ ⊥ X) X hX
    le_rfl).trans h.thetaLG_bot_eq_bot.le)

theorem thetaM_bot_pair
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    (thetaM p A θ ⊥ X, (⊥ : Subgroup G)) ∈ pairsP p A θ ∧ thetaM p A θ ⊥ X ≤ X := by
  have hP := thetaM_thetaL_mem_pairsYX h.hyp.nearFunctor h.bot_mem_dset hX
  rw [h.thetaL_bot_eq_bot hX] at hP
  exact ⟨hP.1.1, hP.2⟩


theorem kOf_ne_bot_of_not_isSolvable {X : Subgroup G} (hX : ¬ Group.IsSolvable X) :
    kOf X ≠ ⊥ := by
  intro hK
  have hsol : sol X = ⊥ := le_bot_iff.mp ((sol_le_kOf X).trans hK.le)
  have hc := centralizer_kOf_eq_bot hsol
  apply hX
  have hX1 : X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ X ⊓ Subgroup.centralizer (kOf X : Set G) := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      rw [hK, SetLike.mem_coe, Subgroup.mem_bot] at hg
      subst hg
      simp
    rw [hc] at this
    exact this
  rw [hX1]
  infer_instance

theorem thetaM_bot_eq_kOf
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    thetaM p A θ ⊥ X = kOf X := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨hP, hMX⟩ := h.thetaM_bot_pair hX
  have hns := (h.mem_cset_bot_iff.mp hX).2
  have hXm : X ∈ mtil p A θ := hX.1
  have hKM : kOf X ≤ thetaM p A θ ⊥ X := kOf_le_thetaM hθ h.bot_mem_dset hX
  have hAX : Admits A X := hXm.1.1
  have hKn : IsNormalIn (kOf X) (thetaM p A θ ⊥ X ⊔ dsub A θ ⊔ A) := by
    refine ⟨hKM.trans (le_sup_left.trans le_sup_left), sup_le (sup_le ?_ ?_) ?_⟩
    · exact hMX.trans (Thm41Aux.le_normalizer_kOf X)
    · exact hXm.2.trans (Thm41Aux.le_normalizer_kOf X)
    · exact Thm41Aux.admits_kOf hAX
  exact ((hP.2.2.1.2.2.2 (kOf X) hKn bot_le hKM).resolve_left
    (kOf_ne_bot_of_not_isSolvable hns)).symm

theorem isChiefFactorOf_kOf
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) :
    IsChiefFactorOf (kOf X ⊔ dsub A θ ⊔ A) (kOf X) ⊥ := by
  have := (h.thetaM_bot_pair hX).1.2.2.1
  rw [h.thetaM_bot_eq_kOf hX] at this
  exact this

theorem secCenIn_kOf
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    secCenIn (kOf X ⊔ dsub A θ) (kOf X) ⊥ = ⊥ := by
  have := (h.thetaM_bot_pair hX).1.2.2.2
  rw [h.thetaM_bot_eq_kOf hX] at this
  exact this

theorem not_isSolvable_kOf
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) : ¬ Group.IsSolvable (kOf X) := by
  have hθ := h.hyp.nearFunctor
  have hP := thetaM_thetaL_mem_pairsYX hθ h.bot_mem_dset hX
  have hiP : (thetaM p A θ ⊥ X, thetaL p A θ ⊥ X) ∈ iPairs A X := by
    have : (thetaM p A θ ⊥ X, thetaL p A θ ⊥ X) ∈ iPairsY A X ⊥ := by
      rw [← pairsYX_eq_iPairsY hθ hX.1]
      exact hP
    exact this.1
  rw [h.thetaL_bot_eq_bot hX, h.thetaM_bot_eq_kOf hX] at hiP
  intro hsol
  obtain ⟨n, hn⟩ := hsol.solvable
  exact Thm33a.not_isSolvableSection_of_mem_iPairs hiP ⟨n, (le_of_eq hn).trans bot_le⟩

theorem sol_eq_bot_of_mem_cset
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) : sol X = ⊥ := by
  have hXm : X ∈ mtil p A θ := hX.1
  have hch := h.isChiefFactorOf_kOf hX
  have hAX : Admits A X := hXm.1.1
  have hsn : IsNormalIn (sol X) (kOf X ⊔ dsub A θ ⊔ A) := by
    refine ⟨(sol_le_kOf X).trans (le_sup_left.trans le_sup_left), sup_le (sup_le ?_ ?_) ?_⟩
    · exact (kOf_le X).trans (Thm41Aux.le_normalizer_sol X)
    · exact hXm.2.trans (Thm41Aux.le_normalizer_sol X)
    · exact fun a ha => Thm41Aux.mem_normalizer_sol_of_mem_normalizer (hAX ha)
  rcases hch.2.2.2 (sol X) hsn bot_le (sol_le_kOf X) with h0 | h1
  · exact h0
  · exact absurd (h1 ▸ isSolvable_sol X) (h.not_isSolvable_kOf hX)

theorem isSemisimple_kOf_of_mem_cset
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) : IsSemisimple (kOf X) :=
  isSemisimple_kOf (h.sol_eq_bot_of_mem_cset hX)

theorem dsub_inf_centralizer_kOf
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) : dsub A θ ⊓ Subgroup.centralizer (kOf X : Set G) = ⊥ := by
  have hsec := h.secCenIn_kOf hX
  rw [eq_bot_iff]
  rintro d ⟨hdD, hdC⟩
  have : d ∈ secCenIn (kOf X ⊔ dsub A θ) (kOf X) ⊥ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hdD, ?_⟩
    refine ⟨?_, Thm41Aux.le_normalizer_kOf X (hX.1.2 hdD), fun y hy => ?_⟩
    · exact (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)) ▸
        Subgroup.mem_top d
    · have := Subgroup.mem_centralizer_iff.mp hdC y hy
      rw [commutatorElement_eq_one_iff_mul_comm.mpr this.symm]
      exact one_mem _
  rw [hsec] at this
  exact this


theorem mem_pairsYX_bot
    (h : Counterexample p A θ) {P : Subgroup G × Subgroup G}
    (hP : P ∈ pairsP p A θ) {X : Subgroup G} (hPX : P.1 ≤ X) : P ∈ pairsYX p A θ ⊥ X := by
  have hmem : dsub A θ ⊓ P.2 ∈ dset p A θ := ⟨P, hP, rfl⟩
  rw [h.dset_eq_singleton, Set.mem_singleton_iff] at hmem
  exact ⟨⟨hP, by rw [inf_comm]; exact hmem⟩, hPX⟩

theorem le_kOf_of_mem_pairsP
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) {P : Subgroup G × Subgroup G} (hP : P ∈ pairsP p A θ)
    (hPX : P.1 ≤ X) : P.1 ≤ kOf X :=
  (le_iSup₂_of_le (f := fun P (_ : P ∈ pairsYX p A θ ⊥ X) => P.1) P
    (h.mem_pairsYX_bot hP hPX) le_rfl).trans (h.thetaM_bot_eq_kOf hX).le

theorem perfRes_le_kOf
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    perfRes X ≤ kOf X := by
  by_contra hnle
  have hθ := h.hyp.nearFunctor
  have hXm : X ∈ mtil p A θ := hX.1
  set U : Subgroup G := perfRes X with hU
  have hUX : U ≤ X := Subgroup.map_subtype_le _
  have hNX : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    Nonsolvable.normalizer_le_normalizer_perfectResidual_map X
  have hAX : Admits A X := hXm.1.1
  have hUadm : Admits (dsub A θ ⊔ A) U :=
    sup_le (hXm.2.trans (Subgroup.le_normalizer.trans hNX)) (hAX.trans hNX)
  have hUp : Group.IsPerfect U := Nonsolvable.isPerfect_perfectResidual_map X
  have hKadm : Admits (dsub A θ ⊔ A) (kOf X) :=
    sup_le (hXm.2.trans (Thm41Aux.le_normalizer_kOf X)) (Thm41Aux.admits_kOf hAX)
  have hNU : U ⊓ kOf X < U := inf_lt_left.mpr hnle
  have hNn : IsNormalIn (U ⊓ kOf X) U :=
    ⟨inf_le_left, fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, Thm41Aux.le_normalizer_kOf X (hUX hg)⟩⟩
  obtain ⟨P, hP, hUP, hPX⟩ :=
    RFAux.exists_pair_above_perfect hθ hXm hUX hUadm hUp hNU hNn (hUadm.inf hKadm)
  exact hnle (hUP.trans (h.le_kOf_of_mem_pairsP hX hP hPX))

theorem isPerfect_kOf
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    Group.IsPerfect ↥(kOf X) := by
  rw [kOf_eq_map_layer (h.sol_eq_bot_of_mem_cset hX)]
  have : Group.IsPerfect ↥(CFSG.layer ↥X) := CFSG.LocalCores.layer_isPerfect
  exact Group.IsPerfect.map X.subtype

theorem perfRes_eq_kOf
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    perfRes X = kOf X :=
  le_antisymm (h.perfRes_le_kOf hX)
    (Nonsolvable.le_perfectResidual_map_of_isPerfect (h.isPerfect_kOf hX) (kOf_le X))

theorem eq_kOf_of_isChiefFactorOf
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) {M : Subgroup G}
    (hM : IsChiefFactorOf (kOf X ⊔ dsub A θ ⊔ A) M ⊥) (hMle : M ≤ kOf X ⊔ dsub A θ) :
    M = kOf X := by
  have hch := h.isChiefFactorOf_kOf hX
  have hsec := h.secCenIn_kOf hX
  have hMK : IsNormalIn (M ⊓ kOf X) (kOf X ⊔ dsub A θ ⊔ A) :=
    ⟨inf_le_left.trans hM.2.1.1, fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hM.2.1.2 hg, hch.2.1.2 hg⟩⟩
  rcases hM.2.2.2 (M ⊓ kOf X) hMK bot_le inf_le_left with h0 | h1
  · exfalso
    refine absurd ?_ (ne_of_gt hM.2.2.1)
    rw [eq_bot_iff]
    intro m hm
    have hmT := hM.2.1.1 hm
    have : m ∈ secCenIn (kOf X ⊔ dsub A θ) (kOf X) ⊥ := by
      refine Subgroup.mem_inf.mpr ⟨hMle hm, ?_⟩
      refine ⟨?_, hch.2.1.2 hmT, fun y hy => ?_⟩
      · exact (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)) ▸
          Subgroup.mem_top m
      · have hyT : y ∈ kOf X ⊔ dsub A θ ⊔ A := hch.2.1.1 hy
        have h1 : ⁅m, y⁆ ∈ kOf X := by
          have := (Subgroup.mem_normalizer_iff.mp (hch.2.1.2 hmT) y).mp hy
          exact mul_mem this (inv_mem hy)
        have h2 : ⁅m, y⁆ ∈ M := by
          have := (Subgroup.mem_normalizer_iff.mp (hM.2.1.2 hyT) m⁻¹).mp (inv_mem hm)
          have e : ⁅m, y⁆ = m * (y * m⁻¹ * y⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact mul_mem hm (by simpa using this)
        have h3 : ⁅m, y⁆ ∈ M ⊓ kOf X := ⟨h2, h1⟩
        rwa [h0] at h3
    rw [hsec] at this
    exact this
  · have hMK' : M ≤ kOf X := inf_eq_left.mp h1
    exact (hch.2.2.2 M hM.2.1 bot_le hMK').resolve_left (ne_of_gt hM.2.2.1)


theorem exists_conj_eq_of_mem_lcal_kOf
    (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ cset p A θ ⊥) {J J' : Subgroup G} (hJ : J ∈ lcal (kOf X))
    (hJ' : J' ∈ lcal (kOf X)) :
    ∃ g ∈ dsub A θ ⊔ A, J' = J.map (MulAut.conj g).toMonoidHom := by
  classical
  have hK := h.isSemisimple_kOf_of_mem_cset hX
  have hdp := hK.isDirectProduct_lcal
  have hch := h.isChiefFactorOf_kOf hX
  have hXm : X ∈ mtil p A θ := hX.1
  have hDAN : dsub A θ ⊔ A ≤ Subgroup.normalizer (kOf X : Set G) :=
    sup_le (hXm.2.trans (Thm41Aux.le_normalizer_kOf X)) (Thm41Aux.admits_kOf hXm.1.1)
  set O : Set (Subgroup G) :=
    {J'' | ∃ g ∈ dsub A θ ⊔ A, J'' = J.map (MulAut.conj g).toMonoidHom} with hO
  have hOsub : O ⊆ lcal (kOf X) := by
    rintro _ ⟨g, hg, rfl⟩
    exact map_conj_mem_lcal hJ (hDAN hg)
  have hJO : J ∈ O := ⟨1, one_mem _, by ext y; simp⟩
  have hJne : ∀ J'' ∈ lcal (kOf X), J'' ≠ ⊥ := by
    intro J'' hJ'' hbot
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ''
    rw [hbot] at hnc
    exact hnc inferInstance
  set N : Subgroup G := sSup O with hN
  have hNK : N ≤ kOf X := sSup_le fun J'' hJ'' => hdp.le (hOsub hJ'')
  have hKN : kOf X ≤ Subgroup.normalizer (N : Set G) := by
    have : Admits (kOf X) N := by
      rw [hN, sSup_eq_iSup']
      exact Admits.iSup fun J'' => hdp.le_normalizer (hOsub J''.2)
    exact this
  have hconj : ∀ g ∈ dsub A θ ⊔ A, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    intro g hg
    have : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun J'' hJ'' y hy => ?_
      obtain ⟨g₀, hg₀, rfl⟩ := hJ''
      have hmem : (MulAut.conj g).toMonoidHom y ∈
          (J.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
      rw [Subgroup.map_map] at hmem
      have hO' : (J.map ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom)) ∈ O := by
        refine ⟨g * g₀, mul_mem hg hg₀, ?_⟩
        ext z
        simp [mul_assoc]
      exact le_sSup hO' hmem
    intro x hx
    exact this hx
  have hDAN' : dsub A θ ⊔ A ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun x =>
      ⟨hconj g hg x, fun hx => by
        have := hconj g⁻¹ (inv_mem hg) _ hx
        have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rwa [e] at this⟩
  have hNn : IsNormalIn N (kOf X ⊔ dsub A θ ⊔ A) :=
    ⟨hNK.trans (le_sup_left.trans le_sup_left), sup_le (sup_le hKN
      (le_sup_left.trans hDAN')) (le_sup_right.trans hDAN')⟩
  have hNK' : N = kOf X := by
    refine (hch.2.2.2 N hNn bot_le hNK).resolve_left fun hbot => hJne J hJ ?_
    exact le_bot_iff.mp (hbot ▸ le_sSup hJO)
  have hJ'N : J' ≤ N := hNK' ▸ hdp.le hJ'
  by_contra hcon
  push Not at hcon
  have hJ'O : J' ∉ O := fun hmem => by
    obtain ⟨g, hg, hg'⟩ := hmem
    exact hcon g hg hg'
  have hle : N ≤ sSup (lcal (kOf X) \ {J'}) := by
    refine sSup_le_sSup fun J'' hJ'' => ⟨hOsub hJ'', fun hh => hJ'O ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rwa [← hh]
  have hdisj := disjoint_iff.mp (hdp.indep hJ')
  have : J' ≤ J' ⊓ sSup (lcal (kOf X) \ {J'}) := le_inf le_rfl (hJ'N.trans hle)
  rw [hdisj] at this
  exact hJne J' hJ' (le_bot_iff.mp this)

theorem apply_mem_cset_bot
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hns : ¬ Group.IsSolvable (θ a)) : θ a ∈ cset p A θ ⊥ :=
  h.mem_cset_bot_iff.mpr ⟨apply_mem_mtil h.hyp.nearFunctor ha ha1, hns⟩

theorem zpowers_mem_rSetN_one_iff
    (h : Counterexample p A θ) {a : G} :
    Subgroup.zpowers a ∈ rSetN p A θ 1 ↔ a ∈ A ∧ a ≠ 1 ∧ ¬ Group.IsSolvable (θ a) := by
  have hθ := h.hyp.nearFunctor
  constructor
  · intro hmem
    obtain ⟨h1, h2, h3, -⟩ := h.mem_rSetN_iff.mp hmem
    have ha1 : a ≠ 1 := fun h' => h1 (by rw [h', Subgroup.zpowers_one_eq_bot])
    have ha : a ∈ A := Subgroup.zpowers_le.mp h2
    refine ⟨ha, ha1, ?_⟩
    rwa [hθ.isFunctor.thetaOf_zpowers ha ha1] at h3
  · rintro ⟨ha, ha1, hns⟩
    refine h.mem_rSetN_iff.mpr ⟨?_, Subgroup.zpowers_le.mpr ha, ?_, ?_⟩
    · exact fun hbot => ha1 (Subgroup.zpowers_eq_bot.mp hbot)
    · rwa [hθ.isFunctor.thetaOf_zpowers ha ha1]
    · rw [pow_one, Nat.card_zpowers]
      have := Fact.mk hθ.prime
      exact orderOf_eq_prime (hθ.elemAbelian.2 a ha) ha1

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
