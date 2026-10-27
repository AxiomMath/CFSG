module

public import CFSG.Timmesfeld.ARS.Sec13Restrict
public import CFSG.Timmesfeld.ARS.Sec5Count

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem gen_singleton' (P : Subgroup G) : gen {P} = P := by
  simp [gen]

section Prelim

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hA₀

theorem commuting_of_mem_lambdaSet_of_mem_leviSet {D F X : Subgroup G}
    (hD : D ∈ lambdaSet R A) (hF : F ∈ leviSet R A A₀) (hDF : D ∈ lambdaSet R F)
    (hX : X ∈ leviSet R A A₀) (hXF : X ∈ lambdaSet R F) : Commuting D X := by
  have := h.finite
  have hR := h.root
  have hFR : F ∈ R := hF.1.1
  rw [commuting_iff_commutator_eq_bot, eq_bot_iff, ← M_inf_levi_eq_bot h hA hA₀]
  refine le_inf (commutator_le_of_le_normalizer (QD.le_M hD)
    (QD.le_normalizer_M hR hA ⟨hX.1.1, hX.1.2.2⟩)) ?_
  calc ⁅D, X⁆ ≤ ⁅M R F, M R F⁆ := Subgroup.commutator_mono (QD.le_M hDF) (QD.le_M hXF)
    _ = F := (Q_eq_M h hFR).2.2.1
    _ ≤ levi R A A₀ := le_gen hF

theorem eq_of_le_sup_of_mem_lambdaStar {X Y : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hY : Y ∈ lambdaStar R A A₀) (hYle : Y ≤ A ⊔ X) : Y = X := by
  have := h.finite
  obtain ⟨D', -, hu⟩ :=
    existsUnique_mem_psiSet_of_le h.root h.noIsolated hA hA₀.1 hA₀.2 hX.1
  exact (hu Y ⟨hY.1.1.1, hYle, hY.2⟩).trans (hu X ⟨hX.1.1.1, le_sup_right, hX.2⟩).symm

omit hA hA₀ in
theorem le_of_inf_ne_bot {T X : Subgroup G} (hT : CoveredBy R T) (hX : X ∈ R)
    (hXT : X ⊓ T ≠ ⊥) : X ≤ T := by
  have := h.finite
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hXT
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  obtain ⟨hxX, hxT⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨Q, hQ, hQT, hxQ⟩ := hT x hxT hx1'
  by_contra hXQ
  have hne : X ≠ Q := fun e => hXQ (e ▸ hQT)
  have hm : x ∈ X ⊓ Q := ⟨hxX, hxQ⟩
  rw [inf_eq_bot h.root h.noIsolated hX hQ hne, Subgroup.mem_bot] at hm
  exact hx1' hm

end Prelim

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

theorem exists_commutator_eq_of_mem_lambdaSet {D E : Subgroup G}
    (hD : D ∈ lambdaStar R A A₀) (hE : E ∈ lambdaStar R A A₀) (hED : E ∈ lambdaSet R D) :
    ∃ F ∈ leviSet R A A₀, ⁅E, F⁆ = D ∧ Special R E F ∧ F ∈ lambdaSet R D ∧
      (∃ L ∈ leviSet R A A₀, Opposite F L ∧ E ∈ lambdaSet R L) ∧
      ∀ P ∈ R, P ≤ E ⊔ D → P ∈ lambdaStar R A A₀ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hDR : D ∈ R := hD.1.1.1
  have hER : E ∈ R := hE.1.1.1
  obtain ⟨F, hF, hEFD⟩ :=
    exists_commutator_eq_of_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hE hD hED
  have hs : Special R E F :=
    special_of_commutator_mem_of_mem_leviSet hS.hyp hS.mem hE hF (hEFD ▸ hDR)
  have hFD : F ∈ lambdaSet R D := by
    have := (mem_lambdaSet_commutator hR hiso hER hF.1.1 hs).2
    rwa [hEFD] at this
  obtain ⟨hpts, L, hL, hFL, hEL⟩ :=
    exists_opposite_of_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hF hE hs
  exact ⟨F, hF, hEFD, hs, hFD, ⟨L, hL, hFL, hEL⟩, fun P hP hPle => hpts P hP (hEFD ▸ hPle)⟩

theorem exists_mem_lambdaStar_inf_eq_bot {D E : Subgroup G} (hD : D ∈ lambdaStar R A A₀)
    (hE : E ∈ lambdaStar R A A₀) (hED : E ∈ lambdaSet R D) :
    ∃ P ∈ lambdaStar R A A₀, P ∈ lambdaSet R D ∧ P ∈ lambdaSet R E ∧ P ⊓ (A ⊔ D ⊔ E) = ⊥ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hA₀ := hS.opp
  have hDR : D ∈ R := hD.1.1.1
  have hER : E ∈ R := hE.1.1.1
  obtain ⟨F, hF, hEFD, hs, hFD, ⟨L, hL, hFL, hEL⟩, hline⟩ :=
    hS.exists_commutator_eq_of_mem_lambdaSet hD hE hED
  have hDF : D ∈ lambdaSet R F := mem_lambdaSet_comm hDR hFD
  have hDE : D ∈ lambdaSet R E := mem_lambdaSet_comm hDR hED
  have hcD : ∀ X ∈ leviSet R A A₀, X ∈ lambdaSet R F → Commuting D X := fun X hX hXF =>
    commuting_of_mem_lambdaSet_of_mem_leviSet hS.hyp hA hA₀ hD.1 hF hDF hX hXF
  obtain ⟨F₁, hF₁, hF₁F, hEF₁, hF₁D⟩ : ∃ F₁ ∈ leviSet R A A₀, F₁ ∈ lambdaSet R F ∧
      ¬ Commuting E F₁ ∧ F₁ ∉ lambdaSet R D := by
    by_contra! hall
    have hN : levi R A A₀ ≤ Subgroup.normalizer ((E ⊔ D : Subgroup G) : Set G) := by
      rw [← hS.gen_inter_lambdaSet_sup_eq_levi hF hL hFL]
      refine sup_le (gen_le fun X hX => le_normalizer_of_conjSub_le fun x hx => ?_) ?_
      · have hXD := hcD X hX.1 hX.2
        by_cases hEX : Commuting E X
        · rw [conjSub_of_forall_commute fun y hy =>
            ((Commuting.sup_left hEX hXD) y hy x hx).symm]
        · have hXΛ := hall X hX.1 hX.2 hEX
          have hEX' : ⁅E, X⁆ ≤ D := by
            rw [← (Q_eq_M hS.hyp hDR).2.2.1]
            exact Subgroup.commutator_mono (QD.le_M hED) (QD.le_M hXΛ)
          rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
            conjSub_of_forall_commute fun y hy => (hXD y hy x hx).symm]
          exact sup_le ((conjSub_le_commutator_sup hx).trans (sup_le (hEX'.trans le_sup_right)
            le_sup_left)) le_sup_right
      · refine le_normalizer_of_conjSub_le fun x hx => ?_
        have hinv := Sec3.conjSub_sup_commutator_eq hR hiso hL.1.1 hF.1.1 hFL.symm hEL
          ⟨hER, hs.symm⟩ (Subgroup.mem_sup_left hx)
        rw [Subgroup.commutator_comm, hEFD] at hinv
        exact hinv.le
    have hM : M R A ≤ E ⊔ D := by
      rw [M_eq_gen_lambdaStar hS.hyp hA hA₀]
      refine gen_le fun C hC => ?_
      obtain ⟨v, hv, rfl⟩ :=
        exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hA hS.sec8.2 hS.max hA₀ hE hC
      calc conjSub E v ≤ conjSub (E ⊔ D) v := Subgroup.map_mono le_sup_left
        _ = E ⊔ D := conjSub_eq_self_iff.2 (hN hv)
    have hM' : M R A ≤ D ⊔ E := sup_comm E D ▸ hM
    have hcomm : Commuting (M R A) (M R A) :=
      (commuting_sup_of_mem_lambdaSet hR hDR hED).mono hM' hM'
    apply hR.ne_bot A hA
    rw [← (Q_eq_M hS.hyp hA).2.2.1]
    exact commuting_iff_commutator_eq_bot.1 hcomm
  have hsF₁ : Special R E F₁ :=
    special_of_not_commuting_of_mem_leviSet hS.hyp hA hE hF₁ hEF₁
  obtain ⟨hP, hPE, hPF₁⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hE hF₁ hsF₁
  set P := ⁅E, F₁⁆ with hPdef
  have hPR : P ∈ R := hP.1.1.1
  have hDF₁ : Commuting D F₁ := hcD F₁ hF₁ hF₁F
  have hPD' : P ≠ D := fun e => hF₁D (e ▸ mem_lambdaSet_comm hF₁.1.1 hPF₁)
  have hPD : P ∈ lambdaSet R D :=
    mem_lambdaSet_of_le_M_of_hyp hS.hyp hDR hPR (commutator_le_of_le_normalizer (QD.le_M hED)
      (QD.le_normalizer_M hR hDR ⟨hF₁.1.1, hDF₁⟩)) hPD'
  refine ⟨P, hP, hPD, hPE, ?_⟩
  have hpl := plane hR hiso hA hDR hED fun X hX hXle => (hline X hX (sup_comm D E ▸ hXle)).1
  by_contra hne
  have hPle : P ≤ A ⊔ D ⊔ E := le_of_inf_ne_bot hS.hyp hpl.2.2.1 hPR hne
  have hAP : A ≠ P := fun e => hP.1.1.2.1 e.symm
  obtain ⟨Q, hQ, hQAP, hQDE⟩ := Plane.exists_le_sup_le_sup hR hiso hA hDR hED
    (fun X hX hXle => (hline X hX (sup_comm D E ▸ hXle)).1) hA (le_sup_left.trans le_sup_left)
    hPR hPle hAP hDR (le_sup_right.trans le_sup_left) hER le_sup_right hED.1.2.1.symm
  have hQP : Q = P := eq_of_le_sup_of_mem_lambdaStar hS.hyp hA hA₀ hP
    (hline Q hQ (sup_comm D E ▸ hQDE)) hQAP
  rw [hQP] at hQDE
  have hsup := (mem_lambdaSet_of_le_sup hR hiso hDR hED hDR le_sup_left hPR hQDE hPD'.symm).2
  have hF₁N : Commuting F₁ (D ⊔ P) :=
    Commuting.sup_right hDF₁.symm hPF₁.1.2.2
  exact hEF₁ (hF₁N.symm.mono ((le_sup_right.trans hsup.symm.le)) le_rfl)

theorem eq_of_deltaSet_eq {C D : Subgroup G} (hC : C ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (he : deltaSet R A A₀ C = deltaSet R A A₀ D) : C = D := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hA₀ := hS.opp
  have hCR : C ∈ R := hC.1.1.1
  have hDR : D ∈ R := hD.1.1.1
  by_contra hCD
  obtain ⟨Y, hY⟩ := deltaSet_nonempty hS.hyp hA hS.sec8.2 hA₀ hD
  have hYC : Y ∈ deltaSet R A A₀ C := he ▸ hY
  have hcCD : Commuting C D := by
    rcases commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hA hC.1 hD.1 hCD with h1 | h1
    · exact h1
    · exfalso
      have hle : A ≤ Y := by
        rw [← h1.2, ← (Q_eq_M hS.hyp hY.1.1.1).2.2.1]
        exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hCR hYC.2))
          (QD.le_M (mem_lambdaSet_comm hDR hY.2))
      exact hY.1.1.2.1 (QD.eq_of_le_of_mem hR hiso hA hY.1.1.1 hle).symm
  have hDC : D ∉ lambdaSet R C := by
    intro hDC
    obtain ⟨X, hX, hDXC⟩ :=
      exists_commutator_eq_of_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hD hC hDC
    have hs : Special R D X :=
      special_of_commutator_mem_of_mem_leviSet hS.hyp hA hD hX (hDXC ▸ hCR)
    have hXC : X ∈ lambdaSet R C := by
      have := (mem_lambdaSet_commutator hR hiso hDR hX.1.1 hs).2
      rwa [hDXC] at this
    have hXD : X ∈ deltaSet R A A₀ D := he ▸ ⟨hX, hXC⟩
    exact hs.not_commuting hR hXD.2.1.2.2
  have hdag : ∀ E ∈ lambdaStar R A A₀, E ∈ lambdaSet R D → ¬ Commuting C E := by
    intro E hE hED hCE
    have hER : E ∈ R := hE.1.1.1
    obtain ⟨F, hF, hEFD, hs, hFD, -, -⟩ := hS.exists_commutator_eq_of_mem_lambdaSet hD hE hED
    have hFR : F ∈ R := hF.1.1
    have hFC : F ∈ lambdaSet R C := by
      have hFD' : F ∈ deltaSet R A A₀ D := ⟨hF, hFD⟩
      rw [← he] at hFD'
      exact hFD'.2
    obtain ⟨e, he', he1⟩ := hR.exists_ne_one hER
    have hFe : conjSub F e ≤ D ⊔ F := by
      have := conjSub_le_commutator_sup (A := F) he'
      rwa [Subgroup.commutator_comm, hEFD] at this
    have hFeF : conjSub F e ≠ F := Sec3.conjSub_ne_of_special hR hiso hER hFR hs he' he1
    have hCe : conjSub C e = C := conjSub_of_forall_commute fun c hc => (hCE c hc e he').symm
    have hCFe : conjSub F e ∈ lambdaSet R C := by
      have := conjSub_mem_lambdaSet hR (mem_lambdaSet_comm hCR hFC) e
      rw [hCe] at this
      exact mem_lambdaSet_comm (hR.conjSub_mem hFR e) this
    have hsup := (mem_lambdaSet_of_le_sup hR hiso hFR (mem_lambdaSet_comm hDR hFD) hFR le_sup_left
      (hR.conjSub_mem hFR e) (sup_comm D F ▸ hFe) hFeF.symm).2
    have hDle : D ≤ M R C := by
      calc D ≤ F ⊔ D := le_sup_right
        _ = F ⊔ conjSub F e := hsup.symm
        _ ≤ M R C := sup_le (QD.le_M hFC) (QD.le_M hCFe)
    exact hDC (mem_lambdaSet_of_le_M_of_hyp hS.hyp hCR hDR hDle fun e => hCD e.symm)
  obtain ⟨X, hX, hDX⟩ := exists_mem_leviSet_special hS.hyp hA hS.sec8.2 hA₀ hD
  obtain ⟨hE, hED', -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hD hX hDX
  set E := ⁅D, X⁆ with hEdef
  have hED : E ∈ lambdaSet R D := hED'
  have hER : E ∈ R := hE.1.1.1
  obtain ⟨P, hP, hPD, hPE, hPinf⟩ := hS.exists_mem_lambdaStar_inf_eq_bot hD hE hED
  have hPR : P ∈ R := hP.1.1.1
  set S : Set (Subgroup G) := {A, D, E, P} with hSdef
  have hSR : S ⊆ R := by
    rintro _ (rfl | rfl | rfl | rfl) <;> assumption
  have hcol : ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → Y ∈ lambdaSet R X := by
    have l1 := hD.1
    have l2 := hE.1
    have l3 := hP.1
    have l4 := mem_lambdaSet_comm hA hD.1
    have l5 := mem_lambdaSet_comm hA hE.1
    have l6 := mem_lambdaSet_comm hA hP.1
    have l7 := mem_lambdaSet_comm hDR hED
    have l8 := mem_lambdaSet_comm hDR hPD
    have l9 := mem_lambdaSet_comm hER hPE
    intro X hX Y hY hXY
    simp only [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
    rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hXY | assumption
  set T := gen S with hTdef
  have hTabel : Commuting T T := Singular.commuting_gen hS.hyp hSR hcol
  have hTcov : CoveredBy R T := Singular.coveredBy_gen hS.hyp hSR hcol
  have hTM : T ≤ M R A := Singular.gen_le_M_of_mem hcol (Set.mem_insert A _)
  have hAT : A ≤ T := le_gen (Set.mem_insert A _)
  have hDT : D ≤ T := le_gen (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hT : T = A ⊔ D ⊔ E ⊔ P := by
    rw [hTdef, hSdef, Sec5.gen_insert, Sec5.gen_insert, Sec5.gen_insert, gen_singleton']
    simp only [sup_assoc]
  have hq : Nat.card A = Nat.card D := hR.card_eq hA hDR
  obtain ⟨-, -, -, -, -, -, hline⟩ := hS.exists_commutator_eq_of_mem_lambdaSet hD hE hED
  have hpl := plane hR hiso hA hDR hED fun Z hZ hZle => (hline Z hZ (sup_comm D E ▸ hZle)).1
  have hcardT : Nat.card A ^ 4 ≤ Nat.card T := by
    rw [hT]
    calc Nat.card A ^ 4 = Nat.card ↥(A ⊔ D ⊔ E) * Nat.card P := by
          rw [hpl.2.1, hR.card_eq hPR hA]; ring
      _ ≤ Nat.card ↥(A ⊔ D ⊔ E ⊔ P) := card_mul_card_le_card_sup (by rw [inf_comm]; exact hPinf)
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
  have hcom : ∀ x ∈ T, ⁅x, c⁆ ∈ A := fun x hx => by
    rw [← (Q_eq_M hS.hyp hA).2.2.1]
    exact Subgroup.commutator_mem_commutator (hTM hx) (QD.le_M hC.1 hc)
  let f : ↥T →* ↥A :=
    { toFun := fun x => ⟨⁅(x : G), c⁆, hcom x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change ⁅(x : G) * y, c⁆ = ⁅(x : G), c⁆ * ⁅(y : G), c⁆
        rw [Plane.commutatorElement_mul_left_of_commute
          (hTabel x x.2 _ (hAT (hcom y y.2)))]
        exact (hR.commute hA (hcom y y.2) (hcom x x.2))) }
  have hker : Nat.card A ^ 3 ≤ Nat.card f.ker := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card f.range ≤ Nat.card A := Subgroup.card_le_card_group _
    have h3 : 0 < Nat.card A := Nat.card_pos
    have h4 : Nat.card A ^ 4 ≤ Nat.card f.ker * Nat.card A :=
      hcardT.trans (h1 ▸ Nat.mul_le_mul_left _ h2)
    rw [pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 h3
  have hAD : Nat.card ↥(A ⊔ D) < Nat.card A ^ 3 := by
    have h1 := card_sup_le_of_commuting (hD.1.1.2.2 : Commuting A D)
    have h2 : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
    calc Nat.card ↥(A ⊔ D) ≤ Nat.card A * Nat.card A := hq ▸ h1
      _ < Nat.card A * Nat.card A * Nat.card A :=
          lt_mul_of_one_lt_right (Nat.mul_pos (by omega) (by omega)) (by omega)
      _ = Nat.card A ^ 3 := by ring
  obtain ⟨x, hxk, hxAD⟩ : ∃ x : ↥T, x ∈ f.ker ∧ (x : G) ∉ A ⊔ D := by
    by_contra! hall
    have hle : f.ker.map T.subtype ≤ A ⊔ D := by
      rintro _ ⟨y, hy, rfl⟩
      exact hall y hy
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective T.subtype_injective] at this
    omega
  have hx1 : (x : G) ≠ 1 := fun e => hxAD (e ▸ one_mem _)
  have hxc : Commute (x : G) c := by
    have := (MonoidHom.mem_ker.1 hxk)
    have h' : ⁅(x : G), c⁆ = 1 := congrArg Subtype.val this
    exact commutatorElement_eq_one_iff_commute.1 h'
  obtain ⟨Q, hQ, hQT, hxQ⟩ := hTcov x x.2 hx1
  have hQpt : Q ∈ pts R T := ⟨hQ, hQT⟩
  have hApt : A ∈ pts R T := ⟨hA, hAT⟩
  have hDpt : D ∈ pts R T := ⟨hDR, hDT⟩
  have hQA : Q ≠ A := fun e => hxAD (Subgroup.mem_sup_left (e ▸ hxQ))
  have hQΛ : Q ∈ lambdaSet R A := Singular.mem_lambdaSet hS.hyp hSR hcol hApt hQpt hQA.symm
  have hQC : Commuting Q C := by
    have hQC' : Q ≠ C := by
      intro hQCe
      have hCpt : C ∈ pts R T := hQCe ▸ hQpt
      exact hDC (mem_lambdaSet_comm hDR
        (Singular.mem_lambdaSet hS.hyp hSR hcol hDpt hCpt fun e => hCD e.symm))
    rcases hR.rel _ hQ _ hCR hQC' with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (not_opposite_of_mem_lambdaSet hS.hyp hA hQΛ hC.1)
    · exact absurd (eq_one_of_commute_of_special hR hiso hQ hCR h1 hxQ hx1 hc hxc) hc1
  obtain ⟨P', ⟨hP'R, hP'le, hP'ψ⟩, -⟩ :=
    existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hQΛ
  have hP'A : P' ≠ A := by
    rintro rfl
    exact Special.not_opposite hR hA₀.1 hP'ψ.2 hA₀.2.symm
  have hP'pt : P' ∈ pts R T := ⟨hP'R, hP'le.trans (sup_le hAT hQT)⟩
  have hP'Λ : P' ∈ lambdaSet R A := Singular.mem_lambdaSet hS.hyp hSR hcol hApt hP'pt hP'A.symm
  have hP'D : P' ≠ D := by
    rintro rfl
    have hsup := (mem_lambdaSet_of_le_sup hR hiso hA hQΛ hA le_sup_left hP'R hP'le
      hP'A.symm).2
    exact hxAD (hsup ▸ (Subgroup.mem_sup_right hxQ : (x : G) ∈ A ⊔ Q))
  have hP'DΛ : P' ∈ lambdaSet R D := Singular.mem_lambdaSet hS.hyp hSR hcol hDpt hP'pt hP'D.symm
  have hP'C : Commuting C P' :=
    ((Commuting.sup_left hC.1.1.2.2 hQC).mono hP'le le_rfl).symm
  exact hdag P' ⟨hP'Λ, hP'ψ⟩ hP'DΛ hP'C

end Sec13

end CFSG.Timmesfeld.ARS
