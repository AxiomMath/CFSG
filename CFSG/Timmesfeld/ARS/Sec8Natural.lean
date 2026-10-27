module

public import CFSG.Timmesfeld.ARS.Sec8Levi

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem commutator_le_of_le_normalizer {H K M' : Subgroup G} (hH : H ≤ M')
    (hK : K ≤ Subgroup.normalizer (M' : Set G)) : ⁅H, K⁆ ≤ M' := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ M' :=
    (Subgroup.mem_normalizer_iff.1 (hK hy) x⁻¹).1 (M'.inv_mem (hH hx))
  rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact M'.mul_mem (hH hx) h1

theorem le_normalizer_of_commutator_le {N M' : Subgroup G} (hNM : N ≤ M') (h : ⁅M', M'⁆ ≤ N) :
    M' ≤ Subgroup.normalizer (N : Set G) := by
  refine le_normalizer_of_conjSub_le fun x hx => ?_
  rintro _ ⟨n, hn, rfl⟩
  change x * n * x⁻¹ ∈ N
  rw [conj_eq_commutator_mul]
  exact N.mul_mem (h (Subgroup.commutator_mem_commutator hx (hNM hn))) hn

theorem exists_opposite_of_mem_lambdaStar (h : Hyp G R) {A A₀ C F : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) (hC : C ∈ leviSet R A A₀)
    (hF : F ∈ lambdaStar R A A₀) (hFC : Special R F C) :
    (∀ P ∈ R, P ≤ F ⊔ ⁅F, C⁆ → P ∈ lambdaStar R A A₀) ∧
      ∃ D ∈ leviSet R A A₀, Opposite C D ∧ F ∈ lambdaSet R D := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hFl, hFψ⟩ := hF
  have hFR : F ∈ R := hFl.1.1
  have hCR : C ∈ R := hC.1.1
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  set F₁ := ⁅F, C⁆ with hF₁
  have hF₁R : F₁ ∈ R := hFC.1
  obtain ⟨hFF₁, hCF₁⟩ := mem_lambdaSet_commutator hR hiso hFR hCR hFC
  have hF₁Fl : F₁ ∈ lambdaSet R F := mem_lambdaSet_comm hF₁R hFF₁
  have hFF₁ne : F ≠ F₁ := hFF₁.1.2.1
  have hCnl : C ∉ lambdaSet R A := fun hCl =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hCl hC.2.2.2
  have hCN : C ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) :=
    QD.le_normalizer_M hR hA ⟨hCR, hC.1.2.2⟩
  have hF₁A : F₁ ∈ lambdaSet R A := by
    have hmem : F₁ ∈ {X | X ∈ R ∧ X ≤ M R A} :=
      ⟨hF₁R, commutator_le_of_le_normalizer (QD.le_M hFl) hCN⟩
    rw [(Q_eq_M h hA).2.1] at hmem
    exact hmem.resolve_left fun e => hCnl (e ▸ hCF₁)
  have hF₁ψ : F₁ ∈ psiSet R A₀ := by
    have hnc : ¬ Commuting A₀ F₁ :=
      not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hF₁A
    have hP : IsPGroup 2 ↥(A₀ ⊔ F ⊔ C) :=
      isPGroup_sup_of_special_special hR hiso hA₀.1 hFR hCR hFψ.2 hFC hC.2.2.2
    have hno : ¬ Opposite A₀ F₁ := Sec3.not_opposite_of_isPGroup_sup hR hA₀.1 hF₁R
      (hP.to_le (sup_le (le_sup_left.trans le_sup_left)
        (QD.commutator_le_of_le (le_sup_right.trans le_sup_left) le_sup_right)))
    rcases hR.rel A₀ hA₀.1 F₁ hF₁R (fun e => hnc (e ▸ hR.commuting_self hA₀.1)) with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho hno
    · exact ⟨hF₁R, hs⟩
  have hline : ∀ P ∈ R, P ≤ F ⊔ F₁ → P ∈ lambdaStar R A A₀ := by
    intro P hP hPle
    by_cases hPF₁ : P = F₁
    · rw [hPF₁]
      exact ⟨hF₁A, hF₁ψ⟩
    obtain ⟨c, hc, rfl⟩ :=
      QD.exists_eq_conjSub_of_le_sup hR hiso hFR hCR hFC hP (hPle.trans (sup_comm _ _).le) hPF₁
    have hcA : conjSub A c = A :=
      conjSub_of_forall_commute fun a ha => (hC.1.2.2 a ha c hc).symm
    have hcA₀ : conjSub A₀ c = A₀ :=
      conjSub_of_forall_commute fun a ha => (hC.2.2.2 a ha c hc).symm
    refine ⟨?_, hR.conjSub_mem hFR c, ?_⟩
    · have := conjSub_mem_lambdaSet hR hFl c
      rwa [hcA] at this
    · have := Sec3.special_conjSub hR hFψ.2 c
      rwa [hcA₀] at this
  refine ⟨hline, ?_⟩
  have hplA : ∀ D ∈ R, D ≤ F ⊔ F₁ → D ∈ lambdaSet R A := fun D hD hDle => (hline D hD hDle).1
  obtain ⟨-, -, -, -, hcoll, -⟩ := plane hR hiso hA hFR hF₁Fl hplA
  obtain ⟨-, -, htrans⟩ := plane_transitive hR hiso hA hFR hF₁Fl hplA
  set N := A ⊔ F ⊔ F₁ with hN
  have hAN : A ≤ N := le_sup_left.trans le_sup_left
  have hFN : F ≤ N := le_sup_right.trans le_sup_left
  have hF₁N : F₁ ≤ N := le_sup_right
  have hFA : F ≠ A := hFl.1.2.1
  obtain ⟨T, hTR, hT⟩ := htrans F hFR A hA hFN hAN hFA
  have hTA : Commuting A T := hT.2.2.1.mono le_sup_right le_rfl
  obtain ⟨P', hP'R, hP'le, hP'F₁, hP'F⟩ := exists_mem_le_sup_ne_ne hR hiso hF₁R hFF₁ F₁ F
  have hF₁L : ¬ F₁ ≤ F ⊔ A := by
    intro hle
    have h1 := (mem_lambdaSet_of_le_sup hR hiso hA hFl hFR le_sup_right hF₁R
      (hle.trans (sup_comm F A).le) hFF₁ne).2
    exact (hline A hA (le_sup_left.trans h1.symm.le)).1.1.2.1 rfl
  obtain ⟨t, ht, hF₁t⟩ := hT.2.2.2 F₁ hF₁R hF₁N hF₁L P' hP'R hP'le hP'F
  have htF₁ : conjSub F₁ t ≠ F₁ := hF₁t ▸ hP'F₁
  have hTne : T ≠ A := by
    intro e
    rw [e] at ht
    exact htF₁ (conjSub_of_forall_commute fun x hx => hF₁A.1.2.2 t ht x hx)
  have hNM : N ≤ M R A := sup_le (sup_le QD.le_M_self (QD.le_M hFl)) (QD.le_M hF₁A)
  have hTnl : T ∉ lambdaSet R A := by
    intro hTl
    refine htF₁ (conjSub_of_forall_commute fun x hx => ?_)
    have h1 : ⁅x, t⁆ ∈ A ⊓ F :=
      ⟨hcommA ▸ Subgroup.commutator_mem_commutator (hNM (hF₁N hx)) (QD.le_M hTl ht),
        hT.2.1 t ht x (hF₁N hx)⟩
    rw [inf_eq_bot hR hiso hA hFR hFA.symm, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  obtain ⟨m, hm, hTm⟩ := exists_mem_M_conjSub_mem_leviSet h hA hAne hA₀ ⟨hTR, hTne, hTA⟩ hTnl
  set D := conjSub T m with hD
  have hDR : D ∈ R := hTm.1.1
  have hMnorm : ∀ {X : Subgroup G}, A ≤ X → X ≤ M R A → conjSub X m = X := fun hAX hXM =>
    conjSub_eq_self_iff.2 (le_normalizer_of_commutator_le hXM (hcommA.le.trans hAX) hm)
  have hmN : conjSub N m = N := hMnorm hAN hNM
  have hDel := hT.conj hR hmN
  rw [hMnorm (X := F ⊔ A) le_sup_right (sup_le (QD.le_M hFl) QD.le_M_self)] at hDel
  have hDFA : Commuting (F ⊔ A) D := hDel.2.2.1
  have hDF : Commuting F D := hDFA.mono le_sup_left le_rfl
  have hDA : Commuting A D := hDFA.mono le_sup_right le_rfl
  have hDA₀ : Commuting A₀ D := hTm.2.2.2
  have hNψ : ∀ Y ∈ R, Y ≤ N → Special R A₀ Y → Y ≤ F ⊔ F₁ := by
    intro Y hY hYN hYψ
    have hYA : Y ≠ A := fun e => Special.not_opposite hR hA₀.1 hYψ (e ▸ hA₀.2.symm)
    have hYl : Y ∈ lambdaSet R A := hcoll A hA hAN Y hY hYN hYA.symm
    obtain ⟨D', hD'R, hD'le₁, hD'le₂⟩ := Plane.exists_le_sup_le_sup hR hiso hA hFR hF₁Fl hplA
      hA hAN hY hYN hYA.symm hFR hFN hF₁R hF₁N hFF₁ne
    obtain ⟨X, -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hYl
    rw [(huniq Y ⟨hY, le_sup_right, hY, hYψ⟩).trans
      (huniq D' ⟨hD'R, hD'le₁, (hline D' hD'R hD'le₂).2⟩).symm]
    exact hD'le₂
  have hDnorm : D ≤ Subgroup.normalizer ((F ⊔ F₁ : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun d hd => ?_
    have hF₁d : conjSub F₁ d ≤ F ⊔ F₁ := by
      refine hNψ _ (hR.conjSub_mem hF₁R d) (hDel.1 d hd ▸ Subgroup.map_mono hF₁N) ?_
      have := Sec3.special_conjSub hR hF₁ψ.2 d
      rwa [conjSub_of_forall_commute fun a ha => (hDA₀ a ha d hd).symm] at this
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun f hf => (hDF f hf d hd).symm]
    exact sup_le le_sup_left hF₁d
  have hDF₁ : ¬ Commuting D F₁ := by
    intro hc
    have hDN : Commuting D N := Commuting.sup_right (Commuting.sup_right hDA.symm hDF.symm) hc
    have hTm' : conjSub D m⁻¹ = T := by rw [hD, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hNm' : conjSub N m⁻¹ = N := by
      conv_lhs => rw [← hmN]
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    have h1 := hDN.conjSub m⁻¹
    rw [hTm', hNm'] at h1
    exact htF₁ (conjSub_of_forall_commute fun x hx => h1 t ht x (hF₁N hx))
  have hF₁D : Special R F₁ D := by
    rcases hR.rel F₁ hF₁R D hDR (fun e => hDF₁ (e ▸ hR.commuting_self hF₁R)) with hc | ho | hs
    · exact absurd hc.symm hDF₁
    · exact absurd hDA.symm
        (not_commuting_of_opposite_of_mem_lambdaSet hR hDR ho.symm (mem_lambdaSet_comm hA hF₁A))
    · exact hs
  have hWF : ⁅F₁, D⁆ = F := by
    have hWle : ⁅F₁, D⁆ ≤ F ⊔ F₁ := commutator_le_of_le_normalizer le_sup_right hDnorm
    by_contra hne
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hFR hF₁Fl hFR le_sup_left hF₁D.1 hWle
      (Ne.symm hne)
    exact hDF₁ ((hsup ▸ Commuting.sup_right hDF.symm hF₁D.2.2.symm).mono le_rfl le_sup_right)
  have hDFl : D ∈ lambdaSet R F :=
    mem_lambdaSet_of_commutator_eq hR hiso hFR hDR hF₁R (by rw [Subgroup.commutator_comm, hWF])
  refine ⟨D, hTm, ?_, mem_lambdaSet_comm hFR hDFl⟩
  have hCnorm : C ≤ Subgroup.normalizer ((F ⊔ F₁ : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun c hc => ?_
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun x hx => (hCF₁.1.2.2 x hx c hc).symm]
    exact sup_le ((conjSub_le_commutator_sup hc).trans (sup_comm _ _).le) le_sup_right
  have hthree : ∀ W : Subgroup G, ⁅C, D⁆ ≤ W → Commuting W F → False := by
    intro W hW hWF'
    have h1 : ⁅⁅F, C⁆, D⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · exact le_bot_iff.1 ((Subgroup.commutator_mono hW le_rfl).trans
          (commuting_iff_commutator_eq_bot.1 hWF').le)
      · rw [Subgroup.commutator_comm D F, commuting_iff_commutator_eq_bot.1 hDF,
          Subgroup.commutator_bot_left]
    have h2 : ⁅F₁, D⁆ = ⊥ := h1
    rw [hWF] at h2
    exact hR.ne_bot F hFR h2
  have hCD : C ≠ D := fun e => Special.not_commuting hR hFC (e ▸ hDF)
  rcases hR.rel C hCR D hDR hCD with hc | ho | hs
  · exfalso
    refine hthree ⊥ (commuting_iff_commutator_eq_bot.1 hc).le fun x hx f _ => ?_
    rw [Subgroup.mem_bot.1 hx]
    exact Commute.one_left f
  · exact ho
  · exfalso
    set W := ⁅C, D⁆ with hW
    have hWR : W ∈ R := hs.1
    have hWnorm : W ≤ Subgroup.normalizer ((F ⊔ F₁ : Subgroup G) : Set G) :=
      (QD.commutator_le_of_le le_sup_left le_sup_right).trans (sup_le hCnorm hDnorm)
    have huniq : ∀ {X P : Subgroup G}, P ∈ R → P ≤ F ⊔ F₁ → Commuting P X →
        ¬ Commuting (F ⊔ F₁) X → ∀ w ∈ W, (∀ x ∈ X, Commute w x) → conjSub P w = P := by
      intro X P hP hPle hPX hLX w hw hwX
      have hPw : conjSub P w ≤ F ⊔ F₁ := by
        rw [← conjSub_eq_self_iff.2 (hWnorm hw)]
        exact Subgroup.map_mono hPle
      have hPwX : Commuting (conjSub P w) X := by
        have := hPX.conjSub w
        rwa [conjSub_of_forall_commute hwX] at this
      by_contra hne
      obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hFR hF₁Fl hP hPle
        (hR.conjSub_mem hP w) hPw (Ne.symm hne)
      exact hLX (hsup ▸ Commuting.sup_left hPX hPwX)
    have hWF' : Commuting W F :=
      Sec3.commuting_of_forall_conjSub_eq hR hWR hFR (fun w hw => huniq hFR le_sup_left hDF
        (fun hLD => hDF₁ (hLD.mono le_sup_right le_rfl).symm) w hw fun x hx => hs.2.2 w hw x hx)
        hiso
    exact hthree W le_rfl hWF'

end CFSG.Timmesfeld.ARS
