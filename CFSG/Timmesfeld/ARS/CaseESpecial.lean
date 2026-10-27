module

public import CFSG.Timmesfeld.ARS.CaseENatural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem le_normalizer_of_commuting {E U : Subgroup G} (h : Commuting E U) :
    U ≤ Subgroup.normalizer (E : Set G) := fun u hu =>
  conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun e he => (h e he u hu).symm)

theorem commutator_eq_of_bruhat (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {ι κ : Type*} {U U' T : Subgroup G} {P Q : ι → Subgroup G}
    {x : κ → G} {ℓ : κ → ℕ} (hxV : ∀ k, x k ∈ levi R A A₀)
    (hB : ∀ v ∈ levi R A A₀, ∃ b ∈ T ⊔ U', ∃ k, ∃ b' ∈ T ⊔ U, v = b * x k * b')
    (hPQ : ∀ j, P j ∈ leviSet R A A₀ ∧ Q j ∈ leviSet R A A₀ ∧ Opposite (P j) (Q j))
    (hPU' : ∀ j, P j ≤ U')
    (hD : ∀ k, x k ∈ T ∨ ∃ j k', ∃ m ∈ P j ⊔ Q j, x k = m * x k' ∧ ℓ k' < ℓ k ∧
      conjSub (Q j) (x k')⁻¹ ≤ U)
    {E C : Subgroup G} (hE : E ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
    (hEU : Commuting E U) (hET : T ≤ Subgroup.normalizer (E : Set G))
    (hCU : Commuting C U') (hCT : T ≤ Subgroup.normalizer (C : Set G))
    (hnat : ∀ k j, Commuting (conjSub E (x k)) (Q j) → ¬ Commuting (conjSub E (x k)) (P j) →
      conjSub E (x k) ∈ lambdaSet R (Q j)) :
    Special R E C ∧ ⁅E, C⁆ = A := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, hcentA, hMP⟩ := Q_eq_M h hA
  have hER : E ∈ R := hE.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  have hEN : T ⊔ U ≤ Subgroup.normalizer (E : Set G) := sup_le hET (le_normalizer_of_commuting hEU)
  have hCN : T ⊔ U' ≤ Subgroup.normalizer (C : Set G) :=
    sup_le hCT (le_normalizer_of_commuting hCU)
  have key : Commuting E C → ∀ k, Commuting (conjSub E (x k)) C := by
    intro hEC k
    induction hk : ℓ k using Nat.strong_induction_on generalizing k with
    | _ N ih =>
      rcases hD k with hkT | ⟨j, k', m, hm, hxk, hlt, hQU⟩
      · rw [conjSub_eq_self_iff.2 (hET hkT)]
        exact hEC
      · have hX : Commuting (conjSub E (x k')) C := ih (ℓ k') (hk ▸ hlt) k' rfl
        obtain ⟨hPl, hQl, hPQo⟩ := hPQ j
        have hXQ : Commuting (conjSub E (x k')) (Q j) := by
          have h1 := (hEU.mono le_rfl hQU).conjSub (x k')
          rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
        have hXs : conjSub E (x k') ∈ lambdaStar R A A₀ :=
          conjSub_mem_lambdaStar_of_mem_levi hR hE (hxV k')
        have hCP : Commuting C (P j) := hCU.mono le_rfl (hPU' j)
        rw [hxk, conjSub_mul]
        by_cases hXP : Commuting (conjSub E (x k')) (P j)
        · rw [conjSub_of_forall_commute fun y hy => ((hXP.sup_right hXQ) y hy m hm).symm]
          exact hX
        · have hXl := hnat k' j hXQ hXP
          have hsX : Special R (conjSub E (x k')) (P j) :=
            special_of_not_commuting_of_mem_leviSet h hA hXs hPl hXP
          have hinv := Sec3.conjSub_sup_commutator_eq hR hiso hQl.1.1 hPl.1.1 hPQo.symm hXl
            ⟨hXs.1.1.1, hsX.symm⟩ (sup_comm (P j) (Q j) ▸ hm)
          have hNC : Commuting (conjSub E (x k') ⊔ ⁅P j, conjSub E (x k')⁆) C := by
            refine hX.sup_left (commuting_iff_commutator_eq_bot.2
              (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_))
            · rw [commuting_iff_commutator_eq_bot.1 hX, Subgroup.commutator_bot_left]
            · rw [commuting_iff_commutator_eq_bot.1 hCP, Subgroup.commutator_bot_left]
          refine hNC.mono ?_ le_rfl
          rw [← hinv]
          exact Subgroup.map_mono le_sup_left
  have hnc : ¬ Commuting E C := by
    intro hEC
    have hall : ∀ v ∈ levi R A A₀, Commuting (conjSub E v) C := by
      intro v hv
      obtain ⟨b, hb, k, b', hb', rfl⟩ := hB v hv
      rw [conjSub_mul, conjSub_mul, conjSub_eq_self_iff.2 (hEN hb')]
      have h1 := (key hEC k).conjSub b
      rwa [conjSub_eq_self_iff.2 (hCN hb)] at h1
    have hCM : Commuting C (M R A) := by
      rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
      refine gen_le fun Y hY => ?_
      obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE hY
      exact commuting_iff_le_centralizer.1 (hall v hv).symm
    have hmem : C ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hCR, hCM⟩
    rw [hcentA, Set.mem_singleton_iff] at hmem
    exact hC.1.1.2.1 hmem
  have hle : E ⊔ C ≤ M R A := sup_le (QD.le_M hE.1) (QD.le_M hC.1)
  have hs : Special R E C := by
    have hne : E ≠ C := fun e => hnc (by rw [← e]; exact hR.commuting_self hER)
    rcases hR.rel _ hER _ hCR hne with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hER hCR (hMP.to_le hle))
    · exact hs
  refine ⟨hs, Subgroup.eq_of_le_of_card_ge ?_ (hR.card_eq hA hs.1).le⟩
  rw [← hcommA]
  exact Subgroup.commutator_mono (le_sup_left.trans hle) (le_sup_right.trans hle)


section Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity

variable {K : Type*} [Group K] {A A₀ : Subgroup G} {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

theorem map_iSup_le_normalizer_of_commuting_negUnipotent (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : CompFrame R A A₀ D n H Ψ) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) :
    (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (E : Set G) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  rw [Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  have hk : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem i
  have hk' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.neg_mem _ hk
  have hkneg : ht (-Pi.single i 1 : Fin D.rank → ℤ) < 0 := by
    rw [ht_neg, ht_single]
    omega
  have hQE : Commuting E ((D.rootGroup (-Pi.single i 1)).map Ψ) :=
    hEU.mono le_rfl (map_rootGroup_le_map_negUnipotent hk' hkneg)
  have hHle : (H i).map Ψ ≤ (D.rootGroup (Pi.single i 1)).map Ψ ⊔
      (D.rootGroup (-Pi.single i 1)).map Ψ := by
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono (hF.hct.H_le i)
  rcases natural_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU i with hc | ⟨hl, hs⟩
  · exact hHle.trans ((commuting_iff_le_centralizer.1 (hc.sup_right hQE)).trans
      (Subgroup.centralizer_le_normalizer _))
  · set P := (D.rootGroup (Pi.single i 1)).map Ψ
    set Q := (D.rootGroup (-Pi.single i 1)).map Ψ
    have hPl := hF.mem _ hk
    have hQl := hF.mem _ hk'
    have hPQ : Opposite Q P := (hF.opp i).symm
    have hψ : E ∈ psiSet R P := ⟨hE.1.1.1, hs.symm⟩
    refine le_normalizer_of_conjSub_le fun t ht => ?_
    have htQP : t ∈ Q ⊔ P := sup_comm P Q ▸ hHle ht
    have hinv := Sec3.conjSub_sup_commutator_eq hR hiso hQl.1.1 hPl.1.1 hPQ hl hψ htQP
    obtain ⟨s, hs', rfl⟩ := ht
    have hQs : conjSub Q (Ψ s) = Q := by
      rw [map_conjSub_eq, (RankOne.map_conj_eq_self_iff).2
        (iSup_le_normalizer_rootGroup hF.hct hk' (le_iSup H i hs'))]
    intro y hy
    refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hQl.1.1 hPl.1.1 hPQ hl hψ ?_ ?_
    · rw [← hinv]
      exact Subgroup.map_mono le_sup_left hy
    · intro a ha
      have h1 := hQE.conjSub (Ψ s)
      rw [hQs] at h1
      exact (h1 y hy a ha).symm

theorem exists_eq_mul_mul_borel_negBorel (hct : IsCTGroupDatum
    (coxeterMatrix D.isFiniteType).toCoxeterSystem (weylAction D.isFiniteType) D.roots
    D.rootGroup n H) (hext : SteinbergExtras D n H) (g : K) :
    ∃ b ∈ (⨆ i, H i) ⊔ posUnipotent D, ∃ x ∈ weylN n H,
      ∃ b' ∈ (⨆ i, H i) ⊔ negUnipotent D, g = b * x * b' := by
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  have hn₀ := nrep_mem_weylN hct w₀
  have hconj : ∀ b ∈ borel D H,
      nrep hct w₀ * b * (nrep hct w₀)⁻¹ ∈ (⨆ i, H i) ⊔ negUnipotent D := by
    intro b hb
    rw [← SetLike.mem_coe, coe_borel hct] at hb
    obtain ⟨t, htT, u, hu, rfl⟩ := Set.mem_mul.1 hb
    rw [show nrep hct w₀ * (t * u) * (nrep hct w₀)⁻¹ =
      nrep hct w₀ * t * (nrep hct w₀)⁻¹ * (nrep hct w₀ * u * (nrep hct w₀)⁻¹) by group]
    exact mul_mem (Subgroup.mem_sup_left (conj_mem_iSup_of_mem_weylN hct hn₀ htT))
      (Subgroup.mem_sup_right (nrep_conj_mem_negUnipotent_of_forall_isRightDescent hct hw₀ hu))
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext (g * nrep hct w₀)
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hw
  refine ⟨b₁, hb₁, nrep hct w * (nrep hct w₀)⁻¹,
    mul_mem (nrep_mem_weylN hct w) (inv_mem hn₀), _, hconj b₂ hb₂, ?_⟩
  calc g = g * nrep hct w₀ * (nrep hct w₀)⁻¹ := by group
    _ = _ := by rw [he]; group

theorem exists_left_descent_of_mem_weylN (hct : IsCTGroupDatum
    (coxeterMatrix D.isFiniteType).toCoxeterSystem (weylAction D.isFiniteType) D.roots
    D.rootGroup n H) (hext : SteinbergExtras D n H) (x : weylN n H) :
    (x : K) ∈ ⨆ i, H i ∨ ∃ j, ∃ x' : weylN n H,
      ∃ m ∈ D.rootGroup (Pi.single j 1) ⊔ D.rootGroup (-Pi.single j 1), (x : K) = m * x' ∧
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hct hext x') <
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hct hext x) ∧
      (D.rootGroup (-Pi.single j 1)).map (MulAut.conj (x' : K)⁻¹).toMonoidHom ≤
        negUnipotent D := by
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  by_cases hw : weylNHom hct hext x = 1
  · left
    exact mem_iSup_of_actsAs_one hct hext x.2 (hw ▸ actsAs_weylNHom hct hext x)
  · right
    obtain ⟨j, hj⟩ := cs.exists_leftDescent_of_ne_one hw
    have hnj : n j ∈ weylN n H := n_mem_weylN j
    set x' : weylN n H := ⟨n j, hnj⟩⁻¹ * x with hx'
    have hx'w : weylNHom hct hext x' = cs.simple j * weylNHom hct hext x := by
      rw [hx', map_mul, map_inv, weylNHom_n hct hext j, CoxeterSystem.inv_simple]
    have hroot : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.neg_mem _ (Φ.single_mem j)
    refine ⟨j, x', n j, hct.n_mem j, by simp [hx'], ?_, ?_⟩
    · rw [hx'w]
      exact hj
    · have hact := (actsAs_weylNHom hct hext x').inv
      rw [hact _ hroot, hx'w]
      refine rootGroup_le_negUnipotent (weylAction_mem_roots _ _ hroot) ?_
      rw [mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply, map_neg,
        weylAction_simple_single, neg_neg]
      exact ht_weylAction_single_neg (cs.isRightDescent_inv_iff.2 hj)


theorem highest_of_commuting_negUnipotent (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : LeviFrame R A A₀ D n H Ψ) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ))
    (hnat : ∀ x ∈ weylN n H, ∀ j,
      Commuting (conjSub E (Ψ x)) ((D.rootGroup (-Pi.single j 1)).map Ψ) →
      ¬ Commuting (conjSub E (Ψ x)) ((D.rootGroup (Pi.single j 1)).map Ψ) →
      conjSub E (Ψ x) ∈ lambdaSet R ((D.rootGroup (-Pi.single j 1)).map Ψ))
    {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (hw₀ : ∀ i, (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w₀ i) :
    conjSub E (Ψ (nrep hF.hct w₀))⁻¹ ∈ lambdaStar R A A₀ ∧
      Commuting (conjSub E (Ψ (nrep hF.hct w₀))⁻¹) ((posUnipotent D).map Ψ) ∧
      (⨆ i, H i).map Ψ ≤
        Subgroup.normalizer ((conjSub E (Ψ (nrep hF.hct w₀))⁻¹ : Subgroup G) : Set G) ∧
      Special R E (conjSub E (Ψ (nrep hF.hct w₀))⁻¹) ∧
      ⁅E, conjSub E (Ψ (nrep hF.hct w₀))⁻¹⁆ = A := by
  have hR := h.root
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  set T := (⨆ i, H i).map Ψ with hTdef
  set n₀ := nrep hF.hct w₀
  have hn₀ : n₀ ∈ weylN n H := nrep_mem_weylN hF.hct w₀
  have hET : T ≤ Subgroup.normalizer (E : Set G) :=
    map_iSup_le_normalizer_of_commuting_negUnipotent h hA hAne hmax hA₀ hF.toCompFrame hE hEU
  set C := conjSub E (Ψ n₀)⁻¹ with hCdef
  have hC : C ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hE (inv_mem (hF.range n₀))
  have hCU : Commuting C ((posUnipotent D).map Ψ) := by
    have h1 := hEU.conjSub (Ψ n₀)⁻¹
    refine h1.mono le_rfl ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_conjSub, inv_inv, ← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem Ψ
      (nrep_conj_mem_negUnipotent_of_forall_isRightDescent hF.hct hw₀ hu)
  have hCT : T ≤ Subgroup.normalizer (C : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← conjSub_eq_self_iff, hCdef, ← conjSub_mul]
    have e : Ψ s * (Ψ n₀)⁻¹ = (Ψ n₀)⁻¹ * Ψ (n₀ * s * n₀⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [e, conjSub_mul, conjSub_eq_self_iff.2
      (hET (Subgroup.mem_map_of_mem Ψ (conj_mem_iSup_of_mem_weylN hF.hct hn₀ hs)))]
  have hmapsup : ∀ {y : K} {X Y : Subgroup K}, y ∈ X ⊔ Y → Ψ y ∈ X.map Ψ ⊔ Y.map Ψ :=
    fun hy => by
      rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem Ψ hy
  have hB : ∀ v ∈ levi R A A₀, ∃ b ∈ T ⊔ (posUnipotent D).map Ψ, ∃ y : weylN n H,
      ∃ b' ∈ T ⊔ (negUnipotent D).map Ψ, v = b * Ψ y * b' := by
    intro v hv
    obtain ⟨g, rfl⟩ := hF.surj v hv
    obtain ⟨b, hb, y, hy, b', hb', rfl⟩ := exists_eq_mul_mul_borel_negBorel hF.hct hF.hext g
    exact ⟨Ψ b, hmapsup hb, ⟨y, hy⟩, Ψ b', hmapsup hb', by simp only [map_mul]⟩
  have hPQ : ∀ j, (D.rootGroup (Pi.single j 1)).map Ψ ∈ leviSet R A A₀ ∧
      (D.rootGroup (-Pi.single j 1)).map Ψ ∈ leviSet R A A₀ ∧
      Opposite ((D.rootGroup (Pi.single j 1)).map Ψ) ((D.rootGroup (-Pi.single j 1)).map Ψ) := by
    intro j
    have hk : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem j
    exact ⟨hF.mem _ hk, hF.mem _ (Φ.neg_mem _ hk), hF.opp j⟩
  have hPU : ∀ j, (D.rootGroup (Pi.single j 1)).map Ψ ≤ (posUnipotent D).map Ψ := fun j =>
    Subgroup.map_mono (rootGroup_le_posUnipotent (Φ.single_mem j) (ht_single_pos j))
  have hD : ∀ y : weylN n H, Ψ y ∈ T ∨ ∃ j, ∃ y' : weylN n H,
      ∃ m ∈ (D.rootGroup (Pi.single j 1)).map Ψ ⊔ (D.rootGroup (-Pi.single j 1)).map Ψ,
      Ψ y = m * Ψ y' ∧
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hF.hct hF.hext y') <
        (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (weylNHom hF.hct hF.hext y) ∧
      conjSub ((D.rootGroup (-Pi.single j 1)).map Ψ) (Ψ y')⁻¹ ≤ (negUnipotent D).map Ψ := by
    intro y
    rcases exists_left_descent_of_mem_weylN hF.hct hF.hext y with hy | ⟨j, y', m, hm, hyy, hlt, hle⟩
    · exact Or.inl (Subgroup.mem_map_of_mem Ψ hy)
    · refine Or.inr ⟨j, y', Ψ m, hmapsup hm, by simp only [hyy, map_mul], hlt, ?_⟩
      rw [← map_inv, map_conjSub_eq]
      exact Subgroup.map_mono hle
  obtain ⟨hs, hEC⟩ := commutator_eq_of_bruhat h hA hAne hmax hA₀
    (fun y : weylN n H => hF.range y) hB hPQ hPU hD hE hC hEU hET hCU hCT
    (fun y j h1 h2 => hnat y y.2 j h1 h2)
  exact ⟨hC, hCU, hCT, hs, hEC⟩

theorem exists_highest_of_commuting_negUnipotent (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : LeviFrame R A A₀ D n H Ψ) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ))
    (hnat : ∀ x ∈ weylN n H, ∀ j,
      Commuting (conjSub E (Ψ x)) ((D.rootGroup (-Pi.single j 1)).map Ψ) →
      ¬ Commuting (conjSub E (Ψ x)) ((D.rootGroup (Pi.single j 1)).map Ψ) →
      conjSub E (Ψ x) ∈ lambdaSet R ((D.rootGroup (-Pi.single j 1)).map Ψ)) :
    ∃ C ∈ lambdaStar R A A₀, Commuting C ((posUnipotent D).map Ψ) ∧
      (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (C : Set G) ∧ Special R E C ∧ ⁅E, C⁆ = A := by
  obtain ⟨w₀, hw₀⟩ := exists_forall_isRightDescent (D := D)
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    highest_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU hnat hw₀
  exact ⟨_, h1, h2, h3, h4, h5⟩

end Steinberg

end CFSG.Timmesfeld.ARS
