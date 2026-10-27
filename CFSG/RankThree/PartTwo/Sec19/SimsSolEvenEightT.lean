module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightBar

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Eight

theorem supp2_indVec {n : ℕ} (I : Finset (Fin n)) : supp2 (indVec I) = I := by
  ext i
  rw [mem_supp2]
  by_cases hi : i ∈ I <;> simp [indVec, hi]

theorem card_compl_eight {I : Finset (Fin 8)} (hI : I.card = 4) : Iᶜ.card = 4 := by
  rw [Finset.card_compl, Fintype.card_fin, hI]

theorem klein8_mul_self {d : ℕ} {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {σ : Perm (Fin d)} (hσ : σ ∈ klein8 I) : σ * σ = 1 := by
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 hσ
  have hc := (klein4_disjoint hI hIc h₁ h₂).commute
  calc σ₁ * σ₂ * (σ₁ * σ₂) = σ₁ * (σ₂ * σ₁) * σ₂ := by group
    _ = σ₁ * (σ₁ * σ₂) * σ₂ := by rw [hc.eq]
    _ = (σ₁ * σ₁) * (σ₂ * σ₂) := by group
    _ = 1 := by rw [klein4_mul_self hI h₁, klein4_mul_self hIc h₂, one_mul]

section Generic

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} {C : Cfg G M X n}
  (D : C.PiData)

theorem barAct_barInd_of_mem_setStab {I : Finset (Fin n)} {τ : Perm (Fin n)}
    (hτ : τ ∈ setStab I) : barAct τ (barInd I) = barInd I := by
  rw [barAct_barInd, (image_eq_iff_mem_setStab τ I).2 hτ]

theorem altOn_le_theta_CMOf {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin n)}
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {S : Finset (Fin n)}
    (hS : S = I ∨ S = Iᶜ) : altOn S ≤ ((CMOf M x).subgroupOf M).map C.θ := by
  refine altOn_le_of_threeCycles S _ fun τ hτ hsupp => ?_
  have hτS : τ ∈ altOn S := mem_altOn.2 ⟨hsupp, hτ.sign⟩
  have hτst : τ ∈ setStab S := altOn_le_setStab S hτS
  have hτI : τ ∈ setStab I := by
    rcases hS with rfl | rfl
    · exact hτst
    · exact setStab_compl_le I hτst
  have hfix : barAct τ (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) =
      Multiplicative.toAdd (D.piQ ⟨x, hx⟩) := by
    rw [hπ]
    exact barAct_barInd_of_mem_setStab hτI
  obtain ⟨y, hyθ, hyc⟩ := D.exists_comm_lift ⟨x, hx⟩ hτ hfix
  have hyM : (y : G) ∈ M := C.S.le y.2
  refine Subgroup.mem_map.2 ⟨⟨(y : G), hyM⟩, ?_, hyθ⟩
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.mem_inf.2 ⟨hyM, mem_centralizer_zpowers_iff.2 (mul_inv_eq_iff_eq_mul.2 hyc)⟩

theorem theta_stab_or_swap {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin n)}
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {k : ↥M} (hk : (k : G) ∈ CMOf M x) :
    C.θ k ∈ setStab I ∨ ∀ y, C.θ k y ∈ I ↔ y ∉ I := by
  have hc : (k : G) * x * (k : G)⁻¹ = x := mem_centralizer_zpowers_iff.1 (Subgroup.mem_inf.1 hk).2
  have h := D.piQ_conj k ⟨x, hx⟩ ⟨x, hx⟩ hc.symm
  rw [hπ] at h
  have h' := stab_or_swap_of_barAct_eq (indVec I) h.symm
  rwa [supp2_indVec] at h'

theorem thetaN_normalized {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin n)}
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {S : Finset (Fin n)}
    (hS : S = I ∨ S = Iᶜ) : ∀ τ ∈ altOn S, ∀ σ ∈ C.thetaN x, τ * σ * τ⁻¹ ∈ C.thetaN x := by
  intro τ hτ σ hσ
  obtain ⟨c, hcC, hcθ⟩ := Subgroup.mem_map.1 (altOn_le_theta_CMOf D hx hπ hS hτ)
  obtain ⟨t, htT, rfl⟩ := C.mem_thetaN.1 hσ
  have hcC' : (c : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hcC
  have hcmT : (c : G) * (t : G) * (c : G)⁻¹ ∈ TOf M x := normalized_TOf M x hcC' htT
  refine C.mem_thetaN.2 ⟨⟨(c : G) * t * (c : G)⁻¹, TOf_le_M M x hcmT⟩, hcmT, ?_⟩
  have : (⟨(c : G) * (t : G) * (c : G)⁻¹, TOf_le_M M x hcmT⟩ : ↥M) = c * t * c⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hcθ]

end Generic

section Eight

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 8} (D : C.PiData)

theorem thetaN_le_setStab {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)}
    (hI : I.card = 4) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    C.thetaN x ≤ setStab I := by
  intro σ hσ
  obtain ⟨t, htT, rfl⟩ := C.mem_thetaN.1 hσ
  rcases theta_stab_or_swap D hx hπ (TOf_le_C M x htT) with h | h
  · exact h
  · exact (not_swap_of_normalized (by omega) (C.isPGroup_thetaN x)
      (thetaN_normalized D hx hπ (Or.inl rfl)) (C.mem_thetaN.2 ⟨t, htT, rfl⟩) h).elim

theorem card_thetaN_le {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)}
    (hI : I.card = 4) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    Nat.card (C.thetaN x) ≤ 16 :=
  card_le_sixteen hI (card_compl_eight hI) (C.isPGroup_thetaN x) (thetaN_le_setStab D hx hI hπ)
    (thetaN_normalized D hx hπ (Or.inl rfl)) (thetaN_normalized D hx hπ (Or.inr rfl))

theorem klein8_le_thetaN (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : klein8 I ≤ C.thetaN x := by
  classical
  have hIc := card_compl_eight hI
  set Lam : Subgroup G := CMOf M x ⊓ ((klein8 I).comap C.θ).map M.subtype with hLam
  have hmemLam : ∀ g : G, g ∈ Lam ↔
      g ∈ CMOf M x ∧ ∃ hg : g ∈ M, C.θ ⟨g, hg⟩ ∈ klein8 I := by
    intro g
    rw [hLam, Subgroup.mem_inf]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hLamC : Lam ≤ CMOf M x := inf_le_left
  have hnorm : ∀ k ∈ CMOf M x, ∀ u ∈ Lam, k * u * k⁻¹ ∈ Lam := by
    intro k hk u hu
    obtain ⟨huC, huM, huθ⟩ := (hmemLam u).1 hu
    have hkM : k ∈ M := (Subgroup.mem_inf.1 hk).1
    have hkuM : k * u * k⁻¹ ∈ M := M.mul_mem (M.mul_mem hkM huM) (M.inv_mem hkM)
    refine (hmemLam _).2 ⟨(CMOf M x).mul_mem ((CMOf M x).mul_mem hk huC) ((CMOf M x).inv_mem hk),
      hkuM, ?_⟩
    have e : (⟨k * u * k⁻¹, hkuM⟩ : ↥M) = ⟨k, hkM⟩ * ⟨u, huM⟩ * ⟨k, hkM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact klein8_conj_mem hI hIc (theta_stab_or_swap D hx hπ (k := ⟨k, hkM⟩) hk) huθ
  have hLam2 : IsPGroup 2 Lam := by
    refine isPGroup_two_of_forall fun u hu => ?_
    obtain ⟨huC, huM, huθ⟩ := (hmemLam u).1 hu
    have hsq := klein8_mul_self hI hIc huθ
    have hK : u * u ∈ C.K := by
      refine C.mem_K.2 ⟨M.mul_mem huM huM, ?_⟩
      have e : (⟨u * u, M.mul_mem huM huM⟩ : ↥M) = ⟨u, huM⟩ * ⟨u, huM⟩ := rfl
      rw [e, map_mul, hsq]
    rw [C.K_eq_Q hR] at hK
    obtain ⟨j, hj⟩ := exists_two_pow_of_mem_pCoreOf M hK
    refine ⟨j + 1, ?_⟩
    rw [pow_succ, mul_comm, pow_mul, pow_two]
    exact hj
  have hLamT : Lam ≤ TOf M x := le_pCoreOf_of_normalized hLamC hnorm hLam2
  intro σ hσ
  obtain ⟨σ₁, h₁, σ₂, h₂, rfl⟩ := (mem_klein8_iff hI hIc).1 hσ
  obtain ⟨c₁, hc₁C, hc₁θ⟩ := Subgroup.mem_map.1
    (altOn_le_theta_CMOf D hx hπ (Or.inl rfl) (klein4_le_altOn hI h₁))
  obtain ⟨c₂, hc₂C, hc₂θ⟩ := Subgroup.mem_map.1
    (altOn_le_theta_CMOf D hx hπ (Or.inr rfl) (klein4_le_altOn hIc h₂))
  have hc₁C' : (c₁ : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hc₁C
  have hc₂C' : (c₂ : G) ∈ CMOf M x := Subgroup.mem_subgroupOf.1 hc₂C
  have hθ : C.θ (c₁ * c₂) = σ₁ * σ₂ := by rw [map_mul, hc₁θ, hc₂θ]
  have hcLam : ((c₁ * c₂ : ↥M) : G) ∈ Lam := (hmemLam _).2
    ⟨(CMOf M x).mul_mem hc₁C' hc₂C', (c₁ * c₂).2, by
      show C.θ (c₁ * c₂) ∈ klein8 I
      rw [hθ]
      exact hσ⟩
  exact C.mem_thetaN.2 ⟨c₁ * c₂, hLamT hcLam, hθ⟩

theorem theta_TOf_eq (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    ((TOf M x).subgroupOf M).map C.θ = klein8 I :=
  (Subgroup.eq_of_le_of_card_ge (klein8_le_thetaN D hR hx hI hπ)
    (by rw [card_klein8 hI (card_compl_eight hI)]; exact card_thetaN_le D hx hI hπ)).symm

theorem elem_le (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {E : Subgroup G} (hET : E ≤ TOf M x)
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card ↥E ≤ Nat.card ↥C.qB ∧ (Nat.card ↥E = Nat.card ↥C.qB → E = C.qB) := by
  classical
  have hQ := C.Q_comm hR
  have hEM : E ≤ M := hET.trans (TOf_le_M M x)
  have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by rw [← pow_two]; exact hE.2 e he
  have hcardE := C.card_eq_card_inf_mul hR hEM
  by_cases hbot : (E.subgroupOf M).map C.θ = ⊥
  · rw [hbot, Subgroup.card_bot, mul_one] at hcardE
    have hEQ : E ⊓ CFSG.Open.pCoreOf 2 M = E :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ CFSG.Open.pCoreOf 2 M ≤ E) hcardE.le
    have hEle : E ≤ CFSG.Open.pCoreOf 2 M := hEQ ▸ inf_le_right
    have hEB : E ≤ C.qB := fun e he => (C.mem_qB_iff hQ).2 ⟨hEle he, hEsq e he⟩
    exact ⟨Subgroup.card_le_of_le hEB, fun h => Subgroup.eq_of_le_of_card_ge hEB h.symm.le⟩
  · set F : Subgroup (Perm (Fin 8)) := (E.subgroupOf M).map C.θ with hF
    have hFN : F ≤ klein8 I := by
      rw [← theta_TOf_eq D hR hx hI hπ]
      exact Subgroup.map_mono (fun m hm => hET hm)
    have hqBQ : C.qB ≤ CFSG.Open.pCoreOf 2 M := C.qB_le_Q
    set A : Subgroup (Multiplicative (permBar 8)) :=
      (C.qB.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ with hA
    set Zg : Subgroup G := C.qB ⊓ Subgroup.centralizer (E : Set G) with hZg
    set Zp : Subgroup (Multiplicative (permBar 8)) :=
      (Zg.subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ with hZp
    have hZgQ : Zg ≤ CFSG.Open.pCoreOf 2 M := inf_le_left.trans hqBQ
    have hAU : ∀ u : altHeart 8, Multiplicative.ofAdd (heartToBar u) ∈ A :=
      D.heart_mem_piQ_qB hQ
    have hZpA : Zp ≤ A := by
      rintro z ⟨q, hq, rfl⟩
      exact ⟨q, Subgroup.mem_subgroupOf.2
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).1, rfl⟩
    have hZpfix : ∀ z ∈ Zp, ∀ σ ∈ F,
        barAct σ (Multiplicative.toAdd z) = Multiplicative.toAdd z := by
      rintro z ⟨q, hq, rfl⟩ σ ⟨m, hm, rfl⟩
      have hqE : (q : G) ∈ Subgroup.centralizer (E : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hq)).2
      have hmE : (m : G) ∈ E := hm
      have hc : (m : G) * (q : G) = (q : G) * (m : G) :=
        Subgroup.mem_centralizer_iff.1 hqE (m : G) hmE
      have := D.piQ_conj m q q (by rw [Subgroup.coe_inv, hc]; group)
      exact this.symm
    have hlt := card_mul_card_lt hI (card_compl_eight hI) hFN hbot hAU hZpA hZpfix
    have hcardZ := D.card_eq_card_inf_R_mul hZgQ
    have hcardB := D.card_eq_card_inf_R_mul hqBQ
    have hRB : C.qB ⊓ Rc X = Rc X := inf_eq_right.2 (C.Rc_le_qB hQ hR)
    rw [hRB] at hcardB
    have hZR : Nat.card ↥(Zg ⊓ Rc X) ≤ Nat.card ↥(Rc X) := Subgroup.card_le_of_le inf_le_right
    have hEZ : E ⊓ CFSG.Open.pCoreOf 2 M ≤ Zg := by
      intro e he
      obtain ⟨heE, heQ⟩ := Subgroup.mem_inf.1 he
      refine Subgroup.mem_inf.2 ⟨(C.mem_qB_iff hQ).2 ⟨heQ, hEsq e heE⟩,
        Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨h, hh⟩ ⟨e, heE⟩)
    have hEZc : Nat.card ↥(E ⊓ CFSG.Open.pCoreOf 2 M) ≤ Nat.card Zg := Subgroup.card_le_of_le hEZ
    have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
    have hlt' : Nat.card ↥E < Nat.card ↥C.qB := by
      rw [hcardE, hcardB]
      calc Nat.card ↥(E ⊓ CFSG.Open.pCoreOf 2 M) * Nat.card F
          ≤ Nat.card Zg * Nat.card F := Nat.mul_le_mul_right _ hEZc
        _ = (Nat.card ↥(Zg ⊓ Rc X) * Nat.card Zp) * Nat.card F := by rw [hcardZ]
        _ ≤ (Nat.card ↥(Rc X) * Nat.card Zp) * Nat.card F :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hZR)
        _ = Nat.card ↥(Rc X) * (Nat.card Zp * Nat.card F) := by ring
        _ < Nat.card ↥(Rc X) * Nat.card A := Nat.mul_lt_mul_of_pos_left hlt hRpos
    exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

theorem conj_qB_eq_of_le_TOf (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {g : G}
    (hg : conjSubgroup g C.qB ≤ TOf M x) : conjSubgroup g C.qB = C.qB := by
  obtain ⟨-, hEq⟩ := elem_le D hR hx hI hπ hg
    (isElemAbelian_conjSubgroup (C.isElemAbelian_qB (C.Q_comm hR)) g)
  exact hEq (Subgroup.card_map_of_injective (MulAut.conj g).injective)

theorem mem_M_of_conj_qB_le_TOf (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {g : G}
    (hg : conjSubgroup g C.qB ≤ TOf M x) : g ∈ M := by
  have h := conj_qB_eq_of_le_TOf D hR hx hI hπ hg
  have hn : g⁻¹ ∈ Subgroup.normalizer ((C.qB : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    have key := mem_conjSubgroup (g := g) (T := C.qB) (x := b)
    rw [h] at key
    simpa using key
  have := (C.normalizer_qB_eq hR).le hn
  simpa using M.inv_mem this

theorem normalizer_le_M_of_qB_le (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {P : Subgroup G} (hBP : C.qB ≤ P)
    (hPT : P ≤ TOf M x) : Subgroup.normalizer (P : Set G) ≤ M := by
  intro g hg
  refine mem_M_of_conj_qB_le_TOf D hR hx hI hπ fun e he => ?_
  have he' : g⁻¹ * e * g ∈ C.qB := mem_conjSubgroup.1 he
  have h2 := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * e * g)).1 (hBP he')
  have : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
  rw [this] at h2
  exact hPT h2

theorem normalizer_TOf_le_M (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    Subgroup.normalizer ((TOf M x : Subgroup G) : Set G) ≤ M :=
  normalizer_le_M_of_qB_le D hR hx hI hπ
    (C.qB_le_Q.trans (Q_le_TOf (C.Q_comm hR) hx)) le_rfl

end Eight

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
