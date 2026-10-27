module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightT
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightQ0

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Eight

section Generic

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} {C : Cfg G M X n}
  (D : C.PiData)

theorem piQ_injective (hrbot : Rc X = ⊥) : Function.Injective D.piQ := by
  intro a b h
  have h1 : D.piQ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (D.piQ_eq_one_iff _).1 h1
  rw [hrbot, Subgroup.mem_bot] at h2
  have h3 : (a : G)⁻¹ * (b : G) = 1 := h2
  exact Subtype.ext (inv_mul_eq_one.1 h3)

theorem exists_piQ_eq_uvec (a b : Fin n) :
    ∃ q : ↥(CFSG.Open.pCoreOf 2 M), Multiplicative.toAdd (D.piQ q) = uvec a b := by
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd (pairEW a b : altHeart n))
  refine ⟨⟨(w : G), C.S.W_le_Q w.2⟩, ?_⟩
  rw [D.piQ_W w _ rfl, hw, toAdd_ofAdd, heartToBar_pairEW_eq_uvec]

theorem exists_piQ_eq_of_heart {v : permBar n}
    (hv : v ∈ (heartToBar : altHeart n →+ permBar n).range) :
    ∃ q : ↥(CFSG.Open.pCoreOf 2 M), Multiplicative.toAdd (D.piQ q) = v := by
  obtain ⟨u, rfl⟩ := hv
  obtain ⟨w, hw⟩ := C.β_surj (Multiplicative.ofAdd u)
  refine ⟨⟨(w : G), C.S.W_le_Q w.2⟩, ?_⟩
  rw [D.piQ_W w _ rfl, hw, toAdd_ofAdd]

theorem x_ne_one {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin n)} (hI : I.card = 4)
    (hIn : 4 < n) (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : x ≠ 1 := by
  intro h
  subst h
  have h1 : D.piQ ⟨1, hx⟩ = 1 := by
    have : (⟨1, hx⟩ : ↥(CFSG.Open.pCoreOf 2 M)) = 1 := rfl
    rw [this, map_one]
  rw [h1, toAdd_one] at hπ
  have h2 := congrArg barLen hπ
  rw [barLen_barInd, hI, H4b.barLen_zero'] at h2
  omega

theorem theta_conj_mem_of_normalized {x : G} {U : Subgroup G} (hUM : U ≤ M)
    (hUn : ∀ k ∈ CMOf M x, ∀ u ∈ U, k * u * k⁻¹ ∈ U) {m : ↥M} (hm : (m : G) ∈ CMOf M x)
    {σ : Perm (Fin n)} (hσ : σ ∈ (U.subgroupOf M).map C.θ) :
    C.θ m * σ * (C.θ m)⁻¹ ∈ (U.subgroupOf M).map C.θ := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hσ
  have hmuU : (m : G) * (u : G) * (m : G)⁻¹ ∈ U := hUn _ hm _ (Subgroup.mem_subgroupOf.1 hu)
  refine Subgroup.mem_map.2 ⟨m * u * m⁻¹, Subgroup.mem_subgroupOf.2 hmuU, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem theta_normalized_of_normalized {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin n)} (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {U : Subgroup G}
    (hUM : U ≤ M) (hUn : ∀ k ∈ CMOf M x, ∀ u ∈ U, k * u * k⁻¹ ∈ U) {S : Finset (Fin n)}
    (hS : S = I ∨ S = Iᶜ) :
    ∀ τ ∈ altOn S, ∀ σ ∈ (U.subgroupOf M).map C.θ, τ * σ * τ⁻¹ ∈ (U.subgroupOf M).map C.θ := by
  intro τ hτ σ hσ
  obtain ⟨c, hcC, hcθ⟩ := Subgroup.mem_map.1 (altOn_le_theta_CMOf D hx hπ hS hτ)
  rw [← hcθ]
  exact theta_conj_mem_of_normalized hUM hUn (Subgroup.mem_subgroupOf.1 hcC) hσ

end Generic

section Eight

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 8} (D : C.PiData)

theorem sup_le_TOf (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M ≤ TOf M x := by
  set H : Subgroup G := CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M with hH
  have hH2 := H4b.isPGroup_sup C hR hx
  have hUT : H ⊓ M ≤ TOf M x := H4b.sup_inf_le_TOf C hR hx
  suffices hHM : H ⊓ M = H by rw [← hHM]; exact hUT
  by_contra hne
  obtain ⟨h, hhH, hhN, hhNN⟩ := exists_mem_normalizer_of_lt hH2 inf_le_left hne
  have hBHM : C.qB ≤ H ⊓ M :=
    le_inf (C.qB_le_Q.trans le_sup_right) (C.qB_le_Q.trans (pCoreOf_le_self M))
  have hconj : conjSubgroup h C.qB ≤ TOf M x := fun e he => by
    have he' : h⁻¹ * e * h ∈ C.qB := mem_conjSubgroup.1 he
    have h2 := (Subgroup.mem_normalizer_iff.1 hhNN (h⁻¹ * e * h)).1 (hBHM he')
    have : h * (h⁻¹ * e * h) * h⁻¹ = e := by group
    rw [this] at h2
    exact hUT h2
  exact hhN ⟨hhH, mem_M_of_conj_qB_le_TOf D hR hx hI hπ hconj⟩

theorem P_le_TOf (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    CFSG.Open.pCoreOf 2 (CGOf x) ≤ TOf M x :=
  le_sup_left.trans (sup_le_TOf D hR hx hI hπ)

theorem P_le_M (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    CFSG.Open.pCoreOf 2 (CGOf x) ≤ M :=
  (P_le_TOf D hR hx hI hπ).trans (TOf_le_M M x)

theorem not_Q_le_P (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    ¬ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 (CGOf x) := by
  intro hQP
  have hPT := P_le_TOf D hR hx hI hπ
  apply hKM
  intro k hk
  refine mem_M_of_conj_qB_le_TOf D hR hx hI hπ (g := k) fun e he => ?_
  have he' : k⁻¹ * e * k ∈ C.qB := mem_conjSubgroup.1 he
  have h1 : k⁻¹ * e * k ∈ CFSG.Open.pCoreOf 2 (CGOf x) := hQP (C.qB_le_Q he')
  have h2 : e ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
    have := pCoreOf_normalized _ hk h1
    simpa [mul_assoc] using this
  exact hPT h2

theorem theta_P_le (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ ≤ klein8 I := by
  rw [← theta_TOf_eq D hR hx hI hπ]
  exact Subgroup.map_mono fun m hm =>
    Subgroup.mem_subgroupOf.2 (P_le_TOf D hR hx hI hπ (Subgroup.mem_subgroupOf.1 hm))

theorem P_normalized {x k p : G} (hk : k ∈ CMOf M x) (hp : p ∈ CFSG.Open.pCoreOf 2 (CGOf x)) :
    k * p * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
  pCoreOf_normalized _ (Subgroup.mem_inf.1 hk).2 hp

theorem theta_P_ne_bot (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ ≠ ⊥ := by
  have hx1 : x ≠ 1 := x_ne_one D hx hI (by norm_num) hπ
  have hPM := P_le_M D hR hx hI hπ
  intro hbot
  apply H4b.not_P_le_Q C hR hx hx1 hKM
  intro p hp
  have hpM : p ∈ M := hPM hp
  have hmem : C.θ ⟨p, hpM⟩ ∈ ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ :=
    Subgroup.mem_map.2 ⟨⟨p, hpM⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  rw [hbot] at hmem
  have hK : p ∈ C.K := C.mem_K.2 ⟨hpM, Subgroup.mem_bot.1 hmem⟩
  rwa [C.K_eq_Q hR] at hK

theorem klein4_le_theta_P (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    klein4 I ≤ ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ ∨
      klein4 Iᶜ ≤ ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ :=
  klein4_le_of_normalized hI (card_compl_eight hI) (theta_P_le D hR hx hI hπ)
    (theta_P_ne_bot D hR hx hI hπ hKM)
    (theta_normalized_of_normalized D hx hπ (P_le_M D hR hx hI hπ)
      (fun k hk p hp => P_normalized hk hp) (Or.inl rfl))
    (theta_normalized_of_normalized D hx hπ (P_le_M D hR hx hI hπ)
      (fun k hk p hp => P_normalized hk hp) (Or.inr rfl))

theorem center_P_le_Q (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) {z : G}
    (hzP : z ∈ CFSG.Open.pCoreOf 2 (CGOf x))
    (hz : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * z = z * p) : z ∈ CFSG.Open.pCoreOf 2 M := by
  classical
  by_contra hzQ
  have hIc := card_compl_eight hI
  have hPM := P_le_M D hR hx hI hπ
  set Zc : Subgroup G := H4b.centerP x with hZc
  have hZcP : Zc ≤ CFSG.Open.pCoreOf 2 (CGOf x) := inf_le_left
  have hZcM : Zc ≤ M := hZcP.trans hPM
  have hzZ : z ∈ Zc := Subgroup.mem_inf.2 ⟨hzP, Subgroup.mem_centralizer_iff.2 hz⟩
  have hZn : ∀ k ∈ CMOf M x, ∀ u ∈ Zc, k * u * k⁻¹ ∈ Zc := fun k hk u hu =>
    center_conj_mem (fun k hk p hp => pCoreOf_normalized _ hk hp) (Subgroup.mem_inf.1 hk).2 hu
  set NZ : Subgroup (Perm (Fin 8)) := (Zc.subgroupOf M).map C.θ with hNZ
  have hNZle : NZ ≤ klein8 I := by
    rw [← theta_TOf_eq D hR hx hI hπ]
    exact Subgroup.map_mono fun m hm => Subgroup.mem_subgroupOf.2
      (P_le_TOf D hR hx hI hπ (hZcP (Subgroup.mem_subgroupOf.1 hm)))
  have hzM : z ∈ M := hPM hzP
  have hθz : C.θ ⟨z, hzM⟩ ≠ 1 := fun h => hzQ (by
    have hK : z ∈ C.K := C.mem_K.2 ⟨hzM, h⟩
    rwa [C.K_eq_Q hR] at hK)
  have hNZne : NZ ≠ ⊥ := by
    intro hbot
    have hmem : C.θ ⟨z, hzM⟩ ∈ NZ :=
      Subgroup.mem_map.2 ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.2 hzZ, rfl⟩
    rw [hbot] at hmem
    exact hθz (Subgroup.mem_bot.1 hmem)
  have hJ := klein4_le_of_normalized hI hIc hNZle hNZne
    (theta_normalized_of_normalized D hx hπ hZcM hZn (Or.inl rfl))
    (theta_normalized_of_normalized D hx hπ hZcM hZn (Or.inr rfl))
  obtain ⟨J, hJside, hJle⟩ : ∃ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) ∧ klein4 J ≤ NZ := by
    rcases hJ with h | h
    · exact ⟨I, Or.inl rfl, h⟩
    · exact ⟨Iᶜ, Or.inr rfl, h⟩
  have hJc : J.card = 4 ∧ Jᶜ.card = 4 := by
    rcases hJside with rfl | rfl
    · exact ⟨hI, hIc⟩
    · rw [compl_compl]; exact ⟨hIc, hI⟩
  have hF := klein4_fourGroup hJc.1
  have hN1 : klein4 J ≠ ⊥ := by
    intro h
    have := card_klein4 hJc.1
    rw [h, Subgroup.card_bot] at this
    omega
  obtain ⟨σ₁, hσ₁N, hσ₁1, -⟩ := hF.exists_ne hJc.1 hN1 1
  obtain ⟨σ', hσ'N, hσ'1, hσ'σ⟩ := hF.exists_ne hJc.1 hN1 σ₁
  obtain ⟨ζm, hζm, hζθ⟩ := Subgroup.mem_map.1 (hJle hσ₁N)
  obtain ⟨pm, hpm, hpmσ⟩ := Subgroup.mem_map.1 (hJle hσ'N)
  have hζZ : (ζm : G) ∈ Zc := Subgroup.mem_subgroupOf.1 hζm
  have hpP : (pm : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := hZcP (Subgroup.mem_subgroupOf.1 hpm)
  obtain ⟨a, haJ⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨d', hd'J⟩ : Jᶜ.Nonempty := Finset.card_pos.1 (by omega)
  have hd'fix : σ' d' = d' := hF.fix σ' hσ'N d' (Finset.mem_compl.1 hd'J)
  obtain ⟨q, hq⟩ := exists_piQ_eq_uvec D a d'
  have hqK : (q : G) ∈ CGOf x := H4b.Q_le_CGOf C hR hx q.2
  have hpq : (pm : G) * (q : G) * (pm : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_normalized M pm.2 q.2
  have hconj := D.piQ_conj pm q ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩ rfl
  let cq : ↥(CFSG.Open.pCoreOf 2 M) := q⁻¹ * ⟨(pm : G) * (q : G) * (pm : G)⁻¹, hpq⟩
  have hπc : Multiplicative.toAdd (D.piQ cq) = uvec a (σ' a) := by
    simp only [cq, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [hconj, hpmσ, hq, barAct_uvec, hd'fix]
    exact neg_uvec_add_uvec a (σ' a) d'
  have hcP : (cq : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
    have e : (cq : G) = ((q : G)⁻¹ * (pm : G) * (q : G)) * (pm : G)⁻¹ := by
      show (q : G)⁻¹ * ((pm : G) * (q : G) * (pm : G)⁻¹) = _
      group
    have h3 : (q : G)⁻¹ * (pm : G) * (q : G) ∈ CFSG.Open.pCoreOf 2 (CGOf x) := by
      have := pCoreOf_normalized _ ((CGOf x).inv_mem hqK) hpP
      simpa using this
    rw [e]
    exact (CFSG.Open.pCoreOf 2 (CGOf x)).mul_mem h3 ((CFSG.Open.pCoreOf 2 (CGOf x)).inv_mem hpP)
  have hζc : (cq : G) = (ζm : G) * (cq : G) * (ζm : G)⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hζZ).2 _ hcP
    calc (cq : G) = ((cq : G) * (ζm : G)) * (ζm : G)⁻¹ := by group
      _ = ((ζm : G) * (cq : G)) * (ζm : G)⁻¹ := by rw [h1]
  have h2 := D.piQ_conj ζm cq cq hζc
  rw [hπc, hζθ] at h2
  exact barAct_uvec_ne_of_fourGroup (by norm_num) hF hJc.1 hσ₁N hσ₁1 hσ'N hσ'1 (Ne.symm hσ'σ)
    haJ h2.symm

theorem rc_eq_bot (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    Rc X = ⊥ := by
  classical
  by_contra hRbot
  obtain ⟨⟨r0, hr0⟩, hr01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRbot
  have hr01' : r0 ≠ 1 := fun h => hr01 (Subtype.ext h)
  have hx1 : x ≠ 1 := x_ne_one D hx hI (by norm_num) hπ
  have hPM := P_le_M D hR hx hI hπ
  have hr0Q : r0 ∈ CFSG.Open.pCoreOf 2 M := by
    have h := hr0
    rw [C.S.R_eq_inf] at h
    exact (Subgroup.mem_inf.1 h).1
  have hr0K : r0 ∈ CGOf x := H4b.Q_le_CGOf C hR hx hr0Q
  have hcons := H4b.twoConstrained_P C hR hx hx1
  have hr0cent : ∀ p ∈ CFSG.Open.pCoreOf 2 (CGOf x), p * r0 = r0 * p := by
    intro p hp
    have h1 := C.R_central hR p (hPM hp) r0 hr0
    calc p * r0 = (p * r0 * p⁻¹) * p := by group
      _ = r0 * p := by rw [h1]
  have hr0P : r0 ∈ CFSG.Open.pCoreOf 2 (CGOf x) :=
    hcons (Subgroup.mem_inf.2 ⟨hr0K, Subgroup.mem_centralizer_iff.2 hr0cent⟩)
  have hEQ : H4b.centerP x ≤ CFSG.Open.pCoreOf 2 M := fun z hz =>
    center_P_le_Q D hR hx hI hπ hKM hz.1 (fun p hp => Subgroup.mem_centralizer_iff.1 hz.2 p hp)
  have hr0E : r0 ∈ H4b.centerP x :=
    Subgroup.mem_inf.2 ⟨hr0P, Subgroup.mem_centralizer_iff.2 hr0cent⟩
  have hKN : ∀ k ∈ CGOf x, k ∈ Subgroup.normalizer ((H4b.centerP x : Subgroup G) : Set G) :=
    fun k hk => H4b.mem_normalizer_centerP hk
  have hCEM : Subgroup.centralizer ((H4b.centerP x : Subgroup G) : Set G) ≤ M := by
    intro c hc
    have h1 : r0 * c = c * r0 := Subgroup.mem_centralizer_iff.1 hc r0 hr0E
    have hl : barLen (Multiplicative.toAdd (D.piQ ⟨r0, hr0Q⟩)) ≠ 2 ∧
        barLen (Multiplicative.toAdd (D.piQ ⟨r0, hr0Q⟩)) ≠ 4 := by
      rw [(D.piQ_eq_one_iff ⟨r0, hr0Q⟩).2 hr0, toAdd_one, H4b.barLen_zero']
      exact ⟨by norm_num, by norm_num⟩
    exact (D.centralizer_le_of_len hR ⟨r0, hr0Q⟩ hr01' hl).1
      (Subgroup.mem_centralizer_singleton_iff.2 h1.symm)
  have hQC : CFSG.Open.pCoreOf 2 M ≤
      Subgroup.centralizer ((H4b.centerP x : Subgroup G) : Set G) :=
    fun q hq => Subgroup.mem_centralizer_iff.2 fun e he => C.Q_comm hR e (hEQ he) q hq
  have hQO : CFSG.Open.pCoreOf 2 M ≤
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ((H4b.centerP x : Subgroup G) : Set G)) :=
    le_pCoreOf_of_normalized hQC (fun c hc q hq => pCoreOf_normalized M (hCEM hc) hq)
      (isPGroup_pCoreOf' M)
  have hnormC : ∀ n' ∈ CGOf x,
      ∀ c ∈ Subgroup.centralizer ((H4b.centerP x : Subgroup G) : Set G),
      n' * c * n'⁻¹ ∈ Subgroup.centralizer ((H4b.centerP x : Subgroup G) : Set G) :=
    fun n' hn' c hc => centralizer_normalized (hKN n' hn') hc
  have hB'P : CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ((H4b.centerP x : Subgroup G) : Set G)) ⊓ CGOf x ≤
      CFSG.Open.pCoreOf 2 (CGOf x) := by
    refine le_pCoreOf_of_normalized inf_le_right (fun k hk b hb => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' _) inf_le_left)
    exact Subgroup.mem_inf.2 ⟨pCoreOf_normalized_of_normal hnormC hk hb.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hb.2) ((CGOf x).inv_mem hk)⟩
  exact not_Q_le_P D hR hx hI hπ hKM fun q hq =>
    hB'P (Subgroup.mem_inf.2 ⟨hQO hq, H4b.Q_le_CGOf C hR hx hq⟩)

theorem exists_swap (hrbot : Rc X = ⊥) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) :
    ∃ m : ↥M, (m : G) ∈ CMOf M x ∧ ∀ y, C.θ m y ∈ I ↔ y ∉ I := by
  classical
  have hIc := card_compl_eight hI
  obtain ⟨τ, hτA, hτI⟩ := Comb.exists_alt_map_eq (by norm_num) (I := I) (J := Iᶜ) (by rw [hI, hIc])
  obtain ⟨y, hy⟩ := C.exists_lift hτA
  have hyM : (y : G) ∈ M := C.S.le y.2
  set m : ↥M := ⟨(y : G), hyM⟩ with hm
  have hθm : C.θ m = τ := hy
  have hswap : ∀ z, C.θ m z ∈ I ↔ z ∉ I := by
    intro z
    rw [hθm]
    have hmem : τ z ∈ Iᶜ ↔ z ∈ I := by
      rw [← hτI]
      simp only [Finset.mem_map_equiv, Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨w, hw, hwz⟩
        rw [← τ.injective hwz]
        exact hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [Finset.mem_compl] at hmem
    constructor
    · intro h hz
      exact (hmem.2 hz) h
    · intro hz
      by_contra h
      exact hz (hmem.1 h)
  have hxm : (m : G) * x * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M hyM hx
  have hconj := D.piQ_conj m ⟨x, hx⟩ ⟨(m : G) * x * (m : G)⁻¹, hxm⟩ rfl
  rw [hπ, barAct_barInd] at hconj
  have himg : I.image (C.θ m) = Iᶜ := by
    ext z
    simp only [Finset.mem_image, Finset.mem_compl]
    constructor
    · rintro ⟨w, hw, rfl⟩ h
      exact (hswap w).1 h hw
    · intro hz
      refine ⟨(C.θ m)⁻¹ z, ?_, perm_apply_inv_self _ z⟩
      by_contra h
      have := (hswap ((C.θ m)⁻¹ z)).2 h
      rw [perm_apply_inv_self] at this
      exact hz this
  rw [himg, barInd_compl, ← hπ] at hconj
  have heq := piQ_injective D hrbot (Multiplicative.toAdd.injective hconj)
  have hc : (m : G) * x * (m : G)⁻¹ = x := congrArg Subtype.val heq
  refine ⟨m, Subgroup.mem_inf.2 ⟨hyM, mem_centralizer_zpowers_iff.2 hc⟩, hswap⟩

theorem theta_P_eq (hR : Nat.card ↥(Rc X) ≤ 2) {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M)
    {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) (hKM : ¬ CGOf x ≤ M) :
    ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ = klein8 I := by
  have hIc := card_compl_eight hI
  have hrbot := rc_eq_bot D hR hx hI hπ hKM
  obtain ⟨m, hmC, hmsw⟩ := exists_swap D hrbot hx hI hπ
  set N := ((CFSG.Open.pCoreOf 2 (CGOf x)).subgroupOf M).map C.θ with hN
  have hPM := P_le_M D hR hx hI hπ
  have hconj : ∀ σ ∈ N, C.θ m * σ * (C.θ m)⁻¹ ∈ N := fun σ hσ =>
    theta_conj_mem_of_normalized hPM (fun k hk p hp => P_normalized hk hp) hmC hσ
  have hmap : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → J.image (C.θ m) = Jᶜ := by
    intro J hJ
    ext z
    simp only [Finset.mem_image, Finset.mem_compl]
    rcases hJ with rfl | rfl
    · constructor
      · rintro ⟨w, hw, rfl⟩ h
        exact (hmsw w).1 h hw
      · intro hz
        refine ⟨(C.θ m)⁻¹ z, ?_, perm_apply_inv_self _ z⟩
        by_contra h
        have := (hmsw ((C.θ m)⁻¹ z)).2 h
        rw [perm_apply_inv_self] at this
        exact hz this
    · simp only [Finset.mem_compl, not_not]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hmsw w).2 hw
      · intro hz
        refine ⟨(C.θ m)⁻¹ z, fun h => ?_, perm_apply_inv_self _ z⟩
        have := (hmsw ((C.θ m)⁻¹ z)).1
        rw [perm_apply_inv_self] at this
        exact this hz h
  have hboth : ∀ J : Finset (Fin 8), (J = I ∨ J = Iᶜ) → klein4 J ≤ N → klein4 Jᶜ ≤ N := by
    intro J hJ hle σ hσ
    have hJc : J.card = 4 := by rcases hJ with rfl | rfl <;> assumption
    have hσ' : (C.θ m)⁻¹ * σ * (C.θ m)⁻¹⁻¹ ∈ klein4 J := by
      have hJcc : Jᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hJc]
      have h1 := klein4_conj_mem_image hJcc (C.θ m)⁻¹ hσ
      have himg : Jᶜ.image ⇑((C.θ m)⁻¹) = J := by
        rw [← hmap J hJ, Finset.image_image]
        have hid : (⇑((C.θ m)⁻¹) ∘ ⇑(C.θ m) : Fin 8 → Fin 8) = id := by
          funext z
          simp
        rw [hid, Finset.image_id]
      rwa [himg] at h1
    have := hconj _ (hle hσ')
    simpa [mul_assoc] using this
  rcases klein4_le_theta_P D hR hx hI hπ hKM with h | h
  · refine le_antisymm (theta_P_le D hR hx hI hπ) ?_
    unfold klein8
    exact sup_le h (hboth I (Or.inl rfl) h)
  · refine le_antisymm (theta_P_le D hR hx hI hπ) ?_
    unfold klein8
    have h2 := hboth Iᶜ (Or.inr rfl) h
    rw [compl_compl] at h2
    exact sup_le h2 h

end Eight

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
