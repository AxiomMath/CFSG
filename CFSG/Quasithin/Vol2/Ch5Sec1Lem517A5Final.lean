module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Lab
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517Two
public import CFSG.Quasithin.H13.NQCatLieOverRank1
public import CFSG.Quasithin.H13.VolIC113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512FFProof

public section

namespace CFSG.Quasithin.H13.A5Push

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T M L W : Subgroup G} {F : S5Frame (L ⊔ T) W} {n : ℕ} {hs : Setting T M L W F n}
  {P : Subgroup G}

theorem conj_S_eq {x : G} (hx : x ∈ Subgroup.normalizer (baum T : Set G)) :
    (baum T).map (MulAut.conj x).toMonoidHom = baum T :=
  Subgroup.eq_of_le_of_card_ge (conj_le_S le_rfl hx)
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge

theorem Partner.Q_ne_P (hp : hs.Partner P) : baum T ⊓ Subgroup.centralizer (W : Set G) ≠ P := by
  intro heq
  have h1 := hp.sup
  rw [← heq, sup_idem] at h1
  obtain ⟨s, hsS, hs1⟩ := hs.hB.rho_baum_surj (swap 0 1) (by decide)
  have h2 : (s : G) ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by rw [h1]; exact hsS
  have h3 := (hs.rho_eq_one_iff s hsS).2 h2
  rw [hs1] at h3
  exact absurd h3 (by decide)

theorem conj_sup_eq {X Y : Subgroup G} (hXY : X ⊔ Y = baum T) {x : G}
    (hx : x ∈ Subgroup.normalizer (baum T : Set G)) :
    X.map (MulAut.conj x).toMonoidHom ⊔ Y.map (MulAut.conj x).toMonoidHom = baum T := by
  rw [← Subgroup.map_sup, hXY, conj_S_eq hx]

theorem Partner.mem_pair (hp : hs.Partner P) {A₂ A₃ A₄ : Subgroup G}
    (h₂ : IsMaxElemAbelian T A₂) (h₃ : IsMaxElemAbelian T A₃) (h₄ : IsMaxElemAbelian T A₄)
    (hQ₂ : A₂ ≠ baum T ⊓ Subgroup.centralizer (W : Set G)) (hP₂ : A₂ ≠ P)
    (hQ₃ : A₃ ≠ baum T ⊓ Subgroup.centralizer (W : Set G)) (hP₃ : A₃ ≠ P)
    (hQ₄ : A₄ ≠ baum T ⊓ Subgroup.centralizer (W : Set G)) (hP₄ : A₄ ≠ P)
    (h23 : A₂ ⊔ A₃ = baum T) : A₄ = A₂ ∨ A₄ = A₃ := by
  classical
  have hne : A₂ ≠ A₃ := by
    intro heq
    rw [← heq, sup_idem] at h23
    apply hP₂
    refine hp.eq_P_of_sup h₂ ?_
    rw [h23]
    exact sup_eq_right.mpr inf_le_left
  obtain ⟨a₂, ha₂, hσ₂, hlab₂⟩ := hp.label_of_ne h₂ hQ₂ hP₂
  obtain ⟨a₃, ha₃, hσ₃, hlab₃⟩ := hp.label_of_ne h₃ hQ₃ hP₃
  obtain ⟨a₄, ha₄, hσ₄, hlab₄⟩ := hp.label_of_ne h₄ hQ₄ hP₄
  have heqlab : ∀ {A A' : Subgroup G} (hA : IsMaxElemAbelian T A)
      (hA' : IsMaxElemAbelian T A') (a a' : ↥(L ⊔ T)), (a : G) ∈ A → (a' : G) ∈ A' →
      (∀ b : ↥(L ⊔ T), (b : G) ∈ A → F.ρ b = 1 ∨ F.ρ b = F.ρ a) →
      (∀ b : ↥(L ⊔ T), (b : G) ∈ A' → F.ρ b = 1 ∨ F.ρ b = F.ρ a') → F.ρ a = F.ρ a' →
        A = A' := by
    intro A A' hA hA' a a' ha ha' hl hl' hρ
    refine hp.eq_of_label hA hA' (fun b hb => ?_) fun b hb => ?_
    · rcases hl b hb with h | h
      · exact ⟨1, A'.one_mem, by rw [map_one, h]⟩
      · exact ⟨a', ha', by rw [h, hρ]⟩
    · rcases hl' b hb with h | h
      · exact ⟨1, A.one_mem, by rw [map_one, h]⟩
      · exact ⟨a, ha, by rw [h, hρ]⟩
  have h23' : F.ρ a₂ ≠ F.ρ a₃ := fun h => hne (heqlab h₂ h₃ a₂ a₃ ha₂ ha₃ hlab₂ hlab₃ h)
  rcases hσ₂ with e₂ | e₂ <;> rcases hσ₃ with e₃ | e₃ <;> rcases hσ₄ with e₄ | e₄
  all_goals first
    | exact absurd (e₂.trans e₃.symm) h23'
    | exact Or.inl (heqlab h₄ h₂ a₄ a₂ ha₄ ha₂ hlab₄ hlab₂ (e₄.trans e₂.symm))
    | exact Or.inr (heqlab h₄ h₃ a₄ a₃ ha₄ ha₃ hlab₄ hlab₃ (e₄.trans e₃.symm))

omit [Finite G] in
theorem conj_pow_succ (X : Subgroup G) (x : G) (j : ℕ) :
    (X.map (MulAut.conj (x ^ j)).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      X.map (MulAut.conj (x ^ (j + 1))).toMonoidHom := by
  rw [conj_map_conj_map, pow_succ']

omit [Finite G] in
theorem parity_contra {x : G} (hodd : Odd (orderOf x)) (Q₀ : Subgroup G)
    (C D : Subgroup G → Prop) (hD0 : D Q₀)
    (hDf : ∀ X, D X → D (X.map (MulAut.conj x).toMonoidHom))
    (hflip : ∀ X, D X → (C (X.map (MulAut.conj x).toMonoidHom) ↔ ¬ C X)) (hC0 : C Q₀) :
    False := by
  have key : ∀ j : ℕ, D (Q₀.map (MulAut.conj (x ^ j)).toMonoidHom) ∧
      (C (Q₀.map (MulAut.conj (x ^ j)).toMonoidHom) ↔ Even j) := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, conj_map_one]
      exact ⟨hD0, iff_of_true hC0 Even.zero⟩
    | succ j ih =>
      rw [← conj_pow_succ]
      refine ⟨hDf _ ih.1, ?_⟩
      rw [hflip _ ih.1, ih.2, Nat.even_add_one]
  have h := (key (orderOf x)).2
  rw [pow_orderOf_eq_one, conj_map_one] at h
  exact (Nat.not_even_iff_odd.mpr hodd) (h.mp hC0)

theorem Partner.conj_Q_eq (hp : hs.Partner P) {x : G}
    (hx : x ∈ Subgroup.normalizer (baum T : Set G)) (hodd : Odd (orderOf x)) :
    (baum T ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj x).toMonoidHom =
      baum T ⊓ Subgroup.centralizer (W : Set G) := by
  classical
  set Q := baum T ⊓ Subgroup.centralizer (W : Set G) with hQdef
  have hQmax := hs.isMax_Q hp.elQ
  have hQP := hp.Q_ne_P
  set f : Subgroup G → Subgroup G := fun X => X.map (MulAut.conj x).toMonoidHom with hfdef
  have hfinj : Function.Injective f := Subgroup.map_injective (MulAut.conj x).injective
  have hfmax : ∀ X, IsMaxElemAbelian T X → IsMaxElemAbelian T (f X) := fun X hX =>
    isMax_conj hX (le_S_of_isMax hX) hx
  have hfsup : f Q ⊔ f P = baum T := conj_sup_eq hp.sup hx
  by_contra hne
  change f Q ≠ Q at hne
  by_cases hfP : f Q = P
  ·
    have hfQ : f P = Q := by
      refine hp.eq_Q_of_sup (hfmax P hp.maxP) ?_
      have h1 := hfsup
      rw [hfP] at h1
      exact h1
    refine parity_contra hodd Q (fun X => X = Q) (fun X => X = Q ∨ X = P) (Or.inl rfl)
      (fun X hX => ?_) (fun X hX => ?_) rfl
    · show f X = Q ∨ f X = P
      rcases hX with h | h
      · rw [h]; exact Or.inr hfP
      · rw [h]; exact Or.inl hfQ
    · show f X = Q ↔ ¬ X = Q
      rcases hX with h | h
      · rw [h]; exact iff_of_false hne (fun h' => h' rfl)
      · rw [h]; exact iff_of_true hfQ (Ne.symm hQP)
  ·
    have hfPQ : f P ≠ Q := by
      intro h
      apply hfP
      refine hp.eq_P_of_sup (hfmax Q hQmax) ?_
      have h1 := hfsup
      rw [h, sup_comm] at h1
      exact h1
    have hfPP : f P ≠ P := by
      intro h
      apply hne
      refine hp.eq_Q_of_sup (hfmax Q hQmax) ?_
      have h1 := hfsup
      rw [h, sup_comm] at h1
      exact h1
    refine parity_contra hodd Q (fun X => X = Q ∨ X = P) (fun X => IsMaxElemAbelian T X)
      hQmax (fun X hX => hfmax X hX) (fun X hX => ?_) (Or.inl rfl)
    show (f X = Q ∨ f X = P) ↔ ¬ (X = Q ∨ X = P)
    constructor
    · rintro h (hX₁ | hX₁)
      · rw [hX₁] at h
        rcases h with h | h
        · exact hne h
        · exact hfP h
      · rw [hX₁] at h
        rcases h with h | h
        · exact hfPQ h
        · exact hfPP h
    · intro hX'
      push Not at hX'
      by_contra hfX
      push Not at hfX
      rcases hp.mem_pair (hfmax Q hQmax) (hfmax P hp.maxP) (hfmax X hX) hne hfP hfPQ hfPP
        hfX.1 hfX.2 hfsup with h | h
      · exact hX'.1 (hfinj h)
      · exact hX'.2 (hfinj h)

theorem false (hs : Setting T M L W F n) : False := by
  obtain ⟨k₀, hk₀, hk₀W⟩ := hs.exists_conj_not_le
  have hQel := hs.isElemAbelian_Q hk₀ hk₀W
  obtain ⟨k, hk, hpart⟩ := hs.exists_partner hQel hk₀ hk₀W
  have hp : hs.Partner ((baum T ⊓ Subgroup.centralizer (W : Set G)).map
      (MulAut.conj k).toMonoidHom) :=
    ⟨hQel, isMax_conj (hs.isMax_Q hQel) inf_le_left hk, hpart,
      hs.QC_le_partner hQel hk hpart⟩
  apply hs.NS
  have hTS : IsSylowTwoOf T (Subgroup.normalizer (baum T : Set G)) :=
    hs.hyp.isSylowTwoOf (T_le_normalizer_S T)
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' hTS]
  refine sup_le ?_ hs.hyp.T_le
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxN, hxodd⟩
  apply hs.normalizer_Q_le
  have heq := hp.conj_Q_eq hxN hxodd
  refine mem_normalizer_of_conj (fun q hq => ?_) fun q hq => ?_
  · rw [← heq]
    exact conj_mem_conj_map hq
  · rw [← heq, mem_conj_map] at hq
    exact hq

end Setting

end CFSG.Quasithin.H13.A5Push

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv
open scoped IsMulCommutative commutatorElement

theorem stmt5_1_7_one_A5_of (he234 : E2.E23FourStatement) (h432 : Stmt4_3_2)
    (hC113 : A5.StmtC113c) (hR : L2RankOneSylowFact) : Stmt5_1_7_one_A5 := by
  intro G _ _ T M L V n h hV hJ _ hsplit _ hS5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hNS
  set W := ⁅V, L⁆ with hWdef
  obtain ⟨hLTW, hWc, hsym⟩ := hS5
  have hT : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  obtain ⟨F, hTD, hDT⟩ := (nonempty_s5Frame hLTW hsym).some.exists_adapted hT
  have hred := hV.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hWV : W ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hVT : V ≤ T := h.le_T_of_isCh5Module hV
  have hWel : IsElemAbelian 2 W := A5Push.isElemAbelian_of_mul_self fun w hw => by
    rw [← pow_two]; exact hred.2.2.1.2 w (hWV hw)
  have hJ' : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hJ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G) := by
    intro hle
    apply hJ'
    rw [Subgroup.le_centralizer_iff, ← hsplit.2]
    refine sup_le (Subgroup.le_centralizer_iff.mp hle) fun v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjT : j ∈ L ⊔ T :=
      Subgroup.mem_sup_right ((iSup₂_le fun _ hA => hA.1 : thompsonJ T ≤ T) hj)
    exact Subgroup.mem_centralizer_iff.mp hv.2 j hjT
  have hB : A5BaumHyp F T := ⟨le_sup_right, hWV.trans hVT, hWel, hTD, hDT, hJW⟩
  have hWQ : W ≤ pCoreOf 2 L := h.commutator_le_pCoreOf hV
  have hO2W : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) :=
    (h.pCoreOf_le_centralizer hV).trans (Subgroup.centralizer_le hWV)
  obtain ⟨hshort, halt⟩ := h.isA5Block he234 h432 hR hV hJ' hNS F hWQ hO2W
  obtain ⟨hO2, hdisj⟩ := hC113 G L T hT h.T_le_normalizer hshort halt
  have hUT : blockU L ≤ T := by
    have h1 : blockU L ≤ pCoreOf 2 (L ⊔ T) := by rw [hO2]; exact le_sup_left
    exact h1.trans (F7.isSylowTwoOf_pCoreOf_le hT)
  have hZ : blockZ L = ⊥ := by
    rw [eq_bot_iff, ← hdisj]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hUT) inf_le_right)
  have hWU' : W ≤ blockU L := by
    rw [hWdef, Subgroup.commutator_le]
    intro v hv l hl
    have hVO : V ≤ pCoreOf 2 (L ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.1 hred.2.1
        (fun x => ⟨1, Subtype.ext (by simpa using hred.2.2.1.2 x x.2)⟩)
    have hCN : T ⊓ Subgroup.centralizer (L : Set G) ≤
        Subgroup.normalizer (blockU L : Set G) := fun c hc =>
      C1.mem_normalizer_blockU (h.T_le_normalizer hc.1)
    have h1 : v ∈ ((blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) :
        Set G) := by rw [← hO2]; exact hVO hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCN] at h1
    obtain ⟨u, hu, c, hc, rfl⟩ := Set.mem_mul.mp h1
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
    have e : ⁅u * c, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      calc u * c * l * (u * c)⁻¹ * l⁻¹ = u * (c * l) * c⁻¹ * u⁻¹ * l⁻¹ := by group
        _ = u * (l * c) * c⁻¹ * u⁻¹ * l⁻¹ := by rw [hcl]
        _ = u * (l * u⁻¹ * l⁻¹) := by group
    rw [e]
    refine (blockU L).mul_mem hu ?_
    exact (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer hl))
      _).mp ((blockU L).inv_mem hu)
  have hWU : W = blockU L := by
    have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
      le_normalizer_commutator_of hLV Subgroup.le_normalizer
    rcases hshort.2.2.2.2.2 W (by rw [hZ]; exact bot_le) hWU' hLW with h1 | h1
    · exact absurd (h1.trans hZ) hV.2.2
    · exact h1
  have hCTW : T ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 (L ⊔ T) := by
    rw [← h.centralizer_eq_pCoreOf hV]
    refine le_antisymm (fun t ht => Subgroup.mem_inf.mpr ⟨ht.1, ?_⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le hWV))
    have hle : V ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [← hsplit.2]
      refine sup_le ?_ fun v hv => ?_
      · rw [← Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr ht.2
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have h1 := Subgroup.mem_centralizer_iff.mp hv.2 t (Subgroup.mem_sup_right ht.1)
        exact ((Commute.zpow_left h1 m)).eq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hle hv) t (Subgroup.mem_zpowers t)).symm
  have hs : A5Push.Setting T M L W F n :=
    ⟨h, h432, hB, hWU, by rw [hWU]; exact hO2, by rw [hWU]; exact hdisj, hCTW, hNS⟩
  exact hs.false

theorem stmt5_1_7_one_of_asB51' (h331 : Stmt3_3_1) (h51 : AsB51)
    (h432 : Stmt4_3_2) (he234 : E2.E23FourStatement) : A5.Stmt5_1_7_one :=
  stmt5_1_7_one_of (stmt5_1_2_of_asB51 h331 h51) h432
    (stmt5_1_7_one_nat_of_rankOne NQCat.l2RankOneSylowFact_holds)
    (stmt5_1_7_one_A5_of he234 h432 VolI.stmtC113c NQCat.l2RankOneSylowFact_holds)

end CFSG.Quasithin.H13
