module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Defs
public import CFSG.Quasithin.Vol2.Ch4Sec3L436

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436
open scoped commutatorElement Pointwise

theorem isPSp4_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n : ℕ} (e : X ≃* Y)
    (h : IsPSp4 2 n X) : IsPSp4 2 n Y := by
  obtain ⟨hadm, F, hF, hfin, hcard, ⟨f⟩⟩ := h
  exact ⟨hadm, F, hF, hfin, hcard, ⟨e.symm.trans f⟩⟩

variable {G : Type} [Group G]

@[expose] noncomputable def sl2u (F : Type) [Field F] : StatedSL 2 F :=
  ⟨⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩

theorem sl2u_mulVec {F : Type} [Field F] (w : Fin 2 → F) :
    ((sl2u F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w 0 = w 0 + w 1 := by
  simp [sl2u, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem not_le_centralizer_of_isNaturalSection {A V Z : Subgroup G} {N : Subgroup ↥A}
    {F : Type} [Field F] [Fintype F] (h : IsNaturalSection A V Z N (StatedSL 2 F)) :
    ¬ A ≤ Subgroup.centralizer (V : Set G) := by
  intro hAC
  obtain ⟨-, α, hαs, -, β, hβs, -, hβ⟩ := h
  obtain ⟨a, ha⟩ := hαs (sl2u F)
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single 1 1))
  have hc : (u : G) = a * u * a⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.mp (hAC a.2) u u.2
    rw [Subgroup.coe_inv, ← h1, mul_inv_cancel_right]
  have h2 := congrFun (hβ a u u hc) 0
  rw [ha, hu, sl2u_mulVec] at h2
  simp at h2

theorem eq_one_of_isNaturalSection_bot {A V : Subgroup G} {N : Subgroup ↥A} {F : Type} [Field F]
    [Fintype F] (h : IsNaturalSection A V ⊥ N (StatedSL 2 F)) {v : G} (hv : v ∈ V)
    (hvA : A ≤ Subgroup.centralizer ({v} : Set G)) : v = 1 := by
  obtain ⟨-, α, hαs, -, β, -, hβk, hβ⟩ := h
  have hfix : ∀ g : StatedSL 2 F, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      (Multiplicative.toAdd (β ⟨v, hv⟩)) = Multiplicative.toAdd (β ⟨v, hv⟩) := by
    intro g
    obtain ⟨a, rfl⟩ := hαs g
    have hc : v = a * v * a⁻¹ := by
      have h1 := Subgroup.mem_centralizer_iff.mp (hvA a.2) v rfl
      rw [Subgroup.coe_inv, ← h1, mul_inv_cancel_right]
    exact (hβ a ⟨v, hv⟩ ⟨v, hv⟩ hc).symm
  set w := Multiplicative.toAdd (β ⟨v, hv⟩) with hw
  have h1 : w 1 = 0 := by
    have := congrFun (hfix (sl2u F)) 0
    rw [sl2u_mulVec] at this
    exact add_eq_left.mp this
  let ut : StatedSL 2 F :=
    ⟨⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
      Subgroup.subset_closure (by simp [Matrix.det_fin_two_of])⟩
  have h0 : w 0 = 0 := by
    have := congrFun (hfix ut) 1
    simp [ut, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    exact this
  have hw0 : w = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hker : (⟨v, hv⟩ : ↥V) ∈ β.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    rw [← hw, hw0]
    rfl
  rw [hβk] at hker
  simpa using hker

variable [Finite G]

@[expose] def v432 (T M L : Subgroup G) : Subgroup G :=
  ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆

structure Setting436Sp4 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ)
    (I H K : Subgroup G) (t : G) : Prop where
  sk : Setting432K G T M L n I H K t
  comp : CFSG.Open.IsComponentOf K H
  center : Subgroup.center ↥K = ⊥
  L_eq : L = perfectCore (H ⊓ M ⊓ K)
  concl : Sp4ParConcl n K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L)
  nat : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    IsNaturalSection L (v432 T M L) (v432 T M L ⊓ Subgroup.centralizer (L : Set G))
      (CFSG.pCore 2 ↥L) (StatedSL 2 F)

theorem setting436Sp4_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hMult : Sp4MultTrivial) (hPar : Sp4ParabolicFacts) {T M L : Subgroup G} {n : ℕ}
    {I H K : Subgroup G} {t : G} (sk : Setting432K G T M L n I H K t)
    (hK : CFSG.Open.IsComponentOf K H)
    (hC1 : C31Case1 H (pCoreOf 2 I) (H ⊓ M) L (v432 T M L) K)
    (hSp : IsPSp4 2 n (↥K ⧸ Subgroup.center ↥K)) : Setting436Sp4 G T M L n I H K t := by
  classical
  have hn : 2 ≤ n := sk.base.hyp.two_le
  have hZ : Subgroup.center ↥K = ⊥ := hMult ↥K n hn hK.2.2 hSp
  have hSpK : IsPSp4 2 n ↥K :=
    isPSp4_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      hSp
  obtain ⟨n', -, hmax, hLP, -, halt⟩ := hC1
  have hHM : H ⊓ M ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans sk.base.hyp.normal
  have hcl : conjClosure L (H ⊓ M) = L :=
    le_antisymm (conjClosure_le fun _ hs x hx => (Subgroup.mem_normalizer_iff.mp (hHM hs) x).mp hx)
      (le_conjClosure L _)
  rw [hcl] at hLP halt
  set P := H ⊓ M ⊓ K with hP
  set S := T ⊓ H ⊓ K with hS
  set V := v432 T M L with hV
  have hSHM : IsSylowTwoOf (T ⊓ H) (H ⊓ M) := sk.base.isSylowTwoOf_S h37 h38 h39
  have hHMP : H ⊓ M ≤ Subgroup.normalizer (P : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (sk.le_normalizer hx)
  have hSP : IsSylowTwoOf S P := by
    have h := A4.isSylowTwoOf_inf_normal hSHM (inf_le_left : P ≤ H ⊓ M) hHMP
    have e : T ⊓ H ⊓ P = S := by
      ext x
      simp only [hP, hS, Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨hxT, hxH⟩, -, hxK⟩
        exact ⟨⟨hxT, hxH⟩, hxK⟩
      · rintro ⟨⟨hxT, hxH⟩, hxK⟩
        exact ⟨⟨hxT, hxH⟩, ⟨hxH, sk.base.hyp.T_le hxT⟩, hxK⟩
    rwa [e] at h
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  have hVZ : V ≤ omegaOneCenterOf Rp := sk.base.hyp421.V_le sk.base.hyp.normal
  have hV2 : IsPGroup 2 V :=
    (sk.base.hyp.sylow.1.to_le inf_le_left).to_le (hVZ.trans (A4.omegaOneCenterOf_le _))
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := by
    intro l hl
    apply mem_normalizer_of_map_conj_le
    rw [hV, v432, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
      (normalizer_le_normalizer_omegaOneCenterOf Rp
        ((le_sup_left.trans (sk.base.hyp421.sup_le_normalizer_Rp sk.base.hyp.normal)) hl)),
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hl)]
  have hVL : V ≤ L := sk.base.hyp421.V_le_L sk.base.hyp.normal
  have hO2L : pCoreOf 2 L ≤ Rp :=
    le_inf (sk.base.hyp421.pCoreOf_L_le_T sk.base.hyp.normal)
      (pCoreOf_le_centralizerSection sk.base.hyp.L_le)
  have hVO : V ≤ pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    refine le_inf (le_pCoreOf_of_le_normalizer 2 hVL hLV hV2) ?_
    exact (hVZ.trans ((A4.omegaOneCenterOf_le_centerOf _).trans
      (A4.centerOf_le_centralizer _))).trans (Subgroup.centralizer_le hO2L)
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hVO ha).2) b (hVO hb).1).symm
  have hLC : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    rcases halt with ⟨F, _, _, -, hnat⟩ | ⟨-, F, _, _, -, hnat⟩
    · exact not_le_centralizer_of_isNaturalSection hnat
    · exact not_le_centralizer_of_isNaturalSection hnat
  have hconcl : Sp4ParConcl n K P S V := by
    refine hPar G n K P S V hn hSpK hmax hSP ?_ hVab (hLP ▸ hLV) (hLP ▸ hLC)
    rw [← hLP]
    exact hVO.trans inf_le_left
  have hCcard : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 ^ n := by
    have h := hconcl.card_C
    rwa [sp4C, ← hLP] at h
  refine ⟨sk, hK, hZ, hLP, hconcl, ?_⟩
  rcases halt with ⟨F, _, _, -, hnat⟩ | ⟨-, F, _, _, -, hnat⟩
  ·
    exfalso
    have hcz : V ⊓ centerOf K = ⊥ := by
      refine eq_bot_iff.mpr fun c hc => ?_
      obtain ⟨hcK1, hcK2⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hc).2
      have hcZ : (⟨c, hcK1⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hcK2) g g.2)
      rw [hZ, Subgroup.mem_bot] at hcZ
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcZ)
    rw [hcz] at hnat
    have h1 : ∀ c ∈ V ⊓ Subgroup.centralizer (L : Set G), c = 1 := fun c hc =>
      eq_one_of_isNaturalSection_bot hnat hc.1 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hc.2) l hl)
    have h2 : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
      eq_bot_iff.mpr fun c hc => Subgroup.mem_bot.mpr (h1 c hc)
    rw [h2, Subgroup.card_bot] at hCcard
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · refine ⟨F, inferInstance, inferInstance, ?_, hnat⟩
    obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := hnat
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv] at hcard
    have hker : Nat.card ↥β.ker = 2 ^ n := by
      rw [hβk, ← hCcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hF2 : Nat.card (Multiplicative (Fin 2 → F)) = Fintype.card F ^ 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    rw [hker, hF2, hconcl.card_V] at hcard
    have h3 : (2 ^ n) ^ 2 = Fintype.card F ^ 2 := by
      have : 2 ^ (3 * n) = (2 ^ n) ^ 2 * 2 ^ n := by ring
      rw [this] at hcard
      exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos n) hcard
    exact ((Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h3).symm

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem T_le_normalizer_L : T ≤ Subgroup.normalizer (L : Set G) := fun _ hx =>
  s.sk.base.hyp.normal (s.sk.base.hyp.T_le hx)

theorem T_le_normalizer_V : T ≤ Subgroup.normalizer (v432 T M L : Set G) := by
  intro x hx
  apply mem_normalizer_of_map_conj_le
  rw [v432, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
    (normalizer_le_normalizer_omegaOneCenterOf _
      ((le_sup_right.trans (s.sk.base.hyp421.sup_le_normalizer_Rp s.sk.base.hyp.normal)) hx)),
    map_conj_eq_of_mem_normalizer (s.T_le_normalizer_L hx)]

theorem T_inf_L : T ⊓ L = T ⊓ H ⊓ K := by
  have hLK : L ≤ K := s.sk.L_le_K
  have hKH : K ≤ H := s.comp.1
  refine le_antisymm (le_inf (le_inf inf_le_left (inf_le_right.trans (hLK.trans hKH)))
    (inf_le_right.trans hLK)) (le_inf (inf_le_left.trans inf_le_left) ?_)
  have h := s.concl.S_le
  rwa [← s.L_eq] at h

theorem T_le_normalizer_S : T ≤ Subgroup.normalizer ((T ⊓ H ⊓ K : Subgroup G) : Set G) := by
  rw [← s.T_inf_L]
  exact fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx) (s.T_le_normalizer_L hx)

theorem T_le_normalizer_Z :
    T ≤ Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) := by
  intro x hx
  have hxS := s.T_le_normalizer_S hx
  have hxL : x ∈ Subgroup.normalizer ((perfectCore (H ⊓ M ⊓ K) : Subgroup G) : Set G) := by
    rw [← s.L_eq]
    exact s.T_le_normalizer_L hx
  apply mem_normalizer_of_map_conj_le
  rw [sp4Z, Subgroup.map_commutator,
    map_conj_eq_of_mem_normalizer (mem_normalizer_inf (s.T_le_normalizer_V hx)
      (A4.mem_normalizer_centralizer hxS)),
    map_conj_eq_of_mem_normalizer (mem_normalizer_inf hxL
      (Subgroup.le_normalizer hxS))]

theorem false_of_le_normalizer_K (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : False := by
  have sk := s.sk
  have hK := s.comp
  set R₀ := T ⊓ Subgroup.centralizer (K : Set G) with hR₀
  have h414 := lemma_4_1_4_five (sk.base.hyp4_2_3N.hyp4_1_1 h37 h38 h39) sk.base.isSigma
    sk.base.isGammaStar sk.base.inH sk.base.not_le_M
  have hO2HR : pCoreOf 2 H ≤ pCoreOf 2 I := h414.2.2.1.trans h414.2.2.2
  have hO2HT : pCoreOf 2 H ≤ T := hO2HR.trans (sk.base.pCoreOf_le_S.trans inf_le_left)
  have hO2H1 : pCoreOf 2 H ≠ ⊥ := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal sk.base.inM.1.1
  have hKcent : ⁅K, pCoreOf 2 H⁆ = ⊥ :=
    commutator_eq_bot_of_isComponentOf hK (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H)
      (pCoreOf_isPGroup 2 H)
  have hO2HC : pCoreOf 2 H ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKcent)
  have hR₀1 : R₀ ≠ ⊥ := fun h => hO2H1 (le_bot_iff.mp (h ▸ le_inf hO2HT hO2HC))
  have hR₀2 : IsPGroup 2 R₀ := (sk.base.hyp.sylow.1).to_le inf_le_left
  have hX : L ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) := by
    refine _root_.sup_le (fun l hl => ?_) (fun x hx => ?_)
    · refine A4.mem_normalizer_of_conj_mem fun r hr => ?_
      have h1 : l * r = r * l :=
        (Subgroup.mem_centralizer_iff.mp hr.2) l (sk.L_le_K hl)
      rw [h1, mul_inv_cancel_right]
      exact hr
    · exact mem_normalizer_inf (Subgroup.le_normalizer hx)
        (A4.mem_normalizer_centralizer (hTK hx))
  have hU := (sk.base.hyp421.isUniqueM_sup h37 h38 h39).1
  have hNM : Subgroup.normalizer (R₀ : Set G) ≤ M := isUniqueM_normalizer_le hU hR₀1 hR₀2 hX
  have hKC : K ≤ Subgroup.centralizer (R₀ : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  exact sk.not_le (le_inf hK.1 (hKC.trans ((Subgroup.centralizer_le_normalizer _).trans hNM)))

theorem false_of_le_normalizer_K₂ (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hT : T ≤ Subgroup.normalizer
      (sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) : False := by
  refine s.false_of_le_normalizer_K h37 h38 h39 fun x hx => ?_
  have hK : K = L ⊔ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) := by
    have h := s.concl.sup_eq
    rw [← s.L_eq] at h
    exact h.symm
  apply mem_normalizer_of_map_conj_le
  rw [hK, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (s.T_le_normalizer_L hx),
    map_conj_eq_of_mem_normalizer (hT hx)]

end Setting436Sp4

@[expose] def Step436Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting436Sp4 G T M L n I H K t →
      T ≤ Subgroup.normalizer (sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)

theorem lemma436Sp4_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hMult : Sp4MultTrivial) (hPar : Sp4ParabolicFacts) (hStep : Step436Sp4) :
    Lemma436Sp4 := by
  intro G _ _ T M L n I H K t sk hK _ hC1 hSp
  have s := setting436Sp4_of h37 h38 h39 hMult hPar sk hK hC1 hSp
  exact s.false_of_le_normalizer_K₂ h37 h38 h39 (hStep G T M L n I H K t s)

end CFSG.Quasithin.H13.Ch4
