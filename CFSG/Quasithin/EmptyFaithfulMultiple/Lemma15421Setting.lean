module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15419
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15423
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.F6Solvable

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace L15421

section GroupTheory

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_of_odd_of_mem_mul [Finite G] {K N : Subgroup G} (hK : IsPGroup 2 K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ K ⊔ N)
    (ho : Odd (orderOf x)) : x ∈ N := by
  have hx' : x ∈ ((K ⊔ N : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K N hKN] at hx'
  obtain ⟨k, hk, n, hn, rfl⟩ := hx'
  obtain ⟨e', he⟩ := hK ⟨k, hk⟩
  have hke : k ^ 2 ^ e' = 1 := by simpa using congrArg Subtype.val he
  have hk' : k * n * k⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hKN hk) n).mp hn
  have e : k * n = k * n * k⁻¹ * k := by group
  change Odd (orderOf (k * n)) at ho
  change k * n ∈ N
  rw [e] at ho ⊢
  exact B2F.mem_of_odd_orderOf_mul hk' (hKN hk) ⟨e', hke⟩ ho

end GroupTheory

section Factors

variable {G : Type} [Group G] [Finite G] {T M X X₁ X₂ : Subgroup G}

theorem pCoreOf_le_centralizer_vZ (hyp : MultipleCentralizerHypothesis G T) (hM : InM T M) :
    pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hyp.qtke.2.1 M hM.1.1 ⟨S, hSM⟩
  have h1 := (conjClosure_le_centerOf_pCoreOf M S hSM hF (Z := quasithinOmegaOneCenter T)
    (by rw [hS])).1
  have h2 : VZ T M ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := fun v hv => (h1 hv).2
  exact Subgroup.le_centralizer_iff.mp h2

theorem sixTwo_inf_centralizer_eq_pCoreOf (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) (hM : InM T M) (hX : IsYFamily T X) (hXM : X ≤ M)
    (h : IsSixTwoData T M X X₁ X₂) :
    X₁ ⊓ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) = pCoreOf 2 X₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := h.factor_left
  have hV := isElemAbelian_VZ_of_inM hyp hM
  have hXV : X ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hXM.trans (le_normalizer_conjClosure _ _)
  set C := X₁ ⊓ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) with hC
  have hO : pCoreOf 2 X₁ ≤ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) :=
    ((hf.pCoreOf_le_pCoreOf h12 hM hX hXM).trans (pCoreOf_le_centralizer_vZ hyp hM)).trans
      (Subgroup.centralizer_le (hf.commutator_le_vZ hXM))
  have hle : pCoreOf 2 X₁ ≤ C := le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X₁) hO
  have hne : C.relIndex X₁ ≠ 1 := by
    intro h1
    have h2 : X₁ ≤ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) :=
      (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    have h3 := commutator_inf_centralizer_eq_bot_of_sixTwoData hV hXV h
    rw [inf_eq_left.mpr (Subgroup.le_centralizer_iff.mp h2)] at h3
    have h4 := hf.card_commutator
    rw [h3, Subgroup.card_bot] at h4
    omega
  have htower := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X₁) C X₁ hle inf_le_left
  rw [hf.relIndex_eq] at htower
  have hdvd : C.relIndex X₁ ∣ 3 := ⟨(pCoreOf 2 X₁).relIndex C, by rw [← htower, mul_comm]⟩
  have ha : (pCoreOf 2 X₁).relIndex C = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd h1 hne
    · rw [h1] at htower
      omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp ha) hle

theorem sixTwo_mem_of_odd (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (hM : InM T M) (hX : IsYFamily T X) (hXM : X ≤ M) (h : IsSixTwoData T M X X₁ X₂) {x : G}
    (hx : x ∈ X) (hxc : x ∈ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G))
    (ho : Odd (orderOf x)) : x ∈ X₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := sixTwo_inf_centralizer_eq_pCoreOf hyp h12 hM hX hXM h
  have hXV : X ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hXM.trans (le_normalizer_conjClosure _ _)
  have hC₂ : X₂ ≤ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (commutator_le_centralizer_of_sixTwoData h.symm hXV)
  have hXeq : X = X₁ ⊔ X₂ := h.1
  have hXN₂ : X ≤ Subgroup.normalizer (X₂ : Set G) := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hX₁N : X₁ ≤ Subgroup.normalizer (X₂ : Set G) := (hXeq ▸ le_sup_left).trans hXN₂
  have hx' : x ∈ ((X₁ ⊔ X₂ : Subgroup G) : Set G) := hXeq ▸ hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X₁ X₂ hX₁N] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
  have hac : a ∈ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) := by
    have e : a = x * b⁻¹ := by rw [← hab]; group
    rw [e]
    exact Subgroup.mul_mem _ hxc (Subgroup.inv_mem _ (hC₂ hb))
  have haO : a ∈ pCoreOf 2 X₁ := hO ▸ ⟨ha, hac⟩
  have hON : pCoreOf 2 X₁ ≤ Subgroup.normalizer (X₂ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X₁).trans hX₁N
  rw [← hab] at ho ⊢
  exact mem_of_odd_of_mem_mul (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X₁) hON
    (Subgroup.mul_mem_sup haO hb) ho

theorem sixTwo_normalizer_le (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (hM : InM T M) (hX : IsYFamily T X) (hXM : X ≤ M) (h : IsSixTwoData T M X X₁ X₂) :
    T ⊓ Subgroup.normalizer (X₁ : Set G) ≤ Subgroup.normalizer (X₂ : Set G) := by
  rintro t ⟨htT, htN⟩
  have htM : t ∈ M := hM.2 htT
  have htX : t ∈ Subgroup.normalizer (X : Set G) := ((h12 M hM).2 X hX hXM).1 htM
  have htV : t ∈ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _ htM
  have htV₁ : t ∈ Subgroup.normalizer
      (Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) : Set G) :=
    B2F.normalizer_le_normalizer_centralizer _ (A4.mem_normalizer_commutator htV htN)
  have hXV : X ≤ Subgroup.normalizer (VZ T M : Set G) :=
    hXM.trans (le_normalizer_conjClosure _ _)
  have hC₂ : X₂ ≤ Subgroup.centralizer ((⁅VZ T M, X₁⁆ : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (commutator_le_centralizer_of_sixTwoData h.symm hXV)
  have hX₂X : X₂ ≤ X := h.1 ▸ le_sup_right
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hx' : x ∈ oTwoUpper X₂ := h.2.2.1 ▸ hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨hy₂, hyo⟩ := hy
    refine sixTwo_mem_of_odd hyp h12 hM hX hXM h ?_ ?_ ?_
    · exact (Subgroup.mem_normalizer_iff.mp htX y).mp (hX₂X hy₂)
    · exact (Subgroup.mem_normalizer_iff.mp htV₁ y).mp (hC₂ hy₂)
    · rw [gold_orderOf_conj]
      exact hyo
  | one => simp
  | mul y z _ _ ihy ihz =>
    have e : t * (y * z) * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ih =>
    have e : t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

end Factors

section Three

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_mul_eq_three {a b : ℕ} (h : a * b = 3) (hb : b ≠ 1) : a = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left a h) with h1 | h1
  · exact absurd h1 hb
  · rw [h1] at h
    omega

theorem inf_eq_pCoreOf_of_le {L T₀ : Subgroup G} (hT₀ : IsPGroup 2 T₀) (hO : pCoreOf 2 L ≤ T₀)
    (h3 : (pCoreOf 2 L).relIndex L = 3) : L ⊓ T₀ = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 L ≤ L ⊓ T₀ := le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hO
  have htower := Subgroup.relIndex_mul_relIndex (pCoreOf 2 L) (L ⊓ T₀) L hle inf_le_left
  rw [h3] at htower
  have hne : (L ⊓ T₀).relIndex L ≠ 1 := by
    intro h1
    have hLT : L ≤ T₀ := (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hT₀.to_le hLT)
    have hc := Subgroup.relIndex_mul_card (pCoreOf 2 L) L
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L), h3, hk] at hc
    have h3k : 3 ∣ 2 ^ k := ⟨_, hc.symm⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3k
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (eq_one_of_mul_eq_three htower hne)) hle

theorem relIndex_sup_eq_three {L T₀ : Subgroup G} (hTN : T₀ ≤ Subgroup.normalizer (L : Set G))
    (hinf : L ⊓ T₀ = pCoreOf 2 L) (h3 : (pCoreOf 2 L).relIndex L = 3) :
    T₀.relIndex (L ⊔ T₀) = 3 := by
  rw [sup_comm]
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hTN
  have h2 := Subgroup.relIndex_mul_card L (T₀ ⊔ L)
  have h4 := Subgroup.relIndex_mul_card L T₀
  have h5 := Subgroup.relIndex_mul_card (pCoreOf 2 L) L
  have h6 := Subgroup.relIndex_mul_card T₀ (T₀ ⊔ L)
  rw [inf_eq_left.mpr le_sup_right, h1] at h2
  rw [hinf] at h4
  rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L), h3] at h5
  rw [inf_eq_left.mpr le_sup_left] at h6
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h6, ← h2, ← h5, ← h4]
  ring

omit [Finite G] in
theorem commutator_le_inf_of_le_normalizer {L K : Subgroup G}
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) (hLK : L ≤ Subgroup.normalizer (K : Set G)) :
    ⁅L, K⁆ ≤ L ⊓ K := by
  rw [Subgroup.commutator_le]
  intro l hl k hk
  rw [commutatorElement_def]
  constructor
  · have h : k * l⁻¹ * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hKL hk) l⁻¹).mp (L.inv_mem hl)
    have e : l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) := by group
    rw [e]
    exact L.mul_mem hl h
  · have h : l * k * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hLK hl) k).mp hk
    exact K.mul_mem h (K.inv_mem hk)

theorem quotient_pCore_iso {L T₀ R : Subgroup G} (hT₀ : IsPGroup 2 T₀)
    (hTN : T₀ ≤ Subgroup.normalizer (L : Set G)) (hinf : L ⊓ T₀ = pCoreOf 2 L)
    (h3 : (pCoreOf 2 L).relIndex L = 3) (hRT : R ≤ T₀) (hLR : ⁅L, R⁆ = L) :
    Nonempty (↥(L ⊔ T₀) ⧸ CFSG.Open.pCore 2 ↥(L ⊔ T₀) ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := L ⊔ T₀ with hK
  have hT₀K : T₀ ≤ K := le_sup_right
  set H : Subgroup ↥K := T₀.subgroupOf K with hH
  have hidx : H.index = 3 := relIndex_sup_eq_three hTN hinf h3
  have hH2 : IsPGroup 2 H := hT₀.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀K).symm
  have hcore : H.normalCore = CFSG.Open.pCore 2 ↥K := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCore 2 (Subgroup.normalCore_normal H)
        (hH2.to_le H.normalCore_le)
    · have hS : CFSG.Open.pCore 2 ↥K ≤ H := by
        have hodd : ¬ 2 ∣ H.index := by rw [hidx]; decide
        have := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2).le_sylow_of_normal
          (hH2.toSylow hodd)
        simpa using this
      exact Subgroup.normal_le_normalCore.mpr hS
  rcases gold_normalCore_quotient_equiv hidx with ⟨h3', -⟩ | ⟨-, ⟨e⟩⟩
  · exfalso
    have hHn : H ≤ H.normalCore := by
      have h := Subgroup.relIndex_mul_index H.normalCore_le
      rw [hidx, h3'] at h
      exact Subgroup.relIndex_eq_one.mp (by omega)
    have hLN : L ≤ Subgroup.normalizer (T₀ : Set G) := by
      intro l hl
      refine mem_normalizer_of_conj_mem fun t ht => ?_
      have hlK : l ∈ K := (le_sup_left : L ≤ K) hl
      have ht' : (⟨t, hT₀K ht⟩ : ↥K) ∈ H.normalCore := hHn ht
      have := (Subgroup.normalCore_normal H).conj_mem _ ht' ⟨l, hlK⟩
      exact H.normalCore_le this
    have hc := commutator_le_inf_of_le_normalizer hTN hLN
    have hLO : L ≤ pCoreOf 2 L := by
      rw [← hinf]
      calc L = ⁅L, R⁆ := hLR.symm
        _ ≤ ⁅L, T₀⁆ := Subgroup.commutator_mono le_rfl hRT
        _ ≤ L ⊓ T₀ := hc
    have h1 : (pCoreOf 2 L).relIndex L = 1 := Subgroup.relIndex_eq_one.mpr hLO
    omega
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans e⟩

end Three

section Setting

variable {G : Type} [Group G] {T : Subgroup G}

theorem sixTwoFactor_pCoreOf_le_baum [Finite G] {M W L : Subgroup G} (h12 : Stmt15412 G T)
    (hM : InM T M) (hW : IsYFamily T W) (hWM : W ≤ M) (hf : IsSixTwoFactor T M W L) :
    pCoreOf 2 L ≤ baum T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMN, -, -, -, hSyl, -⟩ := (h12 M hM).2 W hW hWM
  have hLW : pCoreOf 2 L ≤ pCoreOf 2 W :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hf.le)
      (hf.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hSW : baum T ≤ Subgroup.normalizer (W : Set G) := (inf_le_left.trans hM.2).trans hMN
  have hWS : pCoreOf 2 W ≤ pCoreOf 2 (W ⊔ baum T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 W).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 W)
        (hSW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W)
  exact (hLW.trans hWS).trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hSyl)

variable (s : Setting15419 G T)

theorem factor_L₁ : IsSixTwoFactor T s.M₁ s.X s.L₁ := by
  rcases s.choice₁ with h | h <;> rw [h]
  · exact s.dataX.factor_left
  · exact s.dataX.factor_right

theorem factor_L₂ : IsSixTwoFactor T s.M₂ s.Y s.L₂ := by
  rcases s.choice₂ with h | h <;> rw [h]
  · exact s.dataY.factor_left
  · exact s.dataY.factor_right

theorem commutator_L₁ : ⁅s.L₁, thompsonJ T⁆ = s.L₁ := by
  rcases s.choice₁ with h | h <;> rw [h]
  · exact s.dataX.2.2.2.2.2.2.2.2.2.1
  · exact s.dataX.2.2.2.2.2.2.2.2.2.2.1

theorem commutator_L₂ : ⁅s.L₂, thompsonJ T⁆ = s.L₂ := by
  rcases s.choice₂ with h | h <;> rw [h]
  · exact s.dataY.2.2.2.2.2.2.2.2.2.1
  · exact s.dataY.2.2.2.2.2.2.2.2.2.2.1

theorem T₀_le : s.T₀ ≤ T := inf_le_left.trans inf_le_left

theorem baum_le_T₀ : baum T ≤ s.T₀ :=
  le_inf (le_inf inf_le_left s.dataY.2.2.2.2.2.2.2.2.2.2.2.1) s.dataX.2.2.2.2.2.2.2.2.2.2.2.1

theorem thompsonJ_le_T₀ : thompsonJ T ≤ s.T₀ := (B2F.thompsonJ_le_baum T).trans (baum_le_T₀ s)

theorem T₀_le_normalizer_L₁ [Finite G] (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) :
    s.T₀ ≤ Subgroup.normalizer (s.L₁ : Set G) := by
  rcases s.choice₁ with h | h <;> rw [h]
  · exact inf_le_right
  · exact (le_inf (T₀_le s) inf_le_right).trans
      (sixTwo_normalizer_le hyp h12 s.inM₁ s.famX s.le_X s.dataX)

theorem T₀_le_normalizer_L₂ [Finite G] (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) :
    s.T₀ ≤ Subgroup.normalizer (s.L₂ : Set G) := by
  rcases s.choice₂ with h | h <;> rw [h]
  · exact inf_le_left.trans inf_le_right
  · exact (le_inf (T₀_le s) (inf_le_left.trans inf_le_right)).trans
      (sixTwo_normalizer_le hyp h12 s.inM₂ s.famY s.le_Y s.dataY)

theorem isPGroup_T₀ [Finite G] (hyp : MultipleCentralizerHypothesis G T) : IsPGroup 2 s.T₀ :=
  hyp.sylow.1.to_le (T₀_le s)

theorem inf_T₀_L₁ [Finite G] (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) :
    s.L₁ ⊓ s.T₀ = pCoreOf 2 s.L₁ :=
  inf_eq_pCoreOf_of_le (isPGroup_T₀ s hyp)
    ((sixTwoFactor_pCoreOf_le_baum h12 s.inM₁ s.famX s.le_X (factor_L₁ s)).trans (baum_le_T₀ s))
    (factor_L₁ s).relIndex_eq

theorem inf_T₀_L₂ [Finite G] (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) :
    s.L₂ ⊓ s.T₀ = pCoreOf 2 s.L₂ :=
  inf_eq_pCoreOf_of_le (isPGroup_T₀ s hyp)
    ((sixTwoFactor_pCoreOf_le_baum h12 s.inM₂ s.famY s.le_Y (factor_L₂ s)).trans (baum_le_T₀ s))
    (factor_L₂ s).relIndex_eq

theorem relIndex_T₀_G₁ [Finite G] (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) :
    s.T₀.relIndex s.G₁ = 3 :=
  relIndex_sup_eq_three (T₀_le_normalizer_L₁ s hyp h12) (inf_T₀_L₁ s hyp h12)
    (factor_L₁ s).relIndex_eq

theorem G₁_inf_G₂ [Finite G] (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (h19 : Stmt15419 G T) : s.G₁ ⊓ s.G₂ = s.T₀ := by
  have hle : s.T₀ ≤ s.G₁ ⊓ s.G₂ := le_inf le_sup_right le_sup_right
  have htower := Subgroup.relIndex_mul_relIndex s.T₀ (s.G₁ ⊓ s.G₂) s.G₁ hle inf_le_left
  rw [relIndex_T₀_G₁ s hyp h12] at htower
  have hne : (s.G₁ ⊓ s.G₂).relIndex s.G₁ ≠ 1 := by
    intro h1
    have hG : s.G₁ ≤ s.G₂ := (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
    have hG₂M : s.G₂ ≤ s.M₂ :=
      sup_le ((factor_L₂ s).le.trans s.le_Y) ((T₀_le s).trans s.inM₂.2)
    exact (h19 s).2.2.2.2.1 ((le_sup_left.trans hG).trans hG₂M)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (eq_one_of_mul_eq_three htower hne)) hle

theorem isGoldschmidtTripleIn [Finite G] (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T)
    (h19 : Stmt15419 G T) (hT₀ : IsSylowTwoOf s.T₀ s.I) :
    F6.IsGoldschmidtTripleIn s.I s.G₁ s.G₂ := by
  refine ⟨rfl, ?_, ?_, by rw [G₁_inf_G₂ s hyp h12 h19]; exact hT₀⟩
  · exact quotient_pCore_iso (isPGroup_T₀ s hyp) (T₀_le_normalizer_L₁ s hyp h12)
      (inf_T₀_L₁ s hyp h12) (factor_L₁ s).relIndex_eq (thompsonJ_le_T₀ s) (commutator_L₁ s)
  · exact quotient_pCore_iso (isPGroup_T₀ s hyp) (T₀_le_normalizer_L₂ s hyp h12)
      (inf_T₀_L₂ s hyp h12) (factor_L₂ s).relIndex_eq (thompsonJ_le_T₀ s) (commutator_L₂ s)

end Setting

end L15421

end CFSG.Quasithin.EmptyFaithfulMultiple
