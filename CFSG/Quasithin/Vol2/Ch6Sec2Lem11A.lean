module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem mem_centralizer_of_odd_ch611 {A B : Subgroup G} (hB : ∀ b ∈ B, b ^ 2 = 1) {g : G}
    {o : ℕ} (ho : Odd o) (hgo : g ^ o = 1) (hgB : ∀ b ∈ B, g * b = b * g)
    (hgA : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ B) : g ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨b, hbdef⟩ : ∃ b, b = g * a * g⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hb : b ∈ B := hbdef ▸ hgA a ha
  have hga : g * a * g⁻¹ = b * a := by rw [hbdef]; group
  have hk : ∀ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = b ^ k * a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hgb : g * b ^ k * g⁻¹ = b ^ k := by
        rw [hgB _ (B.pow_mem hb k), mul_inv_cancel_right]
      calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (b ^ k * a) * g⁻¹ := by rw [ih]
        _ = (g * b ^ k * g⁻¹) * (g * a * g⁻¹) := by group
        _ = b ^ (k + 1) * a := by rw [hgb, hga, pow_succ]; group
  have h1 := hk o
  rw [hgo, one_mul, inv_one, mul_one] at h1
  have hbo : b ^ o = 1 := by
    have := congrArg (· * a⁻¹) h1
    simpa using this.symm
  obtain ⟨m, rfl⟩ := ho
  have hb1 : b = 1 := by
    have : b ^ (2 * m + 1) = (b ^ 2) ^ m * b := by rw [pow_succ, pow_mul]
    rw [this, hB b hb, one_pow, one_mul] at hbo
    exact hbo
  have hga' : g * a * g⁻¹ = a := by rw [hga, hb1, one_mul]
  calc a * g = (g * a * g⁻¹) * g := by rw [hga']
    _ = g * a := by group

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem ZS_le_centralizerMod_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    ch6ZS T L V ≤ V ⊓ centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
      (conjClosure (ch6ZS T L V) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set H := Subgroup.centralizer (Z : Set G) with hH
  have hV := h.toHyp611.isElemAbelian
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  obtain ⟨⟨-, hUQ, hcomm⟩, -, -, -⟩ := h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  intro y hy
  have hyH : y ∈ H := Subgroup.mem_centralizer_iff.mpr fun w hw =>
    B2F.isElemAbelian_comm hV (hZZS hw).1 hy.1
  refine ⟨hy.1, mem_centralizerMod.mpr ⟨hyH, Subgroup.centralizer_le_normalizer _ hyH,
    fun u hu => ?_⟩⟩
  have := Subgroup.commutator_mem_commutator (hUQ (le_conjClosure _ H hy)) hu
  rw [Subgroup.commutator_comm] at this
  have h1 := hcomm this
  rwa [commutatorElement_def] at h1

theorem le_centralizerMod_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      centralizerMod (quasithinOmegaOneCenter T)
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
        (conjClosure (ch6ZS T L V) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) := by
  obtain ⟨⟨-, -, hcomm⟩, -, -, -⟩ := h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  intro q hq
  refine mem_centralizerMod.mpr ⟨pCoreOf_le 2 _ hq,
    Subgroup.centralizer_le_normalizer _ (pCoreOf_le 2 _ hq), fun u hu => ?_⟩
  have := Subgroup.commutator_mem_commutator hq hu
  rw [Subgroup.commutator_comm] at this
  have h1 := hcomm this
  rwa [commutatorElement_def] at h1

theorem oTwoUpper_centralizerMod_eq_bot (h331 : Stmt3_3_1) (h432 : Stmt4_3_2)
    (h512 : Stmt5_1_2) (h614 : Stmt6_1_4) (h615 : Stmt6_1_5)
    (hYV : oTwoUpper (centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
      (conjClosure (ch6ZS T L V) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))) ≤
        Subgroup.centralizer (V : Set G)) :
    oTwoUpper (centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
      (conjClosure (ch6ZS T L V) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))) =
        ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T with hZ
  set H := Subgroup.centralizer (Z : Set G) with hH
  set U := conjClosure (ch6ZS T L V) H with hU
  obtain ⟨⟨hchar, -, -⟩, ⟨hCN, hNM, -⟩, -, -⟩ :=
    h.lemma_6_2_10_one_three_five h331 h432 h512 h614 h615
  set C := centralizerMod Z H U with hC
  have hCH : C ≤ H := centralizerMod_le_left _ _ _
  have hCHM : C ≤ H ⊓ M := fun c hc => ⟨hCH hc, hNM (hCN hc)⟩
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizerMod_ch62 (Subgroup.centralizer_le_normalizer _ hg)
      (Subgroup.le_normalizer hg) (le_normalizer_conjClosure _ H hg)
  by_contra hYne
  set Y := oTwoUpper C with hYdef
  have hYC : Y ≤ C := oTwoUpper_le C
  have hYM : Y ≤ M := hYC.trans (hCHM.trans inf_le_right)
  have hYL : ∀ y ∈ Y, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
    intro y hy l hl
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := h.normal (hYM hy)
    have h1 : l * y * l⁻¹ * y⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hyN l⁻¹).mp (L.inv_mem hl)
      have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
      rw [e]
      exact L.mul_mem hl this
    have h2 : l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have hlC : l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer_ch62
          (h.toHyp611.L_le_normalizer hl)) y).mp (hYV hy)
      exact Subgroup.mul_mem _ hlC (Subgroup.inv_mem _ (hYV hy))
    exact h.toHyp611Nat.mem_pCoreOf_of_rho_eq_one (ℓ := ⟨_, h1⟩)
      ((h.data.mem_ker_rho_iff _).mpr h2)
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    hHC.trans (normalizer_le_normalizer_oTwoUpper C)
  have hZV : Z ≤ V := h.omega_le_V h331 h432 h512 h614 h615
  have hO2LH : pCoreOf 2 L ≤ H := fun x hx =>
    Subgroup.centralizer_le (show (Z : Set G) ⊆ V from hZV)
      (h.toHyp611.pCoreOf_le_centralizer hx)
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    exact mem_normalizer_oTwoUpper_ch62 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (hO2LH.trans hHY) (fun y hy => hYL y hy l hl)
      (fun y hy => by simpa using hYL y hy l⁻¹ (L.inv_mem hl))
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hTH : T ≤ H := fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  have hYchar : CharTwo Y := A4.charTwo_of_normal (hYC.trans hCH) hHY hchar
  have hY2 : pCoreOf 2 Y ≠ ⊥ := by
    intro h0
    apply hYne
    refine le_bot_iff.mp fun y hy => ?_
    have hyC : y ∈ Y ⊓ Subgroup.centralizer (pCoreOf 2 Y : Set G) := by
      refine ⟨hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      rw [h0] at hx
      rw [Subgroup.mem_bot.mp hx, one_mul, mul_one]
    have := hYchar hyC
    rwa [h0] at this
  have hNO : Subgroup.normalizer (pCoreOf 2 Y : Set G) ≤ M :=
    le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM h432)
      (sup_le (hLY.trans (normalizer_le_normalizer_pCoreOf 2 Y))
        ((hTH.trans hHY).trans (normalizer_le_normalizer_pCoreOf 2 Y)))
      ⟨pCoreOf 2 Y, hY2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
  exact h.not_centralizer_omega_le h331 h615 fun x hx =>
    hNO (normalizer_le_normalizer_pCoreOf 2 Y (hHY hx))

theorem step_a_ch611 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10)
    (h4 : (V ⊓ centralizerMod (quasithinOmegaOneCenter T)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
      (conjClosure (ch6ZS T L V)
        (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))).relIndex V ≠ 2) :
    let Z := quasithinOmegaOneCenter T
    let H := Subgroup.centralizer (Z : Set G)
    let U := conjClosure (ch6ZS T L V) H
    V ⊓ centralizerMod Z H U = ch6ZS T L V ∧ V ⊓ U = ch6ZS T L V ∧ ⁅V, U⁆ ≤ ch6ZS T L V ∧
      centralizerMod Z H U = pCoreOf 2 H := by
  intro Z H U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.toHyp611.isElemAbelian
  have hZZS := h.omega_le_ZS h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hV16 : Nat.card V = 16 := by
    rw [h.natural.card_eq]
    norm_num
  obtain ⟨⟨-, hUQ, -⟩, ⟨hCN, -, -⟩, -, hVnC, hVU⟩ := h6210 G T M L V h
  set C := centralizerMod Z H U with hC
  have hZSC : ch6ZS T L V ≤ V ⊓ C := h.ZS_le_centralizerMod_ch611 h331 h432 h512 h614 h615
  have hQC : pCoreOf 2 H ≤ C := h.le_centralizerMod_ch611 h331 h432 h512 h614 h615
  have h4' : (V ⊓ C).relIndex V ≠ 2 := h4
  have hVC : V ⊓ C = ch6ZS T L V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hZSC
    have hdvd : Nat.card ↥(V ⊓ C) ∣ 16 := hV16 ▸ Subgroup.card_dvd_of_le inf_le_left
    have hge : 4 ≤ Nat.card ↥(V ⊓ C) := hZS4 ▸ Subgroup.card_le_of_le hZSC
    have hne : Nat.card ↥(V ⊓ C) ≠ 16 := by
      intro h16
      apply hVnC
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : V ⊓ C ≤ V) (by rw [h16, hV16])
      rw [← this]
      exact inf_le_right
    have hne8 : Nat.card ↥(V ⊓ C) ≠ 8 := by
      intro h8
      apply h4'
      have h1 := Subgroup.relIndex_mul_card (H := V ⊓ C) (K := V)
      rw [inf_of_le_left (inf_le_left : V ⊓ C ≤ V), h8, hV16] at h1
      omega
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    have hcases : Nat.card ↥(V ⊓ C) = 1 ∨ Nat.card ↥(V ⊓ C) = 2 ∨ Nat.card ↥(V ⊓ C) = 4 ∨
        Nat.card ↥(V ⊓ C) = 8 ∨ Nat.card ↥(V ⊓ C) = 16 := by
      rw [h16] at hdvd
      obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      interval_cases i <;> simp only [Nat.reducePow, pow_zero] at hik <;> omega
    rw [hZS4]
    omega
  have hUC : U ≤ C := hUQ.trans hQC
  have hVU' : V ⊓ U = ch6ZS T L V := by
    apply le_antisymm
    · rw [← hVC]
      exact inf_le_inf_left _ hUC
    · exact le_inf (inf_le_left) (le_conjClosure _ H)
  refine ⟨hVC, hVU', hVU'.symm ▸ hVU, ?_⟩
  have hZsq : ∀ b ∈ Z, b ^ 2 = 1 := fun b hb => by
    have h1 : orderOf b ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (s := Z) hb
      rwa [hZ2] at this
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hZSsq : ∀ b ∈ ch6ZS T L V, b ^ 2 = 1 := fun b hb => hV.2 b hb.1
  have hCH : C ≤ H := centralizerMod_le_left _ _ _
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizerMod_ch62 (Subgroup.centralizer_le_normalizer _ hg)
      (Subgroup.le_normalizer hg) (le_normalizer_conjClosure _ H hg)
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hTH : T ≤ H := fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm
  have hVH : V ≤ H := h.toHyp611.le_T.trans hTH
  have hodd : ∀ x ∈ C, Odd (orderOf x) → x ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx hxo
    have hxU : x ∈ Subgroup.centralizer (U : Set G) :=
      mem_centralizer_of_odd_ch611 hZsq hxo (pow_orderOf_eq_one x)
        (fun b hb => (Subgroup.mem_centralizer_iff.mp (hCH hx) b hb).symm)
        (fun a ha => (mem_centralizerMod.mp hx).2.2 a ha)
    refine mem_centralizer_of_odd_ch611 hZSsq hxo (pow_orderOf_eq_one x)
      (fun b hb => (Subgroup.mem_centralizer_iff.mp hxU b (le_conjClosure _ H hb)).symm)
      (fun a ha => ?_)
    rw [← hVC]
    refine ⟨?_, ?_⟩
    · have hxa : x * a * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hCN hx) a).mp ha
      exact V.mul_mem hxa (V.inv_mem ha)
    · have hxa : a * x⁻¹ * a⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hHC (hVH ha)) x⁻¹).mp (C.inv_mem hx)
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact C.mul_mem hx hxa
  have hY : oTwoUpper C = ⊥ := h.oTwoUpper_centralizerMod_eq_bot h331 h432 h512 h614 h615
    ((Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2)
  refine le_antisymm (le_pCoreOf_of_le_normalizer 2 hCH hHC ?_) hQC
  refine A4.isPGroup_two_of_odd_order_eq_one fun c hc hodd' => ?_
  have : c ∈ oTwoUpper C := mem_oTwoUpper_of_odd hc hodd'
  rw [hY] at this
  exact Subgroup.mem_bot.mp this

end Hyp6Sec2

end CFSG.Quasithin.H13
