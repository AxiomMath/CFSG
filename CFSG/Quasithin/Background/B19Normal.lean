module

public import CFSG.Quasithin.Background.B19Setup

public section

namespace CFSG.Quasithin.B19

open CFSG.Quasithin

theorem card_le_card_mul_card_image {G : Type*} [Group G] [Fintype G] {β : Type*}
    [DecidableEq β] (f : G → β) (H : Subgroup G) (hf : ∀ a b, f a = f b → a⁻¹ * b ∈ H) :
    Fintype.card G ≤ Nat.card H * (Finset.univ.image f).card := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_mul_card_image Finset.univ (Nat.card H) fun y hy => ?_
  obtain ⟨b₀, -, hb₀⟩ := Finset.mem_image.1 hy
  have : Fintype H := Fintype.ofFinite H
  calc (Finset.univ.filter fun a => f a = y).card ≤ (Finset.univ : Finset H).card := by
        refine Finset.card_le_card_of_injOn
          (fun a => if h : b₀⁻¹ * a ∈ H then (⟨_, h⟩ : H) else 1) (fun a _ => Finset.mem_univ _)
          ?_
        intro a ha a' ha' heq
        simp at ha ha'
        have h1 : b₀⁻¹ * a ∈ H := hf b₀ a (hb₀.trans ha.symm)
        have h2 : b₀⁻¹ * a' ∈ H := hf b₀ a' (hb₀.trans ha'.symm)
        simp only [h1, h2, ↓reduceDIte] at heq
        have h3 := congrArg Subtype.val heq
        simpa using h3
    _ = Nat.card H := by rw [Finset.card_univ, Nat.card_eq_fintype_card]

theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h, mem_map_conj] at hy
    simpa [mul_assoc] using hy

theorem four_mul_lt_four_pow {n : ℕ} (hn : 2 ≤ n) : 4 * n < 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    omega

variable {V : Type*} [CommGroup V]

theorem map_conj_map_conj (K : Subgroup (MulAut V)) (b c : MulAut V) :
    (K.map (MulAut.conj c).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * c)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem map_eq_of_fix {U : Subgroup V} {b : MulAut V} (hb : ∀ u ∈ U, b u = u) :
    U.map b.toMonoidHom = U := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    show b u ∈ U
    rw [hb u hu]
    exact hu
  · intro hv
    exact ⟨v, hv, hb v hv⟩

variable [Finite V] {X Φ : Subgroup (MulAut V)}

namespace Setting

variable (hV : ∀ v : V, v ^ 2 = 1) (hS : Setting X Φ)
include hV hS

theorem card_iSup_commV (O : Finset (Subgroup (MulAut V)))
    (hO : ∀ K ∈ O, ∃ t ∈ tvSet X Φ, K = FOf Φ t) :
    Nat.card ↥(⨆ K ∈ O, commV K) = 4 ^ O.card := by
  classical
  induction O using Finset.induction_on with
  | empty => simp
  | insert K₀ O hK₀ ih =>
    have hO' : ∀ K ∈ O, ∃ t ∈ tvSet X Φ, K = FOf Φ t := fun K hK =>
      hO K (Finset.mem_insert_of_mem hK)
    obtain ⟨t₀, ht₀, rfl⟩ := hO K₀ (Finset.mem_insert_self _ _)
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem hK₀, pow_succ]
    have hle : (⨆ K ∈ O, commV K) ≤ fixV (FOf Φ t₀) := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨t, ht, rfl⟩ := hO' K hK
      refine hS.pair_fixV hV ht₀ ht fun h => hK₀ ?_
      rw [h]
      exact hK
    have hinf : commV (FOf Φ t₀) ⊓ (⨆ K ∈ O, commV K) = ⊥ := by
      refine le_bot_iff.1 ?_
      rw [← (hS.decomp_FOf hV ht₀).2, inf_comm]
      exact inf_le_inf_right _ hle
    have := card_sup_mul_card_inf (commV (FOf Φ t₀)) (⨆ K ∈ O, commV K)
    rw [hinf, Subgroup.card_bot, mul_one, hS.card_commV_FOf hV ht₀, ih hO'] at this
    rw [this, mul_comm]

theorem map_conj_FOf {A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) {t₁ : MulAut V}
    (ht₁ : t₁ ∈ tvSet X Φ) {a : MulAut V} (ha : a ∈ A) :
    (FOf Φ t₁).map (MulAut.conj a).toMonoidHom = FOf Φ t₁ := by
  classical
  by_contra hne
  have : Fintype ↥A := Fintype.ofFinite _
  have hAX : A ≤ X := hA.1
  have hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := hA.2.2.1.1
  set K₁ := FOf Φ t₁ with hK₁
  set V₁ := commV K₁ with hV₁
  let conjS : ↥A → Subgroup (MulAut V) := fun b => K₁.map (MulAut.conj (b : MulAut V)).toMonoidHom
  set O : Finset (Subgroup (MulAut V)) := Finset.univ.image conjS with hOdef
  have hmemO : ∀ K, K ∈ O ↔ ∃ c ∈ A, K = K₁.map (MulAut.conj c).toMonoidHom := by
    intro K
    rw [hOdef, Finset.mem_image]
    constructor
    · rintro ⟨c, -, rfl⟩
      exact ⟨c, c.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩
  have hOtv : ∀ K ∈ O, ∃ t ∈ tvSet X Φ, K = FOf Φ t := by
    intro K hK
    obtain ⟨c, hc, rfl⟩ := (hmemO K).1 hK
    exact ⟨c * t₁ * c⁻¹, hS.conj_mem_tvSet (hAX hc) ht₁, hS.FOf_conj (hAX hc) t₁⟩
  have hK₁O : K₁ ∈ O := (hmemO K₁).2 ⟨1, A.one_mem, by
    ext y
    simp⟩
  have haO : K₁.map (MulAut.conj a).toMonoidHom ∈ O := (hmemO _).2 ⟨a, ha, rfl⟩
  have hconjO : ∀ b ∈ A, ∀ K ∈ O, K.map (MulAut.conj b).toMonoidHom ∈ O := by
    intro b hb K hK
    obtain ⟨c, hc, rfl⟩ := (hmemO K).1 hK
    rw [map_conj_map_conj]
    exact (hmemO _).2 ⟨b * c, A.mul_mem hb hc, rfl⟩
  have hOcard : 2 ≤ O.card := by
    have h2 : ({K₁, K₁.map (MulAut.conj a).toMonoidHom} : Finset _) ⊆ O := by
      intro K hK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl
      · exact hK₁O
      · exact haO
    have := Finset.card_le_card h2
    rwa [Finset.card_pair (Ne.symm hne)] at this
  have hcommO : ∀ c ∈ A, commV (K₁.map (MulAut.conj c).toMonoidHom) = V₁.map c.toMonoidHom :=
    fun c _ => commV_map_conj c K₁
  set W := ⨆ K ∈ O, commV K with hW
  set A₁ := A ⊓ Subgroup.normalizer (K₁ : Set (MulAut V)) with hA₁
  set B := A ⊓ centSub V₁ with hB
  have hV₁4 : Nat.card V₁ = 4 := hS.card_commV_FOf hV ht₁
  have hV₁fix : V₁ ⊓ fixV K₁ = ⊥ := by
    rw [inf_comm]
    exact (hS.decomp_FOf hV ht₁).2
  have hA₁V₁ : ∀ b ∈ A₁, ∀ v ∈ V₁, b v ∈ V₁ := by
    intro b hb v hv
    have h1 : commV (K₁.map (MulAut.conj b).toMonoidHom) = V₁.map b.toMonoidHom :=
      hcommO b hb.1
    rw [map_conj_eq_of_mem_normalizer hb.2] at h1
    have : b v ∈ V₁.map b.toMonoidHom := ⟨v, hv, rfl⟩
    rwa [← h1] at this
  have hBA₁ : B ≤ A₁ := by
    intro b hb
    refine ⟨hb.1, ?_⟩
    show b ∈ Subgroup.normalizer (K₁ : Set (MulAut V))
    by_contra hbn
    have hK' : K₁.map (MulAut.conj b).toMonoidHom ≠ K₁ := fun h =>
      hbn (mem_normalizer_of_map_conj_eq h)
    have hbt : b * t₁ * b⁻¹ ∈ tvSet X Φ := hS.conj_mem_tvSet (hAX hb.1) ht₁
    have hFeq : FOf Φ (b * t₁ * b⁻¹) = K₁.map (MulAut.conj b).toMonoidHom :=
      (hS.FOf_conj (hAX hb.1) t₁).symm
    have hle := hS.pair_fixV hV ht₁ hbt (by rw [hFeq]; exact hK'.symm)
    rw [hFeq, hcommO b hb.1, map_eq_of_fix hb.2] at hle
    have : V₁ = ⊥ := le_bot_iff.1 (hV₁fix ▸ le_inf le_rfl hle)
    rw [this, Subgroup.card_bot] at hV₁4
    omega
  have hA₁A : A₁ ≤ A := inf_le_left
  have hA₁stab : A₁ ≤ stabSub V₁ := B1.le_stabSub_of_invariant hA₁V₁
  have hA₁B : A₁ ⊓ centSub V₁ = B := by
    apply le_antisymm
    · exact fun b hb => ⟨hb.1.1, hb.2⟩
    · exact fun b hb => ⟨hBA₁ hb, hb.2⟩
  have hWB : W ≤ fixV B := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨c, hc, rfl⟩ := (hmemO K).1 hK
    rw [hcommO c hc]
    rintro _ ⟨u, hu, rfl⟩ b hb
    show b (c u) = c u
    have h1 : b * c = c * b := hAc b hb.1 c hc
    have h2 : b (c u) = c (b u) := by
      have := congrArg (fun z : MulAut V => z u) h1
      simpa only [MulAut.mul_apply] using this
    rw [h2, hb.2 u hu]
  have hineq := B1.card_inf_fixV_le hA (inf_le_left : B ≤ A) W
  rw [inf_eq_left.2 hWB] at hineq
  have hWcard : Nat.card W = 4 ^ O.card := hS.card_iSup_commV hV O hOtv
  have hAcard : Nat.card A ≤ Nat.card A₁ * O.card := by
    have h1 := card_le_card_mul_card_image conjS (A₁.subgroupOf A) (by
      intro b c hbc
      rw [Subgroup.mem_subgroupOf]
      refine ⟨(b⁻¹ * c).2, ?_⟩
      show ((b⁻¹ * c : ↥A) : MulAut V) ∈ Subgroup.normalizer (K₁ : Set (MulAut V))
      have h2 : K₁.map (MulAut.conj ((b⁻¹ * c : ↥A) : MulAut V)).toMonoidHom = K₁ := by
        have h3 : ((b⁻¹ * c : ↥A) : MulAut V) = (b : MulAut V)⁻¹ * c := rfl
        rw [h3, ← map_conj_map_conj]
        change (conjS c).map _ = K₁
        rw [← hbc]
        change (K₁.map (MulAut.conj (b : MulAut V)).toMonoidHom).map _ = K₁
        rw [map_conj_map_conj, inv_mul_cancel]
        ext y
        simp
      exact mem_normalizer_of_map_conj_eq h2)
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁A).toEquiv] at h1
    exact h1
  have hA₁card : Nat.card (autSub A₁ V₁) * Nat.card B = Nat.card A₁ := by
    have := card_autSub_mul hA₁stab
    rwa [hA₁B] at this
  set C₁ := W ⊓ fixV K₁ with hC₁
  have hV₁W : V₁ ≤ W := le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ O) => commV K)
    K₁ hK₁O le_rfl
  have hWsplit : W ≤ V₁ ⊔ C₁ := by
    refine iSup₂_le fun K hK => ?_
    by_cases hKK : K = K₁
    · rw [hKK]
      exact le_sup_left
    · obtain ⟨t, ht, rfl⟩ := hOtv K hK
      refine le_sup_of_le_right (le_inf ?_ (hS.pair_fixV hV ht₁ ht (Ne.symm hKK)))
      exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ O) => commV K)
        (FOf Φ t) hK le_rfl
  have hYodd : Odd (Nat.card ↥(⨆ K ∈ O, K)) := by
    refine Odd.of_dvd_nat hS.odd (Subgroup.card_dvd_of_le (iSup₂_le fun K hK => ?_))
    obtain ⟨t, ht, rfl⟩ := hOtv K hK
    exact hS.FOf_le hV ht
  have hβ : (W ⊓ fixV A) ⊓ C₁ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun w hw => ?_
    obtain ⟨⟨hwW, hwA⟩, -, hwK⟩ := hw
    have hwY : w ∈ fixV (⨆ K ∈ O, K) := by
      have hle : (⨆ K ∈ O, K) ≤ MulAction.stabilizer (MulAut V) w := by
        refine iSup₂_le fun K hK => ?_
        obtain ⟨c, hc, rfl⟩ := (hmemO K).1 hK
        rintro _ ⟨k, hk, rfl⟩
        rw [MulAction.mem_stabilizer_iff]
        show (c * k * c⁻¹) w = w
        have hcw : c⁻¹ w = w := hwA c⁻¹ (A.inv_mem hc)
        simp only [MulAut.mul_apply]
        rw [hcw, hwK k hk, hwA c hc]
      intro g hg
      exact hle hg
    have hwC : w ∈ commV (⨆ K ∈ O, K) := by
      have hle : W ≤ commV (⨆ K ∈ O, K) := iSup₂_le fun K hK =>
        commV_mono (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ O) => K) K hK
          le_rfl)
      exact hle hwW
    obtain ⟨-, hinf⟩ := B1.coprime_decomp hV hYodd (M := ⊤) (fun _ _ _ _ => trivial)
    have : w ∈ (⊤ ⊓ fixV (⨆ K ∈ O, K)) ⊓ commSub ⊤ (⨆ K ∈ O, K) :=
      ⟨⟨trivial, hwY⟩, by rw [← commV_eq_commSub]; exact hwC⟩
    rw [hinf] at this
    exact this
  have hbW : ∀ b ∈ A, ∀ c ∈ W, b c ∈ W := by
    intro b hb c hc
    have hle : W ≤ W.comap b.toMonoidHom := by
      refine iSup₂_le fun K hK => ?_
      intro u hu
      show b u ∈ W
      have h1 : b u ∈ commV (K.map (MulAut.conj b).toMonoidHom) := by
        rw [commV_map_conj]
        exact ⟨u, hu, rfl⟩
      exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ O) => commV K)
        _ (hconjO b hb K hK) le_rfl h1
    exact hle hc
  have hbK : ∀ b ∈ A₁, ∀ c ∈ fixV K₁, b c ∈ fixV K₁ := by
    intro b hb c hc
    refine B1.fixV_smul_mem b (fun y hy => ?_) hc
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb.2) y).1 hy
    simpa using this
  have hγ : W ⊓ fixV A ≤ (V₁ ⊓ fixV A₁) ⊔ C₁ := by
    rintro w ⟨hwW, hwA⟩
    obtain ⟨v, hv, c, hc, rfl⟩ := Subgroup.mem_sup.1 (hWsplit hwW)
    refine Subgroup.mul_mem_sup ⟨hv, fun b hb => ?_⟩ hc
    have hbv : b v ∈ V₁ := hA₁V₁ b hb v hv
    have hbc : b c ∈ C₁ := ⟨hbW b hb.1 c hc.1, hbK b hb c hc.2⟩
    have h1 : b v * b c = v * c := by rw [← map_mul]; exact hwA b hb.1
    have h2 : b v * v⁻¹ ∈ V₁ ⊓ C₁ := by
      refine ⟨V₁.mul_mem hbv (V₁.inv_mem hv), ?_⟩
      have e : b v * v⁻¹ = c * (b c)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, h1, mul_comm]
      rw [e]
      exact C₁.mul_mem hc (C₁.inv_mem hbc)
    have hVC : V₁ ⊓ C₁ = ⊥ := le_bot_iff.1 (hV₁fix ▸ inf_le_inf_left _ inf_le_right)
    rw [hVC, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact h2
  have hCW : Nat.card ↥(W ⊓ fixV A) ≤ Nat.card ↥(V₁ ⊓ fixV A₁) := by
    have hpos : 0 < Nat.card C₁ := Nat.card_pos
    have h1 := card_sup_mul_card_inf (W ⊓ fixV A) C₁
    rw [hβ, Subgroup.card_bot, mul_one] at h1
    have h2 := card_sup_mul_card_inf (V₁ ⊓ fixV A₁) C₁
    have hinf2 : (V₁ ⊓ fixV A₁) ⊓ C₁ = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_right _ inf_le_left).trans
        (le_bot_iff.2 (le_bot_iff.1 (hV₁fix ▸ inf_le_inf_left _ inf_le_right))))
    rw [hinf2, Subgroup.card_bot, mul_one] at h2
    have h3 : Nat.card ↥((W ⊓ fixV A) ⊔ C₁) ≤ Nat.card ↥((V₁ ⊓ fixV A₁) ⊔ C₁) :=
      Subgroup.card_le_of_le (sup_le hγ le_sup_right)
    rw [h1, h2] at h3
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hE : Nat.card (autSub A₁ V₁) * Nat.card ↥(V₁ ⊓ fixV A₁) ≤ 4 := by
    have hdvd : Nat.card (autSub A₁ V₁) ∣ 6 := by
      rw [← B1.card_mulAut_of_card_four hV hV₁4]
      exact Subgroup.card_subgroup_dvd_card _
    have hle4 : Nat.card ↥(V₁ ⊓ fixV A₁) ≤ 4 := hV₁4 ▸ Subgroup.card_le_of_le inf_le_left
    by_cases hbot : autSub A₁ V₁ = ⊥
    · rw [hbot, Subgroup.card_bot, one_mul]
      exact hle4
    · have hmov : ¬ V₁ ≤ fixV A₁ := fun h => hbot ((B1.autSub_eq_bot_iff hA₁stab).2 h)
      have hA₁ne : A₁ ≠ ⊥ := fun h => hmov (by rw [h, B1.fixV_bot]; exact le_top)
      have hA₁2 : IsA2 A₁ A₁ := ⟨le_rfl, hA₁ne, fun b hb c hc => hAc b hb.1 c hc.1,
        fun b hb => hA.2.2.1.2 b hb.1⟩
      have hEab : IsElemAbelian2 (autSub A₁ V₁) := (B1.isA2_autSub hA₁2 hA₁stab hmov).2.2
      have hEcard := B1.card_elemAbelian hEab
      have hE2 : Nat.card (autSub A₁ V₁) ≤ 2 := by
        rw [hEcard] at hdvd ⊢
        rcases Nat.lt_or_ge (rk (autSub A₁ V₁)) 2 with hlt | hge
        · interval_cases (rk (autSub A₁ V₁)) <;> simp
        · exfalso
          have h4 : 4 ∣ 2 ^ rk (autSub A₁ V₁) := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hge
            rw [hk, pow_add]
            exact Dvd.intro _ rfl
          have := h4.trans hdvd
          omega
      have hfix2 : Nat.card ↥(V₁ ⊓ fixV A₁) ≤ 2 := by
        have hne' : V₁ ⊓ fixV A₁ ≠ V₁ := by
          intro h
          apply hmov
          rw [← h]
          exact inf_le_right
        have hd : Nat.card ↥(V₁ ⊓ fixV A₁) ∣ 4 := hV₁4 ▸ Subgroup.card_dvd_of_le inf_le_left
        have hne4 : Nat.card ↥(V₁ ⊓ fixV A₁) ≠ 4 := by
          intro h4
          exact hne' (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hV₁4]))
        have hmem : Nat.card ↥(V₁ ⊓ fixV A₁) ∈ Nat.divisors 4 :=
          Nat.mem_divisors.2 ⟨hd, by norm_num⟩
        have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [hdiv] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        omega
      calc Nat.card (autSub A₁ V₁) * Nat.card ↥(V₁ ⊓ fixV A₁) ≤ 2 * 2 :=
            Nat.mul_le_mul hE2 hfix2
        _ = 4 := by norm_num
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hfin : Nat.card B * 4 ^ O.card ≤ Nat.card B * (4 * O.card) := by
    calc Nat.card B * 4 ^ O.card = Nat.card B * Nat.card W := by rw [hWcard]
      _ ≤ Nat.card A * Nat.card ↥(W ⊓ fixV A) := hineq
      _ ≤ Nat.card A₁ * O.card * Nat.card ↥(V₁ ⊓ fixV A₁) :=
          Nat.mul_le_mul hAcard hCW
      _ = Nat.card B * (Nat.card (autSub A₁ V₁) * Nat.card ↥(V₁ ⊓ fixV A₁)) * O.card := by
          rw [← hA₁card]
          ring
      _ ≤ Nat.card B * 4 * O.card := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left _ hE
      _ = Nat.card B * (4 * O.card) := by ring
  have := Nat.le_of_mul_le_mul_left hfin hBpos
  have := four_mul_lt_four_pow hOcard
  omega

end Setting

end CFSG.Quasithin.B19
