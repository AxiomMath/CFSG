module

public import CFSG.Quasithin.H13.A5S136a
public import CFSG.Quasithin.H13.A5S135
public import CFSG.Quasithin.Background.E3Nlow

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Quasithin.E3
open scoped commutatorElement

@[expose] def E02 : W5 := Multiplicative.ofAdd (e2 0 2)

@[expose] def E04 : W5 := Multiplicative.ofAdd (e2 0 4)

@[expose] def DPair (x : W5) (σ τ : Equiv.Perm (Fin 5)) : Prop :=
  InD σ → InD τ → pact σ x ≠ x → pact τ x ≠ x → pact (σ * τ) x = x

instance (x : W5) : DecidableRel (DPair x) := fun σ τ =>
  inferInstanceAs
    (Decidable (InD σ → InD τ → pact σ x ≠ x → pact τ x ≠ x → pact (σ * τ) x = x))

theorem dPair_E12 : ∀ σ τ : Equiv.Perm (Fin 5), DPair E12 σ τ := by
  decide +kernel

@[expose] def DPair2 (σ τ : Equiv.Perm (Fin 5)) : Prop :=
  pact σ E12 = E12 → pact τ E12 = E12 → DPair E04 σ τ

instance : DecidableRel DPair2 := fun σ τ =>
  inferInstanceAs (Decidable (pact σ E12 = E12 → pact τ E12 = E12 → DPair E04 σ τ))

theorem dPair2 : ∀ σ τ : Equiv.Perm (Fin 5), DPair2 σ τ := by
  decide +kernel

@[expose] def DPair3 (σ τ : Equiv.Perm (Fin 5)) : Prop :=
  pact σ E12 = E12 → pact τ E12 = E12 → pact σ E04 = E04 → pact τ E04 = E04 → DPair E02 σ τ

instance : DecidableRel DPair3 := fun σ τ =>
  inferInstanceAs (Decidable (pact σ E12 = E12 → pact τ E12 = E12 → pact σ E04 = E04 →
    pact τ E04 = E04 → DPair E02 σ τ))

theorem dPair3 : ∀ σ τ : Equiv.Perm (Fin 5), DPair3 σ τ := by
  decide +kernel

@[expose] def DFix (σ : Equiv.Perm (Fin 5)) : Prop :=
  InD σ → pact σ E12 = E12 → pact σ E04 = E04 → pact σ E02 = E02 → σ = 1

instance : DecidablePred DFix := fun σ =>
  inferInstanceAs
    (Decidable (InD σ → pact σ E12 = E12 → pact σ E04 = E04 → pact σ E02 = E02 → σ = 1))

theorem dFix : ∀ σ : Equiv.Perm (Fin 5), DFix σ := by
  decide +kernel

theorem mQuot_le_one_of_pair {G : Type} [Group G] [Finite G] {A C : Subgroup G} (hCA : C ≤ A)
    (h : ∀ a ∈ A, ∀ b ∈ A, a ∉ C → b ∉ C → a * b ∈ C) : mQuot A C ≤ 1 := by
  by_cases hAC : A ≤ C
  · have : C = A := le_antisymm hCA hAC
    subst this
    rw [mQuot_self]
    omega
  · obtain ⟨a₀, ha₀A, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
    have h2 : (C.subgroupOf A).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and']
      refine ⟨⟨a₀, ha₀A⟩, fun hm => ha₀C (Subgroup.mem_subgroupOf.mp hm), fun b => ?_⟩
      by_cases hb : (b : G) ∈ C
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr (h a₀ ha₀A b b.2 ha₀C hb))
    show padicValNat 2 (C.subgroupOf A).index ≤ 1
    rw [h2, padicValNat_self]

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem mQuot_V_V1 : mQuot V S.V1 = 3 := by
  have h := card_eq_two_pow_mul S.isPGroup_V S.V1_le_V
  rw [S.card_V, S.card_V1] at h
  have h8 : 2 ^ mQuot V S.V1 = 8 := by omega
  exact Nat.pow_right_injective (le_refl 2) (h8.trans (by norm_num))

theorem exists_nonsing_of_four_le {U : Subgroup G} (hUV : U ≤ V) (hU : 4 ≤ Nat.card U) :
    ∃ u : ↥V, (u : G) ∈ U ∧ u ≠ 1 ∧ ¬ IsSing (S.frame.ψ u) := by
  obtain ⟨x, hxU, hx1⟩ : ∃ x ∈ U, x ≠ 1 := by
    by_contra h
    push Not at h
    have : U = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hU
    omega
  have hx2 : x ^ 2 = 1 := S.elemAbelian_V.2 x (hUV hxU)
  obtain ⟨y, hyU, hyx⟩ : ∃ y ∈ U, y ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : U ≤ Subgroup.zpowers x := h
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers x) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hx2
    omega
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hyx' : y ≠ x := fun h => hyx (h ▸ Subgroup.mem_zpowers x)
  have hψ1 : ∀ w (hw : w ∈ V), w ≠ 1 → S.frame.ψ ⟨w, hw⟩ ≠ 1 := fun w hw hw1 h =>
    hw1 (congrArg Subtype.val (S.frame.ψ.injective (h.trans (map_one _).symm)))
  by_cases hsx : IsSing (S.frame.ψ ⟨x, hUV hxU⟩)
  · by_cases hsy : IsSing (S.frame.ψ ⟨y, hUV hyU⟩)
    · have hxy1 : x * y ≠ 1 := by
        intro h
        apply hyx'
        have hx2' : x * x = 1 := by rw [← pow_two]; exact hx2
        calc y = x * (x * y) := by rw [← mul_assoc, hx2', one_mul]
          _ = x := by rw [h, mul_one]
      refine ⟨⟨x * y, V.mul_mem (hUV hxU) (hUV hyU)⟩, U.mul_mem hxU hyU,
        fun h => hxy1 (congrArg Subtype.val h), ?_⟩
      have hne : S.frame.ψ ⟨x, hUV hxU⟩ ≠ S.frame.ψ ⟨y, hUV hyU⟩ := fun h =>
        hyx' (congrArg Subtype.val (S.frame.ψ.injective h)).symm
      have e : S.frame.ψ ⟨x * y, V.mul_mem (hUV hxU) (hUV hyU)⟩ =
          S.frame.ψ ⟨x, hUV hxU⟩ * S.frame.ψ ⟨y, hUV hyU⟩ :=
        map_mul S.frame.ψ ⟨x, hUV hxU⟩ ⟨y, hUV hyU⟩
      rw [e]
      exact not_isSing_mul _ _ (hψ1 x _ hx1) (hψ1 y _ hy1) hne hsx hsy
    · exact ⟨⟨y, hUV hyU⟩, hyU, fun h => hy1 (congrArg Subtype.val h), hsy⟩
  · exact ⟨⟨x, hUV hxU⟩, hxU, fun h => hx1 (congrArg Subtype.val h), hsx⟩

theorem rParam_eq_three (h137 : Thm13_6_7) (h1336 : Input1336)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) : rParam V = 3 := by
  apply le_antisymm
  · have hG1 : ¬ Subgroup.centralizer (S.V1 : Set G) ≤ Subgroup.normalizer (V : Set G) := by
      rw [S.centralizer_V1]
      exact fun h => h1336 G T L V S (h.trans S.NV_le_M)
    have h := rParam_le_mQuot S.V1_le_V hG1
    rw [S.mQuot_V_V1] at h
    exact_mod_cast h
  · refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hC⟩ := hU
    by_contra hlt
    push Not at hlt
    have hm3 : mQuot V U < 3 := by exact_mod_cast hlt
    have hm : mQuot V U ≤ 2 := by omega
    have hcard := card_eq_two_pow_mul S.isPGroup_V hUV
    rw [S.card_V] at hcard
    have h4 : 4 ≤ Nat.card U := by
      have : 2 ^ mQuot V U ≤ 4 := (Nat.pow_le_pow_right (by norm_num) hm).trans (by norm_num)
      have hpos : 0 < Nat.card U := Nat.card_pos
      nlinarith
    obtain ⟨u, huU, hu1, hu⟩ := S.exists_nonsing_of_four_le hUV h4
    apply hC
    refine le_trans (Subgroup.centralizer_le ?_) (S.centralizer_le_of_nonsing h137 hab u hu1 hu)
    rw [Set.singleton_subset_iff]
    exact huU

theorem comm_iff_pact {a : G} (ha : a ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    a * v = v * a ↔ pact (S.frame.ρ ⟨a, ha⟩) (S.frame.ψ v) = S.frame.ψ v := by
  rw [← S.conj_eq_iff ⟨a, ha⟩ v]
  constructor
  · intro h
    show a * v * a⁻¹ = v
    rw [h, mul_inv_cancel_right]
  · intro h
    have h' : a * v * a⁻¹ = v := h
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [h']

theorem comm_of_mQuot_le_two (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hAT : A ≤ T)
    (hAV : A ≤ conjSubgroup V g) {x : G} (hx : x ∈ V)
    (hm : mQuot (conjSubgroup V g) (A ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 2) :
    ∀ a ∈ A, a * x = x * a := by
  set B := A ⊓ Subgroup.centralizer ({x} : Set G) with hBdef
  have hBV : B ≤ conjSubgroup V g := inf_le_left.trans hAV
  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer (conjSubgroup V g : Set G) := by
    by_contra hcon
    have h1 := rParam_le_mQuot hBV hcon
    rw [rParam_conj, hr] at h1
    have h2 : 3 ≤ mQuot (conjSubgroup V g) B := by exact_mod_cast h1
    omega
  have hxB : x ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hb).2
  have hxN := hCB hxB
  have hAV' : A ≤ conjSub g⁻¹ V := hAV
  intro a ha
  have hcV : ⁅x, a⁆ ∈ V := by
    rw [commutatorElement_def]
    have h1 : a * x⁻¹ * a⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (S.frame.T_le (hAT ha)) x⁻¹).mp (V.inv_mem hx)
    have h2 : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [h2]
    exact V.mul_mem hx h1
  have hcVg : ⁅x, a⁆ ∈ conjSubgroup V g := by
    rw [commutatorElement_def]
    have h1 : x * a * x⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.mp hxN a).mp (hAV ha)
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem (hAV ha))
  by_contra hne
  have hc1 : ⁅x, a⁆ ≠ 1 := fun h =>
    hne (commutatorElement_eq_one_iff_mul_comm.mp h).symm
  have hne' : V ⊓ conjSub g⁻¹ V ≠ ⊥ := by
    intro h
    apply hc1
    have : ⁅x, a⁆ ∈ V ⊓ conjSub g⁻¹ V := ⟨hcV, hcVg⟩
    rw [h] at this
    exact (Subgroup.mem_bot).mp this
  have hcomm := S.lemma_13_6_24_two h137 h1326 hab hg hne'
  have := Subgroup.commutator_mem_commutator hx (hAV' ha)
  rw [hcomm] at this
  exact hc1 (Subgroup.mem_bot.mp this)

theorem false_of_pair (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) {g : G}
    (hg : g ∉ Subgroup.normalizer (V : Set G)) {A : Subgroup G} (hAT : A ≤ T)
    (hAV : A ≤ conjSubgroup V g) (hmA : mQuot (conjSubgroup V g) A ≤ 1) {x : G} (hx : x ∈ V)
    (hmove : ∃ a ∈ A, a * x ≠ x * a)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a * x ≠ x * a → b * x ≠ x * b → a * b * x = x * (a * b)) :
    False := by
  set C := A ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have hCA : C ≤ A := inf_le_left
  have hmem : ∀ a ∈ A, a ∈ C ↔ a * x = x * a := fun a ha => by
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact and_iff_right ha
  have h1 : mQuot A C ≤ 1 := mQuot_le_one_of_pair hCA fun a ha b hb haC hbC => by
    rw [hmem a ha] at haC
    rw [hmem b hb] at hbC
    rw [hmem (a * b) (A.mul_mem ha hb)]
    exact hpair a ha b hb haC hbC
  have h2 : mQuot (conjSubgroup V g) C ≤ 2 := by
    rw [mQuot_add hCA hAV]
    omega
  obtain ⟨a, ha, hax⟩ := hmove
  exact hax (S.comm_of_mQuot_le_two h137 h1326 hab hr hg hAT hAV hx h2 a ha)

theorem wClos_le (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) {i : ℕ} (hi : i ≤ 1) :
    wClos V i T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAV, hmA⟩ := hA
  refine le_inf hAT ?_
  by_cases hgN : g ∈ Subgroup.normalizer (V : Set G)
  ·
    have hVg : conjSubgroup V g = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hgN)
    rw [hVg] at hAV
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := S.elemAbelian_V.1.is_comm.comm ⟨v, hv⟩ ⟨a, hAV ha⟩
    exact congrArg Subtype.val this
  ·
    have hmA' : mQuot (conjSubgroup V g) A ≤ 1 := by rw [hmA]; exact hi
    by_contra hAC
    have hNT : ∀ a ∈ A, a ∈ Subgroup.normalizer (V : Set G) := fun a ha =>
      S.frame.T_le (hAT ha)
    have hD : ∀ a (ha : a ∈ A), InD (S.frame.ρ ⟨a, hNT a ha⟩) := fun a ha =>
      S.frame.T_D ⟨a, hNT a ha⟩ (hAT ha)
    have hρmul : ∀ a (ha : a ∈ A) b (hb : b ∈ A),
        S.frame.ρ ⟨a * b, hNT _ (A.mul_mem ha hb)⟩ =
          S.frame.ρ ⟨a, hNT a ha⟩ * S.frame.ρ ⟨b, hNT b hb⟩ := fun a ha b hb =>
      map_mul S.frame.ρ ⟨a, hNT a ha⟩ ⟨b, hNT b hb⟩
    let x₁ : ↥V := S.frame.ψ.symm E12
    let x₂ : ↥V := S.frame.ψ.symm E04
    let x₃ : ↥V := S.frame.ψ.symm E02
    have hx₁ : S.frame.ψ x₁ = E12 := S.frame.ψ.apply_symm_apply E12
    have hx₂ : S.frame.ψ x₂ = E04 := S.frame.ψ.apply_symm_apply E04
    have hx₃ : S.frame.ψ x₃ = E02 := S.frame.ψ.apply_symm_apply E02
    have hc : ∀ a (ha : a ∈ A) (x : ↥V),
        a * (x : G) = x * a ↔ pact (S.frame.ρ ⟨a, hNT a ha⟩) (S.frame.ψ x) = S.frame.ψ x :=
      fun a ha x => S.comm_iff_pact (hNT a ha) x
    by_cases hP1 : ∃ a ∈ A, a * (x₁ : G) ≠ x₁ * a
    · refine S.false_of_pair h137 h1326 hab hr hgN hAT hAV hmA' x₁.2 hP1 ?_
      intro a ha b hb hax hbx
      rw [Ne, hc a ha, hx₁] at hax
      rw [Ne, hc b hb, hx₁] at hbx
      rw [hc (a * b) (A.mul_mem ha hb), hx₁, hρmul a ha b hb]
      exact dPair_E12 _ _ (hD a ha) (hD b hb) hax hbx
    push Not at hP1
    have hf1 : ∀ a (ha : a ∈ A), pact (S.frame.ρ ⟨a, hNT a ha⟩) E12 = E12 := fun a ha => by
      rw [← hx₁, ← hc a ha]
      exact hP1 a ha
    by_cases hP2 : ∃ a ∈ A, a * (x₂ : G) ≠ x₂ * a
    · refine S.false_of_pair h137 h1326 hab hr hgN hAT hAV hmA' x₂.2 hP2 ?_
      intro a ha b hb hax hbx
      rw [Ne, hc a ha, hx₂] at hax
      rw [Ne, hc b hb, hx₂] at hbx
      rw [hc (a * b) (A.mul_mem ha hb), hx₂, hρmul a ha b hb]
      exact dPair2 _ _ (hf1 a ha) (hf1 b hb) (hD a ha) (hD b hb) hax hbx
    push Not at hP2
    have hf2 : ∀ a (ha : a ∈ A), pact (S.frame.ρ ⟨a, hNT a ha⟩) E04 = E04 := fun a ha => by
      rw [← hx₂, ← hc a ha]
      exact hP2 a ha
    have hP3 : ∃ a ∈ A, a * (x₃ : G) ≠ x₃ * a := by
      obtain ⟨a, ha, haV⟩ := IsConcreteLE.not_le_iff_exists.mp hAC
      refine ⟨a, ha, fun h3 => haV ?_⟩
      have h3' := (hc a ha x₃).mp h3
      rw [hx₃] at h3'
      have hρ1 := dFix _ (hD a ha) (hf1 a ha) (hf2 a ha) h3'
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := (hc a ha ⟨v, hv⟩).mpr (by rw [hρ1, map_one, MulAut.one_apply])
      exact this.symm
    refine S.false_of_pair h137 h1326 hab hr hgN hAT hAV hmA' x₃.2 hP3 ?_
    intro a ha b hb hax hbx
    rw [Ne, hc a ha, hx₃] at hax
    rw [Ne, hc b hb, hx₃] at hbx
    rw [hc (a * b) (A.mul_mem ha hb), hx₃, hρmul a ha b hb]
    exact dPair3 _ _ (hf1 a ha) (hf1 b hb) (hf2 a ha) (hf2 b hb) (hD a ha) (hD b hb) hax hbx

theorem one_lt_wParam (h137 : Thm13_6_7) (h1326 : Input1326Two)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (hr : rParam V = 3) : 1 < wParam T V := by
  have h := le_wParam_of_wClos_le (n := 2) (T := T) (V := V) fun j hj =>
    S.wClos_le h137 h1326 hab hr (by omega)
  exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)) h

theorem V_ne_bot_of_z : V ≠ ⊥ := fun h =>
  S.z_ne_one ((Subgroup.eq_bot_iff_forall V).mp h S.z S.z_mem_V)

theorem hypE322 : HypE322 T V := ⟨S.sylow_top, S.V_le_T, S.frame.T_le⟩

theorem isUniqueM_normalizer :
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
  rw [S.cT]
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h =>
    S.V_ne_bot_of_z (le_bot_iff.mp (h ▸ S.V_le_pCoreOf_LT))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G)) :=
    ⟨pCoreOf 2 (L ⊔ T), hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T), rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := S.uniqueM.2 M' ⟨hM', hLT.trans hle⟩
  subst hM'eq
  refine ⟨⟨hM', hle⟩, fun M'' hM'' => S.uniqueM.2 M'' ⟨hM''.1, hLT.trans hM''.2⟩⟩

theorem one_lt_nParam (h137 : Thm13_6_7) (h1326 : Input1326Two) (h1336 : Input1336)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) : 1 < E1.nParam H := by
  have hr := S.rParam_eq_three h137 h1336 hab
  have hw := S.one_lt_wParam h137 h1326 hab hr
  by_contra hn
  push Not at hn
  apply hHM
  refine e3_35_one S.elemAbelian_V S.V_ne_bot_of_z S.hypE322 S.isUniqueM_normalizer
    (isSylowTwoOf_of_le S.h13.sylow hH.1) ?_ inf_le_left ?_
  · exact fun x hx => S.NV_le_M (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2)
  · rw [hr]
    exact lt_of_le_of_lt hn (lt_min hw (by norm_num))

theorem le_M_of_solvable (h137 : Thm13_6_7) (h1326 : Input1326Two) (h1336 : Input1336)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) {H : Subgroup G} (hH : InH T H)
    (hs : Group.IsSolvable ↥H) : H ≤ Subgroup.normalizer (L : Set G) := by
  have hr := S.rParam_eq_three h137 h1336 hab
  have hw := S.one_lt_wParam h137 h1326 hab hr
  refine e3_35_one_solvable S.elemAbelian_V S.V_ne_bot_of_z S.hypE322 S.isUniqueM_normalizer
    (isSylowTwoOf_of_le S.h13.sylow hH.1) ?_ inf_le_left hs ?_
  · exact fun x hx => S.NV_le_M (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2)
  · rw [hr]
    exact lt_min hw (by norm_num)

end Setting

end CFSG.Quasithin.H13.A5
