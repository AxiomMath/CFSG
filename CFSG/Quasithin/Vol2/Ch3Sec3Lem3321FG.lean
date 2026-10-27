module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321W

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.ChiefCount
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.Lift
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le liftPre_le)
open CFSG.Quasithin.H13.Gen3324 (pre₀ mem_pre₀ parabolic_gen₀)
open scoped commutatorElement IsMulCommutative

theorem a3_mul : ∀ A B : SL2F2, A ^ 3 = 1 → B ^ 3 = 1 → (A * B) ^ 3 = 1 := by decide

theorem a3_pow : ∀ (A : SL2F2) (r : Fin 6), r.val % 2 = 1 → A ^ r.val = 1 → A ^ 3 = 1 := by
  decide

theorem sl2_pow_six : ∀ A : SL2F2, A ^ 6 = 1 := by decide

theorem sl2_sq_of : ∀ A : SL2F2, (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 = 0 → A * A = 1 := by
  decide

theorem sl2_noncomm : ∃ A B : SL2F2, (B * A)⁻¹ * (A * B) ≠ 1 := by decide

@[expose] def A3 : Subgroup SL2F2 where
  carrier := {A | A ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := fun {A B} hA hB => a3_mul A B hA hB
  inv_mem' := fun {A} hA => by
    show A⁻¹ ^ 3 = 1
    rw [inv_pow, show A ^ 3 = 1 from hA, inv_one]

theorem card_A3 : Nat.card ↥A3 = 3 := by
  have e : ↥A3 ≃ {A : SL2F2 // A ^ 3 = 1} := Equiv.subtypeEquivRight fun _ => Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

theorem mem_A3_of_odd {A : SL2F2} {m : ℕ} (hm : Odd m) (hA : A ^ m = 1) : A ∈ A3 := by
  have h6 := sl2_pow_six A
  have hmod : A ^ (m % 6) = 1 := by
    rw [← hA, ← Nat.mod_add_div m 6, pow_add, pow_mul, h6, one_pow, mul_one, Nat.mod_add_div]
  have hodd : (m % 6) % 2 = 1 := by
    obtain ⟨j, rfl⟩ := hm
    omega
  exact a3_pow A ⟨m % 6, Nat.mod_lt _ (by norm_num)⟩ hodd hmod

theorem mem_Ut_of_blk {g : ↥P2} (hA : blkA g = 1) (hC : blkC g = 1) : (g : SL4) ∈ FLc.Ut 4 := by
  have hAe : ∀ i j : Fin 2, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨i, by omega⟩ ⟨j, by omega⟩ =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := fun i j => by
    rw [← blkAM_apply, ← coe_blkA, hA]
    rfl
  have hCe : ∀ i j : Fin 2,
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ⟨2 + i, by omega⟩ ⟨2 + j, by omega⟩ =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j := fun i j => by
    rw [← blkCM_apply, ← coe_blkC, hC]
    rfl
  have hP := (mem_P2_iff (g : SL4)).1 g.2
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | exact hP _ _ (by decide) (by decide)
      | exact hAe 1 0
      | exact hCe 1 0
  · fin_cases i
    · exact hAe 0 0
    · exact hAe 1 1
    · exact hCe 0 0
    · exact hCe 1 1

theorem QI23_le_P2 : FLc.QI 4 {2, 3} ≤ P2 :=
  (FLc.QI_le_QI_iff fun j hj => by
    rw [Set.mem_singleton_iff] at hj
    subst hj
    exact ⟨by norm_num, by norm_num⟩).2 (by simp)

theorem QI12_le_P2 : FLc.QI 4 {1, 2} ≤ P2 :=
  (FLc.QI_le_QI_iff fun j hj => by
    rw [Set.mem_singleton_iff] at hj
    subst hj
    exact ⟨by norm_num, by norm_num⟩).2 (by simp)

theorem blkC_sq_of_QI23 {g : ↥P2} (hg : (g : SL4) ∈ FLc.QI 4 {2, 3}) : blkC g * blkC g = 1 := by
  apply sl2_sq_of
  rw [coe_blkC, blkCM_apply]
  exact stabilizer_entries (mem_flagStabilizer.1 hg 3 (by simp)) (by simp) (by simp)

theorem blkA_sq_of_QI12 {g : ↥P2} (hg : (g : SL4) ∈ FLc.QI 4 {1, 2}) : blkA g * blkA g = 1 := by
  apply sl2_sq_of
  rw [coe_blkA, blkAM_apply]
  exact stabilizer_entries (mem_flagStabilizer.1 hg 1 (by simp)) (by simp) (by simp)

theorem diag_mem_QI23 : ∀ A : SL2F2, ∀ p : Fin 4 × Fin 4,
    ((p.2 : ℕ) < 2 ∧ 2 ≤ (p.1 : ℕ)) ∨ ((p.2 : ℕ) < 3 ∧ 3 ≤ (p.1 : ℕ)) →
      (diagSL A 1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) p.1 p.2 = 0 := by
  decide

theorem diag_mem_QI12 : ∀ C : SL2F2, ∀ p : Fin 4 × Fin 4,
    ((p.2 : ℕ) < 1 ∧ 1 ≤ (p.1 : ℕ)) ∨ ((p.2 : ℕ) < 2 ∧ 2 ≤ (p.1 : ℕ)) →
      (diagSL 1 C : Matrix (Fin 4) (Fin 4) (ZMod 2)) p.1 p.2 = 0 := by
  decide

theorem diagSL_mem_QI23 (A : SL2F2) : diagSL A 1 ∈ FLc.QI 4 {2, 3} := by
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  rcases hc with rfl | hc
  · exact diag_mem_QI23 A (k, l) (Or.inl ⟨hl, hk⟩)
  · rw [Set.mem_singleton_iff] at hc
    subst hc
    exact diag_mem_QI23 A (k, l) (Or.inr ⟨hl, hk⟩)

theorem diagSL_mem_QI12 (C : SL2F2) : diagSL 1 C ∈ FLc.QI 4 {1, 2} := by
  refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
  rcases hc with rfl | hc
  · exact diag_mem_QI12 C (k, l) (Or.inl ⟨hl, hk⟩)
  · rw [Set.mem_singleton_iff] at hc
    subst hc
    exact diag_mem_QI12 C (k, l) (Or.inr ⟨hl, hk⟩)

variable {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* SL4}

theorem mem_of_mem_liftPre {P : Subgroup SL4} {x : G} (hx : x ∈ liftPre α P) :
    α ⟨x, liftPre_le α P hx⟩ ∈ P := by
  obtain ⟨l, hl, rfl⟩ := hx
  exact hl

@[expose] noncomputable def toP2 (α : ↥L →* SL4) {P : Subgroup SL4} (hP : P ≤ P2) :
    ↥(liftPre α P) →* ↥P2 :=
  (α.comp (Subgroup.inclusion (liftPre_le α P))).codRestrict P2 fun x =>
    hP (mem_of_mem_liftPre x.2)

theorem coe_toP2 {P : Subgroup SL4} (hP : P ≤ P2) (x : ↥(liftPre α P)) :
    ((toP2 α hP x : ↥P2) : SL4) = α ⟨x, liftPre_le α P x.2⟩ := rfl

@[expose] noncomputable def leviA (α : ↥L →* SL4) : ↥(liftPre α (FLc.QI 4 {2, 3})) →* SL2F2 :=
  blkA.comp (toP2 α QI23_le_P2)

@[expose] noncomputable def leviC (α : ↥L →* SL4) : ↥(liftPre α (FLc.QI 4 {1, 2})) →* SL2F2 :=
  blkC.comp (toP2 α QI12_le_P2)

theorem leviA_surjective (hαs : Function.Surjective α) : Function.Surjective (leviA α) := by
  intro A
  obtain ⟨l, hl⟩ := hαs (diagSL A 1)
  have hlP : (l : G) ∈ liftPre α (FLc.QI 4 {2, 3}) :=
    ⟨l, by show α l ∈ FLc.QI 4 {2, 3}; rw [hl]; exact diagSL_mem_QI23 A, rfl⟩
  refine ⟨⟨l, hlP⟩, ?_⟩
  have e : toP2 α QI23_le_P2 ⟨l, hlP⟩ = ⟨diagSL A 1, diagSL_mem A 1⟩ := Subtype.ext hl
  show blkA (toP2 α QI23_le_P2 ⟨l, hlP⟩) = A
  rw [e, blkA_diagSL]

theorem leviC_surjective (hαs : Function.Surjective α) : Function.Surjective (leviC α) := by
  intro C
  obtain ⟨l, hl⟩ := hαs (diagSL 1 C)
  have hlP : (l : G) ∈ liftPre α (FLc.QI 4 {1, 2}) :=
    ⟨l, by show α l ∈ FLc.QI 4 {1, 2}; rw [hl]; exact diagSL_mem_QI12 C, rfl⟩
  refine ⟨⟨l, hlP⟩, ?_⟩
  have e : toP2 α QI12_le_P2 ⟨l, hlP⟩ = ⟨diagSL 1 C, diagSL_mem 1 C⟩ := Subtype.ext hl
  show blkC (toP2 α QI12_le_P2 ⟨l, hlP⟩) = C
  rw [e, blkC_diagSL]

variable [Finite G]

omit [Finite G] in
theorem exists_pow_of_mem_Ut (hker : α.ker = CFSG.pCore 2 ↥L) {x : ↥L} (hx : α x ∈ FLc.Ut 4) :
    ∃ n : ℕ, (x : G) ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) (n := 4)
    (by norm_num)).2.1 ⟨α x, hx⟩
  have ha' : α (x ^ 2 ^ a) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val ha
  have hk : x ^ 2 ^ a ∈ CFSG.pCore 2 ↥L := by
    rw [← hker]
    exact ha'
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hk⟩
  refine ⟨a + b, ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hb
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  rw [pow_add, pow_mul, this]

omit [Finite G] in
theorem mem_pCoreOf_of_ker {K : Subgroup G} {Γ : Type} [Group Γ] (ρ : ↥K →* Γ)
    (h2 : ∀ g : ↥K, ρ g = 1 → ∃ n : ℕ, (g : G) ^ 2 ^ n = 1) :
    ∀ g : ↥K, ρ g = 1 → (g : G) ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNK : ρ.ker.map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hsub : (ρ.ker.map K.subtype).subgroupOf K = ρ.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hKN : K ≤ Subgroup.normalizer ((ρ.ker.map K.subtype : Subgroup G) : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hNK, hsub]
    exact MonoidHom.normal_ker ρ
  have hN2 : IsPGroup 2 ↥(ρ.ker.map K.subtype) := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    obtain ⟨n, hn⟩ := h2 g hg
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  intro g hg
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNK hKN hN2 ⟨g, hg, rfl⟩

omit [Finite G] in
theorem pre₀_top {K : Subgroup G} {Γ : Type} [Group Γ] (ρ : ↥K →* Γ) : pre₀ ρ ⊤ = K := by
  ext x
  rw [mem_pre₀]
  exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, Subgroup.mem_top _⟩⟩

theorem card_sl2 : Nat.card SL2F2 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem parabolic_pkg {T K : Subgroup G} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hTK : T ≤ K) (ρ : ↥K →* SL2F2) (hρs : Function.Surjective ρ)
    (h2 : ∀ g : ↥K, ρ g = 1 → ∃ n : ℕ, (g : G) ^ 2 ^ n = 1) :
    oTwoUpper (oTwoUpper K) = oTwoUpper K ∧ T ≤ Subgroup.normalizer (oTwoUpper K : Set G) ∧
      oTwoUpper K ⊔ T = K ∧ Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Equiv.Perm (Fin 3)) ∧
      pCoreOf 2 K = pre₀ ρ ⊥ ∧ pre₀ ρ ⊥ ≤ T := by
  have hrange : ρ.range = ⊤ := MonoidHom.range_eq_top.mpr hρs
  have h6 : Nat.card ↥(ρ.range ⊓ (⊤ : Subgroup SL2F2)) =
      6 * Nat.card ↥(ρ.range ⊓ (⊥ : Subgroup SL2F2)) := by
    rw [hrange, top_inf_eq, top_inf_eq, Subgroup.card_top, card_sl2, Subgroup.card_bot]
  obtain ⟨A, B, hAB⟩ := sl2_noncomm
  obtain ⟨ka, hka⟩ := hρs A
  obtain ⟨kb, hkb⟩ := hρs B
  have key := parabolic_gen₀ ρ hTK hT2 hTidx (mem_pCoreOf_of_ker ρ h2) (p := ⊤) (r := ⊥)
    (fun _ _ => Subgroup.mem_top _) bot_le (fun x _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro h1
        simpa using h1)
    (fun x hx => by rw [Subgroup.mem_bot.1 hx, mul_one]) h6 (ka := ka) (kb := kb)
    (Subgroup.mem_top _) (Subgroup.mem_top _)
    (by rw [hka, hkb, Subgroup.mem_bot]; exact hAB)
  rw [pre₀_top] at key
  exact key

omit [Finite G] in
theorem liftPre_mono {P P' : Subgroup SL4} (h : P ≤ P') : liftPre α P ≤ liftPre α P' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite G] in
theorem inf_pre₀_le (hker : α.ker = CFSG.pCore 2 ↥L) :
    pre₀ (leviA α) ⊥ ⊓ pre₀ (leviC α) ⊥ ≤ pCoreOf 2 (liftPre α P2) := by
  let φ : ↥(liftPre α P2) →* SL2F2 × SL2F2 := (blkA.prod blkC).comp (toP2 α le_rfl)
  have h2 : ∀ g : ↥(liftPre α P2), φ g = 1 → ∃ n : ℕ, (g : G) ^ 2 ^ n = 1 := by
    intro g hg
    have hA : blkA (toP2 α le_rfl g) = 1 := congrArg Prod.fst hg
    have hC : blkC (toP2 α le_rfl g) = 1 := congrArg Prod.snd hg
    exact exists_pow_of_mem_Ut hker (x := ⟨g, liftPre_le α P2 g.2⟩) (mem_Ut_of_blk hA hC)
  rintro x ⟨hxa, hxb⟩
  obtain ⟨hxLa, hxa'⟩ := (mem_pre₀ _).1 hxa
  obtain ⟨hxLb, hxb'⟩ := (mem_pre₀ _).1 hxb
  have hxP : x ∈ liftPre α P2 := liftPre_mono QI23_le_P2 hxLa
  refine mem_pCoreOf_of_ker φ h2 ⟨x, hxP⟩ ?_
  have hA : leviA α ⟨x, hxLa⟩ = 1 := Subgroup.mem_bot.1 hxa'
  have hC : leviC α ⟨x, hxLb⟩ = 1 := Subgroup.mem_bot.1 hxb'
  show (blkA (toP2 α QI23_le_P2 ⟨x, hxLa⟩), blkC (toP2 α QI12_le_P2 ⟨x, hxLb⟩)) = 1
  exact Prod.ext hA hC

omit [Finite G] in
theorem card_le_32 {H : Subgroup SL4} (hHU : H ≤ FLc.Ut 4) {t : SL4} (ht : t ∈ FLc.Ut 4)
    (htH : t ∉ H) : Nat.card ↥H ≤ 32 := by
  have hU : Nat.card ↥(FLc.Ut 4) = 64 := by
    have := card_unitriangular (K := ZMod 2) 4
    rw [Nat.card_zmod] at this
    simpa using this
  have hdvd : Nat.card ↥H ∣ 64 := hU ▸ Subgroup.card_dvd_of_le hHU
  have hne : Nat.card ↥H ≠ 64 := by
    intro h64
    apply htH
    have := Subgroup.eq_of_le_of_card_ge hHU (by rw [hU, h64])
    rw [this]
    exact ht
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · omega
  · omega
  · nlinarith

theorem not_hasNoncentralTwoChief_five {X R V Z : Subgroup G} (hZV : Z ≤ V)
    (hXZ : X ≤ Subgroup.centralizer (Z : Set G)) (hZ : Z ≠ ⊥) (hV : Nat.card ↥V = 64)
    (hVR : V ≤ R) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) (hR32 : (X ⊓ V).relIndex (X ⊓ R) ≤ 32)
    (hR3 : (X ⊓ R).relIndex X ≤ 3) : ¬ HasNoncentralTwoChief X 5 := by
  rintro ⟨A, B, hAB, hle⟩
  have hNC : HasNCBetween X ⊥ X 5 :=
    ⟨A, B, fun i => ⟨(hAB i).1, (hAB i).2, bot_le, (hAB i).1.2.1⟩, hle⟩
  have hXZn : X ≤ Subgroup.normalizer (Z : Set G) :=
    hXZ.trans (Subgroup.centralizer_le_normalizer _)
  have ha : NCAtMost X ⊥ (Z ⊓ X) 0 := by
    refine ncAtMost_zero_of_commutator_le ?_
    have : ⁅Z, X⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (Subgroup.le_centralizer_iff.1 hXZ)
    rw [← this]
    exact Subgroup.commutator_mono inf_le_left le_rfl
  have hb : NCAtMost X (Z ⊓ X) (X ⊓ V) 2 := by
    refine ncAtMost_of_relIndex_lt ?_
    have hle' : Z ⊓ X ≤ X ⊓ V := fun x hx => ⟨hx.2, hZV hx.1⟩
    have h1 := Subgroup.relIndex_mul_card (Z ⊓ X) (X ⊓ V)
    rw [inf_eq_left.2 hle'] at h1
    have hXV64 : Nat.card ↥(X ⊓ V) ≤ 64 := hV ▸ Subgroup.card_le_of_le inf_le_right
    by_cases hZX : Z ⊓ X = ⊥
    · have hne : X ⊓ V ≠ V := by
        intro e
        apply hZ
        rw [eq_bot_iff]
        intro z hz
        have hzXV : z ∈ X ⊓ V := by
          rw [e]
          exact hZV hz
        have : z ∈ Z ⊓ X := ⟨hz, hzXV.1⟩
        rw [hZX] at this
        exact this
      have hlt : Nat.card ↥(X ⊓ V) ≤ 32 := by
        have hdvd : Nat.card ↥(X ⊓ V) ∣ 64 := hV ▸ Subgroup.card_dvd_of_le inf_le_right
        have hne64 : Nat.card ↥(X ⊓ V) ≠ 64 := fun h64 =>
          hne (Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hV, h64]))
        obtain ⟨k, hk⟩ := hdvd
        rcases k with _ | _ | k
        · omega
        · omega
        · nlinarith
      rw [hZX, Subgroup.card_bot, mul_one] at h1
      rw [hZX, h1]
      calc Nat.card ↥(X ⊓ V) ≤ 32 := hlt
        _ < 4 ^ (2 + 1) := by norm_num
    · have h2 : 2 ≤ Nat.card ↥(Z ⊓ X) := by
        have := (Subgroup.one_lt_card_iff_ne_bot (Z ⊓ X)).2 hZX
        omega
      norm_num
      nlinarith
  have hc : NCAtMost X (X ⊓ V) (X ⊓ R) 2 := ncAtMost_of_relIndex_lt (by norm_num; omega)
  have hd : NCAtMost X (X ⊓ R) X 0 := ncAtMost_of_relIndex_lt (by norm_num; omega)
  have hab := ha.add hb bot_le (fun x hx => ⟨hx.2, hZV hx.1⟩) inf_le_left
    (fun x hx => ChiefCount.mem_normalizer_inf (hXZn hx) (Subgroup.le_normalizer hx))
  have habc := hab.add hc bot_le (inf_le_inf_left X hVR) inf_le_left
    (fun x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hXV hx))
  have habcd := habc.add hd bot_le inf_le_left le_rfl
    (fun x hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (hXR hx))
  exact habcd hNC

end CFSG.Quasithin.H13.L3321
