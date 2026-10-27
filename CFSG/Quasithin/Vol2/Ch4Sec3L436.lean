module

public import CFSG.Quasithin.Vol2.Ch4Sec3Ut

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped commutatorElement Pointwise

theorem odd_eq_of_two_pow_mul_eq {m m' : ℕ} (hm : Odd m) (hm' : Odd m') :
    ∀ {a b : ℕ}, 2 ^ a * m = 2 ^ b * m' → m = m' := by
  intro a
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => simpa using h
    | succ b =>
      exfalso
      rw [pow_zero, one_mul] at h
      rw [h, pow_succ] at hm
      simp only [Nat.odd_mul] at hm
      exact absurd hm.1.2 (by decide)
  | succ a ih =>
    intro b h
    cases b with
    | zero =>
      exfalso
      rw [pow_zero, one_mul] at h
      rw [← h, pow_succ] at hm'
      simp only [Nat.odd_mul] at hm'
      exact absurd hm'.1.2 (by decide)
    | succ b =>
      refine ih (b := b) (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_)
      rw [← mul_assoc, ← mul_assoc, ← pow_succ', ← pow_succ']
      exact h

theorem odd_four_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (4 ^ n - 1) := by
  have he : Even (4 ^ n) := (by decide : Even 4).pow_of_ne_zero (by omega)
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) he odd_one

theorem four_pow_sub_one_ne (n : ℕ) {N : ℕ}
    (hN : N = 21 ∨ N = 45 ∨ N = 135 ∨ N = 189 ∨ N = 315 ∨ N = 9765 ∨ N = 239085) :
    4 ^ n - 1 ≠ N := by
  intro h
  have hle : n < 10 := by
    by_contra hge
    have h1 : 4 ^ 10 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  interval_cases n <;> rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h

theorem eq_two_of_four_pow_sub_one {n : ℕ} (h : 4 ^ n - 1 = 15) : n = 2 := by
  have hle : n < 3 := by
    by_contra hge
    have h1 : 4 ^ 3 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> simp_all

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_of_isExt {X : Type} [Group X] {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt X PV PY) :
    ∃ (V : Subgroup X) (_ : V.Normal), PV ↥V ∧ PY (X ⧸ V) ∧
      Nat.card X = Nat.card V * Nat.card (X ⧸ V) := by
  obtain ⟨V, hV, hPV, hPY⟩ := h
  exact ⟨V, hV, hPV, hPY, by rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, mul_comm]⟩

omit [Finite G] in
theorem card_of_isE2 {V : Type} [Group V] {k : ℕ} (h : IsE2 k V) : Nat.card V = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

omit [Finite G] in
theorem card_of_isSpecial2Group {V : Type} [Group V] {a b : ℕ} (h : IsSpecial2Group a b V) :
    Nat.card V = 2 ^ (a + b) := by
  obtain ⟨hc, -, hq⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center V), card_of_isE2 hq, hc,
    pow_add, mul_comm]

omit [Finite G] in
theorem card_of_isZ4Cubed {V : Type} [Group V] (h : IsZ4Cubed V) : Nat.card V = 2 ^ 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

omit [Finite G] in
theorem card_of_isHat_alt6 {Y : Type} [Group Y] (h : IsHat Y ↥(alternatingGroup (Fin 6))) :
    Nat.card Y = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hc,
    Nat.card_congr e.toEquiv, card_of_alt' (by norm_num) (MulEquiv.refl _)]
  decide

omit [Finite G] in
theorem card_eq_two_pow_mul_card_imageModCenter {K X : Subgroup G} (hXK : X ≤ K)
    (hZ : IsPGroup 2 ↥(centerOf K)) [Finite K] :
    ∃ u : ℕ, Nat.card X = 2 ^ u * Nat.card ↥(imageModCenter K X) := by
  set f : ↥(X.subgroupOf K) →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype with hf
  have hrange : f.range = imageModCenter K X := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h2 : IsPGroup 2 ↥f.ker := by
    rintro ⟨g, hg⟩
    have hgc : ((g : K) : K) ∈ Subgroup.center ↥K := by
      have : (QuotientGroup.mk' (Subgroup.center ↥K)) (g : K) = 1 := hg
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hgZ : (((g : K) : K) : G) ∈ centerOf K := by
      refine ⟨((g : K) : K).2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have := Subgroup.mem_center_iff.mp hgc ⟨k, hk⟩
      exact congrArg Subtype.val this
    obtain ⟨m, hm⟩ := hZ ⟨_, hgZ⟩
    refine ⟨m, Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    have := congrArg Subtype.val hm
    simpa using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := IsPGroup.iff_card.mp h2
  refine ⟨u, ?_⟩
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hu] at e1
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv, e1, mul_comm]

@[expose] def C436Two (M L K : Subgroup G) : Prop :=
  (IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K) ∧
      IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsE2 4 N)
        (fun Y _ => IsPSL 2 2 2 Y)) ∨
    (IsSporadic .M23 ↥K ∧
      IsExt ↥(conjClosure L M) (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 2 2 2 Y))

theorem c31_cases_of_psl_two {H R M L V K : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hL : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n)
    (h : C31Conclusion H R M L V K) :
    C31Case1 H R M L V K ∨ (n = 2 ∧ C436Two M L K) := by
  obtain ⟨hLeq, -, hM0K, -, hZ2, hcase⟩ := h
  have hLK : L ≤ K := hLeq ▸ hM0K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardL : ∃ a : ℕ, Nat.card L = 2 ^ a * (4 ^ n - 1) := by
    have hq : Nat.card (ModO2 L) = 2 ^ n * (4 ^ n - 1) :=
      F420.card_of_statedPSL_two_two (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
        (by decide) hL)
    obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
    refine ⟨n + t, ?_⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), ht,
      show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (ModO2 L) from rfl, hq, pow_add]
    ring
  obtain ⟨a, ha⟩ := hcardL
  have hodd : Odd (4 ^ n - 1) := odd_four_pow_sub_one (by omega)
  set M₀ := conjClosure L M with hM₀
  have hM0card : Nat.card ↥M₀ = Nat.card ↥L := by rw [← hLeq]
  have key : ∀ (b m : ℕ), Odd m → Nat.card ↥M₀ = 2 ^ b * m → m = 4 ^ n - 1 :=
    fun b m hm hb => odd_eq_of_two_pow_mul_eq hm hodd (hb.symm.trans (hM0card.trans ha))
  have hne : ∀ (b m : ℕ), Nat.card ↥M₀ = 2 ^ b * m →
      (m = 21 ∨ m = 45 ∨ m = 135 ∨ m = 189 ∨ m = 315 ∨ m = 9765 ∨ m = 239085) → False := by
    intro b m hb hm
    have hmo : Odd m := by
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact four_pow_sub_one_ne n hm (key b m hmo hb).symm
  have : Finite K := inferInstance
  obtain ⟨u, hu⟩ := card_eq_two_pow_mul_card_imageModCenter hM0K hZ2
  have hquot : ∀ (c m : ℕ), Nat.card (ModO2 M₀) = 2 ^ c * m →
      ∃ b, Nat.card ↥M₀ = 2 ^ b * m := by
    intro c m hc
    obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (G := ↥M₀) (p := 2))
    refine ⟨c + t, ?_⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥M₀), ht,
      show Nat.card (↥M₀ ⧸ CFSG.pCore 2 ↥M₀) = Nat.card (ModO2 M₀) from rfl, hc, pow_add]
    ring
  have hext : ∀ {X : Type} [Group X] {PV PY : ∀ (V : Type) [Group V], Prop} (k c m : ℕ),
      IsExt X PV PY → (∀ (N : Type) [Group N], PV N → Nat.card N = 2 ^ k) →
      (∀ (Y : Type) [Group Y], PY Y → Nat.card Y = 2 ^ c * m) →
      Nat.card X = 2 ^ (k + c) * m := by
    intro X _ PV PY k c m hX hPV hPY
    obtain ⟨N, _, hN, hQ, hcard⟩ := card_of_isExt hX
    rw [hcard, hPV _ hN, hPY _ hQ, pow_add]
    ring
  have himg : ∀ (k c m : ℕ) {PV PY : ∀ (V : Type) [Group V], Prop},
      IsExt ↥(imageModCenter K M₀) PV PY →
      (∀ (N : Type) [Group N], PV N → Nat.card N = 2 ^ k) →
      (∀ (Y : Type) [Group Y], PY Y → Nat.card Y = 2 ^ c * m) →
      Nat.card ↥M₀ = 2 ^ (u + (k + c)) * m := by
    intro k c m PV PY hX hPV hPY
    rw [hu, hext k c m hX hPV hPY, ← mul_assoc, ← pow_add]
  have h168 : ∀ (Y : Type) [Group Y], IsPSL 3 2 1 Y → Nat.card Y = 2 ^ 3 * 21 :=
    fun Y _ hY => (card_of_l32 hY).trans (by norm_num)
  have h20160 : ∀ (Y : Type) [Group Y], IsPSL 4 2 1 Y → Nat.card Y = 2 ^ 6 * 315 :=
    fun Y _ hY => (F420.card_of_l42 hY).trans (by norm_num)
  have h360 : ∀ (Y : Type) [Group Y], IsAlt 6 Y → Nat.card Y = 2 ^ 3 * 45 :=
    fun Y _ ⟨e⟩ => by rw [card_of_alt' (by norm_num) e]; decide
  have h2520 : ∀ (Y : Type) [Group Y], IsAlt 7 Y → Nat.card Y = 2 ^ 3 * 315 :=
    fun Y _ ⟨e⟩ => by rw [card_of_alt' (by norm_num) e]; decide
  have h1080 : ∀ (Y : Type) [Group Y], IsHat Y ↥(alternatingGroup (Fin 6)) →
      Nat.card Y = 2 ^ 3 * 135 :=
    fun Y _ hY => (card_of_isHat_alt6 hY).trans (by norm_num)
  have h60 : ∀ (Y : Type) [Group Y], IsPSL 2 2 2 Y → Nat.card Y = 2 ^ 2 * 15 :=
    fun Y _ hY => (F420.card_of_statedPSL_two_two hY).trans (by norm_num)
  have hE : ∀ k : ℕ, ∀ (N : Type) [Group N], IsE2 k N → Nat.card N = 2 ^ k :=
    fun k N _ hN => card_of_isE2 hN
  rcases hcase with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  · exact Or.inl c1
  ·
    exfalso
    obtain ⟨m, hm, -, -, -, h2⟩ := c2
    rcases h2 with ⟨hP, -⟩ | ⟨-, hX, -⟩
    · rcases hm with rfl | rfl
      · obtain ⟨b, hb⟩ := hquot 3 21 (h168 _ hP)
        exact hne b 21 hb (by norm_num)
      · obtain ⟨b, hb⟩ := hquot 6 315 (h20160 _ hP)
        exact hne b 315 hb (by norm_num)
    · exact hne _ 21 (hext 6 3 21 hX (hE 6) h168) (by norm_num)
  ·
    obtain ⟨hM22, h3 | h3 | h3⟩ := c3
    · have hn2 : n = 2 :=
        eq_two_of_four_pow_sub_one (key _ 15 (by decide) (himg 4 2 15 h3 (hE 4) h60)).symm
      exact Or.inr ⟨hn2, Or.inl ⟨hM22, h3⟩⟩
    · exact (hne _ 45 (himg 4 3 45 h3 (hE 4) h360) (by norm_num)).elim
    · exact (hne _ 21 (himg 3 3 21 h3 (hE 3) h168) (by norm_num)).elim
  ·
    obtain ⟨hM23, h4 | h4 | h4⟩ := c4
    · have hn2 : n = 2 :=
        eq_two_of_four_pow_sub_one (key _ 15 (by decide) (hext 4 2 15 h4 (hE 4) h60)).symm
      exact Or.inr ⟨hn2, Or.inr ⟨hM23, h4⟩⟩
    · exact (hne _ 315 (hext 4 3 315 h4 (hE 4) h2520) (by norm_num)).elim
    · exact (hne _ 21 (hext 3 3 21 h4 (hE 3) h168) (by norm_num)).elim
  ·
    exfalso
    obtain ⟨-, h5 | h5 | h5⟩ := c5
    · exact hne _ 135 (hext 6 3 135 h5 (hE 6) h1080) (by norm_num)
    · exact hne _ 315 (hext 4 6 315 h5 (hE 4) h20160) (by norm_num)
    · exact hne _ 21 (hext 6 3 21 h5 (hE 6) h168) (by norm_num)
  ·
    exfalso
    obtain ⟨-, h6 | h6 | h6⟩ := c6
    · exact hne _ 239085 (hext 11 10 239085 h6 (hE 11)
        (fun Y _ ⟨e⟩ => (Nat.card_congr e.toEquiv).trans
          (CFSG.Sporadic.Mathieu.card_M24.trans (by norm_num))))
        (by norm_num)
    · exact hne _ 21 (hext (3 + 12) 3 21 h6 (fun N _ hN => card_of_isSpecial2Group hN) h168)
        (by norm_num)
    · exact hne _ 9765 (hext 10 10 9765 h6 (hE 10)
        (fun Y _ hY => (F420.card_of_l52 hY).trans (by norm_num))) (by norm_num)
  ·
    exfalso
    obtain ⟨-, h7 | h7⟩ := c7
    · exact hne _ 21 (himg 6 3 21 h7 (fun N _ hN => card_of_isZ4Cubed hN) h168) (by norm_num)
    · exact hne _ 45 (himg 4 3 45 h7 (hE 4) h360) (by norm_num)
  ·
    exfalso
    exact hne _ 135 (hext 6 3 135 c8.2 (hE 6) h1080) (by norm_num)
  ·
    exfalso
    obtain ⟨-, h9 | h9⟩ := c9
    · exact hne _ 21 (himg (3 + 8) 3 21 h9 (fun N _ hN => card_of_isSpecial2Group hN) h168)
        (by norm_num)
    · exact hne _ 189 (himg 6 5 189 h9 (hE 6)
        (fun Y _ hY => (F420.card_of_u33 hY).trans (by norm_num))) (by norm_num)
  ·
    exfalso
    obtain ⟨-, -, hVA, -, hV16, -, -, -, α, hα, hker, -⟩ := c10
    refine hne (4 + 3) 21 ?_ (by norm_num)
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      card_statedSL_three_two, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hV16] at e1
    rw [e1]
    norm_num

omit [Finite G] in
theorem commutator_eq_bot_of_isComponentOf {K H P : Subgroup G} (hK : IsComponentOf K H)
    (hPH : P ≤ H) (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup 2 P) [Finite K] :
    ⁅K, P⁆ = ⊥ := by
  have hKperf : ⁅K, K⁆ = K := by
    have h1 := Subgroup.map_subtype_commutator K
    rw [hK.2.2.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have hbase : ⁅K, P ⊓ K⁆ = ⊥ := by
    have hKP : K ≤ Subgroup.normalizer ((P ⊓ K : Subgroup G) : Set G) := fun k hk =>
      mem_normalizer_inf (hHP (hK.1 hk)) (Subgroup.le_normalizer hk)
    have : ((P ⊓ K).subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKP
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK.2.2
        ((P ⊓ K).subgroupOf K) with hc | htop
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxc := hc (show (⟨x, hx.2⟩ : K) ∈ (P ⊓ K).subgroupOf K from hx)
      have := Subgroup.mem_center_iff.mp hxc ⟨k, hk⟩
      exact (congrArg Subtype.val this).symm
    · exfalso
      have hKP2 : IsPGroup 2 ↥K := by
        refine hP.to_le fun k hk => ?_
        have : (⟨k, hk⟩ : K) ∈ (P ⊓ K).subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
        exact this.1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2
      have : Group.IsPerfect ↥K := ⟨hK.2.2.1⟩
      have : Group.IsNilpotent ↥K := hKP2.isNilpotent
      have hsolv : Group.IsSolvable ↥K := inferInstance
      exact Group.IsPerfect.not_isSolvable ↥K hsolv
  have hstep : ∀ A B : Subgroup G, A ≤ B → B ≤ Subgroup.normalizer (A : Set G) →
      B ≤ Subgroup.normalizer (P : Set G) → K ≤ A → ⁅K, P ⊓ A⁆ = ⊥ → ⁅K, P ⊓ B⁆ = ⊥ := by
    intro A B hAB hBA hBP hKA hA
    set N := P ⊓ B with hN
    have hBN : B ≤ Subgroup.normalizer (N : Set G) := fun b hb =>
      mem_normalizer_inf (hBP hb) (Subgroup.le_normalizer hb)
    have h1 : ⁅A, N⁆ ≤ P ⊓ A := by
      have hA' : ⁅A, N⁆ ≤ A := commutator_le_left_of_le_normalizer (inf_le_right.trans hBA)
      have hN' : ⁅A, N⁆ ≤ N := commutator_le_right_of_le_normalizer (hAB.trans hBN)
      exact le_inf (hN'.trans inf_le_left) hA'
    have h2 : ⁅⁅K, N⁆, K⁆ = ⊥ := by
      have : ⁅⁅K, N⁆, K⁆ ≤ ⁅P ⊓ A, K⁆ :=
        Subgroup.commutator_mono ((Subgroup.commutator_mono hKA le_rfl).trans h1) le_rfl
      rw [Subgroup.commutator_comm (P ⊓ A) K, hA] at this
      exact le_bot_iff.mp this
    have h3 : ⁅⁅N, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm N K]
      exact h2
    have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
    rwa [hKperf] at h4
  have hind : ∀ A X : Subgroup G, IsSubnormal A X → X ≤ H → K ≤ A → ⁅K, P ⊓ A⁆ = ⊥ →
      ⁅K, P ⊓ X⁆ = ⊥ := by
    intro A X hAX
    induction hAX with
    | refl X => exact fun _ _ h => h
    | @step A B X hAB hAn hBX ih =>
      intro hXH hKA hA
      have hBX' : B ≤ X := A3.subnormal_le hBX
      refine ih hXH (hKA.trans hAB) (hstep A B hAB ?_ ((hBX'.trans hXH).trans hHP) hKA hA)
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hAn
  have := hind K H hK.2.1 le_rfl le_rfl hbase
  rwa [inf_eq_left.mpr hPH] at this

@[expose] def Insp436Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K R₀ : Subgroup G) (n : ℕ), 2 ≤ n →
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n → HypC28 H R M L V →
    CFSG.Open.IsComponentOf K H → C31Conclusion H R M L V K →
    (C31Case1 H R M L V K ∨ (n = 2 ∧ C436Two M L K)) →
    V ≤ pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) →
    IsPGroup 2 R₀ → R₀ ≤ H → R₀ ≤ Subgroup.normalizer (K : Set G) →
    R₀ ≤ Subgroup.centralizer (L : Set G) → ¬ R₀ ≤ Subgroup.centralizer (K : Set G) →
    H ⊓ Subgroup.normalizer (R₀ : Set G) ≤ M →
    C31Case1 H R M L V K ∧ IsPSp4 2 n (↥K ⧸ Subgroup.center ↥K)

@[expose] def Lemma436Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CFSG.Open.IsComponentOf K H →
      C31Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      C31Case1 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      IsPSp4 2 n (↥K ⧸ Subgroup.center ↥K) → False

theorem lemma436Comp_of (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hInsp : Insp436Sp4) (hSp4 : Lemma436Sp4) : Lemma436Comp := by
  intro G _ _ T M L n I H K t sk hK hC31
  classical
  set V := ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ with hV
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  set R := pCoreOf 2 I with hRdef
  set R₀ := R ⊓ Subgroup.centralizer (L : Set G) with hR₀
  have hn := sk.base.hyp.two_le
  have hLie := sk.base.hyp.lie
  have hLK := sk.L_le_K
  have hKH : K ≤ H := hK.1
  have h414 := lemma_4_1_4_five (sk.base.hyp4_2_3N.hyp4_1_1 h37 h38 h39) sk.base.isSigma
    sk.base.isGammaStar sk.base.inH sk.base.not_le_M
  have hO2HR : pCoreOf 2 H ≤ R := h414.2.2.1.trans h414.2.2.2
  have hO2H1 : pCoreOf 2 H ≠ ⊥ := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal sk.base.inM.1.1
  have hKcent : ⁅K, pCoreOf 2 H⁆ = ⊥ :=
    commutator_eq_bot_of_isComponentOf hK (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H)
      (pCoreOf_isPGroup 2 H)
  have hO2HC : pCoreOf 2 H ≤ Subgroup.centralizer (L : Set G) := by
    have h1 : pCoreOf 2 H ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKcent)
    exact h1.trans (Subgroup.centralizer_le hLK)
  have hR₀1 : R₀ ≠ ⊥ := fun h => hO2H1 (le_bot_iff.mp (h ▸ le_inf hO2HR hO2HC))
  have hR₀2 : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 I).to_le inf_le_left
  have hR43 : R = T ⊓ H ⊓ Rp := sk.base.lemma_4_3_4
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    sk.base.hyp.normal (sk.base.hyp.T_le hx)
  have hNR : ∀ x ∈ T, x ∈ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G) →
      x ∈ Subgroup.normalizer (R₀ : Set G) := by
    intro x hxT hxS
    have hxR : x ∈ Subgroup.normalizer (R : Set G) := by
      rw [hR43]
      exact mem_normalizer_inf hxS (sk.base.le_normalizer_Rp hxT)
    exact mem_normalizer_inf hxR (A4.mem_normalizer_centralizer (hTL hxT))
  have hX : L ⊔ (T ⊓ H ⊔ Subgroup.zpowers t) ≤ Subgroup.normalizer (R₀ : Set G) := by
    refine _root_.sup_le (fun l hl => ?_) (_root_.sup_le (fun s hs => ?_) ?_)
    · exact mem_normalizer_inf (le_normalizer_pCoreOf 2 I (sk.base.L_le_I hl))
        (A4.mem_normalizer_centralizer (Subgroup.le_normalizer hl))
    · exact hNR s hs.1 (Subgroup.le_normalizer hs)
    · exact Subgroup.zpowers_le.mpr (hNR t sk.t_mem sk.t_normalizer)
  have hNM : Subgroup.normalizer (R₀ : Set G) ≤ M :=
    isUniqueM_normalizer_le sk.lemma_4_3_5 hR₀1 hR₀2 hX
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    sk.base.le_normalizer_of_cComp hR hC h37 h38 h39 sk.cComp sk.S_le_normalizer
  have hR₀H : R₀ ≤ H := inf_le_left.trans (sk.base.pCoreOf_le_S.trans inf_le_right)
  have hR₀C : ¬ R₀ ≤ Subgroup.centralizer (K : Set G) := by
    intro hle
    have hKR : K ≤ Subgroup.centralizer (R₀ : Set G) := Subgroup.le_centralizer_iff.mp hle
    exact sk.not_le (le_inf hKH (hKR.trans
      ((Subgroup.centralizer_le_normalizer _).trans hNM)))
  have hVL : V ≤ L := sk.base.hyp421.V_le_L sk.base.hyp.normal
  have hVO : V ≤ pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
    have hVZ : V ≤ omegaOneCenterOf Rp := sk.base.hyp421.V_le sk.base.hyp.normal
    have hV2 : IsPGroup 2 V :=
      (sk.base.hyp.sylow.1.to_le inf_le_left).to_le (hVZ.trans (A4.omegaOneCenterOf_le _))
    have hLV : L ≤ Subgroup.normalizer (V : Set G) := by
      intro l hl
      apply mem_normalizer_of_map_conj_le
      rw [hV, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
        (normalizer_le_normalizer_omegaOneCenterOf Rp
          ((le_sup_left.trans (sk.base.hyp421.sup_le_normalizer_Rp sk.base.hyp.normal)) hl)),
        map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hl)]
    have hO2L : pCoreOf 2 L ≤ Rp :=
      le_inf (sk.base.hyp421.pCoreOf_L_le_T sk.base.hyp.normal)
        (pCoreOf_le_centralizerSection sk.base.hyp.L_le)
    refine le_inf (le_pCoreOf_of_le_normalizer 2 hVL hLV hV2) ?_
    exact (hVZ.trans ((A4.omegaOneCenterOf_le_centerOf _).trans
      (A4.centerOf_le_centralizer _))).trans (Subgroup.centralizer_le hO2L)
  have hC28 := sk.base.hyp4_2_3N.lemma_4_2_4N h36 h37 h38 h39 sk.base.inH sk.base.not_le_M
  have hcases := c31_cases_of_psl_two hn hLie hC31
  obtain ⟨hcase1, hSp⟩ := hInsp G H R (H ⊓ M) L V K R₀ n hn hLie hC28 hK hC31 hcases hVO hR₀2
    hR₀H (hR₀H.trans hHK) inf_le_right hR₀C (fun x hx => ⟨hx.1, hNM hx.2⟩)
  exact hSp4 G T M L n I H K t sk hK hC31 hcase1 hSp

end CFSG.Quasithin.H13.Ch4
