module

public import CFSG.Quasithin.H13.NQS1312B
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.EmptyFaithful.Insp9Tr
public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent1
public import CFSG.Quasithin.H13.NQS1312L
public import CFSG.Quasithin.H13.NQS1312Y

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sixteen_le_relIndex_of_lperp {V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6} {K X C : Subgroup G} {k₁ : G} (hk₁K : k₁ ∈ K)
    (hk₁ : k₁ ∈ normalizer (V : Set G)) (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL)
    (hX : ∀ c ∈ lperpList, ptOf Φ (vecOf c) ∈ X) (hCK : C ≤ centralizer (K : Set G)) :
    16 ≤ C.relIndex X := by
  classical
  have : Fintype (↥X ⧸ C.subgroupOf X) := Fintype.ofFinite _
  let f : ℕ → ↥X ⧸ C.subgroupOf X := fun c =>
    if hc : c ∈ lperpList then QuotientGroup.mk ⟨ptOf Φ (vecOf c), hX c hc⟩ else QuotientGroup.mk 1
  have hinj : Set.InjOn f lperpList.toFinset := by
    intro c hc c' hc' h
    rw [Finset.mem_coe, List.mem_toFinset] at hc hc'
    simp only [f, hc, hc', ↓reduceDIte] at h
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    exact lperp_eq_of_mem_centralizer hk₁K hk₁ hτ hc hc' (hCK (by simpa using h1))
  have h := Finset.card_le_card_of_injOn f (fun c _ => Finset.mem_univ (f c)) hinj
  rw [List.toFinset_card_of_nodup lperp_spec.2.2.2.1, lperp_spec.2.2.2.2, Finset.card_univ,
    ← Nat.card_eq_fintype_card] at h
  exact h

theorem sixteen_le_relIndex_fixSub_V {V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6} (hV64 : Nat.card V = 64) {k₁ : G}
    (hk₁ : k₁ ∈ normalizer (V : Set G)) (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL) :
    16 ≤ (fixSub V ⊥ k₁ (le_normalizer_bot_line V)).relIndex V := by
  classical
  set F := fixSub V ⊥ k₁ (le_normalizer_bot_line V) with hF
  have hsub : (F : Set G) ⊆ ↑({ptOf Φ (vecOf 0), ptOf Φ (vecOf 15), ptOf Φ (vecOf 52),
      ptOf Φ (vecOf 59)} : Finset G) := by
    intro v hv
    obtain ⟨hvV, hkv⟩ := mem_fixSub_bot.1 hv
    obtain ⟨c, hc, hcv⟩ := exists_vecOf (Φ (Additive.ofMul ⟨v, hvV⟩))
    have hv' : v = ptOf Φ (vecOf c) := by rw [hcv]; exact eq_ptOf hvV
    rw [hv', conj_ptOf_k hk₁ hτ c] at hkv
    have h1 := vecOf_injective (kc_lt c hc) hc (ptOf_injective hkv)
    rcases (kc_fix_iff c hc).1 h1 with h | h | h | h <;> subst h <;> simp [hv']
  have hcard : Nat.card F ≤ 4 := by
    calc Nat.card F = Nat.card (F : Set G) := rfl
      _ ≤ Nat.card ↑({ptOf Φ (vecOf 0), ptOf Φ (vecOf 15), ptOf Φ (vecOf 52),
          ptOf Φ (vecOf 59)} : Finset G) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 4 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
  have h1 : F.relIndex V * Nat.card F = Nat.card V := by
    rw [← Subgroup.relIndex_mul_card (H := F) (K := V), inf_of_le_left (fixSub_le _)]
  rw [hV64] at h1
  have hpos : 0 < Nat.card F := Nat.card_pos
  nlinarith

omit [Finite G] in
theorem card_mult_fin3 {F : Type} [Field F] [Fintype F] (h : Fintype.card F = 2) :
    Nat.card (Multiplicative (Fin 3 → F)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, h]
  norm_num

omit [Finite G] in
theorem card_mult_fin1_fin3 {F : Type} [Field F] [Fintype F] (h : Fintype.card F = 2) :
    Nat.card (Multiplicative (Fin 1 → Fin 3 → F)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, h]
  norm_num

omit [Finite G] in
theorem card_mult_fin2_fin3 {F : Type} [Field F] [Fintype F] (h : Fintype.card F = 2) :
    Nat.card (Multiplicative (Fin 2 → Fin 3 → F)) = 64 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, h]
  norm_num

omit [Finite G] in
theorem exists_fixed_vec_line {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (M : Matrix (Fin 3) (Fin 3) F) (hM : M ^ 3 = 1) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ M.mulVec v = v := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : Function.End (Fin 3 → F) := fun v => M.mulVec v
  have hφ3 : φ ^ 3 = 1 := by
    funext v
    show M.mulVec (M.mulVec (M.mulVec v)) = v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hM, Matrix.one_mulVec]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := φ) (by simpa using hφ3)
  have hcard : Fintype.card (Fin 3 → F) = 8 := by
    rw [Fintype.card_fun, Fintype.card_fin, hF]
    norm_num
  rw [hcard] at hmod
  have h1 : 1 < Fintype.card (Function.fixedPoints φ) := by
    have h0 : 0 < Fintype.card (Function.fixedPoints φ) :=
      Fintype.card_pos_iff.2 ⟨⟨0, show M.mulVec 0 = 0 from Matrix.mulVec_zero M⟩⟩
    have h2 : Fintype.card (Function.fixedPoints φ) % 3 = 2 := hmod.symm
    omega
  obtain ⟨⟨v, hv⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card h1
    ⟨0, show M.mulVec 0 = 0 from Matrix.mulVec_zero M⟩
  exact ⟨v, fun h => hne (Subtype.ext h), hv⟩

theorem relIndex_fixSub_le_sixteen_of_sum {K W : Subgroup G} {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hKW : K ≤ normalizer (W : Set G)) (β : ↥W →* Multiplicative (Fin 2 → Fin 3 → F))
    (hβs : Function.Surjective β) (hβi : Function.Injective β)
    (hβeq : ∀ (a : ↥K) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : Matrix.GeneralLinearGroup (Fin 3) F)).mulVec
          (Multiplicative.toAdd (β u) i))
    {k : G} (hkK : k ∈ K) (hk3 : k ^ 3 = 1) :
    (fixSub W ⊥ k (le_normalizer_bot_line W)).relIndex W ≤ 16 := by
  classical
  set M : Matrix (Fin 3) (Fin 3) F :=
    ((α ⟨k, hkK⟩ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hM
  have hM3 : M ^ 3 = 1 := by
    have h1 : (⟨k, hkK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    have h2 : α ⟨k, hkK⟩ ^ 3 = 1 := by rw [← map_pow, h1, map_one]
    have h3 : ((α ⟨k, hkK⟩ : Matrix.GeneralLinearGroup (Fin 3) F)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]
    rw [hM, ← Units.val_pow_eq_pow_val, h3, Units.val_one]
  obtain ⟨v, hv0, hMv⟩ := exists_fixed_vec_line hF M hM3
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 v))
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have h1 : u = 1 := Subtype.ext h
    rw [h1, map_one] at hu
    have h2 := congrArg (fun x : Multiplicative (Fin 2 → Fin 3 → F) => Multiplicative.toAdd x 0) hu
    simp only [toAdd_one, toAdd_ofAdd, Pi.single_eq_same, Pi.zero_apply] at h2
    exact hv0 h2.symm
  have hmem : k * (u : G) * k⁻¹ ∈ W := (mem_normalizer_iff.1 (hKW hkK) u).1 u.2
  have hfix : k * (u : G) * k⁻¹ = u := by
    have h1 : β ⟨k * u * k⁻¹, hmem⟩ = β u := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [hβeq ⟨k, hkK⟩ u ⟨k * u * k⁻¹, hmem⟩ rfl i, hu]
      have hmod : moduleAct false (α ⟨k, hkK⟩ : Matrix.GeneralLinearGroup (Fin 3) F) = M := by
        simp [moduleAct, hM]
      rw [hmod, toAdd_ofAdd]
      fin_cases i
      · simpa using hMv
      · simp
    exact congrArg Subtype.val (hβi h1)
  set C := fixSub W ⊥ k (le_normalizer_bot_line W) with hC
  have huC : (u : G) ∈ C := mem_fixSub_bot.2 ⟨u.2, hfix⟩
  have hC2 : 1 < Nat.card C := by
    refine (Subgroup.one_lt_card_iff_ne_bot C).2 fun h => hu1 ?_
    rw [h] at huC
    exact Subgroup.mem_bot.1 huC
  have hW64 : Nat.card W = 64 := by
    rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hβi, hβs⟩).toEquiv, card_mult_fin2_fin3 hF]
  have h1 : C.relIndex W * Nat.card C = Nat.card W := by
    rw [← Subgroup.relIndex_mul_card (H := C) (K := W), inf_of_le_left (fixSub_le _)]
  rw [hW64] at h1
  have hW3 : ¬ 3 ∣ Nat.card W := by rw [hW64]; norm_num
  have hmod3 := relIndex_fixSub_bot_modEq hk3 (hKW hkK) hW3
  have hdvd : C.relIndex W ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hW64]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [he] at h1 hmod3 ⊢
  have he5 : e ≤ 5 := by
    by_contra h
    have h6 : 2 ^ 6 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  interval_cases e <;> simp_all [Nat.ModEq]

theorem relIndex_fixSub_bot_mono {X Y : Subgroup G} {k : G} (hXY : X ≤ Y) :
    (fixSub X ⊥ k (le_normalizer_bot_line X)).relIndex X ≤
      (fixSub Y ⊥ k (le_normalizer_bot_line Y)).relIndex Y := by
  have h : fixSub X ⊥ k (le_normalizer_bot_line X) =
      fixSub Y ⊥ k (le_normalizer_bot_line Y) ⊓ X := by
    ext a
    rw [Subgroup.mem_inf, mem_fixSub_bot, mem_fixSub_bot]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hXY h1, h2⟩, h1⟩, fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, h2⟩⟩
  rw [h, Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_le_of_le_right hXY (relIndex_pos_line _ _).ne'

theorem relIndex_inf_pCoreOf_le_eight {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 P)
    (h168 : (pCoreOf 2 K).relIndex K = 168) : (P ⊓ pCoreOf 2 K).relIndex P ≤ 8 := by
  have hPO : P ≤ normalizer (pCoreOf 2 K : Set G) :=
    hPK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have h2 : (pCoreOf 2 K).relIndex (P ⊔ pCoreOf 2 K) = (pCoreOf 2 K).relIndex P :=
    CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hPO
  have h3 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 K) (P ⊔ pCoreOf 2 K) K le_sup_right
    (sup_le hPK (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  have hdvd168 : (pCoreOf 2 K).relIndex P ∣ 168 := by
    rw [← h168, ← h3, h2]
    exact dvd_mul_right _ _
  have hdvdP : (pCoreOf 2 K).relIndex P ∣ Nat.card P := Subgroup.relIndex_dvd_card _ _
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
  rw [hm] at hdvdP
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvdP
  rw [Subgroup.inf_relIndex_left, he]
  rw [he] at hdvd168
  have he3 : e ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 2 ^ e := Nat.pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd168
    norm_num at this
  calc 2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) he3
    _ = 8 := by norm_num

omit [Finite G] in
theorem exists_sl3F2_line {K VK Mx : Subgroup G} (hKV : K ≤ normalizer (VK : Set G))
    (hker : (SBc17.actOn hKV).ker = CFSG.pCore 2 ↥K)
    {F : Type} [Field F] [Fintype F] (hcard : Fintype.card F = 2)
    (e : ↥(autOn K VK) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K VK) (autOn (Mx ⊓ K) VK)) :
    ∃ (β : ↥K →* SL3F2) (P : Subgroup SL3F2), IsMaxParabolic2 (⊤ : Subgroup SL3F2) P ∧
      (∀ y : ↥K, β y = 1 ↔ (y : G) ∈ pCoreOf 2 K) ∧
      (∀ (m : G) (hm : m ∈ Mx ⊓ K), β ⟨m, hm.2⟩ ∈ P) ∧
      ∀ y ∈ P, ∃ (m : G) (hm : m ∈ Mx ⊓ K), β ⟨m, hm.2⟩ = y := by
  have hF2 : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hcard]
  set e₃ : ↥(autOn K VK) ≃* SL3F2 :=
    (e.trans (Insp9.statedSLEquivZMod2 F hF2 3)).trans
      (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm with he₃
  set π := SBc17.actOn hKV with hπ
  refine ⟨e₃.toMonoidHom.comp π, ((autOn (Mx ⊓ K) VK).subgroupOf (autOn K VK)).map e₃.toMonoidHom,
    QP.isMaxParabolic2_top_of_mulEquiv hmax e₃, fun y => ?_, fun m hm => ?_, ?_⟩
  · rw [coe_mem_pCoreOf_iff_line, ← hker, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · refine ⟨π ⟨m, hm.2⟩, ?_, rfl⟩
    show ((π ⟨m, hm.2⟩ : ↥(autOn K VK)) : MulAut ↥VK) ∈ autOn (Mx ⊓ K) VK
    rw [hπ, SBc17.coe_actOn]
    exact SBc17.mem_autOn_iff.2 ⟨m, hKV hm.2, hm, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : MulAut ↥VK) ∈ autOn (Mx ⊓ K) VK := hs
    obtain ⟨b, hbV, hb, hbs⟩ := SBc17.mem_autOn_iff.mp hs'
    refine ⟨b, hb, ?_⟩
    have hsπ : s = π ⟨b, hb.2⟩ :=
      Subtype.ext (by rw [hπ, SBc17.coe_actOn]; exact hbs.symm)
    rw [hsπ]
    rfl

theorem exists_mem_not_fixSub_line
    {T L V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6} (hTL : T ≤ normalizer (L : Set G))
    (hLV : L ≤ normalizer (V : Set G)) (hCL : L ⊓ centralizer (V : Set G) = pCoreOf 2 L)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hMhV : lineH Φ ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G))
    {K VK : Subgroup G} (hKV : K ≤ normalizer (VK : Set G))
    (hker : (SBc17.actOn hKV).ker = CFSG.pCore 2 ↥K) (hVO : V ⊓ K ≤ pCoreOf 2 K)
    {F : Type} [Field F] [Fintype F] (hcard : Fintype.card F = 2)
    (e : ↥(autOn K VK) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K VK) (autOn ((lineH Φ ⊓ normalizer (L : Set G)) ⊓ K) VK))
    {k₁ : G} (hk₁L : k₁ ∈ L) (hk₁K : k₁ ∈ K) (hk₁H : k₁ ∈ lineH Φ) (hk₁3 : orderOf k₁ = 3)
    (hk₁τ : tau Φ ⟨k₁, hLV hk₁L⟩ = kGL) :
    ∃ u ∈ pCoreOf 2 (L ⊔ T), u⁻¹ * (k₁ * u * k₁⁻¹) ∉ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mh := lineH Φ ⊓ normalizer (L : Set G) with hMh
  obtain ⟨β, Ppar, hP, hβ1, hβP, hPβ⟩ := exists_sl3F2_line hKV hker hcard e hmax
  obtain ⟨U, hUP, hUn, hU2, ⟨u₀, hu₀U, hu₀1⟩, hUfpf⟩ := exists_radical_of_isMaxParabolic2 hP
  have hk₁M : k₁ ∈ Mh ⊓ K := ⟨⟨hk₁H, Subgroup.le_normalizer hk₁L⟩, hk₁K⟩
  set κ := β ⟨k₁, hk₁K⟩ with hκ
  have hκP : κ ∈ Ppar := hβP k₁ hk₁M
  have hk₁3' : k₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one k₁
    rwa [hk₁3] at h
  have hκ3 : κ ^ 3 = 1 := by
    have h1 : (⟨k₁, hk₁K⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hk₁3')
    rw [hκ, ← map_pow, h1, map_one]
  have hκ1 : κ ≠ 1 := by
    intro h
    have hk₁O := (hβ1 _).1 h
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨k₁, hk₁O⟩
    have h2 : k₁ ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hk₁3] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  obtain ⟨m₀, hm₀, hm₀u⟩ := hPβ u₀ (hUP hu₀U)
  have huK : m₀ * k₁ * m₀⁻¹ * k₁⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hm₀.2 hk₁K) (K.inv_mem hm₀.2)) (K.inv_mem hk₁K)
  set u := m₀ * k₁ * m₀⁻¹ * k₁⁻¹ with hu
  have hβu : β ⟨u, huK⟩ = u₀ * κ * u₀⁻¹ * κ⁻¹ := by
    rw [show (⟨u, huK⟩ : ↥K) = ⟨m₀, hm₀.2⟩ * ⟨k₁, hk₁K⟩ * ⟨m₀, hm₀.2⟩⁻¹ * ⟨k₁, hk₁K⟩⁻¹ from rfl,
      map_mul, map_mul, map_mul, map_inv, map_inv, hm₀u]
  have hβuU : β ⟨u, huK⟩ ∈ U := by
    rw [hβu]
    have e1 : u₀ * κ * u₀⁻¹ * κ⁻¹ = u₀ * (κ * u₀⁻¹ * κ⁻¹) := by group
    rw [e1]
    exact U.mul_mem hu₀U (hUn κ hκP _ (U.inv_mem hu₀U))
  have hβu1 : β ⟨u, huK⟩ ≠ 1 := by
    rw [hβu]
    intro h
    refine hUfpf κ hκP hκ3 hκ1 u₀ hu₀U hu₀1 ?_
    calc κ * u₀ = (u₀ * κ * u₀⁻¹ * κ⁻¹)⁻¹ * (u₀ * κ) := by group
      _ = u₀ * κ := by rw [h, inv_one, one_mul]
  set R : Subgroup G := Mh ⊓ (U.comap β).map K.subtype with hR
  have hR2 : IsPGroup 2 R := by
    rintro ⟨r, hrM, x, hx, rfl⟩
    obtain ⟨a, ha⟩ := hU2 ⟨β x, hx⟩
    have h1 : β (x ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨_, (hβ1 _).1 h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 : ((x : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_subtype]
    rw [pow_add, pow_mul]
    exact h2
  have hRN : R ≤ normalizer (V : Set G) := fun r hr => hMhV hr.1
  have hRc : ∀ r ∈ R, r * ptOf Φ (vecOf 15) * r⁻¹ = ptOf Φ (vecOf 15) ∧
      r * ptOf Φ (vecOf 52) * r⁻¹ = ptOf Φ (vecOf 52) := by
    intro r hr
    have hy : r ∈ lineH Φ := hr.1.1
    rw [lineH, mem_centralizer_iff] at hy
    refine ⟨?_, ?_⟩
    · rw [← hy _ (Set.mem_insert _ _)]; group
    · rw [← hy _ (Set.mem_insert_of_mem _ rfl)]; group
  have hkR : ∀ r ∈ R, k₁ * r * k₁⁻¹ ∈ R := by
    rintro r ⟨hrM, x, hx, rfl⟩
    have hx' : β x ∈ U := by
      rw [SetLike.mem_coe, Subgroup.mem_comap] at hx
      exact hx
    refine ⟨Mh.mul_mem (Mh.mul_mem hk₁M.1 hrM) (Mh.inv_mem hk₁M.1),
      ⟨k₁, hk₁K⟩ * x * ⟨k₁, hk₁K⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hUn κ hκP _ hx'
  have hRC := le_centralizer_of_isPGroup hΦN (hLV hk₁L) hk₁τ hR2 hRN hRc hkR
  have hm₀K : m₀ ∈ K := hm₀.2
  have hm₀R : m₀ ∈ R := by
    refine ⟨hm₀.1, ⟨m₀, hm₀K⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, hm₀u]
    exact hu₀U
  have huR : u ∈ R := by
    have e1 : u = m₀ * (k₁ * m₀⁻¹ * k₁⁻¹) := by rw [hu]; group
    rw [e1]
    exact R.mul_mem hm₀R (hkR _ (R.inv_mem hm₀R))
  have huL : u ∈ L := L.mul_mem ((mem_normalizer_iff.1 hm₀.1.2 k₁).1 hk₁L) (L.inv_mem hk₁L)
  have huQ : u ∈ pCoreOf 2 (L ⊔ T) := by
    have h1 : u ∈ L ⊓ centralizer (V : Set G) := ⟨huL, hRC huR⟩
    rw [hCL] at h1
    exact SBc17.pCoreOf_le_pCoreOf_sup hTL h1
  refine ⟨u, huQ, fun hw => ?_⟩
  have hwK : u⁻¹ * (k₁ * u * k₁⁻¹) ∈ K :=
    K.mul_mem (K.inv_mem huK) (K.mul_mem (K.mul_mem hk₁K huK) (K.inv_mem hk₁K))
  have h1 : β ⟨_, hwK⟩ = 1 := (hβ1 _).2 (hVO ⟨hw, hwK⟩)
  rw [show (⟨_, hwK⟩ : ↥K) = ⟨u, huK⟩⁻¹ * (⟨k₁, hk₁K⟩ * ⟨u, huK⟩ * ⟨k₁, hk₁K⟩⁻¹) from rfl,
    map_mul, map_mul, map_mul, map_inv, map_inv, ← hκ] at h1
  refine hUfpf κ hκP hκ3 hκ1 _ hβuU hβu1 ?_
  calc κ * β ⟨u, huK⟩ = β ⟨u, huK⟩ * ((β ⟨u, huK⟩)⁻¹ * (κ * β ⟨u, huK⟩ * κ⁻¹)) * κ := by group
    _ = β ⟨u, huK⟩ * κ := by rw [h1, mul_one]

end CFSG.Quasithin.H13.U3.NLine
