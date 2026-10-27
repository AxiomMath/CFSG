module

public import CFSG.Quasithin.H13.U3S1348I
public import CFSG.Quasithin.H13.U3S1349B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_pow_mem_of_relIndex_three {X H : Subgroup G} (h3 : X.relIndex H = 3) {x : G}
    (hx : x ∈ H) : ∃ a : ℕ, 0 < a ∧ a ≤ 3 ∧ x ^ a ∈ X := by
  classical
  have hcard : Nat.card (↥H ⧸ X.subgroupOf H) = 3 := by
    rw [← index, ← relIndex]
    exact h3
  let f : Fin 4 → ↥H ⧸ X.subgroupOf H := fun i => (((⟨x, hx⟩ : ↥H) ^ (i : ℕ) : ↥H) : _)
  have hf : ¬ Function.Injective f := fun hf => by
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at this
    omega
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  have key : ∀ i j : Fin 4, i < j → f i = f j → ∃ a : ℕ, 0 < a ∧ a ≤ 3 ∧ x ^ a ∈ X := by
    intro i j hlt h
    refine ⟨(j : ℕ) - i, by omega, by omega, ?_⟩
    have h1 := QuotientGroup.eq.1 h
    rw [mem_subgroupOf] at h1
    have e : (((⟨x, hx⟩ : ↥H) ^ (i : ℕ))⁻¹ * (⟨x, hx⟩ : ↥H) ^ (j : ℕ) : ↥H) =
        (⟨x, hx⟩ : ↥H) ^ ((j : ℕ) - i) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [e] at h1
    simpa using h1
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hij
  · exact key j i h hij.symm

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {X : Subgroup G} {x : G} {a : ℕ} (hxa : x ^ a ∈ X)
    (hco : Nat.Coprime a (orderOf x)) : x ∈ X := by
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.1 h1]
    exact one_mem X
  by_cases h0 : orderOf x = 0
  · rw [h0, Nat.coprime_zero_right] at hco
    rw [hco, pow_one] at hxa
    exact hxa
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega)
  have e : x = (x ^ a) ^ b := by
    rw [← pow_mul, ← pow_mod_orderOf, hb, pow_one]
  rw [e]
  exact pow_mem hxa b

theorem s134_V1_cases (S : A6.Setting134 G T L V) {z : G} (hz : z ∈ fsuV1 T V)
    (hzL : z ∉ centralizer (L : Set G)) {w : G} (hw : w ∈ fsuV1 T V) :
    w = 1 ∨ w = S.zV ∨ w = z ∨ w = z * S.zV := by
  obtain ⟨hzV, hψz⟩ := s134_psi_z S hz hzL
  obtain ⟨hwV, hwW⟩ := S.mem_V1_iff.1 hw
  have hcases := W1_cases _ (S.frame.ψ ⟨w, hwV⟩).2 hwW
  have hψ1 : (S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ : P6) = G6.allOnes 6 := by rw [S.psi_zV]
  have key : ∀ a b : G, ∀ (ha : a ∈ V) (hb : b ∈ V),
      (S.frame.ψ ⟨a, ha⟩ : P6) = S.frame.ψ ⟨b, hb⟩ → a = b := fun a b ha hb h =>
    congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
  have hmul : (S.frame.ψ ⟨z * S.zV, mul_mem hzV S.zV_mem_V⟩ : P6) =
      (S.frame.ψ ⟨z, hzV⟩ : P6) * G6.allOnes 6 := by
    rw [show (⟨z * S.zV, mul_mem hzV S.zV_mem_V⟩ : ↥V) = ⟨z, hzV⟩ * ⟨S.zV, S.zV_mem_V⟩
      from rfl, map_mul, Subgroup.coe_mul, hψ1]
  rcases hcases with h | h | h | h
  · left
    have h1 : S.frame.ψ ⟨w, hwV⟩ = 1 := Subtype.ext h
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff _).1 h1)
  · exact Or.inr (Or.inl (key _ _ hwV S.zV_mem_V (h.trans hψ1.symm)))
  · rcases hψz with hz' | hz'
    · exact Or.inr (Or.inr (Or.inl (key _ _ hwV hzV (h.trans hz'.symm))))
    · refine Or.inr (Or.inr (Or.inr (key _ _ hwV (mul_mem hzV S.zV_mem_V) ?_)))
      rw [hmul, hz', h, allOnes_eq_mul]
      decide
  · rcases hψz with hz' | hz'
    · refine Or.inr (Or.inr (Or.inr (key _ _ hwV (mul_mem hzV S.zV_mem_V) ?_)))
      rw [hmul, hz', h, allOnes_eq_mul]
      decide
    · exact Or.inr (Or.inr (Or.inl (key _ _ hwV hzV (h.trans hz'.symm))))

theorem s134_mem_centralizer_V1 (S : A6.Setting134 G T L V) {z : G} (hz : z ∈ fsuV1 T V)
    (hzL : z ∉ centralizer (L : Set G)) {x : G} (hxz : x * z = z * x)
    (hxzV : x * S.zV = S.zV * x) : x ∈ centralizer (fsuV1 T V : Set G) := by
  refine mem_centralizer_iff.2 fun w hw => ?_
  rcases s134_V1_cases S hz hzL hw with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hxzV.symm
  · exact hxz.symm
  · calc z * S.zV * x = z * (S.zV * x) := by group
      _ = z * (x * S.zV) := by rw [hxzV]
      _ = (z * x) * S.zV := by group
      _ = (x * z) * S.zV := by rw [hxz]
      _ = x * (z * S.zV) := by group

theorem s134_relIndex_HM {H I M : Subgroup G} (hIH : I ≤ H)
    (hHI : H ≤ normalizer (I : Set G)) (hI3 : (T ⊓ I).relIndex I = 3) (hTM : T ≤ M)
    (hIM : ¬ I ≤ M) (hdec : ∀ h ∈ H, ∃ i ∈ I, i⁻¹ * h ∈ H ⊓ M) :
    (H ⊓ M).relIndex H = 3 := by
  have hsup : I ⊔ (H ⊓ M) = H := by
    refine le_antisymm (sup_le hIH inf_le_left) fun h hh => ?_
    obtain ⟨i, hi, him⟩ := hdec h hh
    have e : h = i * (i⁻¹ * h) := by group
    rw [e]
    exact mul_mem (mem_sup_left hi) (mem_sup_right him)
  have h1 := relIndex_sup_eq (K := I) (T := H ⊓ M) (inf_le_left.trans hHI)
  rw [hsup] at h1
  rw [h1]
  have e : I ⊓ (H ⊓ M) = I ⊓ M := by
    rw [← inf_assoc, inf_eq_left.2 hIH]
  rw [e]
  rcases eq_or_eq_of_relIndex_three hI3 (le_inf inf_le_right (inf_le_left.trans hTM) :
      T ⊓ I ≤ I ⊓ M) inf_le_left with h | h
  · rw [h, hI3]
  · exact absurd (h ▸ inf_le_right) hIM

theorem inA4_pow_six : ∀ σ : Perm (Fin 6), InA4 σ → σ ^ 6 = 1 := by decide +kernel

theorem s134_two_three (h139 : A6.Stmt13_3_9) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {H : Subgroup G}
    (hHz : InHz T L V z H) (h3 : (H ⊓ normalizer (L : Set G)).relIndex H = 3) :
    ∀ x ∈ H, Nat.Coprime (orderOf x) 6 → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTsyl, -, hHzC, hO2H, hHM⟩ := s134_inHz_facts S hHz
  set Y := closure {x : G | x ∈ H ∧ Nat.Coprime (orderOf x) 6} with hY
  have hYH : Y ≤ H := (closure_le _).2 fun x hx => hx.1
  have hYM : Y ≤ normalizer (L : Set G) := by
    refine (closure_le _).2 fun x ⟨hxH, hco⟩ => ?_
    obtain ⟨a, ha0, ha3, hxa⟩ := exists_pow_mem_of_relIndex_three h3 hxH
    have hco' : Nat.Coprime a (orderOf x) := by
      have hdvd : a ∣ 6 := by interval_cases a <;> norm_num
      exact (Nat.Coprime.coprime_dvd_right hdvd hco).symm
    exact (mem_of_pow_mem_of_coprime hxa hco').2
  have hY2 : oTwoRes Y = Y := by
    refine le_antisymm (oTwoRes_le _) ((closure_le _).2 fun x hx => ?_)
    have hodd : Odd (orderOf x) := by
      have := Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) hx.2
      exact Nat.coprime_two_right.1 this
    exact mem_oTwoRes_of_odd (subset_closure hx) hodd (pow_orderOf_eq_one x)
  have hHY : H ≤ normalizer (Y : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun h hh y hy => ?_
    induction hy using closure_induction with
    | mem x hx =>
      refine subset_closure ⟨mul_mem (mul_mem hh hx.1) (inv_mem hh), ?_⟩
      have e : orderOf (h * x * h⁻¹) = orderOf x := by
        rw [show h * x * h⁻¹ = (MulAut.conj h).toMonoidHom x from rfl,
          orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective]
      rw [e]
      exact hx.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  rcases h139 G T L V H Y z S.h13 S.irr (s134_isA6On S) ⟨hTsyl.1, hO2H⟩ hHM hY2 hYH hHY hz hzL
    (le_inf hYM (hYH.trans hHzC)) with hY1 | ⟨-, hYL1, -⟩
  · intro x hx hco
    have : x ∈ Y := subset_closure ⟨hx, hco⟩
    rw [hY1] at this
    exact (mem_bot).1 this
  ·
    intro x hx hco
    have hxY : x ∈ Y := subset_closure ⟨hx, hco⟩
    rw [hYL1 he] at hxY
    have hxN : x ∈ normalizer (V : Set G) :=
      S.frame.L_le (((oTwoRes_le _).trans inf_le_left) hxY)
    have hA4 := s134_rho_L1 S hxN hxY
    have hρ6 := inA4_pow_six _ hA4
    have hρm : S.frame.ρ ⟨x, hxN⟩ ^ orderOf x = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(normalizer (V : Set G))) ^ orderOf x = 1 :=
        Subtype.ext (by simp)
      rw [this, map_one]
    have hρ1 := pow_gcd_eq_one.2 ⟨hρm, hρ6⟩
    rw [Nat.Coprime.gcd_eq_one hco, pow_one] at hρ1
    have hxC : x ∈ centralizer (V : Set G) := (s134_rho_eq_one_iff S _).1 hρ1
    have hxO : x ∈ pCoreOf 2 L := by
      rw [s134_pCoreOf_L_eq S he]
      exact ⟨((oTwoRes_le _).trans inf_le_left) hxY, hxC⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨x, hxO⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg := pow_gcd_eq_one.2 ⟨pow_orderOf_eq_one x, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k
      (Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) hco)), pow_one] at hg
    exact hg

theorem s134_HM_eq (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {H : Subgroup G}
    (hHz : InHz T L V z H) (h23 : ∀ x ∈ H, Nat.Coprime (orderOf x) 6 → x = 1) :
    H ⊓ normalizer (L : Set G) = L₁Of L (fsuV1 T V) ⊔ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set X := H ⊓ normalizer (L : Set G) with hX
  obtain ⟨hTsyl, hL1TH, hHzC, -, -⟩ := s134_inHz_facts S hHz
  have hL1X : L₁ ≤ X :=
    le_inf (le_sup_left.trans hL1TH) ((oTwoRes_le _).trans (inf_le_left.trans le_normalizer))
  have hTX : T ≤ X := le_inf hTsyl.1 S.T_le_NL
  refine le_antisymm ?_ (sup_le hL1X hTX)
  have hXN : X ≤ normalizer (L₁ : Set G) := by
    refine A5.le_normalizer_oTwoRes_of_le_normalizer fun x hx => ?_
    have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 (hHzC hx.1)
    have hxzV : x * S.zV = S.zV * x := by
      have h1 : x * S.zV * x⁻¹ = S.zV :=
        S.conj_zV ⟨x, A6.Setting134.normalizer_L_le S h1222 hx.2⟩
      calc x * S.zV = (x * S.zV * x⁻¹) * x := by group
        _ = S.zV * x := by rw [h1]
    have hxV1 := s134_mem_centralizer_V1 S hz hzL hxz hxzV
    exact mem_normalizer_inf_of hx.2 (le_normalizer (centralizer_le_normalizer _ hxV1))
  have hLn : (L₁.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hL1X).2 hXN
  have h3el : ∀ y ∈ H, (∃ m, Odd m ∧ y ^ m = 1) → ∃ k : ℕ, y ^ 3 ^ k = 1 := by
    rintro y hy ⟨m, hm, hym⟩
    obtain ⟨b, m', hm', hmm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
    refine ⟨b, h23 _ (pow_mem hy _) ?_⟩
    have hdvd : orderOf (y ^ 3 ^ b) ∣ m' := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, ← hmm, pow_orderOf_eq_one])
    have hodd : Odd (orderOf y) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
    have hm'odd : Odd m' := hodd.of_dvd_nat (Dvd.intro_left _ hmm.symm)
    have hco : Nat.Coprime m' 6 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl]
      exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 hm'odd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm').symm
    exact Nat.Coprime.coprime_dvd_left hdvd hco
  have hQ2 : IsPGroup 2 (↥X ⧸ L₁.subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, z', hz', hxyz, ⟨k, hyk⟩, m, hm, hzm⟩ := exists_two_odd_decomp (x : G)
    have hzX : z' ∈ X := zpowers_le.2 x.2 hz'
    have hyX : y ∈ X := zpowers_le.2 x.2 hy
    have hz'L1 : z' ∈ L₁ := s134_mem_L1_of_three h1332 h1228 S he hz hzL hzX.2 (hHzC hzX.1)
      (h3el z' hzX.1 ⟨m, hm, hzm⟩)
    have e : ((x : ↥X) : ↥X ⧸ L₁.subgroupOf X) = ((⟨y, hyX⟩ : ↥X) : ↥X ⧸ L₁.subgroupOf X) := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      show (x : G)⁻¹ * y ∈ L₁
      rw [hxyz]
      have e2 : (y * z')⁻¹ * y = z'⁻¹ * (y⁻¹ * y) := by group
      rw [e2, inv_mul_cancel, mul_one]
      exact inv_mem hz'L1
    refine ⟨k, ?_⟩
    rw [e, ← QuotientGroup.mk_pow]
    have : (⟨y, hyX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [this, QuotientGroup.mk_one]
  have hTsylX : IsSylowTwoOf T X := A5.isSylowTwoOf_of_le S.h13.sylow hTX
  set T' := (T.subgroupOf X).map (QuotientGroup.mk' (L₁.subgroupOf X)) with hT'
  have hdvd : T'.index ∣ (T.subgroupOf X).index :=
    index_map_dvd _ (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ2.index T'
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 ∣ T'.index := by
      rw [hn]
      exact dvd_pow_self 2 h
    exact hTsylX.2.2 (h2.trans hdvd)
  rw [hn0, pow_zero] at hn
  have hTtop : T' = ⊤ := index_eq_one.1 hn
  intro x hx
  have hmem : QuotientGroup.mk' (L₁.subgroupOf X) ⟨x, hx⟩ ∈ T' := by
    rw [hTtop]
    exact mem_top _
  obtain ⟨t, ht, hteq⟩ := hmem
  have h1 := QuotientGroup.eq.1 hteq
  rw [mem_subgroupOf] at h1
  have ht' : (t : G) ∈ T := mem_subgroupOf.1 ht
  have e : x = (t : G) * ((t : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_right ht') (mem_sup_left h1)

theorem s134_relIndex_L1T (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    (L₁Of L (fsuV1 T V) ⊓ T).relIndex (L₁Of L (fsuV1 T V)) = 3 := by
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1N : L₁ ≤ normalizer (fsuV1 T V : Set G) := (oTwoRes_le _).trans inf_le_right
  obtain ⟨y, hyL1, hyN, hyρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  have hKP : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ L₁ → S.frame.ρ x ∈ A6.P1sub :=
    fun x hx => inP1_of_pres45 _ (s134_pres45 S x (hL1N hx))
  have hOT : pCoreOf 2 L ≤ T :=
    (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have hCK : L₁ ⊓ centralizer (V : Set G) ≤ T := fun x hx => by
    have hxO : x ∈ pCoreOf 2 L := by
      rw [s134_pCoreOf_L_eq S he]
      exact ⟨hL1L hx.1, hx.2⟩
    exact hOT hxO
  exact s134_relIndex_three S A6.card_P1A6 hL1L hKP hCK (s134_T_le_normalizer_L1 S) hyL1
    (by rw [show (⟨y, S.frame.L_le (hL1L hyL1)⟩ : ↥(normalizer (V : Set G))) =
      ⟨y, hyN⟩ from rfl, hyρ]; exact gens_not_mem.2.2.1)

theorem s134_T_ne_r1 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    T ≠ r1Of T L V := by
  intro hTR
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  obtain ⟨y, hyL1, hyN, hyρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  have hyR : y ∈ normalizer (r1Of T L V : Set G) := by
    rw [← (s134Plus_L1 S he).pCoreOf_eq_r1Of]
    exact le_normalizer_pCoreOf 2 _ (mem_sup_left hyL1)
  obtain ⟨hD, hA, hnot⟩ := c012_conj_not_mem
  obtain ⟨t, htT, htσ⟩ := S.frame.DA_T _ hD hA
  have hyt : y * (t : G) * y⁻¹ ∈ T := by
    rw [hTR] at htT ⊢
    exact (mem_normalizer_iff.mp hyR t).mp htT
  have hD' := S.frame.T_D ⟨y * t * y⁻¹, S.frame.T_le hyt⟩ hyt
  apply hnot
  have e : (⟨y * t * y⁻¹, S.frame.T_le hyt⟩ : ↥(normalizer (V : Set G))) =
      ⟨y, hyN⟩ * t * ⟨y, hyN⟩⁻¹ := rfl
  rwa [e, map_mul, map_mul, map_inv, hyρ, htσ] at hD'

theorem s134_relIndex_TH (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {H : Subgroup G}
    (hHM3 : (H ⊓ normalizer (L : Set G)).relIndex H = 3)
    (hHM : H ⊓ normalizer (L : Set G) = L₁Of L (fsuV1 T V) ⊔ T) : T.relIndex H = 9 := by
  have hTX : T ≤ H ⊓ normalizer (L : Set G) := hHM ▸ le_sup_right
  have h1 := relIndex_mul_relIndex T (H ⊓ normalizer (L : Set G)) H hTX inf_le_left
  rw [hHM3] at h1
  rw [← h1, hHM, relIndex_sup_eq (s134_T_le_normalizer_L1 S), s134_relIndex_L1T S he]

end CFSG.Quasithin.H13.U3
