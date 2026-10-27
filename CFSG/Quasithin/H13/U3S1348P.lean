module

public import CFSG.Quasithin.H13.U3S1348O
public import CFSG.Quasithin.H13.U3S1348N

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement IsMulCommutative

theorem exists_lift_of_isPGroup {X Q : Type*} [Group X] [Finite X] [Group Q] (π : X →* Q)
    (hπ : Function.Surjective π) (hker : ∀ x : X, π x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup Q} (hE : IsPGroup p E) :
    ∃ E' : Subgroup X, E'.map π = E ∧ ∀ a ∈ E', ∀ b ∈ E', π a = π b → a = b := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite Q := Finite.of_surjective π hπ
  obtain ⟨Qs, hEQ⟩ := hE.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hπ p Qs
  have hSQ : (S : Subgroup X).map π = Qs := by rw [← hS]; rfl
  have hinj : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), π a = π b → a = b := by
    intro a ha b hb hab
    have hk : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    obtain ⟨i, hi⟩ := hker _ hk
    have hs : a⁻¹ * b ∈ (S : Subgroup X) := Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb
    obtain ⟨j, hj⟩ := S.isPGroup' ⟨_, hs⟩
    have hj' : (a⁻¹ * b) ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hi) (Nat.Coprime.pow_left i
        (Nat.Coprime.pow_right j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)))))
      (orderOf_dvd_of_pow_eq_one hj')
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
    exact h1
  refine ⟨E.comap π ⊓ (S : Subgroup X), le_antisymm (fun _ ⟨s, hs, hse⟩ => hse ▸ hs.1)
    fun e he => ?_, fun a ha b hb => hinj a ha.2 b hb.2⟩
  have heQ : e ∈ (S : Subgroup X).map π := hSQ ▸ hEQ he
  obtain ⟨s, hs, rfl⟩ := heQ
  exact ⟨s, ⟨he, hs⟩, rfl⟩

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_hat_E9 (S : A6.Setting134 G T L V)
    (hhat : IsHatA6 L) :
    ∃ X : Subgroup G, X ≤ L₁Of L (fsuV1 T V) ∧ IsElemAbelian 3 X ∧ Nat.card X = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have P := s134Plus_l1plus S hhat
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := l0_decomp hhat
  obtain ⟨d, hdLp, hd3, hdNV, hdρ⟩ := P.exists_cube
    (inA4_cube_mem_C3 c012 c012_props.2.2 c012_props.2.1)
  have hcL1 : c ∈ L₁ := s134_l0_le_L1 S hcl0
  have hdL1 : d ∈ L₁ := P.le_L1 hdLp
  have hcL : c ∈ L := l0_le_L hcl0
  have hdL : d ∈ L := P.le_L hdLp
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hcl0
  have hcV : c ∈ centralizer (V : Set G) := s134_o2Z_le_centralizer S hcZ
  have hOV : pCoreOf 2 L ≤ centralizer (V : Set G) := s134_pCoreOf_L_le S
  have hNV1 : ∀ x ∈ L₁, x ∈ normalizer (fsuV1 T V : Set G) := fun x hx =>
    (mem_inf.1 (oTwoRes_le _ hx)).2
  have hCV1 : centralizer (V : Set G) ≤ normalizer (fsuV1 T V : Set G) :=
    (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)).trans (centralizer_le_normalizer _)
  have hcube : ∀ {x : G} {k : ℕ}, x ^ 2 ^ k = 1 → x ^ 3 = 1 → x = 1 := fun h2 h3 =>
    cube_two_pow_eq_one h2 h3
  have hcO2 : c ∉ pCoreOf 2 L := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨c, h⟩
    have h1 := hcube (by simpa using congrArg Subtype.val hk) hc3
    exact hcO (h1 ▸ one_mem _)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hπ1 : ∀ x : ↥L, π x = 1 ↔ (x : G) ∈ pCoreOf 2 L := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, AppC.mem_pCore_iff_mem_blockQ]
    exact Iff.rfl
  have hker : ∀ x : ↥L, π x = 1 → ∃ i : ℕ, x ^ 2 ^ i = 1 := by
    intro x hx
    obtain ⟨i, hi⟩ := pCoreOf_isPGroup 2 L ⟨x, (hπ1 x).1 hx⟩
    exact ⟨i, Subtype.ext (by simpa using congrArg Subtype.val hi)⟩
  set cb := π ⟨c, hcL⟩ with hcb
  set db := π ⟨d, hdL⟩ with hdb
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← map_pow]
    exact (hπ1 _).2 (by simp [hc3])
  have hdb3 : db ^ 3 = 1 := by
    rw [hdb, ← map_pow]
    exact (hπ1 _).2 (by simp [hd3])
  have hcb1 : cb ≠ 1 := fun h => hcO2 ((hπ1 _).1 h)
  have hcd : cb * db = db * cb := by
    have h1 : π (⟨c, hcL⟩ * ⟨d, hdL⟩ * (⟨c, hcL⟩)⁻¹ * (⟨d, hdL⟩)⁻¹) = 1 :=
      (hπ1 _).2 ((mem_o2Z_iff.1 hcZ).2 d hdL)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc cb * db = (cb * db * cb⁻¹ * db⁻¹) * (db * cb) := by group
      _ = db * cb := by rw [h1, one_mul]
  have hbot : IsElemAbelian 3 (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).1 hx, one_pow]⟩
  obtain ⟨hA₁, -⟩ := elemAbelian_sup_zpowers hbot (fun h => hcb1 ((mem_bot).1 h)) hcb3
    (fun a ha => by rw [(mem_bot).1 ha, one_mul, mul_one])
  have hdbA : db ∉ (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ⊔ zpowers cb := by
    rw [bot_sup_eq]
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have h1 : π ((⟨d, hdL⟩ : ↥L) * (⟨c, hcL⟩ : ↥L) ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, ← hcb, ← hdb, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
    have h2 := hOV ((hπ1 _).1 h1)
    have hρ : S.frame.ρ (⟨d, hdNV⟩ * ⟨c, S.frame.L_le hcL⟩ ^ (-k)) = 1 := by
      refine (s134_rho_eq_one_iff S _).2 ?_
      simpa using h2
    rw [map_mul, map_zpow, (s134_rho_eq_one_iff S ⟨c, S.frame.L_le hcL⟩).2 hcV, one_zpow,
      mul_one, hdρ] at hρ
    exact absurd hρ (by decide)
  obtain ⟨hE, -⟩ := elemAbelian_sup_zpowers hA₁ hdbA hdb3 (by
    have hle : (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) ⊔ zpowers cb ≤
        centralizer ({db} : Set (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      sup_le bot_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hcd))
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha))
  set E := (⊥ ⊔ zpowers cb) ⊔ zpowers db with hEdef
  have hEp : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨E', hE'map, hinj⟩ := exists_lift_of_isPGroup π (QuotientGroup.mk'_surjective _) hker
    Nat.prime_three (by norm_num) hEp
  have hcbE : cb ∈ E := mem_sup_left (mem_sup_right (mem_zpowers cb))
  have hdbE : db ∈ E := mem_sup_right (mem_zpowers db)
  rw [← hE'map] at hcbE hdbE
  obtain ⟨c₀, hc₀, hc₀π⟩ := hcbE
  obtain ⟨d₀, hd₀, hd₀π⟩ := hdbE
  have hπE : ∀ x ∈ E', π x ∈ E := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hcube' : ∀ x ∈ E', x ^ 3 = 1 := fun x hx => hinj _ (pow_mem hx 3) _ (one_mem _) (by
    rw [map_pow, map_one]
    exact hE.2 _ (hπE x hx))
  have hcomm' : c₀ * d₀ = d₀ * c₀ := hinj _ (mul_mem hc₀ hd₀) _ (mul_mem hd₀ hc₀) (by
    rw [map_mul, map_mul, hc₀π, hd₀π, hcd])
  have hmemL1 : ∀ (x : ↥L) (y : G) (hy : y ∈ L), y ∈ L₁ → π x = π ⟨y, hy⟩ → x ^ 3 = 1 →
      (x : G) ∈ L₁ := by
    intro x y hy hyL1 hxy hx3
    have hq : ((⟨y, hy⟩ : ↥L)⁻¹ * x : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq]
      exact hxy.symm
    have hqO : y⁻¹ * (x : G) ∈ pCoreOf 2 L := (AppC.mem_pCore_iff_mem_blockQ _).1 hq
    have hxN : (x : G) ∈ normalizer (fsuV1 T V : Set G) := by
      have e : (x : G) = y * (y⁻¹ * x) := by group
      rw [e]
      exact mul_mem (hNV1 y hyL1) (hCV1 (hOV hqO))
    have hx3' : (x : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    exact mem_oTwoRes_of_odd (m := 3) (mem_inf.2 ⟨x.2, hxN⟩) (by decide) hx3'
  have hc₀L1 : (c₀ : G) ∈ L₁ := hmemL1 c₀ c hcL hcL1 hc₀π (hcube' c₀ hc₀)
  have hd₀L1 : (d₀ : G) ∈ L₁ := hmemL1 d₀ d hdL hdL1 hd₀π (hcube' d₀ hd₀)
  have hbotG : IsElemAbelian 3 (⊥ : Subgroup G) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).1 hx, one_pow]⟩
  have hc₀1 : (c₀ : G) ∉ (⊥ : Subgroup G) := by
    intro h
    have h1 : c₀ = 1 := Subtype.ext ((mem_bot).1 h)
    rw [h1, map_one] at hc₀π
    exact hcb1 hc₀π.symm
  have hc₀3 : (c₀ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val (hcube' c₀ hc₀)
  have hd₀3 : (d₀ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val (hcube' d₀ hd₀)
  obtain ⟨hX₁, hX₁c⟩ := elemAbelian_sup_zpowers hbotG hc₀1 hc₀3
    (fun a ha => by rw [(mem_bot).1 ha, one_mul, mul_one])
  have hd₀A : (d₀ : G) ∉ (⊥ : Subgroup G) ⊔ zpowers (c₀ : G) := by
    rw [bot_sup_eq]
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    have h1 : d₀ = c₀ ^ k := Subtype.ext (by simpa using hk.symm)
    apply hdbA
    rw [bot_sup_eq, ← hd₀π, h1, map_zpow, hc₀π]
    exact zpow_mem_zpowers cb k
  have hcommG : (c₀ : G) * d₀ = d₀ * c₀ := congrArg Subtype.val hcomm'
  obtain ⟨hX, hXc⟩ := elemAbelian_sup_zpowers hX₁ hd₀A hd₀3 (by
    have hle : (⊥ : Subgroup G) ⊔ zpowers (c₀ : G) ≤ centralizer ({(d₀ : G)} : Set G) :=
      sup_le bot_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hcommG))
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha))
  refine ⟨(⊥ ⊔ zpowers (c₀ : G)) ⊔ zpowers (d₀ : G),
    sup_le (sup_le bot_le (zpowers_le.2 hc₀L1)) (zpowers_le.2 hd₀L1), hX, ?_⟩
  rw [hXc, hX₁c, card_bot]

theorem s134_single_block {H VH R : Subgroup G} {hV : IsElemAbelian 2 VH}
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hV)))} (B : BlocksR (hV := hV) H R 𝓗 𝓘)
    (h1 : 𝓘.card = 1) :
    ∃ K ∈ 𝓘, autI hV (conjClosure (thompsonJ R) H) = K ∧
      ∀ g ∈ autI hV H, B1.conjAut g K = K := by
  obtain ⟨K, hK⟩ := Finset.card_eq_one.1 h1
  have hK𝓘 : K ∈ 𝓘 := hK ▸ Finset.mem_singleton_self K
  refine ⟨K, hK𝓘, ?_, fun g hg => ?_⟩
  · rw [B.eq, hK]
    simp
  · have := B.conjAut_mem hg hK𝓘
    rw [hK, Finset.mem_singleton] at this
    exact this

theorem s134_exists_tau (S : A6.Setting134 G T L V) {Lp : Subgroup G} (P : S134Plus S Lp)
    {z : G} {H VH : Subgroup G} (hHz : InHz T L V z H) (hsolv : Group.IsSolvable ↥H)
    (hred : IsTwoReducedIn H VH) (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hcard : 𝓘.card ≤ 2)
    {K : Subgroup (MulAut (IntMod VH hred.2.2.1))} (hK : K ∈ 𝓘) :
    ∃ τ ∈ autI hred.2.2.1 (thompsonJ (r1Of T L V)), τ ∈ K ∧ τ ≠ 1 ∧ τ ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTsyl, -, -, -, -⟩ := s134_inHz_facts S hHz
  have hRH : r1Of T L V ≤ H := (r1Of_le_T T L V).trans hTsyl.1
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hVR : VH ≤ r1Of T L V :=
    (s134_VH_le_r1Of hred hcR).1.trans (s134_VH_le_r1Of hred hcR).2
  have hTR : T ≤ normalizer (r1Of T L V : Set G) := by
    rw [← P.pCoreOf_eq_r1Of]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨⟨τ, hτm⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (B.inf_ne_bot hred hsolv hVR hRH hJ hTsyl hTR hcard hK)
  have hτ1' : τ ≠ 1 := fun h => hτ1 (Subtype.ext h)
  obtain ⟨hτJ, hτK⟩ := mem_inf.1 hτm
  refine ⟨τ, hτJ, hτK, hτ1', ?_⟩
  obtain ⟨g, hgJ, rfl⟩ := (mem_autI hred.2.2.1).1 hτJ
  obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨g, (r1Of_le_T T L V) (hJR hgJ)⟩
  have hk' : (convI hred.2.2.1 g) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have h6 : (convI hred.2.2.1 g) ^ 6 = 1 := by
    have h1 : orderOf (⟨_, hτK⟩ : ↥K) ∣ 6 :=
      B.hb.card_eq K (B.sub hK) ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hg := pow_gcd_eq_one.2 ⟨h6, hk'⟩
  have hd : Nat.gcd 6 (2 ^ k) ∣ 2 := by
    rw [show (6 : ℕ) = 3 * 2 from rfl,
      Nat.Coprime.gcd_mul_left_cancel 2 (Nat.Coprime.pow_right k (by norm_num))]
    exact Nat.gcd_dvd_left 2 (2 ^ k)
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hg).trans hd)

theorem s134_false_of_hat_C (h1332 : Stmt13_3_2)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (S : A6.Setting134 G T L V)
    (hhat : IsHatA6 L) {z : G} {H VH : Subgroup G} (hHz : InHz T L V z H)
    (hsolv : Group.IsSolvable ↥H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    (hC : H ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty)
    (hcard : 𝓘.card ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have P := s134Plus_l1plus S hhat
  have h1 := s134_card_blocks_eq_one_of_C S P hHz hsolv hred hcR hJ hC B hne hcard
  obtain ⟨K, hK𝓘, hIK, hHK⟩ := s134_single_block B h1
  have hK : K ∈ 𝓗 := B.sub hK𝓘
  obtain ⟨hTsyl, hL1TH, -, hO2H, hHM⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hL1H : L₁Of L (fsuV1 T V) ≤ H := le_sup_left.trans hL1TH
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hVT : VH ≤ T := (le_pCoreOf_of_reduced hred).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  have hL1Z := s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S ⟨H, ⟨hTH, hO2H⟩, hHM⟩
  obtain ⟨X, hXL1, hX, hX9⟩ := s134_hat_E9 S hhat
  have hXH : X ≤ H := hXL1.trans hL1H
  have hXN : X ≤ normalizer (VH : Set G) := hXH.trans hHN
  have hXC : X ⊓ centralizer (VH : Set G) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hxO : x ∈ pCoreOf 2 H := hC ▸ mem_inf.2 ⟨hXH hx.1, hx.2⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hxO⟩
    exact cube_two_pow_eq_one (by simpa using congrArg Subtype.val hk) (hX.2 x hx.1)
  set B₉ := autI hred.2.2.1 X with hB₉
  have hB₉c : Nat.card ↥B₉ = 9 := by
    have h := card_autI_mul_card_inf hred.2.2.1 hXN
    rw [hXC, card_bot, mul_one, hX9] at h
    exact h
  have hB₉H : B₉ ≤ autI hred.2.2.1 H := autI_mono _ hXH
  have hB₉ab : IsElemAbelian 3 B₉ := by
    have hXc := hX.1
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun φ hφ => ?_⟩
    · obtain ⟨g, hgX, hg⟩ := (mem_autI hred.2.2.1).1 a.2
      obtain ⟨h, hhX, hh⟩ := (mem_autI hred.2.2.1).1 b.2
      have hgh : (g : G) * h = h * g :=
        congrArg Subtype.val (mul_comm (⟨g, hgX⟩ : ↥X) ⟨h, hhX⟩)
      have hgh' : g * h = h * g := Subtype.ext hgh
      simp only [Subgroup.coe_mul]
      rw [← hg, ← hh, ← map_mul, ← map_mul, hgh']
    · obtain ⟨g, hgX, rfl⟩ := (mem_autI hred.2.2.1).1 hφ
      have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hX.2 _ hgX)
      rw [← map_pow, hg3, map_one]
  have hB₉K : ∀ φ ∈ B₉, φ ∈ K → φ = 1 := by
    intro φ hφ hφK
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hred.2.2.1).1 hφ
    exact s134_eq_one_of_cent_Z hred.2.2.1 B.hb hK hHN hHK hTH S.h13.sylow.1 hVT g.2
      (hL1Z (hXL1 hgX)) hφK (hB₉ab.2 _ hφ)
  obtain ⟨y, hyK, hy3⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K hK)
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hyB : y ∉ B₉ := by
    intro h
    have := hB₉K y h hyK
    rw [this, orderOf_one] at hy3
    omega
  have hyc : ∀ φ ∈ B₉, φ * y = y * φ := fun φ hφ =>
    blocks_comm_of_pow_three B hcard (hB₉H hφ) (hB₉ab.2 φ hφ) hK𝓘 hyK hy3
  obtain ⟨hA, hAc⟩ := elemAbelian_sup_zpowers hB₉ab hyB hy3' hyc
  have hyH : y ∈ autI hred.2.2.1 H := by
    rw [← hIK] at hyK
    exact autI_mono _ (conjClosure_le fun h hh j hj => mul_mem (mul_mem hh
      ((((iSup₂_le fun _ hA => hA.1 : thompsonJ (r1Of T L V) ≤ r1Of T L V).trans
        (r1Of_le_T T L V)).trans hTH) hj)) (inv_mem hh)) hyK
  have hAH : B₉ ⊔ zpowers y ≤ autI hred.2.2.1 H := sup_le hB₉H (zpowers_le.2 hyH)
  have := s134_rank_autI_le S hHz hred hC hAH hA (r := 3) (by rw [hAc, hB₉c]; norm_num)
  omega

theorem s134_false_of_hat_sylow (h1332 : Stmt13_3_2)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (S : A6.Setting134 G T L V)
    (hhat : IsHatA6 L) {z : G} {H VH : Subgroup G} (hHz : InHz T L V z H)
    (hsolv : Group.IsSolvable ↥H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    (hL1eq : l1plus T L V = oTwoRes (H ⊓ centralizer (VH : Set G)))
    (hHL1 : H ≤ normalizer (l1plus T L V : Set G))
    (hR₁ : IsSylowTwoOf (r1Of T L V)
      (centralizerMod (pCoreOf 2 (l1plus T L V)) H (l1plus T L V)))
    {𝓗 𝓘 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))}
    (B : BlocksR (hV := hred.2.2.1) H (r1Of T L V) 𝓗 𝓘) (hne : 𝓘.Nonempty)
    (hcard : 𝓘.card ≤ 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have P := s134Plus_l1plus S hhat
  set Lp := l1plus T L V with hLp
  set H₁ := centralizerMod (pCoreOf 2 Lp) H Lp with hH₁
  have h1 := s134_card_blocks_eq_one_of_sylow S P hHz hsolv hred hcR hJ hL1eq hHL1 hR₁ B hne
    hcard
  obtain ⟨K, hK𝓘, hIK, hHK⟩ := s134_single_block B h1
  have hK : K ∈ 𝓗 := B.sub hK𝓘
  have hW : ∀ w : IntMod VH hred.2.2.1, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨hTsyl, hL1TH, -, hO2H, hHM⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hL1H : L₁Of L (fsuV1 T V) ≤ H := le_sup_left.trans hL1TH
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hVT : VH ≤ T := (le_pCoreOf_of_reduced hred).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  have hL1Z := s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S ⟨H, ⟨hTH, hO2H⟩, hHM⟩
  obtain ⟨ℓ, hℓLp, hℓ3, hℓO, hℓC, hℓcomm, hℓmod, -⟩ :=
    s134_bar_ctx S P hHz hred hcR hL1eq hHL1 hR₁
  have hLpH : Lp ≤ H := P.le_L1.trans hL1H
  have hℓH : ℓ ∈ H := hLpH hℓLp
  have hH₁H : H₁ ≤ H := fun x hx => hx.1
  have hOn : H ≤ normalizer (pCoreOf 2 Lp : Set G) :=
    hHL1.trans (normalizer_le_normalizer_pCoreOf 2 Lp)
  have hH₁n : H ≤ normalizer (H₁ : Set G) := le_normalizer_centralizerMod hOn le_normalizer hHL1
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hIH₁ : conjClosure (thompsonJ (r1Of T L V)) H ≤ H₁ := conjClosure_le fun h hh j hj =>
    (mem_normalizer_iff.mp (hH₁n hh) j).mp (hR₁.1 (hJR hj))
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := l0_decomp hhat
  have hcL1 : c ∈ L₁Of L (fsuV1 T V) := s134_l0_le_L1 S hcl0
  have hcH : c ∈ H := hL1H hcL1
  have hcZ : c ∈ o2Z L := oTwoRes_le _ hcl0
  have hL1Lp : L₁Of L (fsuV1 T V) ≤ normalizer (Lp : Set G) :=
    A5.le_normalizer_oTwoRes_of_le_normalizer (le_normalizer_commutator_left' _ _)
  have hLpO : Lp ⊓ pCoreOf 2 L ≤ pCoreOf 2 Lp := by
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
      inf_le_left ?_ ((pCoreOf_isPGroup 2 L).to_le inf_le_right)
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk => ?_
    exact mem_normalizer_inf (le_normalizer hk) (le_normalizer_pCoreOf 2 L (P.le_L hk))
  have hcH₁ : c ∈ H₁ := by
    refine ⟨hcH, normalizer_le_normalizer_pCoreOf 2 Lp (hL1Lp hcL1), fun u hu => ?_⟩
    have h1 : c * u * c⁻¹ * u⁻¹ ∈ Lp :=
      mul_mem ((mem_normalizer_iff.mp (hL1Lp hcL1) u).mp hu) (inv_mem hu)
    exact hLpO ⟨h1, (mem_o2Z_iff.1 hcZ).2 u (P.le_L hu)⟩
  have hcube : ∀ {x : G} {k : ℕ}, x ^ 2 ^ k = 1 → x ^ 3 = 1 → x = 1 := fun h2 h3 =>
    cube_two_pow_eq_one h2 h3
  set cs := convI hred.2.2.1 ⟨c, hHN hcH⟩ with hcs
  have hcsH : cs ∈ autI hred.2.2.1 H := convI_mem_autI _ hcH (hHN hcH)
  have hcs3 : cs ^ 3 = 1 := by
    rw [hcs, ← map_pow]
    have : (⟨c, hHN hcH⟩ : ↥(normalizer (VH : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hcsK : cs ∉ K := by
    intro h
    have h1 := s134_eq_one_of_cent_Z hred.2.2.1 B.hb hK hHN hHK hTH S.h13.sylow.1 hVT
      (hHN hcH) (hL1Z hcL1) h hcs3
    have hcC : c ∈ centralizer (VH : Set G) := (convI_eq_one_iff _ _).1 h1
    have hcLp : c ∈ Lp := hL1eq.ge (mem_oTwoRes_of_odd (m := 3) (mem_inf.2 ⟨hcH, hcC⟩)
      (by decide) hc3)
    have hcO2 : c ∈ pCoreOf 2 L := s134_hatL1Plus S hhat ⟨hcLp, hcZ⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨c, hcO2⟩
    have hc1 := hcube (by simpa using congrArg Subtype.val hk) hc3
    exact hcO (hc1 ▸ one_mem _)
  obtain ⟨y, hyK, hy3⟩ := exists_orderOf_three_of_card_six (B.hb.card_eq K hK)
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hcy : cs * y = y * cs := blocks_comm_of_pow_three B hcard hcsH hcs3 hK𝓘 hyK hy3
  have hcK : ∀ k ∈ K, cs * k * cs⁻¹ ∈ K := fun k hk => by
    rw [← hHK _ hcsH]
    exact B1.mem_conjAut.2 (by simpa [mul_assoc] using hk)
  obtain ⟨τ, hτJ, hτK, hτ1, hτ2⟩ := s134_exists_tau S P hHz hsolv hred hcR hJ B hcard hK𝓘
  obtain ⟨j, hj⟩ := blk_exists_adjust hW B.hb hK hcK hyK hy3 hcy hτK hτ2 hτ1
  set cp := (y ^ j)⁻¹ * cs with hcp
  have hcpK : cp ∉ K := fun h => hcsK (by
    have : cs = y ^ j * cp := by rw [hcp]; group
    rw [this]
    exact mul_mem (pow_mem hyK j) h)
  have hcpy : cp * y = y * cp := by
    have hc : Commute cs y := hcy
    have hc' : Commute (y ^ j)⁻¹ y := ((Commute.refl y).pow_left j).inv_left
    exact (hc'.mul_left hc).eq
  have hyI := hyK
  rw [← hIK] at hyI
  obtain ⟨⟨i, hiN⟩, hiI, hiy⟩ := (mem_autI hred.2.2.1).1 hyI
  obtain ⟨⟨t, htN⟩, htJ, htτ⟩ := (mem_autI hred.2.2.1).1 hτJ
  have hiH₁ : i ∈ H₁ := hIH₁ hiI
  have htH₁ : t ∈ H₁ := hR₁.1 (hJR htJ)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hker : CFSG.pCore 2 ↥H ≤ (convHom hred.2.2.1 H hHN).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff]
    exact pCoreOf_le_centralizer_of_reduced' hred ((AppC.mem_pCore_iff_mem_blockQ x).1 hx)
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥H) (convHom hred.2.2.1 H hHN) hker with hψ
  have hψπ : ∀ x : ↥H, ψ (π x) = convI hred.2.2.1 ⟨x, hHN x.2⟩ := fun _ => rfl
  have hπ1 : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, AppC.mem_pCore_iff_mem_blockQ]
    exact Iff.rfl
  set w := π ⟨ℓ, hℓH⟩ with hw
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow]
    exact (hπ1 _).2 (by simp [hℓ3])
  have hw1 : w ≠ 1 := fun h => hℓO ((hπ1 _).1 h)
  have hψw : ψ w = 1 := by
    rw [hw, hψπ, convI_eq_one_iff]
    exact hℓC
  have hcommw : ∀ x : ↥H, (x : G) ∈ H₁ → Commute (π x) w := by
    intro x hx
    have h1 : π (x * ⟨ℓ, hℓH⟩ * x⁻¹ * (⟨ℓ, hℓH⟩)⁻¹) = 1 := (hπ1 _).2 (hℓcomm x hx)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    show π x * w = w * π x
    calc π x * w = (π x * w * (π x)⁻¹ * w⁻¹) * (w * π x) := by group
      _ = w * π x := by rw [hw, h1, one_mul]
  have hQ1 : ∀ x : ↥H, (x : G) ∈ H₁ → ψ (π x) = 1 → ∃ k : ℕ, π x = w ^ k := by
    intro x hx h
    have hxC : (x : G) ∈ centralizer (VH : Set G) := by
      rw [hψπ, convI_eq_one_iff] at h
      exact h
    obtain ⟨k, hk⟩ := hℓmod x hx hxC
    refine ⟨k, ?_⟩
    have h1 : π (x * (⟨ℓ, hℓH⟩ ^ k)⁻¹) = 1 := (hπ1 _).2 (by simpa using hk)
    rw [map_mul, map_inv, map_pow, ← hw] at h1
    calc π x = (π x * (w ^ k)⁻¹) * w ^ k := by group
      _ = w ^ k := by rw [h1, one_mul]
  have hiH : i ∈ H := hH₁H hiH₁
  have htH : t ∈ H := hH₁H htH₁
  set ii : ↥H := ⟨i, hiH⟩ with hii
  set tt : ↥H := ⟨t, htH⟩ with htt
  set cc : ↥H := (ii ^ j)⁻¹ * ⟨c, hcH⟩ with hcc
  have hccH₁ : (cc : G) ∈ H₁ := by
    rw [hcc]
    exact mul_mem (inv_mem (pow_mem hiH₁ j)) hcH₁
  have hψi : ψ (π ii) = y := by rw [hψπ, ← hiy]
  have hψt : ψ (π tt) = τ := by rw [hψπ, ← htτ]
  have hψc : ψ (π cc) = cp := by
    rw [hcc, map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, hψi, hψπ]
  have hmemH₁ : ∀ x : ↥H, (x : G) ∈ H₁ → ∀ x' : ↥H, (x' : G) ∈ H₁ → (x * x' : G) ∈ H₁ :=
    fun x hx x' hx' => mul_mem hx hx'
  have hinvτ := block_conj_eq_inv hW B.hb hK hyK hy3 hτK hτ2 hτ1
  have hτcp : τ * cp * τ⁻¹ = cp := by
    calc τ * cp * τ⁻¹ = cp * τ * τ⁻¹ := by rw [hj]
      _ = cp := by group
  have ha : ψ (π (tt * ii * tt⁻¹ * ii)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hψi, hψt,
      hinvτ, inv_mul_cancel]
  have hb : ψ (π (tt * cc * tt⁻¹ * cc⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv, hψt, hψc, hτcp, mul_inv_cancel]
  have he : ψ (π (ii * cc * ii⁻¹ * cc⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv, hψi, hψc]
    calc y * cp * y⁻¹ * cp⁻¹ = (y * cp) * y⁻¹ * cp⁻¹ := rfl
      _ = (cp * y) * y⁻¹ * cp⁻¹ := by rw [hcpy]
      _ = 1 := by group
  have hf : ψ (π (ii ^ 3)) = 1 := by rw [map_pow, map_pow, hψi, hy3']
  have hiH₁' : (ii : G) ∈ H₁ := hiH₁
  have htH₁' : (tt : G) ∈ H₁ := htH₁
  obtain ⟨a, haw⟩ := hQ1 _ (mul_mem (mul_mem (mul_mem htH₁' hiH₁') (inv_mem htH₁')) hiH₁') ha
  obtain ⟨b, hbw⟩ := hQ1 _ (mul_mem (mul_mem (mul_mem htH₁' hccH₁) (inv_mem htH₁'))
    (inv_mem hccH₁)) hb
  obtain ⟨e, hew⟩ := hQ1 _ (mul_mem (mul_mem (mul_mem hiH₁' hccH₁) (inv_mem hiH₁'))
    (inv_mem hccH₁)) he
  obtain ⟨f, hfw⟩ := hQ1 _ (pow_mem hiH₁' 3) hf
  rw [map_mul, map_mul, map_mul, map_inv] at haw
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hbw hew
  rw [map_pow] at hfw
  have htu : (π tt) * (π ii) * (π tt)⁻¹ = w ^ a * (π ii)⁻¹ := by
    rw [← haw]
    group
  have htv : (π tt) * (π cc) * (π tt)⁻¹ = w ^ b * (π cc) := by
    rw [← hbw]
    group
  have huv : ⁅(π ii), (π cc)⁆ = w ^ e := by rw [commutatorElement_def]; exact hew
  have hYw := hcommw ii hiH₁'
  have hCw := hcommw cc hccH₁
  have hUw := hcommw tt htH₁'
  have hYC : ⁅(π ii), (π cc)⁆ = 1 :=
    commutatorElement_eq_one_of_central hw3 hYw hCw hUw htu htv huv
  have hY3 : (π ii) ^ 3 = 1 := pow_three_eq_one_of_central hw3 hYw hUw htu hfw
  have hYCc : (π ii) * (π cc) = (π cc) * (π ii) := by
    rw [commutatorElement_def] at hYC
    calc (π ii) * (π cc) = ((π ii) * (π cc) * (π ii)⁻¹ * (π cc)⁻¹) * ((π cc) * (π ii)) := by
          group
      _ = (π cc) * (π ii) := by rw [hYC, one_mul]
  have hC3 : (π cc) ^ 3 = 1 := by
    have hc0 : π ⟨c, hcH⟩ ^ 3 = 1 := by
      rw [← map_pow]
      exact (hπ1 _).2 (by simp [hc3])
    have e1 : (π cc) = ((π ii) ^ j)⁻¹ * π ⟨c, hcH⟩ := by
      rw [hcc, map_mul, map_inv, map_pow]
    have hcomm : Commute ((π ii) ^ j)⁻¹ (π ⟨c, hcH⟩) := by
      have h1 : Commute (π ii) (π cc) := hYCc
      have h2 : π ⟨c, hcH⟩ = (π ii) ^ j * (π cc) := by rw [e1]; group
      rw [h2]
      exact ((Commute.refl (π ii)).pow_pow j j).inv_left.mul_right (h1.pow_left j).inv_left
    rw [e1, hcomm.mul_pow, hc0, mul_one, inv_pow, ← pow_mul, mul_comm, pow_mul, hY3, one_pow,
      inv_one]
  have hbot : IsElemAbelian 3 (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).1 hx, one_pow]⟩
  obtain ⟨hA₁, hA₁c⟩ := elemAbelian_sup_zpowers hbot (fun h => hw1 ((mem_bot).1 h)) hw3
    (fun a ha => by rw [(mem_bot).1 ha, one_mul, mul_one])
  have hA₁ψ : (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w ≤ ψ.ker :=
    sup_le bot_le (zpowers_le.2 (MonoidHom.mem_ker.2 hψw))
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy3
    omega
  have hYA : π ii ∉ (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w := fun h =>
    hy1 (hψi ▸ MonoidHom.mem_ker.1 (hA₁ψ h))
  obtain ⟨hA₂, hA₂c⟩ := elemAbelian_sup_zpowers hA₁ hYA hY3 (by
    have hle : (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w ≤
        centralizer ({π ii} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      sup_le bot_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hYw.eq.symm))
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha))
  have hA₂ψ : (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w ⊔ zpowers (π ii) ≤
      K.comap ψ := by
    refine sup_le (hA₁ψ.trans fun x hx => ?_) (zpowers_le.2 (mem_comap.2 (hψi ▸ hyK)))
    rw [mem_comap, MonoidHom.mem_ker.1 hx]
    exact one_mem _
  have hCA : π cc ∉ (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w ⊔ zpowers (π ii) :=
    fun h => hcpK (hψc ▸ mem_comap.1 (hA₂ψ h))
  obtain ⟨hA₃, hA₃c⟩ := elemAbelian_sup_zpowers hA₂ hCA hC3 (by
    have hle : (⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w ⊔ zpowers (π ii) ≤
        centralizer ({π cc} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      refine sup_le (sup_le bot_le (zpowers_le.2 ?_)) (zpowers_le.2 ?_)
      · exact mem_centralizer_singleton_iff.2 hCw.eq.symm
      · exact mem_centralizer_singleton_iff.2 hYCc
    exact fun a ha => mem_centralizer_singleton_iff.1 (hle ha))
  have hcard3 : Nat.card ↥((⊥ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ⊔ zpowers w ⊔ zpowers (π ii) ⊔
      zpowers (π cc)) = 3 ^ 3 := by
    rw [hA₃c, hA₂c, hA₁c, card_bot]
    norm_num
  have hrank : ∀ E : Subgroup G, E ≤ H → IsElemAbelian 3 E → ∀ r, Nat.card E = 3 ^ r →
      r ≤ 2 := fun E hE hEab r hr =>
    Vol2.Ch11.SecD.le_two_of_elemAbelian S.fsu.qtke.2.2 hO2H (pCoreOf_isPGroup 2 H)
      Nat.prime_three (by norm_num) (hE.trans (le_normalizer_pCoreOf 2 H)) hEab hr
  have := Vol2.Ch11.SecD.le_two_of_elemAbelian_quotient (G₁ := H) Nat.prime_three
    (by norm_num) hrank hA₃ hcard3
  omega

end CFSG.Quasithin.H13.U3
