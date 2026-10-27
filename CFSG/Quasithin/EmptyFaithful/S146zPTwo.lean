module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.Vol2.Ch1Eight
public import CFSG.Quasithin.EmptyFaithful.S146zPTwoFin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSL25
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin

namespace P1469Two

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev iD (T I K₁ K₂ : Subgroup G) : Subgroup G :=
  Subgroup.normalizer ((dOf1469 T I K₁ K₂ : Subgroup G) : Set G)

variable {T M H : Subgroup G} {u : G} {I K₁ K₂ : Subgroup G} {ρ : G}

omit [Finite G] in
theorem le_iD_of_blockProduct (h : IsBlockProduct I (T ⊓ I) 2 ![K₁, K₂]) : I ≤ iD T I K₁ K₂ := by
  obtain ⟨-, -, -, -, hgen, -, hinv⟩ := h
  have hsup : (⨆ i, (![K₁, K₂] : Fin 2 → Subgroup G) i) = K₁ ⊔ K₂ :=
    le_antisymm (iSup_le fun i => by fin_cases i <;> simp)
      (sup_le (le_iSup (![K₁, K₂] : Fin 2 → Subgroup G) 0)
        (le_iSup (![K₁, K₂] : Fin 2 → Subgroup G) 1))
  rw [hsup] at hgen
  have hconj : ∀ t ∈ T ⊓ I, ∀ i : Fin 2, B6.conjSub t (![K₁, K₂] i) ≤ K₁ ⊔ K₂ := by
    intro t ht i
    obtain ⟨j, hj⟩ := hinv t ht i
    rw [hj]
    fin_cases j <;> simp
  have hK : ∀ t ∈ T ⊓ I, B6.conjSub t (K₁ ⊔ K₂) ≤ K₁ ⊔ K₂ := by
    intro t ht
    rw [OrderIso.map_sup]
    exact sup_le (by simpa using hconj t ht 0) (by simpa using hconj t ht 1)
  have hKn : ∀ s ∈ T ⊓ I, ∀ k ∈ K₁ ⊔ K₂, s⁻¹ * k * s ∈ K₁ ⊔ K₂ := by
    intro s hs k hk
    exact hK s⁻¹ (inv_mem hs) (B6.mem_conjSub.mpr (by simpa [mul_assoc] using hk))
  have key : ∀ s ∈ T ⊓ I, ∀ x ∈ dOf1469 T I K₁ K₂, s * x * s⁻¹ ∈ dOf1469 T I K₁ K₂ := by
    intro s hs x hx
    refine ⟨(T ⊓ I).mul_mem ((T ⊓ I).mul_mem hs hx.1) ((T ⊓ I).inv_mem hs),
      Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have h' := Subgroup.mem_centralizer_iff.mp hx.2 _ (hKn s hs k hk)
    calc k * (s * x * s⁻¹) = s * ((s⁻¹ * k * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * k * s)) * s⁻¹ := by rw [h']
      _ = (s * x * s⁻¹) * k := by group
  refine hgen.le.trans (sup_le (fun s hs => ?_) (fun k hk => ?_))
  · refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => key s hs x hx, fun hx => ?_⟩
    simpa [mul_assoc] using key s⁻¹ ((T ⊓ I).inv_mem hs) _ hx
  · have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ((dOf1469 T I K₁ K₂ : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp inf_le_right
    exact Subgroup.centralizer_le_normalizer _ (hle hk)

theorem obs_a_iD (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (hD : dOf1469 T I K₁ K₂ ≠ ⊥) :
    IsIStar T M u (iD T I K₁ K₂) ∧ T ⊓ iD T I K₁ K₂ = T ⊓ I ∧
      IsSylowTwoOf (T ⊓ I) (iD T I K₁ K₂) :=
  c.obs_a _ inf_le_left hD (le_iD_of_blockProduct c.blocks)

omit [Finite G] in
theorem iSup_pair (K₁ K₂ : Subgroup G) :
    (⨆ i, (![K₁, K₂] : Fin 2 → Subgroup G) i) = K₁ ⊔ K₂ :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp)
    (sup_le (le_iSup (![K₁, K₂] : Fin 2 → Subgroup G) 0)
      (le_iSup (![K₁, K₂] : Fin 2 → Subgroup G) 1))

theorem isLocal_of_block {I S K : Subgroup G} (hK : IsBlock2 I K) (hA5 : IsAltType K 5)
    (hgen : K ⊔ S = I) (hS : IsSylowTwoOf S I) (hpc : pCoreOf 2 I ≠ ⊥) :
    quasithinIsLocal S K := by
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    hK.1.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl hA5)
  have hsub : IsSubnormal K (K ⊔ S) := by
    rw [hgen]
    exact C1GN.isSubnormal_of_isBlock2 hK
  have hsyl' : IsSylowTwoOf S (K ⊔ S) := by
    rw [hgen]
    exact hS
  refine ⟨hS.2.1, C1GN.mem_cComp_of_short hK.1 hq hsub, hsyl'.2.2, ?_⟩
  rw [hgen]
  exact hpc

theorem isLocal_blocks (c : Ctx1469A5 T M H u I K₁ K₂ ρ) :
    quasithinIsLocal (T ⊓ I) K₁ ∧ quasithinIsLocal (T ⊓ I) K₂ := by
  obtain ⟨-, -, hb, -, hgen, hres, -⟩ := c.blocks
  rw [iSup_pair] at hgen
  have hS : IsSylowTwoOf (T ⊓ I) I := c.ctx.minPar.isSylow
  have hpc : pCoreOf 2 I ≠ ⊥ := c.ctx.hI.1.1.1.2
  have hb₁ : IsBlock2 I K₁ := (hb 0).1
  have hb₂ : IsBlock2 I K₂ := (hb 1).1
  have hK₁I : K₁ ≤ I := hb₁.2.1
  have hK₂I : K₂ ≤ I := hb₂.2.1
  have hmem : ∀ {t : G} {A B : Subgroup G}, t ∈ T ⊓ I → B6.conjSub t A = B → B ≤ A ⊔ (T ⊓ I) := by
    intro t A B ht hAB x hx
    rw [← hAB, B6.mem_conjSub] at hx
    have hts : t ∈ A ⊔ (T ⊓ I) := (le_sup_right : T ⊓ I ≤ A ⊔ (T ⊓ I)) ht
    have hx' : t⁻¹ * x * t ∈ A ⊔ (T ⊓ I) := (le_sup_left : A ≤ A ⊔ (T ⊓ I)) hx
    have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ A ⊔ (T ⊓ I) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hts hx') (Subgroup.inv_mem _ hts)
    simpa [mul_assoc] using h1
  obtain ⟨t, ht, ht12⟩ := hres 0 1
  obtain ⟨t', ht', ht21⟩ := hres 1 0
  have h12 : K₂ ≤ K₁ ⊔ (T ⊓ I) := hmem ht (by simpa using ht12)
  have h21 : K₁ ≤ K₂ ⊔ (T ⊓ I) := hmem ht' (by simpa using ht21)
  have e₁ : K₁ ⊔ (T ⊓ I) = I := by
    refine le_antisymm (sup_le hK₁I inf_le_right) (hgen.le.trans ?_)
    exact sup_le le_sup_right (sup_le le_sup_left h12)
  have e₂ : K₂ ⊔ (T ⊓ I) = I := by
    refine le_antisymm (sup_le hK₂I inf_le_right) (hgen.le.trans ?_)
    exact sup_le le_sup_right (sup_le h21 le_sup_left)
  exact ⟨isLocal_of_block hb₁ c.a5.1 e₁ hS hpc, isLocal_of_block hb₂ c.a5.2 e₂ hS hpc⟩

theorem blocks_ne (c : Ctx1469A5 T M H u I K₁ K₂ ρ) : K₁ ≠ K₂ := by
  intro h
  have hb₁ : IsBlock2 I K₁ := (c.blocks.2.2.1 0).1
  have h12 : ⁅K₁, K₂⁆ = ⊥ := by simpa using c.blocks.2.2.2.1 0 1 (by decide)
  have hq : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
    hb₁.1.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl c.a5.1)
  have hperf : ⁅K₁, K₁⁆ = K₁ := C1GN.isShort2_perfect_of_perfect_quotient hb₁.1 hq.1.commutator_eq_top
  rw [← h, hperf] at h12
  exact C1GN.isShort2_ne_bot hb₁.1 h12

theorem not_le_normalizer_of_ge {X S B K : Subgroup G} (hQ : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h128 : Lemma128One)
    (hS : IsSylowTwoOf S X) (hpc : pCoreOf 2 X ≠ ⊥) (hB : quasithinIsLocal S B)
    (hKc : K ∈ cComp X) (hBK : B ≤ K) (hmove : ∃ t ∈ S, B6.conjSub t B ≠ B) :
    ¬ X ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨t, ht, hne⟩ := hmove
  intro hXN
  have hKl : quasithinIsLocal S K := isLocal_of_mem_cComp_of_sylow hS hpc hKc
  have hN := h128 G hQ hs hnab S B K hB hKl hBK ⟨ht, hXN (hS.1 ht)⟩
  exact hne (B6.conjSub_eq_self hN)

omit [Finite G] in
theorem coe_mem_pCoreOf_iff_mem_pCore' {H : Subgroup G} (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := CFSG.mem_openPCoreOf_iff x

theorem false_of_a38Types_of_inf_le (hR : A5.C25.RankOneLocalSolvable) {Kp B : Subgroup G}
    (hBK : B ≤ Kp) (hBs : IsShort2 B) (hB5 : IsAltType B 5)
    (hA : A38Types (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) (hW : blockU B ⊓ pCoreOf 2 Kp ≤ blockZ B) : False := by
  classical
  set N : Subgroup ↥Kp := CFSG.pCore 2 ↥Kp with hN
  set π : ↥Kp →* ↥Kp ⧸ N := QuotientGroup.mk' N with hπ
  have hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) :=
    hBs.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl hB5)
  have hBperf : ⁅B, B⁆ = B := C1GN.isShort2_perfect_of_perfect_quotient hBs hBq.1.commutator_eq_top
  have hBne : B ≠ ⊥ := C1GN.isShort2_ne_bot hBs
  have hUB : blockU B ≤ B := (C1.blockU_le_blockQ hBs).trans (C1.blockQ_le B)
  have hUK : blockU B ≤ Kp := hUB.trans hBK
  have hUel : IsElemAbelian 2 (blockU B) := AppC.isElemAbelian_blockU hBs
  let θ : ↥(blockU B) →* ↥Kp ⧸ N := π.comp (Subgroup.inclusion hUK)
  have hkerZ : θ.ker ≤ ((blockZ B).subgroupOf (blockU B)) := by
    intro u hu
    have huN : (Subgroup.inclusion hUK u : ↥Kp) ∈ N := by
      have h1 : θ u = 1 := hu
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mpr (hW ⟨u.2, (coe_mem_pCoreOf_iff_mem_pCore' _).mpr huN⟩)
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβc⟩ := hB5
  have hβcard : Nat.card β.ker * 16 = Nat.card ↥(blockU B) := by
    have h1 : Nat.card β.ker * Nat.card β.range = Nat.card ↥(blockU B) := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have h2 : Nat.card β.range = 16 := by
      rw [MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
      exact A5.G3.card_evenWeight_five
    rw [← h1, h2]
  have hθcard : Nat.card θ.ker * Nat.card θ.range = Nat.card ↥(blockU B) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker_le : Nat.card θ.ker ≤ Nat.card β.ker := by
    rw [hβk]
    exact Subgroup.card_le_of_le hkerZ
  have hPcard : 16 ≤ Nat.card θ.range := by
    by_contra hlt
    have h15 : Nat.card θ.range ≤ 15 := by omega
    have hβpos : 0 < Nat.card β.ker := Nat.card_pos
    have h1 : Nat.card θ.ker * Nat.card θ.range ≤ Nat.card β.ker * 15 :=
      Nat.mul_le_mul hker_le h15
    omega
  have hPel : IsElemAbelian 2 θ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, ⟨u₁, rfl⟩⟩ := a
      obtain ⟨_, ⟨u₂, rfl⟩⟩ := b
      refine Subtype.ext ?_
      show θ u₁ * θ u₂ = θ u₂ * θ u₁
      rw [← map_mul, ← map_mul, hUel.1.is_comm.comm u₁ u₂]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow]
      have : u ^ 2 = 1 := Subtype.ext (hUel.2 u u.2)
      rw [this, map_one]
  set Λ : Subgroup (↥Kp ⧸ N) := (B.subgroupOf Kp).map π with hΛ
  have key : ∀ b ∈ B.subgroupOf Kp, ∀ p ∈ θ.range, π b * p * (π b)⁻¹ ∈ θ.range := by
    intro b hb p hp
    obtain ⟨u, rfl⟩ := hp
    have hbB : (b : G) ∈ B := hb
    have hbu : (b : G) * (u : G) * (b : G)⁻¹ ∈ blockU B :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hbB) (u : G)).mp u.2
    refine ⟨⟨(b : G) * (u : G) * (b : G)⁻¹, hbu⟩, ?_⟩
    show π (Subgroup.inclusion hUK ⟨(b : G) * (u : G) * (b : G)⁻¹, hbu⟩) =
      π b * π (Subgroup.inclusion hUK u) * (π b)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext rfl)
  have hnorm : Λ ≤ Subgroup.normalizer (θ.range : Set (↥Kp ⧸ N)) := by
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr fun p => ⟨fun hp => key b hb p hp, fun hp => ?_⟩
    have := key b⁻¹ ((B.subgroupOf Kp).inv_mem hb) _ hp
    simpa [mul_assoc] using this
  have hΛsolv : Group.IsSolvable ↥Λ := hR _ hA θ.range Λ hPel hPcard hnorm
  let ψ : ↥B →* ↥Kp ⧸ N := π.comp (Subgroup.inclusion hBK)
  have hψΛ : ψ.range ≤ Λ := by
    rintro _ ⟨b, rfl⟩
    exact ⟨Subgroup.inclusion hBK b, b.2, rfl⟩
  have : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hψΛ)
  have hkerP : IsPGroup 2 ↥ψ.ker := by
    intro b
    have hbN : (Subgroup.inclusion hBK (b : ↥B) : ↥Kp) ∈ N :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp b.2)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Kp)) ⟨_, hbN⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    have h2 : (Subgroup.inclusion hBK (b : ↥B) : ↥Kp) ^ 2 ^ k = 1 := h1
    have h3 : (b : ↥B) ^ 2 ^ k = 1 :=
      Subgroup.inclusion_injective hBK (by rw [map_pow, map_one]; exact h2)
    rw [Subgroup.coe_pow]
    exact h3
  have : Group.IsNilpotent ↥ψ.ker := hkerP.isNilpotent
  have : Group.IsSolvable ↥ψ.ker := inferInstance
  have hBsolv : Group.IsSolvable ↥B :=
    Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hBperf
  exact Group.IsPerfect.not_isSolvable ↥B inferInstance

theorem generalizedFitting_le_closure_odd {Q : Type*} [Group Q] [Finite Q] (h2 : CFSG.pCore 2 Q = ⊥) :
    CFSG.generalizedFitting Q ≤
      Subgroup.closure {x | x ∈ CFSG.generalizedFitting Q ∧ Odd (orderOf x)} := by
  refine sup_le ?_ ?_
  · rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    by_cases hq : q.1.1 = 2
    · rw [hq, h2]
      exact bot_le
    · have hqp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have : Fact q.1.1.Prime := ⟨hqp⟩
      intro x hx
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (le_sup_left : CFSG.fittingSubgroup Q ≤ CFSG.fittingSubgroup Q ⊔ CFSG.layer Q)
          (CFSG.pCore_le_fitting Q q.1.1 hx)
      · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := q.1.1) (G := Q)) ⟨x, hx⟩
        have hk' : x ^ q.1.1 ^ k = 1 := congrArg Subtype.val hk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hqp).mp (orderOf_dvd_of_pow_eq_one hk')
        rw [hj]
        exact (hqp.odd_of_ne_two hq).pow
  · refine sSup_le fun C hC => ?_
    have hper : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hC.1.1
    have hCle : C ≤ CFSG.generalizedFitting Q :=
      (le_sSup hC : C ≤ CFSG.layer Q).trans
        (le_sup_right : CFSG.layer Q ≤ CFSG.fittingSubgroup Q ⊔ CFSG.layer Q)
    refine (eq_oTwoUpper_of_perfect hper).le.trans ?_
    exact Subgroup.closure_mono fun x hx => ⟨hCle hx.1, hx.2⟩

theorem exists_odd_orderOf_pow_two_pow' {K : Type*} [Group K] [Finite K] (y : K) :
    ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem pCore_two_quotient_eq_bot' {H : Type*} [Group H] :
    CFSG.pCore 2 (H ⧸ CFSG.pCore 2 H) = ⊥ := by
  set N : Subgroup H := CFSG.pCore 2 H with hN
  set M : Subgroup H := (CFSG.pCore 2 (H ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := H ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := H) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hMn : M.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
  have hMN : M ≤ N := le_sSup ⟨hMn, hMp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N y
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hMN hy

theorem oTwoFstarIn_le_oTwoUpper_sup (H : Subgroup G) :
    oTwoFstarIn H ≤ oTwoUpper (oTwoFstarIn H) ⊔ pCoreOf 2 H := by
  classical
  set N : Subgroup ↥H := CFSG.pCore 2 ↥H with hN
  have hNn : N.Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ N := QuotientGroup.mk' N with hπ
  set F := CFSG.generalizedFitting (↥H ⧸ N) with hF
  have hA : F ≤ Subgroup.closure {x | x ∈ F ∧ Odd (orderOf x)} :=
    generalizedFitting_le_closure_odd pCore_two_quotient_eq_bot'
  set Y := oTwoUpper (oTwoFstarIn H) with hY
  set T : Subgroup ↥H := Y.subgroupOf H ⊔ N with hT
  have hodd : ∀ y ∈ F, Odd (orderOf y) → y ∈ T.map π := by
    intro y hyF hyo
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk'_surjective N y
    obtain ⟨e, he⟩ := exists_odd_orderOf_pow_two_pow' k₀
    have hk₁F : π (k₀ ^ 2 ^ e) ∈ F := by
      rw [map_pow]
      exact F.pow_mem hyF _
    have hk₁Y : ((k₀ ^ 2 ^ e : ↥H) : G) ∈ oTwoFstarIn H :=
      Subgroup.mem_map.mpr ⟨k₀ ^ 2 ^ e, hk₁F, rfl⟩
    have hk₁o : Odd (orderOf ((k₀ ^ 2 ^ e : ↥H) : G)) := by
      rw [Subgroup.orderOf_coe]
      exact he
    have hk₁T : k₀ ^ 2 ^ e ∈ T :=
      (le_sup_left : Y.subgroupOf H ≤ T)
        (Subgroup.mem_subgroupOf.mpr (mem_oTwoUpper_of_odd hk₁Y hk₁o))
    have hcop : Nat.Coprime (2 ^ e) (orderOf (π k₀)) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hyo)
    have hyz : π k₀ ∈ Subgroup.zpowers (π k₀ ^ 2 ^ e) := A4.mem_zpowers_pow_of_coprime hcop
    refine (Subgroup.zpowers_le.mpr ?_) hyz
    exact Subgroup.mem_map.mpr ⟨k₀ ^ 2 ^ e, hk₁T, by simp [map_pow]⟩
  have hW : Subgroup.closure {x | x ∈ F ∧ Odd (orderOf x)} ≤ T.map π :=
    (Subgroup.closure_le _).mpr fun y hy => hodd y hy.1 hy.2
  intro x hx
  have hx' : x ∈ (F.comap π).map H.subtype := hx
  obtain ⟨k, hkF, rfl⟩ := hx'
  have hk : π k ∈ T.map π := hW (hA hkF)
  obtain ⟨t, htT, htk⟩ := hk
  have hkt : t⁻¹ * k ∈ N := QuotientGroup.eq.mp htk
  have hkT : k ∈ T := by
    have e : k = t * (t⁻¹ * k) := by group
    rw [e]
    exact T.mul_mem htT ((le_sup_right : N ≤ T) hkt)
  have h1 : (k : G) ∈ T.map H.subtype := Subgroup.mem_map_of_mem _ hkT
  have hYH : Y ≤ H := (oTwoUpper_le _).trans (oTwoFstarIn_le H)
  have hNe : N.map H.subtype = pCoreOf 2 H := by
    rw [hN]
    rfl
  rwa [hT, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYH, hNe] at h1

theorem oTwoFstarIn_mcOf_le_iD (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (f : Facts1469A5 T M u I K₁ K₂) : oTwoFstarIn (mcOf T) ≤ iD T I K₁ K₂ := by
  refine (oTwoFstarIn_le_oTwoUpper_sup (mcOf T)).trans (sup_le ?_ ?_)
  · have hDz : dOf1469 T I K₁ K₂ ≤ omegaOneCenterOf (pCoreOf 2 (I ⊓ mcOf T)) := by
      rw [f.g3]
      exact le_sup_left
    intro y hy
    have hyC := f.f hy
    have hyD : y ∈ Subgroup.centralizer ((dOf1469 T I K₁ K₂ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hDz.trans le_sup_right)) hyC
    exact Subgroup.centralizer_le_normalizer _ hyD
  · exact f.c.trans ((pCoreOf_le 2 _).trans (inf_le_left.trans (le_iD_of_blockProduct c.blocks)))

theorem pCoreOf_iD_inf_mcOf (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (f : Facts1469A5 T M u I K₁ K₂) :
    pCoreOf 2 (iD T I K₁ K₂ ⊓ mcOf T) = pCoreOf 2 (mcOf T) := by
  have hX : oTwoFstarIn (mcOf T) ≤ mcOf T ⊓ iD T I K₁ K₂ :=
    le_inf (oTwoFstarIn_le _) (oTwoFstarIn_mcOf_le_iD c f)
  have h := a4_4_1 (pCoreOf_le_oTwoFstarIn (mcOf T)) hX (a44Hyp_oTwoFstarIn (mcOf T))
  rwa [inf_comm] at h

theorem pCoreOf_iD_le (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (f : Facts1469A5 T M u I K₁ K₂)
    (hD : dOf1469 T I K₁ K₂ ≠ ⊥) : pCoreOf 2 (iD T I K₁ K₂) ≤ pCoreOf 2 (mcOf T) := by
  obtain ⟨-, -, hsyl⟩ := obs_a_iD c hD
  have hIID : I ≤ iD T I K₁ K₂ := le_iD_of_blockProduct c.blocks
  have hTG : T ⊓ I ≤ mcOf T := inf_le_left.trans (le_centralizer_quasithinOmegaOneCenter T)
  have hTz : T ⊓ I ≤ iD T I K₁ K₂ ⊓ mcOf T := le_inf (inf_le_right.trans hIID) hTG
  have h := pCoreOf_le_pCoreOf_of_sylow (p := 2) (inf_le_left : iD T I K₁ K₂ ⊓ mcOf T ≤ iD T I K₁ K₂)
    hsyl.2.1 hTz hsyl.2.2
  rwa [pCoreOf_iD_inf_mcOf c f] at h

theorem pCoreOf_le_pCoreOf_iD (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (f : Facts1469A5 T M u I K₁ K₂)
    (hK : pCoreOf 2 (K₁ ⊔ K₂) ≤ pCoreOf 2 (iD T I K₁ K₂)) :
    pCoreOf 2 I ≤ pCoreOf 2 (iD T I K₁ K₂) := by
  have S : Setting146 G T M := c.ctx.setting
  have hIID : I ≤ iD T I K₁ K₂ := le_iD_of_blockProduct c.blocks
  have hDT : dOf1469 T I K₁ K₂ ≤ T := inf_le_left.trans inf_le_left
  have hDI : dOf1469 T I K₁ K₂ ≤ I := inf_le_left.trans inf_le_right
  have hD2 : IsPGroup 2 (dOf1469 T I K₁ K₂) := S.hyp.sylow.1.to_le hDT
  have hDle : dOf1469 T I K₁ K₂ ≤ pCoreOf 2 (iD T I K₁ K₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hDI.trans hIID) le_rfl hD2
  rw [f.g2]
  exact sup_le hDle hK

theorem false_of_pCoreOf_le (hJ : Input1469A5J) (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (f : Facts1469A5 T M u I K₁ K₂) (hle : pCoreOf 2 I ≤ pCoreOf 2 (mcOf T)) : False := by
  have S : Setting146 G T M := c.ctx.setting
  have hO : pCoreOf 2 I ≠ ⊥ := c.ctx.hI.1.1.1.2
  have hJeq : thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) = thompsonJ (pCoreOf 2 I) :=
    hJ G I (T ⊓ I) (I ⊓ mcOf T) K₁ K₂ (S.isSQTKTC_of_pCoreOf_ne_bot hO) c.charTwo c.ctx.minPar
      c.blocks c.a5.1 c.a5.2 c.not_le
  have hJQ : thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) ≤ pCoreOf 2 (mcOf T) := by
    rw [hJeq]
    exact (B6.thompsonJ_le _).trans hle
  have hJQ' : thompsonJ (pCoreOf 2 (mcOf T)) = thompsonJ (pCoreOf 2 (I ⊓ mcOf T)) :=
    B6.thompsonJ_eq_of_le hJQ f.c
  have hIJ : I ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 (mcOf T)) : Set G) := by
    rw [hJQ', hJeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I).trans
      (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hmax : quasithinIsMaxTwoLocal (mcOf T) := (S.isUniqueM_mcOf S.isHTM_mcOf).1.1
  have hQ1 : pCoreOf 2 (mcOf T) ≠ ⊥ := S.isHTM_mcOf.1.2
  have hne : thompsonJ (pCoreOf 2 (mcOf T)) ≠ ⊥ :=
    S1414.thompsonJ_ne_bot (pCoreOf_isPGroup 2 _) hQ1
  have hN := normalizer_eq_of_char_pCoreOf hmax hne (B6.thompsonJ_le _)
    (S1414.characteristic_thompsonJ _)
  rw [hN] at hIJ
  exact c.ctx.hI.1.1.2.1 hIJ

theorem blockU_le_pCoreOf_of_a38Types (hR : A5.C25.RankOneLocalSolvable) {Kp B : Subgroup G}
    (hBK : B ≤ Kp) (hBs : IsShort2 B) (hB5 : IsAltType B 5)
    (hA : A38Types (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) : blockU B ≤ pCoreOf 2 Kp := by
  classical
  have hUB : blockU B ≤ B := (C1.blockU_le_blockQ hBs).trans (C1.blockQ_le B)
  have hUel : IsElemAbelian 2 (blockU B) := AppC.isElemAbelian_blockU hBs
  have hcomm : ∀ x ∈ blockU B, ∀ y ∈ blockU B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set W := blockU B ⊓ pCoreOf 2 Kp with hW
  have hWn : ∀ b ∈ B, b ∈ Subgroup.normalizer (W : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    have h1 := Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hb) x
    have h2 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Kp (hBK hb)) x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hZn : ∀ b ∈ B, b ∈ Subgroup.normalizer (blockZ B : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    have h1 := Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU B hb) x
    have hc : ∀ y ∈ blockZ B, b * y = y * b := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hy.2 b hb
    constructor
    · intro hx
      have : b * x * b⁻¹ = x := by rw [hc x hx]; group
      rw [this]
      exact hx
    · intro hx
      have h3 := hc _ hx
      have : b * x * b⁻¹ = x := by
        have h4 : b * (b * x * b⁻¹) = (b * x * b⁻¹) * b := h3
        calc b * x * b⁻¹ = b⁻¹ * (b * (b * x * b⁻¹)) := by group
          _ = b⁻¹ * ((b * x * b⁻¹) * b) := by rw [h4]
          _ = x := by group
      rw [← this]
      exact hx
  by_cases hWZ : W ≤ blockZ B
  · exact (false_of_a38Types_of_inf_le hR hBK hBs hB5 hA hWZ).elim
  · have hirr := hBs.2.2.2.2.2
    have hsup : blockZ B ⊔ W = blockU B := by
      refine (hirr (blockZ B ⊔ W) le_sup_left (sup_le inf_le_left inf_le_left) ?_).resolve_left ?_
      · intro b hb
        have e1 := A38.map_conj_eq_iff.mpr (hZn b hb)
        have e2 := A38.map_conj_eq_iff.mpr (hWn b hb)
        refine A38.map_conj_eq_iff.mp ?_
        rw [Subgroup.map_sup, e1, e2]
      · intro h
        exact hWZ (h ▸ (le_sup_right : W ≤ blockZ B ⊔ W))
    have hZW : blockZ B ≤ Subgroup.normalizer (W : Set G) := fun z hz =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (hcomm w hw.1 z hz.1))
    have hcomm_le : ⁅blockU B, B⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro u hu b hb
      rw [← hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZW] at hu
      obtain ⟨z, hz, w, hw, rfl⟩ := hu
      have hzb : b * z = z * b := Subgroup.mem_centralizer_iff.mp hz.2 b hb
      have hwb : b * w⁻¹ * b⁻¹ ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (hWn b hb) w⁻¹).mp (W.inv_mem hw)
        exact this
      have hcw : ⁅w, b⁆ ∈ W := by
        rw [commutatorElement_def]
        simpa [mul_assoc] using W.mul_mem hw hwb
      have hbz' : b * z⁻¹ * b⁻¹ = z⁻¹ := by
        have h1 : b * z⁻¹ = z⁻¹ * b := (Commute.inv_right (show Commute b z from hzb)).eq
        rw [h1]
        group
      have hzc : z * ⁅w, b⁆ = ⁅w, b⁆ * z := hcomm z hz.1 _ hcw.1
      have e : ⁅z * w, b⁆ = ⁅w, b⁆ := by
        calc ⁅z * w, b⁆ = z * ⁅w, b⁆ * (b * z⁻¹ * b⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅w, b⁆ := by
              rw [hbz']
              calc z * ⁅w, b⁆ * z⁻¹ = (⁅w, b⁆ * z) * z⁻¹ := by rw [hzc]
                _ = ⁅w, b⁆ := by group
      rw [e]
      exact hcw
    rw [← C1.commutator_blockU hBs]
    exact hcomm_le.trans inf_le_right

theorem noSL25_of_noOrderFour {X : Type} [Group X] [Finite X] (h4 : ∀ g : X, g ^ 4 = 1 → g ^ 2 = 1)
    {B : Type} [Group B] [Finite B] (hper : Group.IsPerfect B) (ψ : B →* X)
    (α : B →* alternatingGroup (Fin 5)) (hα : Function.Surjective α) (hψα : ψ.ker ≤ α.ker)
    (hα2 : IsPGroup 2 ↥α.ker) (hcent : ∀ q ∈ α.ker, ∀ g : B, ψ q * ψ g = ψ g * ψ q) :
    ∀ q ∈ α.ker, ψ q = 1 := by
  classical
  have : Group.IsPerfect B := hper
  have h2pow : ∀ k : ℕ, ∀ y : X, y ^ 2 ^ (k + 1) = 1 → y ^ 2 = 1 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      apply h4
      have hz : (y ^ 2) ^ 2 ^ (k + 1) = 1 := by
        rw [← pow_mul, ← pow_succ']
        exact hy
      have := ih (y ^ 2) hz
      rw [← pow_mul] at this
      simpa using this
  let ψ' : B →* ↥ψ.range := ψ.rangeRestrict
  have hψ' : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hker' : ψ'.ker ≤ α.ker := by
    intro b hb
    apply hψα
    rw [MonoidHom.mem_ker] at hb ⊢
    simpa [ψ'] using congrArg Subtype.val hb
  let α' : ↥ψ.range →* alternatingGroup (Fin 5) :=
    (MonoidHom.liftOfRightInverse ψ' (Function.surjInv hψ') (Function.rightInverse_surjInv hψ'))
      ⟨α, hker'⟩
  have hα' : ∀ b, α' (ψ' b) = α b := fun b =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨α, hker'⟩ b
  have hα'surj : Function.Surjective α' := by
    intro a
    obtain ⟨b, rfl⟩ := hα a
    exact ⟨ψ' b, hα' b⟩
  have hLΛ : ∀ (N : Subgroup ↥ψ.range) [N.Normal], IsPGroup 2 (↥ψ.range ⧸ N) → N = ⊤ := by
    intro N _ hN
    have : Group.IsPerfect ↥ψ.range := Group.IsPerfect.ofSurjective hψ'
    have : Group.IsNilpotent (↥ψ.range ⧸ N) := hN.isNilpotent
    have : Group.IsSolvable (↥ψ.range ⧸ N) := inferInstance
    have hsub : Subsingleton (↥ψ.range ⧸ N) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (↥ψ.range ⧸ N) inferInstance
    rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
    exact Nat.card_of_subsingleton (1 : ↥ψ.range ⧸ N)
  have hQ2 : ∀ q ∈ α'.ker, q * q = 1 := by
    intro q hq
    obtain ⟨b, rfl⟩ := hψ' q
    have hb : b ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      have := MonoidHom.mem_ker.mp hq
      rwa [hα'] at this
    obtain ⟨k, hk⟩ := hα2 ⟨b, hb⟩
    have hbk : b ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hyk : ψ b ^ 2 ^ k = 1 := by rw [← map_pow, hbk, map_one]
    have hy2 : ψ b ^ 2 = 1 := by
      rcases k with _ | k
      · have : ψ b = 1 := by simpa using hyk
        rw [this]; simp
      · exact h2pow k _ hyk
    refine Subtype.ext ?_
    simpa [ψ', pow_two] using hy2
  have hcomm : ∀ q ∈ α'.ker, ∀ g : ↥ψ.range, q * g * q⁻¹ * g⁻¹ ∈ (⊥ : Subgroup ↥ψ.range) := by
    intro q hq g
    obtain ⟨b, rfl⟩ := hψ' q
    obtain ⟨b', rfl⟩ := hψ' g
    have hb : b ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      have := MonoidHom.mem_ker.mp hq
      rwa [hα'] at this
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    have := hcent b hb b'
    simp only [ψ', MonoidHom.coe_rangeRestrict, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_one]
    calc ψ b * ψ b' * (ψ b)⁻¹ * (ψ b')⁻¹ = ψ b' * ψ b * (ψ b)⁻¹ * (ψ b')⁻¹ := by rw [this]
      _ = 1 := by group
  obtain ⟨x, hx⟩ := hα'surj ⟨AppC.zA, Equiv.Perm.mem_alternatingGroup.2 AppC.zA_sign⟩
  have hxx : x * x = 1 := by
    have hx2 : x * x ∈ α'.ker := by
      rw [MonoidHom.mem_ker, map_mul, hx]
      refine Subtype.ext ?_
      show AppC.zA * AppC.zA = 1
      decide +kernel
    have h4x : x * x * (x * x) = 1 := hQ2 _ hx2
    have : ((x : X)) ^ 4 = 1 := by
      have := congrArg Subtype.val h4x
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at this
      calc (x : X) ^ 4 = (x : X) * x * ((x : X) * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    have h2 := h4 _ this
    refine Subtype.ext ?_
    simpa [pow_two] using h2
  have key := AppC.central_cover_trivial (Λ := ↥ψ.range) hLΛ α' hα'surj ⊥ bot_le hQ2 hcomm x hxx
    (by rw [hx])
  intro q hq
  have h1 : ψ' q ∈ α'.ker := by
    rw [MonoidHom.mem_ker, hα']
    exact hq
  have h2 := key h1
  rw [Subgroup.mem_bot] at h2
  simpa [ψ'] using congrArg Subtype.val h2

theorem noSL25_J1
    {X : Type} [Group X] [Finite X] (hJ : IsSporadic .J1 X) {B : Type} [Group B]
    [Finite B] (hper : Group.IsPerfect B) (_hns : ¬ Group.IsSolvable B) (ψ : B →* X)
    (α : B →* alternatingGroup (Fin 5)) (hα : Function.Surjective α) (hψα : ψ.ker ≤ α.ker)
    (hα2 : IsPGroup 2 ↥α.ker) (hcent : ∀ q ∈ α.ker, ∀ g : B, ψ q * ψ g = ψ g * ψ q) :
    ∀ q ∈ α.ker, ψ q = 1 :=
  noSL25_of_noOrderFour (noOrderFour_J1 hJ) hper ψ α hα hψα hα2 hcent

theorem noSL25_of_bender
    {X : Type} [Group X] [Finite X] (hX : fusionIsBenderGroup X) {B : Type}
    [Group B] [Finite B] (_hper : Group.IsPerfect B) (hns : ¬ Group.IsSolvable B) (ψ : B →* X)
    (α : B →* alternatingGroup (Fin 5)) (_hα : Function.Surjective α) (hψα : ψ.ker ≤ α.ker)
    (hα2 : IsPGroup 2 ↥α.ker) (hcent : ∀ q ∈ α.ker, ∀ g : B, ψ q * ψ g = ψ g * ψ q) :
    ∀ q ∈ α.ker, ψ q = 1 := by
  classical
  intro q hq
  by_contra hq1
  obtain ⟨b, hbo, hbc⟩ := exists_central_involution ψ hα2 hcent hq hq1
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers (ψ b)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo]; simp)
  have hP1 : Subgroup.zpowers (ψ b) ≠ ⊥ := by
    intro h
    have : ψ b = 1 := by
      have := Subgroup.mem_zpowers (ψ b)
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [this, orderOf_one] at hbo
    omega
  have hΛ : ψ.range ≤ Subgroup.normalizer ((Subgroup.zpowers (ψ b) : Subgroup X) : Set X) := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute (ψ b) (ψ g) from hbc g) i)).eq
  exact not_isSolvable_range hns ψ (hα2.to_le hψα) (A5.C25.solvable_of_bender hX hP2 hP1 hΛ)

theorem noSL25_a38Types
    {X : Type} [Group X] [Finite X] (hA : A38Types X) {B : Type} [Group B]
    [Finite B] (hper : Group.IsPerfect B) (hns : ¬ Group.IsSolvable B) (ψ : B →* X)
    (α : B →* alternatingGroup (Fin 5)) (hα : Function.Surjective α) (hψα : ψ.ker ≤ α.ker)
    (hα2 : IsPGroup 2 ↥α.ker) (hcent : ∀ q ∈ α.ker, ∀ g : B, ψ q * ψ g = ψ g * ψ q) :
    ∀ q ∈ α.ker, ψ q = 1 := by
  rcases hA with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, hp, hp3, hn⟩
  · exact noSL25_of_bender (A5.C25.fusionIsBenderGroup_of_isPSL hn) hper hns ψ α hα hψα hα2 hcent
  · exact noSL25_of_bender (A5.C25.fusionIsBenderGroup_of_isSz hn) hper hns ψ α hα hψα hα2 hcent
  · exact noSL25_J1 hJ hper hns ψ α hα hψα hα2 hcent
  · exact noSL25_psl2_odd hp hp3 hn hper hns ψ α hα hψα hα2 hcent

theorem pCoreOf_le_of_blockU_le
    {Kp B : Subgroup G} (hBK : B ≤ Kp) (hBs : IsShort2 B)
    (hB5 : IsAltType B 5) (hA : A38Types (↥Kp ⧸ CFSG.pCore 2 ↥Kp)) (hU : blockU B ≤ pCoreOf 2 Kp) :
    pCoreOf 2 B ≤ pCoreOf 2 Kp := by
  classical
  set N : Subgroup ↥Kp := CFSG.pCore 2 ↥Kp with hN
  set π : ↥Kp →* ↥Kp ⧸ N := QuotientGroup.mk' N with hπ
  have hBq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) :=
    hBs.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl hB5)
  have hBperf : ⁅B, B⁆ = B := C1GN.isShort2_perfect_of_perfect_quotient hBs hBq.1.commutator_eq_top
  have hBne : B ≠ ⊥ := C1GN.isShort2_ne_bot hBs
  have hper : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hBperf
  have hns : ¬ Group.IsSolvable ↥B := by
    intro hsolv
    have : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
    exact Group.IsPerfect.not_isSolvable ↥B hsolv
  let ψ : ↥B →* ↥Kp ⧸ N := π.comp (Subgroup.inclusion hBK)
  obtain ⟨α, hα, hαk, -⟩ := id hB5
  have hα2 : IsPGroup 2 ↥α.ker := by
    rw [hαk]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥B)
  have hBP : B ⊓ pCoreOf 2 Kp ≤ pCoreOf 2 B := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    intro b hb
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hb, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Kp (hBK hb)⟩
  have hψα : ψ.ker ≤ α.ker := by
    intro b hb
    have h1 : (Subgroup.inclusion hBK (b : ↥B) : ↥Kp) ∈ N :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hb)
    have h2 : (b : G) ∈ pCoreOf 2 Kp := (coe_mem_pCoreOf_iff_mem_pCore' _).mpr h1
    rw [hαk]
    exact (coe_mem_pCoreOf_iff_mem_pCore' b).mp (hBP ⟨b.2, h2⟩)
  have hcent : ∀ q ∈ α.ker, ∀ g : ↥B, ψ q * ψ g = ψ g * ψ q := by
    intro q hq g
    rw [hαk] at hq
    have hq' : (q : G) ∈ pCoreOf 2 B := (coe_mem_pCoreOf_iff_mem_pCore' q).mpr hq
    have hcb : ⁅(q : G), (g : G)⁆ ∈ blockU B := Subgroup.commutator_mem_commutator hq' g.2
    have h1 : (Subgroup.inclusion hBK ⁅q, g⁆ : ↥Kp) ∈ N :=
      (coe_mem_pCoreOf_iff_mem_pCore' _).mp (hU hcb)
    have h2 : ψ ⁅q, g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    have h3 : ⁅ψ q, ψ g⁆ = 1 := by
      simp only [commutatorElement_def, map_mul, map_inv] at h2 ⊢
      exact h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  intro c hc
  have hcB : c ∈ B := pCoreOf_le 2 B hc
  have hcα : (⟨c, hcB⟩ : ↥B) ∈ α.ker := by
    rw [hαk]
    exact (coe_mem_pCoreOf_iff_mem_pCore' (⟨c, hcB⟩ : ↥B)).mp hc
  have h1 := noSL25_a38Types hA hper hns ψ α hα hψα hα2 hcent ⟨c, hcB⟩ hcα
  exact (coe_mem_pCoreOf_iff_mem_pCore' (⟨c, hBK hcB⟩ : ↥Kp)).mpr
    ((QuotientGroup.eq_one_iff _).mp h1)

theorem exists_move_blocks (c : Ctx1469A5 T M H u I K₁ K₂ ρ) :
    (∃ t ∈ T ⊓ I, B6.conjSub t K₁ ≠ K₁) ∧ (∃ t ∈ T ⊓ I, B6.conjSub t K₂ ≠ K₂) := by
  have hne := blocks_ne c
  obtain ⟨t₁, ht₁, ht₁₂⟩ := c.blocks.2.2.2.2.2.1 0 1
  obtain ⟨t₂, ht₂, ht₂₁⟩ := c.blocks.2.2.2.2.2.1 1 0
  exact ⟨⟨t₁, ht₁, fun h => hne (h.symm.trans (by simpa using ht₁₂))⟩,
    ⟨t₂, ht₂, fun h => hne ((by simpa using ht₂₁ : B6.conjSub t₂ K₂ = K₁).symm.trans h)⟩⟩

theorem pCoreOf_block_le_of_cComp_ge
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h128 : Lemma128One)
    (hR : A5.C25.RankOneLocalSolvable) (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (hD : dOf1469 T I K₁ K₂ ≠ ⊥) {B Kp : Subgroup G} (hBb : IsBlock2 I B) (hB5 : IsAltType B 5)
    (hBl : quasithinIsLocal (T ⊓ I) B) (hmove : ∃ t ∈ T ⊓ I, B6.conjSub t B ≠ B)
    (hKc : Kp ∈ cComp (iD T I K₁ K₂)) (hBK : B ≤ Kp) : pCoreOf 2 B ≤ pCoreOf 2 Kp := by
  have S : Setting146 G T M := c.ctx.setting
  obtain ⟨hI, -, hsyl⟩ := obs_a_iD c hD
  have hpc : pCoreOf 2 (iD T I K₁ K₂) ≠ ⊥ := hI.1.1.2
  have hnn := not_le_normalizer_of_ge S.hyp1281.qtke S.hyp1281.simple S.hyp1281.nonabelian h128
    hsyl hpc hBl hKc hBK hmove
  rcases lemma_1_2_1_three S.hyp1281.qtke S.hyp1281.simple S.hyp1281.nonabelian hA37 hA38 hpc
    hKc with hnorm | ⟨-, hA⟩
  · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKc)).1 hnorm) hnn
  · exact pCoreOf_le_of_blockU_le hBK hBb.1 hB5 hA
      (blockU_le_pCoreOf_of_a38Types hR hBK hBb.1 hB5 hA)

theorem pCoreOf_blocks_le_pCoreOf_iD
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h128 : Lemma128One) (hR : A5.C25.RankOneLocalSolvable) (c : Ctx1469A5 T M H u I K₁ K₂ ρ)
    (hD : dOf1469 T I K₁ K₂ ≠ ⊥) :
    pCoreOf 2 K₁ ≤ pCoreOf 2 (iD T I K₁ K₂) ∧ pCoreOf 2 K₂ ≤ pCoreOf 2 (iD T I K₁ K₂) := by
  have S : Setting146 G T M := c.ctx.setting
  obtain ⟨hI, -, hsyl⟩ := obs_a_iD c hD
  have hpc : pCoreOf 2 (iD T I K₁ K₂) ≠ ⊥ := hI.1.1.2
  obtain ⟨hl₁, hl₂⟩ := isLocal_blocks c
  have hIID : I ≤ iD T I K₁ K₂ := le_iD_of_blockProduct c.blocks
  have hb₁ : IsBlock2 I K₁ := (c.blocks.2.2.1 0).1
  have hb₂ : IsBlock2 I K₂ := (c.blocks.2.2.1 1).1
  obtain ⟨hm₁, hm₂⟩ := exists_move_blocks c
  have key : ∀ {B : Subgroup G}, IsBlock2 I B → IsAltType B 5 → quasithinIsLocal (T ⊓ I) B →
      (∃ t ∈ T ⊓ I, B6.conjSub t B ≠ B) → pCoreOf 2 B ≤ pCoreOf 2 (iD T I K₁ K₂) := by
    intro B hBb hB5 hBl hmove
    obtain ⟨Kp, hKp, hBKp⟩ := lemma_1_2_4_exists S.hyp1281.qtke S.hyp1281.simple
      S.hyp1281.nonabelian hA37 hA39 hpc hsyl (hBb.2.1.trans hIID) (mem_lFamily_of_isLocal hBl)
    exact (pCoreOf_block_le_of_cComp_ge hA37 hA38 h128 hR c hD hBb hB5 hBl hmove hKp hBKp).trans
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKp))
  exact ⟨key hb₁ c.a5.1 hl₁ hm₁, key hb₂ c.a5.2 hl₂ hm₂⟩

theorem mem_pCoreOf_of_mul_mem_pCoreOf_sup {K₁ K₂ : Subgroup G} (hA5 : IsAltType K₁ 5)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) {a b : G} (ha : a ∈ K₁) (hb : b ∈ K₂)
    (hp : a * b ∈ pCoreOf 2 (K₁ ⊔ K₂)) : a ∈ pCoreOf 2 K₁ := by
  classical
  have hK₁K : K₁ ≤ K₁ ⊔ K₂ := le_sup_left
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hcomm x hx y hy))
  have hKN : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hK₂N
  have hab : a * b ∈ K₁ ⊔ K₂ := pCoreOf_le 2 _ hp
  have hPK₁ : pCoreOf 2 (K₁ ⊔ K₂) ⊓ K₁ ≤ pCoreOf 2 K₁ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hK₁K hk), Subgroup.le_normalizer hk⟩
  have hcommut : ∀ k ∈ K₁, ⁅a, k⁆ ∈ pCoreOf 2 K₁ := by
    intro k hk
    have hbk : b * k * b⁻¹ = k := by rw [(hcomm k hk b hb).symm]; group
    have e : ⁅a * b, k⁆ = ⁅a, k⁆ := by
      simp only [commutatorElement_def]
      calc a * b * k * (a * b)⁻¹ * k⁻¹ = a * (b * k * b⁻¹) * a⁻¹ * k⁻¹ := by group
        _ = a * k * a⁻¹ * k⁻¹ := by rw [hbk]
    rw [← e]
    refine hPK₁ ⟨?_, ?_⟩
    · have h2 : k * (a * b)⁻¹ * k⁻¹ ∈ pCoreOf 2 (K₁ ⊔ K₂) :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hK₁K hk)) (a * b)⁻¹).mp
          ((pCoreOf 2 (K₁ ⊔ K₂)).inv_mem hp)
      have h3 := (pCoreOf 2 (K₁ ⊔ K₂)).mul_mem hp h2
      have e2 : ⁅a * b, k⁆ = a * b * (k * (a * b)⁻¹ * k⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e2]
      exact h3
    · have h2 : a * b * k * (a * b)⁻¹ ∈ K₁ :=
        (Subgroup.mem_normalizer_iff.mp (hKN hab) k).mp hk
      have e2 : ⁅a * b, k⁆ = a * b * k * (a * b)⁻¹ * k⁻¹ := by
        simp only [commutatorElement_def]
      rw [e2]
      exact K₁.mul_mem h2 (K₁.inv_mem hk)
  obtain ⟨α, hα, hαk, -⟩ := hA5
  have hker : ∀ x : ↥K₁, α x = 1 ↔ (x : G) ∈ pCoreOf 2 K₁ := fun x => by
    rw [coe_mem_pCoreOf_iff_mem_pCore', ← hαk, MonoidHom.mem_ker]
  have hcen : α ⟨a, ha⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := hα z
    have h1 : α ⟨⁅a, (y : G)⁆, by
        simp only [commutatorElement_def]
        exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem ha y.2) (K₁.inv_mem ha)) (K₁.inv_mem y.2)⟩ = 1 :=
      (hker _).mpr (hcommut y y.2)
    have h2 : α ⟨a, ha⟩ * α y * (α ⟨a, ha⟩)⁻¹ * (α y)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    have h3 := commutatorElement_eq_one_iff_mul_comm.mp (show ⁅α ⟨a, ha⟩, α y⁆ = 1 from h2)
    exact h3.symm
  have hcb : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  rw [hcb, Subgroup.mem_bot] at hcen
  exact (hker ⟨a, ha⟩).mp hcen

theorem pCoreOf_blocks_sup_le (c : Ctx1469A5 T M H u I K₁ K₂ ρ) :
    pCoreOf 2 (K₁ ⊔ K₂) ≤ pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂ := by
  have h12 : ⁅K₁, K₂⁆ = ⊥ := by simpa using c.blocks.2.2.2.1 0 1 (by decide)
  have hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := fun x hx y hy => by
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [h12, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hcomm x hx y hy))
  intro p hp
  have hpK : p ∈ K₁ ⊔ K₂ := pCoreOf_le 2 _ hp
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hcomm x hx y hy).symm)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hK₁N] at hpK
  obtain ⟨a, ha, b, hb, rfl⟩ := hpK
  have h1 : a ∈ pCoreOf 2 K₁ := mem_pCoreOf_of_mul_mem_pCoreOf_sup c.a5.1 hcomm ha hb hp
  have h2 : b ∈ pCoreOf 2 K₂ := by
    refine mem_pCoreOf_of_mul_mem_pCoreOf_sup c.a5.2 (fun x hx y hy => (hcomm y hy x hx).symm)
      hb ha ?_
    rw [← hcomm a ha b hb, sup_comm]
    exact hp
  exact Subgroup.mul_mem _ ((le_sup_left : pCoreOf 2 K₁ ≤ pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂) h1)
    ((le_sup_right : pCoreOf 2 K₂ ≤ pCoreOf 2 K₁ ⊔ pCoreOf 2 K₂) h2)

theorem false_of_dOf_ne_bot
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h128One : Lemma128One) (hR : A5.C25.RankOneLocalSolvable) (hJ : Input1469A5J)
    (c : Ctx1469A5 T M H u I K₁ K₂ ρ) (f : Facts1469A5 T M u I K₁ K₂)
    (hD : dOf1469 T I K₁ K₂ ≠ ⊥) : False := by
  have hb := pCoreOf_blocks_le_pCoreOf_iD hA37 hA38 hA39 h128One hR c hD
  have hK : pCoreOf 2 (K₁ ⊔ K₂) ≤ pCoreOf 2 (iD T I K₁ K₂) :=
    (pCoreOf_blocks_sup_le c).trans (sup_le hb.1 hb.2)
  exact false_of_pCoreOf_le hJ c f ((pCoreOf_le_pCoreOf_iD c f hK).trans (pCoreOf_iD_le c f hD))

theorem input1469A5DTwo_of_blocks
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h128One : Lemma128One) (hR : A5.C25.RankOneLocalSolvable) (hJ : Input1469A5J) :
    Input1469A5DTwo := by
  intro G _ _ T M H u I K₁ K₂ ρ c f hD _
  exact false_of_dOf_ne_bot hA37 hA38 hA39 h128One hR hJ c f hD

end P1469Two

end CFSG.Quasithin
