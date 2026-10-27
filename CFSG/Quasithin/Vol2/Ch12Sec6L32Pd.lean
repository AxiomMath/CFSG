module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33f
public import CFSG.Quasithin.Vol2.Ch5Sec1L34E54NoFF
public import CFSG.Quasithin.Vol2.Ch9KGFFB51

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S126 F126 L1233
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Aut

variable {X : Type*} [Group X] {S : Type*} [Group S]

theorem eq_one_of_commute_conj (hZ : Subgroup.center S = ⊥) {φ : MulAut S}
    (hφ : ∀ s : S, φ * MulAut.conj s = MulAut.conj s * φ) : φ = 1 := by
  ext s : 1
  have h2 : s⁻¹ * φ s ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have e := congrArg (fun ψ : MulAut S => ψ (φ.symm g)) (hφ s)
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at e
    symm
    calc s⁻¹ * φ s * g = s⁻¹ * (φ s * g * (φ s)⁻¹) * φ s := by group
      _ = s⁻¹ * (s * g * s⁻¹) * φ s := by rw [e]
      _ = g * (s⁻¹ * φ s) := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2.symm

theorem conj_injective (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro s hs
  rw [MonoidHom.mem_ker] at hs
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun ψ : MulAut S => ψ g) hs
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc g * s = s * g * s⁻¹ * s := by rw [this]
    _ = s * g := by group

theorem centralizer_eq_bot_of_aut [Finite S] (hZ : Subgroup.center S = ⊥) (e : X ≃* MulAut S)
    {N : Subgroup X} (hNn : N.Normal) (hN : IsSimpleGroup ↥N) (hc : Nat.card ↥N = Nat.card S) :
    Subgroup.centralizer (N : Set X) = ⊥ := by
  set Inn : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hInn
  have hInnN : Inn.Normal := ⟨by
    rintro _ ⟨s, rfl⟩ φ
    refine ⟨φ s, ?_⟩
    ext y : 1
    simp [MulAut.mul_apply, MulAut.conj_apply]⟩
  have hcInn : Nat.card ↥Inn = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective hZ)).toEquiv).symm
  set M : Subgroup X := Inn.comap e.toMonoidHom with hM
  have hMn : M.Normal := hInnN.comap _
  have hNM : N ≤ M := by
    have hsub : ((M ⊓ N).subgroupOf N).Normal := by
      have := hMn
      have := hNn
      exact (inferInstance : (M ⊓ N).Normal).subgroupOf N
    rcases hsub.eq_bot_or_eq_top with h | h
    · exfalso
      have hcomm : ⁅N, M⁆ = ⊥ := by
        have h1 := Subgroup.commutator_le_inf N M
        rw [inf_comm] at h1
        rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_assoc, inf_idem] at h
        exact le_bot_iff.1 (h ▸ h1)
      have hN1 : N = ⊥ := by
        rw [eq_bot_iff]
        intro n hn
        rw [Subgroup.mem_bot]
        apply e.injective
        rw [map_one]
        refine eq_one_of_commute_conj hZ fun s => ?_
        obtain ⟨m, hm⟩ := e.surjective (MulAut.conj s)
        have hmM : m ∈ M := by
          show e m ∈ Inn
          rw [hm]
          exact ⟨s, rfl⟩
        have hc' : ⁅n, m⁆ = 1 := by
          have := Subgroup.commutator_mem_commutator hn hmM
          rw [hcomm, Subgroup.mem_bot] at this
          exact this
        rw [commutatorElement_eq_one_iff_mul_comm] at hc'
        rw [← hm, ← map_mul, hc', map_mul]
      have : Nontrivial ↥N := hN.toNontrivial
      rw [hN1] at this
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
    · intro n hn
      have : (⟨n, hn⟩ : ↥N) ∈ (M ⊓ N).subgroupOf N := h ▸ Subgroup.mem_top _
      exact this.1
  have hNI : N.map e.toMonoidHom = Inn := by
    refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨n, hn, h⟩ => h ▸ hNM hn) ?_
    rw [hcInn, Subgroup.card_map_of_injective e.injective, hc]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [map_one]
  refine eq_one_of_commute_conj hZ fun s => ?_
  have hs : MulAut.conj s ∈ N.map e.toMonoidHom := by
    rw [hNI]
    exact ⟨s, rfl⟩
  obtain ⟨n, hn, hns⟩ := hs
  rw [← hns]
  show e x * e n = e n * e x
  rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hx n hn).symm]

theorem sq_mul_eq_one_of_commute {a b : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hc : a * (a * b) ^ 2 = (a * b) ^ 2 * a) (h3 : ((a * b) ^ 2) ^ 3 = 1) : (a * b) ^ 2 = 1 := by
  set z := (a * b) ^ 2 with hz
  have haa : a * a = 1 := by rw [← sq]; exact ha
  have hbb : b * b = 1 := by rw [← sq]; exact hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have h1 : a * z * a⁻¹ = b * a * b * a := by
    calc a * z * a⁻¹ = (a * a) * (b * a * b * a⁻¹) := by rw [hz, sq]; group
      _ = b * a * b * a := by rw [haa, one_mul, ha']
  have h2 : z⁻¹ = b * a * b * a := by
    rw [hz, sq, mul_inv_rev, mul_inv_rev, ha', hb']
    group
  have h4 : a * z * a⁻¹ = z := by rw [hc, mul_inv_cancel_right]
  have h5 : z * z = 1 := by
    calc z * z = z * z⁻¹ := by rw [h2, ← h1, h4]
      _ = 1 := mul_inv_cancel z
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [h3, h5, inv_one, one_mul]

theorem centralizer_le_of_sq_mem [Finite X] {N : Subgroup X} (hNn : N.Normal)
    (hsq : ∀ x : X, x ^ 2 ∈ N) (hO2 : CFSG.pCore 2 X = ⊥)
    (h3 : ∀ z ∈ N, z ∈ Subgroup.centralizer (N : Set X) → z ^ 3 = 1) :
    Subgroup.centralizer (N : Set X) ≤ N := by
  set C := Subgroup.centralizer (N : Set X) with hCdef
  have hCconj : ∀ (g : X) {y : X}, y ∈ C → g * y * g⁻¹ ∈ C := by
    intro g y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro n hn
    have h1 := hy (g⁻¹ * n * g) (by simpa using hNn.conj_mem n hn g⁻¹)
    calc n * (g * y * g⁻¹) = g * ((g⁻¹ * n * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * n := by group
  let P : Subgroup X :=
    { carrier := {y | y ∈ C ∧ y ^ 2 = 1}
      one_mem' := ⟨C.one_mem, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨haC, ha2⟩ ⟨hbC, hb2⟩
        refine ⟨C.mul_mem haC hbC, sq_mul_eq_one_of_commute ha2 hb2 ?_ ?_⟩
        · exact (Subgroup.mem_centralizer_iff.mp haC _ (hsq _)).symm
        · exact h3 _ (hsq _) (C.pow_mem (C.mul_mem haC hbC) 2)
      inv_mem' := by
        rintro y ⟨hyC, hy2⟩
        exact ⟨C.inv_mem hyC, by rw [inv_pow, hy2, inv_one]⟩ }
  have hPn : P.Normal := ⟨fun y hy g => ⟨hCconj g hy.1, by
    rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩⟩
  have hP2 : IsPGroup 2 ↥P := fun y => ⟨1, Subtype.ext (by simpa using y.2.2)⟩
  have hPle : P ≤ CFSG.pCore 2 X := by
    exact CFSG.LieType.BorelTits.le_pCore 2 hPn hP2
  rw [hO2] at hPle
  intro x hx
  have hx2N : x ^ 2 ∈ N := hsq x
  have h6 : (x ^ 2) ^ 3 = 1 := h3 _ hx2N (C.pow_mem hx 2)
  have hx3 : x ^ 3 = 1 := by
    have hy : x ^ 3 ∈ P :=
      ⟨C.pow_mem hx 3, by rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, h6]⟩
    exact Subgroup.mem_bot.1 (hPle hy)
  have e : x = (x ^ 2) ^ 2 * (x ^ 3)⁻¹ := by group
  rw [e, hx3, inv_one, mul_one]
  exact N.pow_mem hx2N 2

end Aut

section Case1

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem star_normal_of_case1 (h918 : HypF918 T V L V₁ Vp H K) (h1 : Case1 T L H K) :
    (S126.star H K).Normal := by
  have : (K.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgN := h918.K₀_normal g.2
    rw [h1.1] at hgN
    exact (Subgroup.mem_normalizer_iff.1 hgN n).1 hn⟩
  exact this.map _ (QuotientGroup.mk'_surjective _)

theorem lieModel_psl3Model {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    CFSG.Blueprint.LieModel (PSL3Model F) .PSL 3 2 2 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, F,
    inferInstance, inferInstance, by rw [hF]; norm_num, ⟨MulEquiv.refl _⟩⟩

theorem center_psl3Model_eq_bot {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Subgroup.center (PSL3Model F) = ⊥ := by
  have hLie := lieModel_psl3Model hF
  have : IsSimpleGroup (PSL3Model F) := E54.isSimpleGroup_of_lieModel hLie
  rcases (Subgroup.center (PSL3Model F)).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : PSL3Model F, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
    let _ : CommGroup (PSL3Model F) := { (inferInstance : Group (PSL3Model F)) with
      mul_comm := hcomm }
    have hp : (Nat.card (PSL3Model F)).Prime := IsSimpleGroup.prime_card
    rw [E54.card_of_lieModel hLie] at hp
    norm_num at hp

theorem centralizer_star_le_of_case1 (h918 : HypF918 T V L V₁ Vp H K) (h1 : Case1 T L H K) :
    Subgroup.centralizer (S126.star H K : Set (S126.HStar H)) ≤ S126.star H K ∧
      ∀ z ∈ S126.star H K, z ∈ Subgroup.centralizer (S126.star H K : Set (S126.HStar H)) →
        z ^ 3 = 1 := by
  have hKn := star_normal_of_case1 h918 h1
  rcases h1.2.1 with ⟨F, _, _, hF, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨F, _, _, hF, ⟨e₁⟩, -, hsq⟩
  · have : IsSimpleGroup (PSL3Model F) := E54.isSimpleGroup_of_lieModel (lieModel_psl3Model hF)
    have hN : IsSimpleGroup ↥(S126.star H K) := e₁.isSimpleGroup
    have hC := centralizer_eq_bot_of_aut (center_psl3Model_eq_bot hF) e₂ hKn hN
      (Nat.card_congr e₁.toEquiv)
    rw [hC]
    exact ⟨bot_le, fun z _ hz => by rw [Subgroup.mem_bot.1 hz, one_pow]⟩
  · have h3 : ∀ z ∈ S126.star H K,
        z ∈ Subgroup.centralizer (S126.star H K : Set (S126.HStar H)) → z ^ 3 = 1 := by
      intro z hz hzc
      have hcen : (⟨z, hz⟩ : ↥(S126.star H K)) ∈ Subgroup.center ↥(S126.star H K) :=
        Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc g g.2)
      have hc3 : Nat.card ↥(Subgroup.center ↥(S126.star H K)) = 3 := by
        rw [Nat.card_congr (Subgroup.centerCongr
          (e₁.trans (specialLinearGroupEquivStatedSL 3 F).symm)).toEquiv]
        exact Ch9.KGFF.card_center_sl3_four hF
      have h1' := pow_card_eq_one' (G := ↥(Subgroup.center ↥(S126.star H K)))
        (x := ⟨⟨z, hz⟩, hcen⟩)
      rw [hc3] at h1'
      exact congrArg (fun w : ↥(Subgroup.center ↥(S126.star H K)) =>
        (((w : ↥(S126.star H K)) : S126.HStar H))) h1'
    exact ⟨centralizer_le_of_sq_mem hKn hsq
      (CFSG.QuasithinUnique.Setup.Campbell.pCore_quotient_pCore_eq_bot' 2) h3, h3⟩

theorem exists_outer_pair (h918 : HypF918 T V L V₁ Vp H K) (h1 : Case1 T L H K)
    (hidx : (S126.star H K).index = 4) (hsq : ∀ x : S126.HStar H, x ^ 2 ∈ S126.star H K) :
    ∃ t₁ t₂ : ↥H, (t₁ : G) ∈ T ∧ (t₂ : G) ∈ T ∧
      (QuotientGroup.mk t₁ : S126.HStar H) ∉ S126.star H K ∧
      (QuotientGroup.mk t₂ : S126.HStar H) ∉ S126.star H K ∧
      (QuotientGroup.mk (t₁ * t₂⁻¹) : S126.HStar H) ∉ S126.star H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := star_normal_of_case1 h918 h1
  set f : S126.HStar H →* S126.HStar H ⧸ S126.star H K := QuotientGroup.mk' _ with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hQ : Nat.card (S126.HStar H ⧸ S126.star H K) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hTs := card_star_of_sylow h918.toHypF98.toHypF91.sylow_H
  set P := Sylow.ofCard (p := 2) (S126.star H T) hTs with hP
  have hP' : (↑(Sylow.mapSurjective hfs P) : Subgroup (S126.HStar H ⧸ S126.star H K)) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Sylow.card_eq_multiplicity, hQ,
      factorization_two_eq (n := 4) (k := 2) (by norm_num) (by norm_num) (by norm_num)]
    rfl
  rw [Sylow.coe_mapSurjective] at hP'
  have hsqQ : ∀ q : S126.HStar H ⧸ S126.star H K, q ^ 2 = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := hfs q
    rw [← map_pow, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hsq x
  have : Nontrivial (S126.HStar H ⧸ S126.star H K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQ]
    norm_num
  obtain ⟨q₁, hq₁⟩ := exists_ne (1 : S126.HStar H ⧸ S126.star H K)
  obtain ⟨q₂, hq₂1, hq₂q₁⟩ : ∃ q₂ : S126.HStar H ⧸ S126.star H K, q₂ ≠ 1 ∧ q₂ ≠ q₁ := by
    by_contra hno
    push Not at hno
    have hsurj : Function.Surjective (![1, q₁] : Fin 2 → S126.HStar H ⧸ S126.star H K) := by
      intro q
      by_cases h : q = 1
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [hno q h]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hQ, Nat.card_fin] at this
    omega
  have hlift : ∀ q : S126.HStar H ⧸ S126.star H K, ∃ t : ↥H, (t : G) ∈ T ∧
      f (QuotientGroup.mk t) = q := by
    intro q
    have hq : q ∈ (S126.star H T).map f := hP' ▸ Subgroup.mem_top q
    obtain ⟨y, ⟨t, ht, rfl⟩, rfl⟩ := hq
    exact ⟨t, Subgroup.mem_subgroupOf.1 ht, rfl⟩
  obtain ⟨t₁, ht₁T, ht₁⟩ := hlift q₁
  obtain ⟨t₂, ht₂T, ht₂⟩ := hlift q₂
  have hnot : ∀ y : S126.HStar H, f y ≠ 1 → y ∉ S126.star H K := fun y hy hyK =>
    hy ((QuotientGroup.eq_one_iff y).2 hyK)
  refine ⟨t₁, t₂, ht₁T, ht₂T, hnot _ (ht₁ ▸ hq₁), hnot _ (ht₂ ▸ hq₂1), hnot _ ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, ht₁, ht₂]
  exact fun h => hq₂q₁ (mul_inv_eq_one.1 h).symm

end Case1

end CFSG.Quasithin.H13.L1232
