module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Block
public import CFSG.Quasithin.EmptyFaithful.S14111
public import CFSG.Quasithin.Background.I4Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

section Chi

theorem perfect_of_short {L : Subgroup G} (hL : IsShort2 L) {Q : Type*} [Group Q]
    [hQ : Group.IsPerfect Q] (α : L →* Q) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 L) : ⁅L, L⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  have hmap : (commutator L).map α = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hα]
    exact hQ.commutator_eq_top
  have hp : IsPGroup 2 (L ⧸ commutator L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : α x ∈ (commutator L).map α := by rw [hmap]; trivial
      obtain ⟨d, hd, hdx⟩ := hx
      have hk : d⁻¹ * x ∈ CFSG.pCore 2 L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨_, hk⟩
      refine ⟨n, ?_⟩
      have hn' : (d⁻¹ * x) ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hdq : (QuotientGroup.mk d : L ⧸ commutator L) = 1 :=
        (QuotientGroup.eq_one_iff d).mpr hd
      have hxq : (QuotientGroup.mk x : L ⧸ commutator L) = QuotientGroup.mk (d⁻¹ * x) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hdq, inv_one, one_mul]
      rw [hxq, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]
  exact hL.1 (commutator L) hp

variable [Finite G]

theorem isAltType_three_of_isChiBlock {M L : Subgroup G} (hL : IsChiBlock M L)
    (hM : Group.IsSolvable M) : IsAltType L 3 := by
  obtain ⟨hblock, htype⟩ := hL
  have hLM : L ≤ M := hblock.2.1
  have hnotperf : ¬ ⁅L, L⁆ = L := by
    intro hp
    have hbot : L = ⊥ := by
      have h1 := le_perfectCore_of_perfect hLM hp
      rw [(isSolvable_iff_perfectCore_eq_bot M).mp hM] at h1
      exact le_bot_iff.mp h1
    have hlt := hblock.1.2.2.2.2.1
    have hU : blockU L = ⊥ := by
      rw [blockU, hbot, Subgroup.commutator_bot_right]
    exact absurd (hU ▸ hlt) (not_lt_bot)
  rcases htype with ⟨n, hn, F, hF, hFt, hcard, α, hα, hker, -⟩ | ⟨m, hm, hm3, hAlt⟩
  · exfalso
    apply hnotperf
    have h4 : ∃ s : Finset F, s.card = 4 := by
      have : 4 ≤ (Finset.univ : Finset F).card := by
        rw [Finset.card_univ, hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq this
      exact ⟨t, ht⟩
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    exact perfect_of_short hblock.1 α hα hker
  · by_cases hm3' : m = 3
    · rwa [hm3'] at hAlt
    · exfalso
      apply hnotperf
      obtain ⟨α, hα, hker, -⟩ := hAlt
      have h5 : 5 ≤ Nat.card (Fin m) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        obtain ⟨k, rfl⟩ := hm
        omega
      have : Group.IsPerfect (alternatingGroup (Fin m)) :=
        ⟨commutator_alternatingGroup_eq_top h5⟩
      exact perfect_of_short hblock.1 α hα hker

end Chi

section Subnormal

variable [Finite G]

omit [Finite G] in
theorem pCoreOf_eq_self {p : ℕ} {Y : Subgroup G} (hY : IsPGroup p Y) : pCoreOf p Y = Y := by
  refine le_antisymm (pCoreOf_le p Y) fun y hy => ?_
  have htop : (⊤ : Subgroup Y) ≤ CFSG.Open.pCore p Y :=
    le_pCore p Subgroup.normal_top (hY.of_equiv Subgroup.topEquiv.symm)
  exact ⟨⟨y, hy⟩, htop (Subgroup.mem_top _), rfl⟩

omit [Finite G] in
theorem pCoreOf_le_top_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hK : K.IsSubnormal) : pCoreOf p K ≤ pCoreOf p ⊤ := by
  induction hK with
  | top => exact le_rfl
  | step H K hle hK hN ih =>
    refine le_trans ?_ ih
    refine le_pCoreOf_of_le_normalizer p ((pCoreOf_le p H).trans hle) ?_ (pCoreOf_isPGroup p H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact normalizer_le_normalizer_pCoreOf p H hmH

theorem le_pCoreOf_top_of_isSubnormal {p : ℕ} [Fact p.Prime] {Y : Subgroup G}
    (hY : Y.IsSubnormal) (hp : IsPGroup p Y) : Y ≤ pCoreOf p ⊤ := by
  rw [← pCoreOf_eq_self hp]
  exact pCoreOf_le_top_of_isSubnormal hY

theorem le_normalizer_of_isSubnormal {M X Q V : Subgroup G} (hX : IsA4 X Q) (hXM : X ≤ M)
    (hXs : (X.subgroupOf M).IsSubnormal) (hVM : V ≤ M)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V) :
    V ≤ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := X ⊔ V with hYdef
  have hYM : Y ≤ M := sup_le hXM hVM
  have hsub : (X.subgroupOf Y).IsSubnormal := by
    have := hXs.comap (Subgroup.inclusion hYM)
    convert this using 1
    ext y
    simp [Subgroup.mem_subgroupOf]
  have hidx : ∃ k : ℕ, (X.subgroupOf Y).index = 2 ^ k := by
    have h1 : (X.subgroupOf Y).index = X.relIndex V :=
      relIndex_sup_eq_relIndex (hXM.trans hMV)
    obtain ⟨n, hn⟩ := hV2.exists_card_eq
    have h2 : X.relIndex V ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact ⟨k, h1.trans hk⟩
  have hodd : ∀ v ∈ V, ∀ y ∈ X, Odd (orderOf y) → v * y * v⁻¹ ∈ X := by
    intro v hv y hy hyodd
    have hmem : v * y * v⁻¹ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Subgroup.mem_sup_right hv) (Subgroup.mem_sup_left hy))
        (Y.inv_mem (Subgroup.mem_sup_right hv))
    have hord : Odd (orderOf (⟨v * y * v⁻¹, hmem⟩ : Y)) := by
      rw [Subgroup.orderOf_mk]
      have := (MulAut.conj v).orderOf_eq y
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hyodd
    exact Subgroup.mem_subgroupOf.mp (mem_of_isSubnormal_of_odd hsub hidx hord)
  intro v hv
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : X ≤ X.comap (MulAut.conj v).toMonoidHom := by
    refine hX.le_of_forall_syl3_le fun P hP y hyP => ?_
    show v * y * v⁻¹ ∈ X
    refine hodd v hv y (hP.1 hyP) ?_
    have h3 : orderOf y ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard P hyP
      rwa [hP.2] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h <;> rw [h] <;> decide
  exact hle hx

theorem commutator_eq_of_isSubnormal {M X Q V : Subgroup G} (hX : IsA4 X Q)
    (hQ : Q = pCoreOf 2 X) (hXM : X ≤ M) (hXs : (X.subgroupOf M).IsSubnormal) (hVM : V ≤ M)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (hXV : ¬ X ≤ Subgroup.centralizer (V : Set G)) : ⁅V, X⁆ = Q := by
  have hVX := le_normalizer_of_isSubnormal hX hXM hXs hVM hMV hV2
  have hcX : ⁅V, X⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVX hv) x).mp hx) (X.inv_mem hx)
  have hcV : ⁅V, X⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    have : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
    rw [this]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hMV (hXM hx)) v⁻¹).mp (V.inv_mem hv))
  have hnorm : X ≤ Subgroup.normalizer ((⁅V, X⁆ : Subgroup G) : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem fun w hw => ?_
    have hmap : (⁅V, X⁆).map (MulAut.conj x).toMonoidHom ≤ ⁅V, X⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hMV (hXM hx)) v).mp hv
      · rintro _ ⟨y, hy, rfl⟩
        exact X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
    exact hmap ⟨w, hw, rfl⟩
  have hcQ : ⁅V, X⁆ ≤ Q := by
    rw [hQ]
    exact le_pCoreOf_of_le_normalizer 2 hcX hnorm (hV2.to_le hcV)
  rcases hX.eq_bot_or_eq hcQ hnorm with h | h
  · exfalso
    apply hXV
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (this hv) x hx).symm
  · exact h

end Subnormal

section Rhat

variable [Finite G]

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hg)
      v).mp hv
  have h1 := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * v := by group

theorem exists_rhat {M V : Subgroup G} (hVM : V ≤ M) (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hVab : V ≤ Subgroup.centralizer (V : Set G)) (hF : CharTwo M) :
    ∃ R : Subgroup G, V ≤ R ∧ R ≤ M ∧ M ≤ Subgroup.normalizer (R : Set G) ∧
      (∀ r ∈ R, ∃ k : ℕ, r ^ 3 ^ k ∈ V) ∧ R ⊓ Subgroup.centralizer (V : Set G) ≤ V ∧
      ∀ Y : Subgroup G, Y ≤ M → (Y.subgroupOf M).IsSubnormal →
        (∀ y ∈ Y, ∃ k : ℕ, y ^ 3 ^ k ∈ V) → Y ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVn : (V.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr hMV
  set π := QuotientGroup.mk' (V.subgroupOf M) with hπ
  set O : Subgroup (↥M ⧸ V.subgroupOf M) := pCoreOf 3 ⊤ with hO
  have hOn : O.Normal := ⟨fun n hn g =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 ⊤ (Subgroup.mem_top g)) n).mp hn⟩
  set R₀ : Subgroup M := O.comap π with hR₀
  set R : Subgroup G := R₀.map M.subtype with hR
  have hRM : R ≤ M := Subgroup.map_subtype_le _
  have hMR : M ≤ Subgroup.normalizer (R : Set G) := by
    intro m hm
    refine mem_normalizer_of_conj_mem ?_
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨⟨m, hm⟩ * r * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    show π (⟨m, hm⟩ * r * ⟨m, hm⟩⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact hOn.conj_mem _ hr _
  have hR3 : ∀ r ∈ R, ∃ k : ℕ, r ^ 3 ^ k ∈ V := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 3 (⊤ : Subgroup (↥M ⧸ V.subgroupOf M))) ⟨π r, hr⟩
    refine ⟨k, ?_⟩
    have h1 : π (r ^ 3 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    simpa using Subgroup.mem_subgroupOf.mp h2
  have hVR : V ≤ R := by
    intro v hv
    refine ⟨⟨v, hVM hv⟩, ?_, rfl⟩
    show π ⟨v, hVM hv⟩ ∈ O
    have : π ⟨v, hVM hv⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hv)
    rw [this]
    exact O.one_mem
  refine ⟨R, hVR, hRM, hMR, hR3, ?_, ?_⟩
  ·
    set N₁ : Subgroup G := R ⊓ Subgroup.centralizer (V : Set G) with hN₁
    have hN₁M : N₁ ≤ M := inf_le_left.trans hRM
    have hMN₁ : M ≤ Subgroup.normalizer (N₁ : Set G) := fun m hm =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hMR hm, normalizer_le_normalizer_centralizer V (hMV hm)⟩
    have hVN₁ : V ≤ N₁ := le_inf hVR hVab
    have hO3 : pCoreOf 3 N₁ = ⊥ := by
      refine I4.eq_bot_of_normal_of_coprime_of_le hF ((pCoreOf_le 3 N₁).trans hN₁M) ?_ ?_
      · exact (Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 3 N₁).trans hN₁M)).mpr
          (hMN₁.trans (normalizer_le_normalizer_pCoreOf 3 N₁))
      · obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 3 N₁).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num)
    have hVn₁ : (V.subgroupOf N₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVN₁).mpr (inf_le_left.trans
        (hRM.trans hMV))
    have hq3 : IsPGroup 3 (↥N₁ ⧸ V.subgroupOf N₁) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H n =>
        obtain ⟨k, hk⟩ := hR3 n n.2.1
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hk
    have hnil : Group.IsNilpotent N₁ := by
      have := hq3.isNilpotent
      refine Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (V.subgroupOf N₁)) ?_
      intro n hn
      rw [QuotientGroup.ker_mk'] at hn
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp m.2.2 n (Subgroup.mem_subgroupOf.mp hn)).symm
    have hnd : ¬ 3 ∣ Nat.card N₁ := by
      intro hd
      obtain P : Sylow 3 N₁ := default
      have hPn : (P : Subgroup N₁).Normal := hnil.sylow_normal 3 P
      have hle : (P : Subgroup N₁).map N₁.subtype ≤ pCoreOf 3 N₁ := by
        refine le_pCoreOf_of_le_normalizer 3 (Subgroup.map_subtype_le _) ?_ ?_
        · intro n hn
          refine mem_normalizer_of_conj_mem ?_
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨⟨n, hn⟩ * x * ⟨n, hn⟩⁻¹, hPn.conj_mem x hx _, rfl⟩
        · exact P.isPGroup'.map N₁.subtype
      rw [hO3, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N₁.subtype_injective] at hle
      have hcard := P.card_eq_multiplicity
      rw [hle, Subgroup.card_bot] at hcard
      have hpos : 0 < (Nat.card N₁).factorization 3 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hd
      have := (Nat.pow_eq_one.mp hcard.symm)
      omega
    intro n hn
    obtain ⟨k, hk⟩ := hR3 n hn.1
    let q : ↥N₁ ⧸ V.subgroupOf N₁ := ((⟨n, hn⟩ : N₁) : ↥N₁ ⧸ V.subgroupOf N₁)
    have hq1 : q ^ 3 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    have hq2 : q ^ Nat.card (↥N₁ ⧸ V.subgroupOf N₁) = 1 := pow_card_eq_one'
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (↥N₁ ⧸ V.subgroupOf N₁)) := by
      refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
      intro h3
      exact hnd (h3.trans (Subgroup.card_quotient_dvd_card _))
    have hq : q = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hq1, hq2⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)
  ·
    intro Y hYM hYs hY3
    have hmap := hYs.map (f := π) (QuotientGroup.mk'_surjective _)
    have hp : IsPGroup 3 ((Y.subgroupOf M).map π) := by
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      obtain ⟨k, hk⟩ := hY3 y hy
      refine ⟨k, Subtype.ext ?_⟩
      show π y ^ 3 ^ k = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
    have hle := le_pCoreOf_top_of_isSubnormal hmap hp
    intro y hy
    exact ⟨⟨y, hYM hy⟩, hle ⟨⟨y, hYM hy⟩, hy, rfl⟩, rfl⟩

end Rhat


end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
