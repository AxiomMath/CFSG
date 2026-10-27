module

public import CFSG.Quasithin.Background.F6CatM12ShapeChk
public import CFSG.Quasithin.Background.F6NQShapes
public import CFSG.Quasithin.Recognition.M12AmalFacts
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Recognition.M12AmalClass

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12Amal CFSG.Sporadic.Bridge

namespace F6

theorem IsExtensionOf.of_mulEquiv {X Y A N : Type*} [Group X] [Group Y] [Group A] [Group N]
    (e : X ≃* Y) (h : IsExtensionOf Y A N) : IsExtensionOf X A N := by
  obtain ⟨φ, hφ, ⟨eN⟩⟩ := h
  refine ⟨φ.comp e.toMonoidHom, hφ.comp e.surjective, ⟨?_⟩⟩
  have hker : (φ.comp e.toMonoidHom).ker.map e.toMonoidHom = φ.ker := by
    rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq_self_of_surjective e.surjective]
  exact ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hker)).trans eN

instance isKleinFour_z2_sq : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  isKleinFour_of_card_four_of_mul_self (by rw [Nat.card_eq_fintype_card]; rfl) (by decide)

namespace M12Shape

@[expose] noncomputable def z4Hom : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* M12G where
  toFun g := telG (z4Idx g)
  map_one' := by rw [z4_one_chk]; exact tel_zero
  map_mul' g h := by
    have hg := N_lt_chk _ (z4_mem_chk g)
    have hh := N_lt_chk _ (z4_mem_chk h)
    have hgh := N_lt_chk _ (z4_mem_chk (g * h))
    exact (eq_of_compL_eq hg hh hgh (z4_mul_chk g h)).symm

theorem z4Hom_injective : Function.Injective z4Hom := by
  intro g h hgh
  have h1 : telG (z4Idx g) = telG (z4Idx h) := hgh
  have hg := N_lt_chk _ (z4_mem_chk g)
  have hh := N_lt_chk _ (z4_mem_chk h)
  exact z4_inj_chk g h (tl_inj_chk _ hg _ hh
    (repL_unique (reprG_tel _ hg) (h1 ▸ reprG_tel _ hh)))

@[expose] noncomputable def N : Subgroup M12G := z4Hom.range

theorem mem_N_iff {g : M12G} : g ∈ N ↔ ∃ i ∈ NIdx, g = telG i := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨_, z4_mem_chk h, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨h, hh⟩ := z4_surj_chk i hi
    exact ⟨h, by rw [← hh]; rfl⟩

noncomputable def NEquiv : ↥N ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (MonoidHom.ofInjective z4Hom_injective).symm

theorem card_N : Nat.card ↥N = 16 := by
  rw [Nat.card_congr NEquiv.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem N_le_T : N ≤ m12Data.T := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := mem_N_iff.mp hg
  exact m12Data.Tel_mem_T ⟨i, N_lt_chk i hi⟩

theorem mem_N_of_reprG {l : List ℕ} {g : M12G} (hg : ReprG l g) (h : ∃ k ∈ NIdx, l = tl k) :
    g ∈ N := by
  obtain ⟨k, hk, rfl⟩ := h
  exact mem_N_iff.mpr ⟨k, hk, eq_of_reprG hg (reprG_tel k (N_lt_chk k hk))⟩

theorem not_mem_N_of_reprG {l : List ℕ} {g : M12G} (hg : ReprG l g) (h : ∀ k ∈ NIdx, l ≠ tl k) :
    g ∉ N := by
  intro hgN
  obtain ⟨k, hk, rfl⟩ := mem_N_iff.mp hgN
  exact h k hk (repL_unique hg (reprG_tel k (N_lt_chk k hk)))

theorem B_le_normalizer : m12Data.B ≤ Subgroup.normalizer (N : Set M12G) := by
  refine closure_le_normalizer_of_conj _ N fun g hg n hn => ?_
  obtain ⟨i, hi, rfl⟩ := mem_N_iff.mp hn
  have hi64 := N_lt_chk i hi
  have key : ∀ k : ℕ, k ∈ [0, 1, 2, 4] → g = genG k →
      g * telG i * g⁻¹ ∈ N ∧ g⁻¹ * telG i * g ∈ N := by
    intro k hk hgk
    subst hgk
    have hk5 : k < 5 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    obtain ⟨h1, h2⟩ := N_norm_chk k hk i hi
    exact ⟨mem_N_of_reprG (reprG_mul (reprG_mul (reprG_gen k hk5) (reprG_tel i hi64))
      (reprG_inv_gen k hk5)) h1, mem_N_of_reprG (reprG_mul (reprG_mul (reprG_inv_gen k hk5)
        (reprG_tel i hi64)) (reprG_gen k hk5)) h2⟩
  change g ∈ ({genG 0, genG 1, genG 2, genG 4} : Set M12G) at hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h
  · exact key 0 (by simp) h
  · exact key 1 (by simp) h
  · exact key 2 (by simp) h
  · exact key 4 (by simp) h

theorem normal_subgroupOf_B : (N.subgroupOf m12Data.B).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (N_le_T.trans m12Data.T_le_B)).mpr B_le_normalizer

theorem normal_subgroupOf_T : (N.subgroupOf m12Data.T).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer N_le_T).mpr
    (m12Data.T_le_B.trans B_le_normalizer)

theorem sq_mem_N {t : M12G} (ht : t ∈ m12Data.T) : t * t ∈ N := by
  obtain ⟨i, rfl⟩ := (m12Data.mem_T_iff t).mp ht
  exact mem_N_of_reprG (reprG_mul (reprG_tel i i.2) (reprG_tel i i.2)) (T_sq_chk i i.2)

theorem card_T : Nat.card ↥m12Data.T = 64 := m12_card_T

theorem T_shape : IsExtensionOf ↥m12Data.T (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have := normal_subgroupOf_T
  set N' := N.subgroupOf m12Data.T with hN'
  have hN'card : Nat.card ↥N' = 16 := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe N_le_T).toEquiv, card_N]
  have hQ4 : Nat.card (↥m12Data.T ⧸ N') = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [card_T, hN'card] at h1
    omega
  have hK : IsKleinFour (↥m12Data.T ⧸ N') := by
    refine isKleinFour_of_card_four_of_mul_self hQ4 fun q => ?_
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    exact sq_mem_N t.2
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥m12Data.T ⧸ N')
    (G₂ := Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N'), e.surjective.comp
    (QuotientGroup.mk'_surjective N'), ⟨?_⟩⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' N')).ker = N' := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (MulEquiv.subgroupCongr hker).trans
    ((Subgroup.subgroupOfEquivOfLe N_le_T).trans NEquiv)


theorem reprG_rho : ReprG rhoL (genG 4 * genG 2) :=
  reprG_mul (reprG_gen 4 (by norm_num)) (reprG_gen 2 (by norm_num))

theorem reprG_rhoPow (m : ℕ) : ReprG (rhoPowL m) ((genG 4 * genG 2) ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact reprG_one
  | succ m ih => rw [pow_succ]; exact reprG_mul ih reprG_rho

theorem B_shape (hB : Nat.card ↥m12Data.B = 192) : IsExtensionOf ↥m12Data.B (DihedralGroup 6)
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have := normal_subgroupOf_B
  have hNB : N ≤ m12Data.B := N_le_T.trans m12Data.T_le_B
  set N' := N.subgroupOf m12Data.B with hN'
  have hN'card : Nat.card ↥N' = 16 := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv, card_N]
  have hQ12 : Nat.card (↥m12Data.B ⧸ N') = 12 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [hB, hN'card] at h1
    omega
  have haB : genG 0 ∈ m12Data.B := m12Data.T_le_B m12Data.a_mem_T
  have hsB : genG 2 ∈ m12Data.B := m12Data.T_le_B m12Data.s_mem_T
  have hyB : genG 4 ∈ m12Data.B := m12Data.y_mem_B
  have hmk : ∀ b : ↥m12Data.B, (QuotientGroup.mk b : ↥m12Data.B ⧸ N') = 1 ↔ (b : M12G) ∈ N :=
    fun b => by rw [QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
  set r : ↥m12Data.B := ⟨genG 4 * genG 2, m12Data.B.mul_mem hyB hsB⟩ with hr
  set a : ↥m12Data.B := ⟨genG 0, haB⟩ with ha
  set ρ : ↥m12Data.B ⧸ N' := QuotientGroup.mk r with hρ
  set σ : ↥m12Data.B ⧸ N' := QuotientGroup.mk a with hσ
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← QuotientGroup.mk_pow, hmk, pow_two]
    exact mem_N_of_reprG (reprG_mul (reprG_gen 0 (by norm_num)) (reprG_gen 0 (by norm_num)))
      sigma_sq_chk
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hσ, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, hmk]
    exact mem_N_of_reprG (reprG_mul (reprG_mul (reprG_mul (reprG_gen 0 (by norm_num))
      reprG_rho) (reprG_inv_gen 0 (by norm_num))) reprG_rho) sigma_rho_chk
  have hρpow : ∀ m : ℕ, ρ ^ m = 1 ↔ (genG 4 * genG 2) ^ m ∈ N := fun m => by
    rw [hρ, ← QuotientGroup.mk_pow, hmk]
    rfl
  have hρo : orderOf ρ = 6 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
      ((hρpow 6).mpr (mem_N_of_reprG (reprG_rhoPow 6) rho_six_chk)) fun q hq hq6 => ?_
    have hq23 : q = 2 ∨ q = 3 := by
      have := Nat.le_of_dvd (by norm_num) hq6
      interval_cases q <;> simp_all <;> norm_num at hq
    rcases hq23 with rfl | rfl
    · rw [show 6 / 2 = 3 by norm_num, Ne, hρpow]
      exact not_mem_N_of_reprG (reprG_rhoPow 3) rho_three_chk
    · rw [show 6 / 3 = 2 by norm_num, Ne, hρpow]
      exact not_mem_N_of_reprG (reprG_rhoPow 2) rho_two_chk
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hk' : ρ ^ (k % 6).toNat = σ := by
      rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num)),
        show (6 : ℤ) = ((orderOf ρ : ℕ) : ℤ) by rw [hρo]; rfl, zpow_mod_orderOf]
    have hm6 : (k % 6).toNat < 6 := by omega
    rw [hρ, hσ, ← QuotientGroup.mk_pow, QuotientGroup.eq, hN', Subgroup.mem_subgroupOf] at hk'
    obtain ⟨i, hi, hiv⟩ := mem_N_iff.mp hk'
    have heq : genG 0 = (genG 4 * genG 2) ^ (k % 6).toNat * telG i := by
      have := congrArg (fun z => (genG 4 * genG 2) ^ (k % 6).toNat * z) hiv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, hr, ha] at this
      rw [← this]
      group
    exact sigma_not_chk _ hm6 i hi (repL_unique (reprG_mul (reprG_rhoPow _)
      (reprG_tel i (N_lt_chk i hi))) (heq ▸ reprG_gen 0 (by norm_num)))
  obtain ⟨eD⟩ := nonempty_dihedral_of_inverting hσ2 hrel hσρ
  rw [hρo] at eD
  have htop : Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hQ12]
  let e : ↥m12Data.B ⧸ N' ≃* DihedralGroup 6 :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans eD
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' N'), e.surjective.comp
    (QuotientGroup.mk'_surjective N'), ⟨?_⟩⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' N')).ker = N' := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (MulEquiv.subgroupCongr hker).trans ((Subgroup.subgroupOfEquivOfLe hNB).trans NEquiv)

theorem exists_conj {K₁ K₂ : Subgroup M12G} (hK₁ : IsMaximalTwoLocal K₁)
    (hK₂ : IsMaximalTwoLocal K₂) (hne : K₁ ≠ K₂) (hS : IsSylowTwoOf (K₁ ⊓ K₂) ⊤) :
    ∃ φ : M12G ≃* M12G, (K₁.map φ.toMonoidHom = m12Data.A ∧ K₂.map φ.toMonoidHom = m12Data.B) ∨
      (K₁.map φ.toMonoidHom = m12Data.B ∧ K₂.map φ.toMonoidHom = m12Data.A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp', hidx'⟩ := hS
  have e1 : ((K₁ ⊓ K₂).subgroupOf ⊤).index = (K₁ ⊓ K₂).index := Subgroup.relIndex_top_right _
  have hidx : ¬ 2 ∣ (K₁ ⊓ K₂).index := by rwa [e1] at hidx'
  let S : Sylow 2 M12G := m12_syl.1.toSylow m12_syl.2
  let S' : Sylow 2 M12G := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M12G S S'
  have hk' : MulAut.conj k • m12Data.T = K₁ ⊓ K₂ := by
    have h1 := congrArg (fun P : Sylow 2 M12G => (P : Subgroup M12G)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hTmap : K₁ ⊓ K₂ = m12Data.T.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : M12G ≃* M12G := (MulAut.conj k).symm
  have hTφ : (K₁ ⊓ K₂).map φ.toMonoidHom = m12Data.T := by
    rw [hTmap]
    exact map_map_symm_eq (MulAut.conj k) m12Data.T
  have hT₁ : m12Data.T ≤ K₁.map φ.toMonoidHom := hTφ ▸ Subgroup.map_mono inf_le_left
  have hT₂ : m12Data.T ≤ K₂.map φ.toMonoidHom := hTφ ▸ Subgroup.map_mono inf_le_right
  have hne' : K₁.map φ.toMonoidHom ≠ K₂.map φ.toMonoidHom :=
    fun h => hne (Subgroup.map_injective φ.injective h)
  refine ⟨φ, ?_⟩
  rcases m12Extra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hK₁) hT₁ with h₁ | h₁ <;>
    rcases m12Extra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hK₂) hT₂ with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne'
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (h₁.trans h₂.symm) hne'

end M12Shape

theorem mulEquiv_of_map_eq {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) {K : Subgroup G}
    {L : Subgroup H} (h : K.map ψ.toMonoidHom = L) : Nonempty (↥K ≃* ↥L) :=
  ⟨(K.equivMapOfInjective ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr h)⟩

theorem m12AmalgamShapeFact_holds : M12AmalgamShapeFact := by
  intro W _ _ K₁ K₂ hW hTL hQ₁ hQ₂ hC₁ h₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK₁, hK₂, hne, S, hS⟩ := hTL
  obtain ⟨ε⟩ := nonempty_mulEquiv_quasithinM12_of_isM12 hW
  have hS' : IsSylowTwoOf (K₁.map ε.toMonoidHom ⊓ K₂.map ε.toMonoidHom) ⊤ := by
    rw [← Subgroup.map_inf _ _ _ ε.injective, ← hS]
    exact isSylowTwoOf_top_map ε (isSylowTwoOf_top_of_sylow S)
  obtain ⟨φ, hφ⟩ := M12Shape.exists_conj (isMaximalTwoLocal_map ε hK₁)
    (isMaximalTwoLocal_map ε hK₂) (fun h => hne (Subgroup.map_injective ε.injective h)) hS'
  have hmap : ∀ K : Subgroup W,
      K.map (ε.trans φ).toMonoidHom = (K.map ε.toMonoidHom).map φ.toMonoidHom := fun K => by
    rw [Subgroup.map_map]
    rfl
  rcases hφ with ⟨hA, hB⟩ | ⟨hB, hA⟩
  ·
    obtain ⟨eK₂⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₂).trans hB)
    have hinf : (K₁ ⊓ K₂).map (ε.trans φ).toMonoidHom = m12Data.T := by
      rw [Subgroup.map_inf _ _ _ (ε.trans φ).injective, hmap, hmap, hA, hB, m12Data.inf_AB]
    obtain ⟨eT⟩ := mulEquiv_of_map_eq (ε.trans φ) hinf
    have hB192 : Nat.card ↥m12Data.B = 192 := by
      rw [← Nat.card_congr eK₂.toEquiv]
      obtain ⟨e₂⟩ := hQ₂
      have := CFSG.LieType.BorelTits.pCore_normal (G := ↥K₂) 2
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥K₂)
      have h3 : Nat.card ↥(Open.pCore 2 ↥K₂) = 2 ^ 5 := by
        rw [← h₂]
        exact Nat.card_congr ((Open.pCore 2 ↥K₂).equivMapOfInjective _
          K₂.subtype_injective).toEquiv
      rw [h1, Nat.card_congr e₂.toEquiv, h3, Nat.card_perm, Nat.card_fin]
      rfl
    exact ⟨IsExtensionOf.of_mulEquiv eT M12Shape.T_shape,
      IsExtensionOf.of_mulEquiv eK₂ (M12Shape.B_shape hB192)⟩
  ·
    exfalso
    obtain ⟨eK₁⟩ := mulEquiv_of_map_eq (ε.trans φ) ((hmap K₁).trans hB)
    exact false_of_isQ8Sq_pCoreOf_B (isQ8Sq_pCoreOf_of_mulEquiv K₁ m12Data.B eK₁
      (isQ8Sq_of_centralProduct₂ hC₁))

end F6

end CFSG.Quasithin
