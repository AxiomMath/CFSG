module

public import CFSG.Quasithin.Background.F6CatAutM12ShapeChk
public import CFSG.Quasithin.Background.F6CatShapeG22
public import CFSG.Quasithin.Recognition.M12AmalAutLFacts
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.M12AmalAut CFSG.Sporadic.Bridge

namespace F6

namespace AutShape

theorem B_le_normalizer_of_normOK {Q : Subgroup AutG} {L : List ℕ} (hlt : ∀ i ∈ L, i < 128)
    (hQ : ∀ g, g ∈ Q ↔ ∃ i ∈ L, g = telG i) (hN : NormOK L) :
    autData.B ≤ Subgroup.normalizer (Q : Set AutG) := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set AutG) ≤ _
  refine closure_le_normalizer_of_conj' _ _ ?_
  intro s hs k hk
  obtain ⟨j, hj, rfl⟩ := (hQ k).mp hk
  have hj128 := hlt j hj
  have key : ∀ g : ℕ, g ∈ [0, 1, 2, 4] → s = genG g →
      s * telG j * s⁻¹ ∈ Q ∧ s⁻¹ * telG j * s ∈ Q := by
    intro g hg hsg
    subst hsg
    obtain ⟨⟨k₁, hk₁, hl₁⟩, ⟨k₂, hk₂, hl₂⟩⟩ := hN g hg j hj
    have hg5 : g < 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      omega
    have r1 : ReprG (compL (compL (gl g) (tl j)) (gil g)) (genG g * telG j * (genG g)⁻¹) :=
      reprG_mul (reprG_mul (reprG_gen g hg5) (reprG_tel j hj128)) (reprG_inv_gen g hg5)
    have r2 : ReprG (compL (compL (gil g) (tl j)) (gl g)) ((genG g)⁻¹ * telG j * genG g) :=
      reprG_mul (reprG_mul (reprG_inv_gen g hg5) (reprG_tel j hj128)) (reprG_gen g hg5)
    exact ⟨(hQ _).mpr ⟨k₁, hk₁, eq_of_reprG r1 (by rw [hl₁]; exact reprG_tel k₁ (hlt k₁ hk₁))⟩,
      (hQ _).mpr ⟨k₂, hk₂, eq_of_reprG r2 (by rw [hl₂]; exact reprG_tel k₂ (hlt k₂ hk₂))⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h
  · exact key 0 (by simp) h
  · exact key 1 (by simp) h
  · exact key 2 (by simp) h
  · exact key 4 (by simp) h

theorem mem_pCore_of_mem_pCoreOf {H : Subgroup AutG} {b : ↥H} (hb : (b : AutG) ∈ pCoreOf 2 H) :
    b ∈ Open.pCore 2 ↥H := (CFSG.mem_openPCoreOf_iff_open b).mp hb

theorem shPowIdx_lt {i : ℕ} (hi : i < 128) (m : ℕ) : shPowIdx i m < 128 := by
  induction m with
  | zero => show 0 < 128; norm_num
  | succ m ih => exact (telMul_chk _ ih i hi).1

theorem telG_pow {i : ℕ} (hi : i < 128) (m : ℕ) : telG i ^ m = telG (shPowIdx i m) := by
  induction m with
  | zero => rw [pow_zero]; exact telG_zero_idx.symm
  | succ m ih => rw [pow_succ, ih, telG_mul (shPowIdx_lt hi m) hi]; rfl

@[expose] noncomputable def z4Hom : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* AutG where
  toFun g := telG (shZ4Idx g)
  map_one' := by rw [sh_z4_one_chk]; exact telG_zero_idx
  map_mul' g h := by
    rw [telG_mul (sh_N_lt_chk _ (sh_z4_mem_chk g)) (sh_N_lt_chk _ (sh_z4_mem_chk h)),
      sh_z4_mul_chk]

theorem z4Hom_injective : Function.Injective z4Hom := fun g h hgh =>
  sh_z4_inj_chk g h (telG_inj_idx (sh_N_lt_chk _ (sh_z4_mem_chk g))
    (sh_N_lt_chk _ (sh_z4_mem_chk h)) hgh)

@[expose] noncomputable def Nsub : Subgroup AutG := z4Hom.range

theorem mem_Nsub_iff {g : AutG} : g ∈ Nsub ↔ ∃ i ∈ shNIdx, g = telG i := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨_, sh_z4_mem_chk h, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨h, hh⟩ := sh_z4_surj_chk i hi
    exact ⟨h, by rw [← hh]; rfl⟩

theorem telG_mem_Nsub_iff {i : ℕ} (hi : i < 128) : telG i ∈ Nsub ↔ i ∈ shNIdx := by
  rw [mem_Nsub_iff]
  constructor
  · rintro ⟨k, hk, he⟩
    rw [telG_inj_idx hi (sh_N_lt_chk k hk) he]
    exact hk
  · exact fun h => ⟨i, h, rfl⟩

noncomputable def NsubEquiv : ↥Nsub ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (MonoidHom.ofInjective z4Hom_injective).symm

theorem card_Nsub : Nat.card ↥Nsub = 16 := by
  rw [Nat.card_congr NsubEquiv.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem Nsub_le_T : Nsub ≤ autData.T := fun g hg => by
  obtain ⟨i, hi, rfl⟩ := mem_Nsub_iff.mp hg
  exact telG_mem_T (sh_N_lt_chk i hi)

theorem B_le_normalizer_Nsub : autData.B ≤ Subgroup.normalizer (Nsub : Set AutG) :=
  B_le_normalizer_of_normOK sh_N_lt_chk (fun _ => mem_Nsub_iff) sh_N_norm_chk

theorem Nsub_le_pCoreOf : Nsub ≤ pCoreOf 2 autData.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Nsub_le_T.trans autData.T_le_B)
    B_le_normalizer_Nsub (isPGroup_T.to_le Nsub_le_T)

@[expose] noncomputable def Rsub' : Subgroup AutG :=
  idxSubgroup shRIdx sh_R_chk.1 sh_R_chk.2.1 sh_R_chk.2.2.1 sh_R_chk.2.2.2

theorem Rsub'_le_T : Rsub' ≤ autData.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact telG_mem_T (sh_R_chk.2.1 i hi)

theorem R_le_pCoreOf : Rsub' ≤ pCoreOf 2 autData.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Rsub'_le_T.trans autData.T_le_B)
    (B_le_normalizer_of_normOK sh_R_chk.2.1 (fun _ => Iff.rfl) sh_R_norm_chk)
    (isPGroup_T.to_le Rsub'_le_T)

theorem T_shape : IsExtensionOf ↥autData.T (DihedralGroup 4)
    (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have b1 : (1 : ℕ) < 128 := by norm_num
  have b2 : (2 : ℕ) < 128 := by norm_num
  have hσ2 : telG 1 * telG 1 ∈ Nsub := by
    rw [telG_mul b1 b1, telG_mem_Nsub_iff (telMul_chk 1 b1 1 b1).1]
    exact sh_sigma_sq_chk
  have hrel : telG 1 * telG 2 * (telG 1)⁻¹ * telG 2 ∈ Nsub := by
    have b12 := (telMul_chk 1 b1 2 b2).1
    have bi := (telInv_chk 1 b1).1
    have b3 := (telMul_chk _ b12 _ bi).1
    have b4 := (telMul_chk _ b3 2 b2).1
    rw [telG_inv b1, telG_mul b1 b2, telG_mul b12 bi, telG_mul b3 b2, telG_mem_Nsub_iff b4]
    exact sh_sigma_rho_chk
  have h4 : telG 2 ^ 4 ∈ Nsub := by
    rw [telG_pow b2, telG_mem_Nsub_iff (shPowIdx_lt b2 4)]
    exact sh_rho_four_chk
  have hord : ∀ q, q.Prime → q ∣ 4 → telG 2 ^ (4 / q) ∉ Nsub := fun q hq hq4 => by
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow (show q ∣ 2 ^ 2 from hq4))
    subst hq2
    rw [show 4 / 2 = 2 by norm_num, telG_pow b2, telG_mem_Nsub_iff (shPowIdx_lt b2 2)]
    exact sh_rho_two_chk
  have hnot : ∀ m < 4, ∀ x ∈ Nsub, telG 1 ≠ telG 2 ^ m * x := by
    intro m hm x hx hax
    obtain ⟨k, hk, rfl⟩ := mem_Nsub_iff.mp hx
    have hk128 := sh_N_lt_chk k hk
    rw [telG_pow b2, telG_mul (shPowIdx_lt b2 m) hk128] at hax
    exact sh_sigma_not_chk m hm k hk
      (telG_inj_idx (telMul_chk _ (shPowIdx_lt b2 m) k hk128).1 b1 hax.symm)
  obtain ⟨φ, hφ, ⟨eN⟩⟩ := isExtensionOf_dihedral_of (n := 4) (by norm_num) Nsub_le_T
    (autData.T_le_B.trans B_le_normalizer_Nsub) (by rw [aut_card_T, card_Nsub])
    (telG_mem_T b2) (telG_mem_T b1) hσ2 hrel h4 hord hnot
  exact ⟨φ, hφ, ⟨eN.trans NsubEquiv⟩⟩

@[expose] noncomputable def chiE
    (g : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) : AutG :=
  genG 4 ^ g.1.toAdd.val * telG (shVWIdx g.2)

theorem reprG_yPow (m : ℕ) : ReprG (shYPowL m) (genG 4 ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact reprG_one
  | succ m ih => rw [pow_succ]; exact reprG_mul ih (reprG_gen 4 (by norm_num))

theorem shVW_lt (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : shVWIdx g < 128 :=
  sh_R_chk.2.1 _ (sh_VW_chk g)

theorem reprG_chiE
    (g : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ReprG (shChiL g) (chiE g) :=
  reprG_mul (reprG_yPow _) (reprG_tel _ (shVW_lt g.2))

theorem genG_four_mem_B : genG 4 ∈ autData.B := genG_mem_B (by simp)

theorem chiE_mem_B
    (g : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    chiE g ∈ autData.B :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ genG_four_mem_B _)
    (autData.T_le_B (telG_mem_T (shVW_lt g.2)))

theorem B_shape (hB : Nat.card ↥autData.B = 384) (hQ : QuotientPCoreIsL22 autData.B) :
    IsExtensionOf₃ ↥autData.B (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  obtain ⟨e⟩ := hQ
  have hNB : Nsub ≤ autData.B := Nsub_le_T.trans autData.T_le_B
  have : (Nsub.subgroupOf autData.B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNB).mpr B_le_normalizer_Nsub
  set N' := Nsub.subgroupOf autData.B with hN'
  refine ⟨N', inferInstance, ⟨(Subgroup.subgroupOfEquivOfLe hNB).trans NsubEquiv⟩, ?_⟩
  let σ₂ : ℤˣ ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) (by rw [Nat.card_eq_fintype_card]; rfl)
      (by rw [Nat.card_eq_fintype_card]; rfl)
  let φ : ↥autData.B →* Multiplicative (ZMod 2) :=
    σ₂.toMonoidHom.comp (Equiv.Perm.sign.comp (e.toMonoidHom.comp (QuotientGroup.mk' _)))
  have hφ1 : ∀ b : ↥autData.B, (b : AutG) ∈ pCoreOf 2 autData.B → φ b = 1 := by
    intro b hb
    have h1 : QuotientGroup.mk' (Open.pCore 2 ↥autData.B) b = 1 :=
      (QuotientGroup.eq_one_iff b).mpr (mem_pCore_of_mem_pCoreOf hb)
    simp only [φ, MonoidHom.comp_apply, h1, map_one]
  have hNφ : N' ≤ φ.ker := fun b hb =>
    hφ1 b (Nsub_le_pCoreOf (Subgroup.mem_subgroupOf.mp hb))
  have hφsurj : Function.Surjective φ :=
    σ₂.surjective.comp ((Equiv.Perm.sign_surjective (α := Fin 3)).comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _)))
  let φ' : ↥autData.B ⧸ N' →* Multiplicative (ZMod 2) := QuotientGroup.lift N' φ hNφ
  have hφ'surj : Function.Surjective φ' := fun z => by
    obtain ⟨b, rfl⟩ := hφsurj z
    exact ⟨QuotientGroup.mk b, QuotientGroup.lift_mk _ _ _⟩
  have hN'card : Nat.card ↥N' = 16 := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv, card_Nsub]
  have hcard24 : Nat.card (↥autData.B ⧸ N') = 24 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [hB, hN'card] at h1
    omega
  have hker12 : Nat.card ↥φ'.ker = 12 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ'.ker
    rw [hcard24, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ' hφ'surj).toEquiv,
      Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))] at h1
    change 24 = 2 * Nat.card ↥φ'.ker at h1
    omega
  let χ : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →*
      ↥autData.B ⧸ N' :=
    { toFun := fun g => QuotientGroup.mk ⟨chiE g, chiE_mem_B g⟩
      map_one' := by
        have h1 : chiE 1 = 1 := by
          have r := reprG_chiE 1
          rw [sh_chi_one_chk] at r
          exact eq_of_reprG r reprG_one
        have h2 : (⟨chiE 1, chiE_mem_B 1⟩ : ↥autData.B) = 1 := Subtype.ext h1
        simp only [h2, QuotientGroup.mk_one]
      map_mul' := fun g h => by
        obtain ⟨k, hk, hkl⟩ := sh_chi_mul_chk g h
        have r : ReprG (compL (shChiL (g * h)) (tl k)) (chiE (g * h) * telG k) :=
          reprG_mul (reprG_chiE (g * h)) (reprG_tel k (sh_N_lt_chk k hk))
        rw [hkl] at r
        have heq : chiE g * chiE h = chiE (g * h) * telG k :=
          eq_of_reprG (reprG_mul (reprG_chiE g) (reprG_chiE h)) r
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [heq, ← mul_assoc, inv_mul_cancel, one_mul]
        exact mem_Nsub_iff.mpr ⟨k, hk, rfl⟩ }
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : chiE g ∈ Nsub := by
      have := (QuotientGroup.eq_one_iff _).mp hg
      rwa [hN', Subgroup.mem_subgroupOf] at this
    obtain ⟨k, hk, hke⟩ := mem_Nsub_iff.mp h1
    have r := reprG_chiE g
    rw [hke] at r
    exact sh_chi_inj_chk g ⟨k, hk, repL_unique r (reprG_tel k (sh_N_lt_chk k hk))⟩
  have hφy : φ ⟨genG 4, genG_four_mem_B⟩ = 1 := by
    have h3 : (⟨genG 4, genG_four_mem_B⟩ : ↥autData.B) ^ 3 = 1 := by
      apply Subtype.ext
      have r := reprG_yPow 3
      rw [sh_y_cube_chk] at r
      exact eq_of_reprG r reprG_one
    have h2 : ∀ z : Multiplicative (ZMod 2), z ^ 3 = 1 → z = 1 := by decide
    have h3' := congrArg φ h3
    rw [map_pow, map_one] at h3'
    exact h2 _ h3'
  have hrange : χ.range ≤ φ'.ker := by
    rintro _ ⟨g, rfl⟩
    rw [MonoidHom.mem_ker]
    have ht : telG (shVWIdx g.2) ∈ autData.B := autData.T_le_B (telG_mem_T (shVW_lt g.2))
    have hsplit : (⟨chiE g, chiE_mem_B g⟩ : ↥autData.B) =
        ⟨genG 4, genG_four_mem_B⟩ ^ g.1.toAdd.val * ⟨_, ht⟩ := Subtype.ext rfl
    have htR : φ ⟨_, ht⟩ = 1 := hφ1 _ (R_le_pCoreOf ⟨shVWIdx g.2, sh_VW_chk g.2, rfl⟩)
    change φ' (QuotientGroup.mk _) = 1
    rw [QuotientGroup.lift_mk, hsplit, map_mul, map_pow, hφy, one_pow, htR, one_mul]
  have hcardχ : Nat.card ↥χ.range = 12 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv, Nat.card_eq_fintype_card]
    rfl
  have heq : χ.range = φ'.ker :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hker12, hcardχ])
  exact ⟨φ', hφ'surj, ⟨(MulEquiv.subgroupCongr heq).symm.trans
    (MonoidHom.ofInjective hχinj).symm⟩⟩

theorem exists_conj {K₁ K₂ : Subgroup AutG} (hK₁ : IsMaximalTwoLocal K₁)
    (hK₂ : IsMaximalTwoLocal K₂) (hne : K₁ ≠ K₂) (hS : IsSylowTwoOf (K₁ ⊓ K₂) ⊤) :
    ∃ φ : AutG ≃* AutG, (K₁.map φ.toMonoidHom = autData.A ∧ K₂.map φ.toMonoidHom = autData.B) ∨
      (K₁.map φ.toMonoidHom = autData.B ∧ K₂.map φ.toMonoidHom = autData.A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp', hidx'⟩ := hS
  have e1 : ((K₁ ⊓ K₂).subgroupOf ⊤).index = (K₁ ⊓ K₂).index := Subgroup.relIndex_top_right _
  have hidx : ¬ 2 ∣ (K₁ ⊓ K₂).index := by rwa [e1] at hidx'
  let S : Sylow 2 AutG := aut_syl.1.toSylow aut_syl.2
  let S' : Sylow 2 AutG := hp'.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq AutG S S'
  have hg' : MulAut.conj g • autData.T = K₁ ⊓ K₂ := by
    have h1 := congrArg (fun P : Sylow 2 AutG => (P : Subgroup AutG)) hg
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hTmap : K₁ ⊓ K₂ = autData.T.map (MulAut.conj g).toMonoidHom := by
    rw [← hg']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : AutG ≃* AutG := (MulAut.conj g).symm
  have hTφ : (K₁ ⊓ K₂).map φ.toMonoidHom = autData.T := by
    rw [hTmap]
    exact map_map_symm_eq (MulAut.conj g) autData.T
  have hT₁ : autData.T ≤ K₁.map φ.toMonoidHom := hTφ ▸ Subgroup.map_mono inf_le_left
  have hT₂ : autData.T ≤ K₂.map φ.toMonoidHom := hTφ ▸ Subgroup.map_mono inf_le_right
  have hne' : K₁.map φ.toMonoidHom ≠ K₂.map φ.toMonoidHom :=
    fun h => hne (Subgroup.map_injective φ.injective h)
  refine ⟨φ, ?_⟩
  rcases autExtra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hK₁) hT₁ with h₁ | h₁ <;>
    rcases autExtra.eq_A_or_B_of_maxTwoLocal (isMaximalTwoLocal_map φ hK₂) hT₂ with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne'
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (h₁.trans h₂.symm) hne'

end AutShape

end F6

end CFSG.Quasithin
