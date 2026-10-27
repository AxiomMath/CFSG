module

public import CFSG.Quasithin.Vol2.Ch12Sec5E49Q
public import CFSG.Quasithin.Vol2.Ch12Sec5Hat7
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMap
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableW
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32S
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma37
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.InternalSecRealB
public import CFSG.Quasithin.EmptyFaithful.Der6EMain
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152FinCore
public import CFSG.Quasithin.EmptyFaithful.S152He8Aut
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5Sit15d
public import CFSG.Quasithin.H13.A6S1372L19c
public import CFSG.Quasithin.H13.A6S1372L74a
public import CFSG.Quasithin.H13.A6S1372L74d
public import CFSG.Quasithin.H13.A6S1372L74f
public import CFSG.Quasithin.H13.A6S1372L76Of3
public import CFSG.Quasithin.H13.A6S1372L76V
public import CFSG.Quasithin.H13.A6S13827a
public import CFSG.Quasithin.H13.A6S138Ia
public import CFSG.Quasithin.H13.A7Nat1238QTabA7
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34Out
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Act
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lie
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.Sporadic.J4.QT2LocProof
public import Certificates.Kernel.J4Count.Prim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125
open scoped commutatorElement

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125E49

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

section Rho

variable {K₁ L₁ : Subgroup G}

@[expose] noncomputable def rho (hLK : L₁ ≤ K₁) : ↥L₁ →* ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)).comp (Subgroup.inclusion hLK)

omit [Finite G] in
theorem rho_apply (hLK : L₁ ≤ K₁) (l : ↥L₁) :
    rho hLK l = QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) (Subgroup.inclusion hLK l) := rfl

theorem ker_rho_le (hLK : L₁ ≤ K₁) : (rho hLK).ker ≤ CFSG.pCore 2 ↥L₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro l hl
  rw [← A6.A6L74.mem_pCoreOf_iff]
  have hlO : (l : G) ∈ pCoreOf 2 K₁ := by
    rw [MonoidHom.mem_ker, rho_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← A6.A6L74.mem_pCoreOf_iff] at hl
    exact hl
  have hle : L₁ ⊓ pCoreOf 2 K₁ ≤ pCoreOf 2 L₁ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => ?_) ?_
    · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₁ (hLK hx)⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁).to_le inf_le_right
  exact hle ⟨l.2, hlO⟩

theorem card_quot_le (hLK : L₁ ≤ K₁) :
    Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ≤ Nat.card (rho hLK).range := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (rho hLK)).toEquiv]
  show (CFSG.pCore 2 ↥L₁).index ≤ (rho hLK).ker.index
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le (ker_rho_le hLK))

theorem eq_bot_of_isPGroup_seven (hLK : L₁ ≤ K₁)
    (eL : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {N : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)} (hNA : N ≤ (rho hLK).range)
    (hNn : ∀ n ∈ N, ∀ a ∈ (rho hLK).range, a * n * a⁻¹ ∈ N) (h7 : IsPGroup 7 ↥N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set ρ := rho hLK with hρ
  set Ñ := N.comap ρ with hÑ
  have hÑn : Ñ.Normal := ⟨fun x hx g => by
    show ρ (g * x * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn _ hx _ ⟨g, rfl⟩⟩
  set π₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) with hπ₂
  have hs : IsSimpleGroup (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := by
    have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
    exact eL.isSimpleGroup
  have hMn : (Ñ.map π₂).Normal := hÑn.map π₂ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hMn with hb | ht
  ·
    have hÑ2 : Ñ ≤ CFSG.pCore 2 ↥L₁ := by
      intro x hx
      have : π₂ x ∈ Ñ.map π₂ := ⟨x, hx, rfl⟩
      rw [hb, Subgroup.mem_bot, hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hN2 : IsPGroup 2 ↥N := by
      intro n
      obtain ⟨l, hl⟩ := hNA n.2
      have hlÑ : l ∈ Ñ := by
        show ρ l ∈ N
        rw [hl]
        exact n.2
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L₁)) ⟨l, hÑ2 hlÑ⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : l ^ 2 ^ k = 1 := congrArg Subtype.val hk
      show (n : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ^ 2 ^ k = 1
      rw [← hl, ← map_pow, hk', map_one]
    exact disjoint_self.1 (IsPGroup.disjoint_of_ne 2 7 (by norm_num) N N hN2 h7)
  ·
    exfalso
    have h7L : IsPGroup 7 (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := by
      intro y
      obtain ⟨x, hx, rfl⟩ : y ∈ Ñ.map π₂ := ht ▸ Subgroup.mem_top y
      obtain ⟨k, hk⟩ := h7 ⟨ρ x, hx⟩
      refine ⟨k, ?_⟩
      have h1 : x ^ 7 ^ k ∈ ρ.ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact congrArg Subtype.val hk
      rw [← map_pow, hπ₂, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ker_rho_le hLK h1
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (h7L.of_surjective eL.toMonoidHom eL.surjective)
    rw [card_sl_three_zmod_two] at hn
    have hn3 : n < 3 := by
      by_contra h
      have : 7 ^ 3 ≤ 7 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> norm_num at hn

omit [Finite G] in
theorem quot_perfect (hK : ⁅K₁, K₁⁆ = K₁) :
    ⁅(⊤ : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)), (⊤ : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))⁆ = ⊤ := by
  have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr hK
  exact Group.IsPerfect.commutator_eq_top

theorem e49_facts (hK : ⁅K₁, K₁⁆ = K₁) (hLK : L₁ ≤ K₁)
    (eL : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hE : IsSL27OverE49 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    ∃ E : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁), E.Normal ∧ (∀ e ∈ E, e ^ 7 = 1) ∧
      Subgroup.centralizer (E : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) = E ∧
      (rho hLK).range ⊓ E = ⊥ ∧ (rho hLK).range ⊔ E = ⊤ ∧
      ∃ z ∈ (rho hLK).range, z ≠ 1 ∧ (∀ a ∈ (rho hLK).range, a * z = z * a) ∧
        (∀ e ∈ E, z * e * z⁻¹ = e⁻¹) ∧
        ∀ w ∈ (rho hLK).range, w * w = 1 → w ≠ 1 → w = z := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨E, hE7, hEc, hcent, hEn, ⟨f⟩⟩ := hE
  have hQp := quot_perfect hK
  have hAE : (rho hLK).range ⊓ E = ⊥ := by
    refine eq_bot_of_isPGroup_seven hLK eL inf_le_left
      (fun n hn a ha => ⟨(rho hLK).range.mul_mem ((rho hLK).range.mul_mem ha hn.1)
        ((rho hLK).range.inv_mem ha), hEn.conj_mem _ hn.2 a⟩) ?_
    intro n
    exact ⟨1, Subtype.ext (by rw [pow_one]; exact hE7.2 _ n.2.2)⟩
  have hQE : Nat.card ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ⧸ E) = 336 := by
    rw [Nat.card_congr f.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num),
      Nat.card_zmod]
    decide
  have hA : Nat.card ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ⧸ E) ≤ 2 * Nat.card (rho hLK).range := by
    have h1 := card_quot_le hLK
    rw [Nat.card_congr eL.toEquiv, card_sl_three_zmod_two] at h1
    omega
  have hAQ := sup_eq_top_of_card hAE hA hQp
  obtain ⟨z, hzA, hz1, -, hzc, hzi, huniq⟩ :=
    exists_central_involution hE7 hEc hcent f hAE hAQ hQp
  exact ⟨E, hEn, hE7.2, hcent, hAE, hAQ, z, hzA, hz1, hzc, hzi, huniq⟩

theorem map_inf_eq_bot (hLK : L₁ ≤ K₁)
    (eL : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {E : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)} (hEn : E.Normal) (h7 : ∀ e ∈ E, e ^ 7 = 1)
    (α : MulAut (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    (rho hLK).range.map α.toMonoidHom ⊓ E = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hN : (rho hLK).range ⊓ E.comap α.toMonoidHom = ⊥ := by
    refine eq_bot_of_isPGroup_seven hLK eL inf_le_left (fun n hn a ha => ⟨?_, ?_⟩) ?_
    · exact (rho hLK).range.mul_mem ((rho hLK).range.mul_mem ha hn.1) ((rho hLK).range.inv_mem ha)
    · show α (a * n * a⁻¹) ∈ E
      rw [map_mul, map_mul, map_inv]
      exact hEn.conj_mem _ hn.2 _
    · intro n
      refine ⟨1, Subtype.ext ?_⟩
      have h1 : α ((n : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ^ 7) = 1 := by
        rw [map_pow]
        exact h7 _ n.2.2
      rw [pow_one]
      exact (MulEquiv.map_eq_one_iff α).1 h1
  rw [eq_bot_iff]
  rintro x ⟨⟨a, ha, rfl⟩, hxE⟩
  have : a ∈ (rho hLK).range ⊓ E.comap α.toMonoidHom := ⟨ha, hxE⟩
  rw [hN, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot, this, map_one]

end Rho

section Y

theorem transvection_mul_self₂ : ∀ i j : Fin 5, i ≠ j →
    Matrix.transvection i j (1 : ZMod 2) * Matrix.transvection i j 1 = 1 := by
  decide +kernel

theorem transvection_comm₂₃₄ :
    Matrix.transvection (2 : Fin 5) (3 : Fin 5) (1 : ZMod 2) * Matrix.transvection (3 : Fin 5) 4 1 *
        Matrix.transvection (2 : Fin 5) 3 1 * Matrix.transvection (3 : Fin 5) 4 1 =
      Matrix.transvection (2 : Fin 5) (4 : Fin 5) 1 := by
  decide +kernel

theorem tv_comm₂₃₄ : S125Gen.tv 2 3 (by decide) * S125Gen.tv 3 4 (by decide) *
    S125Gen.tv 2 3 (by decide) * S125Gen.tv 3 4 (by decide) = S125Gen.tv 2 4 (by decide) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact transvection_comm₂₃₄

theorem tv_inv {i j : Fin 5} (h : i ≠ j) : (S125Gen.tv i j h)⁻¹ = S125Gen.tv i j h :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (transvection_mul_self₂ i j h))

theorem stabGam_tv {i j : Fin 5} (h : i ≠ j) {k : ℕ} (hk : ¬ (j.val < k ∧ k ≤ i.val)) :
    StabGam k (S125Gen.tv i j h) := by
  intro a b hb ha
  change Matrix.transvection i j (1 : ZMod 2) a b = 0
  rw [S125Gen.transvection_apply, Matrix.one_apply_ne (fun h' => by rw [h'] at ha; omega),
    zero_add, ite_eq_right (fun h' => (hk ⟨by rw [h'.2]; exact hb, by rw [h'.1]; exact ha⟩).elim)]

theorem not_mem_uniRad :
    (CFSG.LieType.SteinbergBR.BlockPar.reindexSL (ZMod 2) (by norm_num : 2 + 3 = 5)).symm
      (S125Gen.tv 2 4 (by decide)) ∉ S125Pb.uniRad (Fin 2) (Fin 3) := by
  intro h
  have h22 := (S125Pb.mem_uniRad.1 h).2.2
  have := congrFun₂ h22 0 2
  rw [Matrix.toBlocks₂₂, Matrix.of_apply, S125Gen.symm_val_apply, S125Gen.sumEquiv_inr_val,
    S125Gen.sumEquiv_inr_val] at this
  revert this
  decide +kernel

theorem phi_mem_uniRad (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    {x : ↥(L ⊔ T)} (hx : (x : G) ∈ pCoreOf 2 (li L F.V1)) :
    (CFSG.LieType.SteinbergBR.BlockPar.reindexSL (ZMod 2) (by norm_num : 2 + 3 = 5)).symm
      (S125Pm.phi F hLV hTV x) ∈ S125Pb.uniRad (Fin 2) (Fin 3) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hRL := S125Tr2.rbar_inf_lbar F hH hf (S := {0}) (by norm_num : 2 + 3 = 5)
    (S125St.isStab_V1 F hf.normalizes hf.T_le) (S125L2G.T_le_V F hf.T_le).1
    (S125L2G.hres_of CFSG.LieType.SteinbergBR.BlockPar.parJR_le_parQ
      S125Pb.perfectResidual_parQ23) S125Pb.uniRad_le_parJR
    (fun N hN hn hp => S125Pb.le_uniRad_of_parJR (S125Pb.noO2_GL 3 S125Pb.noO2_SL3) hN hn hp)
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  have hOY : pCoreOf 2 (li L F.V1) ≤ ri T L F.V1 :=
    E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left (sup_le Subgroup.le_normalizer hTL₁)
  have hxL₁ : (x : G) ∈ li L F.V1 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
  have hxN : (x : G) ∈ Subgroup.normalizer (V : Set G) := (sup_le hLV hTV) x.2
  have hact : S125Tr2.psi F (S125Pm.phi F hLV hTV x) ∈
      autOn (ri T L (F.sub {0})) V ⊓ autOn (li L (F.sub {0})) V := by
    rw [S125Pm.psi_phi]
    exact ⟨mem_autOn_iff_exists.mpr ⟨x, hxN, hOY hx, rfl⟩,
      mem_autOn_iff_exists.mpr ⟨x, hxN, hxL₁, rfl⟩⟩
  rw [hRL] at hact
  obtain ⟨u, hu, hue⟩ := hact
  have hu' : CFSG.LieType.SteinbergBR.BlockPar.reindexSL (ZMod 2) (by norm_num : 2 + 3 = 5) u =
      S125Pm.phi F hLV hTV x := S125Tr2.psi_injective F hue
  rw [← hu', MulEquiv.symm_apply_apply]
  exact hu

theorem exists_mem_inf (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    ∃ y : ↥(L ⊔ T), (y : G) ∈ li L F.V1 ∧ (y : G) ∈ li L F.V6 ∧
      S125Pm.phi F hLV hTV y = S125Gen.tv 2 4 (by decide) := by
  obtain ⟨-, h1⟩ := S125Pm.phi_li_iff h1222 F hH (S125L8.autOn_l1 h1222 F hH)
  obtain ⟨g, hgL, hg⟩ := h1 _ (S125Gen.tv_mem_pR (show (2 : Fin 5) ≠ 3 by decide) (by decide))
  obtain ⟨-, h6⟩ := S125Pm.phi_li_iff h1222 F hH (S125L4.autOn_l6 h1222 F hH)
  obtain ⟨r, hrL, hr⟩ := h6 _ (S125Gen.tv_mem_pL41 (show (3 : Fin 5) ≠ 4 by decide) (by decide))
  have hgV₆ : (g : G) ∈ Subgroup.normalizer (F.V6 : Set G) := by
    show (g : G) ∈ Subgroup.normalizer (F.sub {0, 1, 2, 4, 5, 7} : Set G)
    rw [S125Pm.mem_normalizer_sub_iff F hLV hTV, show S125Pm.phi F hLV hTV g = _ from hg,
      S125W.coordFix_V6_iff]
    exact stabGam_tv _ (by decide)
  have hrV₁ : (r : G) ∈ Subgroup.normalizer (F.V1 : Set G) := by
    show (r : G) ∈ Subgroup.normalizer (F.sub {0} : Set G)
    rw [S125Pm.mem_normalizer_sub_iff F hLV hTV, show S125Pm.phi F hLV hTV r = _ from hr,
      S125W.coordFix_V1_iff]
    exact stabGam_tv _ (by decide)
  have hgN : (g : G) ∈ Subgroup.normalizer (li L F.V6 : Set G) :=
    S125K6.le_normalizer_li ((Subgroup.zpowers_le).2 (Subgroup.le_normalizer
      (S125K6.li_le L _ hgL))) ((Subgroup.zpowers_le).2 hgV₆) (Subgroup.mem_zpowers _)
  have hrN : (r : G) ∈ Subgroup.normalizer (li L F.V1 : Set G) :=
    S125K6.le_normalizer_li ((Subgroup.zpowers_le).2 (Subgroup.le_normalizer
      (S125K6.li_le L _ hrL))) ((Subgroup.zpowers_le).2 hrV₁) (Subgroup.mem_zpowers _)
  refine ⟨g * r * g⁻¹ * r⁻¹, ?_, ?_, ?_⟩
  · have h2 : (r : G) * (g : G)⁻¹ * (r : G)⁻¹ ∈ li L F.V1 :=
      (Subgroup.mem_normalizer_iff.mp hrN _).mp ((li L F.V1).inv_mem hgL)
    have e : ((g * r * g⁻¹ * r⁻¹ : ↥(L ⊔ T)) : G) =
        (g : G) * ((r : G) * (g : G)⁻¹ * (r : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (li L F.V1).mul_mem hgL h2
  · have h2 : (g : G) * (r : G) * (g : G)⁻¹ ∈ li L F.V6 :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mp hrL
    have e : ((g * r * g⁻¹ * r⁻¹ : ↥(L ⊔ T)) : G) =
        ((g : G) * (r : G) * (g : G)⁻¹) * (r : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact (li L F.V6).mul_mem h2 ((li L F.V6).inv_mem hrL)
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, hr, tv_inv, tv_inv]
    exact tv_comm₂₃₄

theorem exists_rho_eq (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G} (hLK : li L F.V1 ≤ K₁) {z : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁}
    (huniq : ∀ w ∈ (rho hLK).range, w * w = 1 → w ≠ 1 → w = z) :
    ∃ y : G, ∃ hy : y ∈ li L F.V1, y ∈ li L F.V6 ∧ rho hLK ⟨y, hy⟩ = z := by
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨y, hy1, hy6, hφy⟩ := exists_mem_inf h1222 F hH hf.normalizes hf.T_le
  set yL : ↥(li L F.V1) := ⟨y, hy1⟩ with hyL
  set n := orderOf (rho hLK yL) with hn
  have hn0 : 0 < n := orderOf_pos _
  have hev : Even n := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have h1 : yL ^ n ∈ (rho hLK).ker := by
      rw [MonoidHom.mem_ker, map_pow, hn, pow_orderOf_eq_one]
    have h2 : ((yL ^ n : ↥(li L F.V1)) : G) ∈ pCoreOf 2 (li L F.V1) :=
      (A6.A6L74.mem_pCoreOf_iff _).2 (ker_rho_le hLK h1)
    have h3 : (((y ^ n : ↥(L ⊔ T)) : G)) ∈ pCoreOf 2 (li L F.V1) := by
      simpa [hyL] using h2
    have h4 := phi_mem_uniRad h1222 F hH hf.normalizes hf.T_le h3
    obtain ⟨k, hk⟩ := hodd
    have hsq : S125Gen.tv 2 4 (by decide) * S125Gen.tv 2 4 (by decide) = 1 :=
      Subtype.ext (transvection_mul_self₂ 2 4 (by decide))
    have h5 : S125Pm.phi F hf.normalizes hf.T_le (y ^ n) = S125Gen.tv 2 4 (by decide) := by
      rw [map_pow, hφy, hk, pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
    rw [h5] at h4
    exact not_mem_uniRad h4
  obtain ⟨m, hm⟩ := hev
  have hm0 : 0 < m := by omega
  refine ⟨((yL ^ m : ↥(li L F.V1)) : G), (yL ^ m).2, ?_, ?_⟩
  · have : ((yL ^ m : ↥(li L F.V1)) : G) = y ^ m := by simp [hyL]
    rw [this]
    exact (li L F.V6).pow_mem hy6 m
  · refine huniq _ ⟨yL ^ m, rfl⟩ ?_ ?_
    · rw [← map_mul, ← pow_add, map_pow, ← hm, hn, pow_orderOf_eq_one]
    · rw [map_pow]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega)

end Y

section Alpha

omit [Finite G] in
theorem autQ_mk (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    S125Hat7.autQ K hg (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) (S125Hat7.conjK K hg k) := rfl

theorem centralizer_V6_le_of_e49
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G} (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (hE : IsSL27OverE49 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  obtain ⟨E, hEn, h7, -, hAE, hAQ, z, -, -, hzc, hzi, huniq⟩ := e49_facts hK.2.1 hLK eL hE
  obtain ⟨y, hy1, hy6, hyz⟩ := exists_rho_eq h1222 F hH hLK huniq
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hV₁V₆ : F.V1 ≤ F.V6 := S125L5a.sub_mono_le F (by decide)
  have hCG₁ : Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (F.V1 : Set G) :=
    (Subgroup.centralizer_le hV₁V₆).trans (Subgroup.centralizer_le_normalizer _)
  set L₆ := li L F.V6 with hL₆
  obtain ⟨-, hG₆N⟩ := S125K6.l6_cComp h1222 h36 h37 h38 h39 h312 F hH
  have hTL₆ := S125K6.T_le_normalizer_l6 h1222 F hH
  have hO₆T : pCoreOf 2 L₆ ≤ T := by
    have hS : QuasithinUnique.IsSylowTwoOf T (L₆ ⊔ T) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
    exact (E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left (sup_le Subgroup.le_normalizer hTL₆)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hS)
  have hcomm : ∀ c ∈ Subgroup.centralizer (F.V6 : Set G), c * y * c⁻¹ * y⁻¹ ∈ T := by
    intro c hc
    have hcL₆ := hG₆N (Subgroup.centralizer_le_normalizer _ hc)
    refine hO₆T (S125Cfg.inf_centralizer_V6_le h1222 F hH ⟨?_, ?_⟩)
    · exact L₆.mul_mem ((Subgroup.mem_normalizer_iff.mp hcL₆ y).mp hy6) (L₆.inv_mem hy6)
    · have hyN := S125K6.li_le_normalizer L F.V6 hy6
      have hci : y * c⁻¹ * y⁻¹ ∈ Subgroup.centralizer (F.V6 : Set G) :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.Quasithin.normalizer_le_normalizer_centralizer F.V6 hyN) c⁻¹).mp
          (Subgroup.inv_mem _ hc)
      have e : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hc hci
  refine S125L4.le_normalizer_L h1222 F hH (S125K6.li_le L F.V6) hTL₆
    (S125L4.autOn_sup_l6 h1222 F hH) (fun c hc b hb => ?_) (fun c hc => ?_)
  · have hbW := S125K6.li_le_normalizer L F.V6 hb
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have hw' : b * w * b⁻¹ ∈ F.V6 := (Subgroup.mem_normalizer_iff.mp hbW w).mp hw
    have h1 := hc _ hw'
    calc w * (b⁻¹ * c * b) = b⁻¹ * ((b * w * b⁻¹) * c) * b := by group
      _ = b⁻¹ * (c * (b * w * b⁻¹)) * b := by rw [h1]
      _ = b⁻¹ * c * b * w := by group
  ·
    have := hEn
    set O := pCoreOf 2 K₁ with hO
    have hcK : c⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := hK₁n (Subgroup.inv_mem _ (hCG₁ hc))
    set α := S125Hat7.autQ K₁ hcK with hα
    have hyc : ∀ l ∈ li L F.V1, (c * y * c⁻¹) * l * (c * y * c⁻¹)⁻¹ ∈ li L F.V1 := by
      intro l hl
      have hN : c * y * c⁻¹ ∈ Subgroup.normalizer (li L F.V1 : Set G) := by
        rw [show c * y * c⁻¹ = (c * y * c⁻¹ * y⁻¹) * y by group]
        exact Subgroup.mul_mem _ (hTL₁ (hcomm c hc)) (Subgroup.le_normalizer hy1)
      exact (Subgroup.mem_normalizer_iff.mp hN l).mp hl
    have hzX : z ∈ Subgroup.normalizer
        (((rho hLK).range.map α.toMonoidHom : Subgroup _) : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) := by
      apply S125St.mem_normalizer_of_conj_le
      rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
      have hl' := hyc l l.2
      refine ⟨rho hLK ⟨_, hl'⟩, ⟨⟨_, hl'⟩, rfl⟩, ?_⟩
      rw [← hyz]
      simp only [MulEquiv.coe_toMonoidHom, rho_apply, hα, autQ_mk]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [S125Hat7.conjK, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_inclusion]
      group
    have hXA : (rho hLK).range.map α.toMonoidHom = (rho hLK).range :=
      eq_of_mem_normalizer h7 hAE hAQ hzc hzi (map_inf_eq_bot hLK eL hEn h7 α)
        (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective) hzX
    have hconj : ∀ l ∈ li L F.V1, c⁻¹ * l * c⁻¹⁻¹ ∈ li L F.V1 ⊔ O := by
      intro l hl
      have hmem : α (rho hLK ⟨l, hl⟩) ∈ (rho hLK).range :=
        hXA ▸ ⟨rho hLK ⟨l, hl⟩, ⟨⟨l, hl⟩, rfl⟩, rfl⟩
      obtain ⟨l₀, hl₀⟩ := hmem
      rw [rho_apply, hα, rho_apply, autQ_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hl₀
      have h2 := (A6.A6L74.mem_pCoreOf_iff _).2 hl₀
      have e : c⁻¹ * l * c⁻¹⁻¹ = (l₀ : G) *
          (((Subgroup.inclusion hLK l₀)⁻¹ *
            S125Hat7.conjK K₁ hcK (Subgroup.inclusion hLK ⟨l, hl⟩) : ↥K₁) : G) := by
        simp only [S125Hat7.conjK, MulEquiv.coe_mk, Equiv.coe_fn_mk, Subgroup.coe_mul,
          Subgroup.coe_inv, Subgroup.coe_inclusion]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left l₀.2) (Subgroup.mem_sup_right h2)
    have hcO : c⁻¹ ∈ Subgroup.normalizer (O : Set G) :=
      S125Fin.normalizer_le_normalizer_pCoreOf K₁ hcK
    have hcR : c⁻¹ ∈ Subgroup.normalizer ((li L F.V1 ⊔ O : Subgroup G) : Set G) :=
      S125Fin.mem_normalizer_sup (fun l hl => hconj l hl)
        (fun o ho => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hcO o).mp ho))
    have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right (S125L2G.T_le_V F hf.T_le).1
    have hL₁M : li L F.V1 ≤ mi T L F.V1 :=
      (Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)
    have hOT : O ≤ T := S125Cfg.pCoreOf_le_T h1222 F hH hK₁n hKG
    have hres : CFSG.inSubgroup CFSG.perfectResidual (li L F.V1 ⊔ O) = li L F.V1 :=
      le_antisymm ((CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_mono
          (sup_le hL₁M (hOT.trans hTM))).trans (S125Cfg.mi_perfectResidual_le F hH))
        (CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual (S125K6.commutator_li L _)
          le_sup_left)
    have h1 :=
      CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _ hcR
    rw [hres] at h1
    simpa using Subgroup.inv_mem _ h1

end Alpha

section Beta

theorem V_le_of_comm (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {X : Subgroup G} (hX : ∀ v ∈ V, ∀ l ∈ li L F.V1, v⁻¹ * l * v * l⁻¹ ∈ X) : V ≤ X := by
  have hbasis : ∀ k : Fin 10,
      ((F.e.symm (Multiplicative.ofAdd (Pi.single k 1)) : ↥V) : G) ∈ X := by
    intro k
    obtain ⟨m, t, ht, hw⟩ := S125Gen.exists_transvec_wedge k
    have hψ : S125Tr2.psi F t ∈ autOn (li L F.V1) V := by
      rw [S125L8.autOn_l1 h1222 F hH]
      exact ⟨t, ht, rfl⟩
    obtain ⟨l, hlN, hlL, hl⟩ := mem_autOn_iff_exists.mp hψ
    set v : ↥V := F.e.symm (Multiplicative.ofAdd (Pi.single m 1)) with hv
    set b : ↥V := F.e.symm (Multiplicative.ofAdd (Pi.single k 1)) with hb
    have hact : conjAct V ⟨l, hlN⟩ v = v * b := by
      apply F.e.injective
      rw [hl]
      change F.e (((F.γ.symm t : ↥(autOn L V)) : MulAut ↥V) v) = _
      rw [F.wedge, MulEquiv.apply_symm_apply, S125ZV.wedgeRep_apply, map_mul, hv, hb,
        MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, hw, ofAdd_add]
    have hcoe : l * (v : G) * l⁻¹ = (v : G) * (b : G) := by
      have := congrArg Subtype.val hact
      rwa [S125ZV.coe_conjAct_apply] at this
    have hbG : (b : G) = (v : G)⁻¹ * l * v * l⁻¹ := by
      have h1 : (b : G) = (v : G)⁻¹ * (l * v * l⁻¹) := by
        rw [hcoe]
        group
      rw [h1]
      group
    rw [hbG]
    exact hX _ v.2 _ hlL
  have hle : S125Ir.coordOf F V ≤ S125Ir.coordOf F X := by
    rw [S125Ir.coordOf_V, ← S125Ir.coordSub_univ]
    exact S125Ir.coordSub_le fun k _ => S125Ir.mem_coordOf.2 (hbasis k)
  exact (S125Ir.coordOf_le_iff F le_rfl).1 hle

theorem V_le_pCoreOf_of_e49 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G} (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (hE : IsSL27OverE49 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    V ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  obtain ⟨E, -, -, -, -, -, z, -, -, hzc, -, huniq⟩ := e49_facts hK.2.1 hLK eL hE
  have hVL₁ := S125L8.V_le_l1 h1222 F hH
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hcen : ∀ v (hv : v ∈ li L F.V1), v ∈ V → ∀ a ∈ (rho hLK).range,
      a * rho hLK ⟨v, hv⟩ = rho hLK ⟨v, hv⟩ * a := by
    intro v hv hvV a ha
    by_cases h1 : rho hLK ⟨v, hv⟩ = 1
    · rw [h1, mul_one, one_mul]
    · have hsq : rho hLK ⟨v, hv⟩ * rho hLK ⟨v, hv⟩ = 1 := by
        rw [← map_mul]
        have : (⟨v, hv⟩ : ↥(li L F.V1)) * ⟨v, hv⟩ = 1 :=
          Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hf.sq v hvV)
        rw [this, map_one]
      rw [huniq _ ⟨_, rfl⟩ hsq h1]
      exact hzc a ha
  have hVO : V ≤ pCoreOf 2 K₁ := by
    refine V_le_of_comm h1222 F hH fun v hv l hl => ?_
    have hvL := hVL₁ hv
    have hx : v⁻¹ * l * v * l⁻¹ ∈ li L F.V1 :=
      (li L F.V1).mul_mem ((li L F.V1).mul_mem ((li L F.V1).mul_mem
        ((li L F.V1).inv_mem hvL) hl) hvL) ((li L F.V1).inv_mem hl)
    have h1 : rho hLK ⟨v⁻¹ * l * v * l⁻¹, hx⟩ = 1 := by
      have e : (⟨v⁻¹ * l * v * l⁻¹, hx⟩ : ↥(li L F.V1)) =
          (⟨v, hvL⟩ : ↥(li L F.V1))⁻¹ * ⟨l, hl⟩ * ⟨v, hvL⟩ * (⟨l, hl⟩ : ↥(li L F.V1))⁻¹ :=
        Subtype.ext (by simp)
      have hc := hcen v hvL hv _ ⟨⟨l, hl⟩, rfl⟩
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (rho hLK ⟨v, hvL⟩)⁻¹ * rho hLK ⟨l, hl⟩ * rho hLK ⟨v, hvL⟩ * (rho hLK ⟨l, hl⟩)⁻¹
          = (rho hLK ⟨v, hvL⟩)⁻¹ * (rho hLK ⟨l, hl⟩ * rho hLK ⟨v, hvL⟩) *
            (rho hLK ⟨l, hl⟩)⁻¹ := by group
        _ = (rho hLK ⟨v, hvL⟩)⁻¹ * (rho hLK ⟨v, hvL⟩ * rho hLK ⟨l, hl⟩) *
            (rho hLK ⟨l, hl⟩)⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [rho_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (A6.A6L74.mem_pCoreOf_iff _).2 h1
  exact hVO.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hKG)
    (hK₁n.trans (S125Fin.normalizer_le_normalizer_pCoreOf K₁))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁))

end Beta

section Gamma

theorem exists_solvable_of_e49 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G} (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hLK : li L F.V1 ≤ K₁) (hE : IsSL27OverE49 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    ∃ H : Subgroup G, T ≤ H ∧ H ≤ K₁ ⊔ T ∧ Group.IsSolvable ↥H ∧
      ¬ H ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  obtain ⟨E, hEn, h7, hcent, hAE, -, -⟩ := e49_facts hK.2.1 hLK eL hE
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := (S125L2G.T_le_V F hf.T_le).1.trans hK₁n
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) with hπ
  set P₇ := CFSG.pCore 7 (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) with hP₇
  set O₇ : Subgroup G := (P₇.comap π).map K₁.subtype with hO₇
  have hO₇K : O₇ ≤ K₁ := Subgroup.map_subtype_le _
  have hmemO₇ : ∀ k : ↥K₁, π k ∈ P₇ → (k : G) ∈ O₇ := fun k hk => ⟨k, hk, rfl⟩
  have hEP : E ≤ P₇ := by
    have hE7 : IsPGroup 7 ↥E := fun e => ⟨1, Subtype.ext (by rw [pow_one]; exact h7 _ e.2)⟩
    rw [hP₇]
    exact le_sSup ⟨hEn, hE7⟩
  have hTO : T ≤ Subgroup.normalizer (O₇ : Set G) := by
    intro t ht
    apply S125St.mem_normalizer_of_conj_le
    rintro _ ⟨k, hk, rfl⟩
    have hk' : π k ∈ P₇ := hk
    have h1 : S125Hat7.autQ K₁ (hTK ht) (π k) ∈ P₇ := by
      have h := CFSG.pCore_map_iso 7 (S125Hat7.autQ K₁ (hTK ht))
      rw [hP₇, ← h]
      exact ⟨π k, hk', rfl⟩
    exact hmemO₇ _ h1
  have hO₇s : Group.IsSolvable ↥O₇ := by
    have hCs : Group.IsSolvable ↥(P₇.comap π) := by
      have h2 : Group.IsSolvable ↥(CFSG.pCore 2 ↥K₁) := by
        have := (CFSG.pCore_isPGroup (p := 2) (G := ↥K₁)).isNilpotent
        infer_instance
      have h7s : Group.IsSolvable ↥P₇ := by
        have := (CFSG.pCore_isPGroup (p := 7) (G := ↥K₁ ⧸ CFSG.pCore 2 ↥K₁)).isNilpotent
        infer_instance
      have hle : CFSG.pCore 2 ↥K₁ ≤ P₇.comap π := fun x hx => by
        show π x ∈ P₇
        rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
        exact P₇.one_mem
      let g : ↥(P₇.comap π) →* ↥P₇ := (π.comp (P₇.comap π).subtype).codRestrict P₇ fun x => x.2
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) g ?_
      intro x hx
      have hx1 : π (x : ↥K₁) = 1 := congrArg Subtype.val hx
      exact ⟨⟨x, (QuotientGroup.eq_one_iff _).1 hx1⟩, rfl⟩
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (P₇.comap π) _ K₁.subtype_injective).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective _ _ K₁.subtype_injective).symm.injective
  set H := O₇ ⊔ T with hHdef
  have hHN : H ≤ Subgroup.normalizer (O₇ : Set G) := sup_le Subgroup.le_normalizer hTO
  have hHs : Group.IsSolvable ↥H := by
    have : (O₇.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHN
    have h1 : Group.IsSolvable ↥(O₇.subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : O₇ ≤ H)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe _).injective
    have h2 : Group.IsSolvable (↥H ⧸ O₇.subgroupOf H) := by
      have hp : IsPGroup 2 (↥H ⧸ O₇.subgroupOf H) := by
        intro q
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
        have hh : (h : G) ∈ ((T ⊔ O₇ : Subgroup G) : Set G) := by
          rw [sup_comm]
          exact h.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right T O₇ hTO] at hh
        obtain ⟨t, ht, o, ho, hto⟩ := hh
        obtain ⟨k, hk⟩ := hH.hyp.sylow.1 ⟨t, ht⟩
        have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
        refine ⟨k, ?_⟩
        have htH : t ∈ H := Subgroup.mem_sup_right ht
        have hoH : o ∈ H := Subgroup.mem_sup_left ho
        have he : h = ⟨t, htH⟩ * ⟨o, hoH⟩ := Subtype.ext hto.symm
        have ho1 : (QuotientGroup.mk (⟨o, hoH⟩ : ↥H) : ↥H ⧸ O₇.subgroupOf H) = 1 :=
          (QuotientGroup.eq_one_iff _).2 ho
        rw [he, QuotientGroup.mk_mul, ho1, mul_one, ← QuotientGroup.mk_pow]
        have : (⟨t, htH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
        rw [this, QuotientGroup.mk_one]
      have := hp.isNilpotent
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient (O₇.subgroupOf H)
  refine ⟨H, le_sup_right, sup_le_sup_right hO₇K T, hHs, fun hHM => ?_⟩
  have hAle : (rho hLK).range ≤ E := by
    rw [← hcent]
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₁) e
    have hkO : (k : G) ∈ O₇ := hmemO₇ k (hEP he)
    have hkM : (k : G) ∈ Subgroup.normalizer (L : Set G) := hHM (Subgroup.mem_sup_left hkO)
    have hkN : (k : G) ∈ Subgroup.normalizer (li L F.V1 : Set G) :=
      S125K6.le_normalizer_li ((Subgroup.zpowers_le).2 hkM) ((Subgroup.zpowers_le).2 (hKG k.2))
        (Subgroup.mem_zpowers _)
    have hl' : (k : G) * l * (k : G)⁻¹ ∈ li L F.V1 := (Subgroup.mem_normalizer_iff.mp hkN l).mp l.2
    have h1 : π k * rho hLK l * (π k)⁻¹ = rho hLK ⟨_, hl'⟩ := by
      rw [rho_apply, rho_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    have h2 : π k * rho hLK l * (π k)⁻¹ * (rho hLK l)⁻¹ ∈ (rho hLK).range ⊓ E := by
      refine ⟨?_, ?_⟩
      · rw [h1]
        exact (rho hLK).range.mul_mem ⟨_, rfl⟩ ((rho hLK).range.inv_mem ⟨l, rfl⟩)
      · rw [show π k * rho hLK l * (π k)⁻¹ * (rho hLK l)⁻¹ =
          π k * (rho hLK l * (π k)⁻¹ * (rho hLK l)⁻¹) by group]
        exact E.mul_mem he (hEn.conj_mem _ (E.inv_mem he) _)
    rw [hAE, Subgroup.mem_bot] at h2
    calc π k * rho hLK l = π k * rho hLK l * (π k)⁻¹ * (rho hLK l)⁻¹ * (rho hLK l * π k) := by
          group
      _ = rho hLK l * π k := by rw [h2, one_mul]
  have hbot : (rho hLK).range = ⊥ := by
    rw [eq_bot_iff, ← hAE]
    exact le_inf le_rfl hAle
  have hc := card_quot_le hLK
  rw [hbot, Subgroup.card_bot, Nat.card_congr eL.toEquiv, card_sl_three_zmod_two] at hc
  omega

end Gamma

end S125E49

end CFSG.Quasithin.H13
