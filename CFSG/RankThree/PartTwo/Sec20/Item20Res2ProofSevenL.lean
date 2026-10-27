module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSevenE
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofCases
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLCentral
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofLNormal

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix

@[expose] def Step207Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    L ≤ (L ⊓ Subgroup.normalizer (T : Set G)) ⊔ (A ⊓ L)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_hom_sl3_of_odd {K : Subgroup G} {n : ℕ} (hn : Odd n)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 3 (GaloisField 2 n)) :
    ∃ α : ↥K →* SpecialLinearGroup (Fin 3) (GaloisField 2 n), Function.Surjective α ∧
      α.ker = (CFSG.Open.pCoreOf 2 K).subgroupOf K := by
  set ε : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* SpecialLinearGroup (Fin 3) (GaloisField 2 n) :=
    (e.trans (projSLEquivStatedSL hn)).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (GaloisField 2 n)).symm
  refine ⟨ε.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)),
    ε.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext w
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf,
    ← mem_pCore_iff_mem_pCoreOf_two, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
  constructor
  · intro h
    apply ε.injective
    rw [h, map_one]
  · intro h
    rw [h, map_one]

theorem le_normalizer_normalClosureIn_of_hom_core {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hTN : T ≤ N)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F % 3 = 2) (α : ↥(kTwenty M c) →* SpecialLinearGroup (Fin 3) F)
    {V : Subgroup G} (hαk : α.ker = V.subgroupOf (kTwenty M c)) (hV2 : IsPGroup 2 V) :
    L ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hc1 : c = 1
  · have hX : normalClosureIn (kTwenty M c ⊓ N) c = ⊥ := by
      rw [eq_bot_iff, normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m, -, rfl⟩
      rw [hc1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    intro l _
    rw [hX]
    exact mem_normalizer_of_map_conj_le (le_of_eq (Subgroup.map_bot _))
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  have hc3 : c ^ 3 = 1 := hT.mem_partTwoE.1.2 c hcA
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hcN : c ∈ N := by
    rw [hN]
    exact hAL hcA
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hkey : ∀ y ∈ kTwenty M c ⊓ N, y ^ 3 = 1 → y ∈ normalClosureIn (kTwenty M c ⊓ N) c := by
    intro y hy hy3
    obtain ⟨k, hk, hyk⟩ := exists_mem_zpowers_conj hq α hαk hV2 inf_le_left ⟨hcK, hcN⟩ hy hc3
      hy3 hc1
    have hkc : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    exact (Subgroup.zpowers_le.mpr hkc) hyk
  have hcKN : c ∈ kTwenty M c ⊓ N := ⟨hcK, hcN⟩
  have hTX : T ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) := by
    intro t ht
    have htKN : t ∈ Subgroup.normalizer ((kTwenty M c ⊓ N : Subgroup G) : Set G) :=
      mem_normalizer_inf_of_mem (hMK (hT.sylow.le ht)) (Subgroup.le_normalizer (hTN ht))
    apply mem_normalizer_of_map_conj_le
    rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hkcKN : k * c * k⁻¹ ∈ kTwenty M c ⊓ N :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hcKN) (Subgroup.inv_mem _ hk)
    show t * (k * c * k⁻¹) * t⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c
    refine hkey _ ((Subgroup.mem_normalizer_iff.mp htKN _).mp hkcKN) ?_
    rw [conj_pow, conj_pow, hc3]
    group
  have hOX : CFSG.Open.pCoreOf 2 L ≤
      Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) :=
    (pCoreOf_le_core hT hN hO2L hTN).trans hTX
  have hLXO := le_normalizer_normalClosureIn_sup_pCoreOf_core hT hN hAL
  intro l hl
  apply mem_normalizer_of_map_conj_le
  rw [normalClosureIn, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hmem : k * c * k⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c ⊔ CFSG.Open.pCoreOf 2 L :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, hk, rfl⟩)
  show l * (k * c * k⁻¹) * l⁻¹ ∈ normalClosureIn (kTwenty M c ⊓ N) c
  refine mem_of_pow_three_eq_one hOX (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ((Subgroup.mem_normalizer_iff.mp (hLXO hl) _).mp hmem) ?_
  rw [conj_pow, conj_pow, hc3]
  group

omit [Finite G] in
theorem mem_normalizer_commutator_of_mem {Z I : Subgroup G} {x : G}
    (hZ : x ∈ Subgroup.normalizer (Z : Set G)) (hI : x ∈ Subgroup.normalizer (I : Set G)) :
    x ∈ Subgroup.normalizer ((⁅Z, I⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hZ, Subgroup.mem_normalizer_iff_map_conj_eq.mp hI]

theorem le_centralizer_of_le_normalizer_core {A L E : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ L) L)
    (hLE : L ≤ Subgroup.normalizer (E : Set G))
    (hBE : A ⊓ L ≤ Subgroup.centralizer (E : Set G)) : L ≤ Subgroup.centralizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hLq
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := isSimpleGroup_projSL_three_galois_four
    exact e.isSimpleGroup
  have h3L : 3 ∣ Nat.card L := by
    rw [card_eq_of_nonempty_quotient e]
    exact (show (3 : ℕ) ∣ 20160 by norm_num).mul_right _
  have hgen := closure_pow_eq_one_eq hLp hs Nat.prime_three (by norm_num) h3L
  rw [← hgen, Subgroup.closure_le]
  rintro y ⟨hyL, hy3⟩
  obtain ⟨P, hP, hyP⟩ := exists_isSylowOf_le (isPGroup_zpowers_of_pow_three hy3)
    (Subgroup.zpowers_le.mpr hyL)
  obtain ⟨l, hlL, hPl⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hsyl hP
  have hyP' : y ∈ P := hyP (Subgroup.mem_zpowers y)
  rw [hPl] at hyP'
  obtain ⟨b, hb, rfl⟩ := hyP'
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : l⁻¹ * x * l ∈ E := by
    have := (Subgroup.mem_normalizer_iff.mp (hLE (L.inv_mem hlL)) x).mp hx
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp (hBE hb) _ hx'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc x * (l * b * l⁻¹) = l * ((l⁻¹ * x * l) * b) * l⁻¹ := by group
    _ = l * (b * (l⁻¹ * x * l)) * l⁻¹ := by rw [hc]
    _ = l * b * l⁻¹ * x := by group

theorem step207LE_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)))
    (hO2L : CFSG.Open.pCoreOf 2 L ≤ M) (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ L) L)
    (hLp : ⁅L, L⁆ = L) (h3 : KIsL3 M c) (h206 : ⁅vTwenty M c T, A ⊓ L⁆ = ⊥)
    (hgen : L ≤ (L ⊓ Subgroup.normalizer (T : Set G)) ⊔ (A ⊓ L)) (hTN : T ≤ N) :
    L ≤ Subgroup.centralizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  obtain ⟨α, -, hαk⟩ := exists_hom_sl3_of_odd hn e
  have hq : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn.pos.ne']
    exact two_pow_mod_three_of_odd hn
  have hLI := le_normalizer_normalClosureIn_of_hom_core hT hN hAL hO2L hTN hq α hαk
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hEV : ⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ ≤ vTwenty M c T :=
    Subgroup.commutator_mono le_rfl
      ((normalClosureIn_le (show c ∈ kTwenty M c ⊓ N from ⟨self_mem_normalClosureIn M c, by
        rw [hN]
        exact hAL (mem_of_hyp201 hT.toHyp201)⟩)).trans
        inf_le_left)
  have hBE : A ⊓ L ≤ Subgroup.centralizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G) := by
    have h1 : ⁅⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆, A ⊓ L⁆ = ⊥ :=
      le_bot_iff.mp (h206 ▸ Subgroup.commutator_mono hEV le_rfl)
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
  have hLE : L ≤ Subgroup.normalizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G) := by
    refine hgen.trans (sup_le ?_ ?_)
    · rintro x ⟨hxL, hxT⟩
      exact mem_normalizer_commutator_of_mem (normalizer_le_normalizer_fourChar T 0 hxT)
        (hLI hxL)
    · exact hBE.trans (Subgroup.centralizer_le_normalizer _)
  exact le_centralizer_of_le_normalizer_core hLp hLq hsyl hLE hBE

section Certificates

theorem step207LE_of (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) (h204 : Item204One)
    (h2051 : Step2051) (h2053 : Step2053) (h206 : Item206One) (hgen : Step207Gen) :
    Step207LE := by
  intro G _ _ A M L N c T hT hTN _
  have h := hT.hyp201One
  obtain ⟨H, hH18, -, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  have hLp : ⁅L, L⁆ = L := by
    rw [hL]
    exact Sec18.commutator_eq_of_mem_oTwoComponentsIn
      (mem_scriptH_iff.mp hH18.mem_scriptH).2.2.1
  exact step207LE_core hT.toCtx20 hN (le_normalizer_of_hyp201One h)
    (nonempty_quotient_of_hyp201One h184 h) (pCoreOf_le_of_hyp201One h)
    (isSylowOf_three_inf_of_hyp201One h1812 h184 h) hLp
    (h2053 G A M L N c T hT (rank3II_20_5_2_of h204 hT (h2051 G A M L N c T hT)))
    (h206 G A M L N c T hT hTN) (hgen G A M L N c T hT hTN) hTN

theorem item207One_of_items (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (h1812 : Sec18.Item181_2)
    (h184 : Sec18.Item184_1) (h206 : Item206One) (hgen : Step207Gen) (hK0 : Step207K0) :
    Item207One :=
  item207One_of_steps h204 h2051 h2053 h189 (step207E_of h204 h2051 h2053 h189 h321)
    (step207LE_of h1812 h184 h204 h2051 h2053 h206 hgen) hK0

end Certificates

end CFSG.RankThree.PartTwo.Sec20
