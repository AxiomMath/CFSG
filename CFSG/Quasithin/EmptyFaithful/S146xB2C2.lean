module

public import CFSG.Quasithin.EmptyFaithful.S146xB2Aut
public import CFSG.Quasithin.EmptyFaithful.S146G2
public import CFSG.Quasithin.EmptyFaithful.S146E6
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.SmallRanks
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Centers

theorem center_eq_bot_of_equiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hex : e x ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y')]
  rw [h, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hex, map_one])

theorem center_eq_bot_of_shape {N : Type} [Group N]
    (hN : (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPSL 2 p 1 N) ∨ IsPSL 3 2 1 N ∨ IsAlt 6 N ∨ IsPSL 3 3 1 N) :
    Subgroup.center N = ⊥ := by
  rcases hN with ⟨p, hp, hp2, h⟩ | h | h | h
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    exact center_eq_bot_of_equiv'
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
      (GorensteinWalter.psl2_center_eq_bot K)
  · obtain ⟨e⟩ := isPSL_three_two_iff.mp h
    exact center_eq_bot_of_equiv'
      (e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3))
      CFSG.QuasithinUnique.Setup.Family.center_GL32
  · obtain ⟨e⟩ : Nonempty (N ≃* alternatingGroup (Fin 6)) := h
    exact center_eq_bot_of_equiv' e (alternatingGroup.center_eq_bot (by simp))
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = Fintype.card (ZMod 3) := by
      rw [← Nat.card_eq_fintype_card, hK, ZMod.card]; norm_num
    let φ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
    exact center_eq_bot_of_equiv'
      (e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3)).trans
          CFSG.GH74.SmallRanks.pslEquivSl3)))
      CFSG.GH74.SmallRanks.center_sl3

end Centers

section CoreFree

theorem exists_sylow_eq_of_odd_index {X : Type*} [Group X] [Finite X] (S₀ : Subgroup X)
    (hp : IsPGroup 2 S₀) (hodd : ¬ 2 ∣ S₀.index) : ∃ Y : Sylow 2 X, (Y : Subgroup X) = S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hY⟩ := hp.exists_le_sylow
  refine ⟨Y, le_antisymm ?_ hY⟩
  have h1 : S₀.relIndex (Y : Subgroup X) * (Y : Subgroup X).index = S₀.index := by
    rw [Subgroup.relIndex_mul_index hY]
  have h2 : ¬ 2 ∣ S₀.relIndex (Y : Subgroup X) := fun h => hodd (h.trans (h1 ▸ dvd_mul_right _ _))
  have hYp : IsPGroup 2 (Y : Subgroup X) := Y.isPGroup'
  obtain ⟨n, hn⟩ := hYp.index (S₀.subgroupOf Y)
  have : S₀.relIndex Y = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    exact h2 (this ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero] at this
  exact Subgroup.relIndex_eq_one.mp this

theorem centralizer_eq_one_of_coreFree {X : Type*} [Group X] [Finite X] (N S₀ P : Subgroup X)
    [N.Normal] (hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1)
    (hX2 : ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) (hS₀ : IsPGroup 2 S₀) (hodd : ¬ 2 ∣ S₀.index)
    (hSP : S₀ ≤ P) (hP : ∀ x : X, (∀ g : X, g * x * g⁻¹ ∈ P) → x = 1) :
    ∀ y : X, (∀ n ∈ N, y * n * y⁻¹ = n) → y = 1 := by
  intro y hy
  obtain ⟨Y, hY⟩ := exists_sylow_eq_of_odd_index S₀ hS₀ hodd
  set C : Subgroup X := Subgroup.centralizer (N : Set X) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer (H := N)
  have hCp : IsPGroup 2 C := by
    intro c
    obtain ⟨k, hk⟩ := hX2 (c : X)
    refine ⟨k, Subtype.ext ?_⟩
    have hcc : (c : X) ^ 2 ^ k ∈ C := C.pow_mem c.2 _
    have : (c : X) ^ 2 ^ k = 1 := by
      apply hZ _ hk
      intro m hm
      exact ((Subgroup.mem_centralizer_iff.mp hcc) m hm).symm
    simpa using this
  have hCY : C ≤ Y := hCp.le_sylow_of_normal Y
  have hyC : y ∈ C := by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro n hn
    have := hy n hn
    calc n * y = y * n * y⁻¹ * y := by rw [this]
      _ = y * n := by group
  apply hP y
  intro g
  have hgy : g * y * g⁻¹ ∈ C := hCn.conj_mem y hyC g
  have : g * y * g⁻¹ ∈ (Y : Subgroup X) := hCY hgy
  rw [hY] at this
  exact hSP this

end CoreFree

section StarFacts

variable {G : Type} [Group G]

theorem kerIn_le_self (Iz I : Subgroup G) : kerIn Iz I ≤ Iz := fun x hx => by
  simpa using hx 1 (Subgroup.one_mem I)

theorem star_coreFree {I Iz : Subgroup G} :
    ∀ x : E2.StarQuot Iz I, (∀ g : E2.StarQuot Iz I, g * x * g⁻¹ ∈ E2.star Iz I Iz) → x = 1 := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : (y : G) ∈ kerIn Iz I := by
    intro b hb
    obtain ⟨z, hz, hzeq⟩ := hx (QuotientGroup.mk ⟨b, hb⟩)
    have h1 : z⁻¹ * (⟨b, hb⟩ * y * ⟨b, hb⟩⁻¹) ∈ (kerIn Iz I).subgroupOf I :=
      QuotientGroup.eq.mp hzeq
    have h2 : (z : G)⁻¹ * (b * (y : G) * b⁻¹) ∈ kerIn Iz I := h1
    have h3 : (z : G)⁻¹ * (b * (y : G) * b⁻¹) ∈ Iz := kerIn_le_self Iz I h2
    have hz' : (z : G) ∈ Iz := hz
    have e : b * (y : G) * b⁻¹ = (z : G) * ((z : G)⁻¹ * (b * (y : G) * b⁻¹)) := by group
    rw [e]
    exact Iz.mul_mem hz' h3
  exact (QuotientGroup.eq_one_iff y).mpr hy

theorem star_isPGroup_odd {I Iz S : Subgroup G} (hS : IsSylowTwoOf S I) :
    IsPGroup 2 (E2.star Iz I S) ∧ ¬ 2 ∣ (E2.star Iz I S).index := by
  constructor
  · exact (hS.isPGroup.comap_subtype (K := I)).map _
  · set π : ↥I →* E2.StarQuot Iz I := QuotientGroup.mk' ((kerIn Iz I).subgroupOf I)
    have hle : S.subgroupOf I ≤ (E2.star Iz I S).comap π := fun x hx => ⟨x, hx, rfl⟩
    have h1 : ((E2.star Iz I S).comap π).index = (E2.star Iz I S).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 := Subgroup.index_dvd_of_le hle
    rw [h1] at h2
    exact fun h => hS.2.2 (h.trans h2)

variable [Finite G]

theorem le_pCore_of_mem_kerIn_two {I S Iz K : Subgroup G} (hIK : I = K ⊔ S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hJ : ∀ x : G, x ∈ kerIn Iz I ↔ x ∈ K ⊔ pCoreOf 2 I ∧
      ∀ y ∈ K ⊔ pCoreOf 2 I, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 I)
    {x : G} (hxJ : x ∈ kerIn Iz I) (hx2 : x ^ 2 = 1) : x ∈ pCoreOf 2 I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 I with hQ
  set M : Subgroup G := K ⊔ Q with hM
  have hKI : K ≤ I := hIK ▸ le_sup_left
  have hKnI : I ≤ Subgroup.normalizer (K : Set G) := by
    rw [hIK]; exact sup_le Subgroup.le_normalizer hSK
  have hQnI : I ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 I
  have hMI : M ≤ I := sup_le hKI (pCoreOf_le 2 I)
  have hMn : I ≤ Subgroup.normalizer (M : Set G) := le_normalizer_sup_of_le hKnI hQnI
  obtain ⟨hxM, hcomm⟩ := (hJ x).mp hxJ
  have hxI : x ∈ I := hMI hxM
  have hxNQ : x ∈ Subgroup.normalizer (Q : Set G) := hQnI hxI
  have hx2' : x ^ 2 ∈ Q := by rw [hx2]; exact Q.one_mem
  have hxinv : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, hx2]
  let P : Subgroup G := twoCoset Q x hxNQ hx2'
  have hPM : P ≤ M := by
    rintro y (hy | hy)
    · exact Subgroup.mem_sup_right hy
    · have : y = (y * x) * x⁻¹ := by group
      rw [this]
      exact M.mul_mem (Subgroup.mem_sup_right hy) (M.inv_mem hxM)
  have key : ∀ m ∈ M, ∀ y ∈ P, m * y * m⁻¹ ∈ P := by
    intro m hm y hy
    have hmI : m ∈ I := hMI hm
    have hmQ : ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun q hq =>
      (Subgroup.mem_normalizer_iff.mp (hQnI hmI) q).mp hq
    rcases hy with hy | hy
    · exact Or.inl (hmQ y hy)
    · refine Or.inr ?_
      have hxm := hcomm m hm
      have h1 : m * x * m⁻¹ * x ∈ Q := by
        have h2 := Q.inv_mem hxm
        have e : (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ := by group
        rw [e, hxinv] at h2
        exact h2
      have e : m * y * m⁻¹ * x = (m * (y * x) * m⁻¹) * (m * x * m⁻¹ * x) := by
        calc m * y * m⁻¹ * x = (m * (y * x) * m⁻¹) * (m * x⁻¹ * m⁻¹ * x) := by group
          _ = (m * (y * x) * m⁻¹) * (m * x * m⁻¹ * x) := by rw [hxinv]
      rw [e]
      exact Q.mul_mem (hmQ _ hy) h1
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key m hm y hy, fun hy => ?_⟩
    have := key m⁻¹ (M.inv_mem hm) _ hy
    simpa [mul_assoc] using this
  have hxx : x * x = 1 := by rw [← pow_two, hx2]
  have hPp : IsPGroup 2 P := by
    intro y
    have hy2 : (y : G) ^ 2 ∈ Q := by
      rcases y.2 with hy | hy
      · exact Q.pow_mem hy 2
      · have h3 : x * ((y : G) * x) * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxNQ _).mp hy
        have e : (y : G) ^ 2 = ((y : G) * x) * (x * ((y : G) * x) * x⁻¹) := by
          calc (y : G) ^ 2 = (y : G) * (x * x) * (y : G) := by rw [hxx, mul_one, pow_two]
            _ = ((y : G) * x) * (x * ((y : G) * x) * x⁻¹) := by group
        rw [e]
        exact Q.mul_mem hy h3
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 I) ⟨(y : G) ^ 2, hy2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((y : G) ^ 2) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    show (y : G) ^ 2 ^ (k + 1) = 1
    rw [pow_succ', pow_mul]
    exact hk'
  have hxP : x ∈ P := mem_twoCoset_self hxNQ hx2'
  have hxM2 : x ∈ pCoreOf 2 M := le_pCoreOf_of_le_normalizer 2 hPM hMP hPp hxP
  have hMQ : pCoreOf 2 M ≤ Q :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 M).trans hMI)
      (hMn.trans (normalizer_le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)
  exact hMQ hxM2

theorem relIndex_le_card_star {I Iz A Q : Subgroup G} (hAI : A ≤ I)
    (hAJ : ∀ x ∈ A, x ∈ kerIn Iz I → x ∈ Q) :
    Q.relIndex A ≤ Nat.card (E2.star Iz I A) := by
  classical
  set π : ↥I →* E2.StarQuot Iz I := QuotientGroup.mk' ((kerIn Iz I).subgroupOf I) with hπ
  set A' : Subgroup ↥I := A.subgroupOf I with hA'
  let g : ↥A' →* E2.StarQuot Iz I := π.comp A'.subtype
  have hrange : g.range = E2.star Iz I A := by
    show (π.comp A'.subtype).range = A'.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hmul : g.ker.index * Nat.card g.ker = Nat.card A' := Subgroup.index_mul_card g.ker
  rw [Subgroup.index_ker, hrange] at hmul
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv
  have hker : Nat.card g.ker ≤ Nat.card ↥(Q ⊓ A) := by
    refine Nat.card_le_card_of_injective
      (fun x : g.ker => (⟨((x.1 : ↥A') : ↥I).1, ?_⟩ : ↥(Q ⊓ A))) ?_
    · have hx : g x.1 = 1 := x.2
      have h1 : π ((x.1 : ↥A') : ↥I) = 1 := hx
      have h2 : ((x.1 : ↥A') : ↥I) ∈ (kerIn Iz I).subgroupOf I :=
        (QuotientGroup.eq_one_iff _).mp h1
      exact ⟨hAJ _ (Subgroup.mem_subgroupOf.mp x.1.2) h2, Subgroup.mem_subgroupOf.mp x.1.2⟩
    · intro x y hxy
      have := congrArg Subtype.val hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact this
  have hrel := Subgroup.relIndex_mul_card Q A
  have hpos : 0 < Nat.card ↥(Q ⊓ A) := Nat.card_pos
  have hle : Q.relIndex A * Nat.card ↥(Q ⊓ A) ≤
      Nat.card (E2.star Iz I A) * Nat.card ↥(Q ⊓ A) := by
    calc Q.relIndex A * Nat.card ↥(Q ⊓ A) = Nat.card A := hrel
      _ = Nat.card A' := hA'card.symm
      _ = Nat.card (E2.star Iz I A) * Nat.card g.ker := hmul.symm
      _ ≤ Nat.card (E2.star Iz I A) * Nat.card ↥(Q ⊓ A) := Nat.mul_le_mul_left _ hker
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem sixteen_le_relIndex_of_mIdx {A Q : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ mIdx A Q) :
    16 ≤ Q.relIndex A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hA Q
  unfold mIdx at h4
  rw [hn, padicValNat.prime_pow] at h4
  rw [hn]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4

theorem isElemAbelian_map_two {H K : Type*} [Group H] [Group K] (f : H →* K) {A : Subgroup H}
    (hA : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map hA _

omit [Finite G] in
theorem isElemAbelian_subgroupOf_two {I A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (A.subgroupOf I) := CFSG.Open.IsElemAbelian.subgroupOf hA I

theorem e22_case_two_false {I S Iz K A : Subgroup G}
    (hS : IsSylowTwoOf S I) (hSIz : S ≤ Iz) (hIK : I = K ⊔ S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hJ : ∀ x : G, x ∈ kerIn Iz I ↔ x ∈ K ⊔ pCoreOf 2 I ∧
      ∀ y ∈ K ⊔ pCoreOf 2 I, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 I)
    (hshape : (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPSL 2 p 1 ↥(E2.star Iz I K)) ∨
      IsPSL 3 2 1 ↥(E2.star Iz I K) ∨ IsAlt 6 ↥(E2.star Iz I K) ∨ IsPSL 3 3 1 ↥(E2.star Iz I K))
    (hAS : A ≤ S) (hAel : IsElemAbelian 2 A) (h4 : 4 ≤ mIdx A (pCoreOf 2 I)) : False := by
  classical
  have hSI : S ≤ I := hS.1
  have hKI : K ≤ I := hIK ▸ le_sup_left
  have hAI : A ≤ I := hAS.trans hSI
  have hKnI : I ≤ Subgroup.normalizer (K : Set G) := by
    rw [hIK]; exact sup_le Subgroup.le_normalizer hSK
  set X := E2.StarQuot Iz I with hXdef
  set π : ↥I →* X := QuotientGroup.mk' ((kerIn Iz I).subgroupOf I) with hπ
  set N : Subgroup X := E2.star Iz I K with hN
  set S₀ : Subgroup X := E2.star Iz I S with hS₀
  set P : Subgroup X := E2.star Iz I Iz with hP
  set B : Subgroup X := E2.star Iz I A with hB
  have hNn : N.Normal := by
    have : (K.subgroupOf I).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKnI
    exact Subgroup.Normal.map this π (QuotientGroup.mk'_surjective _)
  have hX2 : ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : (y : G) ∈ K ⊔ S := hIK ▸ y.2
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hS.isPGroup hSK hy
    refine ⟨k, ⟨y ^ 2 ^ k, ?_, ?_⟩⟩
    · show (y ^ 2 ^ k : ↥I).1 ∈ K
      simpa using hk
    · simp
  have hZ : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 := by
    intro n hn hc
    have : (⟨n, hn⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (hc m m.2).symm
    rw [center_eq_bot_of_shape hshape, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨hS₀p, hS₀odd⟩ := star_isPGroup_odd (Iz := Iz) hS
  have hSP : S₀ ≤ P := Subgroup.map_mono (Subgroup.comap_mono hSIz)
  have hC1 := centralizer_eq_one_of_coreFree N S₀ P hZ hX2 hS₀p hS₀odd hSP star_coreFree
  have hAJ : ∀ x ∈ A, x ∈ kerIn Iz I → x ∈ pCoreOf 2 I := fun x hx hxJ =>
    le_pCore_of_mem_kerIn_two hIK hSK hJ hxJ (hAel.2 x hx)
  have hBcard : 16 ≤ Nat.card B :=
    (sixteen_le_relIndex_of_mIdx (isPGroup_of_isElemAbelian hAel) h4).trans
      (relIndex_le_card_star hAI hAJ)
  have hBab : IsElemAbelian 2 B :=
    isElemAbelian_map_two π (isElemAbelian_subgroupOf_two hAel)
  let φ : ↥B →* MulAut ↥N := (MulAut.conjNormal (H := N)).comp B.subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    apply Subtype.ext
    apply hC1
    intro n hn
    have := congrArg (fun α : MulAut ↥N => ((α ⟨n, hn⟩ : ↥N) : X)) hb
    simpa [φ, MulAut.conjNormal_val] using this
  have hEcard : Nat.card φ.range = Nat.card B :=
    (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hE : IsElemAbelian 2 φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := b
      obtain ⟨a, ha⟩ := a
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      apply Subtype.ext
      show φ a' * φ b' = φ b' * φ a'
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact congrArg Subtype.val (hBab.1.is_comm.comm a' b')
    · obtain ⟨a', rfl⟩ := hx
      rw [← map_pow]
      have : (a' : X) ^ 2 = 1 := hBab.2 a' a'.2
      have h' : a' ^ 2 = 1 := Subtype.ext this
      rw [h', map_one]
  have h8 : Nat.card B ≤ 8 := by
    rw [← hEcard]
    exact card_le_eight_of_shape hshape hE
  omega

end StarFacts

end CFSG.Quasithin
