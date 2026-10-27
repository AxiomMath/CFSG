module

public import CFSG.Quasithin.MS93.ASIrr
public import CFSG.Quasithin.MS93.ASIrrHeart
public import CFSG.Quasithin.MS93.SkConcl
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem vq_ne_bot {M T L : Subgroup G} (h : PUHyp M T L) : Vq M L ≠ ⊥ := by
  intro hV
  have hLC : L ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hV
  have hLQ : L ≤ pCoreOf 2 M := (le_inf h.L_le hLC).trans h.charTwo
  have hL2 : IsPGroup 2 L := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hLQ
  apply h.L_ne_bot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  have hsub : Subsingleton ↥L := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent ↥L hL2.isNilpotent
  refine eq_bot_iff.mpr fun x hx => ?_
  have := Subsingleton.elim (⟨x, hx⟩ : ↥L) 1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

omit [Finite G] in
theorem lt_of_surjective_of_ker {V Z : Subgroup G} (hZV : Z ≤ V) {B : Type*} [Group B]
    [Nontrivial B] (β : ↥V →* B) (hβ : Function.Surjective β) (hker : β.ker = Z.subgroupOf V) :
    Z < V := by
  refine lt_of_le_of_ne hZV fun hZ => ?_
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  obtain ⟨v, rfl⟩ := hβ b
  apply hb
  have : v ∈ β.ker := by
    rw [hker, Subgroup.mem_subgroupOf, hZ]
    exact v.2
  exact this

theorem inf_centralizer_eq_pCoreOf {M T L : Subgroup G} (h : PUHyp M T L) (hVX : Vq M L ≤ Xq M) :
    L ⊓ Subgroup.centralizer (Vq M L : Set G) = pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer
        (le_normalizer_centralizer (h.L_le.trans (le_normalizer_Vq h.le_normalizer)))) ?_
    refine isPGroup_of_odd_eq_one fun k hk hodd => ?_
    exact eq_one_of_odd_of_commute h.charTwo h.L_le hk.1 hodd fun v hv =>
      (Subgroup.mem_centralizer_iff.mp hk.2 v hv).symm
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) fun o ho => ?_
    have hoQ := pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer ho
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp
      (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ (hVX hv))) o hoQ).symm

omit [Finite G] in
theorem pCoreOf_subgroupOf (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L

noncomputable def quotEquivAutI {M T L : Subgroup G} (h : PUHyp M T L) (hVX : Vq M L ≤ Xq M)
    (hV : IsElemAbelian 2 (Vq M L)) : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autI hV L) := by
  have hLN : L ≤ Subgroup.normalizer (Vq M L : Set G) :=
    h.L_le.trans (le_normalizer_Vq h.le_normalizer)
  have hker : (convHom hV L hLN).ker = CFSG.pCore 2 ↥L := by
    rw [ker_convHom, inf_centralizer_eq_pCoreOf h hVX, pCoreOf_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange (convHom hV L hLN)).trans
      (MulEquiv.subgroupCongr (range_convHom hV L hLN)))

theorem le_normalizer_blockU {M T L : Subgroup G} (h : PUHyp M T L) :
    L ≤ Subgroup.normalizer (blockU L : Set G) := by
  rw [blockU_eq h]
  exact h.L_le.trans (le_normalizer_Vq h.le_normalizer)

omit [Finite G] in
theorem inf_centralizer_le_of_natural {L V Z : Subgroup G} {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {α : ↥L →* ↥Γ} (hα : Function.Surjective α)
    (htr : ∀ x y : ι → F, x ≠ 0 → y ≠ 0 →
      ∃ γ : ↥Γ, ((γ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec x = y)
    (htwo : ∀ x : ι → F, ∃ y : ι → F, y ≠ 0 ∧ y ≠ x)
    (h : IsSumOfNaturalModulesVia L V Z α false 1) :
    V ⊓ Subgroup.centralizer (L : Set G) ≤ Z := by
  obtain ⟨-, -, β, -, hker, hβeq⟩ := h
  intro v ⟨hvV, hvC⟩
  have hfix : ∀ ℓ : ↥L, ((α ℓ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
      (Multiplicative.toAdd (β ⟨v, hvV⟩) 0) = Multiplicative.toAdd (β ⟨v, hvV⟩) 0 := by
    intro ℓ
    have hc : (ℓ : G) * v * (ℓ : G)⁻¹ = v := by
      rw [Subgroup.mem_centralizer_iff.mp hvC ℓ ℓ.2, mul_inv_cancel_right]
    have := hβeq ℓ ⟨v, hvV⟩ ⟨v, hvV⟩ hc.symm 0
    simpa [moduleAct] using this.symm
  have h0 : Multiplicative.toAdd (β ⟨v, hvV⟩) 0 = 0 := by
    by_contra hx
    obtain ⟨y, hy0, hyx⟩ := htwo (Multiplicative.toAdd (β ⟨v, hvV⟩) 0)
    obtain ⟨γ, hγ⟩ := htr _ y hx hy0
    obtain ⟨ℓ, rfl⟩ := hα γ
    exact hyx (hγ ▸ hfix ℓ)
  have hβ1 : β ⟨v, hvV⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [Subsingleton.elim i 0, h0]
    rfl
  have : (⟨v, hvV⟩ : ↥V) ∈ β.ker := hβ1
  rw [hker, Subgroup.mem_subgroupOf] at this
  exact this

omit [Finite G] in
theorem exists_ne_zero_ne {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (i j : ι) (hij : i ≠ j) (x : ι → F) : ∃ y : ι → F, y ≠ 0 ∧ y ≠ x := by
  by_cases hx : (Pi.single i 1 : ι → F) = x
  · refine ⟨Pi.single j 1, fun h => ?_, fun h => ?_⟩
    · have := congrFun h j
      simp at this
    · have := congrFun (h.trans hx.symm) j
      simp [hij.symm] at this
  · exact ⟨Pi.single i 1, fun h => by simpa using congrFun h i, hx⟩

theorem isSL3Block_of_case4 {M T L : Subgroup G} (h : PUHyp M T L) (h4 : MS93Case4 M L) :
    IsSL3Block L ∧ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection L (c134Q M L) ⊥ (CFSG.pCore 2 ↥L)
        (CFSG.Assembly.LowTwoRank.StatedSL 3 F) := by
  obtain ⟨hVX, n, F, _, _, α, hF, hα, hn⟩ := h4
  have hmod := isModO2Surj_of_natural h hVX bot_le hα hn
  have hinf : Vq M L ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    le_bot_iff.mp (inf_centralizer_le_of_natural hα statedSL3_transitive
      (exists_ne_zero_ne 0 1 (by decide)) hn)
  have hsec : IsNaturalSection L (Vq M L) ⊥ (CFSG.pCore 2 ↥L)
      (CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    (isNaturalSection_iff_isSumOfNaturalModules_one _ _ bot_le).mpr ⟨α, hα, hmod.2, hn⟩
  have hshort : IsShort2 L := by
    refine isShort2_of h hVX ?_ fun W hZW hWV hLW => ?_
    · rw [hinf]
      exact bot_lt_iff_ne_bot.mpr (vq_ne_bot h)
    · rw [hinf] at hZW ⊢
      exact eq_or_eq_of_natural hα statedSL3_transitive hn hZW hWV hLW
  refine ⟨⟨hshort, n, F, inferInstance, inferInstance, hF, ?_⟩, n, F, inferInstance,
    inferInstance, hF, hsec⟩
  rw [isMatrixBlockType_iff_isNaturalSection L _ (le_normalizer_blockU h), blockU_eq h,
    blockZ_eq h, hinf]
  exact hsec

theorem isModO2Surj_of_case4 {M T L : Subgroup G} (h : PUHyp M T L) (h4 : MS93Case4 M L) :
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α := by
  obtain ⟨hVX, n, F, _, _, α, hF, hα, hn⟩ := h4
  exact ⟨n, F, inferInstance, inferInstance, α, hF, isModO2Surj_of_natural h hVX bot_le hα hn⟩

theorem isSp4Block_of_case3 {M T L : Subgroup G} (h : PUHyp M T L) (h3 : MS93Case3 M T L)
    (hodd : IsOddRadical M T) : IsSp4Block L := by
  obtain ⟨hVX, k, F, _, _, α, -, hF, hα, hn, hT⟩ := h3
  have hk2 := hT hodd
  subst hk2
  have hmod := isModO2Surj_of_natural h hVX inf_le_right hα hn
  have hshort : IsShort2 L := by
    obtain ⟨-, hZV, β, hβ, hker, -⟩ := id hn
    refine isShort2_of h hVX (lt_of_surjective_of_ker hZV β hβ hker) fun W hZW hWV hLW => ?_
    exact eq_or_eq_of_natural hα statedSp2_transitive hn hZW hWV hLW
  refine ⟨hshort, F, inferInstance, inferInstance, hF, ?_⟩
  rw [isMatrixBlockType_iff_isNaturalSection L _ (le_normalizer_blockU h), blockU_eq h,
    blockZ_eq h]
  exact (isNaturalSection_iff_isSumOfNaturalModules_one _ _ inf_le_left).mpr ⟨α, hα, hmod.2, hn⟩

omit [Finite G] in
theorem altHeart6_nontrivial : Nontrivial (AltHeart 6) := by
  refine ⟨⟨QuotientAddGroup.mk (pairVec 0 1), 0, fun h => ?_⟩⟩
  rw [QuotientAddGroup.eq_zero_iff] at h
  have := h 0 2
  rw [pairVec_apply, pairVec_apply] at this
  simp [eVec] at this

omit [Finite G] in
theorem alt6_normal_isPGroup_eq_bot (N : Subgroup ↥(alternatingGroup (Fin 6))) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hN.eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    subst ht
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [Subgroup.card_top, Nat.card_eq_fintype_card, card_alternatingGroup] at hk
    have h3 : 3 ∣ 2 ^ k := by
      rw [← hk]
      decide
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem isAltBlockType_of_case2 {M T L : Subgroup G} (h : PUHyp M T L) (h2 : MS93Case2 M L) :
    IsAltBlockType L 6 := by
  have : Nontrivial (AltHeart 6) := altHeart6_nontrivial
  obtain ⟨hVX, N, hLV, α, hα, hker, β, hβ, hβker, hβeq⟩ := h2
  set Z := Vq M L ⊓ Subgroup.centralizer (L : Set G) with hZ
  have hpk : α.ker = CFSG.pCore 2 ↥L := by
    refine le_antisymm (ker_le_pCore_of_odd α fun ℓ hℓ hodd => ?_)
      (pCore_le_ker_of_surjective α hα alt6_normal_isPGroup_eq_bot)
    have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
    have h2Z : ∀ a ∈ Z, ∃ k : ℕ, a ^ 2 ^ k = 1 := fun a ha => by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
        ⟨a, Vq_le_pCoreOf h.L_le (Subgroup.mem_inf.mp ha).1⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hcomm := commute_of_commutator_mem hodd' (A := Z)
      (fun a ha => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 ℓ ℓ.2) h2Z
      fun b hb => by
        have hv : (ℓ : G) * b * (ℓ : G)⁻¹ ∈ Vq M L :=
          (Subgroup.mem_normalizer_iff.mp (hLV ℓ.2) b).mp hb
        obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨b, hb⟩))
        have he := hβeq ℓ ⟨b, hb⟩ ⟨_, hv⟩ rfl x hx
        rw [hℓ] at he
        have hfix : β ⟨_, hv⟩ = β ⟨b, hb⟩ := by
          apply Multiplicative.toAdd.injective
          rw [← he, ← hx]
          congr 1
        have hmem : (⟨_, hv⟩ : ↥(Vq M L)) * (⟨b, hb⟩ : ↥(Vq M L))⁻¹ ∈ β.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hfix, mul_inv_cancel]
        rw [hβker, Subgroup.mem_subgroupOf] at hmem
        simpa using hmem
    exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hcomm)
  let act : ↥L → Multiplicative (AltHeart 6) → Multiplicative (AltHeart 6) :=
    fun ℓ y => Multiplicative.ofAdd
      (SBc9.heartAct ((α ℓ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
        (Multiplicative.toAdd y))
  have hact : ∀ (ℓ : ↥L) (u v : ↥(Vq M L)), (v : G) = ℓ * u * ℓ⁻¹ → β v = act ℓ (β u) := by
    intro ℓ u v huv
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
    have he := hβeq ℓ u v huv x hx
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (β v) = SBc9.heartAct _ (Multiplicative.toAdd (β u))
    rw [← hx, SBc9.heartAct_mk, he]
  have hirr : ∀ Y : Subgroup (Multiplicative (AltHeart 6)),
      (∀ (ℓ : ↥L) (y : Multiplicative (AltHeart 6)), y ∈ Y → act ℓ y ∈ Y) → Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    let Ya : AddSubgroup (AltHeart 6) :=
      { carrier := {a | Multiplicative.ofAdd a ∈ Y}
        add_mem' := fun {a b} ha hb => by
          show Multiplicative.ofAdd (a + b) ∈ Y
          rw [ofAdd_add]
          exact Y.mul_mem ha hb
        zero_mem' := by
          show Multiplicative.ofAdd (0 : AltHeart 6) ∈ Y
          rw [ofAdd_zero]
          exact Y.one_mem
        neg_mem' := fun {a} ha => by
          show Multiplicative.ofAdd (-a) ∈ Y
          rw [ofAdd_neg]
          exact Y.inv_mem ha }
    have hYa : ∀ σ ∈ alternatingGroup (Fin 6), ∀ y ∈ Ya, SBc9.heartAct σ y ∈ Ya := by
      intro σ hσ y hy
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, hσ⟩
      have := hY ℓ _ hy
      show Multiplicative.ofAdd (SBc9.heartAct σ y) ∈ Y
      have e : (((α ℓ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))) = σ := by
        rw [hℓ]
      rw [← e]
      exact this
    rcases heart6_irreducible Ya hYa with hb | ht
    · left
      refine eq_bot_iff.mpr fun y hy => ?_
      have : Multiplicative.toAdd y ∈ Ya := hy
      rw [hb, AddSubgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact this
    · right
      refine eq_top_iff.mpr fun y _ => ?_
      have : Multiplicative.toAdd y ∈ Ya := ht ▸ AddSubgroup.mem_top _
      exact this
  have hshort : IsShort2 L := by
    refine isShort2_of h hVX (lt_of_surjective_of_ker inf_le_left β hβ hβker)
      fun W hZW hWV hLW => ?_
    exact eq_or_eq_of_section β hβker act hact hirr hLV hZW hWV hLW
  refine ⟨hshort, (exists_isAltBlockTypeWith_iff_isAltNaturalSection L 6
    (le_normalizer_blockU h)).mpr ?_⟩
  rw [blockU_eq h, blockZ_eq h]
  exact ⟨hLV, α, hα, hpk, β, hβ, hβker, hβeq⟩

end CFSG.Quasithin.MS93
