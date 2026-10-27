module

public import CFSG.RankThree.PartTwo.Sec18.Rem187
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLUsed

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

namespace Rem187Bypass

theorem exists_mem_oTwoComponentsIn_of_item4443 (h444 : Sec4.Item4_44_3) {A M : Subgroup G}
    (h : Sec18Std G A M) {H : Subgroup G} (hH : H ∈ scriptH A M) {X : Subgroup G}
    (hHX : H ≤ X) (hX : X ≠ ⊤) :
    ∃ K ∈ oTwoComponentsIn X, ¬ K ≤ M ∧
      (K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K ∨
        (Nonempty (inSubgroup perfectResidual H ⧸
            CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) ∧
          ∃ J ∈ oTwoComponentsIn X, ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J ∧
            Nonempty (K ⧸ CFSG.pCore 2 K ≃*
              Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
            ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
              Sec4.IsExtOf (J ⧸ CFSG.pCore 2 J) CFSG.Blueprint.NativeSporadic.M22
                (Multiplicative (ZMod 3))))) := by
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAX : A ≤ X := hAH.trans hHX
  have hXM : X ⊓ M ≠ X := by
    intro heq
    apply inf_ne_of_mem_scriptH₀ hH₀
    exact inf_eq_left.mpr (hHX.trans (inf_eq_left.mp heq))
  have hctx := ctx444_subgroupOf h hAX hX hXM
  obtain ⟨K', hK', hK'M, hcase⟩ :=
    h444 X _ _ hctx (H.subgroupOf X) (subgroupOf_mem_scriptH₀ hAX hHX hH)
  set K := K'.map X.subtype with hKdef
  have hK : K ∈ oTwoComponentsIn X := ⟨K', hK', rfl⟩
  have hKM : ¬ K ≤ M := by
    intro hle
    apply hK'M
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hle (Subgroup.mem_map_of_mem X.subtype hx)⟩
  have hres : (inSubgroup perfectResidual (H.subgroupOf X)).map X.subtype =
      inSubgroup perfectResidual H := by
    rw [← inSubgroup_perfectResidual_map X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hHX]
  have hO2 : (inSubgroup (CFSG.pCore 2) K').map X.subtype = CFSG.Open.pCoreOf 2 K := by
    rw [inSubgroup_pCore_eq_pCoreOf, ← pCoreOf_map X.subtype X.subtype_injective]
  refine ⟨K, hK, hKM, ?_⟩
  rcases hcase with hi | ⟨hL34, J', hJ', hLX, hK34, hJ⟩
  ·
    have hKL : K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K := by
      conv_lhs => rw [hKdef, hi]
      rw [Subgroup.map_sup, hres, hO2]
    exact Or.inl hKL
  ·
    right
    set J := J'.map X.subtype
    have hJm : J ∈ oTwoComponentsIn X := ⟨J', hJ', rfl⟩
    have hiso : ∀ (Y : Type) [Group Y], ∀ W : Subgroup X,
        Nonempty (W ⧸ CFSG.pCore 2 W ≃* Y) →
          Nonempty ((W.map X.subtype : Subgroup G) ⧸ CFSG.pCore 2 (W.map X.subtype) ≃* Y) := by
      intro Y _ W ⟨φ⟩
      set e : W ≃* (W.map X.subtype : Subgroup G) := W.equivMapOfInjective _ X.subtype_injective
      exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).symm.trans φ⟩
    have hL34' : Nonempty (inSubgroup perfectResidual H ⧸
        CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2)) := by
      have := hiso _ _ hL34
      rwa [hres] at this
    have hLX' : ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J := by
      have h1 := congrArg (Subgroup.map X.subtype) hLX
      rwa [Subgroup.map_commutator, hres, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        Subgroup.map_sup] at h1
    refine ⟨hL34', J, hJm, hLX', hiso _ K' hK34, ?_⟩
    rcases hJ with ⟨n, hn, hJn⟩ | ⟨N, hN, hNiso, hq⟩
    · exact Or.inl ⟨n, hn, hiso _ J' hJn⟩
    · right
      set e : J' ≃* J := J'.equivMapOfInjective _ X.subtype_injective
      set φ := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
      have hN' : (N.map φ.toMonoidHom).Normal := hN.map _ φ.surjective
      exact ⟨N.map φ.toMonoidHom, hN',
        ⟨(N.equivMapOfInjective _ φ.injective).symm.trans hNiso.some⟩,
        ⟨(QuotientGroup.congr N (N.map φ.toMonoidHom) φ rfl).symm.trans hq.some⟩⟩

theorem exists_mem_oTwoComponentsIn_of_item4443SLUsed (h444 : Sec4.Item4_44_3SLUsed)
    {A M : Subgroup G} (h : Sec18Std G A M) {H : Subgroup G} (hH : H ∈ scriptH A M)
    {X : Subgroup G} (hHX : H ≤ X) (hX : X ≠ ⊤)
    (hSL : Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) :
    ∃ K ∈ oTwoComponentsIn X, K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K := by
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAX : A ≤ X := hAH.trans hHX
  have hXM : X ⊓ M ≠ X := by
    intro heq
    apply inf_ne_of_mem_scriptH₀ hH₀
    exact inf_eq_left.mpr (hHX.trans (inf_eq_left.mp heq))
  have hctx := ctx444_subgroupOf h hAX hX hXM
  have hres : (inSubgroup perfectResidual (H.subgroupOf X)).map X.subtype =
      inSubgroup perfectResidual H := by
    rw [← inSubgroup_perfectResidual_map X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hHX]
  have hSLX : Nonempty (inSubgroup perfectResidual (H.subgroupOf X) ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual (H.subgroupOf X)) ≃*
        Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
    obtain ⟨φ⟩ := hSL
    set W := inSubgroup perfectResidual (H.subgroupOf X)
    set e : W ≃* (inSubgroup perfectResidual H : Subgroup G) :=
      (W.equivMapOfInjective _ X.subtype_injective).trans (MulEquiv.subgroupCongr hres)
    exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).trans φ⟩
  obtain ⟨K', hK', hi⟩ :=
    h444 X _ _ hctx (H.subgroupOf X) (subgroupOf_mem_scriptH₀ hAX hHX hH) hSLX
  set K := K'.map X.subtype with hKdef
  have hO2 : (inSubgroup (CFSG.pCore 2) K').map X.subtype = CFSG.Open.pCoreOf 2 K := by
    rw [inSubgroup_pCore_eq_pCoreOf, ← pCoreOf_map X.subtype X.subtype_injective]
  refine ⟨K, ⟨K', hK', rfl⟩, ?_⟩
  conv_lhs => rw [hKdef, hi]
  rw [Subgroup.map_sup, hres, hO2]

theorem exists_mem_scriptH_pCoreOf_ne_bot {A M : Subgroup G} (h : Sec18Std G A M)
    {H₀ : Subgroup G} (hH₀ : H₀ ∈ scriptH A M) (hH₀2 : CFSG.Open.pCoreOf 2 H₀ ≠ ⊥) :
    ∃ H₁ ∈ scriptH A M, H₀ ≤ H₁ ∧
      CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H₁) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R₀ := CFSG.Open.pCoreOf 2 H₀
  have hR₀2 : IsPGroup 2 R₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀
  set X := Subgroup.normalizer (R₀ : Set G)
  have hX2 : CFSG.Assembly.IsTwoLocal X := ⟨R₀, hH₀2, hR₀2, rfl⟩
  have hH₀X : H₀ ≤ X := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀
  set R := CFSG.Open.pCoreOf 2 X
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hR₀R : R₀ ≤ R := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 H₀).trans hH₀X) le_rfl hR₀2
  have hR1 : R ≠ ⊥ := fun hbot => hH₀2 (le_bot_iff.mp (hbot ▸ hR₀R))
  have hH₀R : H₀ ≤ Subgroup.normalizer (R : Set G) :=
    hH₀X.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  refine ⟨H₀ ⊔ R, sup_mem_scriptH h hH₀ hR2 hR1 hH₀R, le_sup_left, fun hbot => ?_⟩
  set L := inSubgroup perfectResidual H₀
  set N := inSubgroup perfectResidual (H₀ ⊔ R)
  have hLc : L ∈ oTwoComponentsIn H₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH₀).1.2.1
  have hLH₀ : L ≤ H₀ := Subgroup.map_subtype_le _
  have hLN : L ≤ N :=
    le_inSubgroup_perfectResidual (commutator_eq_of_mem_oTwoComponentsIn hLc)
      (hLH₀.trans le_sup_left)
  have hNY : N ≤ H₀ ⊔ R := Subgroup.map_subtype_le _
  have hYN : H₀ ⊔ R ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inSubgroup_perfectResidual _
  have hNR : N ≤ Subgroup.normalizer (R : Set G) :=
    hNY.trans (sup_le hH₀R Subgroup.le_normalizer)
  have hNR1 : N ⊓ R ≤ ⊥ := by
    rw [← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hNR hx⟩)
      (hR2.to_le inf_le_right)
  have hLC : L ≤ Subgroup.centralizer (R : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hlr : l * r * l⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hH₀R (hLH₀ hl)) r).mp hr
    have hrl : r * l⁻¹ * r⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hYN ((le_sup_right : R ≤ H₀ ⊔ R) hr)) l⁻¹).mp
        (N.inv_mem (hLN hl))
    have hc : l * r * l⁻¹ * r⁻¹ ∈ N ⊓ R := by
      refine Subgroup.mem_inf.mpr ⟨?_, R.mul_mem hlr (R.inv_mem hr)⟩
      have := N.mul_mem (hLN hl) hrl
      simpa only [mul_assoc] using this
    have hc1 : l * r * l⁻¹ * r⁻¹ = 1 := Subgroup.mem_bot.mp (hNR1 hc)
    calc r * l = (l * r * l⁻¹ * r⁻¹)⁻¹ * (l * r) := by group
      _ = l * r := by rw [hc1, inv_one, one_mul]
  have hLR : L ≤ R := fun x hx => h.charTwoType X hX2 ⟨hH₀X (hLH₀ hx), hLC hx⟩
  have : Nontrivial L :=
    (Subgroup.nontrivial_iff_ne_bot L).mpr (ne_bot_of_mem_oTwoComponentsIn hLc)
  have : Group.IsPerfect L := isPerfect_of_mem_oTwoComponentsIn hLc
  exact Group.IsPerfect.not_isNilpotent L (hR2.to_le hLR).isNilpotent

theorem pCoreOf_perfectResidual_le_of_le (h1841 : Item184_1)
    {A M : Subgroup G} (h : Sec18Std G A M) {H₁ H : Subgroup G} (hH₁ : H₁ ∈ scriptH A M)
    (hH : H ∈ scriptH A M) (hle : H₁ ≤ H) :
    CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H₁) ≤
      CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := inSubgroup perfectResidual H₁
  set K := inSubgroup perfectResidual H
  have hL₁K : L₁ ≤ K := inSubgroup_perfectResidual_mono hle
  obtain ⟨⟨e₁⟩, -⟩ := h1841 G A M h H₁ hH₁
  obtain ⟨⟨e⟩, -⟩ := h1841 G A M h H hH
  set φ : L₁ →* K ⧸ CFSG.pCore 2 K :=
    (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hL₁K)
  have hker : φ.ker ≤ CFSG.pCore 2 L₁ := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have himg : φ.ker.map (Subgroup.inclusion hL₁K) ≤ CFSG.pCore 2 K := by
      rintro _ ⟨k, hk, rfl⟩
      have hk1 : QuotientGroup.mk' (CFSG.pCore 2 K) (Subgroup.inclusion hL₁K k) = 1 := hk
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
    exact ((CFSG.pCore_isPGroup (p := 2) (G := K)).to_le himg).of_equiv
      (φ.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hL₁K)).symm
  have hq : Nat.card (L₁ ⧸ CFSG.pCore 2 L₁) = Nat.card (K ⧸ CFSG.pCore 2 K) :=
    Nat.card_congr (e₁.trans e.symm).toEquiv
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  have h2 := Subgroup.card_mul_index (CFSG.pCore 2 L₁)
  rw [Subgroup.index_eq_card, hq] at h2
  have hr : Nat.card φ.range ≤ Nat.card (K ⧸ CFSG.pCore 2 K) := Subgroup.card_le_card_group _
  have hge : Nat.card (CFSG.pCore 2 L₁) ≤ Nat.card φ.ker := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := K ⧸ CFSG.pCore 2 K))
    calc Nat.card (CFSG.pCore 2 L₁) * Nat.card (K ⧸ CFSG.pCore 2 K) = Nat.card L₁ := h2
      _ = Nat.card φ.ker * Nat.card φ.range := h1.symm
      _ ≤ Nat.card φ.ker * Nat.card (K ⧸ CFSG.pCore 2 K) := Nat.mul_le_mul_left _ hr
  have hkeq : φ.ker = CFSG.pCore 2 L₁ := Subgroup.eq_of_le_of_card_ge hker hge
  intro x hx
  have hxL : x ∈ L₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 L₁ hx
  have hy : (⟨x, hxL⟩ : L₁) ∈ φ.ker := hkeq ▸ (mem_pCore_iff_mem_pCoreOf _).mpr hx
  have hy1 : QuotientGroup.mk' (CFSG.pCore 2 K) (Subgroup.inclusion hL₁K ⟨x, hxL⟩) = 1 := hy
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy1
  exact (mem_pCore_iff_mem_pCoreOf _).mp hy1

theorem exists_mem_scriptHStar_pCoreOf_ne_bot (h1841 : Item184_1)
    {A M : Subgroup G} (h : Sec18Std G A M) {H₀ : Subgroup G} (hH₀ : H₀ ∈ scriptH A M)
    (hH₀2 : CFSG.Open.pCoreOf 2 H₀ ≠ ⊥) :
    ∃ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≠ ⊥ := by
  obtain ⟨H₁, hH₁, -, hH₁2⟩ := exists_mem_scriptH_pCoreOf_ne_bot h hH₀ hH₀2
  obtain ⟨H, hH₁H, hHmax⟩ :=
    Finite.exists_le_maximal (p := fun Y : Subgroup G => Y ∈ scriptH A M) hH₁
  refine ⟨H, hHmax, fun hbot => hH₁2 (le_bot_iff.mp ?_)⟩
  rw [← hbot]
  exact pCoreOf_perfectResidual_le_of_le h1841 h hH₁ hHmax.prop hH₁H

end Rem187Bypass

theorem rank3II_rem_18_7_of_item184 (h1841 : Item184_1) (hQ : Rem187Q) : Rem187 := by
  intro G _ _ A M h hex
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H₀, hH₀, hH₀2⟩ := hex
  obtain ⟨H, hH, hH2⟩ := Rem187Bypass.exists_mem_scriptHStar_pCoreOf_ne_bot h1841 h hH₀ hH₀2
  obtain ⟨-, c, -, hc⟩ := h1841 G A M h H hH.prop
  have hHc : Sec18H G A M H c := ⟨h, hH.prop, hc⟩
  have hO2H : CFSG.Open.pCoreOf 2 H ≠ ⊥ := by
    have hle : CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ CFSG.Open.pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.map_subtype_le _))
        ((le_normalizer_inSubgroup_perfectResidual H).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact fun hbot => hH2 (le_bot_iff.mp (hbot ▸ hle))
  by_cases hC : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥
  · exact ⟨H, c, hHc, hH, hO2H, fun hne => absurd hC hne⟩
  · exact hQ G A M H c hHc hH hO2H hC

end CFSG.RankThree.PartTwo.Sec18
