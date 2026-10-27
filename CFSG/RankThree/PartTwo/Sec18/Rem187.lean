module

public import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.RankThree.PartTwo.KFacts.KS18SL34
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Rem187Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    H ∈ scriptHStar A M → CFSG.Open.pCoreOf 2 H ≠ ⊥ →
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ →
      ∃ H' : Subgroup G, ∃ c' : G, Sec18H G A M H' c' ∧ Hyp187 A M H' c'

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_bot_of_mem_oTwoComponentsIn {X K : Subgroup G} (hK : K ∈ oTwoComponentsIn X) :
    K ≠ ⊥ := by
  intro hbot
  have := CFSG.LocalCores.isQuasisimple_nontrivial (isQuasisimple_of_mem_oTwoComponentsIn hK)
  obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ CFSG.pCore 2 K)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have ha : (a : G) = 1 := (Subgroup.eq_bot_iff_forall K).mp hbot a a.2
  have hb : (b : G) = 1 := (Subgroup.eq_bot_iff_forall K).mp hbot b b.2
  rw [show a = b from Subtype.ext (ha.trans hb.symm)]

theorem eq_inSubgroup_perfectResidual_of_isSubnormal {X J : Subgroup G}
    (hX : inSubgroup perfectResidual X ∈ oTwoComponentsIn X) (hJX : J ≤ X)
    (hsn : (J.subgroupOf X).IsSubnormal) (hJ : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥) :
    J = inSubgroup perfectResidual X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual X with hLdef
  have hLX : L ≤ X := Subgroup.map_subtype_le _
  have hJL : J ≤ L := le_inSubgroup_perfectResidual hJ hJX
  have hsnL : (J.subgroupOf L).IsSubnormal := isSubnormal_subgroupOf_of_le hsn hLX
  have hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) := isQuasisimple_of_mem_oTwoComponentsIn hX
  set J₁ : Subgroup (L ⧸ CFSG.pCore 2 L) :=
    (J.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) with hJ₁
  have hJ₁sn : J₁.IsSubnormal := hsnL.map (QuotientGroup.mk'_surjective _)
  have hJp : Group.IsPerfect (J.subgroupOf L) :=
    (Subgroup.isPerfect_iff).mpr (commutator_subgroupOf_eq hJL hJ)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq hJ₁sn with
    htop | hcen
  ·
    have hsup' : J.subgroupOf L ⊔ CFSG.pCore 2 L = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 L)) (J.subgroupOf L)
      rw [← hJ₁, htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hO : (CFSG.pCore 2 L).map L.subtype = CFSG.Open.pCoreOf 2 L :=
      inSubgroup_pCore_eq_pCoreOf 2 L
    have hsup : J ⊔ CFSG.Open.pCoreOf 2 L = L := by
      have h2 := congrArg (Subgroup.map L.subtype) hsup'
      rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJL, hO, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h2
    have hQs : Group.IsSolvable (CFSG.Open.pCoreOf 2 L) := by
      have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).isNilpotent
      infer_instance
    have hres := inSubgroup_perfectResidual_eq_of_isSubnormal hJL
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      hQs hsnL hJ hsup
    have hLL : inSubgroup perfectResidual L = L :=
      le_antisymm (Subgroup.map_subtype_le _)
        (le_inSubgroup_perfectResidual (commutator_eq_of_mem_oTwoComponentsIn hX) le_rfl)
    rw [hLL] at hres
    exact hres.symm
  ·
    exfalso
    have hJ₁p : Group.IsPerfect J₁ :=
      Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' (CFSG.pCore 2 L)).subgroupMap
        (J.subgroupOf L)) (MonoidHom.subgroupMap_surjective _ _)
    have hcomm : IsMulCommutative J₁ :=
      (Subgroup.le_centralizer_iff_isMulCommutative).mp
        (hcen.trans (Subgroup.center_le_centralizer _))
    have hJ₁bot : J₁ = ⊥ := by
      by_contra hne
      have : Nontrivial J₁ := (Subgroup.nontrivial_iff_ne_bot J₁).mpr hne
      exact Group.IsPerfect.not_isMulCommutative J₁ hcomm
    have hle : J.subgroupOf L ≤ CFSG.pCore 2 L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 L), ← Subgroup.map_eq_bot_iff]
      exact hJ₁bot
    have hJ2 : IsPGroup 2 J :=
      ((CFSG.pCore_isPGroup (p := 2) (G := L)).to_le hle).of_equiv
        (Subgroup.subgroupOfEquivOfLe hJL)
    have hJs : Group.IsSolvable J := by
      have := hJ2.isNilpotent
      infer_instance
    have : Group.IsPerfect J := (Subgroup.isPerfect_iff).mpr hJ
    have : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
    exact Group.IsPerfect.not_isSolvable J hJs

theorem eq_of_mem_oTwoComponentsIn_of_mem_scriptH {A M H K : Subgroup G}
    (hH : H ∈ scriptH A M) (hK : K ∈ oTwoComponentsIn H) : K = inSubgroup perfectResidual H := by
  obtain ⟨hKH, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  exact eq_inSubgroup_perfectResidual_of_isSubnormal (mem_scriptH_iff_mem_scriptH₀.mp hH).1.2.1
    hKH hsn (commutator_eq_of_mem_oTwoComponentsIn hK) (ne_bot_of_mem_oTwoComponentsIn hK)

theorem pCoreOf_le_pCoreOf_of_eq_sup {K L : Subgroup G} (hKL : K ≤ L)
    (hsup : L = K ⊔ CFSG.Open.pCoreOf 2 L) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 K ⊔ CFSG.Open.pCoreOf 2 L with hP
  have hK2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hL2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hKO : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hKL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hP2 : IsPGroup 2 P :=
    hK2.to_sup_of_normal_right' hL2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKO)
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := by
    refine hsup.le.trans (sup_le (fun x hx => Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hx, hKO hx⟩) ?_)
    exact (le_sup_right : CFSG.Open.pCoreOf 2 L ≤ P).trans Subgroup.le_normalizer
  have hPL : P ≤ L :=
    sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKL)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPL hLP hP2)

theorem exists_mem_scriptHStar_pCoreOf_ne_bot (h182 : Item182) (hSL : KFacts.KS18SL34)
    {A M : Subgroup G} (h : Sec18Std G A M) {H₀ : Subgroup G} (hH₀ : H₀ ∈ scriptH A M)
    (hH₀2 : CFSG.Open.pCoreOf 2 H₀ ≠ ⊥) :
    ∃ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.isSimpleGroup
  set R₀ := CFSG.Open.pCoreOf 2 H₀ with hR₀
  have hR₀2 : IsPGroup 2 R₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀
  set X := Subgroup.normalizer (R₀ : Set G) with hX
  have hXtop : X ≠ ⊤ := normalizer_ne_top_of_isPGroup_two h.nonabelian hR₀2 hH₀2
  have hH₀X : H₀ ≤ X := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀
  obtain ⟨K, hK, -, hH₁, -⟩ := h182 G A M h H₀ hH₀ X hH₀X hXtop
  have hAH₀ := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH₀).1
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hH₁X : K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H₀ ⊓ M) ≤ X :=
    sup_le (sup_le hKX (hAH₀.trans hH₀X))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_left.trans hH₀X))
  have hKH₁ : K ≤ K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H₀ ⊓ M) := le_sup_left.trans le_sup_left
  obtain ⟨-, ⟨-, hsnX, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  have hKc : K ∈ oTwoComponentsIn (K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H₀ ⊓ M)) :=
    mem_oTwoComponentsIn_of_le hK hKH₁ (isSubnormal_subgroupOf_of_le hsnX hH₁X)
  have hKeq := eq_of_mem_oTwoComponentsIn_of_mem_scriptH hH₁ hKc
  have hK2 : CFSG.Open.pCoreOf 2 K ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_oTwoComponentsIn h.charTwoType ⟨R₀, hH₀2, hR₀2, rfl⟩ hK
  obtain ⟨H, hH₁H, hHmax⟩ :=
    Finite.exists_le_maximal (p := fun Y : Subgroup G => Y ∈ scriptH A M) hH₁
  have hH : H ∈ scriptH A M := hHmax.prop
  refine ⟨H, hHmax, ?_⟩
  obtain ⟨K', hK', -, -, hcase⟩ := h182 G A M h _ hH₁ H hH₁H hH.1
  have hK'eq := eq_of_mem_oTwoComponentsIn_of_mem_scriptH hH hK'
  rcases hcase with h1 | ⟨hL34, -, -, -, ⟨e⟩, -⟩
  ·
    rw [← hKeq, hK'eq] at h1
    have hle := pCoreOf_le_pCoreOf_of_eq_sup (le_sup_left.trans h1.symm.le) h1
    exact fun hbot => hK2 (le_bot_iff.mp (hbot ▸ hle))
  ·
    exfalso
    set L₁ := inSubgroup perfectResidual (K ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H₀ ⊓ M)) with hL₁
    have hKK' : L₁ ≤ K' := by
      rw [hK'eq, ← hKeq]
      exact le_inSubgroup_perfectResidual (commutator_eq_of_mem_oTwoComponentsIn hK)
        (hKH₁.trans hH₁H)
    set φ : L₁ →* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 K')).comp (Subgroup.inclusion hKK'))
      with hφ
    have hker : φ.ker ≤ CFSG.pCore 2 L₁ := by
      refine le_sSup ⟨inferInstance, ?_⟩
      have himg : φ.ker.map (Subgroup.inclusion hKK') ≤ CFSG.pCore 2 K' := by
        rintro _ ⟨k, hk, rfl⟩
        have hk1 : e (QuotientGroup.mk' (CFSG.pCore 2 K') (Subgroup.inclusion hKK' k)) = 1 := hk
        rw [← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk1
        exact hk1
      exact ((CFSG.pCore_isPGroup (p := 2) (G := K')).to_le himg).of_equiv
        (φ.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hKK')).symm
    exact (hSL L₁ φ (CFSG.pCore 2 L₁) (CFSG.pCore_isPGroup (p := 2) (G := L₁)) hker).false
      hL34.some

theorem rank3II_rem_18_7_of (h182 : Item182) (h1841 : Item184_1) (hSL : KFacts.KS18SL34)
    (hQ : Rem187Q) : Rem187 := by
  intro G _ _ A M h hex
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H₀, hH₀, hH₀2⟩ := hex
  obtain ⟨H, hH, hH2⟩ := exists_mem_scriptHStar_pCoreOf_ne_bot h182 hSL h hH₀ hH₀2
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
