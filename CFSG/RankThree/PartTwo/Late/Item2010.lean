module

public import CFSG.RankThree.PartTwo.Sec20.Statements
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec18.Item181
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec18

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_normal_isPGroup_two [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {R : Subgroup G} (hRn : R.Normal) (hR : IsPGroup 2 R) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hRn.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h] at hR
    have hG : IsPGroup 2 G := hR.of_equiv Subgroup.topEquiv
    have : Nontrivial G := IsSimpleGroup.toNontrivial
    have hc : (Subgroup.center G).Normal := inferInstance
    rcases hc.eq_bot_or_eq_top with h1 | h1
    · exact hG.bot_lt_center.ne' h1
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hb : b ∈ Subgroup.center G := h1 ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)

theorem ne_top_of_pCoreOf_ne_bot [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} (hH : CFSG.Open.pCoreOf 2 H ≠ ⊥) : H ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro rfl
  apply hH
  refine eq_bot_of_normal_isPGroup_two hnab ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤)
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤

theorem normalizer_ne_top_of_isPGroup_two [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    Subgroup.normalizer (R : Set G) ≠ ⊤ := by
  intro htop
  exact hR1 (eq_bot_of_normal_isPGroup_two hnab (Subgroup.normalizer_eq_top_iff.mp htop) hR)

omit [Finite G] in
theorem le_inSubgroup_pPrimeCore_of {p : ℕ} {Q X : Subgroup G}
    (hQ : Nat.Coprime p (Nat.card Q)) (hQX : Q ≤ X)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    Q ≤ inSubgroup (CFSG.pPrimeCore p) X := by
  have hn : (Q.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
  have hc : Nat.Coprime p (Nat.card (Q.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]
  have hle : Q.subgroupOf X ≤ CFSG.pPrimeCore p X := le_sSup ⟨hn, hc⟩
  intro x hx
  exact ⟨⟨x, hQX hx⟩, hle hx, rfl⟩

omit [Finite G] in
theorem le_normalizer_inSubgroup_pPrimeCore (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore p) X : Set G) := by
  have : (CFSG.pPrimeCore p X).Characteristic :=
    Subgroup.characteristic_iff_map_eq.mpr fun φ => CFSG.pPrimeCore_map_iso p φ
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)

theorem pCoreOf_inf_le_of_pPrimeCore_eq {X M : Subgroup G}
    (heq : inSubgroup (CFSG.pPrimeCore 3) X = inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M)) :
    CFSG.Open.pCoreOf 2 (X ⊓ M) ≤ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := inSubgroup (CFSG.pPrimeCore 3) X with hY
  set T := CFSG.Open.pCoreOf 2 (X ⊓ M) with hT
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTXM : T ≤ X ⊓ M := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hXMT : X ⊓ M ≤ Subgroup.normalizer (T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hTY : T ≤ Y := by
    rw [heq]
    exact le_inSubgroup_pPrimeCore_of hcop hTXM hXMT
  have hYXM : Y ≤ X ⊓ M := by
    rw [heq]
    exact Subgroup.map_subtype_le _
  have hTY2 : T ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTY (hYXM.trans hXMT) hT2
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_inSubgroup_pPrimeCore 3 X
  refine hTY2.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans (Subgroup.map_subtype_le _))
    (hXY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))

theorem pCoreOf_ne_bot_of_mem_oTwoComponentsIn (hchar : CFSG.Assembly.IsCharTwoType G)
    {X K : Subgroup G} (hX : CFSG.Assembly.IsTwoLocal X) (hK : K ∈ oTwoComponentsIn X) :
    CFSG.Open.pCoreOf 2 K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', ⟨-, hsn, hq⟩, rfl⟩ := hK
  intro hbot
  rw [pCoreOf_map X.subtype X.subtype_injective,
    Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective, CFSG.Open.pCoreOf,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hbot
  have hq' : CFSG.IsQuasisimple K' := by
    set e : K' ⧸ CFSG.pCore 2 K' ≃* K' :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    exact CFSG.LocalCores.isQuasisimple_of_surjective hq e.toMonoidHom e.surjective
      (by
        intro x hx
        have hx1 : e x = 1 := hx
        rw [show x = 1 from e.injective (by rw [hx1, map_one])]
        exact Subgroup.one_mem _)
  have hcen := CFSG.RankThreeCoreUniqueness.Helpers.charTwo_twoLocal_internal_self_centralizing_core
    hchar X hX
  have hcharP : CFSG.IsCharacteristicP 2 X := by
    change Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X
    exact hcen
  have hlayer := CFSG.layer_eq_bot_of_isCharacteristicP X 2 hcharP
  have hle : K' ≤ CFSG.layer X := le_sSup ⟨hq', hsn⟩
  rw [hlayer, le_bot_iff] at hle
  subst hle
  obtain ⟨-, hsimple, -⟩ := hq'
  have hnt := hsimple.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊥ : Subgroup X) ⧸ Subgroup.center ↥(⊥ : Subgroup X))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [Subsingleton.elim x y]

theorem pCoreOf_le_of_mem_oTwoComponentsIn {X K H₁ : Subgroup G} (hK : K ∈ oTwoComponentsIn X)
    (hKH : K ≤ H₁) (hH₁X : H₁ ≤ X) : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', ⟨-, hsn, -⟩, rfl⟩ := hK
  set H' : Subgroup X := H₁.subgroupOf X with hH'
  have hK'H' : K' ≤ H' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hKH (Subgroup.mem_map_of_mem X.subtype hx))
  have hW : (K'.subgroupOf H').IsSubnormal := hsn.subgroupOf
  have h1 := pCoreOf_le_pCore_of_isSubnormal 2 hW
  have h2 := Subgroup.map_mono (f := H'.subtype) h1
  rw [← CFSG.Open.pCoreOf, ← pCoreOf_map H'.subtype H'.subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK'H'] at h2
  have h3 := Subgroup.map_mono (f := X.subtype) h2
  rwa [← pCoreOf_map X.subtype X.subtype_injective, ← pCoreOf_map X.subtype X.subtype_injective,
    hH', Subgroup.map_subgroupOf_eq_of_le hH₁X] at h3

omit [Finite G] in
theorem le_of_isSylowOf_of_normal {R Y X S : Subgroup G} (hR : IsPGroup 2 R) (hRY : R ≤ Y)
    (hYX : Y ≤ X) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S Y) : R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hS
  have hn : (Subgroup.comap Y.subtype R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mpr (hYX.trans hXR)
  have hle : R.subgroupOf Y ≤ Q := (hR.comap_subtype (K := Y)).le_sylow_of_normal Q
  rw [← Subgroup.map_subgroupOf_eq_of_le hRY]
  exact Subgroup.map_mono hle

theorem rank3II_20_10_reduction (h181 : Item181_1) (hrem : Rem187)
    (h201 : Sec20.Item201Contra1) : Item2010 := by
  intro G _ _ hst hS A M H hA hM hAH hH2
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hst.isSimpleGroup
  have hAE : A ∈ partTwoE G := mem_partTwoE_of_le hA hM.1 (le_of_mem_scriptM_gamma hA hM)
  have h18 : Sec18Std G A M := ⟨hst, hS, hAE, hM⟩
  have hle := pCoreOf_le_pCoreOf_inf h18 hAH
  have hO : inSubgroup (CFSG.pPrimeCore 3) H ≠ inSubgroup (CFSG.pPrimeCore 3) (H ⊓ M) :=
    fun heq => hne (le_antisymm (pCoreOf_inf_le_of_pPrimeCore_eq heq) hle)
  have hHtop := ne_top_of_pCoreOf_ne_bot hst.nonabelian hH2
  obtain ⟨L₀, hL₀, S₀, hS₀, hH₀⟩ := h181 G A M h18 H hAH hHtop hO
  have hH₀H : L₀ ⊔ A ⊔ S₀ ≤ H :=
    sup_le (sup_le (le_of_mem_oTwoComponentsIn hL₀) hAH)
      (hS₀.le.trans ((Subgroup.map_subtype_le _).trans inf_le_left))
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hRHM : R ≤ H ⊓ M :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hle.trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right))
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hRY : R ≤ inSubgroup (CFSG.pPrimeCore 3) (H ⊓ M) :=
    le_inSubgroup_pPrimeCore_of hcop hRHM (inf_le_left.trans hHR)
  have hRS₀ : R ≤ S₀ :=
    le_of_isSylowOf_of_normal hR2 hRY ((Subgroup.map_subtype_le _).trans inf_le_left) hHR hS₀
  have hRH₀ : R ≤ CFSG.Open.pCoreOf 2 (L₀ ⊔ A ⊔ S₀) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRS₀.trans le_sup_right)
      (hH₀H.trans hHR) hR2
  have hH₀2 : CFSG.Open.pCoreOf 2 (L₀ ⊔ A ⊔ S₀) ≠ ⊥ :=
    fun h => hH2 (le_bot_iff.mp (h ▸ hRH₀))
  obtain ⟨H₂, c, hH₂, hstar, hH₂2, hchoice⟩ := hrem G A M h18 ⟨_, hH₀, hH₀2⟩
  exact h201 G A M _ _ c ⟨⟨hst, hS, hAE, hM, Or.inl ⟨H₂, hstar, hH₂2, rfl, rfl, hchoice⟩,
    hH₂.centralizer_eq⟩, H₂, hstar, hH₂2, rfl, rfl, hchoice⟩

theorem rank3II_20_11_of_items (h444 : Sec4.Item4_44_1) (hrem : Rem187)
    (h201 : Sec20.Item201Contra1) (h1912 : Item1912) : Item2011 :=
  item2011_of_item2010_item1912
    (rank3II_20_10_reduction (rank3II_18_1_1_of h444) hrem h201) h1912

end CFSG.RankThree.PartTwo.Late
