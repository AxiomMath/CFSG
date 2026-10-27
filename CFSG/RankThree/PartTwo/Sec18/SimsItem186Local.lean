module

public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.RankThree.PartTwo.Sec18.Item186Two
import CFSG.RankThree.PartTwo.Sec18.Item186Three
import CFSG.RankThree.PartTwo.Sec18.Item186Rank
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec5.Items52

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item186HProof

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem mem_oTwoComponentsIn_of_le (hAlt : Item182Alt1At H) (h : Sec18Std G A M)
    (hH : H ∈ scriptHStar A M) {X : Subgroup G} (hHX : H ≤ X) (hX : X ≠ ⊤) :
    inSubgroup perfectResidual H ∈ oTwoComponentsIn X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hLdef
  obtain ⟨K, hK, hKL⟩ := hAlt X hHX hX
  have hXH : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 H :=
    le_pCoreOf_of_mem_scriptHStar h hH (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      (hHX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hQK : CFSG.Open.pCoreOf 2 K ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK).trans
      (hXH.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHL))
  have hLK : L ≤ K := hKL ▸ le_sup_left
  have hQKK : CFSG.Open.pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := by
    rw [hKL]
    exact sup_le Subgroup.le_normalizer hQK
  haveI hLn : (L.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKN
  have hQs : Group.IsSolvable (CFSG.Open.pCoreOf 2 K) := by
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).isNilpotent
    infer_instance
  have hq : Group.IsSolvable (K ⧸ L.subgroupOf K) :=
    isSolvable_quotient_of_sup_eq hLK hQKK hKN hKL.symm hQs
  have hKle : K ≤ L := by
    have h1 := inSubgroup_perfectResidual_le_of_isSolvable hLK hq
    have h2 : K ≤ inSubgroup perfectResidual K :=
      le_inSubgroup_perfectResidual (commutator_eq_of_mem_oTwoComponentsIn hK) le_rfl
    exact h2.trans h1
  rwa [le_antisymm hKle hLK] at hK

theorem pCoreOf_perfectResidual_ne_bot (hAlt : Item182Alt1At H) (h : Sec18Std G A M)
    (hH : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.isSimpleGroup
  set Q := CFSG.Open.pCoreOf 2 H with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hX : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (Q : Set G)) := ⟨Q, hH2, hQ2, rfl⟩
  exact Late.pCoreOf_ne_bot_of_mem_oTwoComponentsIn h.charTwoType hX
    (mem_oTwoComponentsIn_of_le hAlt h hH (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
      (normalizer_ne_top_of_isPGroup_two h.nonabelian hQ2 hH2))

theorem pCoreOf_ne_bot_of_isCoatom (hAlt : Item182Alt1At H) (h : Sec18Std G A M)
    (hH : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) {X : Subgroup G}
    (hX : IsCoatom X) (hHX : H ≤ X) : CFSG.Open.pCoreOf 2 X ≠ ⊥ := by
  intro hbot
  apply pCoreOf_perfectResidual_ne_bot hAlt h hH hH2
  rw [eq_bot_iff, ← hbot]
  exact pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn (mem_oTwoComponentsIn_of_le hAlt h hH hHX hX.1)

theorem eq_normalizer_of_isCoatom (hAlt : Item182Alt1At H) (h : Sec18Std G A M)
    (hH : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) {X : Subgroup G}
    (hX : IsCoatom X) (hHX : H ≤ X) :
    X = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
  have : IsSimpleGroup G := h.isSimpleGroup
  rcases hX.le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) with htop | heq
  · exact absurd htop (normalizer_ne_top_of_isPGroup_two h.nonabelian
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      (pCoreOf_ne_bot_of_isCoatom hAlt h hH hH2 hX hHX))
  · exact heq.symm

section Certified


theorem le_normalizer_of_isCoatom (h1812 : Item181_2) (h184 : Item184_1)
    (hAlt : Item182Alt1At H) (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M)
    (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) {X : Subgroup G} (hX : IsCoatom X) (hHX : H ≤ X) :
    X ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have h := hH.toSec18Std
  set L := inSubgroup perfectResidual H with hLdef
  set B := A ⊓ L with hBdef
  set Q := CFSG.Open.pCoreOf 2 X with hQdef
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hLX : L ∈ oTwoComponentsIn X := mem_oTwoComponentsIn_of_le hAlt h hHs hHX hX.1
  have hLXle : L ≤ X := (Subgroup.map_subtype_le _).trans hHX
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isCoatom hAlt h hHs hH2 hX hHX
  have hB9 : Nat.card B = 9 := card_inf_of_sec18H h1812 h184 hH
  have hBe : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => hA.1.2 b hb.1
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨b, hb.1⟩ ⟨b', hb'.1⟩)
  intro x hx
  by_contra hxN
  set J := L.map (MulAut.conj x).toMonoidHom with hJdef
  have hJ : J ∈ oTwoComponentsIn X := map_conj_mem_oTwoComponentsIn hLX hx
  have hJL : J ≠ L := fun heq => hxN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  set B' := B.map (MulAut.conj x).toMonoidHom with hB'def
  have hconj : ∀ g : G, (MulAut.conj x).toMonoidHom g = x * g * x⁻¹ := fun g => rfl
  have hQx : ∀ q ∈ Q, x⁻¹ * q * x ∈ Q := fun q hq => by
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx)) q).mp hq
    rwa [inv_inv] at h1
  have h4 := Item186Proof.four_le_localRank_of_pair hQ hLX hJ hJL inf_le_right hBe hBc hB9.ge
    (Subgroup.map_mono inf_le_right)
    (by
      rintro _ ⟨b, hb, rfl⟩
      rw [hconj, conj_pow, hBe b hb, mul_one, mul_inv_cancel])
    (by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      simp only [hconj]
      calc x * b * x⁻¹ * (x * b' * x⁻¹) = x * (b * b') * x⁻¹ := by group
        _ = x * (b' * b) * x⁻¹ := by rw [hBc b hb b' hb']
        _ = x * b' * x⁻¹ * (x * b * x⁻¹) := by group)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]; exact hB9.ge)
    (by
      rintro _ ⟨b, hb, rfl⟩ hcomm
      have hb1 : b = 1 := by
        refine Item186Proof.eq_one_of_commutator_mem h184 hH hLXle hb.1 hb.2 fun l hl => ?_
        have h1 := hcomm (x * l * x⁻¹) ⟨l, hl, rfl⟩
        simp only [hconj] at h1
        have h2 := hQx _ h1
        have e : x⁻¹ * (x * b * x⁻¹ * (x * l * x⁻¹) * (x * b * x⁻¹)⁻¹ * (x * l * x⁻¹)⁻¹) * x =
            b * l * b⁻¹ * l⁻¹ := by group
        rwa [e] at h2
      rw [hconj, hb1, mul_one, mul_inv_cancel])
  have h3 := h.toTheoremFourHyp.localRank_three
  omega

theorem eq_normalizer_perfectResidual_of_isCoatom (h1812 : Item181_2) (h184 : Item184_1)
    (hAlt : Item182Alt1At H) (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M)
    (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) {X : Subgroup G} (hX : IsCoatom X) (hHX : H ≤ X) :
    X = Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have h := hH.toSec18Std
  have : IsSimpleGroup G := h.isSimpleGroup
  rcases hX.le_iff.mp (le_normalizer_of_isCoatom h1812 h184 hAlt hH hHs hH2 hX hHX) with htop | heq
  · exfalso
    set L := inSubgroup perfectResidual H
    have hLn : L.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hLn.eq_bot_or_eq_top with hL | hL
    · exact pCoreOf_perfectResidual_ne_bot hAlt h hHs hH2
        (eq_bot_iff.mpr ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hL.le))
    · exact hX.1 (eq_top_iff.mpr (hL.ge.trans ((Subgroup.map_subtype_le _).trans hHX)))
  · exact heq.symm

theorem isCoatom_normalizer (h1812 : Item181_2) (h184 : Item184_1) (hAlt : Item182Alt1At H)
    (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    IsCoatom (Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) := by
  obtain ⟨X, hX, hHX⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hHs.prop.1
  rw [← eq_normalizer_perfectResidual_of_isCoatom h1812 h184 hAlt hH hHs hH2 hX hHX]
  exact hX

theorem scriptN_eq (h1812 : Item181_2) (h184 : Item184_1) (hAlt : Item182Alt1At H)
    (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    scriptN (H : Set G) = {Subgroup.normalizer (inSubgroup perfectResidual H : Set G)} := by
  ext X
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hX, hHX⟩
    exact eq_normalizer_perfectResidual_of_isCoatom h1812 h184 hAlt hH hHs hH2 hX hHX
  · rintro rfl
    exact ⟨isCoatom_normalizer h1812 h184 hAlt hH hHs hH2,
      le_normalizer_inSubgroup_perfectResidual H⟩

theorem isMaximalTwoLocal_normalizer (h1812 : Item181_2) (h184 : Item184_1)
    (hAlt : Item182Alt1At H) (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M)
    (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    IsMaximalTwoLocal (Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) := by
  have h := hH.toSec18Std
  have : IsSimpleGroup G := h.isSimpleGroup
  set N := Subgroup.normalizer (inSubgroup perfectResidual H : Set G) with hN
  have hNc := isCoatom_normalizer h1812 h184 hAlt hH hHs hH2
  have hHN : H ≤ N := le_normalizer_inSubgroup_perfectResidual H
  refine ⟨⟨CFSG.Open.pCoreOf 2 N, pCoreOf_ne_bot_of_isCoatom hAlt h hHs hH2 hNc hHN,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N,
    eq_normalizer_of_isCoatom hAlt h hHs hH2 hNc hHN⟩, fun Y hNY hY => ?_⟩
  obtain ⟨P, hP1, hP2, hYP⟩ := hY
  have hYtop : Y = ⊤ := hNc.2 Y hNY
  exact normalizer_ne_top_of_isPGroup_two h.nonabelian hP2 hP1 (hYP ▸ hYtop)

theorem normalizer_le_normalizer (h1812 : Item181_2) (h1813 : Item181_3) (h184 : Item184_1)
    (hAlt : Item182Alt1At H) (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M)
    (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hH.toSec18Std
  have : IsSimpleGroup G := h.isSimpleGroup
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  obtain ⟨⟨C, hCc, hC1, hHC⟩, -⟩ := h1813 G A M h H hH.mem_scriptH
    (generalizedFitting_eq_of_mem_scriptHStar h hHs hH2)
  set C' := C.map S.subtype with hC'
  have hC'2 : IsPGroup 2 C' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).to_le (Subgroup.map_subtype_le C)
  have hC'1 : C' ≠ ⊥ := fun hb =>
    hC1 ((Subgroup.map_eq_bot_iff_of_injective C (Subgroup.subtype_injective S)).mp hb)
  obtain ⟨X, hX, hCX⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (Subgroup.normalizer (C' : Set G))).resolve_left
    (normalizer_ne_top_of_isPGroup_two h.nonabelian hC'2 hC'1)
  have hXeq := eq_normalizer_perfectResidual_of_isCoatom h1812 h184 hAlt hH hHs hH2 hX
    (hHC.trans hCX)
  haveI := hCc
  exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic C).trans
    (hCX.trans hXeq.le)

theorem mem_maxInvariantPiSubgroups (h1812 : Item181_2) (h1813 : Item181_3) (h184 : Item184_1)
    (hAlt : Item182Alt1At H) (hH : Sec18H G A M H c) (hHs : H ∈ scriptHStar A M)
    (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) :
    CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hH.toSec18Std
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M) with hSdef
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    Item186Proof.le_normalizer_pCoreOf_inf h hH.mem_scriptH
  have hNS := normalizer_le_normalizer h1812 h1813 h184 hAlt hH hHs hH2
  rw [mem_maxInvariantPiSubgroups_iff, mem_invariantPiSubgroups_piOf_iff Nat.prime_two]
  refine ⟨⟨le_top, hS2, hAS⟩, fun Y hY hSY => ?_⟩
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hY
  obtain ⟨-, hY2, hAY⟩ := hY
  by_contra hne
  have hgrow := Sec5.lt_inf_normalizer_of_lt hY2 (lt_of_le_of_ne hSY (Ne.symm hne))
  have hAU : A ≤ Subgroup.normalizer ((Y ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) :
      Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAY ha, Subgroup.le_normalizer (hAS ha)⟩
  exact hgrow.not_ge (Item186Proof.le_of_le_normalizer h1812 h184 hH hHs (hY2.to_le inf_le_left)
    hAU hgrow.le (inf_le_right.trans hNS))

end Certified

end Item186HProof

section Certified


theorem item186_of_item182Alt1At (h1812 : Item181_2) (h1813 : Item181_3) (h184 : Item184_1)
    {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} (hH : Sec18H G A M H c)
    (hHs : H ∈ scriptHStar A M) (hH2 : CFSG.Open.pCoreOf 2 H ≠ ⊥) (hAlt : Item182Alt1At H) :
    CFSG.generalizedFitting H = CFSG.pCore 2 H ∧
      (CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) ∧
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) ≤
          Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) ∧
      scriptN (H : Set G) = {Subgroup.normalizer (inSubgroup perfectResidual H : Set G)} ∧
        IsMaximalTwoLocal (Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) :=
  ⟨generalizedFitting_eq_of_mem_scriptHStar hH.toSec18Std hHs hH2,
    ⟨Item186HProof.mem_maxInvariantPiSubgroups h1812 h1813 h184 hAlt hH hHs hH2,
      Item186HProof.normalizer_le_normalizer h1812 h1813 h184 hAlt hH hHs hH2⟩,
    Item186HProof.scriptN_eq h1812 h184 hAlt hH hHs hH2,
    Item186HProof.isMaximalTwoLocal_normalizer h1812 h184 hAlt hH hHs hH2⟩

end Certified

end CFSG.RankThree.PartTwo.Sec18
