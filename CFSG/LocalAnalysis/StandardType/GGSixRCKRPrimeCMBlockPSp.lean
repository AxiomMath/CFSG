module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMConverseSU
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)


theorem rckIsComponentOf_map_subtype_of_top {G : Type*} [Group G]
    {Y : Subgroup G} {K : Subgroup ↥Y} (h : CFSG.Open.IsComponentOf K ⊤) :
    CFSG.Assembly.IsComponentOf (K.map Y.subtype) Y := by
  have hA : CFSG.Assembly.IsComponentOf K ⊤ :=
    ⟨le_top, (CFSG.Assembly.isSubnormal_iff_open).2 h.2.1, h.2.2⟩
  have hsub : CFSG.Assembly.IsSubnormal (K.map Y.subtype)
      ((⊤ : Subgroup ↥Y).map Y.subtype) :=
    hA.2.1.map Y.subtype
  rw [Subgroup.map_top, Subgroup.range_subtype] at hsub
  exact ⟨Subgroup.map_subtype_le K, hsub,
    (CFSG.Assembly.IsQuasisimple.congr
      (Subgroup.equivMapOfInjective K Y.subtype Y.subtype_injective)).mp hA.2.2⟩

private theorem rckBlockModel_PSp_spCase {n f n₁ : ℕ} (hf : 1 ≤ f)
    {H : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {C : Subgroup ↥H} (hCo : CFSG.Open.IsComponentOf C ⊤)
    {Φ : ↥H ≃* ↥(CFSG.Open.StatedSp n₁ (GaloisField 2 f))} :
    (∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →* ↥H),
      RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m g κ) ∨
    (Nat.card (GaloisField 2 f) = 2 ∧
      Nonempty (↥H ≃* ↥(CFSG.Open.StatedSp 2 (GaloisField 2 f)))) := by
  have hmap : CFSG.Open.IsComponentOf (C.map Φ.toMonoidHom) ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv Φ hCo
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr Φ.surjective] at h
  by_cases hsmall : n₁ = 0 ∨ (n₁ = 1 ∧ Nat.card (GaloisField 2 f) = 2)
  · exfalso
    exact (not_isComponentOf_statedSp_of_small (K := GaloisField 2 f) hsmall _)
      (rckIsComponentOf_map_subtype_of_top hmap)
  · by_cases h22 : n₁ = 2 ∧ Nat.card (GaloisField 2 f) = 2
    · obtain ⟨rfl, hcard⟩ := h22
      exact Or.inr ⟨hcard, ⟨Φ⟩⟩
    · have hm : 1 ≤ n₁ := by
        rcases Nat.eq_zero_or_pos n₁ with h | h
        · exact absurd (Or.inl h) hsmall
        · exact h
      have h1 : ¬ (n₁ = 1 ∧ Nat.card (GaloisField 2 f) = 2) :=
        fun h => hsmall (Or.inr h)
      have hq : CFSG.Assembly.IsQuasisimple
          ↥(CFSG.Open.StatedSp n₁ (GaloisField 2 f)) :=
        CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.isQuasisimple_statedSp_of_not_small
          hm h1 h22
      have hA : CFSG.Assembly.IsComponentOf (C.map Φ.toMonoidHom) ⊤ :=
        (CFSG.Assembly.isComponentOf_iff_open).2 hmap
      have htop : C.map Φ.toMonoidHom = ⊤ :=
        CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple
          ((CFSG.Assembly.IsQuasisimple.congr Subgroup.topEquiv).mpr hq) hA
      have hCtop : C = ⊤ := by
        refine le_antisymm le_top ?_
        intro x _
        have hx : Φ x ∈ C.map Φ.toMonoidHom := by
          rw [htop]
          exact Subgroup.mem_top _
        obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx
        rw [← Φ.injective hcx]
        exact hc
      refine Or.inl ⟨.PSp, n₁, f, Φ.symm.toMonoidHom, ?_, hf, ?_⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rw [hCtop]
        exact rckModelConverse_top (t := .PSp) (m := n₁) (g := f)
          (κ := Φ.symm.toMonoidHom) Φ.symm.injective Φ.symm.surjective

theorem rckBlockModel_linearCase {W : Type} [Group W] {m : ℕ} {H : Subgroup W}
    {C : Subgroup ↥H} (hCo : CFSG.Open.IsComponentOf C ⊤)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {Φ : ↥H ≃* GL (Fin m) E} :
    ∃ (t : StatedLieTag) (m' g : ℕ) (κ : (ggU t m' g).K →* ↥H),
      RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m' g κ := by
  haveI : Fintype E := Fintype.ofFinite E
  have hmap : CFSG.Open.IsComponentOf (C.map Φ.toMonoidHom) ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv Φ hCo
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr Φ.surjective] at h
  have hmapA : CFSG.Assembly.IsComponentOf (C.map Φ.toMonoidHom) ⊤ :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hmap
  have hm0 : m ≠ 0 := by
    rintro rfl
    haveI : Subsingleton (GL (Fin 0) E) := inferInstance
    exact CFSG.StandardType.GGHalf.ne_bot_of_isComponentOf hmapA
      (Subgroup.eq_bot_of_subsingleton _)
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst m
  have hSL : C.map Φ.toMonoidHom = CFSG.Open.StatedSL (k + 1) E :=
    eq_statedSL_of_isComponentOf_top hmapA
  obtain ⟨g, -, hEfieldcard⟩ := FiniteField.card E 2
  have hg : 1 ≤ (g : ℕ) := g.pos
  have hEnat : Nat.card E = 2 ^ (g : ℕ) := by
    rw [Nat.card_eq_fintype_card, hEfieldcard]
  obtain ⟨κ₀, hκ₀⟩ := exists_rckModelConverse_SL (k := k) (g := (g : ℕ)) hg hEnat
  have hmapback : (CFSG.Open.StatedSL (k + 1) E).map Φ.symm.toMonoidHom = C := by
    rw [← hSL, Subgroup.map_map]
    have heq : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id _ := by
      ext z
      simp
    rw [heq, Subgroup.map_id]
  refine ⟨.PSL, k + 1, (g : ℕ), Φ.symm.toMonoidHom.comp κ₀, ?_, hg, ?_⟩
  · exact Or.inl rfl
  · rw [← hmapback]
    exact rckModelConverse_map Φ.symm hκ₀

theorem rckBlockModel_unitaryCase {W : Type} [Group W] {m Q : ℕ} {H : Subgroup W}
    {C : Subgroup ↥H}
    (hCo : CFSG.Open.IsComponentOf C ⊤) {E : Type} [Field E] [Finite E] [CharP E 2]
    (hEcard : Nat.card E = Q ^ 2) {Φ : ↥H ≃* ↥(ClassicalBlocks.GUFull m Q E)} :
    (∃ (t : StatedLieTag) (m' g : ℕ) (κ : (ggU t m' g).K →* ↥H),
      RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m' g κ) ∨
    (∃ (m' Q' : ℕ) (E' : Type) (_ : Field E') (_ : Finite E') (_ : CharP E' 2), m' ≤ 3 ∧
      Nat.card E' = Q' ^ 2 ∧ ∃ Φ' : ↥H ≃* ↥(ClassicalBlocks.GUFull m' Q' E'),
        C.map Φ'.toMonoidHom =
          (CFSG.Open.StatedSU m' Q' E').subgroupOf (ClassicalBlocks.GUFull m' Q' E')) := by
  haveI : Fintype E := Fintype.ofFinite E
  have hmap : CFSG.Open.IsComponentOf (C.map Φ.toMonoidHom) ⊤ := by
    have h := CFSG.isComponentOf_map_mulEquiv Φ hCo
    rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr Φ.surjective] at h
  have hSUmap : (C.map Φ.toMonoidHom).map (ClassicalBlocks.GUFull m Q E).subtype =
      CFSG.Open.StatedSU m Q E :=
    eq_statedSU_of_isComponentOf_unitaryFull (m := m) (Q := Q) (E := E) hEcard
      (rckIsComponentOf_map_subtype_of_top hmap)
  have hSU : C.map Φ.toMonoidHom =
      (CFSG.Open.StatedSU m Q E).subgroupOf (ClassicalBlocks.GUFull m Q E) := by
    rw [← hSUmap]
    show Subgroup.map Φ.toMonoidHom C =
      Subgroup.comap (ClassicalBlocks.GUFull m Q E).subtype
        (Subgroup.map (ClassicalBlocks.GUFull m Q E).subtype (Subgroup.map Φ.toMonoidHom C))
    exact (Subgroup.comap_map_eq_self_of_injective
      (ClassicalBlocks.GUFull m Q E).subtype_injective _).symm
  by_cases hm3 : m ≤ 3
  · exact Or.inr ⟨m, Q, E, inferInstance, inferInstance, inferInstance, hm3, hEcard, Φ, hSU⟩
  · have hm4 : 4 ≤ m := by omega
    obtain ⟨k, -, hkcard⟩ := FiniteField.card E 2
    have hEnat2 : Nat.card E = 2 ^ (k : ℕ) := by
      rw [Nat.card_eq_fintype_card, hkcard]
    have hdvd : Q ∣ 2 ^ (k : ℕ) := by
      rw [← hEnat2, hEcard]
      exact ⟨Q, by ring⟩
    obtain ⟨j, -, hQj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · have hQ1 : Q = 1 := by rw [hQj, hj, pow_zero]
        rw [hQ1, one_pow] at hEcard
        have hgt : 1 < Nat.card E := Finite.one_lt_card
        omega
      · exact hj
    obtain ⟨s, hs⟩ : ∃ s, j = s + 1 := ⟨j - 1, by omega⟩
    subst j
    subst Q
    obtain ⟨κ₀, hκ₀⟩ := exists_rckModelConverse_SU (m := m) (g := s) hm4 hEcard
    have hmapback : ((CFSG.Open.StatedSU m (2 ^ (s + 1)) E).subgroupOf
        (ClassicalBlocks.GUFull m (2 ^ (s + 1)) E)).map Φ.symm.toMonoidHom = C := by
      rw [← hSU, Subgroup.map_map]
      have heq : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id _ := by
        ext z
        simp
      rw [heq, Subgroup.map_id]
    refine Or.inl ⟨.PSU, m, s + 1, Φ.symm.toMonoidHom.comp κ₀, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inl rfl)
    · omega
    · rw [← hmapback]
      exact rckModelConverse_map Φ.symm hκ₀

theorem rckBlockModel_PSp {n f : ℕ} (hf : 1 ≤ f) {s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hs : s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) (hodd : Odd (orderOf s))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({s} : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))))) ε)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε,
        glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε⁆) :
    (∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →*
        ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε)),
      RCKClassicalTag t ∧ 1 ≤ g ∧
        RCKModelConverse
          (J'.subgroupOf (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε))
          t m g κ) ∨
    (Nat.card (GaloisField 2 f) = 2 ∧
      Nonempty (↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε) ≃*
        ↥(CFSG.Open.StatedSp 2 (GaloisField 2 f)))) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧
      ∃ Φ : ↥(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε) ≃*
          ↥(ClassicalBlocks.GUFull m Q E),
        (J'.subgroupOf (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε)).map
          Φ.toMonoidHom =
          (CFSG.Open.StatedSU m Q E).subgroupOf (ClassicalBlocks.GUFull m Q E)) := by
  classical
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  let H : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
    glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype {s} ε
  let C : Subgroup ↥H := J'.subgroupOf H
  have hC : IsComponentOf C ⊤ := rckIsComponentOf_top_of_commutator hJ'
  have hCo : CFSG.Open.IsComponentOf C ⊤ := (CFSG.Assembly.isComponentOf_iff_open).1 hC
  change (∃ (t : StatedLieTag) (m g : ℕ) (κ : (ggU t m g).K →* ↥H),
      RCKClassicalTag t ∧ 1 ≤ g ∧ RCKModelConverse C t m g κ) ∨
    (Nat.card (GaloisField 2 f) = 2 ∧
      Nonempty (↥H ≃* ↥(CFSG.Open.StatedSp 2 (GaloisField 2 f)))) ∨
    (∃ (m Q : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), m ≤ 3 ∧
      Nat.card E = Q ^ 2 ∧
      ∃ Φ : ↥H ≃* ↥(ClassicalBlocks.GUFull m Q E),
        C.map Φ.toMonoidHom =
          (CFSG.Open.StatedSU m Q E).subgroupOf (ClassicalBlocks.GUFull m Q E))
  rcases blockGroup_iso_Sp_cases s hs hodd hε with
    ⟨n₁, ⟨Φ⟩⟩ | ⟨m, E, hEfield, hEfin, hchar, ⟨Φ⟩⟩ |
      ⟨m, Q, E, hEfield, hEfin, hchar, hEcard, ⟨Φ⟩⟩
  · rcases rckBlockModel_PSp_spCase (n := n) (f := f) hf hCo (Φ := Φ) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · letI : Field E := hEfield
    letI : Finite E := hEfin
    letI : CharP E 2 := hchar
    exact Or.inl (rckBlockModel_linearCase (m := m) (E := E)
      hCo (Φ := Φ))
  · letI : Field E := hEfield
    letI : Finite E := hEfin
    letI : CharP E 2 := hchar
    rcases rckBlockModel_unitaryCase (m := m) (Q := Q) (E := E)
      hCo hEcard (Φ := Φ) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

end CFSG.StandardType.RCKRP
