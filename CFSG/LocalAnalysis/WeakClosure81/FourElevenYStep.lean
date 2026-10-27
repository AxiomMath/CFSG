module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenBasic
public import CFSG.LocalAnalysis.WeakClosure81.PGLTwoPrimePrintedRelativeGeneration
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IP
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_index_eq_two)

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isPGroup_sup_inf_centralizer {Y T : Subgroup Q} (hT : IsPGroup 2 T)
    (hTY : T ≤ normalizer (Y : Set Q)) (hZ : IsPGroup 2 ↥(Y ⊓ centralizer (Y : Set Q))) :
    IsPGroup 2 ↥((Y ⊔ T) ⊓ centralizer (Y : Set Q)) := by
  classical
  let D : Subgroup Q := Y ⊔ T
  let C : Subgroup Q := centralizer (Y : Set Q)
  have hTD : T ≤ D := le_sup_right
  have hDnorm : D ≤ normalizer (Y : Set Q) := sup_le le_normalizer hTY
  have : (Y.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hDnorm
  have hTsub : IsPGroup 2 ↥(T.subgroupOf D) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (Y.subgroupOf D)).comp (T.subgroupOf D).subtype) := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf D) x
    have hdtop : d ∈ (Y.subgroupOf D) ⊔ (T.subgroupOf D) := by
      change d ∈ (Y.subgroupOf (Y ⊔ T)) ⊔ (T.subgroupOf (Y ⊔ T))
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top d
    obtain ⟨y, hy, t, ht, hyt⟩ := Subgroup.mem_sup_of_normal_left.mp hdtop
    refine ⟨⟨t, ht⟩, ?_⟩
    change QuotientGroup.mk' (Y.subgroupOf D) t =
      QuotientGroup.mk' (Y.subgroupOf D) d
    rw [← hyt, map_mul]
    have hy1 : QuotientGroup.mk' (Y.subgroupOf D) y = 1 :=
      (QuotientGroup.eq_one_iff (N := Y.subgroupOf D) y).mpr hy
    rw [hy1, one_mul]
  have hquot : IsPGroup 2 (D ⧸ Y.subgroupOf D) :=
    hTsub.of_surjective ((QuotientGroup.mk' (Y.subgroupOf D)).comp
      (T.subgroupOf D).subtype) hsurj
  rw [isPGroup_iff_pow_pow_eq_one]
  intro c
  have hcD : (c : Q) ∈ D := c.2.1
  have hcC : (c : Q) ∈ C := c.2.2
  obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk' (Y.subgroupOf D) ⟨c.1, hcD⟩)
  have hkY : c.1 ^ 2 ^ k ∈ Y := by
    have hk' : QuotientGroup.mk' (Y.subgroupOf D) (⟨c.1, hcD⟩ ^ 2 ^ k) = 1 := by
      rwa [map_pow]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hk')
  have hkC : c.1 ^ 2 ^ k ∈ C := C.pow_mem hcC _
  obtain ⟨l, hl⟩ := hZ ⟨c.1 ^ 2 ^ k, hkY, hkC⟩
  refine ⟨k + l, ?_⟩
  apply Subtype.ext
  have hl' : (c.1 ^ 2 ^ k) ^ 2 ^ l = 1 := by
    simpa using congrArg Subtype.val hl
  show c.1 ^ 2 ^ (k + l) = 1
  rw [pow_add, pow_mul, hl']

theorem LeviData.not_le_centralizer {L : Subgroup Q} [L.Normal] {p : ℕ} {z : Q}
    {Y A : Subgroup Q} (hY : LeviData L p z Y) (hidx : L.index ≤ 2)
    (hout : ∀ b : Q, b ∉ L → orderOf b = 2 → ¬ Y ≤ centralizer ({b} : Set Q))
    (hA : IsElemAbelian 2 A) (h4 : 4 ≤ Nat.card A) : ¬ A ≤ centralizer (Y : Set Q) := by
  classical
  intro hle
  have hsub : A ⊓ L ≤ L ⊓ centralizer (Y : Set Q) :=
    le_inf inf_le_right (inf_le_left.trans hle)
  have hx_eq : ∀ x ∈ A ⊓ L, x ≠ 1 → x = z := by
    intro x hx hx1
    have hx2 : orderOf x = 2 :=
      orderOf_eq_prime (by simpa using hA.2 x hx.1) hx1
    exact hY.involution_eq x (hsub hx) hx2
  have hpair : (A ⊓ L : Set Q) ⊆ ({1, z} : Set Q) := by
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    · simp [hx_eq x hx hx1]
  have hcard2 : Nat.card ↥(A ⊓ L) ≤ 2 := by
    change (A ⊓ L : Set Q).ncard ≤ 2
    calc (A ⊓ L : Set Q).ncard ≤ ({1, z} : Set Q).ncard := Set.ncard_le_ncard hpair
      _ ≤ 2 := by
        have h := Set.ncard_insert_le (1 : Q) ({z} : Set Q)
        rw [Set.ncard_singleton] at h
        simpa using h
  have hcardA_le : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := card_le_two_mul_card_inf hidx A
  have hcardA : Nat.card A = 4 := by omega
  have hcardInf : Nat.card ↥(A ⊓ L) = 2 := by omega
  have hlt : (A ⊓ L : Set Q).ncard < (A : Set Q).ncard := by
    have hcardInf' : (A ⊓ L : Set Q).ncard = 2 := hcardInf
    have hcardA' : (A : Set Q).ncard = 4 := hcardA
    omega
  obtain ⟨b, hbA, hbnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hbL : b ∉ L := by
    intro hbL
    exact hbnot (Subgroup.mem_inf.mpr ⟨hbA, hbL⟩)
  have hb1 : b ≠ 1 := by
    intro hb1
    exact hbL (by rw [hb1]; exact L.one_mem)
  have hb2 : orderOf b = 2 :=
    orderOf_eq_prime (by simpa using hA.2 b hbA) hb1
  have hYC : Y ≤ centralizer ({b} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hle hbA)) y hy
  exact hout b hbL hb2 hYC

theorem LeviData.isPGroup_inf_centralizer_sl2 {L : Subgroup Q} {p : ℕ} [Fact p.Prime]
    {z : Q} {Y : Subgroup Q} (hY : LeviData L p z Y) (hp2 : p ≠ 2) :
    IsPGroup 2 ↥(Y ⊓ centralizer (Y : Set Q)) := by
  classical
  obtain ⟨e⟩ := hY.sl2
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  have hcard : Nat.card ↥(Subgroup.center Y) = 2 :=
    CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e
  have hcenter : IsPGroup 2 ↥(Subgroup.center Y) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hcard]; norm_num⟩
  have hcenter_eq : Y ⊓ centralizer (Y : Set Q) = (Subgroup.center Y).map Y.subtype := by
    ext x
    constructor
    · intro hx
      have hxY : x ∈ Y := hx.1
      have hxC : x ∈ centralizer (Y : Set Q) := hx.2
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      change (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.center Y
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : Q) y.2)
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun z hz => congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)⟩
  rw [hcenter_eq]
  exact hcenter.map Y.subtype

omit [Finite Q] in
theorem LeviData.exists_surjective_hom_pgl2_centralizer {L : Subgroup Q} {p : ℕ} [Fact p.Prime]
    {z : Q} {Y : Subgroup Q} (hp5 : 5 ≤ p) (hY : LeviData L p z Y) :
    ∃ φ : ↥(centralizer ({z} : Set Q)) →* CFSG.GorensteinWalter.PGL2 (ZMod p),
      Function.Surjective φ ∧
      (∀ h ∈ φ.ker, (h : Q) ∈ centralizer (Y : Set Q)) ∧
      (Y.subgroupOf (centralizer ({z} : Set Q))).map φ = pslRange (ZMod p) := by
  classical
  let C : Subgroup Q := centralizer ({z} : Set Q)
  have hYC : Y ≤ C := by
    have hYeq : Y = ⁅L ⊓ C, L ⊓ C⁆ := by simpa [C] using hY.eq_commutator
    rw [hYeq]
    exact (Subgroup.commutator_le_self (L ⊓ C)).trans inf_le_right
  obtain ⟨φ, hker, hmap, hpsl⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.exists_hom_pgl2_centralizer hp5 hYC
      hY.centralizer_le_normalizer hY.sl2.some
  have hoddPP : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.isOddPrimePower_zmod (by omega)
  obtain ⟨g, hgLC, hgnot⟩ : ∃ g ∈ L ⊓ C, ∀ s ∈ Y, s⁻¹ * g ∉ centralizer (Y : Set Q) := by
    simpa [C] using hY.exists_not_mem
  have hgC : g ∈ C := hgLC.2
  let g' : ↥C := ⟨g, hgC⟩
  have hgφJ : φ g' ∉ pslRange (ZMod p) := by
    intro hmem
    obtain ⟨s, hs, hsc⟩ := hpsl g' hmem
    exact hgnot s hs hsc
  have hJle : pslRange (ZMod p) ≤ φ.range := by
    rw [← hmap]
    exact Subgroup.map_le_range (f := φ) _
  have hxgeo : φ g' ∈ φ.range := MonoidHom.mem_range.mpr ⟨g', rfl⟩
  have hdvd : φ.range.index ∣ 2 := by
    have := Subgroup.index_dvd_of_le hJle
    rwa [pslRange_index_eq_two hoddPP] at this
  have htop : φ.range = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have heq : pslRange (ZMod p) = φ.range :=
        Subgroup.eq_of_index_dvd_index hJle (by
          rw [h2, pslRange_index_eq_two hoddPP])
      rw [← heq] at hxgeo
      exact hgφJ hxgeo
  exact ⟨φ, MonoidHom.range_eq_top.mp htop, hker, hmap⟩

theorem LeviData.le_sup_iSup_calEi
    {L : Subgroup Q} [L.Normal] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) {T A Y : Subgroup Q}
    {z : Q} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (hzT : T ≤ centralizer ({z} : Set Q)) (hY : LeviData L p z Y)
    (hAY : ¬ A ≤ centralizer (Y : Set Q)) :
    Y ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q | UniquenessCase.PartTwo.InCalEi 1 T A J}, J := by
  classical
  let C : Subgroup Q := centralizer ({z} : Set Q)
  let D : Subgroup Q := Y ⊔ T
  have hYC : Y ≤ C := by
    have hYeq : Y = ⁅L ⊓ C, L ⊓ C⁆ := by simpa [C] using hY.eq_commutator
    rw [hYeq]
    exact (Subgroup.commutator_le_self (L ⊓ C)).trans inf_le_right
  have hTD : T ≤ D := le_sup_right
  have hAD : A ≤ D := hAT.trans hTD
  have hDC : D ≤ C := sup_le hYC hzT
  obtain ⟨φ, hφsurj, hkerφ, hmap⟩ := hY.exists_surjective_hom_pgl2_centralizer (by omega)
  let π : ↥D →* CFSG.GorensteinWalter.PGL2 (ZMod p) := φ.comp (Subgroup.inclusion hDC)
  have hTau : E1.tauOf (⊤ : Subgroup Q) T A ≤ T ⊓ D :=
    le_inf (E1.tauOf_le ⊤ T A) ((E1.tauOf_le ⊤ T A).trans hTD)
  have hSyl : IsSylowIn 2 (T ⊓ D) D := by
    have hinf : T ⊓ D = T := inf_eq_left.mpr hTD
    rw [hinf]
    refine ⟨hTD, hT.isPGroup, ?_⟩
    have hdiv : T.relIndex D ∣ T.relIndex ⊤ :=
      ⟨_, (Subgroup.relIndex_mul_relIndex T D ⊤ hTD le_top).symm⟩
    exact fun h => hT.not_dvd_relIndex (h.trans hdiv)
  have hTY : T ≤ normalizer (Y : Set Q) := hzT.trans hY.centralizer_le_normalizer
  have hZ : IsPGroup 2 ↥(Y ⊓ centralizer (Y : Set Q)) :=
    hY.isPGroup_inf_centralizer_sl2 (by omega)
  have hDp : IsPGroup 2 ↥((Y ⊔ T) ⊓ centralizer (Y : Set Q)) :=
    isPGroup_sup_inf_centralizer hT.isPGroup hTY hZ
  have hKsubp : IsPGroup 2 ↥(((Y ⊔ T) ⊓ centralizer (Y : Set Q)).subgroupOf D) :=
    hDp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hkerle : π.ker ≤ ((Y ⊔ T) ⊓ centralizer (Y : Set Q)).subgroupOf D := by
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hincl : (Subgroup.inclusion hDC) d = ⟨d.1, hDC d.2⟩ := Subtype.ext rfl
    have hd' : φ ⟨d.1, hDC d.2⟩ = 1 := by
      rw [← hincl]
      simpa [π] using hd
    rw [Subgroup.mem_subgroupOf]
    exact ⟨d.2, hkerφ ⟨d.1, hDC d.2⟩ hd'⟩
  have hkerπ : IsPGroup 2 π.ker := hKsubp.to_le hkerle
  have hne : (A.subgroupOf D).map π ≠ ⊥ := by
    intro hbot
    apply hAY
    intro a ha
    have haD : a ∈ D := hAD ha
    have hmem : π ⟨a, haD⟩ ∈ (A.subgroupOf D).map π :=
      Subgroup.mem_map.mpr ⟨⟨a, haD⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [hbot] at hmem
    have hpi1 : π ⟨a, haD⟩ = 1 := by simpa using hmem
    have hincl : (Subgroup.inclusion hDC) ⟨a, haD⟩ = ⟨a, hDC haD⟩ := Subtype.ext rfl
    have hpi1' : φ ⟨a, hDC haD⟩ = 1 := by
      rw [← hincl]
      simpa [π] using hpi1
    exact hkerφ ⟨a, hDC haD⟩ hpi1'
  have hoddPP : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.isOddPrimePower_zmod (by omega)
  have hTC : IsSylowIn 2 T C := by
    refine ⟨hzT, hT.isPGroup, ?_⟩
    have hdiv : T.relIndex C ∣ T.relIndex ⊤ :=
      ⟨_, (Subgroup.relIndex_mul_relIndex T C ⊤ hzT le_top).symm⟩
    exact fun h => hT.not_dvd_relIndex (h.trans hdiv)
  let S' : Subgroup (CFSG.GorensteinWalter.PGL2 (ZMod p)) := (T.subgroupOf C).map φ
  have hSylS' : IsSylowIn 2 S' ⊤ := by
    let P : Sylow 2 (CFSG.GorensteinWalter.PGL2 (ZMod p)) :=
      hTC.toSylow.mapSurjective hφsurj
    have hcoe : (P : Subgroup (CFSG.GorensteinWalter.PGL2 (ZMod p))) = S' := by
      change ((hTC.toSylow : Subgroup C).map φ) = S'
      rw [IsSylowIn.coe_toSylow]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hcoe]
      exact P.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hcoe]
      exact P.not_dvd_index
  have htopJ : pslRange (ZMod p) ⊔ S' = ⊤ :=
    CFSG.Quasithin.E22L2.e22pl2pgl_sup_eq_top hoddPP hSylS'
  have hpi : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top]
    refine le_antisymm le_top ?_
    rw [← htopJ]
    refine sup_le ?_ ?_
    · intro x hx
      rw [← hmap] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyD : (y : Q) ∈ D := Subgroup.mem_sup_left hy
      refine MonoidHom.mem_range.mpr ⟨⟨(y : Q), hyD⟩, ?_⟩
      change φ (Subgroup.inclusion hDC ⟨(y : Q), hyD⟩) = φ y
      exact congrArg φ (Subtype.ext rfl)
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
      have htT : (t : Q) ∈ T := Subgroup.mem_subgroupOf.mp ht
      have htD : (t : Q) ∈ D := Subgroup.mem_sup_right htT
      refine MonoidHom.mem_range.mpr ⟨⟨(t : Q), htD⟩, ?_⟩
      change φ (Subgroup.inclusion hDC ⟨(t : Q), htD⟩) = φ t
      exact congrArg φ (Subtype.ext rfl)
  have hDle : D ≤ T ⊔ ⨆ J ∈ {J : Subgroup Q |
      UniquenessCase.PartTwo.InCalEi 1 T A J}, J :=
    relative_generation_printed_of_pgl2_prime (Nat.card_zmod p) (by omega)
      hT hAT hA hTau hSyl π hpi hkerπ hne
  exact le_sup_left.trans hDle

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
