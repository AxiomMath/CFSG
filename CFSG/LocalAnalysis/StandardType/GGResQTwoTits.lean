module

public import CFSG.LocalAnalysis.StandardType.GGF4QTwoEndsL
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpTwoDelta
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_inf_normalizer_eq_card_centralizer_mul_card_automizer
    {G : Type} [Group G] [Finite G] (H A : Subgroup G) :
    Nat.card ↥(H ⊓ Subgroup.normalizer (A : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer (A : Set G)) * Nat.card (ggAutomizer H A) := by
  classical
  let N : Subgroup G := H ⊓ Subgroup.normalizer (A : Set G)
  let f : ↥N →* MulAut ↥A :=
    { toFun := fun n => ggConjAut A n.2.2
      map_one' := by
        ext a
        change (1 : G) * (a : G) * (1 : G)⁻¹ = (a : G)
        group
      map_mul' := by
        intro x y
        ext a
        change ((x : G) * (y : G)) * (a : G) * ((x : G) * (y : G))⁻¹ =
          (x : G) * ((y : G) * (a : G) * (y : G)⁻¹) * (x : G)⁻¹
        group }
  have hker : f.ker = (H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      refine ⟨n.2.1, ?_⟩
      change (n : G) ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := congrArg (fun φ : MulAut ↥A => (φ ⟨a, ha⟩ : ↥A)) h
      simp only [MulAut.one_apply] at h1
      have h2 : (n : G) * a * (n : G)⁻¹ = a := by
        have h2' := congrArg Subtype.val h1
        change (((ggConjAut A n.2.2) ⟨a, ha⟩ : ↥A) : G) = a at h2'
        simpa only [ggConjAut_apply, Subgroup.coe_mk] using h2'
      calc a * (n : G) = ((n : G) * a * (n : G)⁻¹) * (n : G) := by rw [h2]
        _ = (n : G) * a := by group
    · rintro ⟨-, hc⟩
      ext a
      change (n : G) * (a : G) * (n : G)⁻¹ = (a : G)
      have hc' : (n : G) ∈ Subgroup.centralizer (A : Set G) := hc
      have h1 := Subgroup.mem_centralizer_iff.mp hc' a a.2
      rw [← h1]
      group
  have hrange : f.range = ggAutomizer H A := by
    rw [ggAutomizer_eq]
    ext φ
    constructor
    · rintro ⟨n, rfl⟩
      exact ggConjAut_mem_ggInduced n.2.1 n.2.2
    · rintro ⟨g, hgH, hgN, hφ⟩
      refine ⟨⟨g, hgH, hgN⟩, ?_⟩
      ext a
      change g * (a : G) * g⁻¹ = ((φ a : ↥A) : G)
      exact (hφ a).symm
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange] at hcard
  have hsub : Nat.card ↥((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf N) =
      Nat.card ↥(H ⊓ Subgroup.centralizer (A : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer (A : Set G))))).toEquiv
  rw [hsub] at hcard
  exact hcard.symm

theorem ggQTwoTitsExcl_of_noTransvection_three
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4)
    (hNoTr : GGNoTransvection 3 Bs)
    (h3A : 3 ∣ Nat.card (ggAutomizer L Bs)) :
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twF4der, 0, 1⟩) 3 Bs L → False := by
  intro hqT
  obtain ⟨hL, lab, hlab, hraw⟩ := hqT
  have hEq : lab = ⟨.twF4der, 0, 1⟩ := by
    obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
    exact hEq
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, _, _, hK, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hBN, h3⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Subsingleton Kˣ := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK2
  have hLperf : commutator ↥L = ⊤ := (GGConfig.data_L hC).2.2.2
  have hS : LargeEvenSStar 3 B x L := hC.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S := hS.2.2.2.2
  have hxBs : x ∈ Bs := hC.2.1.1 hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hBs : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hcardA : Nat.card (ggGamma L hBN).range = 27 := by
    have hmul := card_range_ggGamma_mul_of Nat.prime_three hBs hxBs hx1 hLx hcyc hBN
    rw [hcard] at hmul
    omega
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hBp : ∀ a : ↥Bs, a ^ 3 = 1 := fun a =>
    Subtype.ext (by simpa using hBs.2 a a.2)
  have hAelem : IsElemAbelian 3 (ggGamma L hBN).range :=
    isElemAbelian_range hBc hBp (ggGamma L hBN)
  have hAinn : (ggGamma L hBN).range ≤ (MulAut.conj : L →* MulAut L).range := by
    rintro a ⟨b, rfl⟩
    have hbInv : (((b : ↥Bs) : G))⁻¹ ∈ Bs := Bs.inv_mem b.2
    obtain ⟨φ, hφI, hφind⟩ := h3 (((b : ↥Bs) : G))⁻¹ hbInv
    obtain ⟨r, rfl⟩ := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanF4)
      (LargeEvenTwF4H 0 K) hφI
    have hind : ∀ l : ↥L, MulAut.conj r (ggQuotHom θ l) =
        ggQuotHom θ (ggGamma L hBN b l) := by
      intro l
      have hrel : (((ggGamma L hBN b l : ↥L) : G)) =
          ((((b : ↥Bs) : G)⁻¹)⁻¹) * (l : G) * (((b : ↥Bs) : G)⁻¹) := by
        rw [ggGamma_coe]
        group
      simpa only [ggQuotHom_apply] using hφind l (ggGamma L hBN b l) hrel
    obtain ⟨g, hg⟩ := isInner_of_induces (ψ := ggQuotHom θ)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hLperf
      (ggGamma L hBN b) ⟨r, rfl⟩ hind
    exact ⟨g, hg.symm⟩
  have hCBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxBs hx1 hLx hcyc
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
    have hle : Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G) ≤
        Bs ⊓ Subgroup.centralizer (L : Set G) := fun z hz => ⟨hz.1.1, hz.2⟩
    have hcardle := Subgroup.card_le_of_le hle
    rw [hCBL, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hx1] at hcardle
    exact hcardle
  have h3dvd : 3 ∣ Nat.card (ggAutomizer (MulAut.conj : L →* MulAut L).range
      (ggGamma L hBN).range) :=
    dvd_trans h3A (card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hBN hZ)
  have hNcard := card_inf_normalizer_eq_card_centralizer_mul_card_automizer
    (H := (MulAut.conj : L →* MulAut L).range) (A := (ggGamma L hBN).range)
  have hA_le_cent : (ggGamma L hBN).range ≤
      Subgroup.centralizer (((ggGamma L hBN).range : Subgroup (MulAut L)) :
        Set (MulAut L)) :=
    Subgroup.le_centralizer_iff.mpr fun a ha b hb => IsElemAbelian.comm hAelem hb ha
  have hA_le_C : (ggGamma L hBN).range ≤ (MulAut.conj : L →* MulAut L).range ⊓
      Subgroup.centralizer (((ggGamma L hBN).range : Subgroup (MulAut L)) :
        Set (MulAut L)) :=
    le_inf hAinn hA_le_cent
  have h27 : 27 ∣ Nat.card ↥((MulAut.conj : L →* MulAut L).range ⊓
      Subgroup.centralizer (((ggGamma L hBN).range : Subgroup (MulAut L)) :
        Set (MulAut L))) := by
    have hdvd := Subgroup.card_dvd_of_le hA_le_C
    rwa [hcardA] at hdvd
  have h81N : 81 ∣ Nat.card ↥((MulAut.conj : L →* MulAut L).range ⊓
      Subgroup.normalizer (((ggGamma L hBN).range : Subgroup (MulAut L)) :
        Set (MulAut L))) := by
    have h81 : 27 * 3 ∣ Nat.card ↥((MulAut.conj : L →* MulAut L).range ⊓
        Subgroup.centralizer (((ggGamma L hBN).range : Subgroup (MulAut L)) :
          Set (MulAut L))) * Nat.card (ggAutomizer (MulAut.conj : L →* MulAut L).range
            (ggGamma L hBN).range) := Nat.mul_dvd_mul h27 h3dvd
    rw [← hNcard] at h81
    simpa using h81
  have h81S : 81 ∣ Nat.card ↥((MulAut.conj : L →* MulAut L).range) :=
    dvd_trans h81N (Subgroup.card_dvd_of_le inf_le_left)
  have hm : CFSG.Blueprint.ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK2⟩
  obtain ⟨eTits⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv
    (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) 2 1 hm
  have hScard : Nat.card ↥((MulAut.conj : L →* MulAut L).range) = 17971200 := by
    calc Nat.card ↥((MulAut.conj : L →* MulAut L).range)
        = Nat.card (L ⧸ Subgroup.center L) := by
          rw [← CFSG.GroupTheory.ker_conj_eq_center]
          exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange
            (MulAut.conj : L →* MulAut L)).toEquiv).symm
      _ = Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) := Nat.card_congr θ.toEquiv
      _ = Nat.card CFSG.Sporadic.Schreier.Tits.titsD := Nat.card_congr eTits.toEquiv
      _ = 17971200 := CFSG.Sporadic.Schreier.Tits.card_titsD
  rw [hScard] at h81S
  exact (by norm_num : ¬ 81 ∣ 17971200) h81S

theorem ggQTwoEnds_of_card_bstar_of_noTransvection_three
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 4)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hNoTr : GGNoTransvection 3 Bs)
    (h3A : 3 ∣ Nat.card (ggAutomizer L Bs)) :
    GGInnerDiagOnLabel GGLabSp6 3 Bs L ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6) ∧
        LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = n ∧ lab.n = 1)) ∨
      LargeEvenMarking ↥L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1) :=
  ggQTwoEnds_of_card_bstar_of_titsExcl hC hcard hq
    (ggQTwoTitsExcl_of_noTransvection_three hC hcard hNoTr h3A)

end CFSG.StandardType

end
