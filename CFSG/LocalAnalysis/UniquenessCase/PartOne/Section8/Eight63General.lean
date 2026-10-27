module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_inner_of_isPGroup_of_not_dvd_card_outer
    {X : Type} [Group X] [Finite X] {r : ℕ} [Fact r.Prime] {φ : MulAut X}
    (hφ : IsPGroup r (Subgroup.zpowers φ))
    (hOut : ¬ r ∣ Nat.card (Outer X)) :
    φ ∈ inner X := by
  let ψ : Outer X := QuotientGroup.mk' (inner X) φ
  have hψP : IsPGroup r (Subgroup.zpowers ψ) := by
    have h := hφ.map (QuotientGroup.mk' (inner X))
    rwa [MonoidHom.map_zpowers] at h
  have hψ1 : ψ = 1 := by
    by_contra hψ
    have hψsub : (⟨ψ, Subgroup.mem_zpowers ψ⟩ : Subgroup.zpowers ψ) ≠ 1 := by
      simpa using hψ
    have hrdvd : r ∣ orderOf ψ := by
      have h := hψP.dvd_orderOf hψsub
      simpa using h
    exact hOut (hrdvd.trans (orderOf_dvd_natCard ψ))
  exact (QuotientGroup.eq_one_iff (N := inner X) φ).mp (by simpa [ψ] using hψ1)

private abbrev O2sub (L : Subgroup G) : Subgroup ↥L := CFSG.pCore 2 ↥L

private theorem mem_O2sub_iff {L : Subgroup G} {x : ↥L} :
    x ∈ O2sub L ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
  rw [CFSG.Open.pCoreOf]
  exact (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm

private theorem normalizerMonoidHom_apply_coe (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (y : ↥L) :
    (((Subgroup.normalizerMonoidHom L) n) y : G) = (n : G) * (y : G) * (n : G)⁻¹ :=
  rfl

private theorem barAction_eq_one_iff' (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) :
    barAction L n = 1 ↔ ∀ y ∈ L, ⁅(n : G), y⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  constructor
  · intro h y hy
    let y' : ↥L := ⟨y, hy⟩
    have h1 : barAction L n (QuotientGroup.mk y') = QuotientGroup.mk y' := by
      rw [h, MulAut.one_apply]
    rw [barAction_mk] at h1
    have h2 : ((Subgroup.normalizerMonoidHom L) n y') / y' ∈ O2sub L :=
      QuotientGroup.eq_iff_div_mem.mp h1
    rw [mem_O2sub_iff] at h2
    simpa [commutatorElement_def, Subgroup.coe_div, normalizerMonoidHom_apply_coe,
      div_eq_mul_inv] using h2
  · intro h
    apply MulEquiv.ext
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    rw [barAction_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem, mem_O2sub_iff]
    simpa [commutatorElement_def, Subgroup.coe_div, normalizerMonoidHom_apply_coe,
      div_eq_mul_inv] using h (y : G) y.2

private theorem barAction_eq_of_inner' {L : Subgroup G} {x l : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hlL : l ∈ L)
    (h : ∀ y ∈ L, (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    barAction L ⟨x, hxN⟩ = barAction L ⟨l, Subgroup.le_normalizer hlL⟩ := by
  apply MulEquiv.ext
  intro a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  rw [barAction_mk, barAction_mk, QuotientGroup.eq_iff_div_mem, mem_O2sub_iff]
  simpa [Subgroup.coe_div, normalizerMonoidHom_apply_coe, div_eq_mul_inv] using h (y : G) y.2

theorem exists_conj_of_not_dvd_outer
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {r : ℕ} [Fact r.Prime] (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hxr : IsPGroup r (Subgroup.zpowers x))
    (hOut : ¬ r ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))) :
    ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let n : ↥N := ⟨x, hx⟩
  have hmap : (Subgroup.zpowers n).map N.subtype = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hxr' : IsPGroup r (Subgroup.zpowers n) := by
    have h : IsPGroup r ((Subgroup.zpowers n).map N.subtype) := by
      rwa [hmap]
    exact h.of_equiv (Subgroup.equivMapOfInjective (Subgroup.zpowers n) N.subtype
      Subtype.coe_injective).symm
  have hφ : IsPGroup r (Subgroup.zpowers (barAction L n)) := by
    rw [← MonoidHom.map_zpowers (barAction L) n]
    exact hxr'.map (barAction L)
  have hmem : barConjAut x ∈ inner (Bar2 L) := by
    rw [barConjAut_of_mem (L := L) hx]
    exact mem_inner_of_isPGroup_of_not_dvd_card_outer hφ hOut
  exact (barConjAut_mem_inner_iff x hx).mp hmem

theorem le_sup_centralizerBar_of_inner_prime
    {G : Type} [Group G] [Finite G] {P L Q X : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hQP : Q ≤ P) (hQL : Q ≤ L) (hQeq : Q = P ⊓ L)
    (hQnormP : (Q.subgroupOf P).Normal)
    (hQ : CFSG.ABGLocalTools.IsSylowOf r Q L)
    (hPr : IsPGroup r P) (hPNL : P ≤ Subgroup.normalizer (L : Set G))
    (hX : X ≤ P)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    X ≤ Q ⊔ centralizerBar P L := by
  classical
  haveI hHfin : Finite (↥L ⧸ O2sub L) :=
    Finite.of_surjective (QuotientGroup.mk' (O2sub L)) (QuotientGroup.mk'_surjective (O2sub L))
  haveI hAfin : Finite (MulAut (↥L ⧸ O2sub L)) :=
    Finite.of_injective
      (fun f : MulAut (↥L ⧸ O2sub L) => (f : (↥L ⧸ O2sub L) → (↥L ⧸ O2sub L)))
      DFunLike.coe_injective
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hPN : P ≤ N := hPNL
  have hQN : Q ≤ N := hQL.trans hLN
  let φ : N →* MulAut (↥L ⧸ O2sub L) := barAction L
  let P' : Subgroup N := P.subgroupOf N
  let L' : Subgroup N := L.subgroupOf N
  let Q' : Subgroup N := Q.subgroupOf N
  let B : Subgroup (MulAut (↥L ⧸ O2sub L)) := P'.map φ
  let I : Subgroup (MulAut (↥L ⧸ O2sub L)) := L'.map φ
  let J : Subgroup (MulAut (↥L ⧸ O2sub L)) := Q'.map φ
  have hQ'L' : Q' ≤ L' := Subgroup.subgroupOf_mono N hQL
  have hBr : IsPGroup r B := (hPr.comap_subtype (K := N)).map φ
  have hQNm : IsSylowOf r Q' L' := by
    rw [← isSylowOf_map_subtype_iff N, Subgroup.map_subgroupOf_eq_of_le hQN,
      Subgroup.map_subgroupOf_eq_of_le hLN]
    exact hQ
  have hJ : IsSylowOf r J I := by
    let φL : L' →* MulAut (↥L ⧸ O2sub L) := φ.comp L'.subtype
    have htop : (⊤ : Subgroup L').map L'.subtype = L' := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hrange : φL.range = I := by
      dsimp only [φL, I]
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, htop]
    have hJeq : (Q'.subgroupOf L').map φL = J := by
      dsimp only [J, Q', φL]
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(x : N), hx, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨⟨n, hQ'L' hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
    obtain ⟨S, hS⟩ := hQNm.exists_sylow_eq_subgroupOf
    have hSyl' : IsSylowOf r ((Q'.subgroupOf L').map φL) φL.range := by
      refine ⟨S.mapSurjective (f := φL.rangeRestrict)
        (MonoidHom.rangeRestrict_surjective φL), ?_⟩
      rw [Sylow.coe_mapSurjective, Subgroup.map_map,
        MonoidHom.subtype_comp_rangeRestrict, hS]
    rw [← hrange, ← hJeq]
    exact hSyl'
  have hBIr : IsPGroup r (B ⊓ I : Subgroup (MulAut (↥L ⧸ O2sub L))) :=
    hBr.to_inf_left (K := I)
  have hJI : J ≤ B ⊓ I := by
    refine le_inf ?_ hJ.le
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono N hQP)
  have hEq : B ⊓ I = J := hJ.eq_of_le hJI inf_le_right hBIr
  intro x hx
  have hxP : x ∈ P := hX hx
  have hxN : x ∈ N := hPN hxP
  obtain ⟨l, hlL, hinner⟩ := hInner x hx
  have hlN : l ∈ N := hLN hlL
  have hact : φ ⟨x, hxN⟩ = φ ⟨l, hlN⟩ := by
    dsimp only [φ]
    exact barAction_eq_of_inner' hxN hlL hinner
  have hxB : φ ⟨x, hxN⟩ ∈ B := by
    dsimp only [B, P']
    exact Subgroup.mem_map_of_mem φ hxP
  have hxI : φ ⟨x, hxN⟩ ∈ I := by
    rw [hact]
    dsimp only [I, L']
    exact Subgroup.mem_map_of_mem φ hlL
  have hxJ : φ ⟨x, hxN⟩ ∈ J := by
    rw [← hEq]
    exact ⟨hxB, hxI⟩
  dsimp only [J, Q'] at hxJ
  rw [Subgroup.mem_map] at hxJ
  obtain ⟨qN, hqN, hqeq⟩ := hxJ
  let q : G := (qN : G)
  have hqQ : q ∈ Q := hqN
  have hqP : q ∈ P := hQP hqQ
  have hxqP : x * q⁻¹ ∈ P := P.mul_mem hxP (P.inv_mem hqP)
  have hxqN : x * q⁻¹ ∈ N := hPN hxqP
  have hlam1 : φ ⟨x * q⁻¹, hxqN⟩ = 1 := by
    have h1 : (⟨x * q⁻¹, hxqN⟩ : N) = ⟨x, hxN⟩ * qN⁻¹ := by
      ext
      rfl
    rw [h1, map_mul, map_inv, hqeq]
    simp
  have hcent : x * q⁻¹ ∈ centralizerBar P L := by
    rw [mem_centralizerBar_iff]
    refine ⟨hxqP, ?_⟩
    intro y hy
    exact (barAction_eq_one_iff' L ⟨x * q⁻¹, hxqN⟩).mp hlam1 y hy
  have hmem : (x * q⁻¹) * q ∈ centralizerBar P L ⊔ Q :=
    Subgroup.mul_mem_sup hcent hqQ
  rw [sup_comm]
  rw [show x = (x * q⁻¹) * q by group]
  exact hmem

theorem star863_of_bar
    {G : Type} [Group G] [Finite G] {L M S : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hLM : L ≤ M) (hLnorm : (L.subgroupOf M).Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf r S M)
    (hdecomp : S ≤ (S ⊓ L) ⊔ centralizerBar S L)
    (hSLab : ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x)
    (hSL : S ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥) :
    (S ⊓ L).subgroupOf S ≤ Subgroup.center ↥S := by
  classical
  let A : Subgroup G := S ⊓ L
  have hMnormL : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hSNL : S ≤ Subgroup.normalizer (L : Set G) := hS.le.trans hMnormL
  haveI hCnorm : ((centralizerBar S L).subgroupOf S).Normal :=
    centralizerBar_normal hSNL
  have hxcent : ∀ x ∈ S, x ∈ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hxsub : (⟨x, hx⟩ : ↥S) ∈
        A.subgroupOf S ⊔ (centralizerBar S L).subgroupOf S := by
      refine (Subgroup.mem_map_iff_mem (f := S.subtype) S.subtype_injective).mp ?_
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
        Subgroup.map_subgroupOf_eq_of_le (centralizerBar_le S L)]
      exact hdecomp hx
    obtain ⟨a', ha', c', hc', hac'⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := A.subgroupOf S)
        (t := (centralizerBar S L).subgroupOf S)).mp hxsub
    let a : G := (a' : G)
    let c : G := (c' : G)
    have haA : a ∈ A := Subgroup.mem_subgroupOf.mp ha'
    have hcC : c ∈ centralizerBar S L := Subgroup.mem_subgroupOf.mp hc'
    have hac : a * c = x := by
      have h := congrArg (fun z : ↥S => (z : G)) hac'
      simpa [a, c] using h
    have hcS : c ∈ S := centralizerBar_le S L hcC
    have hab : b * a = a * b := hSLab b hb a haA
    have hcO : ⁅c, b⁆ ∈ CFSG.Open.pCoreOf 2 L :=
      (mem_centralizerBar_iff.mp hcC).2 b hb.2
    have hcS' : ⁅c, b⁆ ∈ S := by
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hcS hb.1) (S.inv_mem hcS)) (S.inv_mem hb.1)
    have hmem : ⁅c, b⁆ ∈ S ⊓ L ⊓ CFSG.Open.pCoreOf 2 L :=
      ⟨⟨hcS', CFSG.LieType.BorelTits.pCoreOf_le 2 L hcO⟩, hcO⟩
    rw [hSL] at hmem
    have hcb : c * b = b * c :=
      commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
    rw [← hac]
    calc b * (a * c) = (b * a) * c := by group
      _ = (a * b) * c := by rw [hab]
      _ = a * (b * c) := by group
      _ = a * (c * b) := by rw [← hcb]
      _ = (a * c) * b := by group
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hzA : (z : G) ∈ A := Subgroup.mem_subgroupOf.mp hz
  exact (Subgroup.mem_centralizer_iff.mp (hxcent w w.2) (z : G) hzA).symm

theorem false_of_abelian_sylow_of_bar
    {G : Type} [Group G] [Finite G] {M L S E : Subgroup G} {r : ℕ}
    (h614 : CFSG.Yardstones.Mf4cdcdf2e013.Theorem614At M)
    (hsub : CFSG.Open.uniqueFourSigma M ⊆ CFSG.Yardstones.Mf4cdcdf2e013.SigmaOne4 G)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrsig : r ∉ CFSG.Open.uniqueFourSigma M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r M)
    (hLM : L ≤ M) (hLnorm : (L.subgroupOf M).Normal)
    (hS : CFSG.ABGLocalTools.IsSylowOf r S M)
    (hdecomp : S ≤ (S ⊓ L) ⊔ centralizerBar S L)
    (hSLab : ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x)
    (hSL : S ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hE : E ≤ S ⊓ L)
    (hEel : CFSG.Open.IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : CFSG.Open.rankThreeGamma 1 r E ≤ M) :
    False := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  have hZ := star863_of_bar hLM hLnorm hS hdecomp hSLab hSL
  have hEcenter : E ≤ S ⊓ Subgroup.centralizer (S : Set G) := by
    refine le_inf (hE.trans inf_le_left) ?_
    intro e he
    have heA : e ∈ S ⊓ L := hE he
    have hmem : (⟨e, heA.1⟩ : ↥S) ∈ (S ⊓ L).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr heA
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := Subgroup.mem_center_iff.mp (hZ hmem) ⟨s, hs⟩
    simpa using congrArg (fun w : ↥S => (w : G)) h
  exact hnot (h614 hsub r hr hr2 hrsig S hS E hEcenter hEel hEcard hΓ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
