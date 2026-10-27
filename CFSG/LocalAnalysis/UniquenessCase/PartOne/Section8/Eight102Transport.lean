module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas

import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.GroupTheory.PCoreSurjective
import CFSG.Quasithin.H13.NQTermAmbientQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem card_barImage_of_isPGroup {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hX : IsPGroup s X) : Nat.card (barImage L X) = Nat.card X := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hs hs2
  have h := CFSG.GroupTheory.CoprimeTransport.card_map_mk_eq_of_isPGroup
    (N := CFSG.pCore 2 ↥L) hsN (E := X.subgroupOf L) hX.comap_subtype
  rw [show barImage L X = (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl,
    h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv

private theorem nonempty_barImage_mulEquiv {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hX : IsPGroup s X) :
    Nonempty (↥X ≃* ↥(barImage L X)) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hs hs2
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (X.subgroupOf L).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hsN hX.comap_subtype
  let f : ↥X →* Bar2 L :=
    { toFun := fun x => QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x.1, hXL x.2⟩
      map_one' := map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      map_mul' := fun x y => by
        simpa using map_mul (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
          (⟨x.1, hXL x.2⟩ : ↥L) ⟨y.1, hXL y.2⟩ }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (X.subgroupOf L).subtype)
        ⟨⟨x.1, hXL x.2⟩, x.2⟩ = ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
        (X.subgroupOf L).subtype) ⟨⟨y.1, hXL y.2⟩, y.2⟩ := hxy
    have h' : (⟨x.1, hXL x.2⟩ : ↥L) = ⟨y.1, hXL y.2⟩ :=
      congrArg Subtype.val (hinj hxy')
    exact Subtype.ext (congrArg (fun z : ↥L => (z : G)) h')
  have hf_range : f.range = barImage L X := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map_of_mem _ x.2
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨z.1, hz⟩, hzy⟩
  exact ⟨(MonoidHom.ofInjective hf_inj).trans (MulEquiv.subgroupCongr hf_range)⟩

private theorem isMulCommutative_barImage_iff {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hX : IsPGroup s X) :
    IsMulCommutative ↥(barImage L X) ↔ IsMulCommutative ↥X := by
  obtain ⟨φ⟩ := nonempty_barImage_mulEquiv hXL hs hs2 hX
  rw [isMulCommutative_iff, isMulCommutative_iff]
  constructor
  · intro hc x y
    exact φ.injective (by rw [map_mul, map_mul, hc (φ x) (φ y)])
  · intro hc a b
    obtain ⟨x, rfl⟩ := φ.surjective a
    obtain ⟨y, rfl⟩ := φ.surjective b
    rw [← map_mul, ← map_mul, hc x y]

private theorem pow_eq_one_barImage_iff {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hX : IsPGroup s X) :
    (∀ y ∈ (barImage L X : Subgroup (Bar2 L)), y ^ s = 1) ↔ ∀ x ∈ X, x ^ s = 1 := by
  obtain ⟨φ⟩ := nonempty_barImage_mulEquiv hXL hs hs2 hX
  constructor
  · intro hp x hx
    have hp' : ∀ y : ↥(barImage L X), (y : Bar2 L) ^ s = 1 := fun y => hp y y.2
    have h1 : φ (⟨x, hx⟩ ^ s) = 1 := by
      rw [map_pow]
      exact Subtype.ext (hp' (φ ⟨x, hx⟩))
    have h2 : (⟨x, hx⟩ : ↥X) ^ s = 1 := φ.injective (by simpa using h1)
    simpa using congrArg (fun y : ↥X => (y : G)) h2
  · intro hp y hy
    obtain ⟨x, hx⟩ := φ.surjective ⟨y, hy⟩
    have h1 : φ x ^ s = 1 := by
      rw [← map_pow, show x ^ s = 1 from Subtype.ext (hp x x.2), map_one]
    have h2 : ((φ x : ↥(barImage L X)) : Bar2 L) ^ s = 1 := by
      simpa using congrArg (fun z : ↥(barImage L X) => (z : Bar2 L)) h1
    rwa [congrArg Subtype.val hx] at h2

theorem isElemAbelian_barImage_iff {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hX : IsPGroup s X) : IsElemAbelian s (barImage L X) ↔ IsElemAbelian s X :=
  Iff.and (isMulCommutative_barImage_iff hXL hs hs2 hX)
    (pow_eq_one_barImage_iff hXL hs hs2 hX)

theorem eq_of_barImage_eq {L P X Y : Subgroup G} (hPL : P ≤ L) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hP : IsPGroup s P) (hXP : X ≤ P) (hYP : Y ≤ P)
    (h : barImage L X = barImage L Y) : X = Y := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hs hs2
  let ι : ↥P →* ↥L :=
    { toFun := fun x => ⟨x.1, hPL x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f : ↥P →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp ι
  have hinj : Function.Injective f := by
    intro x y hxy
    have hQ := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
      (N := CFSG.pCore 2 ↥L) (Q := P.subgroupOf L) hsN hP.comap_subtype
    have hxy' : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (P.subgroupOf L).subtype)
        ⟨ι x, x.2⟩ = ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
        (P.subgroupOf L).subtype) ⟨ι y, y.2⟩ := hxy
    have h' := congrArg (fun z : ↥(P.subgroupOf L) => (z : G)) (hQ hxy')
    exact Subtype.ext h'
  have hbar : ∀ Z : Subgroup G, Z ≤ P → barImage L Z = (Z.subgroupOf P).map f := by
    intro Z hZP
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨⟨z.1, hZP (Subgroup.mem_subgroupOf.1 hz)⟩, hz, ?_⟩
      exact hzy
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_map.2
        ⟨⟨z.1, hPL z.2⟩, Subgroup.mem_subgroupOf.2 hz, hzy⟩
  have hXY : X.subgroupOf P = Y.subgroupOf P := by
    have h' : (X.subgroupOf P).map f = (Y.subgroupOf P).map f := by
      rw [← hbar X hXP, ← hbar Y hYP]
      exact h
    have h2 := congrArg (Subgroup.comap f) h'
    rwa [Subgroup.comap_map_eq_self_of_injective hinj,
      Subgroup.comap_map_eq_self_of_injective hinj] at h2
  calc X = (X.subgroupOf P).map P.subtype := (Subgroup.map_subgroupOf_eq_of_le hXP).symm
    _ = (Y.subgroupOf P).map P.subtype := by rw [hXY]
    _ = Y := Subgroup.map_subgroupOf_eq_of_le hYP

theorem exists_barImage_eq {L P : Subgroup G} (hPL : P ≤ L) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hP : IsPGroup s P) {Y : Subgroup (Bar2 L)} (hY : Y ≤ barImage L P) :
    ∃ X : Subgroup G, X ≤ P ∧ barImage L X = Y := by
  refine ⟨barPreimage L Y ⊓ P, inf_le_right, le_antisymm ?_ ?_⟩
  · calc barImage L (barPreimage L Y ⊓ P) ≤ barImage L (barPreimage L Y) :=
          barImage_mono inf_le_left
      _ = Y := barImage_barPreimage L Y
  · intro y hy
    obtain ⟨p, hpP, hpπ⟩ := uc22p21c_mem_barImage.1 (hY hy)
    refine uc22p21c_mem_barImage.2 ⟨p, ?_, hpπ⟩
    exact Subgroup.mem_inf.2
      ⟨uc22p21c_mem_barPreimage.2 ⟨p.2, by rw [hpπ]; exact hy⟩, hpP⟩

theorem isPGroup_barImage_of_isSylowOf {L P : Subgroup G} {s : ℕ} (hs : s.Prime)
    (hP : IsSylowOf s P L) : IsPGroup s (barImage L P) ∧ ¬ s ∣ (barImage L P).index := by
  haveI : Fact s.Prime := ⟨hs⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hbar : barImage L P =
      (Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) Q :
        Subgroup (Bar2 L)) := by
    rw [show barImage L P =
      (P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl, ← hQ]
    exact (Sylow.coe_mapSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) Q).symm
  rw [hbar]
  exact ⟨(Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) Q).isPGroup',
    (Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) Q).not_dvd_index⟩

theorem pRank_centralizer_barImage {L X : Subgroup G} (hXL : X ≤ L) {s r : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hX : IsPGroup s X) (hr : r.Prime) (hr2 : r ≠ 2) :
    Open.pRank r (⊤ ⊓ centralizer (barImage L X : Set (Bar2 L))) =
      Open.pRank r (L ⊓ centralizer (X : Set G)) := by
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hs hs2
  have hrN : ¬ r ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hr hr2
  have h1 := CFSG.GroupTheory.CoprimeTransport.pRank_centralizer_map_mk_eq
    (N := CFSG.pCore 2 ↥L) (s := s) (p := r) hsN hrN (E := X.subgroupOf L) hX.comap_subtype
  have hcent : ∀ z : ↥L, z ∈ Subgroup.centralizer ((X.subgroupOf L : Subgroup ↥L) : Set ↥L)
      ↔ (z : G) ∈ L ⊓ Subgroup.centralizer (X : Set G) := by
    intro z
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc
      refine ⟨z.2, fun x hx => ?_⟩
      exact congrArg (fun w : ↥L => (w : G)) (hc ⟨x, hXL hx⟩ hx)
    · rintro ⟨-, hc⟩ x hx
      exact Subtype.ext (hc x.1 (Subgroup.mem_subgroupOf.1 hx))
  have hcent2 : (Subgroup.centralizer ((X.subgroupOf L : Subgroup ↥L) : Set ↥L)).map
      L.subtype = L ⊓ Subgroup.centralizer (X : Set G) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hcent z).1 hz
    · intro hy
      exact ⟨⟨y, hy.1⟩, (hcent ⟨y, hy.1⟩).2 hy, rfl⟩
  have h2 : Open.pRank r
      (Subgroup.centralizer ((X.subgroupOf L : Subgroup ↥L) : Set ↥L)) =
      Open.pRank r (L ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [← hcent2]
    exact (CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective r hr
      L.subtype L.subtype_injective _).symm
  rw [show barImage L X =
    (X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl, top_inf_eq, h1, h2]

theorem barImage_inf_centralizer_eq {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hX : IsPGroup s X) :
    barImage L (L ⊓ centralizer (X : Set G)) =
      ⊤ ⊓ centralizer (barImage L X : Set (Bar2 L)) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hs hs2
  have hsub : (L ⊓ centralizer (X : Set G)).subgroupOf L =
      Subgroup.centralizer ((X.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hc⟩ x hx
      exact Subtype.ext (hc x.1 (Subgroup.mem_subgroupOf.1 hx))
    · intro hc
      exact ⟨z.2, fun x hx => congrArg (fun w : ↥L => (w : G)) (hc ⟨x, hXL hx⟩ hx)⟩
  rw [show ⊤ ⊓ centralizer (barImage L X : Set (Bar2 L)) =
      Subgroup.centralizer (barImage L X : Set (Bar2 L)) from top_inf_eq _,
    show barImage L (L ⊓ centralizer (X : Set G)) =
      ((L ⊓ centralizer (X : Set G)).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl, hsub,
    ← CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := s) hsN
      (Q := X.subgroupOf L) hX.comap_subtype]
  rfl

theorem barImage_derInf8_eq {L C : Subgroup G} (hCL : C ≤ L) {Cb : Subgroup (Bar2 L)}
    (hCb : barImage L C = Cb) :
    barImage L (F08.DerInf8 C) = F08.DerInf8 Cb := by
  have hJsub : (F08.DerInf8 C).subgroupOf L = F08.DerInf8 (C.subgroupOf L) := by
    rw [show F08.DerInf8 C = (CFSG.perfectResidual C).map C.subtype from rfl,
      CFSG.perfectResidual_subtype_subgroupOf C L hCL]
    rfl
  have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (C.subgroupOf L)
  have hmapC : (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Cb := hCb
  rw [hmapC] at h
  rw [show barImage L (F08.DerInf8 C) =
    ((F08.DerInf8 C).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl, hJsub]
  exact h

private theorem nonempty_bar2_equiv_of_barImage_eq {L J : Subgroup G} {Jb : Subgroup (Bar2 L)}
    (hJL : J ≤ L) (hJb : barImage L J = Jb) : Nonempty (Bar2 J ≃* Bar2 Jb) := by
  let ι : ↥J →* ↥L :=
    { toFun := fun x => ⟨x.1, hJL x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let πJ : ↥J →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp ι
  let φ : ↥J →* ↥Jb :=
    { toFun := fun x => ⟨πJ x, by
        have hx : πJ x ∈ barImage L J :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)
        rwa [hJb] at hx⟩
      map_one' := Subtype.ext (map_one πJ)
      map_mul' := fun x y => Subtype.ext (map_mul πJ x y) }
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : (y : Bar2 L) ∈ barImage L J := by
      rw [hJb]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨z.1, hz⟩, Subtype.ext hzy⟩
  have hker : IsPGroup 2 φ.ker := by
    have hmem : ∀ x : ↥φ.ker, ι x.1 ∈ CFSG.pCore 2 ↥L := by
      intro x
      have hx : φ x.1 = 1 := (MonoidHom.mem_ker).1 x.2
      have h1 : πJ x.1 = 1 := congrArg Subtype.val hx
      have h2 : ι x.1 ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := MonoidHom.mem_ker.2 h1
      rwa [QuotientGroup.ker_mk'] at h2
    let ψ : ↥φ.ker →* ↥(CFSG.pCore 2 ↥L) :=
      { toFun := fun x => ⟨ι x.1, hmem x⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun _ _ => Subtype.ext rfl }
    have hψinj : Function.Injective ψ := by
      intro x y hxy
      have h1 : ι x.1 = ι y.1 := congrArg Subtype.val hxy
      have h2 : (x.1 : ↥J) = y.1 :=
        Subtype.ext (congrArg (fun z : ↥L => (z : G)) h1)
      exact Subtype.ext h2
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_injective ψ hψinj
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2)
    φ hsurj hker

theorem nonempty_bar2_derInf8_equiv {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hX : IsPGroup s X) :
    Nonempty (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G))) ≃*
      Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (barImage L X : Set (Bar2 L))))) := by
  have hCb := barImage_inf_centralizer_eq hXL hs hs2 hX
  have hJb := barImage_derInf8_eq inf_le_left hCb
  refine nonempty_bar2_equiv_of_barImage_eq ?_ hJb
  exact (Subgroup.map_subtype_le (H := L ⊓ centralizer (X : Set G))
    (CFSG.perfectResidual _)).trans inf_le_left

private theorem isU3_barImage_iff {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hX : IsPGroup s X) :
    (IsU3 (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (barImage L X : Set (Bar2 L))))) 2 ↔
      IsU3 (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G)))) 2) := by
  obtain ⟨e⟩ := nonempty_bar2_derInf8_equiv hXL hs hs2 hX
  constructor
  · intro h
    exact show IsU3 (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G)))) 2 from
      CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSU) (n := 3) (p := 2) (f := 2) e.symm
        (show LieModel (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer
          (barImage L X : Set (Bar2 L))))) .PSU 3 2 2 from h)
  · intro h
    exact show IsU3 (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer
        (barImage L X : Set (Bar2 L))))) 2 from
      CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSU) (n := 3) (p := 2) (f := 2) e
        (show LieModel (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G)))) .PSU 3 2 2 from h)

private theorem isL2_barImage_iff {L X : Subgroup G} (hXL : X ≤ L) {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hX : IsPGroup s X) (n : ℕ) :
    (IsL2 (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer (barImage L X : Set (Bar2 L))))) n ↔
      IsL2 (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G)))) n) := by
  obtain ⟨e⟩ := nonempty_bar2_derInf8_equiv hXL hs hs2 hX
  constructor
  · intro h
    exact show IsL2 (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G)))) n from
      CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e.symm
        (show LieModel (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer
          (barImage L X : Set (Bar2 L))))) .PSL 2 2 n from h)
  · intro h
    exact show IsL2 (Bar2 (F08.DerInf8 (⊤ ⊓ centralizer
        (barImage L X : Set (Bar2 L))))) n from
      CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e
        (show LieModel (Bar2 (F08.DerInf8 (L ⊓ centralizer (X : Set G)))) .PSL 2 2 n from h)

theorem notationA8103_barImage_iff {L P A : Subgroup G} {p n : ℕ} (hPL : P ≤ L)
    (hP : IsPGroup 3 P) (hp : p.Prime) (hp2 : p ≠ 2) (hAP : A ≤ P) :
    F08.NotationA8103 ⊤ (barImage L P) p n (barImage L A) ↔ F08.NotationA8103 L P p n A := by
  have hAL : A ≤ L := hAP.trans hPL
  have hA : IsPGroup 3 A := hP.to_le hAP
  have hcard : Nat.card (barImage L A) = 3 ↔ Nat.card A = 3 := by
    rw [card_barImage_of_isPGroup hAL Nat.prime_three (by norm_num) hA]
  have hU3 := isU3_barImage_iff hAL Nat.prime_three (by norm_num) hA
  have hL2 := isL2_barImage_iff hAL Nat.prime_three (by norm_num) hA n
  have hrank : Open.pRank p (⊤ ⊓ centralizer (barImage L A : Set (Bar2 L))) =
      Open.pRank p (L ⊓ centralizer (A : Set G)) :=
    pRank_centralizer_barImage hAL Nat.prime_three (by norm_num) hA hp hp2
  unfold F08.NotationA8103
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨hcard.1 h1, hAP, ?_, ?_⟩
    · rcases h3 with h3 | h3
      · exact Or.inl (hU3.1 h3)
      · exact Or.inr (hL2.1 h3)
    · rw [← hrank]
      exact h4
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨hcard.2 h1, barImage_mono hAP, ?_, ?_⟩
    · rcases h3 with h3 | h3
      · exact Or.inl (hU3.2 h3)
      · exact Or.inr (hL2.2 h3)
    · rw [hrank]
      exact h4

theorem notationB8103_barImage_iff {L P B : Subgroup G} {n : ℕ} (hPL : P ≤ L)
    (hP : IsPGroup 3 P) (hBP : B ≤ P) :
    F08.NotationB8103 ⊤ (barImage L P) n (barImage L B) ↔ F08.NotationB8103 L P n B := by
  have hBL : B ≤ L := hBP.trans hPL
  have hB : IsPGroup 3 B := hP.to_le hBP
  have hcard : Nat.card (barImage L B) = 3 ↔ Nat.card B = 3 := by
    rw [card_barImage_of_isPGroup hBL Nat.prime_three (by norm_num) hB]
  have hL2 := isL2_barImage_iff hBL Nat.prime_three (by norm_num) hB (2 * n)
  unfold F08.NotationB8103 F08.KOf8103
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨hcard.1 h1, hBP, hL2.1 h3⟩
  · rintro ⟨h1, -, h3⟩
    exact ⟨hcard.2 h1, barImage_mono hBP, hL2.2 h3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
