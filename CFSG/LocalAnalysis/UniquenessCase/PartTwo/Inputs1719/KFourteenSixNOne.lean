module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNCoprime
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GLift
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.GroupTheory.OppositeRadicals
public import CFSG.Goldschmidt.Steps.Sec82Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNSolv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem barIn_eq_bot_iff_OInf {H X : Subgroup G} (hX : X ≤ H) :
    barIn H X = ⊥ ↔ X ≤ UC22.OInf H := by
  unfold barIn
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · intro h x hx
    refine (Subgroup.mem_map (f := H.subtype)).mpr ⟨⟨x, hX hx⟩, ?_, rfl⟩
    exact h (show (⟨x, hX hx⟩ : ↥H) ∈ X.subgroupOf H from hx)
  · intro h y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (h hy)
    have hzy' : z = y := Subtype.ext hzy
    simpa [hzy'] using hz

variable [Finite G] {N T A K : Subgroup G} {r : ℕ}

theorem Hyp146N.inf_sup_OInf_eq (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) (hATK : A ⊔ T ≤ K)
    (hNK : N ⊓ normalizer (A : Set G) ≤ K)
    (hgen : barIn (UC22.conjClosure N A) T ⊔
      normalizer (barIn (UC22.conjClosure N A) A : Set (UC22.BarInf (UC22.conjClosure N A))) = ⊤) :
    K ⊓ UC22.conjClosure N A ⊔ UC22.OInf (UC22.conjClosure N A) = UC22.conjClosure N A := by
  set H := UC22.conjClosure N A with hH
  have hKbar : barIn H K = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le ?_ ?_
    · refine Subgroup.map_mono (Subgroup.subgroupOf_mono H ?_)
      exact (le_sup_right : T ≤ A ⊔ T).trans hATK
    · refine (h.normalizer_barIn_le hns).trans (Subgroup.map_mono ?_)
      exact Subgroup.subgroupOf_mono H hNK
  have hsup : (K.subgroupOf H) ⊔ CFSG.solvableRadical ↥H = ⊤ := by
    have hKbar' : (K.subgroupOf H).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥H)) = ⊤ := hKbar
    have h := Subgroup.comap_map_eq
      (f := QuotientGroup.mk' (CFSG.solvableRadical ↥H)) (K.subgroupOf H)
    rw [hKbar', Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have := congrArg (Subgroup.map H.subtype) hsup
  rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
    Subgroup.range_subtype] at this

theorem Hyp146N.commutator_OInf_le (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A))
    (hsimple : IsSimpleGroup (UC22.BarInf (UC22.conjClosure N A)))
    (hQ : ∃ Q : Subgroup (UC22.BarInf (UC22.conjClosure N A)), IsPGroup 2 Q ∧
      barIn (UC22.conjClosure N A) A ≤ normalizer (Q : Set (UC22.BarInf (UC22.conjClosure N A))) ∧
        ⁅Q, barIn (UC22.conjClosure N A) A⁆ ≠ ⊥) :
    ⁅UC22.OInf (UC22.conjClosure N A), A⁆ ≤
      CFSG.Open.pCoreOf 2 (UC22.OInf (UC22.conjClosure N A)) := by
  classical
  have hTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr3 : 3 < r := h.three_lt
  have hr2 : (2 : ℕ) ≠ r := by omega
  have hr4 : 4 < r := by
    have h5 := h.prime.five_le_of_ne_two_of_ne_three (by omega) (by omega)
    omega
  set H := UC22.conjClosure N A with hH
  set R := UC22.OInf H with hR
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hRH : R ≤ H := UC22.OInf_le H
  have hR'def : CFSG.solvableRadical ↥H = R.subgroupOf H := (UC22.OInf_subgroupOf H).symm
  have hR'map : (CFSG.solvableRadical ↥H).map H.subtype = R := by
    rw [hR'def, Subgroup.map_subgroupOf_eq_of_le hRH]
  let R2' : Subgroup ↥H := (CFSG.Open.pCoreOf 2 R).subgroupOf H
  have hR2'leR : CFSG.Open.pCoreOf 2 R ≤ R := CFSG.LieType.BorelTits.pCoreOf_le 2 R
  have hR2'leR' : R2' ≤ CFSG.solvableRadical ↥H := by
    rw [hR'def]
    exact Subgroup.subgroupOf_mono H hR2'leR
  have hR2'map : R2'.map H.subtype = CFSG.Open.pCoreOf 2 R :=
    Subgroup.map_subgroupOf_eq_of_le (hR2'leR.trans hRH)
  have hR2'2 : IsPGroup 2 R2' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R).comap_subtype
  have hHnormR2 : H ≤ normalizer (CFSG.Open.pCoreOf 2 R : Set G) :=
    (UC22.le_normalizer_OInf H).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 R)
  have hR2'normal : R2'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnormR2
  have hR2'inst : R2'.Normal := hR2'normal
  let π : ↥H →* (↥H ⧸ R2') := QuotientGroup.mk' R2'
  let Y : Subgroup (↥H ⧸ R2') := (CFSG.solvableRadical ↥H).map π
  have hYnormal : Y.Normal :=
    (inferInstance : (CFSG.solvableRadical ↥H).Normal).map π
      (QuotientGroup.mk'_surjective R2')
  have hYinst : Y.Normal := hYnormal
  have hR'solv : Group.IsSolvable (CFSG.solvableRadical ↥H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hYsolv : Group.IsSolvable Y := by
    have hR'solvI : Group.IsSolvable (CFSG.solvableRadical ↥H) := hR'solv
    exact Group.isSolvable_of_surjective (f := π.subgroupMap (CFSG.solvableRadical ↥H))
      (MonoidHom.subgroupMap_surjective π (CFSG.solvableRadical ↥H))
  have hR2'eq : R2' = CFSG.Open.pCoreOf 2 (CFSG.solvableRadical ↥H) := by
    have hpc := CFSG.GroupTheory.pCoreOf_map_of_injective 2 H.subtype
      H.subtype_injective (CFSG.solvableRadical ↥H)
    rw [hR'map] at hpc
    have h2 := congrArg (fun S : Subgroup G => S.subgroupOf H) hpc
    simpa [R2', Subgroup.comap_map_eq_self_of_injective H.subtype_injective] using h2
  have hY2 : CFSG.Open.pCoreOf 2 Y = ⊥ := by
    let P : Subgroup (↥H ⧸ R2') := CFSG.Open.pCoreOf 2 Y
    have hPleY : P ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
    have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
    have hPnormal : P.Normal := by
      have hchar : (CFSG.pCore 2 ↥Y).Characteristic :=
        CFSG.LieType.BorelTits.pCore_characteristic 2
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      exact (Subgroup.le_normalizer_of_normal (H := Y)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (G := ↥H ⧸ R2') (H := Y) (CFSG.pCore 2 ↥Y))
    let P' : Subgroup ↥H := P.comap π
    have hP'2 : IsPGroup 2 P' := by
      have hker2 : IsPGroup 2 π.ker := by
        rw [show π.ker = R2' from QuotientGroup.ker_mk' R2']
        exact hR2'2
      exact hP2.comap_of_ker_isPGroup π hker2
    have hP'normal : P'.Normal := hPnormal.comap π
    have hP'leR' : P' ≤ CFSG.solvableRadical ↥H := by
      have h := Subgroup.comap_mono (f := π) hPleY
      rw [show Y.comap π = CFSG.solvableRadical ↥H ⊔ π.ker by
        dsimp [Y]
        rw [Subgroup.comap_map_eq]] at h
      rwa [show π.ker = R2' from QuotientGroup.ker_mk' R2',
        sup_eq_left.mpr hR2'leR'] at h
    have hP'R2 : P' ≤ R2' := by
      rw [hR2'eq]
      refine CFSG.LieType.BorelTits.le_pCoreOf (r := 2) (N := P')
        (H := CFSG.solvableRadical ↥H) hP'leR' ?_ hP'2
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hP'leR').mpr
        (Subgroup.le_normalizer_of_normal (H := P'))
    have hPbot : P = ⊥ := by
      have hmapbot : P'.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, show π.ker = R2' from QuotientGroup.ker_mk' R2']
        exact hP'R2
      calc P = P'.map π := (Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective R2') P).symm
        _ = ⊥ := hmapbot
    exact hPbot
  have hrank : ∀ s : ℕ, s.Prime → s ≠ 2 → ∀ P : Subgroup (↥H ⧸ R2'),
      P ≤ Y → IsPGroup s P → CFSG.Open.pRank s P ≤ 2 := by
    intro s hs hs2 P hPY hP
    have hsFact : Fact s.Prime := ⟨hs⟩
    obtain ⟨S, hSR', hS2, hSmap, hrank_eq⟩ :=
      exists_isPGroup_map_eq_of_two (Γ := ↥H) (K := R2') hR2'2 hs2 (Y := CFSG.solvableRadical ↥H)
        hR2'leR' hP (by simpa [Y] using hPY)
    rw [hrank_eq]
    have hSR : S.map H.subtype ≤ R := by
      rw [← hR'map]
      exact Subgroup.map_mono hSR'
    have h1 : CFSG.Open.pRank s S ≤ CFSG.Open.pRank s (S.map H.subtype) :=
      CFSG.SectionRank.pRank_le_map (p := s) hs.one_lt H.subtype H.subtype_injective S
    have h2 : CFSG.Open.pRank s (S.map H.subtype) ≤ CFSG.Open.pRank s R :=
      CFSG.RankThreeEvenClassification.Helpers.pRank_mono s hs hSR
    exact (h1.trans h2).trans (pRank_le_two_of_le (G := G) (N := N) (P := R) hs hs2
      (hRH.trans h.conjClosure_le) h.rank_three h.rank_two)
  obtain ⟨Q0, hQ0_2, hQ0_norm, hQ0_comm⟩ := hQ
  obtain ⟨S, hSH, hS2, hAS, hbarS⟩ :=
    h.exists_lift hns Nat.prime_two hr2 hQ0_2 hQ0_norm
  let S' : Subgroup ↥H := S.subgroupOf H
  let A' : Subgroup ↥H := A.subgroupOf H
  let Q : Subgroup (↥H ⧸ R2') := S'.map π
  let AΓ : Subgroup (↥H ⧸ R2') := A'.map π
  have hS'2 : IsPGroup 2 S' := hS2.comap_subtype (K := H)
  have hQ2 : IsPGroup 2 Q := hS'2.map π
  have hcardA' : Nat.card A' = r := by
    have hcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
    simpa [A'] using hcard.trans h.card
  have hA'2 : IsPGroup r A' := IsPGroup.of_card (n := 1) (by simpa using hcardA')
  have hAΓ2 : IsPGroup r AΓ := hA'2.map π
  have hAS' : A' ≤ Subgroup.normalizer (S' : Set ↥H) := by
    intro a ha
    have haG : (a : G) ∈ A := ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hfixG : S.map (MulAut.conj (a : G)) = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAS haG)
    have hmaps : (S'.map (MulAut.conj a)).map H.subtype = S := by
      rw [Subgroup.map_map]
      change S'.map (H.subtype.comp (MulAut.conj a).toMonoidHom) = S
      have hcomp : H.subtype.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (a : G)).toMonoidHom.comp H.subtype := by
        ext x
        simp [MulAut.conj_apply]
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hSH]
      exact hfixG
    have h := congrArg (fun X : Subgroup G => X.subgroupOf H) hmaps
    simpa [S', Subgroup.comap_map_eq_self_of_injective H.subtype_injective] using h
  have hAQ : AΓ ≤ Subgroup.normalizer (Q : Set (↥H ⧸ R2')) := by
    calc AΓ = A'.map π := rfl
      _ ≤ (Subgroup.normalizer (S' : Set ↥H)).map π := Subgroup.map_mono hAS'
      _ ≤ Subgroup.normalizer (S'.map π) := Subgroup.le_normalizer_map π
      _ = Subgroup.normalizer (Q : Set (↥H ⧸ R2')) := rfl
  have hSAbar_ne : barIn H ⁅S, A⁆ ≠ ⊥ := by
    rw [barIn_commutator hSH hAH, hbarS]
    exact hQ0_comm
  have hSAnleR : ¬ ⁅S, A⁆ ≤ R := fun hle =>
    hSAbar_ne ((barIn_eq_bot_iff_OInf (Subgroup.commutator_le_of_le hSH hAH)).mpr hle)
  have hSA'nleR' : ¬ ⁅S', A'⁆ ≤ CFSG.solvableRadical ↥H := by
    intro hle
    apply hSAnleR
    have hmap := Subgroup.map_mono (f := H.subtype) hle
    have hmap_eq : (⁅S', A'⁆).map H.subtype = ⁅S, A⁆ := by
      change (⁅S.subgroupOf H, A.subgroupOf H⁆).map H.subtype = ⁅S, A⁆
      exact CFSG.commutator_subgroupOf_map_eq H A S hAH hSH
    rwa [hmap_eq, hR'map] at hmap
  have hQAnleY : ¬ ⁅Q, AΓ⁆ ≤ Y := by
    intro hle
    apply hSA'nleR'
    have hmap : (⁅S', A'⁆).map π ≤ Y := by
      rw [Subgroup.map_commutator]
      simpa [Q, AΓ] using hle
    have hcomap := (Subgroup.map_le_iff_le_comap).mp hmap
    rwa [show Y.comap π = CFSG.solvableRadical ↥H ⊔ π.ker by
        dsimp [Y]
        rw [Subgroup.comap_map_eq],
      show π.ker = R2' from QuotientGroup.ker_mk' R2',
      sup_eq_left.mpr hR2'leR'] at hcomap
  let C : Subgroup (↥H ⧸ R2') :=
    Subgroup.centralizer (CFSG.fittingSubgroupOf Y : Set (↥H ⧸ R2'))
  have hFnormal : (CFSG.fittingSubgroupOf Y).Normal :=
    CFSG.fittingSubgroupOf_normal Y hYnormal
  have hCnormal : C.Normal := by
    have hFinst : (CFSG.fittingSubgroupOf Y).Normal := hFnormal
    infer_instance
  have hmain : ⁅Q, AΓ⁆ ≤ C :=
    commutator_le_centralizer_fittingSubgroupOf h.prime hr4
      hAΓ2 hQ2 hYsolv hY2
      (Subgroup.le_normalizer_of_normal (K := Q) (H := Y))
      (Subgroup.le_normalizer_of_normal (K := AΓ) (H := Y)) hAQ hrank
  let Ch : Subgroup ↥H := C.comap π
  have hChnormal : Ch.Normal := hCnormal.comap π
  let ρ : ↥H →* UC22.BarInf H := QuotientGroup.mk' (CFSG.solvableRadical ↥H)
  let Kbar : Subgroup (UC22.BarInf H) := Ch.map ρ
  have hKbar_normal : Kbar.Normal :=
    hChnormal.map ρ (QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥H))
  have hKbar_ne : Kbar ≠ ⊥ := by
    intro hbot
    apply hQAnleY
    have hChleR' : Ch ≤ CFSG.solvableRadical ↥H := by
      have h := (Subgroup.map_eq_bot_iff Ch (f := ρ)).mp hbot
      rwa [show ρ.ker = CFSG.solvableRadical ↥H from
        QuotientGroup.ker_mk' (CFSG.solvableRadical ↥H)] at h
    have hCleY : C ≤ Y := by
      have hCeq : C = Ch.map π :=
        (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R2') C).symm
      rw [hCeq]
      calc Ch.map π ≤ (CFSG.solvableRadical ↥H).map π := Subgroup.map_mono hChleR'
        _ = Y := rfl
    exact hmain.trans hCleY
  have hKbar_top : Kbar = ⊤ := by
    have hKbarInst : Kbar.Normal := hKbar_normal
    exact (hsimple.eq_bot_or_eq_top_of_normal Kbar).resolve_left hKbar_ne
  have hChsup : Ch ⊔ CFSG.solvableRadical ↥H = ⊤ := by
    have h := Subgroup.comap_map_eq (f := ρ) Ch
    rw [show Ch.map ρ = ⊤ from hKbar_top, Subgroup.comap_top,
      show ρ.ker = CFSG.solvableRadical ↥H from
        QuotientGroup.ker_mk' (CFSG.solvableRadical ↥H)] at h
    exact h.symm
  have hChindex_dvd : Ch.index ∣ Nat.card (CFSG.solvableRadical ↥H) := by
    rw [Subgroup.index_eq_card]
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' Ch).comp (CFSG.solvableRadical ↥H).subtype) := by
      intro x
      obtain ⟨hx, rfl⟩ := QuotientGroup.mk'_surjective Ch x
      have hxsup : hx ∈ Ch ⊔ CFSG.solvableRadical ↥H := hChsup ▸ Subgroup.mem_top hx
      rw [Subgroup.mem_sup_of_normal_left] at hxsup
      obtain ⟨c, hc, d, hd, hcd⟩ := hxsup
      refine ⟨⟨d, hd⟩, ?_⟩
      rw [← hcd, map_mul,
        show (QuotientGroup.mk' Ch) c = 1 from (QuotientGroup.eq_one_iff c).mpr hc,
        one_mul]
      rfl
    exact Subgroup.card_dvd_of_surjective
      (f := (QuotientGroup.mk' Ch).comp (CFSG.solvableRadical ↥H).subtype) hsurj
  have hcardR' : Nat.card (CFSG.solvableRadical ↥H) = Nat.card R := by
    rw [hR'def]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hRnot : ¬ r ∣ Nat.card R := by
    rw [hR]
    exact h.not_dvd_card_OInf hns
  have hChnotdvd : ¬ r ∣ Ch.index := by
    intro hdvd
    apply hRnot
    rw [← hcardR']
    exact hdvd.trans hChindex_dvd
  have hA'leCh : A' ≤ Ch := by
    intro a ha
    have h1 : orderOf (QuotientGroup.mk' Ch a) ∣ orderOf a := orderOf_map_dvd _ a
    have h2 : orderOf a ∣ r := by
      rw [← hcardA']
      exact Subgroup.orderOf_dvd_natCard A' ha
    have h3 : orderOf (QuotientGroup.mk' Ch a) ∣ Ch.index := by
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime r Ch.index :=
      (h.prime.coprime_iff_not_dvd).mpr hChnotdvd
    have hone := Nat.eq_one_of_dvd_coprimes hcop (h1.trans h2) h3
    exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp hone)
  have hAΓC : AΓ ≤ C := by
    change A'.map π ≤ C
    rw [← Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective R2') C]
    exact Subgroup.map_mono hA'leCh
  have hYdvd : Nat.card Y ∣ Nat.card R := by
    have h := Subgroup.card_map_dvd (f := π) (CFSG.solvableRadical ↥H)
    rwa [hcardR'] at h
  have hrY : ¬ r ∣ Nat.card Y := fun hd => hRnot (hd.trans hYdvd)
  obtain ⟨n, hn⟩ := hAΓ2.exists_card_dvd_pow
  have hcop : Nat.Coprime (Nat.card AΓ) (Nat.card Y) :=
    Nat.Coprime.of_dvd_left hn
      (Nat.Coprime.pow_left n ((h.prime.coprime_iff_not_dvd).mpr hrY))
  have hYcent : Y ≤ Subgroup.centralizer (AΓ : Set (↥H ⧸ R2')) :=
    CFSG.Goldschmidt.Sec82.le_centralizer_of_coprime_of_fitting hYsolv
      (Subgroup.le_normalizer_of_normal (K := AΓ) (H := Y)) hcop
      (Subgroup.le_centralizer_iff.mp hAΓC)
  have hcommY : ⁅Y, AΓ⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYcent
  have hR'A'le : ⁅CFSG.solvableRadical ↥H, A'⁆ ≤ R2' := by
    have hmap : (⁅CFSG.solvableRadical ↥H, A'⁆).map π = ⊥ := by
      rw [Subgroup.map_commutator]
      simpa [AΓ] using hcommY
    have h := (Subgroup.map_eq_bot_iff ⁅CFSG.solvableRadical ↥H, A'⁆ (f := π)).mp hmap
    rwa [show π.ker = R2' from QuotientGroup.ker_mk' R2'] at h
  calc ⁅R, A⁆ = (⁅R.subgroupOf H, A.subgroupOf H⁆).map H.subtype :=
        (CFSG.commutator_subgroupOf_map_eq H A R hAH hRH).symm
    _ = (⁅CFSG.solvableRadical ↥H, A'⁆).map H.subtype := by
        rw [← hR'def]
    _ ≤ R2'.map H.subtype := Subgroup.map_mono hR'A'le
    _ = CFSG.Open.pCoreOf 2 R := hR2'map

theorem Hyp146N.pCoreOf_OInf_le (h : Hyp146N N T A r) :
    CFSG.Open.pCoreOf 2 (UC22.OInf (UC22.conjClosure N A)) ≤ T := by
  have hTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := UC22.conjClosure N A with hH
  set R := UC22.OInf H with hR
  have hHle : H ≤ N := h.conjClosure_le
  have hNH : N ≤ normalizer (H : Set G) := UC22.uc22p22v_le_normalizer_conjClosure N A
  have hRH : R ≤ H := UC22.OInf_le H
  have hHR : H ≤ normalizer (R : Set G) := UC22.le_normalizer_OInf H
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ H) H :=
    h.sylow.inf_of_le_normalizer hHle hNH
  have hOHle : CFSG.Open.pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hOH2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHnormOH : H ≤ normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hOHTH : CFSG.Open.pCoreOf 2 H ≤ T ⊓ H := by
    have hsup2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 H ⊔ (T ⊓ H) : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hOH2 hTH.isPGroup
        ((inf_le_right : T ⊓ H ≤ H).trans hHnormOH)
    have heq : CFSG.Open.pCoreOf 2 H ⊔ (T ⊓ H) = T ⊓ H :=
      hTH.eq_of_le le_sup_right (sup_le hOHle inf_le_right) hsup2
    exact le_sup_left.trans_eq heq
  exact (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hRH hHR).trans
    (hOHTH.trans inf_le_left)

theorem Hyp146N.conjClosure_le_of_sup_eq (h : Hyp146N N T A r) (hAK : A ≤ K)
    (hsup : K ⊓ UC22.conjClosure N A ⊔ UC22.OInf (UC22.conjClosure N A) = UC22.conjClosure N A)
    (hcomm : ⁅UC22.OInf (UC22.conjClosure N A), A⁆ ≤ K) :
    UC22.conjClosure N A ≤ K := by
  set H := UC22.conjClosure N A with hH
  set R := UC22.OInf H with hR
  have hRH : R ≤ H := UC22.OInf_le H
  have hsup' : ((K ⊓ H).subgroupOf H) ⊔ (R.subgroupOf H) = ⊤ := by
    have h := congrArg (fun S : Subgroup G => S.subgroupOf H) hsup
    rw [Subgroup.subgroupOf_sup inf_le_right hRH, Subgroup.subgroupOf_self] at h
    exact h
  have hRnormal : (R.subgroupOf H).Normal := by
    rw [hR, UC22.OInf_subgroupOf]
    infer_instance
  have hdecomp : ∀ x ∈ H, ∃ y ∈ K ⊓ H, ∃ z ∈ R, x = y * z := by
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥H) ∈ ((K ⊓ H).subgroupOf H) ⊔ (R.subgroupOf H) := by
      rw [hsup']; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := hmem
    exact ⟨(y : G), hy, (z : G), hz, (congrArg Subtype.val hyz).symm⟩
  refine iSup₂_le fun L hL => ?_
  obtain ⟨g, hg, rfl⟩ := hL
  obtain ⟨x, hxH, hxeq⟩ := h.exists_conj_eq hg
  rw [hxeq]
  intro w hw
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨y, hy, z, hz, hx_eq⟩ := hdecomp x hxH
  have hyK : y ∈ K := hy.1
  have hzR : z ∈ R := hz
  have hza : z * a * z⁻¹ = ⁅z, a⁆ * a := by
    rw [commutatorElement_def]; group
  have hcK : ⁅z, a⁆ ∈ K := hcomm (Subgroup.commutator_mem_commutator hzR ha)
  rw [hx_eq]
  show (MulAut.conj (y * z)) a ∈ K
  rw [show (MulAut.conj (y * z)) a = (y * ⁅z, a⁆ * y⁻¹) * (y * a * y⁻¹) by
    rw [MulAut.conj_apply]
    calc y * z * a * (y * z)⁻¹ = y * (z * a * z⁻¹) * y⁻¹ := by group
      _ = y * (⁅z, a⁆ * a) * y⁻¹ := by rw [hza]
      _ = (y * ⁅z, a⁆ * y⁻¹) * (y * a * y⁻¹) := by group]
  exact K.mul_mem
    (K.mul_mem (K.mul_mem hyK hcK) (K.inv_mem hyK))
    (K.mul_mem (K.mul_mem hyK (hAK ha)) (K.inv_mem hyK))

theorem Hyp146N.conjClosure_le_of_barOne (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) (hATK : A ⊔ T ≤ K)
    (hNK : N ⊓ normalizer (A : Set G) ≤ K)
    (h1 : BarOne (barIn (UC22.conjClosure N A) A) (barIn (UC22.conjClosure N A) T)) :
    UC22.conjClosure N A ≤ K := by
  obtain ⟨hsimple, hgen, hQ⟩ := h1
  exact h.conjClosure_le_of_sup_eq (le_sup_left.trans hATK) (h.inf_sup_OInf_eq hns hATK hNK hgen)
    ((h.commutator_OInf_le hns hsimple hQ).trans
      (h.pCoreOf_OInf_le.trans (le_sup_right.trans hATK)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN
