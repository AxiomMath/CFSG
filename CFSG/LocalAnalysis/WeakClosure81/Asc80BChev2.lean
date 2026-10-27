module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BFrame
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitDefs

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Orbit
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2OrbitFrame
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamCl
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2FamEx
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2G2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Tits
import CFSG.LocalAnalysis.WeakClosure81.FiveSevenRed
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal

@[expose] def Asc80BGraphEscape (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L A T : Subgroup Q), L.Normal → IsSimpleGroup ↥L →
    (∃ x y : ↥L, x * y ≠ y * x) → P ↥L → centralizer (L : Set Q) = ⊥ → IsSylowIn 2 T ⊤ →
    L ⊔ T = ⊤ → A ≤ T → IsElemAbelian 2 A →
    ∀ a ∈ A, ActsOnDynkinMod ⊥ L a →
      ¬ L ⊓ centralizer ({a} : Set Q) ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q)

private theorem exists_umaxBQ_of_hasBQRank {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    {r : ℕ} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hQR : Chev2Orbit.HasBQRank ↥L r) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K)
      (nn : Fin D.rank → K) (H : Fin D.rank → Subgroup K) (π : K →* ↥L) (e : ℕ),
      D.rank = r ∧ Chev2Orbit.UMaxBQ L T M D nn H π e := by
  obtain ⟨K, hK, hKfin, D, nn, H, π, e, hBQ, hrank⟩ := hQR
  obtain ⟨π', hU⟩ := Chev2Orbit.exists_umaxBQ hLn hLs hnab hT hMt hMax hBQ
  exact ⟨K, hK, hKfin, D, nn, H, π', e, hrank, hU⟩

private theorem false_of_hasBQRank_three_le {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    {r : ℕ} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hQR : Chev2Orbit.HasBQRank ↥L r) (hr : 3 ≤ r) : False := by
  obtain ⟨K, hK, hKfin, D, nn, H, π, e, hrank, hU⟩ :=
    exists_umaxBQ_of_hasBQRank hLn hLs hnab hT hMt hMax hQR
  have := hU.rank_le_two
  omega

private theorem false_of_hasBQUneven {Q : Type} [Group Q] [Finite Q] {L T M : Subgroup Q}
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hT : IsSylowIn 2 T ⊤) (hMt : M < ⊤)
    (hMax : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M)
    (hQU : Chev2Orbit.HasBQUneven ↥L) : False := by
  obtain ⟨K, hK, hKfin, D, nn, H, π, e, hBQ, i, j, hne⟩ := hQU
  obtain ⟨π', hU⟩ := Chev2Orbit.exists_umaxBQ hLn hLs hnab hT hMt hMax hBQ
  exact hne (hU.card_rootGroup_eq i j)

private theorem asc80NoUMax_of_hasBQRank {P : ∀ (X : Type) [Group X], Prop} {r : ℕ}
    (hP : ∀ (X : Type) [Group X], P X → Chev2Orbit.HasBQRank X r) (hr : 3 ≤ r) :
    Asc80NoUMax P := by
  intro Q _ _ L T hLn hLs hnab hC hPL hT hM
  obtain ⟨M, hMt, hMax⟩ := hM
  exact false_of_hasBQRank_three_le hLn hLs hnab hT hMt hMax (hP ↥L hPL) hr

theorem asc80NoUMax_of_hasBQUneven {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X], P X → Chev2Orbit.HasBQUneven X) : Asc80NoUMax P := by
  intro Q _ _ L T hLn hLs hnab hC hPL hT hM
  obtain ⟨M, hMt, hMax⟩ := hM
  exact false_of_hasBQUneven hLn hLs hnab hT hMt hMax (hP ↥L hPL)

private theorem inf_normalizer_eq_map_borel {Q : Type} [Group Q]
    {L T M : Subgroup Q} {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    {π : K →* ↥L} {e : ℕ} (hU : Chev2Orbit.UMaxBQ L T M D nn H π e) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) =
      ((CFSG.LieType.Steinberg.borel D H).map π).map L.subtype := by
  have hsub : (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).subgroupOf L =
      (Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).subgroupOf L := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have h1 : (L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).subgroupOf L =
      (CFSG.LieType.Steinberg.borel D H).map π := by
    rw [hsub, Subgroup.subgroupOf_normalizer_eq (H := T ⊓ L) (N := L) inf_le_right,
      hU.unip, hU.bq.normalizer_map_posUnipotent]
  calc L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) =
        ((L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).subgroupOf L).map
          L.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (H := L ⊓ Subgroup.normalizer
          ((T ⊓ L : Subgroup Q) : Set Q)) inf_le_left).symm
    _ = ((CFSG.LieType.Steinberg.borel D H).map π).map L.subtype := by rw [h1]

private theorem asc80ThmBCase_of_noUMax_lie {t : StatedLieTag} {n f : ℕ}
    (h : Asc80NoUMax fun X _ => CFSG.Models.LieModel X t n 2 f) :
    Asc80ThmBCase fun X _ => CFSG.Models.LieModel X t n 2 f :=
  asc80ThmBCase_of_noUMax
    (fun X Y _ _ ⟨e⟩ hX => CFSG.Models.LieModel.of_mulEquiv e hX) h

theorem exists_mem_actsOnDynkinMod_of_sup {Q : Type} [Group Q] {L A : Subgroup Q}
    (hLn : L.Normal) (hQ : L ⊔ A = ⊤) {t : Q} (ht : ActsOnDynkinMod ⊥ L t) :
    ∃ a ∈ A, ActsOnDynkinMod ⊥ L a := by
  classical
  obtain ⟨-, P, hPmax, hPne⟩ := ht
  have hnorm : ∀ a : Q, a ∈ Subgroup.normalizer (L : Set Q) := fun a => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top a
  by_contra hcon
  push Not at hcon
  have hbad : ∀ a ∈ A, ∃ l ∈ L, conjSubgroup P (a⁻¹ * l) = P := by
    intro a ha
    by_contra h
    push Not at h
    exact hcon a ha ⟨hnorm a, P, hPmax, h⟩
  have hAle : A ≤ L ⊔ Subgroup.normalizer (P : Set Q) := by
    intro a ha
    obtain ⟨l, hl, hconj⟩ := hbad a ha
    have hmem : a⁻¹ * l ∈ Subgroup.normalizer (P : Set Q) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconj
    have hmem' : (a⁻¹ * l)⁻¹ ∈ Subgroup.normalizer (P : Set Q) :=
      (Subgroup.normalizer (P : Set Q)).inv_mem hmem
    have haeq : a = l * (a⁻¹ * l)⁻¹ := by group
    rw [haeq]
    exact Subgroup.mul_mem_sup hl hmem'
  have htopN : L ⊔ Subgroup.normalizer (P : Set Q) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hQ]
    exact sup_le le_sup_left hAle
  have htN : t ∈ L ⊔ Subgroup.normalizer (P : Set Q) := by
    rw [htopN]
    exact Subgroup.mem_top t
  haveI : L.Normal := hLn
  obtain ⟨l', hl', n, hn, hlt⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := L)
      (t := Subgroup.normalizer (P : Set Q)) (x := t)).mp htN
  have htinv : t⁻¹ * l' = n⁻¹ := by
    rw [← hlt]
    group
  have hconj : conjSubgroup P (t⁻¹ * l') = P := by
    rw [htinv]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (P : Set Q)).inv_mem hn)
  exact hPne l' hl' hconj

private theorem false_of_graph_case {G : Type} [Group G] [Finite G] {H A M : Subgroup G}
    (hs : IsSimpleGroup ↥(Fstar H))
    (hnab : ∃ a b : ↥(Fstar H), a * b ≠ b * a)
    (hAH : A ≤ H) (hA : IsElemAbelian 2 A) (hM : maxOver H A = {M})
    {P : ∀ (X : Type) [Group X], Prop}
    (hPL : P ↥((Fstar H).subgroupOf H))
    (hrank : Chev2Orbit.HasBQRank ↥((Fstar H).subgroupOf H) 2)
    (hesc : Asc80BGraphEscape P) : False := by
  classical
  have hsetup := asc80BSetup hs hnab hAH hA hM
  have hMmax : IsMaxSubgroupIn H M := (isUniqueMaxOver_iff.mp hM).1
  obtain ⟨T, hT, hAT⟩ := exists_isSylowIn_ge 2 hAH hA.isPGroup
  let L : Subgroup ↥H := (Fstar H).subgroupOf H
  let T' : Subgroup ↥H := T.subgroupOf H
  let A' : Subgroup ↥H := A.subgroupOf H
  let M' : Subgroup ↥H := M.subgroupOf H
  let eL : ↥L ≃* ↥(Fstar H) := Subgroup.subgroupOfEquivOfLe (fstar_le_group H)
  have hLnorm : L.Normal := by simpa [L] using normal_subgroupOf_fstar H
  have hLsimple : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eL.symm a, eL.symm b, ?_⟩
    intro hcomm
    apply hab
    simpa using congrArg eL hcomm
  have hCentL : Subgroup.centralizer (L : Set ↥H) = ⊥ := by
    have heq : Subgroup.centralizer (L : Set ↥H) =
        (H ⊓ Subgroup.centralizer (Fstar H : Set G)).subgroupOf H := by
      ext x
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        refine ⟨x.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        let fH : ↥H := ⟨f, fstar_le_group H hf⟩
        have hfL : fH ∈ L := by
          change (fH : G) ∈ Fstar H
          exact hf
        have hcomm := hx fH hfL
        exact congrArg (fun t : ↥H => (t : G)) hcomm
      · intro hx y hy
        have hxcent : (x : G) ∈ Subgroup.centralizer (Fstar H : Set G) :=
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
        apply Subtype.ext
        have hyF : (y : G) ∈ Fstar H := by
          change y ∈ (Fstar H).subgroupOf H at hy
          exact Subgroup.mem_subgroupOf.mp hy
        exact (Subgroup.mem_centralizer_iff.mp hxcent) (y : G) hyF
    rw [heq, hsetup.inf_centralizer]
    simp
  have hT'syl : IsSylowIn 2 T' ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le).symm
    · rw [Subgroup.relIndex_top_right]
      simpa [Subgroup.relIndex] using hT.not_dvd_relIndex
  have hMlt : M' < ⊤ := by
    have h := (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := M') (K := ⊤)).mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hMmax.le, Subgroup.map_top,
        Subgroup.range_subtype]
      exact hMmax.1)
    exact h
  have hMaxT' : ∀ X : Subgroup ↥H, T' ≤ X → X < ⊤ → X ≤ M' := by
    intro X hTX hXlt
    let X' : Subgroup G := X.map H.subtype
    have hTX' : T ≤ X' := by
      calc T = (T.subgroupOf H).map H.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hT.le).symm
        _ ≤ X.map H.subtype := Subgroup.map_mono hTX
    have hX'lt : X' < H := by
      have h := (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := X) (K := ⊤)).mpr hXlt
      simpa only [X', Subgroup.map_top, Subgroup.range_subtype] using h
    have hX'M : X' ≤ M := hsetup.le_of_lt X' (hAT.trans hTX') hX'lt
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hX'M (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hMaxA' : ∀ X : Subgroup ↥H, A' ≤ X → X < ⊤ → X ≤ M' := by
    intro X hAX hXlt
    let X' : Subgroup G := X.map H.subtype
    have hA_X' : A ≤ X' := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hAH hx⟩,
        hAX (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hX'lt : X' < H := by
      have h := (Subgroup.map_subtype_lt_map_subtype (G' := H) (H := X) (K := ⊤)).mpr hXlt
      simpa only [X', Subgroup.map_top, Subgroup.range_subtype] using h
    have hX'M : X' ≤ M := hsetup.le_of_lt X' hA_X' hX'lt
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hX'M (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hA'ea : IsElemAbelian 2 A' := hA.subgroupOf H
  have hA'T' : A' ≤ T' := Subgroup.subgroupOf_mono H hAT
  have hLAsup : L ⊔ A' = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := Fstar H) (A' := A) (B := H)
      (fstar_le_group H) hAH
    rw [← hsetup.eq_sup, Subgroup.subgroupOf_self] at h
    exact h.symm
  have hPL' : P ↥L := hPL
  have hrankL : Chev2Orbit.HasBQRank ↥L 2 := hrank
  obtain ⟨K, hK, hKfin, D, nn, H₀, π, e, hrankD, hU⟩ :=
    exists_umaxBQ_of_hasBQRank hLnorm hLsimple hLnab hT'syl hMlt hMaxT' hrankL
  have hr : D.rank = 2 := hrankD
  obtain ⟨t, ht, Ppar, hPLt, hPmax, hPN, hPne⟩ := hU.exists_swap hr
  have hactt : ActsOnDynkinMod ⊥ L t :=
    Chev2Orbit.actsOnDynkinMod_bot_of_swap hLnorm hT'syl ht hPLt hPmax hPN hPne
  obtain ⟨a, ha, hact⟩ := exists_mem_actsOnDynkinMod_of_sup hLnorm hLAsup hactt
  have hLT' : L ⊔ T' = ⊤ := top_le_iff.mp (hLAsup ▸ sup_le_sup_left hA'T' L)
  have hesc' :=
    hesc ↥H L A' T' hLnorm hLsimple hLnab hPL' hCentL hT'syl hLT' hA'T' hA'ea a ha hact
  have hA'cent : A' ≤ Subgroup.centralizer ({a} : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun z : ↥A' => (z : ↥H))
      (hA'ea.1.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩)
  have hCentLt : Subgroup.centralizer ({a} : Set ↥H) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨P₀, hP₀max, hP₀ne⟩ := hact.2
    have hcentral : ∀ x : ↥H, x * a = a * x := by
      intro x
      have hx : x ∈ Subgroup.centralizer ({a} : Set ↥H) := by
        rw [htop]
        exact Subgroup.mem_top x
      exact Subgroup.mem_centralizer_singleton_iff.mp hx
    have hconj : ∀ x : ↥H, a * x * a⁻¹ = x := by
      intro x
      have h := hcentral x
      calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [← h]
        _ = x := by simp
    have hmapP : P₀.map (MulAut.conj a).toMonoidHom = P₀ := by
      refine le_antisymm ?_ ?_
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        simpa [MulAut.conj_apply, hconj x] using hx
      · intro y hy
        exact Subgroup.mem_map.mpr ⟨y, hy, by simpa [MulAut.conj_apply] using hconj y⟩
    have hconj1 : conjSubgroup P₀ (a⁻¹ * 1) = P₀ := by
      unfold conjSubgroup
      simpa using hmapP
    exact hP₀ne 1 L.one_mem hconj1
  have hCentM : Subgroup.centralizer ({a} : Set ↥H) ≤ M' :=
    hMaxA' _ hA'cent hCentLt
  have hle_inf : L ⊓ Subgroup.centralizer ({a} : Set ↥H) ≤ M' ⊓ L :=
    le_inf (le_trans inf_le_right hCentM) inf_le_left
  have hle_borel : M' ⊓ L ≤ ((CFSG.LieType.Steinberg.borel D H₀).map π).map L.subtype := hU.inf_le_borel
  have hEq := inf_normalizer_eq_map_borel hU
  have hle_norm : L ⊓ Subgroup.centralizer ({a} : Set ↥H) ≤
      Subgroup.normalizer ((T' ⊓ L : Subgroup ↥H) : Set ↥H) := by
    refine hle_inf.trans (hle_borel.trans ?_)
    rw [← hEq]
    exact inf_le_right
  exact hesc' hle_norm

theorem asc80ThmBCase_evenLieType_of_cases
    (hL2 : Asc80ThmBCase fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSL 2 2 f)
    (hSz : Asc80ThmBCase fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .twistedB2 n 2 f)
    (hL3 : Asc80BGraphEscape fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSL 3 2 f)
    (hSp4 : Asc80BGraphEscape fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSp 2 2 f)
    (hU3 : Asc80ThmBCase fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .PSU 3 2 f)
    (hD4 : Asc80ThmBCase fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .trialityD4 n 2 f)
    (hF4 : Asc80ThmBCase fun X _ => ∃ n f : ℕ, CFSG.Models.LieModel X .twistedF4 n 2 f) :
    Asc80ThmBCase fun X _ => CFSG.Models.EvenLieType X := by
  intro G _ _ H A M hs hnab hP hAH hA hM
  obtain ⟨t, n, f, hm⟩ := hP
  cases t with
  | PSL =>
      have h2 : 2 ≤ n := hm.1.2.2.1
      by_cases hn2 : n = 2
      · subst n
        exact hL2 H A M hs hnab ⟨f, hm⟩ hAH hA hM
      · by_cases hn3 : n = 3
        · subst n
          let eL : ↥((Fstar H).subgroupOf H) ≃* ↥(Fstar H) :=
            Subgroup.subgroupOfEquivOfLe (fstar_le_group H)
          have hmL : CFSG.Models.LieModel ↥((Fstar H).subgroupOf H) .PSL 3 2 f :=
            CFSG.Models.LieModel.of_mulEquiv eL.symm hm
          have hPL : ∃ f : ℕ, CFSG.Models.LieModel ↥((Fstar H).subgroupOf H) .PSL 3 2 f :=
            ⟨f, hmL⟩
          have hrank : Chev2Orbit.HasBQRank ↥((Fstar H).subgroupOf H) 2 := by
            simpa using Chev2Orbit.hasBQRank_psl hmL
          exact (false_of_graph_case hs hnab hAH hA hM hPL hrank hL3).elim
        · have hn4 : 4 ≤ n := by omega
          exact (asc80ThmBCase_of_noUMax_lie (t := .PSL) (n := n) (f := f)
            (h := asc80NoUMax_of_hasBQRank (r := n - 1)
              (fun X _ hX => Chev2Orbit.hasBQRank_psl hX) (by omega)))
            H A M hs hnab hm hAH hA hM
  | PSU =>
      have h3 : 3 ≤ n := hm.1.2.2.1
      by_cases hn3 : n = 3
      · subst n
        exact hU3 H A M hs hnab ⟨f, hm⟩ hAH hA hM
      · by_cases h45 : n = 4 ∨ n = 5
        · exact (asc80ThmBCase_of_noUMax_lie (t := .PSU) (n := n) (f := f)
            (h := asc80NoUMax_of_hasBQUneven
              (fun X _ hX => Chev2Orbit.hasBQUneven_psu h45 hX)))
            H A M hs hnab hm hAH hA hM
        · have hn4 : n ≠ 4 := fun h => h45 (Or.inl h)
          have hn5 : n ≠ 5 := fun h => h45 (Or.inr h)
          have hn6 : 6 ≤ n := by omega
          exact (asc80ThmBCase_of_noUMax_lie (t := .PSU) (n := n) (f := f)
            (h := asc80NoUMax_of_hasBQRank (r := n / 2)
              (fun X _ hX => Chev2Orbit.hasBQRank_psu hX) (by omega)))
            H A M hs hnab hm hAH hA hM
  | PSp =>
      have h2 : 2 ≤ n := hm.1.2.2.1
      by_cases hn2 : n = 2
      · subst n
        let eL : ↥((Fstar H).subgroupOf H) ≃* ↥(Fstar H) :=
          Subgroup.subgroupOfEquivOfLe (fstar_le_group H)
        have hmL : CFSG.Models.LieModel ↥((Fstar H).subgroupOf H) .PSp 2 2 f :=
          CFSG.Models.LieModel.of_mulEquiv eL.symm hm
        have hPL : ∃ f : ℕ, CFSG.Models.LieModel ↥((Fstar H).subgroupOf H) .PSp 2 2 f :=
          ⟨f, hmL⟩
        have hrank : Chev2Orbit.HasBQRank ↥((Fstar H).subgroupOf H) 2 :=
          Chev2Orbit.hasBQRank_psp hmL
        exact (false_of_graph_case hs hnab hAH hA hM hPL hrank hSp4).elim
      · have hn3 : 3 ≤ n := by omega
        exact (asc80ThmBCase_of_noUMax_lie (t := .PSp) (n := n) (f := f)
          (h := asc80NoUMax_of_hasBQRank (r := n)
            (fun X _ hX => Chev2Orbit.hasBQRank_psp hX) (by omega)))
          H A M hs hnab hm hAH hA hM
  | POmegaOdd => exact absurd rfl hm.1.2.2.2
  | POmegaPlus =>
      have hn4 : 4 ≤ n := hm.1.2.2
      exact (asc80ThmBCase_of_noUMax_lie (t := .POmegaPlus) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := n)
          (fun X _ hX => Chev2Orbit.hasBQRank_pomegaPlus hX) (by omega)))
        H A M hs hnab hm hAH hA hM
  | POmegaMinus =>
      have hn4 : 4 ≤ n := hm.1.2.2
      exact (asc80ThmBCase_of_noUMax_lie (t := .POmegaMinus) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := n - 1)
          (fun X _ hX => Chev2Orbit.hasBQRank_pomegaMinus hX) (by omega)))
        H A M hs hnab hm hAH hA hM
  | G2 =>
      have hn0 : n = 0 := hm.1.2.2.1
      subst n
      refine (asc80ThmBCase_of_noUMax_lie (t := .G2) (n := 0) (f := f) (h := ?_))
        H A M hs hnab hm hAH hA hM
      intro Q _ _ L T hLn hLs hnabQ hC hPL hT hMEx
      obtain ⟨M, hMt, hMax⟩ := hMEx
      obtain ⟨K, hK, hKfin, D, nn, H₀, π, e, hrank, hU⟩ :=
        exists_umaxBQ_of_hasBQRank hLn hLs hnabQ hT hMt hMax
          (Chev2Orbit.hasBQRank_g2 hPL)
      have hr : D.rank = 2 := hrank
      obtain ⟨t, ht, P, hPLt, hPmax, hPN, hPne⟩ := hU.exists_swap hr
      exact Chev2Orbit.false_of_swap_g2 hLn hPL hT ht hPLt hPmax hPN hPne
  | F4 =>
      exact (asc80ThmBCase_of_noUMax_lie (t := .F4) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := 4)
          (fun X _ hX => Chev2Orbit.hasBQRank_f4 hX) (by norm_num)))
        H A M hs hnab hm hAH hA hM
  | E6 =>
      exact (asc80ThmBCase_of_noUMax_lie (t := .E6) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := 6)
          (fun X _ hX => Chev2Orbit.hasBQRank_e6 hX) (by norm_num)))
        H A M hs hnab hm hAH hA hM
  | E7 =>
      exact (asc80ThmBCase_of_noUMax_lie (t := .E7) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := 7)
          (fun X _ hX => Chev2Orbit.hasBQRank_e7 hX) (by norm_num)))
        H A M hs hnab hm hAH hA hM
  | E8 =>
      exact (asc80ThmBCase_of_noUMax_lie (t := .E8) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := 8)
          (fun X _ hX => Chev2Orbit.hasBQRank_e8 hX) (by norm_num)))
        H A M hs hnab hm hAH hA hM
  | twistedE6 =>
      exact (asc80ThmBCase_of_noUMax_lie (t := .twistedE6) (n := n) (f := f)
        (h := asc80NoUMax_of_hasBQRank (r := 4)
          (fun X _ hX => Chev2Orbit.hasBQRank_twistedE6 hX) (by norm_num)))
        H A M hs hnab hm hAH hA hM
  | trialityD4 =>
      exact hD4 H A M hs hnab ⟨n, f, hm⟩ hAH hA hM
  | twistedB2 =>
      exact hSz H A M hs hnab ⟨n, f, hm⟩ hAH hA hM
  | twistedG2 =>
      exact absurd hm.1.2.2.2.1 (by norm_num)
  | twistedF4 =>
      exact hF4 H A M hs hnab ⟨n, f, hm⟩ hAH hA hM
  | Tits =>
      refine (asc80ThmBCase_of_noUMax_lie (t := .Tits) (n := n) (f := f) (h := ?_))
        H A M hs hnab hm hAH hA hM
      intro Q _ _ L T hLn hLs hnabQ hC hPL hT hMEx
      obtain ⟨M, hMt, hMax⟩ := hMEx
      exact Chev2Orbit.false_of_uniqueMax_tits hLn hLs hnabQ hPL hT hMt hMax

end CFSG.LocalAnalysis.WeakClosure81

end
