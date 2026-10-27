module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Defs
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.PCoreOfBasic
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

omit [Finite X] [Finite Y] in
private theorem normal_subgroupOf_map {φ : X →* Y} {N L : Subgroup X} (hNL : N ≤ L)
    (hN : (N.subgroupOf L).Normal) :
    ((N.map φ).subgroupOf (L.map φ)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hNL)).mpr ?_
  exact (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hN)).trans
    (Subgroup.le_normalizer_map φ)

omit [Finite X] [Finite Y] in
private theorem normal_subgroupOf_comap {φ : X →* Y} (hφ : Function.Injective φ)
    {N : Subgroup Y} {L : Subgroup X} (hNL : N ≤ L.map φ)
    (hN : (N.subgroupOf (L.map φ)).Normal) :
    ((N.comap φ).subgroupOf L).Normal := by
  have hle : N.comap φ ≤ L := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (hNL hx)
    rwa [← hφ hlx]
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_
  refine le_trans (Subgroup.le_comap_map (f := φ) L) ?_
  refine le_trans (Subgroup.comap_mono
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hN)) ?_
  exact Subgroup.le_normalizer_comap (H := N) φ

private theorem pCoreOf_comap {φ : X →* Y} (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) (H : Subgroup Y) :
    pCoreOf 2 (H.comap φ) = (pCoreOf 2 H).comap φ := by
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.map_le_iff_le_comap]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · have h1 : (pCoreOf 2 (H.comap φ)).map φ ≤ (H.comap φ).map φ :=
        Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 (H.comap φ))
      rwa [Subgroup.map_comap_eq_self_of_surjective hφ H] at h1
    · have h2 : (H.comap φ).map φ ≤
          Subgroup.normalizer ((pCoreOf 2 (H.comap φ)).map φ : Set Y) :=
        (Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H.comap φ))).trans
          (Subgroup.le_normalizer_map φ)
      rwa [Subgroup.map_comap_eq_self_of_surjective hφ H] at h2
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H.comap φ)).map φ
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact Subgroup.comap_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    · rw [← Subgroup.comap_normalizer_eq_of_surjective (pCoreOf 2 H) hφ]
      exact Subgroup.comap_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_of_ker_isPGroup φ hker

omit [Finite Y] in
private theorem opp_comap_map {φ : X →* Y} (hφ : Function.Surjective φ) (H : Subgroup Y) :
    (Opp 2 (H.comap φ)).map φ = Opp 2 H := by
  simp only [Opp]
  rw [s13_pElementSubgroup_map Nat.prime_two, Subgroup.map_comap_eq_self_of_surjective hφ]

omit [Finite Y] in
private theorem opp_map_eq {φ : X →* Y} (H : Subgroup X) :
    Opp 2 (H.map φ) = (Opp 2 H).map φ := by
  simp only [Opp]
  exact (s13_pElementSubgroup_map Nat.prime_two φ H).symm

omit [Finite Y] in
private theorem oUpperTwo_map_eq {φ : X →* Y} (H : Subgroup X) :
    (S17.oUpperTwo H).map φ = S17.oUpperTwo (H.map φ) :=
  CFSG.AGLEmbedding.SUPair.map_oUpperTwo φ H

omit [Finite X] [Finite Y] in
private theorem nonempty_bar2_map_eq {φ : X →* Y} (hker : IsPGroup 2 φ.ker)
    {A : Subgroup X} {B : Subgroup Y} (hAB : A.map φ = B) :
    Nonempty (Bar2 A ≃* Bar2 B) := by
  let ψ : ↥A →* ↥B :=
    (φ.comp A.subtype).codRestrict B fun x => by
      rw [← hAB]
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    intro y
    have hy : (y : Y) ∈ A.map φ := by rw [hAB]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hψker : IsPGroup 2 ψ.ker := by
    have hle : ψ.ker ≤ (φ.ker).subgroupOf A := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hx' : (ψ x : Y) = 1 := by rw [MonoidHom.mem_ker.mp hx]; rfl
      exact hx'
    exact (hker.comap_of_injective A.subtype A.subtype_injective).to_le hle
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker ψ hψ hψker

omit [Finite X] [Finite Y] in
private theorem nonempty_bar2_comap {φ : X →* Y} (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) (H : Subgroup Y) :
    Nonempty (Bar2 (H.comap φ) ≃* Bar2 H) :=
  nonempty_bar2_map_eq hker (Subgroup.map_comap_eq_self_of_surjective hφ H)

omit [Finite X] [Finite Y] in
private theorem nonempty_bar2_map {φ : X →* Y} (hφ : Function.Injective φ) (H : Subgroup X) :
    Nonempty (Bar2 (H.map φ) ≃* Bar2 H) := by
  let e : ↥H ≃* ↥(H.map φ) := H.equivMapOfInjective φ hφ
  have hker : IsPGroup 2 e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    exact IsPGroup.of_bot
  obtain ⟨e'⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
    e.toMonoidHom e.surjective hker
  exact ⟨e'.symm⟩

omit [Finite X] [Finite Y] in
private theorem comap_normal_subgroupOf {φ : X →* Y} (hφ : Function.Surjective φ)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (hL : IsLeviFamily P d L) (i : Fin d) :
    (((L i).comap φ).subgroupOf (P.comap φ)).Normal := by
  have hP : P ≤ Subgroup.normalizer (L i : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.le i)).mp (hL.normal i)
  have hPn : P.comap φ ≤ Subgroup.normalizer ((L i).comap φ : Set X) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective (L i) hφ]
    exact Subgroup.comap_mono hP
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.comap_mono (hL.le i))).mpr hPn

omit [Finite Y] in
private theorem comap_eq_opp_sup {φ : X →* Y} (hφ : Function.Surjective φ)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (hL : IsLeviFamily P d L)
    (hO : pCoreOf 2 (P.comap φ) = (pCoreOf 2 P).comap φ) (i : Fin d) :
    (L i).comap φ = Opp 2 ((L i).comap φ) ⊔ pCoreOf 2 (P.comap φ) := by
  rw [hO]
  let R : Subgroup X := Opp 2 ((L i).comap φ) ⊔ (pCoreOf 2 P).comap φ
  have hRmap : R.map φ = L i := by
    rw [Subgroup.map_sup, opp_comap_map hφ (L i),
      Subgroup.map_comap_eq_self_of_surjective hφ (pCoreOf 2 P)]
    exact (hL.eq_opp_sup i).symm
  have hR : R = (L i).comap φ := by
    calc
      R = (R.map φ).comap φ :=
        (Subgroup.comap_map_eq_self
          ((MonoidHom.ker_le_comap φ (pCoreOf 2 P)).trans le_sup_right)).symm
      _ = (L i).comap φ := by rw [hRmap]
  exact hR.symm

omit [Finite X] [Finite Y] in
private theorem comap_commutator_le {φ : X →* Y} (hφ : Function.Surjective φ)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (hL : IsLeviFamily P d L)
    (hO : pCoreOf 2 (P.comap φ) = (pCoreOf 2 P).comap φ) {i j : Fin d} (hij : i ≠ j) :
    ⁅(L i).comap φ, (L j).comap φ⁆ ≤ pCoreOf 2 (P.comap φ) := by
  rw [hO]
  have hmapc : (⁅(L i).comap φ, (L j).comap φ⁆).map φ = ⁅L i, L j⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφ,
      Subgroup.map_comap_eq_self_of_surjective hφ]
  calc
    ⁅(L i).comap φ, (L j).comap φ⁆ ≤ (⁅L i, L j⁆).comap φ := by
      rw [← Subgroup.map_le_iff_le_comap, hmapc]
    _ ≤ (pCoreOf 2 P).comap φ := Subgroup.comap_mono (hL.commutator_le i j hij)

omit [Finite Y] in
private theorem comap_iSup_eq {φ : X →* Y} (hφ : Function.Surjective φ)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (hd : d ≠ 0)
    (hL : IsLeviFamily P d L)
    (hO : pCoreOf 2 (P.comap φ) = (pCoreOf 2 P).comap φ) :
    (⨆ i, (L i).comap φ) = Opp 2 (P.comap φ) ⊔ pCoreOf 2 (P.comap φ) := by
  rw [hO]
  let R : Subgroup X := ⨆ i, (L i).comap φ
  let S : Subgroup X := Opp 2 (P.comap φ) ⊔ (pCoreOf 2 P).comap φ
  have hkerO : φ.ker ≤ (pCoreOf 2 P).comap φ := MonoidHom.ker_le_comap φ (pCoreOf 2 P)
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  have hkerR : φ.ker ≤ R :=
    (hkerO.trans (Subgroup.comap_mono (hL.pCoreOf_le ⟨0, hd0⟩))).trans
      (le_iSup (fun i => (L i).comap φ) ⟨0, hd0⟩)
  have hkerS : φ.ker ≤ S := hkerO.trans le_sup_right
  have hRmap : R.map φ = Opp 2 P ⊔ pCoreOf 2 P := by
    rw [Subgroup.map_iSup]
    simp_rw [Subgroup.map_comap_eq_self_of_surjective hφ]
    rw [hL.iSup_eq]
  have hSmap : S.map φ = Opp 2 P ⊔ pCoreOf 2 P := by
    rw [Subgroup.map_sup, opp_comap_map hφ P,
      Subgroup.map_comap_eq_self_of_surjective hφ (pCoreOf 2 P)]
  have hR : R = (Opp 2 P ⊔ pCoreOf 2 P).comap φ := by
    calc
      R = (R.map φ).comap φ := (Subgroup.comap_map_eq_self hkerR).symm
      _ = (Opp 2 P ⊔ pCoreOf 2 P).comap φ := by rw [hRmap]
  have hS : S = (Opp 2 P ⊔ pCoreOf 2 P).comap φ := by
    calc
      S = (S.map φ).comap φ := (Subgroup.comap_map_eq_self hkerS).symm
      _ = (Opp 2 P ⊔ pCoreOf 2 P).comap φ := by rw [hSmap]
  exact hR.trans hS.symm

omit [Finite Y] in
private theorem comap_tits {φ : X →* Y} (hφ : Function.Surjective φ)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (hL : IsLeviFamily P d L)
    (hO : pCoreOf 2 (P.comap φ) = (pCoreOf 2 P).comap φ) (i : Fin d) (N : Subgroup X)
    (hON : pCoreOf 2 (P.comap φ) ≤ N) (hNle : N ≤ (L i).comap φ)
    (hNnormal : (N.subgroupOf ((L i).comap φ)).Normal)
    (hcomm : ¬ ⁅N, (L i).comap φ⁆ ≤ pCoreOf 2 (P.comap φ)) :
    S17.oUpperTwo ((L i).comap φ) ≤ N := by
  have hkerO : φ.ker ≤ (pCoreOf 2 P).comap φ := MonoidHom.ker_le_comap φ (pCoreOf 2 P)
  have hNker : φ.ker ≤ N := hkerO.trans (hO ▸ hON)
  have hONmap : pCoreOf 2 P ≤ N.map φ := by
    have h1 : (pCoreOf 2 (P.comap φ)).map φ ≤ N.map φ := Subgroup.map_mono hON
    rwa [hO, Subgroup.map_comap_eq_self_of_surjective hφ] at h1
  have hNmaple : N.map φ ≤ L i := by
    have h1 : N.map φ ≤ ((L i).comap φ).map φ := Subgroup.map_mono hNle
    rwa [Subgroup.map_comap_eq_self_of_surjective hφ] at h1
  have hNmapnormal : ((N.map φ).subgroupOf (L i)).Normal := by
    have h1 := normal_subgroupOf_map (φ := φ) hNle hNnormal
    rwa [Subgroup.map_comap_eq_self_of_surjective hφ] at h1
  have hNmapcomm : ¬ ⁅N.map φ, L i⁆ ≤ pCoreOf 2 P := by
    intro hc
    have hmapc : (⁅N, (L i).comap φ⁆).map φ = ⁅N.map φ, L i⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφ]
    refine hcomm ?_
    rw [hO, ← Subgroup.map_le_iff_le_comap, hmapc]
    exact hc
  have hupper : S17.oUpperTwo (L i) ≤ N.map φ :=
    hL.tits i (N.map φ) hONmap hNmaple hNmapnormal hNmapcomm
  calc
    S17.oUpperTwo ((L i).comap φ) ≤ (N.map φ).comap φ := by
      rw [← Subgroup.map_le_iff_le_comap, oUpperTwo_map_eq,
        Subgroup.map_comap_eq_self_of_surjective hφ]
      exact hupper
    _ = N := Subgroup.comap_map_eq_self hNker

theorem IsLeviFamily.comap {φ : X →* Y} (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (hd : d ≠ 0) (hL : IsLeviFamily P d L) :
    IsLeviFamily (P.comap φ) d (fun i => (L i).comap φ) := by
  have hO : pCoreOf 2 (P.comap φ) = (pCoreOf 2 P).comap φ := pCoreOf_comap hφ hker P
  refine
    { pCoreOf_le := fun i => hO.trans_le (Subgroup.comap_mono (hL.pCoreOf_le i))
      le := fun i => Subgroup.comap_mono (hL.le i)
      normal := fun i => comap_normal_subgroupOf hφ hL i
      eq_opp_sup := fun i => comap_eq_opp_sup hφ hL hO i
      ne := ?_
      commutator_le := fun i j hij => comap_commutator_le hφ hL hO hij
      iSup_eq := comap_iSup_eq hφ hd hL hO
      tits := fun i N hON hNle hNnormal hcomm =>
        comap_tits hφ hL hO i N hON hNle hNnormal hcomm }
  · intro i
    rw [hO]
    exact fun h => hL.ne i (Subgroup.comap_injective hφ h)

theorem LeviAlt.comap {φ : X →* Y} (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y} (h : LeviAlt P d L) :
    LeviAlt (P.comap φ) d (fun i => (L i).comap φ) := by
  have hO : pCoreOf 2 (P.comap φ) = (pCoreOf 2 P).comap φ :=
    pCoreOf_comap hφ hker P
  unfold LeviAlt at h ⊢
  rcases h with ⟨hd2, hq⟩ | hno
  · left
    refine ⟨hd2, fun i => ?_⟩
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (nonempty_bar2_comap hφ hker (L i)).some (hq i)
  · right
    intro i N n hON hNle hNnormal hn hL2
    have hkerO : φ.ker ≤ (pCoreOf 2 P).comap φ :=
      MonoidHom.ker_le_comap φ (pCoreOf 2 P)
    have hNker : φ.ker ≤ N := hkerO.trans (hO ▸ hON)
    have hONmap : pCoreOf 2 P ≤ N.map φ := by
      have h1 : (pCoreOf 2 (P.comap φ)).map φ ≤ N.map φ := Subgroup.map_mono hON
      rwa [hO, Subgroup.map_comap_eq_self_of_surjective hφ] at h1
    have hNmaple : N.map φ ≤ L i := by
      have h1 : N.map φ ≤ ((L i).comap φ).map φ := Subgroup.map_mono hNle
      rwa [Subgroup.map_comap_eq_self_of_surjective hφ] at h1
    have hNmapnormal : ((N.map φ).subgroupOf (L i)).Normal := by
      have h1 := normal_subgroupOf_map (φ := φ) hNle hNnormal
      rwa [Subgroup.map_comap_eq_self_of_surjective hφ] at h1
    have hNcomap : (N.map φ).comap φ = N := Subgroup.comap_map_eq_self hNker
    obtain ⟨e⟩ := nonempty_bar2_comap hφ hker (N.map φ)
    rw [hNcomap] at e
    exact hno i (N.map φ) n hONmap hNmaple hNmapnormal hn
      (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)

omit [Finite Y] in
theorem IsLeviFamily.map {φ : X →* Y} (hφ : Function.Injective φ) {P : Subgroup X} {d : ℕ}
    {L : Fin d → Subgroup X} (hL : IsLeviFamily P d L) :
    IsLeviFamily (P.map φ) d (fun i => (L i).map φ) := by
  have hPcore : pCoreOf 2 (P.map φ) = (pCoreOf 2 P).map φ :=
    CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 φ hφ P
  refine
    { pCoreOf_le := fun i => hPcore.trans_le (Subgroup.map_mono (hL.pCoreOf_le i))
      le := fun i => Subgroup.map_mono (hL.le i)
      normal := fun i => normal_subgroupOf_map (φ := φ) (hL.le i) (hL.normal i)
      eq_opp_sup := ?_
      ne := ?_
      commutator_le := ?_
      iSup_eq := ?_
      tits := ?_ }
  · intro i
    rw [opp_map_eq, hPcore, ← Subgroup.map_sup]
    exact congrArg (Subgroup.map φ) (hL.eq_opp_sup i)
  · intro i
    rw [hPcore]
    exact fun h => hL.ne i (Subgroup.map_injective hφ h)
  · intro i j hij
    rw [← Subgroup.map_commutator, hPcore]
    exact Subgroup.map_mono (hL.commutator_le i j hij)
  · rw [← Subgroup.map_iSup, hL.iSup_eq, Subgroup.map_sup, opp_map_eq, hPcore]
  · intro i N hON hNle hNnormal hcomm
    have hNle' : N ≤ (L i).map φ := hNle
    have hPcore_le : pCoreOf 2 P ≤ N.comap φ := by
      rw [← Subgroup.comap_map_eq_self_of_injective hφ (pCoreOf 2 P),
        ← hPcore]
      exact Subgroup.comap_mono hON
    have hNcomaple : N.comap φ ≤ L i := by
      rw [← Subgroup.comap_map_eq_self_of_injective hφ (L i)]
      exact Subgroup.comap_mono hNle
    have hNcomapnormal : ((N.comap φ).subgroupOf (L i)).Normal :=
      normal_subgroupOf_comap hφ hNle' hNnormal
    have hNcomapcomm : ¬ ⁅N.comap φ, L i⁆ ≤ pCoreOf 2 P := by
      intro hc
      apply hcomm
      have hNmap : (N.comap φ).map φ = N :=
        Subgroup.map_comap_eq_self (hNle.trans (Subgroup.map_le_range φ (L i)))
      rw [hPcore, ← hNmap, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hc
    have hupper : S17.oUpperTwo (L i) ≤ N.comap φ :=
      hL.tits i (N.comap φ) hPcore_le hNcomaple hNcomapnormal hNcomapcomm
    have hNrange : N ≤ φ.range := hNle.trans (Subgroup.map_le_range φ (L i))
    calc
      S17.oUpperTwo ((L i).map φ) = (S17.oUpperTwo (L i)).map φ :=
        (oUpperTwo_map_eq (L i)).symm
      _ ≤ (N.comap φ).map φ := Subgroup.map_mono hupper
      _ = N := Subgroup.map_comap_eq_self hNrange

omit [Finite X] [Finite Y] in
theorem LeviAlt.map {φ : X →* Y} (hφ : Function.Injective φ) {P : Subgroup X} {d : ℕ}
    {L : Fin d → Subgroup X} (h : LeviAlt P d L) :
    LeviAlt (P.map φ) d (fun i => (L i).map φ) := by
  have hPcore : pCoreOf 2 (P.map φ) = (pCoreOf 2 P).map φ :=
    CFSG.ASVolI.ChH.pCoreOf_map_of_injective 2 φ hφ P
  unfold LeviAlt at h ⊢
  rcases h with ⟨hd2, hq⟩ | hno
  · left
    refine ⟨hd2, fun i => ?_⟩
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (nonempty_bar2_map hφ (L i)).some (hq i)
  · right
    intro i N n hON hNle hNnormal hn hL2
    have hNcomapON : pCoreOf 2 P ≤ N.comap φ := by
      rw [← Subgroup.comap_map_eq_self_of_injective hφ (pCoreOf 2 P), ← hPcore]
      exact Subgroup.comap_mono hON
    have hNcomaple : N.comap φ ≤ L i := by
      rw [← Subgroup.comap_map_eq_self_of_injective hφ (L i)]
      exact Subgroup.comap_mono hNle
    have hNcomapnormal : ((N.comap φ).subgroupOf (L i)).Normal :=
      normal_subgroupOf_comap hφ hNle hNnormal
    have hno' := hno i (N.comap φ) n hNcomapON hNcomaple hNcomapnormal hn
    have hNmap : (N.comap φ).map φ = N :=
      Subgroup.map_comap_eq_self (hNle.trans (Subgroup.map_le_range φ (L i)))
    obtain ⟨e⟩ := nonempty_bar2_map hφ (N.comap φ)
    rw [← hNmap] at hL2
    exact hno' (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)

omit [Finite Y] in
theorem IsLeviFamily.ne_zero {P : Subgroup Y} {d : ℕ} {L : Fin d → Subgroup Y}
    (hL : IsLeviFamily P d L) (hP : S19.IsNontrivialParabolic Y P) : d ≠ 0 := by
  rintro rfl
  have hsup : (⨆ i : Fin 0, L i) = ⊥ := by simp
  have hbot : Opp 2 P ⊔ pCoreOf 2 P = ⊥ := by
    rw [← hL.iSup_eq, hsup]
  have hOpp : Opp 2 P = ⊥ := (sup_eq_bot_iff.mp hbot).1
  obtain ⟨-, -, S, hSlt⟩ := hP
  have hSbot : (S : Subgroup Y) = ⊥ := by
    have hSP : (S : Subgroup Y) ≤ P :=
      (Subgroup.le_normalizer : (S : Subgroup Y) ≤ normalizer (S : Set Y)).trans hSlt.le
    have hle : (S : Subgroup Y) ≤ Opp 2 P :=
      CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two S.isPGroup' hSP
    rwa [hOpp, le_bot_iff] at hle
  have htop : Subgroup.normalizer (S : Set Y) = ⊤ := by
    change Subgroup.normalizer ((S : Subgroup Y) : Set Y) = ⊤
    have h := congrArg (fun H : Subgroup Y => Subgroup.normalizer (H : Set Y)) hSbot
    rw [h]
    exact Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot
  rw [htop] at hSlt
  exact (lt_irrefl (⊤ : Subgroup Y)) (lt_of_lt_of_le hSlt le_top)

theorem isLeviFamily_inf_of_barOfInter {G : Type} [Group G] [Finite G] {M Dsub : Subgroup G}
    (hO : pCoreOf 2 Dsub ≤ M) {d : ℕ} {L : Fin d → Subgroup (Bar2 Dsub)} (hd : d ≠ 0)
    (hL : IsLeviFamily (S19.barOfInter M Dsub) d L) :
    IsLeviFamily (Dsub ⊓ M) d
      (fun i => ((L i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub))).map Dsub.subtype) := by
  let π : ↥Dsub →* Bar2 Dsub := QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hcomap : ((S19.barOfInter M Dsub).comap π).map Dsub.subtype = Dsub ⊓ M := by
    have hker_le : π.ker ≤ (Dsub ⊓ M).subgroupOf Dsub := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨x.2, hO (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)⟩
    have hpre : (S19.barOfInter M Dsub).comap π = (Dsub ⊓ M).subgroupOf Dsub := by
      rw [S19.barOfInter, Subgroup.comap_map_eq, sup_eq_left.mpr hker_le]
    rw [hpre, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have h := ((hL.comap (φ := π) hπ hπker hd)).map (φ := Dsub.subtype) Dsub.subtype_injective
  rwa [hcomap] at h

theorem leviAlt_inf_of_barOfInter {G : Type} [Group G] [Finite G] {M Dsub : Subgroup G}
    (hO : pCoreOf 2 Dsub ≤ M) {d : ℕ} {L : Fin d → Subgroup (Bar2 Dsub)}
    (h : LeviAlt (S19.barOfInter M Dsub) d L) :
    LeviAlt (Dsub ⊓ M) d
      (fun i => ((L i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub))).map Dsub.subtype) := by
  let π : ↥Dsub →* Bar2 Dsub := QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hcomap : ((S19.barOfInter M Dsub).comap π).map Dsub.subtype = Dsub ⊓ M := by
    have hker_le : π.ker ≤ (Dsub ⊓ M).subgroupOf Dsub := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨x.2, hO (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)⟩
    have hpre : (S19.barOfInter M Dsub).comap π = (Dsub ⊓ M).subgroupOf Dsub := by
      rw [S19.barOfInter, Subgroup.comap_map_eq, sup_eq_left.mpr hker_le]
    rw [hpre, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have h' := ((h.comap (φ := π) hπ hπker)).map (φ := Dsub.subtype) Dsub.subtype_injective
  rwa [hcomap] at h'

omit [Finite X] [Finite Y] in
private theorem LeviBlk.of_mulEquiv {two big : Prop} {d : ℕ} {L : Fin d → Subgroup Y}
    {L' : Fin d → Subgroup X}
    (h : ∀ i, Nonempty (Bar2 (S17.oUpperTwo (L' i)) ≃* Bar2 (S17.oUpperTwo (L i))))
    (hL : LeviBlk two big d L) : LeviBlk two big d L' := by
  refine ⟨fun i => ?_, hL.2⟩
  obtain ⟨e⟩ := h i
  obtain ⟨h3, hq | hz⟩ := hL.1 i
  · exact ⟨by rw [Nat.card_congr e.toEquiv]; exact h3,
      Or.inl (CFSG.Open.IsQuasisimple.of_mulEquiv e hq)⟩
  · obtain ⟨⟨ez⟩, htwo⟩ := hz
    exact ⟨by rw [Nat.card_congr e.toEquiv]; exact h3,
      Or.inr ⟨⟨e.trans ez⟩, htwo⟩⟩

omit [Finite Y] in
theorem LeviBlk.comap {two big : Prop} {φ : X →* Y} (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) {d : ℕ} {L : Fin d → Subgroup Y} (h : LeviBlk two big d L) :
    LeviBlk two big d (fun i => (L i).comap φ) :=
  LeviBlk.of_mulEquiv (L := L) (L' := fun i => (L i).comap φ) (fun i => by
    have hmap : (S17.oUpperTwo ((L i).comap φ)).map φ = S17.oUpperTwo (L i) := by
      rw [oUpperTwo_map_eq, Subgroup.map_comap_eq_self_of_surjective hφ]
    exact nonempty_bar2_map_eq hker hmap) h

omit [Finite Y] in
theorem LeviBlk.map {two big : Prop} {φ : X →* Y} (hφ : Function.Injective φ) {d : ℕ}
    {L : Fin d → Subgroup X} (h : LeviBlk two big d L) :
    LeviBlk two big d (fun i => (L i).map φ) :=
  LeviBlk.of_mulEquiv (L := L) (L' := fun i => (L i).map φ) (fun i => by
    rw [← oUpperTwo_map_eq (L i)]
    exact nonempty_bar2_map hφ (S17.oUpperTwo (L i))) h

theorem LeviBlk.comap_mk_map_subtype {two big : Prop} {G : Type} [Group G] [Finite G]
    {J : Subgroup G} {d : ℕ} {M : Fin d → Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (h : LeviBlk two big d M) :
    LeviBlk two big d
      (fun i => ((M i).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥J))).map J.subtype) :=
  (h.comap (φ := QuotientGroup.mk' (CFSG.pCore 2 ↥J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact CFSG.LieType.BorelTits.pCore_isPGroup 2)).map
    (φ := J.subtype) J.subtype_injective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
