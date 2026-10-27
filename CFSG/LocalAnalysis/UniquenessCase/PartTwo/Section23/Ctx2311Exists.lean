module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix
open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem map_mk'_eq_top_iff {X : Type} [Group X] {N H : Subgroup X} [N.Normal] :
    H.map (QuotientGroup.mk' N) = ⊤ ↔ H ⊔ N = ⊤ := by
  rw [show (⊤ : Subgroup (X ⧸ N)) = (⊤ : Subgroup X).map (QuotientGroup.mk' N) from
    (Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)).symm,
    Subgroup.map_eq_map_iff, QuotientGroup.ker_mk']
  simp

theorem map_comap_mk'_eq_of_pCoreOf_le {L Y : Subgroup G} (hYL : Y ≤ L)
    (hO : CFSG.Open.pCoreOf 2 L ≤ Y) :
    (((Y.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype = Y := by
  have hker : CFSG.pCore 2 ↥L ≤ Y.subgroupOf L := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hO (Subgroup.mem_map_of_mem L.subtype hx))
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hker,
    Subgroup.map_subgroupOf_eq_of_le hYL]

theorem exists_not_le_of_residualOvergroupsAt {S : Type} [Group S] [Finite S]
    {U Y : Subgroup S} {P : Fin 2 → Subgroup S} (h : ResidualOvergroupsAt S U P)
    (hUY : U ≤ Y) (hY : Y ≠ ⊤) : ∃ j, ¬ P j ≤ Y := by
  obtain ⟨hne, hUP, hmax, -, -, -⟩ := h
  have hPcoat (i : Fin 2) : IsCoatom (P i) :=
    covBy_top_iff.mp ((hmax (P i) (hUP i)).mpr ⟨i, rfl⟩)
  obtain ⟨Yc, hYc, hYle⟩ := (IsCoatomic.eq_top_or_exists_le_coatom Y).resolve_left hY
  have hYc' : Yc ⋖ ⊤ := covBy_top_iff.mpr hYc
  obtain ⟨k, hk⟩ := (hmax Yc (hUY.trans hYle)).mp hYc'
  have hYleP : Y ≤ P k := by
    rw [← hk]
    exact hYle
  by_cases h0 : P 0 ≤ Y
  · refine ⟨1, ?_⟩
    intro h1
    have hPk0 : P k = P 0 :=
      (hPcoat 0).le_iff_eq (hPcoat k).ne_top |>.mp (h0.trans hYleP)
    have hPk1 : P k = P 1 :=
      (hPcoat 1).le_iff_eq (hPcoat k).ne_top |>.mp (h1.trans hYleP)
    exact hne (hPk0.symm.trans hPk1)
  · exact ⟨0, h0⟩

private theorem pCoreOf_le_map_comap {L : Subgroup G} (P : Subgroup (Bar2 L)) :
    CFSG.Open.pCoreOf 2 L ≤
      ((P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype) := by
  let f : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  intro x hx
  rw [CFSG.Open.pCoreOf] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨y, ?_, hyx⟩
  have hfy : f y = 1 := by
    change QuotientGroup.mk' (CFSG.pCore 2 ↥L) y = 1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff y).2 hy
  rw [Subgroup.mem_comap, hfy]
  exact P.one_mem

theorem isMaximalParabolicOf_preimage {L : Subgroup G} {P : Subgroup (Bar2 L)}
    (hPpar : IsParabolicTwo (Bar2 L) P) (hPcoat : IsCoatom P) :
    IsMaximalParabolicOf L
      ((P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype) := by
  let f : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  set X : Subgroup G := (P.comap f).map L.subtype with hXdef
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hXleL : X ≤ L := by
    rw [hXdef]
    exact Subgroup.map_subtype_le _
  have hXsub : X.subgroupOf L = P.comap f := by
    rw [hXdef]
    exact CFSG.Quasithin.A4.subgroupOf_map_subtype' L (P.comap f)
  have hXimg : (X.subgroupOf L).map f = P := by
    rw [hXsub]
    exact Subgroup.map_comap_eq_self_of_surjective (f := f) hf P
  have hpCoreX : CFSG.Open.pCoreOf 2 L ≤ X := by
    rw [hXdef]
    exact pCoreOf_le_map_comap P
  refine ⟨⟨hpCoreX, hXleL, ?_⟩, ?_, ?_⟩
  · rw [hXimg]
    exact hPpar
  · intro hXL
    have htop : (X.subgroupOf L).map f = ⊤ := by
      rw [hXL, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective f hf]
    rw [hXimg] at htop
    exact hPcoat.ne_top htop
  · intro Y hYpar hXY hYne
    obtain ⟨hOY, hYL, -⟩ := hYpar
    let Z : Subgroup (Bar2 L) := (Y.subgroupOf L).map f
    have hYZ : ((Z.comap f).map L.subtype) = Y :=
      map_comap_mk'_eq_of_pCoreOf_le hYL hOY
    have hPleZ : P ≤ Z := by
      rw [← hXimg]
      refine Subgroup.map_mono ?_
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hXY (Subgroup.mem_subgroupOf.mp hx))
    have hZne : Z ≠ ⊤ := by
      intro hZ
      apply hYne
      rw [← hYZ, hZ, Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype]
    have hZeq : Z = P := hPcoat.le_iff_eq hZne |>.mp hPleZ
    rw [← hYZ, hZeq]

private theorem map_subgroupOf_ne_top {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) :
    (D.M.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)) ≠ ⊤ := by
  intro htop
  have hO2M : CFSG.Open.pCoreOf 2 c.L ≤ D.M :=
    s23_9_O2L_of (D := D) (Ch := Ch) h1930 c
  have hpcH : CFSG.pCore 2 ↥c.L ≤ D.M.subgroupOf c.L := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hO2M (Subgroup.mem_map_of_mem c.L.subtype hx))
  have hsup : D.M.subgroupOf c.L ⊔ CFSG.pCore 2 ↥c.L = ⊤ :=
    (map_mk'_eq_top_iff (N := CFSG.pCore 2 ↥c.L) (H := D.M.subgroupOf c.L)).mp htop
  have hHtop : D.M.subgroupOf c.L = ⊤ := by
    rw [← sup_eq_left.mpr hpcH, hsup]
  exact uc22p20i_not_le_M D c.hL.1 (Subgroup.subgroupOf_eq_top.mp hHtop)

private theorem isParabolicTwo_Q3 {K : Type} [Field K] [Finite K] [CharP K 2] (j : Fin 2) :
    IsParabolicTwo (SpecialLinearGroup (Fin 3) K) (Q3 K j) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (p := 2) (K := K) (n := 3) (by norm_num)
  refine ⟨P, ?_⟩
  have hPset : (P : Set (SpecialLinearGroup (Fin 3) K)) =
      (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) := by
    have h : ((P : Subgroup (SpecialLinearGroup (Fin 3) K)) : Set _) =
        (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) := by
      rw [hP]
    exact h
  rw [hPset, normalizer_unitriangular]
  exact upperTriangular_le_Q3 j

theorem Ctx23L.exists_maxParabolic_of_isSLn {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D)
    (hSL3 : PartTwo.IsSLn (Bar2 c.L) 3 (CFSG.Open.pRank 2 D.Z)) :
    ∃ X : Subgroup G, IsMaximalParabolicOf c.L X ∧ D.T ⊓ c.L ≤ X ∧ ¬ X ≤ D.M := by
  classical
  obtain ⟨K, hKfield, hKfinite, hcard, ⟨e₀⟩⟩ := hSL3
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := CFSG.Open.pRank 2 D.Z)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  let e : SpecialLinearGroup (Fin 3) K ≃* Bar2 c.L :=
    (specialLinearGroupEquivStatedSL 3 K).trans e₀.symm
  let f : ↥c.L →* Bar2 c.L := QuotientGroup.mk' (CFSG.pCore 2 ↥c.L)
  have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective _
  let Ubar : Subgroup (Bar2 c.L) := (unitriangular 3 K).map e.toMonoidHom
  let Pbar : Fin 2 → Subgroup (Bar2 c.L) := fun j => (Q3 K j).map e.toMonoidHom
  have hres : ResidualOvergroupsAt (Bar2 c.L) Ubar Pbar := by
    have hker : e.toMonoidHom.ker ≤ scalars 3 K := by
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective]
      exact bot_le
    have h := linear_three_residual_of_cover (K := K) (S := Bar2 c.L)
      ⟨CFSG.Open.pRank 2 D.Z, hcard⟩ e.toMonoidHom e.surjective hker
    simpa [Ubar, Pbar] using h
  let Sbar : Subgroup (Bar2 c.L) := (D.T.subgroupOf c.L).map f
  have hSbar_sylow : IsSylowTwoOf Sbar ⊤ := by
    have hSLcoe :
        (((isSylowIn_T_inf_L c).toSylow : Sylow 2 ↥c.L) : Subgroup ↥c.L) =
          D.T.subgroupOf c.L := by
      rw [CFSG.Quasithin.IsSylowIn.coe_toSylow, Subgroup.inf_subgroupOf_right]
    have h := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow
      (((isSylowIn_T_inf_L c).toSylow : Sylow 2 ↥c.L).mapSurjective hf_surj)
    simpa [Sbar, hSLcoe, Sylow.coe_mapSurjective] using h
  have hUbar_sylow : IsSylowTwoOf Ubar ⊤ := by
    obtain ⟨P, hP⟩ := exists_sylow_unitriangular (p := 2) (K := K) (n := 3) (by norm_num)
    have h := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow
      (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    simpa [Ubar, hP, Sylow.coe_mapSurjective] using h
  obtain ⟨g, -, hSbar_eq⟩ := hUbar_sylow.exists_conj hSbar_sylow
  let P' : Fin 2 → Subgroup (Bar2 c.L) :=
    fun j => (Pbar j).map (MulAut.conj g).toMonoidHom
  have hres' : ResidualOvergroupsAt (Bar2 c.L) Sbar P' := by
    rw [hSbar_eq]
    simpa [P'] using hres.map (MulAut.conj g)
  let Ybar : Subgroup (Bar2 c.L) := (D.M.subgroupOf c.L).map f
  have hSY : Sbar ≤ Ybar := by
    refine Subgroup.map_mono ?_
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (D.sylowM.le (Subgroup.mem_subgroupOf.mp hx))
  have hYne : Ybar ≠ ⊤ := map_subgroupOf_ne_top c h1930
  obtain ⟨j, hj⟩ := exists_not_le_of_residualOvergroupsAt hres' hSY hYne
  obtain ⟨-, hUP, hmax, -, -, -⟩ := hres'
  have hP'coat (i : Fin 2) : IsCoatom (P' i) :=
    covBy_top_iff.mp ((hmax (P' i) (hUP i)).mpr ⟨i, rfl⟩)
  let X : Subgroup G := ((P' j).comap f).map c.L.subtype
  have hP'par (i : Fin 2) : IsParabolicTwo (Bar2 c.L) (P' i) := by
    have h := (isParabolicTwo_Q3 (K := K) i).map e.toMonoidHom e.surjective
    simpa [P', Pbar] using h.map (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
  have hXmax : IsMaximalParabolicOf c.L X :=
    isMaximalParabolicOf_preimage (hP'par j) (hP'coat j)
  have hTX : D.T ⊓ c.L ≤ X := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
    exact Subgroup.mem_comap.mpr
      (hUP j (Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hx.1)))
  have hXM : ¬ X ≤ D.M := by
    intro hXM
    apply hj
    intro p hp
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥c.L) p
    have hlX : (l : G) ∈ X :=
      Subgroup.mem_map.mpr ⟨l, Subgroup.mem_comap.mpr hp, rfl⟩
    have hlM : (l : G) ∈ D.M := hXM hlX
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hlM, rfl⟩
  exact ⟨X, hXmax, hTX, hXM⟩

