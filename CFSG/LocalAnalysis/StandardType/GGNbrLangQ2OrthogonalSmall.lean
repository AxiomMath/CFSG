module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2LinBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Toral
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Res
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CoverData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem q2_orthogonalPlus_d3
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (d : ℕ) (h3 : d = 3) (K : Type) [Field K] [Finite K]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hrow : GGInnerDiagOnLab
      (fun p lab => q2RowFits .orthogonalPlus p d (Nat.card K) lab) p Bs L) :
    IsMulCommutative
      ((((ggBsAut hN).range).map (kgInducedAut θ)).comap
        (TableB.linConjAut (Fin d) K)) := by
  classical
  subst d
  unfold GGInnerDiagOnLab at hrow
  obtain ⟨hperf, lab, hlabΛ, hraw⟩ := hrow
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R₀, _instR₀, I₀, F₀, hcont₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hfit₀, -, -, -⟩ := hcont₀
  obtain ⟨htag, hrank, -, -, -⟩ :=
    q2RowFits_orthogonalPlus_parameters hlabΛ hfit₀
  cases htag
  cases hrank
  have hp3 : p = 3 := q2RowFits_orthogonalPlus_three hfit₀
  subst p
  let Q0 : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
    ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
      q2RowFits .orthogonalPlus 3 3 (Nat.card K) (⟨.D, 3, n⟩ : LargeEvenLabel) ∧
      LargeEvenSplit 3 (⟨.D, 3, n⟩ : LargeEvenLabel) ∧
      Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b) φ
  have hrawQ0 : LargeEvenRawDatum (⟨.D, 3, n⟩ : LargeEvenLabel) Q0 :=
    (CFSG.StandardType.largeEvenRawDatum_legacy (⟨.D, 3, n⟩) Q0).2 hraw
  have hrawA3 : LargeEvenRawDatum (⟨.A, 3, n⟩ : LargeEvenLabel) Q0 :=
    (Q1DSmall.rawDatum_D3_iff_A3 n Q0).1 hrawQ0
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeLinear] at hrawA3
  obtain ⟨F, hFld, hFfin, hFcard, hcont⟩ := hrawA3
  letI : Field F := hFld
  letI : Finite F := hFfin
  haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  obtain ⟨-, -, θL, hfit, hsplit, hNL, hact⟩ := hcont
  obtain ⟨-, -, -, hn2, hKcard⟩ :=
    q2RowFits_orthogonalPlus_parameters hlabΛ hfit
  have hn2' : 2 ≤ n := by simpa using hn2
  have hKcard' : Nat.card K = 2 ^ n := by simpa using hKcard
  have hn1 : 1 ≤ n := by omega
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  let ML : Subgroup (MulAut ↥L) := (ggBsAut hNL).range
  let R : Type := LargeEvenProj (LargeEvenSLGroup (Fin 4) F)
  let Abar : Subgroup (MulAut R) := ML.map (ggInducedAut θL)
  have hAbarElem : IsElemAbelian 3 Abar :=
    CFSG.Open.IsElemAbelian.map (ggBsAut_range_isElemAbelian hBs hNL) (ggInducedAut θL)
  have hAbarI : ∀ a ∈ Abar,
      a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) F)) Set.univ := by
    rintro a ⟨u, hu, rfl⟩
    obtain ⟨b, rfl⟩ := hu
    obtain ⟨φ, hφI, hφind⟩ := hact ((b : G)⁻¹) (Bs.inv_mem b.2)
    have hφeq : φ = ggInducedAut θL (ggBsAut hNL b) := by
      ext r
      obtain ⟨q, rfl⟩ := θL.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      rw [ggInducedAut_apply]
      exact hφind l (ggBsAut hNL b l) (by
        change (((ggGamma L hNL b) l : ↥L) : G) = (((b : G)⁻¹)⁻¹) * (l : G) * ((b : G)⁻¹)
        rw [ggGamma_coe L hNL b l]
        simp only [inv_inv])
    rwa [hφeq] at hφI
  obtain ⟨y, u, hyD, hyu, huord, hcommu, hJL, hJcompOpen⟩ :=
    q1_fixed_component_data hcfg hNL
  have huML : u ∈ ML := by
    refine ⟨y, ?_⟩
    change ggGamma L hNL y = u
    exact hyu
  have huAbar : ggInducedAut θL u ∈ Abar :=
    Subgroup.mem_map_of_mem (ggInducedAut θL) huML
  have hIu : ggInducedAut θL u ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) F)) Set.univ :=
    hAbarI _ huAbar
  obtain ⟨A_u, hA_u⟩ := TableB.exists_eq_linConjAut hIu
  have hu3 : u ^ 3 = 1 := by
    rw [← huord, pow_orderOf_eq_one]
  have hg3ker : TableB.linConjAut (Fin 4) F (A_u ^ 3) = 1 := by
    rw [map_pow, ← hA_u, ← map_pow, hu3, map_one]
  have hg3center : A_u ^ 3 ∈ Subgroup.center (GL (Fin 4) F) :=
    linConjAut_ker_le_center (d := 4) (K := F) (by norm_num)
      (MonoidHom.mem_ker.mpr hg3ker)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg3center
  obtain ⟨c, hc⟩ := hg3center
  have hc_pow : c ^ (Nat.card F - 1) = 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
    have hcard : Fintype.card Fˣ = Nat.card F - 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_units]
    have := pow_card_eq_one (x := c)
    rwa [hcard] at this
  have hpow : (A_u ^ 3) ^ (Nat.card F - 1) = 1 := by
    rw [← hc, ← map_pow, hc_pow, map_one]
  have hdvd : orderOf A_u ∣ 3 * (Nat.card F - 1) := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [pow_mul]
    exact hpow
  have hodd : Odd (orderOf A_u) := by
    have h3odd : Odd 3 := by norm_num
    have hFodd : Odd (Nat.card F - 1) := by
      rw [hFcard]
      exact CFSG.StandardType.ggOdd_two_pow_sub_one hn1
    exact (h3odd.mul hFodd).of_dvd_nat hdvd
  let Jsub : Subgroup ↥L := J.subgroupOf L
  let J0 : Subgroup R := Jsub.map (q2CoverMap θL)
  obtain ⟨hJ0open, ι, hι_mk⟩ := q2_cover_data hperf θL u Jsub hJcompOpen
  have hJ0open' : CFSG.Open.IsComponentOf J0
      (ggAutFixedSubgroup (ggInducedAut θL u)) := hJ0open
  have hJ0lin : CFSG.Open.IsComponentOf J0
      (ggAutFixedSubgroup (TableB.linConjAut (Fin 4) F A_u)) := by
    rw [← hA_u]
    exact hJ0open'
  obtain ⟨C, hC, hCSL, hJ0eq⟩ :=
    q1TorLin_component_lift (N := 4) (by norm_num) A_u J0 hJ0lin
  obtain ⟨m, D, hDFld, hDFin, ψ0, π, hπ⟩ :=
    q2Lin_block (N := 4) (by norm_num) (K := F) A_u hodd C hC hCSL J0 hJ0eq
  letI : Field D := hDFld
  letI : Finite D := hDFin
  let P : Type := ↥J ⧸ Subgroup.center ↥J
  let eJ : ↥J ≃* ↥Jsub := (Subgroup.subgroupOfEquivOfLe hJL).symm
  let eP0 : P ≃* (↥Jsub ⧸ Subgroup.center ↥Jsub) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥Jsub) eJ
      (Subgroup.map_center_eq eJ)
  let eP : P ≃* (↥J0 ⧸ Subgroup.center ↥J0) := eP0.trans ι
  let jL (j : ↥J) : ↥L := ⟨(j : G), hJL j.2⟩
  let j0 (j : ↥J) : ↥J0 :=
    ⟨θL (QuotientGroup.mk (jL j)),
      Subgroup.mem_map_of_mem (q2CoverMap θL)
        (Subgroup.mem_subgroupOf.mpr j.2)⟩
  have eP_mk (j : ↥J) : eP (QuotientGroup.mk j) = QuotientGroup.mk (j0 j) := by
    change ι (eP0 (QuotientGroup.mk j)) = _
    dsimp only [eP0]
    rw [QuotientGroup.congr_mk]
    rw [hι_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    change θL (QuotientGroup.mk ((eJ j : ↥L))) =
      θL (QuotientGroup.mk (jL j))
    rw [show (eJ j : ↥L) = jL j from Subtype.ext rfl]
  let ψ := eP.trans ψ0
  have hψ_mk (j : ↥J) : ψ (QuotientGroup.mk j) =
      ψ0 (QuotientGroup.mk (j0 j)) := by
    change ψ0 (eP (QuotientGroup.mk j)) = _
    rw [eP_mk]
  have hAb : ∀ b : ↥Bs, ∃ A : GL (Fin 4) F,
      ggInducedAut θL (ggBsAut hNL b) = TableB.linConjAut (Fin 4) F A := by
    intro b
    exact TableB.exists_eq_linConjAut
      (hAbarI _ (Subgroup.mem_map_of_mem (ggInducedAut θL)
        (show ggBsAut hNL b ∈ ML from ⟨b, rfl⟩)))
  let Ab (b : ↥Bs) : GL (Fin 4) F := Classical.choose (hAb b)
  have hAb_spec (b : ↥Bs) :
      ggInducedAut θL (ggBsAut hNL b) = TableB.linConjAut (Fin 4) F (Ab b) :=
    Classical.choose_spec (hAb b)
  let GLpre : Subgroup (GL (Fin 4) F) := Abar.comap (TableB.linConjAut (Fin 4) F)
  haveI hM1 : IsMulCommutative GLpre :=
    ggBstarAbelianPreimageJLin_comm_of_not_dvd (p := 3) (d := 4)
      (by norm_num) (by
        rintro ⟨h34, -⟩
        exact absurd h34 (by norm_num)) Abar hAbarElem
  have hAuPre : A_u ∈ GLpre := by
    change TableB.linConjAut (Fin 4) F A_u ∈ Abar
    rw [← hA_u]
    exact Subgroup.mem_map_of_mem (ggInducedAut θL) huML
  have hAbPre (b : ↥Bs) : Ab b ∈ GLpre := by
    change TableB.linConjAut (Fin 4) F (Ab b) ∈ Abar
    rw [← hAb_spec b]
    exact Subgroup.mem_map_of_mem (ggInducedAut θL)
      (show ggBsAut hNL b ∈ ML from ⟨b, rfl⟩)
  have hcomm_Ab (b b' : ↥Bs) : Ab b * Ab b' = Ab b' * Ab b := by
    have := mul_comm' (⟨Ab b, hAbPre b⟩ : GLpre) (⟨Ab b', hAbPre b'⟩ : GLpre)
    exact congrArg Subtype.val this
  have hcomm_u_Ab (b : ↥Bs) : A_u * Ab b = Ab b * A_u := by
    have := mul_comm' (⟨A_u, hAuPre⟩ : GLpre) (⟨Ab b, hAbPre b⟩ : GLpre)
    exact congrArg Subtype.val this
  let AbC (b : ↥Bs) : ↥(Subgroup.centralizer ({A_u} : Set (GL (Fin 4) F))) :=
    ⟨Ab b, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm_u_Ab b).symm⟩
  have hcomm_AbC (b b' : ↥Bs) : AbC b * AbC b' = AbC b' * AbC b :=
    Subtype.ext (hcomm_Ab b b')
  let Glin : Subgroup (GL (Fin m) D) :=
    Subgroup.closure (Set.range (fun b : ↥Bs => π (AbC b)))
  have hGcomm : IsMulCommutative Glin := by
    change IsMulCommutative (Subgroup.closure (Set.range (fun b : ↥Bs => π (AbC b))))
    apply CFSG.subgroup_isMulCommutative_closure
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    rw [← map_mul, ← map_mul, hcomm_AbC b b']
  have h_action (b : ↥Bs) (j : ↥J) :
      (j0 (ggBsAut hN b j) : R) =
        TableB.linConjAut (Fin 4) F (AbC b : GL (Fin 4) F) (j0 j : R) := by
    change θL (QuotientGroup.mk (jL (ggBsAut hN b j))) =
      TableB.linConjAut (Fin 4) F (Ab b) (θL (QuotientGroup.mk (jL j)))
    rw [← hAb_spec b]
    rw [ggInducedAut_apply]
    apply congrArg (fun l : ↥L => θL (QuotientGroup.mk l))
    apply Subtype.ext
    change (b : G) * (j : G) * (b : G)⁻¹ = (b : G) * ((jL j : ↥L) : G) * (b : G)⁻¹
    rfl
  have hπ_app (b : ↥Bs) (j : ↥J) :
      TableB.linConjAut (Fin m) D (π (AbC b))
          (ψ0 (QuotientGroup.mk (j0 j))) =
        ψ0 (QuotientGroup.mk (j0 (ggBsAut hN b j))) :=
    hπ (AbC b) (j0 j) (j0 (ggBsAut hN b j)) (h_action b j)
  have hcongr (b : ↥Bs) :
      MulAut.congr ψ (centerQuotAut ↥J (ggBsAut hN b)) =
        TableB.linConjAut (Fin m) D (π (AbC b)) := by
    ext x
    obtain ⟨y, rfl⟩ := ψ.surjective x
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MulAut.congr_apply]
    rw [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_apply]
    rw [MulEquiv.trans_apply]
    rw [centerQuotAut_mk]
    rw [hψ_mk, hψ_mk]
    exact (hπ_app b j).symm
  let Mact : Subgroup (MulAut P) := (ggBsAut hN).range.map (centerQuotAut ↥J)
  have hQ2Lift : Q2LinearLift Mact := by
    refine ⟨m, D, hDFld, hDFin, ψ, Glin, hGcomm, ?_⟩
    rintro α hα
    change α ∈ (ggBsAut hN).range.map (centerQuotAut ↥J) at hα
    obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hα
    obtain ⟨b, rfl⟩ := hβ
    exact ⟨π (AbC b), Subgroup.subset_closure ⟨b, rfl⟩, hcongr b⟩
  have hfinal := q2_commutative_of_linearLift (P := P) (M := Mact) hQ2Lift
    (d := 3) (K := K) (by norm_num) (m := n) hn2' hKcard' θ
  have hmap : Mact.map (MulAut.congr θ).toMonoidHom =
      (ggBsAut hN).range.map (kgInducedAut θ) := by
    change ((ggBsAut hN).range.map (centerQuotAut ↥J)).map
      (MulAut.congr θ).toMonoidHom = _
    rw [Subgroup.map_map]
    rfl
  rwa [hmap] at hfinal

end CFSG.StandardType

end
