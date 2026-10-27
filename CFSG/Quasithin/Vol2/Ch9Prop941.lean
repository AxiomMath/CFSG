module

public import CFSG.Quasithin.Vol2.Ch9Sec4Core

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem map_conj_centralizer_singleton (v m : G) :
    (Subgroup.centralizer ({v} : Set G)).map (MulAut.conj m).toMonoidHom =
      Subgroup.centralizer ({m * v * m⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    show m * y * m⁻¹ * (m * v * m⁻¹) = m * v * m⁻¹ * (m * y * m⁻¹)
    calc m * y * m⁻¹ * (m * v * m⁻¹) = m * (y * v) * m⁻¹ := by group
      _ = m * (v * y) * m⁻¹ := by rw [hy']
      _ = m * v * m⁻¹ * (m * y * m⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨m⁻¹ * x * m, ?_, by simp [mul_assoc]⟩
    show m⁻¹ * x * m ∈ Subgroup.centralizer ({v} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m⁻¹ * x * m * v = m⁻¹ * (x * (m * v * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * v * m⁻¹) * x) * m := by rw [hx]
      _ = v * (m⁻¹ * x * m) := by group

theorem isSylowIn_map_conj' {p : ℕ} [Fact p.Prime] {P H : Subgroup G} (hP : IsSylowIn p P H)
    (g : G) :
    IsSylowIn p (P.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  refine isSylowIn_of_card_eq (Subgroup.map_mono hP.le) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hP.card_eq

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {X₀ : Matrix (Fin 2) (Fin 2) K}

theorem prop941_of_sylow (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h2 : n = 2) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v} : Set G))) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ∈ cComp (Subgroup.centralizer ({v} : Set G)) ∧
      Subgroup.centralizer ({v} : Set G) ≤
        Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X₀)) : Set G) := by
  have hfsu := S.hyp.fsu
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  set Gv := Subgroup.centralizer ({v} : Set G) with hGv
  set Tv := T ⊓ Gv with hTv
  set LW := lPt T L (inV e (Om4Pt.lineM X₀)) with hLW
  have hvV : v ∈ fsuV T I := inV_le e _ hv
  have hv2 : v ^ 2 = 1 := S.hV.2 v hvV
  have hTvG : IsSylowTwoOf Tv Gv := S.isSylowTwoOf_centralizer h3104 hvV hv1 hsyl
  have hvGv : v ∈ Gv := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hOGv : pCoreOf 2 Gv ≠ ⊥ := fun h => hv1 (by
    have := mem_pCoreOf_of_le_centralizer hv2 hv1 hvGv le_rfl
    rwa [h, Subgroup.mem_bot] at this)
  have hLWGv : LW ≤ Gv := fun l hl => by
    have h1 := Subgroup.mem_centralizer_iff.mp (hc.lPt_le_centralizer hK4 hX hl) v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
  have hnormLW : fsuM T L ⊓ Gv ≤ Subgroup.normalizer (LW : Set G) := fun x hx =>
    hc.mem_normalizer_lPt hx.1 hv hv1 (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rw [this, mul_inv_cancel_right])
  have hTvN : Tv ≤ Subgroup.normalizer (LW : Set G) := hsyl.1.trans hnormLW
  have hLWl : LW ∈ lFamily Tv := hc.mem_lFamily_lPt h37c h38c hK4 hX hTvN
  obtain ⟨Lv, hLv, hLWLv⟩ := lemma_1_2_4_exists hfsu.qtke hfsu.simple hfsu.nonabelian h37 h39
    hOGv hTvG hLWGv hLWl
  have hLvn := lemma_1_2_4_normal hfsu.qtke hfsu.simple hfsu.nonabelian h37 h38 hOGv hTvG hLWl
    hLWLv hLv hTvN
  have hGvLv : Gv ≤ Subgroup.normalizer (Lv : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hLv)).mp hLvn
  rcases eq_or_lt_of_le hLWLv with heq | hlt
  · rw [heq]
    exact ⟨hLv, hGvLv⟩
  · exact (hc.prop941_false h36 h312 h314 h37c h38c h3104 h3108 hFa hFb h2 hX hv hv1 hsyl hLv hlt
      hGvLv).elim

theorem prop941 (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h2 : n = 2) (hX : X₀.det ≠ 0) {v : G}
    (hv : v ∈ inV e (Om4Pt.lineM X₀)) (hv1 : v ≠ 1) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ∈ cComp (Subgroup.centralizer ({v} : Set G)) ∧
      Subgroup.centralizer ({v} : Set G) ≤
        Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X₀)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set Mv := fsuM T L ⊓ Subgroup.centralizer ({v} : Set G) with hMv
  obtain ⟨S₀, hS₀, -⟩ := exists_isSylowIn_ge 2 (bot_le : (⊥ : Subgroup G) ≤ Mv) IsPGroup.of_bot
  obtain ⟨S₁, hS₁, hS₀₁⟩ := exists_isSylowIn_ge 2 (hS₀.le.trans inf_le_left) hS₀.isPGroup
  have hTM : IsSylowIn 2 T (fsuM T L) :=
    ⟨Setup.T_le_fsuM, hfsu.sylow.1, fun h => hfsu.sylow.2
      (h.trans (Subgroup.relIndex_dvd_index_of_le Setup.T_le_fsuM))⟩
  obtain ⟨h, hhM, hh⟩ := Ch1Sec3.exists_conj_of_isSylowIn hTM hS₁
  set m := h⁻¹ with hm
  have hmM : m ∈ fsuM T L := (fsuM T L).inv_mem hhM
  have hS₀T : S₀.map (MulAut.conj m).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hh x).mp (hS₀₁ hx)
    simpa [hm, MulAut.conj_apply] using this
  set v' := m * v * m⁻¹ with hv'
  have hMv' : Mv.map (MulAut.conj m).toMonoidHom =
      fsuM T L ⊓ Subgroup.centralizer ({v'} : Set G) := by
    rw [hMv, Subgroup.map_inf_eq _ _ _ (MulAut.conj m).injective,
      Ch1Sec3.map_conj_eq_of_mem_normalizer (H := fsuM T L) (Subgroup.le_normalizer hmM),
      map_conj_centralizer_singleton]
  have hS₀' := isSylowIn_map_conj' hS₀ m
  rw [hMv'] at hS₀'
  have hsyl' : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v'} : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ({v'} : Set G)) := by
    have heq := Xi.IsSylowIn.eq_of_le hS₀'
      (inf_le_inf_right _ Setup.T_le_fsuM) (hfsu.sylow.1.to_le inf_le_left)
      (le_inf hS₀T (hS₀'.le.trans inf_le_right))
    rw [heq]
    exact hS₀'
  obtain ⟨X₁, hX₁, -, hW'⟩ := hc.exists_conj_inV_line hX hmM
  have hv'W : v' ∈ inV e (Om4Pt.lineM X₁) := by
    rw [← hW']
    exact ⟨v, hv, rfl⟩
  have hv'1 : v' ≠ 1 := by
    intro h1
    apply hv1
    have : v = m⁻¹ * v' * m := by rw [hv']; group
    rw [this, h1]
    group
  obtain ⟨hc1, hc2⟩ := hc.prop941_of_sylow h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb
    h2 hX₁ hv'W hv'1 hsyl'
  have hLW' : lPt T L (inV e (Om4Pt.lineM X₁)) =
      (lPt T L (inV e (Om4Pt.lineM X₀))).map (MulAut.conj m).toMonoidHom := by
    rw [← hW', conj_lPt hmM]
  have hGv' : Subgroup.centralizer ({v'} : Set G) =
      (Subgroup.centralizer ({v} : Set G)).map (MulAut.conj m).toMonoidHom :=
    (map_conj_centralizer_singleton v m).symm
  have hback : ∀ A : Subgroup G,
      (A.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom = A := by
    intro A
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨?_, fun y hy => ?_⟩
  · have := cComp_map_mulEquiv (MulAut.conj m⁻¹) hc1
    rwa [hLW', hGv', hback, hback] at this
  · have hy' : m * y * m⁻¹ ∈ Subgroup.centralizer ({v'} : Set G) := by
      rw [hGv']
      exact ⟨y, hy, rfl⟩
    have h1 := hc2 hy'
    rw [hLW'] at h1
    have h3 := mem_normalizer_map_conj (X := (lPt T L (inV e (Om4Pt.lineM X₀))).map
      (MulAut.conj m).toMonoidHom) (g := m⁻¹) (y := y) (by simpa [mul_assoc] using h1)
    rwa [hback] at h3

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
