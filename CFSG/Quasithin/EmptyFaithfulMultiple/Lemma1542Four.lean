module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Input311Solvable
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs3
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB513Solvable
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD14Proof
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputD15Proof
public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section General

variable {G : Type*} [Group G]

theorem le_centralizer_quasithinOmegaOneCenter (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp
    (((Subgroup.closure_le _).mpr fun _ hz => hz.1 :
      quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G)).trans inf_le_right)

theorem le_normalizer_inf_centralizer {M V : Subgroup G}
    (hV : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
    have h := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * v := by group
  intro g hg
  refine B6.mem_normalizer_of_forall_mem (fun c hc => ⟨M.mul_mem (M.mul_mem hg hc.1)
    (M.inv_mem hg), key g (hV hg) c hc.2⟩) (fun c hc => ?_)
  have h := key g⁻¹ (inv_mem (hV hg)) c hc.2
  rw [inv_inv] at h
  exact ⟨M.mul_mem (M.mul_mem (M.inv_mem hg) hc.1) hg, h⟩

variable [Finite G]

theorem pCoreOf_inf_centralizer_eq {M₀ V : Subgroup G} (hV : IsTwoReducedIn M₀ V) :
    pCoreOf 2 (M₀ ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 M₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := le_normalizer_inf_centralizer hV.2.1
  refine le_antisymm ?_ ?_
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_left)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  · exact le_pCoreOf_of_le_normalizer 2
      (le_inf (pCoreOf_le 2 M₀) (MinParabolic.pCoreOf_le_centralizer hV))
      (inf_le_left.trans (le_normalizer_pCoreOf 2 M₀)) (pCoreOf_isPGroup 2 M₀)

theorem qhatInt_le_qInt (H V : Subgroup G) (hV : IsElemAbelian 2 V) :
    qhatInt H V hV ≤ qInt H V hV :=
  @qhatOf_le_qOf V (commGroupOfElemAbelian hV) _ (autOn H V)

theorem exists_isHStar_le {T M M' : Subgroup G} (hM' : InH T M') (hM'M : ¬ M' ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ H ≤ M' := by
  obtain ⟨H, ⟨hHH, hHM, hHM'⟩, hmin⟩ :=
    (Set.toFinite {Y : Subgroup G | InH T Y ∧ ¬ Y ≤ M ∧ Y ≤ M'}).exists_minimal
      ⟨M', hM', hM'M, le_rfl⟩
  exact ⟨H, ⟨hHH, hHM, fun Y hY hYH hYM =>
    le_antisymm hYH (hmin ⟨hY, hYM, hYH.trans hHM'⟩ hYH)⟩, hHM'⟩

theorem d11Hyp_of (T : Sylow 2 G) {M₀ M H V : Subgroup G} (hM₀ : InH (T : Subgroup G) M₀)
    (hM : IsUniqueM M₀ M) (hV1 : V ≠ ⊥) (hV : IsTwoReducedIn M₀ V)
    (hCT : (T : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) =
      pCoreOf 2 (M₀ ⊓ Subgroup.centralizer (V : Set G)))
    (hH : IsHStar (T : Subgroup G) M H) : D11Hyp M₀ H T V (H ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowTwoOf (T : Subgroup G) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [show ((T : Subgroup G).subgroupOf ⊤).index = (T : Subgroup G).index from
      Subgroup.relIndex_top_right _]
    exact T.not_dvd_index
  refine
    { sylow₁ := A4.isSylowTwoOf_mono hSyl hM₀.1 le_top
      sylow₂ := A4.isSylowTwoOf_mono hSyl hH.1.1 le_top
      reduced := hV
      nontrivial := hV1
      unique_max := hH.isUniqueMaxOver T (hM₀.1.trans hM.1.2)
      centralizer := by rw [hCT, pCoreOf_inf_centralizer_eq hV]
      no_normal := fun N hN hNn => ?_ }
  by_contra hN1
  have hNle : N ≤ M₀ ⊔ H := (hN.trans (pCoreOf_le 2 M₀)).trans le_sup_left
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mp hNn
  have hloc : IsTwoLocal (Subgroup.normalizer (N : Set G)) :=
    ⟨N, hN1, (pCoreOf_isPGroup 2 M₀).to_le hN, rfl⟩
  obtain ⟨M'', hM'', hle⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge hloc
  have hM''M : M'' = M := hM.2 M'' ⟨hM'', le_sup_left.trans (hnorm.trans hle)⟩
  exact hH.2.1 (hM''M ▸ le_sup_right.trans (hnorm.trans hle))

end General

theorem qhatInt_le_two_of_not_le_pCoreOf (hE213 : InputE213Solvable) {G : Type} [Group G]
    [Finite G] (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G)
    {M₀ M H V : Subgroup G}
    (hTM₀ : (T : Subgroup G) ≤ M₀) (hM₀M : M₀ ≤ M) (hV : IsTwoReducedIn M₀ V)
    (hVM : V ≤ pCoreOf 2 M) (hH : IsHStar (T : Subgroup G) M H) (hHsolv : Group.IsSolvable H)
    (hVQ : ¬ V ≤ pCoreOf 2 H) : qhatInt M₀ V hV.2.2.1 ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : (T : Subgroup G) ≤ H := hH.1.1
  have hTM : (T : Subgroup G) ≤ M := hTM₀.trans hM₀M
  have hVT : V ≤ T :=
    (MinParabolic.le_pCoreOf_of_isTwoReduced hV).trans (pCoreOf_two_le_sylow M₀ T hTM₀)
  have hSyl : IsSylowTwoOf (T : Subgroup G) H := by
    refine A4.isSylowTwoOf_mono ⟨le_top, T.isPGroup', ?_⟩ hTH le_top
    rw [show ((T : Subgroup G).subgroupOf ⊤).index = (T : Subgroup G).index from
      Subgroup.relIndex_top_right _]
    exact T.not_dvd_index
  have hnN : ¬ H ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) := fun hle =>
    hVQ (hVT.trans (le_pCoreOf_of_le_normalizer 2 hTH hle T.isPGroup'))
  have hMP : MinParabolic H T (H ⊓ M) := ⟨hSyl, hnN, hH.isUniqueMaxOver T hTM⟩
  have hker := hMP.isSylowTwoOf_pCoreOf_kerIn
  have hV2 : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2.2.1.2 x x.2)⟩
  have hVker : ¬ V ≤ kerIn (H ⊓ M) H := by
    intro hVk
    have hp : IsPGroup 2 (V ⊔ pCoreOf 2 H : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hV2 (pCoreOf_isPGroup 2 H)
        ((hVT.trans hTH).trans (le_normalizer_pCoreOf 2 H))
    have h := (A4.isSylowTwoOf_iff_maximal.mp hker).2.2 _ (sup_le hVk hker.1) hp le_sup_right
    exact hVQ (le_sup_left.trans h)
  have hVO : V ≤ pCoreOf 2 (H ⊓ M) := by
    refine le_trans ?_ (le_pCoreOf_of_le_normalizer 2
      (inf_le_right : pCoreOf 2 M ⊓ (H ⊓ M) ≤ H ⊓ M) ?_
      ((pCoreOf_isPGroup 2 M).to_le inf_le_left))
    · exact le_inf hVM (le_inf (hVT.trans hTH) (hVT.trans hTM))
    · intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 M hg.2, Subgroup.le_normalizer hg⟩
  obtain ⟨A, hAT, hAe, hcub, hnc, hidx⟩ := hE213 G H T (H ⊓ M) V hMP hHsolv
    (fun p hp hp2 => pRank_le_two_of_pCoreOf_ne_bot_cat hK hH.1.2 hp hp2)
    (charTwo_of_inH hK.2.1 T hH.1) hVT (hTM₀.trans hV.2.1) hV.2.2.1 hVO hVker
  exact qhatOf_autOn_le_two hV.2.2.1 (hAT.trans hTM₀) ((hAT.trans hTM₀).trans hV.2.1) hAe hcub
    hnc hidx

theorem qInt_le_two_of_isDualFFInt_of_isSolvable {G : Type} [Group G] [Finite G]
    {M₀ V : Subgroup G} (hsolv : Group.IsSolvable M₀) (hV : IsTwoReducedIn M₀ V)
    (hdual : IsDualFFInt M₀ V hV.2.2.1) : qInt M₀ V hV.2.2.1 ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  let _ : CommGroup V := commGroupOfElemAbelian hVe
  have hsq : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (hVe.2 v v.2)
  set X₀ : Subgroup (MulAut V) := autOn M₀ V
  set D : Subgroup (MulAut (V →* Multiplicative (ZMod 2))) := X₀.map (dualAct V)
  set J : Subgroup (MulAut (V →* Multiplicative (ZMod 2))) := ffJ D
  set κ : M₀ →* MulAut V := (conjAct V).comp (Subgroup.inclusion hV.2.1)
  have hκr : κ.range = X₀ := range_conjAct_comp_inclusion hV.2.1
  set ψ : M₀ →* MulAut (V →* Multiplicative (ZMod 2)) := (dualAct V).comp κ with hψ
  have hψr : ψ.range = D := by rw [hψ, MonoidHom.range_comp, hκr]
  set K : Subgroup M₀ := J.comap ψ with hKdef
  set X : Subgroup (MulAut V) := K.map κ with hXdef
  have hXmap : X.map (dualAct V) = K.map ψ := by rw [hXdef, Subgroup.map_map]
  have hXD : X.map (dualAct V) = J := by
    rw [hXmap, hKdef, Subgroup.map_comap_eq, hψr]
    exact inf_eq_right.mpr (B6.ffJ_le D)
  have hXX₀ : X ≤ X₀ := hκr ▸ Subgroup.map_le_range κ K
  have hJ1 : J ≠ ⊥ := ffJ_ne_bot hdual
  have hpD : CFSG.Open.pCore 2 D = ⊥ :=
    pCore_map_eq_bot _ (dualAct_injective hsq) (pCore_autOn_eq_bot hV)
  have hpJ : CFSG.Open.pCore 2 J = ⊥ :=
    pCore_eq_bot_of_le_normalizer (B6.ffJ_le D) (B6.le_normalizer_ffJ D) hpD
  have hXsolv : Group.IsSolvable ↥X := by
    have hKsolv : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective
      (Subgroup.subtype_injective K)
    exact Group.isSolvable_of_surjective (κ.subgroupMap_surjective K)
  have hq := inputB513Solvable_holds V hsq X hXsolv (by rw [hXD]; exact hJ1)
    (by rw [hXD]; exact hpJ)
    (hXD.trans ((ffJ_ffJ D).symm.trans (congrArg (fun Y => ffJ Y) hXD.symm)))
  exact (kq_le_kq_of_le hXX₀ 2).trans hq

theorem stmt1542Four_of (hE213 : InputE213Solvable) (h311 : Input311Solvable) {G : Type}
    [Group G] [Finite G] {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T)
    (h2 : Stmt1542Two G T) : Stmt1542Four G T := by
  intro M₀ M V hM₀ hM hV1 hV hCT hVM
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM₀ : (S : Subgroup G) ≤ M₀ := hM₀.1
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hCM₁, hCM₂⟩ := hyp.two_centralizer_maximal
  have hSC := le_centralizer_quasithinOmegaOneCenter (S : Subgroup G)
  obtain ⟨M', hM', hM'ne⟩ : ∃ M' : Subgroup G, InM (S : Subgroup G) M' ∧ M' ≠ M := by
    by_cases h₁ : M₁ = M
    · exact ⟨M₂, ⟨hM₂, hSC.trans hCM₂⟩, fun h => hne (h₁.trans h.symm)⟩
    · exact ⟨M₁, ⟨hM₁, hSC.trans hCM₁⟩, h₁⟩
  have hM'M : ¬ M' ≤ M := fun hle => hM'ne (hM'.1.2 M hM.1.1.1 hle).symm
  obtain ⟨H, hH, hHM'⟩ := exists_isHStar_le (inH_of_inM hM') hM'M
  have : Group.IsSolvable M' := h2 M' hM'
  have hHsolv : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHM')
  have hD11 := d11Hyp_of S hM₀ hM hV1 hV hCT hH
  by_cases hVQ : V ≤ pCoreOf 2 H
  swap
  · exact qhatInt_le_two_of_not_le_pCoreOf hE213 hyp.qtke S hTM₀ hM.1.2 hV hVM hH hHsolv hVQ
  by_cases hdual : IsDualFFInt M₀ V hV.2.2.1
  · have hMs : Group.IsSolvable M := h2 M ⟨hM.1.1, hTM₀.trans hM.1.2⟩
    have hM₀s : Group.IsSolvable M₀ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM.1.2)
    exact (qhatInt_le_qInt _ _ _).trans (qInt_le_two_of_isDualFFInt_of_isSolvable hM₀s hV hdual)
  rcases inputD15Solvable_holds G M₀ H S V (H ⊓ M) hD11 hHsolv with
      h1 | ⟨hq, -⟩ | h3 | ⟨hq, -⟩ | ⟨-, -, hchief, -⟩
  · exact absurd hVQ h1
  · exact (qhatInt_le_qInt _ _ _).trans (hq.trans one_le_two)
  · exact absurd h3 hdual
  · exact (qhatInt_le_qInt _ _ _).trans hq
  ·
    exfalso
    have hsyl := inputD14Solvable_holds G M₀ H S V (H ⊓ M) hD11 hVQ hchief hdual hHsolv
      (charTwo_of_inH hyp.qtke.2.1 S hH.1)
    obtain ⟨R₀, hR₀1, hR₀R, hR₀n⟩ := h311 G S hyp.simple hyp.nonabelian hyp.qtke hyp.sylow M₀ H
      (pCoreOf 2 M₀) hM₀ hH.1 hHsolv ⟨H ⊓ M, hD11.unique_max⟩ hM₀.2
      (pCoreOf_two_le_sylow M₀ S hTM₀)
      hsyl (le_normalizer_pCoreOf 2 M₀)
    exact hR₀1 (hD11.no_normal R₀ hR₀R ((Subgroup.normal_subgroupOf_iff_le_normalizer
      ((hR₀R.trans (pCoreOf_le 2 M₀)).trans le_sup_left)).mpr hR₀n))

end CFSG.Quasithin.EmptyFaithfulMultiple
