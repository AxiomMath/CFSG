module

public import CFSG.Quasithin.H13.A5X1367m
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

theorem exists_cComp_map_eq_of_span {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q] [Finite Q]
    (f : Γ →* Q) {X : Subgroup Γ} (hX : cCompSpan X = perfectCore X) {K : Subgroup Q}
    (hK : IsComponentOf K (X.map f)) : ∃ L ∈ cComp X, L.map f = K := by
  have hq : CFSG.IsQuasisimple ↥K := B1Red.isQuasisimple_of_open hK.2.2
  have hKp : ⁅K, K⁆ = K := S153L.comp_perfect_of_isQuasisimple hq
  have hKne : K ≠ ⊥ := SBc3.ne_bot_of_isQuasisimple hq
  obtain ⟨L, hL, hKL⟩ : ∃ L ∈ cComp X, K ≤ L.map f := by
    by_contra hno
    push Not at hno
    have hc : ∀ L ∈ cComp X, L ≤ (Subgroup.centralizer (K : Set Q)).comap f := by
      intro L hL
      rw [← Subgroup.map_le_iff_le_comap]
      rcases B113.component_le_or_commutator_eq_bot hK
          (A3.subnormal_map f (subnormal_of_mem_cComp hL)) with h | h
      · exact absurd h (hno L hL)
      · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
        exact Subgroup.le_centralizer_iff.mp h
    have hspan : (cCompSpan X).map f ≤ Subgroup.centralizer (K : Set Q) :=
      Subgroup.map_le_iff_le_comap.mpr (show sSup (cComp X) ≤ _ from sSup_le hc)
    rw [hX, map_perfectCore] at hspan
    have hKc : K ≤ Subgroup.centralizer (K : Set Q) :=
      (le_perfectCore_of_perfect hK.1 hKp).trans hspan
    exact hKne (hKp.symm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKc))
  refine ⟨L, hL, le_antisymm ?_ hKL⟩
  obtain ⟨P, hP⟩ : ∃ P : Subgroup Γ, P = K.comap f ⊓ L := ⟨_, rfl⟩
  have hKsub : IsSubnormal K (L.map f) :=
    A3.subnormal_of_le_of_le hK.2.1 hKL (Subgroup.map_mono (le_of_mem_cComp hL))
  have hPsub : IsSubnormal P L := by
    rw [hP]
    exact A3.subnormal_inf_right (A3.subnormal_comap f hKsub) (Subgroup.le_comap_map f L)
  have hPmap : P.map f = K := by
    rw [hP]
    refine le_antisymm ((Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le f K)) ?_
    intro k hk
    obtain ⟨l, hl, rfl⟩ := hKL hk
    exact ⟨l, ⟨hk, hl⟩, rfl⟩
  have hcore : (perfectCore P).map f = K := by
    rw [map_perfectCore, hPmap, perfectCore_eq_self_of_perfect hKp]
  have hcne : perfectCore P ≠ ⊥ := by
    intro h
    apply hKne
    rw [← hcore, h, Subgroup.map_bot]
  have hcL : perfectCore P ≤ L := (perfectCore_le P).trans (hP ▸ inf_le_right)
  have hceq : perfectCore P = L := by
    by_contra hne
    exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hcL hne) hcne (perfectCore_perfect P)
      (A3.subnormal_trans (A3.subnormal_perfectCore hPsub) (subnormal_of_mem_cComp hL))
  rw [← hceq, hcore]

theorem commutator_eq_self_of_qs {Γ : Type} [Group Γ] {K A : Subgroup Γ}
    (hq : CFSG.IsQuasisimple ↥K) (hAN : A ≤ Subgroup.normalizer (K : Set Γ))
    (hne : ¬ A ≤ Subgroup.centralizer (K : Set Γ)) : ⁅K, A⁆ = K := by
  have hDK : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hAN
  have hKD : K ≤ Subgroup.normalizer ((⁅K, A⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_left K A
  have hDn : ((⁅K, A⁆ : Subgroup Γ).subgroupOf K).Normal :=
    ⟨fun x hx k => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hKD k.2) _).mp hx⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hDn with htop | hcen
  · refine le_antisymm hDK fun k hk => ?_
    have : (⟨k, hk⟩ : K) ∈ (⁅K, A⁆ : Subgroup Γ).subgroupOf K := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    apply hne
    have hDC : ⁅K, A⁆ ≤ Subgroup.centralizer (K : Set Γ) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hxc := Subgroup.mem_center_iff.mp
        (hcen (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hDK hx⟩ : K) ∈ _)) ⟨k, hk⟩
      exact congrArg Subtype.val hxc
    have h1 : ⁅⁅K, A⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDC
    have h2 : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact h1
    have h := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [S153L.comp_perfect_of_isQuasisimple hq] at h
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h

theorem pCoreOf_two_le_of_subnormal {Γ : Type} [Group Γ] [Finite Γ] {H K : Subgroup Γ}
    (h : IsSubnormal H K) : pCoreOf 2 H ≤ pCoreOf 2 K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    have hHM : M ≤ Subgroup.normalizer (H : Set Γ) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hle)
      (hHM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem autOn_le_normalizer_autOn {G : Type} [Group G] {U Y H : Subgroup G}
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) :
    autOn H U ≤ Subgroup.normalizer ((autOn Y U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hHY

theorem autOn_conjClosure {G : Type} [Group G] {U Z H : Subgroup G}
    (hZ : Z ≤ Subgroup.normalizer (U : Set G)) (hH : H ≤ Subgroup.normalizer (U : Set G)) :
    autOn (conjClosure Z H) U = conjClosure (autOn Z U) (autOn H U) := by
  apply le_antisymm
  · obtain ⟨R, hR⟩ : ∃ R, R = conjClosure (autOn Z U) (autOn H U) := ⟨_, rfl⟩
    have hZH : conjClosure Z H ≤
        (R.comap (conjAct U)).map (Subgroup.normalizer (U : Set G)).subtype := by
      refine conjClosure_le fun h hh z hz => ?_
      refine ⟨⟨h, hH hh⟩ * ⟨z, hZ hz⟩ * (⟨h, hH hh⟩)⁻¹, ?_, rfl⟩
      show conjAct U _ ∈ R
      rw [map_mul, map_mul, map_inv, hR]
      exact mem_conjClosure ⟨⟨h, hH hh⟩, hh, rfl⟩ ⟨⟨z, hZ hz⟩, hz, rfl⟩
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨g', hg', hgg⟩ := hZH hg
    have e : g' = g := Subtype.ext hgg
    rw [← hR, ← e]
    exact hg'
  · refine conjClosure_le fun φ hφ ψ hψ => ?_
    obtain ⟨h, hh, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨z, hz, rfl⟩ := Setup.mem_autOn_iff.1 hψ
    refine Setup.mem_autOn_iff.2 ⟨h * z * h⁻¹, mem_conjClosure hh hz, ?_⟩
    rw [map_mul, map_mul, map_inv]

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem autOn_eq_map_rhoGv {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({S.v12} : Set G)) :
    autOn K S.Uv = (K.subgroupOf (Subgroup.centralizer ({S.v12} : Set G))).map
      (Setup.rho S.Uv (Subgroup.centralizer ({S.v12} : Set G)) S.Gv_le_normalizer_Uv) := by
  ext φ
  rw [Setup.mem_autOn_iff_rho S.Gv_le_normalizer_Uv hK, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hpK, rfl⟩
    exact ⟨p, hpK, rfl⟩
  · rintro ⟨p, hpK, rfl⟩
    exact ⟨p, hpK, rfl⟩

theorem exists_cComp_autOn_eq (h39 : Vol2Native.A39ForSQTKCat)
    (hO2 : pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) ≠ ⊥)
    {Kb : Subgroup (MulAut ↥S.Uv)}
    (hK : IsComponentOf Kb (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) :
    ∃ K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)), autOn K S.Uv = Kb := by
  have : IsSimpleGroup G := S.h13.simple
  have : Finite (MulAut ↥S.Uv) := MulEquiv.finite_left
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  obtain ⟨Gv, hGv⟩ : ∃ Gv, Gv = Subgroup.centralizer ({S.v12} : Set G) := ⟨_, rfl⟩
  rw [← hGv] at hO2 hK ⊢
  have hGvN : Gv ≤ Subgroup.normalizer (S.Uv : Set G) := hGv ▸ S.Gv_le_normalizer_Uv
  have hspan : cCompSpan Gv = perfectCore Gv := Vol2Native.lemma_1_2_1_one hloc h39 hO2
  have hspan' : cCompSpan (⊤ : Subgroup ↥Gv) = perfectCore (⊤ : Subgroup ↥Gv) := by
    apply Subgroup.map_injective Gv.subtype_injective
    rw [← cCompSpan_eq_map_subtype, hspan, map_perfectCore, Subgroup.map_top,
      Subgroup.range_subtype]
  have hrange : (⊤ : Subgroup ↥Gv).map (Setup.rho S.Uv Gv hGvN) = autOn Gv S.Uv := by
    rw [Subgroup.map_top, Setup.range_rho]
  rw [← hrange] at hK
  obtain ⟨L', hL', hL'K⟩ := exists_cComp_map_eq_of_span _ hspan' hK
  refine ⟨L'.map Gv.subtype, map_subtype_mem_cComp hL', ?_⟩
  have hmap : autOn (L'.map Gv.subtype) S.Uv = L'.map (Setup.rho S.Uv Gv hGvN) := by
    ext φ
    rw [Setup.mem_autOn_iff_rho hGvN (Subgroup.map_subtype_le L'), Subgroup.mem_map]
    constructor
    · rintro ⟨p, ⟨q, hq, hqp⟩, rfl⟩
      have e : q = p := Subtype.ext hqp
      exact ⟨q, hq, by rw [e]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, ⟨p, hp, rfl⟩, rfl⟩
  rw [hmap, hL'K]

theorem GvS_le_normalizer_conjClosure (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) :
    autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer ((conjClosure (autOn K S.Uv) (autOn S.Tv S.Uv) :
        Subgroup (MulAut ↥S.Uv)) : Set (MulAut ↥S.Uv)) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hN := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38
    (S.pCoreOf_Gv_ne_bot h1222 h517 hF) (S.isSylowTwoOf_Tv h1222 h517) hK
  rw [← autOn_conjClosure ((le_of_mem_cComp hK).trans S.Gv_le_normalizer_Uv)
    (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)]
  exact autOn_le_normalizer_autOn hN

theorem inXz_of_goodComp {Kb : Subgroup (MulAut ↥S.Uv)} (hgood : S.GoodComp Kb)
    (hGN : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer ((conjClosure Kb (autOn S.Tv S.Uv) :
        Subgroup (MulAut ↥S.Uv)) : Set (MulAut ↥S.Uv))) :
    S.InXz (conjClosure Kb (autOn S.Tv S.Uv)) := by
  have : Finite (MulAut ↥S.Uv) := MulEquiv.finite_left
  obtain ⟨X, hX⟩ : ∃ X, X = conjClosure Kb (autOn S.Tv S.Uv) := ⟨_, rfl⟩
  rw [← hX] at hGN ⊢
  have hq : CFSG.IsQuasisimple ↥Kb := B1Red.isQuasisimple_of_open hgood.1.2.2
  have hKp : ⁅Kb, Kb⁆ = Kb := S153L.comp_perfect_of_isQuasisimple hq
  have hKne : Kb ≠ ⊥ := SBc3.ne_bot_of_isQuasisimple hq
  have hTG := S.autOn_le_GvS S.Tv_le_Gv
  have hKX : ∀ t ∈ autOn S.Tv S.Uv, Kb.map (MulAut.conj t).toMonoidHom ≤ X := by
    rintro t ht _ ⟨k, hk, rfl⟩
    rw [hX]
    exact mem_conjClosure ht hk
  have hXG : X ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv := by
    rw [hX]
    exact conjClosure_le fun t ht k hk => Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hTG ht) (hgood.1.1 hk)) (Subgroup.inv_mem _ (hTG ht))
  have hXne : X ≠ ⊥ := by
    intro h
    apply hKne
    rw [eq_bot_iff, ← h, hX]
    exact le_conjClosure _ _
  have hXp : ⁅X, X⁆ = X := by
    refine le_antisymm (A3.commutator_self_le X) ?_
    conv_lhs => rw [hX]
    refine conjClosure_le fun t ht k hk => ?_
    have h1 : t * k * t⁻¹ ∈
        (⁅Kb, Kb⁆ : Subgroup (MulAut ↥S.Uv)).map (MulAut.conj t).toMonoidHom := by
      rw [hKp]
      exact ⟨k, hk, rfl⟩
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono (hKX t ht) (hKX t ht) h1
  have hJT : autOn (thompsonJ S.Tv) S.Uv ≤ autOn S.Tv S.Uv :=
    A4.autOn_mono (iSup₂_le fun _ hA => hA.1)
  have hTJ : autOn S.Tv S.Uv ≤
      Subgroup.normalizer ((autOn (thompsonJ S.Tv) S.Uv : Subgroup (MulAut ↥S.Uv)) :
        Set (MulAut ↥S.Uv)) :=
    autOn_le_normalizer_autOn
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ S.Tv))
  have hKJ := commutator_eq_self_of_qs hq hgood.2.1 hgood.2.2
  have hTX : autOn S.Tv S.Uv ≤ Subgroup.normalizer (X : Set (MulAut ↥S.Uv)) := by
    rw [hX]
    exact le_normalizer_conjClosure _ _
  have hXJ : ⁅X, autOn (thompsonJ S.Tv) S.Uv⁆ = X := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp (hJT.trans hTX)) ?_
    conv_lhs => rw [hX]
    refine conjClosure_le fun t ht k hk => ?_
    have h1 : t * k * t⁻¹ ∈ (⁅Kb, autOn (thompsonJ S.Tv) S.Uv⁆ :
        Subgroup (MulAut ↥S.Uv)).map (MulAut.conj t).toMonoidHom := by
      rw [hKJ]
      exact ⟨k, hk, rfl⟩
    have hJt : (autOn (thompsonJ S.Tv) S.Uv).map (MulAut.conj t).toMonoidHom =
        autOn (thompsonJ S.Tv) S.Uv := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
    rw [Subgroup.map_commutator, hJt] at h1
    exact Subgroup.commutator_mono (hKX t ht) le_rfl h1
  refine ⟨⟨hXG, (A4.autOn_mono (sup_le S.Lv_le_Gv S.Tv_le_Gv)).trans hGN, ?_, hXne, hXJ⟩,
    S.exists_apply_ne_zU_of_normal hGN hXne⟩
  rw [oTwoRes_eq_oTwoUpper]
  exact C2Nine.oTwoUpper_eq_of_perfect hXp

theorem inYz_of_goodComp (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hgood : S.GoodComp (autOn K S.Uv)) : S.InYz K := by
  refine ⟨le_of_mem_cComp hK, cComp_subset_lFamily S.Tv_le_Gv hK, ?_,
    S.inXz_of_goodComp hgood (S.GvS_le_normalizer_conjClosure h1222 h517 h37 h38 hF hK)⟩
  have hq : CFSG.IsQuasisimple ↥(autOn K S.Uv) := B1Red.isQuasisimple_of_open hgood.1.2.2
  have hO : CFSG.pCore 2 ↥(autOn K S.Uv) = ⊥ := by
    have h1 : pCoreOf 2 (autOn K S.Uv) = ⊥ :=
      le_bot_iff.mp ((pCoreOf_two_le_of_subnormal hgood.1.2.1).trans
        (S.pCoreOf_GvS h1222 h517 hF).le)
    exact (Subgroup.map_eq_bot_iff_of_injective _ (autOn K S.Uv).subtype_injective).mp h1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)) hq

end Setting

theorem exists1367_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h56 : AsB56) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) : Exists1367 := by
  intro G _ _ T L V S hH
  obtain ⟨Kb, hKb⟩ := S.exists_goodComp h1222 h517 h56 hH
  obtain ⟨K, hK, hKK⟩ :=
    S.exists_cComp_autOn_eq h39 (S.pCoreOf_Gv_ne_bot h1222 h517 hH.hF) hKb.1
  refine ⟨K, S.inYz_of_goodComp h1222 h517 h37 h38 hH.hF hK ?_⟩
  rw [hKK]
  exact hKb

end CFSG.Quasithin.H13.A5
