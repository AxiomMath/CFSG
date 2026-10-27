module

public import CFSG.Quasithin.Vol2.Ch12Sec6L17a
public import CFSG.Quasithin.Vol2.Ch12Sec6L13c
public import CFSG.Quasithin.Vol2.Ch12Sec6VvKey

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 S126L19b S126L19d CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126NF

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem Lv_le_oThree (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) {X : Subgroup G}
    (hLX : Lv L v ≤ X) : Lv L v ≤ oThreePrimeResidual X := by
  set N := oThreePrimeResidual X with hNdef
  have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_oThreePrimeResidual Subgroup.le_normalizer
  have hn : Lv L v ≤ Subgroup.normalizer ((Lv L v ⊓ N : Subgroup G) : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl, hXN (hLX hl)⟩
  obtain ⟨A, hALv, hA, hcA⟩ := exists_nine_Lv h1222 F hH hv hβ
  have hAN : A ≤ Lv L v ⊓ N := fun a ha =>
    ⟨hALv ha, Subgroup.subset_closure ⟨hLX (hALv ha), 1, by simpa using hA.2 a ha⟩⟩
  rcases Lv_dichotomy h1222 F hH hv hβ inf_le_left hn with h | h
  · rw [← h]
    exact inf_le_right
  · exact (false_of_nine_le hA hcA hAN h).elim

theorem Lv_eq (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hGv : Gv v ≤ Subgroup.normalizer (L : Set G)) :
    Lv L v = perfectCore (oThreePrimeResidual (Gv v)) := by
  apply le_antisymm
  · exact le_perfectCore_of_perfect (Lv_le_oThree h1222 F hH hv hβ (Lv_le_Gv L v))
      (perfectCore_perfect _)
  · have h5 : oThreePrimeResidual (Subgroup.normalizer (L : Set G)) = L :=
      (h1261 G T L V F hH).2.2.2.2.1
    have hle : oThreePrimeResidual (Gv v) ≤ L ⊓ Gv v := by
      refine le_inf ?_ ((Subgroup.closure_le _).2 fun x hx => hx.1)
      rw [← h5]
      exact Subgroup.closure_mono fun x hx => ⟨hGv hx.1, hx.2⟩
    exact le_perfectCore_of_perfect ((perfectCore_le _).trans hle) (perfectCore_perfect _)

theorem Lu_eq (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hw : WtTwo F v) (hGv : Gv v ≤ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ Delta F v) : Lv L u = perfectCore (oThreePrimeResidual (Gv u)) := by
  obtain ⟨l, hl, rfl⟩ := exists_conj_eq_of_mem_Delta h1222 hH hv hβ (Or.inl hw) hu
  rw [Lv_conj hl, Lv_eq h1222 h1261 F hH hv hβ hGv, map_perfectCore,
    map_conj_oThreePrimeResidual, map_conj_Gv]

theorem iSup_Lv_eq (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {v : G}
    (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) :
    (⨆ u ∈ Delta F v, Lv L u) = L := by
  classical
  set K := ⨆ u ∈ Delta F v, Lv L u with hK
  have hKL : K ≤ L := iSup₂_le fun u _ => Lv_le_L L u
  have hA8 : alternatingGroup (Fin 8) ≤ (K.subgroupOf L).map (psiP F hH) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    obtain ⟨a, ha, b, hb, hab, hca, hcb⟩ := exists_fix_two hc
    obtain ⟨u, huΔ, hu, hβu⟩ := exists_mem_Delta h1222 F hH hv hβ ha hb hab
    obtain ⟨y, hy, hyc⟩ := exists_Lu h1222 F hH hv hβ hu hab hβu hc.mem_alternatingGroup hca hcb
    exact ⟨y, (le_iSup₂_of_le u huΔ le_rfl : Lv L u ≤ K) hy, hyc⟩
  have hCN : L ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    refine mem_normalizer_biSup fun u huΔ => ?_
    obtain ⟨hu, -⟩ := huΔ
    have hxu : x ∈ L ⊓ Gv u := ⟨hx.1, by
      show x ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx.2 u hu).symm⟩
    exact normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hxu)
  have hdec : ∀ x ∈ L, x ∈ K ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := hA8 (psiP_mem F hH ⟨x, hx⟩)
    have hk' : (k : G) ∈ K := hk
    have hq : S126L19a.psi F hH (k⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact Subtype.ext hkx
    have hqC := (S126L19a.psi_eq_one_iff F hH _).1 hq
    have e : x = (k : G) * ((k : G)⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hk' ⟨L.mul_mem (L.inv_mem k.2) hx, hqC⟩
  have hLN : L ≤ Subgroup.normalizer (K : Set G) := fun x hx =>
    (sup_le Subgroup.le_normalizer hCN) (hdec x hx)
  have hnorm : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLN
  exact hH.hyp.faithful.2.1 K hKL hnorm fun x hx =>
    two_pow_mem_of_mem_sup (isPGroup_CL h1222 hH) hCN (hdec x hx)

theorem mem_M_of_normalizer (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hw : WtTwo F v) (hGv : Gv v ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hgV : g ∈ Subgroup.normalizer (Vv L V v : Set G))
    (hgL : g ∈ Subgroup.normalizer (Lv L v : Set G)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hgΔ := perm_Delta_of_normalizer h1222 hH hv hβ hgV hgL
  have hLu := fun u (hu : u ∈ Delta F v) => Lu_eq h1222 h1261 F hH hv hβ hw hGv hu
  have hgLu : ∀ u ∈ Delta F v,
      (Lv L u).map (MulAut.conj g).toMonoidHom = Lv L (g * u * g⁻¹) := by
    intro u hu
    rw [hLu u hu, hLu _ (hgΔ u hu), map_perfectCore, map_conj_oThreePrimeResidual, map_conj_Gv]
  rw [← iSup_Lv_eq h1222 F hH hv hβ]
  set K := ⨆ u ∈ Delta F v, Lv L u with hK
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rw [hK, Subgroup.map_iSup]
    refine iSup_le fun u => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hu => ?_
    rw [hgLu u hu]
    exact le_iSup₂_of_le (g * u * g⁻¹) (hgΔ u hu) le_rfl
  refine (Subgroup.mem_normalizer_iff_map_conj_eq).2 (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [IsMulCommutative ↥V] in
theorem Tv_le_normalizer_Lv' (hH : Hyp126 G T L V) (v : G) :
    Tv T v ≤ Subgroup.normalizer (Lv L v : Set G) := fun _t ht =>
  normalizer_le_normalizer_perfectCore _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hH.hyp.normalizes ht.1, Subgroup.le_normalizer ht.2⟩)

theorem Vv_eq_comm (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hJ : ¬ thompsonJ T ≤ Qv T V) :
    Vv L V v = ⁅quasithinOmegaOneCenter (pCoreOf 2 (Lv L v ⊔ Tv T v)), Lv L v⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (Lv L v ⊔ Tv T v) with hRdef
  obtain ⟨-, hVe⟩ := V_facts h1222 hH
  have hTvL := Tv_le_normalizer_Lv' hH v
  have hXL : Lv L v ⊔ Tv T v ≤ Subgroup.normalizer (Lv L v : Set G) :=
    sup_le Subgroup.le_normalizer hTvL
  have hXR : Lv L v ⊔ Tv T v ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
  have hXLT : Lv L v ⊔ Tv T v ≤ L ⊔ T := sup_le ((Lv_le_L L v).trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hQN : L ⊔ T ≤ Subgroup.normalizer (Qv T V : Set G) := LT_le_normalizer_Qv h1222 hH
  have hQ2 : IsPGroup 2 (Qv T V) := hH.hyp.sylow.1.to_le inf_le_left
  have hPQ : pCoreOf 2 (Lv L v) ≤ Qv T V := by
    rw [Qv_eq h1222 hH]
    exact le_inf ((pCoreOf_le 2 _).trans ((Lv_le_L L v).trans le_sup_left))
      (pCoreOf_Lv_le h1222 F hH hv hβ)
  have hLR : Lv L v ⊓ R ≤ pCoreOf 2 (Lv L v) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, hXR (Subgroup.mem_sup_left hy)⟩)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have hcomm : ∀ r ∈ R, ∀ l ∈ Lv L v, l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 (Lv L v) := by
    intro r hr l hl
    refine hLR ⟨?_, ?_⟩
    · have h1 : r * l⁻¹ * r⁻¹ ∈ Lv L v :=
        (Subgroup.mem_normalizer_iff.1 (hXL (pCoreOf_le 2 _ hr)) _).1 ((Lv L v).inv_mem hl)
      have e : l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) := by group
      rw [e]
      exact (Lv L v).mul_mem hl h1
    · exact R.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXR (Subgroup.mem_sup_left hl)) r).1 hr)
        (R.inv_mem hr)
  have hQR : Qv T V ≤ R :=
    le_pCoreOf_of_le_normalizer 2 (fun x hx => Subgroup.mem_sup_right ⟨hx.1, Qv_le_Gv hv hx⟩)
      (hXLT.trans hQN) hQ2
  have hRL : ∀ r ∈ R, ∀ l ∈ Lv L v, r * l * r⁻¹ * l⁻¹ ∈ Qv T V := by
    intro r hr l hl
    have h1 := hcomm r hr l⁻¹ ((Lv L v).inv_mem hl)
    have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hl) _).1 h1
    have e : r * l * r⁻¹ * l⁻¹ = l * (l⁻¹ * r * l⁻¹⁻¹ * r⁻¹) * l⁻¹ := by group
    rw [e]
    exact hPQ h2
  refine le_antisymm ?_ (S126VK.comm_omega_le_Vv h1222 h1261 F hH hJ v hQR hRL)
  have hTvS : IsSylowTwoOf (Tv T v) (Lv L v ⊔ Tv T v) :=
    A4.isSylowTwoOf_mono (isSylowTwoOf_Tv h1222 F hH hv hβ) le_sup_right
      (sup_le (le_inf ((Lv_le_L L v).trans le_sup_left) (Lv_le_Gv L v))
        (inf_le_inf_right _ le_sup_right))
  have hRT : R ≤ Tv T v := pCoreOf_two_le_of_sylowIn hTvS.1 hTvS.2.1 hTvS.2.2
  have hTvV : Tv T v ≤ Subgroup.normalizer (Vv L V v : Set G) :=
    MS93.le_normalizer_commutator_of
      (inf_le_left.trans (S126L19b.T_le_normalizer_V h1222 hH)) hTvL
  have hPR : pCoreOf 2 (Lv L v) ≤ R :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (hXL.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hVR : Vv L V v ≤ quasithinOmegaOneCenter R := by
    intro x hx
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨hPR (Vv_le_pCoreOf h1222 hH hv hx), ?_,
      hVe.2 x (Vv_le_V hH v hx)⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrT := hRT hr
    have hrsec : r ∈ centralizerSection (Tv T v) (Lv L v) (pCoreOf 2 (Lv L v)) :=
      ⟨hrT, hTvL hrT, normalizer_le_normalizer_pCoreOf 2 _ (hTvL hrT), fun l hl =>
        hcomm r hr l hl⟩
    exact Subgroup.mem_centralizer_iff.1
      (mem_centralizer_Vv h1222 hH hv hβ hrsec (hTvV hrT)) x hx |>.symm
  exact (Vv_le_comm h1222 hH hv).trans (Subgroup.commutator_mono hVR le_rfl)

omit [IsMulCommutative ↥V] in
theorem normalizer_L_le' (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨-, -, hMV, -⟩ := hall V hyp.irrPlus
  exact hMV.resolve_right hZ

theorem mem_centralizer_z0 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (E : S126FE.Frame126E F)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) : m * ((z0 E : ↥V) : G) * m⁻¹ = z0 E := by
  have hMV := normalizer_L_le' h1222 hH hZ
  obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH hm (hMV hm)
  have hmem : m * ((z0 E : ↥V) : G) * m⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 (hMV hm) _).1 (z0 E).2
  have h1 := E.act m hm (hMV hm) σ hσ (z0 E) ⟨_, hmem⟩ rfl
  rw [gamma_z0, S126FE.coreAct_eOm, ← gamma_z0 E] at h1
  exact congrArg Subtype.val (E.γ.injective h1)

theorem ew_conj (hH : Hyp126 G T L V) {F : Frame126 T L V} (E : S126FE.Frame126E F) {m : G}
    (hmL : m ∈ Subgroup.normalizer (L : Set G)) (hmV : m ∈ Subgroup.normalizer (V : Set G))
    (u : ↥V) :
    ew E ⟨m * u * m⁻¹, (Subgroup.mem_normalizer_iff.1 hmV u).1 u.2⟩ = ew E u := by
  obtain ⟨σ, hσ⟩ := S126N.exists_actsAs F hH hmL hmV
  rw [ew, ew, E.act m hmL hmV σ hσ u ⟨_, (Subgroup.mem_normalizer_iff.1 hmV u).1 u.2⟩ rfl,
    coreAct_coe, wt_permAct]

theorem Gv_mul_z0 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (E : S126FE.Frame126E F)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {v : G}
    (hGv : Gv v ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g * v * g⁻¹ = v * ((z0 E : ↥V) : G)) : Gv (v * ((z0 E : ↥V) : G)) = Gv v := by
  have hle : Gv v ≤ Gv (v * ((z0 E : ↥V) : G)) := by
    intro x hx
    have h1 : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    have h2 := mem_centralizer_z0 h1222 F E hH hZ (hGv hx)
    have h2' : x * ((z0 E : ↥V) : G) = (z0 E : G) * x := by
      calc x * ((z0 E : ↥V) : G) = x * (z0 E : G) * x⁻¹ * x := by group
        _ = (z0 E : G) * x := by rw [h2]
    show x ∈ Subgroup.centralizer ({v * ((z0 E : ↥V) : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (v * ((z0 E : ↥V) : G)) = x * v * (z0 E : G) := by group
      _ = v * (x * (z0 E : G)) := by rw [h1]; group
      _ = v * ((z0 E : G) * x) := by rw [h2']
      _ = v * (z0 E : G) * x := by group
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [← hg, ← map_conj_Gv, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mem_normalizer_Tv (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {v : G} (hv : v ∈ V) (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1))
    (hGv : Gv v ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g ∈ Subgroup.normalizer (Gv v : Set G)) :
    ∃ h ∈ Gv v, h⁻¹ * g ∈ Subgroup.normalizer (Tv T v : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTv := isSylowTwoOf_Tv_Mv h1222 F hH hv hβ
  rw [inf_eq_right.2 hGv] at hTv
  have hTv' : IsSylowIn 2 (Tv T v) (Gv v) := ⟨hTv.1, hTv.2.1, hTv.2.2⟩
  obtain ⟨h, hh, hiff⟩ := Ch1Sec3.exists_conj_of_isSylowIn hTv' (Ch1Sec3.isSylowIn_map_conj hTv' hg)
  refine ⟨h, hh, ?_⟩
  have hle : (Tv T v).map (MulAut.conj (h⁻¹ * g)).toMonoidHom ≤ Tv T v := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : g * t * g⁻¹ ∈ (Tv T v).map (MulAut.conj g).toMonoidHom :=
      ⟨t, ht, by simp [MulAut.conj_apply]⟩
    have h2 := (hiff _).1 h1
    have e : (MulAut.conj (h⁻¹ * g)).toMonoidHom t = h⁻¹ * (g * t * g⁻¹) * h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact h2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])

theorem false_of_conj_z0 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1)
    (F : Frame126 T L V) (E : S126FE.Frame126E F) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {v : G} (hv : v ∈ V)
    (hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1)) (hw : ew E ⟨v, hv⟩ = 2)
    (hGv : Gv v ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g * v * g⁻¹ = v * ((z0 E : ↥V) : G)) : False := by
  have hMV := normalizer_L_le' h1222 hH hZ
  have hGvz := Gv_mul_z0 h1222 F E hH hZ hGv hg
  have hgH : g ∈ Subgroup.normalizer (Gv v : Set G) := by
    have e : (Gv v).map (MulAut.conj g).toMonoidHom = Gv v := by rw [map_conj_Gv, hg, hGvz]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 e
  obtain ⟨h, hh, hT⟩ := exists_mem_normalizer_Tv h1222 F hH hv hβ hGv hgH
  set g' := h⁻¹ * g with hg'def
  have hhz : h * (v * ((z0 E : ↥V) : G)) = (v * (z0 E : G)) * h := by
    have hh' : h ∈ Gv (v * ((z0 E : ↥V) : G)) := hGvz ▸ hh
    exact Subgroup.mem_centralizer_singleton_iff.1 hh'
  have hg'v : g' * v * g'⁻¹ = v * ((z0 E : ↥V) : G) := by
    calc g' * v * g'⁻¹ = h⁻¹ * (g * v * g⁻¹) * h := by rw [hg'def]; group
      _ = h⁻¹ * ((v * (z0 E : G)) * h) := by rw [hg]; group
      _ = h⁻¹ * (h * (v * (z0 E : G))) := by rw [← hhz]
      _ = v * (z0 E : G) := by group
  have hg'H : g' ∈ Subgroup.normalizer (Gv v : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hh)) hgH
  have hg'M : g' ∈ Subgroup.normalizer (L : Set G) := by
    by_cases hJ : thompsonJ T ≤ Qv T V
    · have hQTv : Qv T V ≤ Tv T v := fun x hx => ⟨hx.1, Qv_le_Gv hv hx⟩
      have h1 : thompsonJ T = thompsonJ (Qv T V) := (B6.thompsonJ_eq_of_le hJ inf_le_left).symm
      have h2 : thompsonJ T = thompsonJ (Tv T v) :=
        (B6.thompsonJ_eq_of_le (hJ.trans hQTv) inf_le_left).symm
      apply normalizer_JQ_le h331 h1222 hH
      rw [← h1, h2]
      exact normalizer_le_normalizer_thompsonJ _ hT
    · have hgL : g' ∈ Subgroup.normalizer (Lv L v : Set G) := by
        rw [Lv_eq h1222 h1261 F hH hv hβ hGv]
        exact normalizer_le_normalizer_perfectCore _
          (le_normalizer_oThreePrimeResidual (le_refl _) hg'H)
      have hgV : g' ∈ Subgroup.normalizer (Vv L V v : Set G) := by
        rw [Vv_eq_comm h1222 h1261 F hH hv hβ hJ]
        have hgX : g' ∈ Subgroup.normalizer ((Lv L v ⊔ Tv T v : Subgroup G) : Set G) :=
          Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hgL, hT⟩
        have hgR := normalizer_le_normalizer_pCoreOf 2 _ hgX
        have hgΩ := S126VK.normalizer_le_normalizer_omega _ hgR
        exact MS93.le_normalizer_commutator_of (M := Subgroup.zpowers g')
          (Subgroup.zpowers_le.2 hgΩ) (Subgroup.zpowers_le.2 hgL) (Subgroup.mem_zpowers g')
      exact mem_M_of_normalizer h1222 h1261 F hH hv hβ ⟨E, hv, hw⟩ hGv hgV hgL
  have h1 := ew_conj hH E hg'M (hMV hg'M) ⟨v, hv⟩
  have h2 : (⟨g' * v * g'⁻¹, (Subgroup.mem_normalizer_iff.1 (hMV hg'M) v).1 hv⟩ : ↥V) =
      ⟨v, hv⟩ * z0 E := Subtype.ext hg'v
  rw [h2, ew_mul_z0, hw] at h1
  omega

end S126NF

theorem noFuse1261926_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) :
    NoFuse1261926 := by
  intro G _ _ T L V _ F hH v z g hvn hCv hz hz1 hg
  classical
  obtain ⟨hv, hn⟩ := hvn
  have hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := fun h =>
    hz1 (by rw [h, Subgroup.mem_bot] at hz; exact hz)
  obtain ⟨E⟩ := S126FE.exists_frame126E h1222 F hH hZ
  have hzz : z = ((z0 E : ↥V) : G) := by
    have hβz : F.β ⟨z, hz.1⟩ = 1 := (F.β_ker _).2 hz.2
    rw [E.β_eq, S126FE.mk_eq_one_iff] at hβz
    rcases hβz with h1 | h1
    · exact absurd (congrArg Subtype.val (E.γ.injective (h1.trans (map_one _).symm))) hz1
    · exact congrArg Subtype.val (E.γ.injective (h1.trans (gamma_z0 E).symm))
  subst hzz
  have key : ∀ (u : G) (hu : u ∈ V), ew E ⟨u, hu⟩ = 2 →
      Gv u ≤ Subgroup.normalizer (L : Set G) →
      ∀ g : G, g * u * g⁻¹ = u * ((z0 E : ↥V) : G) → False := by
    intro u hu hwu hGu g hg
    set u₀ : ↥V := E.γ.symm (pe 0 1) with hu₀def
    have hγ₀ : E.γ u₀ = pe 0 1 := MulEquiv.apply_symm_apply _ _
    have hw₀ : ew E u₀ = 2 := by
      rw [ew, hγ₀]
      exact S126L20a.wt_pe (by decide)
    have hβ₀ : F.β u₀ = QuotientGroup.mk (pe 0 1) := by rw [E.β_eq, hγ₀]
    obtain ⟨l, hlL, hl⟩ := exists_L_conj E (show ew E ⟨u, hu⟩ = ew E u₀ by rw [hwu, hw₀])
    have hlz : l * ((z0 E : ↥V) : G) * l⁻¹ = z0 E := by
      have h1 : l * ((z0 E : ↥V) : G) = z0 E * l :=
        Subgroup.mem_centralizer_iff.1 (z0_mem E) l hlL
      rw [h1]
      group
    have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
    refine S126NF.false_of_conj_z0 h331 h1222 h1261 F E hH hZ u₀.2 hβ₀ hw₀ ?_ (g := l * g * l⁻¹) ?_
    · rw [← hl, ← map_conj_Gv]
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlM (hGu hx)) (Subgroup.inv_mem _ hlM)
    · calc l * g * l⁻¹ * (u₀ : G) * (l * g * l⁻¹)⁻¹
          = l * (g * (l⁻¹ * (u₀ : G) * l) * g⁻¹) * l⁻¹ := by group
        _ = l * (g * u * g⁻¹) * l⁻¹ := by rw [← hl]; group
        _ = l * (u * ((z0 E : ↥V) : G)) * l⁻¹ := by rw [hg]
        _ = (l * u * l⁻¹) * (l * ((z0 E : ↥V) : G) * l⁻¹) := by group
        _ = (u₀ : G) * ((z0 E : ↥V) : G) := by rw [hl, hlz]
  rcases ew_of_nonsing E hn with h2 | h6
  · exact key v hv h2 hCv g hg
  ·
    have hGvz := S126NF.Gv_mul_z0 h1222 F E hH hZ hCv hg
    have hvz : v * ((z0 E : ↥V) : G) ∈ V := V.mul_mem hv (z0 E).2
    refine key (v * ((z0 E : ↥V) : G)) hvz ?_ (hGvz ▸ hCv) g⁻¹ ?_
    · have e : (⟨v * ((z0 E : ↥V) : G), hvz⟩ : ↥V) = ⟨v, hv⟩ * z0 E := rfl
      rw [e, ew_mul_z0, h6]
    · have hzz := z0_sq E
      calc g⁻¹ * (v * ((z0 E : ↥V) : G)) * g⁻¹⁻¹ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hg]; group
        _ = v := by group
        _ = v * ((z0 E : ↥V) : G) * ((z0 E : ↥V) : G) := by rw [mul_assoc, hzz, mul_one]

end CFSG.Quasithin.H13
