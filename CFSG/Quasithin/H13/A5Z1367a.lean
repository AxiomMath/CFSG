module

public import CFSG.Quasithin.H13.A5X1367n
public import CFSG.Quasithin.H13.A5Y1367a

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

theorem autOn_map_conj {G : Type} [Group G] {U K : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (g : ↥(Subgroup.normalizer (U : Set G))) :
    autOn (K.map (MulAut.conj (g : G)).toMonoidHom) U =
      (autOn K U).map (MulAut.conj (conjAct U g)).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨x, hx, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨k, hk, hkx⟩ := hx
    have hkU : k ∈ Subgroup.normalizer (U : Set G) := hKU hk
    refine ⟨conjAct U ⟨k, hkU⟩, Setup.mem_autOn_iff.2 ⟨⟨k, hkU⟩, hk, rfl⟩, ?_⟩
    have e : x = g * ⟨k, hkU⟩ * g⁻¹ := Subtype.ext (by rw [← hkx]; rfl)
    show conjAct U g * conjAct U ⟨k, hkU⟩ * (conjAct U g)⁻¹ = conjAct U x
    rw [e, map_mul, map_mul, map_inv]
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Setup.mem_autOn_iff.1 hψ
    refine Setup.mem_autOn_iff.2 ⟨g * k * g⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    show conjAct U (g * k * g⁻¹) = conjAct U g * conjAct U k * (conjAct U g)⁻¹
    rw [map_mul, map_mul, map_inv]

theorem autOn_eq_bot_of_le_centralizer {G : Type} [Group G] {U X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer (U : Set G)) : autOn X U = ⊥ :=
  CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer hX

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem pCoreOf_Gv_le_centralizer_Uv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) ≤ Subgroup.centralizer (S.Uv : Set G) := by
  have hsyl := S.isSylowTwoOf_Tv h1222 h517
  obtain ⟨hUc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv
  rw [Subgroup.le_centralizer_iff]
  exact hUc.trans inf_le_right

theorem Tv_le_normalizer_of_autOn (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple ↥(autOn K S.Uv))
    (hT : autOn S.Tv S.Uv ≤
      Subgroup.normalizer ((autOn K S.Uv : Subgroup (MulAut ↥S.Uv)) : Set (MulAut ↥S.Uv))) :
    S.Tv ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have hO2 := S.pCoreOf_Gv_ne_bot h1222 h517 hF
  have hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G) := le_of_mem_cComp hK
  have hKU : K ≤ Subgroup.normalizer (S.Uv : Set G) := hKG.trans S.Gv_le_normalizer_Uv
  intro t ht
  have htG : t ∈ Subgroup.centralizer ({S.v12} : Set G) := S.Tv_le_Gv ht
  have htU : t ∈ Subgroup.normalizer (S.Uv : Set G) := S.Gv_le_normalizer_Uv htG
  set K' : Subgroup G := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : K' ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) := by
    have h := cComp_map_mulEquiv (MulAut.conj t) hK
    have hGv : (Subgroup.centralizer ({S.v12} : Set G)).map (MulAut.conj t).toMonoidHom =
        Subgroup.centralizer ({S.v12} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htG)
    rwa [hGv] at h
  have hK'U : K' ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (le_of_mem_cComp hK'c).trans S.Gv_le_normalizer_Uv
  have hstar : autOn K' S.Uv = autOn K S.Uv := by
    rw [hK', autOn_map_conj hKU ⟨t, htU⟩]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hT (Setup.mem_autOn_iff.2 ⟨⟨t, htU⟩, ht, rfl⟩))
  by_contra hne
  have hne' : K ≠ K' := fun h => hne (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  obtain ⟨h1, h2⟩ := Vol2Native.lemma_1_2_1_two hloc h37 hO2 hK hK'c hne'
  have hcomm : ⁅K, K'⁆ ≤ Subgroup.centralizer (S.Uv : Set G) :=
    (h1.trans h2).trans (S.pCoreOf_Gv_le_centralizer_Uv h1222 h517 hF)
  have hbot : ⁅autOn K S.Uv, autOn K S.Uv⁆ = ⊥ := by
    conv_lhs => rhs; rw [← hstar]
    rw [← autOn_commutator hKU hK'U]
    exact autOn_eq_bot_of_le_centralizer hcomm
  rw [S153L.comp_perfect_of_isQuasisimple hq] at hbot
  exact SBc3.ne_bot_of_isQuasisimple hq hbot

theorem isGoodComp_conj {Kb : Subgroup (MulAut ↥S.Uv)} (hgood : S.GoodComp Kb) {t : MulAut ↥S.Uv}
    (ht : t ∈ autOn S.Tv S.Uv) : S.GoodComp (B6.conjSub t Kb) := by
  have hTJ : autOn S.Tv S.Uv ≤
      Subgroup.normalizer ((autOn (thompsonJ S.Tv) S.Uv : Subgroup (MulAut ↥S.Uv)) :
        Set (MulAut ↥S.Uv)) :=
    autOn_le_normalizer_autOn
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ S.Tv))
  have hJt : (autOn (thompsonJ S.Tv) S.Uv).map (MulAut.conj t).toMonoidHom =
      autOn (thompsonJ S.Tv) S.Uv := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTJ ht)
  have hJinv : ∀ j ∈ autOn (thompsonJ S.Tv) S.Uv, t⁻¹ * j * t ∈ autOn (thompsonJ S.Tv) S.Uv :=
    fun j hj => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTJ ht)) j).mp hj
      rwa [inv_inv] at this
  have key : ∀ j ∈ autOn (thompsonJ S.Tv) S.Uv, ∀ x ∈ B6.conjSub t Kb,
      j * x * j⁻¹ ∈ B6.conjSub t Kb := by
    intro j hj x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hj' := hJinv j hj
    have hk' : (t⁻¹ * j * t) * k * (t⁻¹ * j * t)⁻¹ ∈ Kb :=
      (Subgroup.mem_normalizer_iff.mp (hgood.2.1 hj') k).mp hk
    refine ⟨(t⁻¹ * j * t) * k * (t⁻¹ * j * t)⁻¹, hk', ?_⟩
    show t * ((t⁻¹ * j * t) * k * (t⁻¹ * j * t)⁻¹) * t⁻¹ = j * (t * k * t⁻¹) * j⁻¹
    group
  refine ⟨S.isComponentOf_conj hgood.1 (S.autOn_le_GvS S.Tv_le_Gv ht), ?_, ?_⟩
  · intro j hj
    refine B6.mem_normalizer_of_forall_mem (key j hj) fun x hx => ?_
    have := key j⁻¹ (Subgroup.inv_mem _ hj) x hx
    rwa [inv_inv] at this
  · intro h
    apply hgood.2.2
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hj' : t * j * t⁻¹ ∈ autOn (thompsonJ S.Tv) S.Uv :=
      (Subgroup.mem_normalizer_iff.mp (hTJ ht) j).mp hj
    have hk' : t * k * t⁻¹ ∈ B6.conjSub t Kb := ⟨k, hk, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (h hj') _ hk'
    calc k * j = t⁻¹ * ((t * k * t⁻¹) * (t * j * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * j * t⁻¹) * (t * k * t⁻¹)) * t := by rw [h1]
      _ = j * k := by group

theorem goodComp_le_JGv {Kb : Subgroup (MulAut ↥S.Uv)} (hgood : S.GoodComp Kb) :
    Kb ≤ S.JGv := by
  have hq : CFSG.IsQuasisimple ↥Kb := B1Red.isQuasisimple_of_open hgood.1.2.2
  rw [← commutator_eq_self_of_qs hq hgood.2.1 hgood.2.2, Subgroup.commutator_le]
  intro k hk j hj
  have hkN := S.GvS_le_normalizer_JGv (hgood.1.1 hk)
  have hjJ := S.autOn_thompsonJ_le_JGv hj
  have e : ⁅k, j⁆ = (k * j * k⁻¹) * j⁻¹ := rfl
  rw [e]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hkN j).mp hjJ)
    (Subgroup.inv_mem _ hjJ)

end Setting

end CFSG.Quasithin.H13.A5
