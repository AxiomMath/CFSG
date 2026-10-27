module

public import CFSG.Quasithin.H13.A5X1367c
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem isSylowTwoOf_Tv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) :
    IsSylowTwoOf S.Tv (Subgroup.centralizer ({S.v12} : Set G)) :=
  S.isSylowTwoOf_centralizer h1222 h517 S.v12_mem_V2 S.v12_not_mem_V1

theorem V1_le_omega_Tv : S.V1 ≤ quasithinOmegaOneCenter S.Tv := by
  have hzGv : S.z ∈ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (S.elemAbelian_V.1.is_comm.comm ⟨S.z, S.z_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩)
  have hzC : S.z ∈ Subgroup.centralizer ((S.Tv : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]
  rw [V1, Subgroup.zpowers_le]
  exact Subgroup.subset_closure
    ⟨Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨S.V_le_T S.z_mem_V, hzGv⟩, hzC⟩, S.z_sq⟩

theorem isTwoReducedIn_Uv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    IsTwoReducedIn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv := by
  have hsyl := S.isSylowTwoOf_Tv h1222 h517
  exact isTwoReducedIn_conjClosure_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv

theorem elemAbelian_Uv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    IsElemAbelian 2 S.Uv :=
  (S.isTwoReducedIn_Uv h1222 h517 hF).2.2.1

theorem pCoreOf_GvS (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot (S.isTwoReducedIn_Uv h1222 h517 hF)

theorem Uv_le_Tv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    S.Uv ≤ S.Tv := by
  have hsyl := S.isSylowTwoOf_Tv h1222 h517
  obtain ⟨hUc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv
  exact hUc.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl))

theorem pCoreOf_Gv_ne_bot (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) ≠ ⊥ := by
  have hsyl := S.isSylowTwoOf_Tv h1222 h517
  obtain ⟨hUc, -⟩ :=
    conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2 hF S.V1_le_omega_Tv
  intro h
  have hz : S.z ∈ pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) :=
    (hUc (S.z_mem_Uv)).1
  rw [h, Subgroup.mem_bot] at hz
  exact S.z_ne_one hz

theorem sqtkGroup_Gv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
  sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
    (S.pCoreOf_Gv_ne_bot h1222 h517 hF)

theorem isSylowTwoOf_TvS (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) :
    IsSylowTwoOf (autOn S.Tv S.Uv) (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) :=
  Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv h1222 h517) S.Gv_le_normalizer_Uv

theorem isFFStarOffender_of_mem (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {A : Subgroup G} (hA : IsFFOffender S.Tv S.Uv A) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
    IsFFStarOffender (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) (autOn A S.Uv) := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have hUT := S.Uv_le_Tv h1222 h517 hF
  have hTN : S.Tv ≤ Subgroup.normalizer (S.Uv : Set G) := S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv
  have h1 := offenderImages_isFFStarOffender hUe hUT hTN ⟨A, hA, rfl⟩
  exact ⟨h1.1.trans (S.autOn_le_GvS S.Tv_le_Gv), h1.2.1, h1.2.2.1, h1.2.2.2⟩

theorem conjAct_Uv_eq_one {g : G} (hgN : g ∈ Subgroup.normalizer (S.Uv : Set G))
    (hgC : g ∈ Subgroup.centralizer (S.Uv : Set G)) : conjAct S.Uv ⟨g, hgN⟩ = 1 := by
  ext u
  rw [coe_conjAct_apply', MulAut.one_apply]
  have h := Subgroup.mem_centralizer_iff.mp hgC (u : G) u.2
  show g * (u : G) * g⁻¹ = u
  rw [← h, mul_inv_cancel_right]

theorem autOn_thompsonJ_le_ffJ (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
    autOn (thompsonJ S.Tv) S.Uv ≤ ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) := by
  have : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
  set P : Subgroup G :=
    ((ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)).comap (conjAct S.Uv)).map
      (Subgroup.normalizer (S.Uv : Set G)).subtype with hP
  have hJP : thompsonJ S.Tv ≤ P := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (S.Uv : Set G) :=
      (hA.1.trans (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)) ha
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    show conjAct S.Uv ⟨a, haN⟩ ∈ ffJ _
    by_cases hAc : A ≤ Subgroup.centralizer (S.Uv : Set G)
    · rw [S.conjAct_Uv_eq_one haN (hAc ha)]
      exact Subgroup.one_mem _
    · have hoff := S.isFFStarOffender_of_mem h1222 h517 hF ⟨hA, hAc⟩
      have hle : autOn A S.Uv ≤ ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) :=
        le_iSup₂_of_le (f := fun B (_ : IsFFStarOffender
          (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) B) => B) (autOn A S.Uv) hoff le_rfl
      exact hle ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  intro x hx
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := hx
  obtain ⟨⟨g', hg'N⟩, hg'P, hg'g⟩ := hJP (Subgroup.mem_subgroupOf.mp hg)
  have : (⟨g', hg'N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) = ⟨g, hgN⟩ := Subtype.ext hg'g
  rw [← this]
  exact hg'P

theorem autOn_thompsonJ_ne_bot
    (hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (S.Uv : Set G)) :
    autOn (thompsonJ S.Tv) S.Uv ≠ ⊥ := by
  intro h
  apply hJ
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (S.Uv : Set G) :=
    ((B6.thompsonJ_le S.Tv).trans (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)) hg
  have h1 : conjAct S.Uv ⟨g, hgN⟩ ∈ autOn (thompsonJ S.Tv) S.Uv :=
    ⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h2 := congrArg (fun f : MulAut ↥S.Uv => ((f ⟨u, hu⟩ : ↥S.Uv) : G)) h1
  simp only [coe_conjAct_apply', MulAut.one_apply] at h2
  calc u * g = g * u * g⁻¹ * g := by rw [h2]
    _ = g * u := by group

theorem b56Cases_GvS (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h56 : AsB56) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (S.Uv : Set G)) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
    B56Case1 (ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) ∨
      B56Case2 (ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) ∨
      B56Case3 (ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) ∨
      B56Case4 (ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) ∨
      B56Case5 (ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)) := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hV : ∀ v : ↥S.Uv, v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hUe.2 _ v.2, Subgroup.coe_one])
  have hJ1 : ffJ (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) ≠ ⊥ := fun h =>
    S.autOn_thompsonJ_ne_bot hJ (le_bot_iff.1 (h ▸ S.autOn_thompsonJ_le_ffJ h1222 h517 hF))
  exact h56 ↥S.Uv hV _ hJ1 (InternalSec.b53Hyp_ffJ_autOn S.Gv_le_normalizer_Uv
    (S.sqtkGroup_Gv h1222 h517 hF) (S.pCoreOf_GvS h1222 h517 hF))

@[expose] noncomputable def JGv : Subgroup (MulAut ↥S.Uv) :=
  ⨆ (A : Subgroup G) (_ : IsFFOffender S.Tv S.Uv A) (g : MulAut ↥S.Uv)
    (_ : g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv), B6.conjSub g (autOn A S.Uv)

theorem conjSub_le_JGv {A : Subgroup G} (hA : IsFFOffender S.Tv S.Uv A) {g : MulAut ↥S.Uv}
    (hg : g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) :
    B6.conjSub g (autOn A S.Uv) ≤ S.JGv :=
  le_iSup₂_of_le (f := fun A (_ : IsFFOffender S.Tv S.Uv A) => ⨆ (g : MulAut ↥S.Uv)
    (_ : g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv),
      B6.conjSub g (autOn A S.Uv)) A hA (le_iSup₂_of_le (f := fun (g : MulAut ↥S.Uv)
        (_ : g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) =>
          B6.conjSub g (autOn A S.Uv)) g hg le_rfl)

theorem JGv_le_GvS : S.JGv ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv := by
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxG : x ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv :=
    S.autOn_le_GvS S.Tv_le_Gv ((show autOn A S.Uv ≤ autOn S.Tv S.Uv from by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := hy
      exact ⟨a, Subgroup.mem_subgroupOf.mpr (hA.1.1 (Subgroup.mem_subgroupOf.mp ha)), rfl⟩) hx)
  show g * x * g⁻¹ ∈ _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxG) (Subgroup.inv_mem _ hg)

theorem conjSub_JGv_le {h : MulAut ↥S.Uv}
    (hh : h ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) :
    B6.conjSub h S.JGv ≤ S.JGv := by
  unfold JGv
  simp only [OrderIso.map_iSup]
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  have e : B6.conjSub h (B6.conjSub g (autOn A S.Uv)) = B6.conjSub (h * g) (autOn A S.Uv) := by
    ext x
    simp only [B6.conjSub, MulEquiv.mapSubgroup_apply, Subgroup.mem_map]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [e]
  exact S.conjSub_le_JGv hA (Subgroup.mul_mem _ hh hg)

theorem GvS_le_normalizer_JGv :
    autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (S.JGv : Set (MulAut ↥S.Uv)) := by
  intro h hh
  have key : ∀ k ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, ∀ x ∈ S.JGv,
      k * x * k⁻¹ ∈ S.JGv := fun k hk x hx =>
    S.conjSub_JGv_le hk ⟨x, hx, by simp [MulAut.conj_apply]⟩
  refine B6.mem_normalizer_of_forall_mem (key h hh) fun x hx => ?_
  have := key h⁻¹ (Subgroup.inv_mem _ hh) x hx
  simpa using this

theorem autOn_thompsonJ_le_JGv : autOn (thompsonJ S.Tv) S.Uv ≤ S.JGv := by
  set P : Subgroup G := (S.JGv.comap (conjAct S.Uv)).map
      (Subgroup.normalizer (S.Uv : Set G)).subtype with hP
  have hJP : thompsonJ S.Tv ≤ P := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (S.Uv : Set G) :=
      (hA.1.trans (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)) ha
    refine ⟨⟨a, haN⟩, ?_, rfl⟩
    show conjAct S.Uv ⟨a, haN⟩ ∈ S.JGv
    by_cases hAc : A ≤ Subgroup.centralizer (S.Uv : Set G)
    · rw [S.conjAct_Uv_eq_one haN (hAc ha)]
      exact Subgroup.one_mem _
    · have h1 := S.conjSub_le_JGv ⟨hA, hAc⟩ (Subgroup.one_mem _)
      refine h1 ⟨conjAct S.Uv ⟨a, haN⟩, ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, ?_⟩
      simp
  intro x hx
  obtain ⟨⟨g, hgN⟩, hg, rfl⟩ := hx
  obtain ⟨⟨g', hg'N⟩, hg'P, hg'g⟩ := hJP (Subgroup.mem_subgroupOf.mp hg)
  have : (⟨g', hg'N⟩ : ↥(Subgroup.normalizer (S.Uv : Set G))) = ⟨g, hgN⟩ := Subtype.ext hg'g
  rw [← this]
  exact hg'P

theorem JGv_eq_ffJ (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
    S.JGv = ffJ S.JGv := by
  have : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
  refine le_antisymm ?_ (B6.ffJ_le _)
  refine iSup₂_le fun A hA => iSup₂_le fun g hg => ?_
  have h1 := S.isFFStarOffender_of_mem h1222 h517 hF hA
  have h2 := B6.isFFStarOffender_conjSub h1 hg
  have h3 := InternalSec.isFFStarOffender_of_le h2 (S.conjSub_le_JGv hA hg)
  exact le_iSup₂_of_le (f := fun B (_ : IsFFStarOffender S.JGv B) => B) _ h3 le_rfl

theorem pCoreOf_JGv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    pCoreOf 2 S.JGv = ⊥ := by
  have h := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 S.JGv
    (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) S.JGv_le_GvS
    ((Subgroup.normal_subgroupOf_iff_le_normalizer S.JGv_le_GvS).2 S.GvS_le_normalizer_JGv)
  rw [S.pCoreOf_GvS h1222 h517 hF] at h
  exact le_bot_iff.1 h

theorem b53Hyp_JGv (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
    B53Hyp S.JGv := by
  have : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
  set Y := Subgroup.centralizer ({S.v12} : Set G) with hY
  set X := autOn Y S.Uv with hX
  set J := S.JGv with hJ
  have hJX : J ≤ X := S.JGv_le_GvS
  have hYW : Y ≤ Subgroup.normalizer (S.Uv : Set G) := S.Gv_le_normalizer_Uv
  set ρ := InternalSec.autOnHom hYW with hρ
  set H : Subgroup ↥Y := (J.subgroupOf X).comap ρ with hH
  let f : ↥H →* ↥J :=
    { toFun := fun h => ⟨((ρ (h : ↥Y) : ↥X) : MulAut ↥S.Uv), h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨y, hy⟩ := InternalSec.autOnHom_surjective hYW ⟨j, hJX hj⟩
    refine ⟨⟨y, ?_⟩, ?_⟩
    · show ρ y ∈ J.subgroupOf X
      rw [Subgroup.mem_subgroupOf, hy]
      exact hj
    · apply Subtype.ext
      show ((ρ y : ↥X) : MulAut ↥S.Uv) = j
      rw [hy]
  refine ⟨S.pCoreOf_JGv h1222 h517 hF, S.JGv_eq_ffJ h1222 h517 hF, ↥H, inferInstance,
    inferInstance, f.ker, inferInstance,
    InternalSec.sqtkGroup_subgroup (S.sqtkGroup_Gv h1222 h517 hF) H,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

theorem JGv_ne_bot (hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (S.Uv : Set G)) :
    S.JGv ≠ ⊥ := fun h =>
  S.autOn_thompsonJ_ne_bot hJ (le_bot_iff.1 (h ▸ S.autOn_thompsonJ_le_JGv))

theorem b56Cases_JGv (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h56 : AsB56) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hJ : ¬ thompsonJ S.Tv ≤ Subgroup.centralizer (S.Uv : Set G)) :
    haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
    B56Case1 S.JGv ∨ B56Case2 S.JGv ∨ B56Case3 S.JGv ∨ B56Case4 S.JGv ∨ B56Case5 S.JGv := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hV : ∀ v : ↥S.Uv, v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hUe.2 _ v.2, Subgroup.coe_one])
  exact h56 ↥S.Uv hV _ (S.JGv_ne_bot hJ) (S.b53Hyp_JGv h1222 h517 hF)

end Setting

end CFSG.Quasithin.H13.A5
