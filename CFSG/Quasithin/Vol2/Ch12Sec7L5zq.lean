module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zp
public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31 CFSG.LargeExtraspecial Module
open scoped IsMulCommutative

theorem false_of_three_compl {G : Type*} [Group G] [Finite G] (S : Setting G) (hw : S.width = 3)
    {X Y Z : Submodule (ZMod 2) S.Qt} (hX : ∀ v ∈ X, S.q v = 0) (hY : ∀ v ∈ Y, S.q v = 0)
    (hZ : ∀ v ∈ Z, S.q v = 0) (hY3 : finrank (ZMod 2) Y = 3) (hZ3 : finrank (ZMod 2) Z = 3)
    (hX3 : finrank (ZMod 2) X = 3) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) : False := by
  classical
  have hdim : finrank (ZMod 2) S.Qt = 6 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hc : IsCompl X Y := (Submodule.isCompl_iff_disjoint X Y (by omega)).mpr hXY
  have hpol : ∀ {W : Submodule (ZMod 2) S.Qt}, (∀ v ∈ W, S.q v = 0) →
      ∀ a ∈ W, ∀ b ∈ W, QuadraticMap.polar S.q a b = 0 := by
    intro W hW a ha b hb
    rw [QuadraticMap.polar, hW _ (W.add_mem ha hb), hW a ha, hW b hb, sub_zero, sub_zero]
  set p₁ := X.projectionOnto Y hc with hp₁
  set p₂ := Y.projectionOnto X hc.symm with hp₂
  have hsum : ∀ v : S.Qt, ((p₁ v : ↥X) : S.Qt) + ((p₂ v : ↥Y) : S.Qt) = v := fun v =>
    Submodule.projection_add_projection_eq_self hc v
  have hinj : Function.Injective (p₂ ∘ₗ Z.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hwX : (w : S.Qt) ∈ X :=
      (Submodule.projectionOnto_apply_eq_zero_iff (x := (w : S.Qt)) hc.symm).mp hw
    have := hXZ.le_bot ⟨hwX, w.2⟩
    exact Subtype.ext (by simpa using this)
  have hsurj : Function.Surjective (p₂ ∘ₗ Z.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hZ3, hY3])).mp hinj
  let B : LinearMap.BilinForm (ZMod 2) ↥Z :=
    S.q.polarBilin.compl₁₂ (X.subtype ∘ₗ p₁ ∘ₗ Z.subtype) (Y.subtype ∘ₗ p₂ ∘ₗ Z.subtype)
  have hB : ∀ w w' : ↥Z, B w w' =
      QuadraticMap.polar S.q ((p₁ w : ↥X) : S.Qt) ((p₂ w' : ↥Y) : S.Qt) := fun _ _ => rfl
  have halt : B.IsAlt := by
    intro w
    rw [hB, QuadraticMap.polar, hsum, hZ _ w.2, hX _ (p₁ w).2, hY _ (p₂ w).2, sub_zero,
      sub_zero]
  have hnd : B.Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun w hw => ?_
    have hrad : ∀ v, QuadraticMap.polar S.q ((p₁ w : ↥X) : S.Qt) v = 0 := by
      intro v
      rw [← hsum v, QuadraticMap.polar_add_right]
      obtain ⟨w', hw'⟩ := hsurj (p₂ v)
      have h2 := hw w'
      rw [hB] at h2
      have hw'' : ((p₂ (w' : S.Qt) : ↥Y) : S.Qt) = ((p₂ v : ↥Y) : S.Qt) :=
        congrArg Subtype.val hw'
      rw [hw''] at h2
      rw [h2, hpol hX _ (p₁ w).2 _ (p₁ v).2, add_zero]
    have hp : ((p₁ w : ↥X) : S.Qt) = 0 := S.q_nondegenerate.1 _ fun v => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hrad v
    have hwY : (w : S.Qt) ∈ Y := by
      have : p₁ w = 0 := Subtype.ext hp
      exact (Submodule.projectionOnto_apply_eq_zero_iff hc).mp this
    have := hYZ.le_bot ⟨hwY, w.2⟩
    exact Subtype.ext (by simpa using this)
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank halt hnd
  omega

namespace Set714

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}

omit [Finite G] in
theorem map_conj_eq_iff {U : Subgroup G} {g : G} [Finite U] :
    U.map (MulAut.conj g).toMonoidHom = U ↔ g ∈ Subgroup.normalizer (U : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [← h]
      exact ⟨u, hu, rfl⟩
    · intro hu
      rw [← h] at hu
      obtain ⟨u', hu', hu'e⟩ := hu
      have e : u = u' := by
        have h1 : g * u' * g⁻¹ = g * u * g⁻¹ := hu'e
        exact (mul_left_cancel (mul_right_cancel h1)).symm
      rw [e]
      exact hu'
  · intro h
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp h u).mp hu
    · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]

theorem z_mem_map_conj (s : Set714 G T L V t z) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    z ∈ (U714 T L V z).map (MulAut.conj g).toMonoidHom :=
  ⟨z, s.z_mem_U, by
    show g * z * g⁻¹ = z
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hg), mul_inv_cancel_right]⟩

end Set714

namespace Set714.N3

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  {s : Set714 G T L V t z} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)
include hn

theorem map_conj_le_Qz {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    (U714 T L V z).map (MulAut.conj g).toMonoidHom ≤ s.Qz h1222 := by
  rintro _ ⟨u, hu, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hn.Gz_le_normalizer_Qz hg) u).mp (s.U_le_Qz hn hu)

theorem H_le_normalizer_map_conj
    {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    H714 T L V z ≤ Subgroup.normalizer
      ((U714 T L V z).map (MulAut.conj g).toMonoidHom : Set G) := by
  intro h hh
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := hx
  have hh' : g⁻¹ * h * g ∈ H714 T L V z := by
    have := (Subgroup.mem_normalizer_iff.mp (hn.Gz_le_normalizer_H
      (Subgroup.inv_mem _ hg)) h).mp hh
    simpa using this
  have hu' : (g⁻¹ * h * g) * u * (g⁻¹ * h * g)⁻¹ ∈ U714 T L V z :=
    (Subgroup.mem_normalizer_iff.mp (s.H_le_normalizer_U h1222 hh') u).mp hu
  refine ⟨_, hu', ?_⟩
  show g * ((g⁻¹ * h * g) * u * (g⁻¹ * h * g)⁻¹) * g⁻¹ = h * (g * u * g⁻¹) * h⁻¹
  group

theorem exists_conj_map {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) {x y : G}
    (hx : x ∈ (U714 T L V z).map (MulAut.conj g).toMonoidHom)
    (hy : y ∈ (U714 T L V z).map (MulAut.conj g).toMonoidHom)
    (hxz : x ∉ Subgroup.zpowers z) (hyz : y ∉ Subgroup.zpowers z) :
    ∃ h ∈ H714 T L V z, (h * x * h⁻¹)⁻¹ * y ∈ Subgroup.zpowers z := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨u', hu', rfl⟩ := hy
  have hgz : ∀ c ∈ Subgroup.zpowers z, g * c * g⁻¹ = c := fun c hc =>
    conj_eq_of_mem_zpowers hc hg
  have huz : u ∉ Subgroup.zpowers z := fun h => hxz (by
    show g * u * g⁻¹ ∈ _
    rw [hgz u h]
    exact h)
  have hu'z : u' ∉ Subgroup.zpowers z := fun h => hyz (by
    show g * u' * g⁻¹ ∈ _
    rw [hgz u' h]
    exact h)
  obtain ⟨h₀, hh₀, hk⟩ := hn.exists_conj hu hu' huz hu'z
  have hh : g * h₀ * g⁻¹ ∈ H714 T L V z :=
    (Subgroup.mem_normalizer_iff.mp (hn.Gz_le_normalizer_H hg) h₀).mp hh₀
  refine ⟨_, hh, ?_⟩
  show (g * h₀ * g⁻¹ * (g * u * g⁻¹) * (g * h₀ * g⁻¹)⁻¹)⁻¹ * (g * u' * g⁻¹) ∈ _
  have e : (g * h₀ * g⁻¹ * (g * u * g⁻¹) * (g * h₀ * g⁻¹)⁻¹)⁻¹ * (g * u' * g⁻¹) =
      g * ((h₀ * u * h₀⁻¹)⁻¹ * u') * g⁻¹ := by group
  rw [e, hgz _ hk]
  exact hk

theorem eq_of_mem_inf {g₁ g₂ : G}
    (hg₁ : g₁ ∈ Subgroup.centralizer ({z} : Set G))
    (hg₂ : g₂ ∈ Subgroup.centralizer ({z} : Set G)) {x : G}
    (hx₁ : x ∈ (U714 T L V z).map (MulAut.conj g₁).toMonoidHom)
    (hx₂ : x ∈ (U714 T L V z).map (MulAut.conj g₂).toMonoidHom)
    (hxz : x ∉ Subgroup.zpowers z) :
    (U714 T L V z).map (MulAut.conj g₁).toMonoidHom =
      (U714 T L V z).map (MulAut.conj g₂).toMonoidHom := by
  have hle : (U714 T L V z).map (MulAut.conj g₁).toMonoidHom ≤
      (U714 T L V z).map (MulAut.conj g₂).toMonoidHom := by
    intro y hy
    by_cases hyz : y ∈ Subgroup.zpowers z
    · exact Subgroup.zpowers_le_of_mem (s.z_mem_map_conj hg₂) hyz
    · obtain ⟨h, hh, hk⟩ := hn.exists_conj_map hg₁ hx₁ hy hxz hyz
      have e : y = (h * x * h⁻¹) * ((h * x * h⁻¹)⁻¹ * y) := by group
      rw [e]
      exact Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (hn.H_le_normalizer_map_conj hg₂ hh) x).mp hx₂)
        (Subgroup.zpowers_le_of_mem (s.z_mem_map_conj hg₂) hk)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulEquiv.injective _),
    Subgroup.card_map_of_injective (MulEquiv.injective _)]

theorem q_clSub_map_conj (g : G) :
    ∀ v ∈ hn.setting.clSub ((U714 T L V z).map (MulAut.conj g).toMonoidHom),
      hn.setting.q v = 0 := by
  intro v hv
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hv
  rw [hn.setting.q_cl_eq_zero_iff hxQ]
  obtain ⟨u, hu, rfl⟩ := hx
  show (g * u * g⁻¹) ^ 2 = 1
  rw [conj_pow, hn.sq_U u hu, mul_one, mul_inv_cancel]

theorem finrank_clSub_map_conj
    {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    finrank (ZMod 2) (hn.setting.clSub ((U714 T L V z).map (MulAut.conj g).toMonoidHom)) = 3 := by
  have hle : (U714 T L V z).map (MulAut.conj g).toMonoidHom ≤ hn.setting.QG := by
    rw [hn.setting_QG]
    exact hn.map_conj_le_Qz hg
  have h1 := hn.setting.card_clPre
    (hn.setting.clSub ((U714 T L V z).map (MulAut.conj g).toMonoidHom))
  rw [hn.setting.clPre_clSub hle (s.z_mem_map_conj hg), Subgroup.card_map_of_injective
    (MulEquiv.injective _), hn.card_U, hn.setting.card_submodule] at h1
  have h8 : 2 ^ finrank (ZMod 2) (hn.setting.clSub
      ((U714 T L V z).map (MulAut.conj g).toMonoidHom)) = 2 ^ 3 := by omega
  exact Nat.pow_right_injective le_rfl h8

theorem disjoint_clSub {g₁ g₂ : G}
    (hg₁ : g₁ ∈ Subgroup.centralizer ({z} : Set G))
    (hg₂ : g₂ ∈ Subgroup.centralizer ({z} : Set G))
    (hne : (U714 T L V z).map (MulAut.conj g₁).toMonoidHom ≠
      (U714 T L V z).map (MulAut.conj g₂).toMonoidHom) :
    Disjoint (hn.setting.clSub ((U714 T L V z).map (MulAut.conj g₁).toMonoidHom))
      (hn.setting.clSub ((U714 T L V z).map (MulAut.conj g₂).toMonoidHom)) := by
  rw [Submodule.disjoint_def]
  intro v hv1 hv2
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hv1
  obtain ⟨y, hy, hyQ, hyx⟩ := hn.setting.mem_clSub_iff.mp hv2
  have hxy : x ∈ (U714 T L V z).map (MulAut.conj g₂).toMonoidHom := by
    rcases (hn.setting.cl_eq_cl_iff hyQ hxQ).mp hyx with rfl | rfl
    · exact hy
    · exact Subgroup.mul_mem _ hy (s.z_mem_map_conj hg₂)
  by_contra hne0
  apply hne
  refine hn.eq_of_mem_inf hg₁ hg₂ hx hxy fun hxz => hne0 ?_
  rcases (Setting.mem_zpowers_iff_of_mul_self (s.z_mul_z)).mp hxz with rfl | rfl
  · exact hn.setting.cl_one
  · exact hn.setting.cl_z

theorem setting_width :
    hn.setting.width = 3 := by
  refine hn.setting.width_eq ?_
  show Nat.card ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))) = _
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (s.Qz_le_Gz h1222)).toEquiv, hn.card_Q]

theorem Gz_le_normalizer_U :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (U714 T L V z : Set G) := by
  have hy := s.setting.hyp.hyp
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set N := Subgroup.normalizer (U714 T L V z : Set G) with hN
  have hw := hn.setting_width
  have hone : (1 : G) ∈ Gz := Subgroup.one_mem _
  have hU1 : (U714 T L V z).map (MulAut.conj (1 : G)).toMonoidHom = U714 T L V z :=
    (map_conj_eq_iff (U := U714 T L V z)).mpr (Subgroup.one_mem _)
  by_contra hle
  obtain ⟨g₀, hg₀, hg₀N⟩ := Set.not_subset.mp hle
  have hkey : ∀ g ∈ Gz, g ∉ N → (U714 T L V z).map (MulAut.conj g).toMonoidHom =
      (U714 T L V z).map (MulAut.conj g₀).toMonoidHom := by
    intro g hg hgN
    by_contra hne
    have h1 : (U714 T L V z).map (MulAut.conj g).toMonoidHom ≠
        (U714 T L V z).map (MulAut.conj (1 : G)).toMonoidHom := by
      rw [hU1]
      exact fun h => hgN ((map_conj_eq_iff (U := U714 T L V z)).mp h)
    have h2 : (U714 T L V z).map (MulAut.conj g₀).toMonoidHom ≠
        (U714 T L V z).map (MulAut.conj (1 : G)).toMonoidHom := by
      rw [hU1]
      exact fun h => hg₀N ((map_conj_eq_iff (U := U714 T L V z)).mp h)
    exact false_of_three_compl hn.setting hw (hn.q_clSub_map_conj g)
      (hn.q_clSub_map_conj g₀) (hn.q_clSub_map_conj 1) (hn.finrank_clSub_map_conj hg₀)
      (hn.finrank_clSub_map_conj hone) (hn.finrank_clSub_map_conj hg)
      (hn.disjoint_clSub hg hg₀ hne) (hn.disjoint_clSub hg hone h1)
      (hn.disjoint_clSub hg₀ hone h2)
  have hmem : ∀ g ∈ Gz, g ∉ N → g₀⁻¹ * g ∈ N := by
    intro g hg hgN
    have h := hkey g hg hgN
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hgu : g * u * g⁻¹ ∈ (U714 T L V z).map (MulAut.conj g₀).toMonoidHom := by
      rw [← h]
      exact ⟨u, hu, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := hgu
    have hu'e' : g₀ * u' * g₀⁻¹ = g * u * g⁻¹ := hu'e
    have e : g₀⁻¹ * g * u * (g₀⁻¹ * g)⁻¹ = u' := by
      calc g₀⁻¹ * g * u * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * u * g⁻¹) * g₀ := by group
        _ = g₀⁻¹ * (g₀ * u' * g₀⁻¹) * g₀ := by rw [hu'e']
        _ = u' := by group
    rw [e]
    exact hu'
  have hidx : (Gz ⊓ N).relIndex Gz ≤ 2 := by
    have hsurj : Function.Surjective (fun b : Bool =>
        if b then (QuotientGroup.mk (⟨g₀, hg₀⟩ : ↥Gz) : ↥Gz ⧸ (Gz ⊓ N).subgroupOf Gz)
        else QuotientGroup.mk (1 : ↥Gz)) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      by_cases hgN : (g : G) ∈ N
      · refine ⟨false, ?_⟩
        show (QuotientGroup.mk (1 : ↥Gz) : ↥Gz ⧸ (Gz ⊓ N).subgroupOf Gz) = QuotientGroup.mk g
        rw [QuotientGroup.eq, inv_one, one_mul]
        exact ⟨g.2, hgN⟩
      · refine ⟨true, ?_⟩
        show (QuotientGroup.mk (⟨g₀, hg₀⟩ : ↥Gz) : ↥Gz ⧸ (Gz ⊓ N).subgroupOf Gz) =
          QuotientGroup.mk g
        rw [QuotientGroup.eq]
        exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀) g.2, hmem g g.2 hgN⟩
    have h := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
    exact h
  have hne1 : (Gz ⊓ N).relIndex Gz ≠ 1 := fun h1 =>
    hg₀N ((Subgroup.relIndex_eq_one.mp h1 hg₀).2)
  have hpos : (Gz ⊓ N).relIndex Gz ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (Gz ⊓ N) Gz
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥Gz)).ne h
  have h2 : (Gz ⊓ N).relIndex Gz = 2 := by omega
  have hTN₀ : T ≤ Gz ⊓ N := le_inf s.le_cent (s.U_le_T h1222).2
  have hrel := Subgroup.relIndex_mul_relIndex T (Gz ⊓ N) Gz hTN₀ inf_le_left
  rw [h2] at hrel
  apply hy.sylow.2
  have hdvd : T.relIndex Gz ∣ T.index := Subgroup.relIndex_dvd_index_of_le s.le_cent
  rw [← hrel] at hdvd
  exact (Dvd.intro_left _ rfl).trans hdvd

theorem Gz_eq_H :
    Subgroup.centralizer ({z} : Set G) = H714 T L V z := by
  have hGN := hn.Gz_le_normalizer_U
  have : IsMulCommutative ↥(U714 T L V z) := ⟨⟨fun a b => Subtype.ext (s.comm_U hn a.2 b.2)⟩⟩
  have hW : ∀ u : ↥(U714 T L V z), u ^ 2 = 1 := fun u => Subtype.ext (hn.sq_U u u.2)
  have hAut : Nat.card (MulAut ↥(U714 T L V z)) = 20160 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
      (fun a b : ↥(U714 T L V z) => mul_comm a b) hW
      (show Nat.card ↥(U714 T L V z) = 2 ^ 4 by rw [hn.card_U]; norm_num)
    rw [Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv, Matrix.card_GL_field,
      ZMod.card]
    simp [Fin.prod_univ_four]
  set zU : ↥(U714 T L V z) := ⟨z, s.z_mem_U⟩ with hzU
  have hz1 : zU ≠ 1 := fun h => s.ne_one (congrArg Subtype.val h)
  have horbit : MulAction.orbit (MulAut ↥(U714 T L V z)) zU = {u | u ≠ 1} := by
    ext u
    constructor
    · rintro ⟨φ, rfl⟩
      show φ zU ≠ 1
      intro h
      exact hz1 (φ.injective (h.trans (map_one φ).symm))
    · intro hu
      obtain ⟨φ, hφ⟩ := ElemAb.exists_mulAut_apply_eq hW hz1 hu
      exact ⟨φ, hφ⟩
  have hidx : (MulAction.stabilizer (MulAut ↥(U714 T L V z)) zU).index = 15 := by
    rw [MulAction.index_stabilizer, horbit,
      show {u : ↥(U714 T L V z) | u ≠ 1} = Set.univ \ {1} by ext; simp,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hn.card_U]
  have hstab : Nat.card ↥(MulAction.stabilizer (MulAut ↥(U714 T L V z)) zU) = 1344 := by
    have h := Subgroup.card_mul_index (MulAction.stabilizer (MulAut ↥(U714 T L V z)) zU)
    rw [hidx, hAut] at h
    omega
  set ψ : ↥(Subgroup.centralizer ({z} : Set G)) →* MulAut ↥(U714 T L V z) :=
    (Subgroup.normalizerMonoidHom (U714 T L V z)).comp (Subgroup.inclusion hGN) with hψdef
  have hψ : ∀ g u, ((ψ g u : ↥(U714 T L V z)) : G) = (g : G) * u * (g : G)⁻¹ := fun g u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ _ u
  have hrange : ψ.range ≤ MulAction.stabilizer (MulAut ↥(U714 T L V z)) zU := by
    rintro _ ⟨g, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show ((ψ g zU : ↥(U714 T L V z)) : G) = z
    rw [hψ]
    show (g : G) * z * (g : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_singleton_iff.mp g.2, mul_inv_cancel_right]
  have hker : Nat.card ↥ψ.ker ≤ 16 := by
    rw [← hn.card_U]
    refine Nat.card_le_card_of_injective (fun k => (⟨((k : ↥(Subgroup.centralizer
      ({z} : Set G))) : G), ?_⟩ : ↥(U714 T L V z))) ?_
    · refine hn.centralizer_U.le (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
      have hk := congrArg (fun φ : MulAut ↥(U714 T L V z) => ((φ ⟨u, hu⟩ :
        ↥(U714 T L V z)) : G)) (MonoidHom.mem_ker.mp k.2)
      simp only [MulAut.one_apply] at hk
      rw [hψ] at hk
      calc u * ((k : ↥(Subgroup.centralizer ({z} : Set G))) : G) =
          (k : G) * u * (k : G)⁻¹ * (k : G) := by rw [hk]
        _ = (k : G) * u := by group
    · intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext (Subtype.ext hab)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  have h2 : Nat.card ↥ψ.range ≤ 1344 := hstab ▸ Subgroup.card_le_of_le hrange
  have h3 : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) ≤ 2 ^ 10 * 21 := by
    rw [h1]
    calc Nat.card ↥ψ.range * Nat.card ↥ψ.ker ≤ 1344 * 16 := Nat.mul_le_mul h2 hker
      _ = 2 ^ 10 * 21 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge (s.H_le_Gz h1222) (by rw [hn.card_H]; exact h3)).symm

end Set714.N3

end CFSG.Quasithin.H13.S127.L715
