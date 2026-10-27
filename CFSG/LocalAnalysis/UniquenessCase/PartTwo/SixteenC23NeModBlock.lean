module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeAlg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeModMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_barSub_perfect {Y V : Subgroup G} {hV : IsElemAbelian 2 V}
    {K : Subgroup G} (hK : ⁅K, K⁆ = K) (hKs : K ≤ stabTil Y V) :
    ⁅barSub Y V hV K, barSub Y V hV K⁆ = barSub Y V hV K := by
  let ψ : ↥K →* MulAut (Vtil Y V hV) := (actTil Y V hV).comp (Subgroup.inclusion hKs)
  have hrange : ψ.range = barSub Y V hV K := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨Subgroup.inclusion hKs k, ?_, rfl⟩
      simpa using k.2
    · rintro ⟨g, hg, hgφ⟩
      refine ⟨⟨(g : G), hg⟩, ?_⟩
      show actTil Y V hV (Subgroup.inclusion hKs ⟨(g : G), hg⟩) = φ
      rw [← hgφ, show Subgroup.inclusion hKs ⟨(g : G), hg⟩ = g from Subtype.ext rfl]
  have hperfK : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  haveI : Group.IsPerfect (⊤ : Subgroup ↥K) := Group.IsPerfect.top_iff.2 hperfK
  have hperf : Group.IsPerfect ↥ψ.range := by
    have hmap := Group.IsPerfect.map (f := ψ) (H := ⊤)
    rw [Subgroup.map_top] at hmap
    exact hmap
  have hperf_eq : ⁅ψ.range, ψ.range⁆ = ψ.range := Subgroup.isPerfect_iff.1 hperf
  rw [← hrange]
  exact hperf_eq

private theorem c23ne_map_imgTil {Y V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {g : G}
    (hg₀ : g ∈ stabTil V₀ V) (hgY : g ∈ stabTil Y V) :
    (imgTil Y V hV V₀).map (actTil Y V hV ⟨g, hgY⟩).toMonoidHom = imgTil Y V hV V₀ := by
  apply le_antisymm
  · rintro q ⟨q₀, hq₀, rfl⟩
    obtain ⟨x, hxV₀, rfl⟩ := (mem_imgTil Y V hV V₀ q₀).1 hq₀
    change (actTil Y V hV ⟨g, hgY⟩) (mkTil Y V hV x) ∈ imgTil Y V hV V₀
    rw [actTil_mk, mem_imgTil]
    refine ⟨actStab Y V hV ⟨g, hgY⟩ x, ?_, rfl⟩
    rw [actStab_apply_val]
    exact (Subgroup.mem_normalizer_iff.1 hg₀.2 x.val).1 hxV₀
  · intro q hq
    have hgY' : g⁻¹ ∈ stabTil Y V := (stabTil Y V).inv_mem hgY
    have hg₀' : g⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem hg₀
    have hmemq : actTil Y V hV ⟨g⁻¹, hgY'⟩ q ∈ imgTil Y V hV V₀ := by
      obtain ⟨x, hxV₀, rfl⟩ := (mem_imgTil Y V hV V₀ q).1 hq
      change (actTil Y V hV ⟨g⁻¹, hgY'⟩) (mkTil Y V hV x) ∈ imgTil Y V hV V₀
      rw [actTil_mk, mem_imgTil]
      refine ⟨actStab Y V hV ⟨g⁻¹, hgY'⟩ x, ?_, rfl⟩
      rw [actStab_apply_val]
      simpa using (Subgroup.mem_normalizer_iff''.1 hg₀.2 x.val).1 hxV₀
    refine Subgroup.mem_map.2 ⟨actTil Y V hV ⟨g⁻¹, hgY'⟩ q, hmemq, ?_⟩
    have h2 : actTil Y V hV ⟨g⁻¹, hgY'⟩ = (actTil Y V hV ⟨g, hgY⟩)⁻¹ := by
      rw [← map_inv (actTil Y V hV) ⟨g, hgY⟩]
      rfl
    rw [h2]
    exact MulEquiv.apply_symm_apply (actTil Y V hV ⟨g, hgY⟩) q

private theorem c23ne_pBlock_sup_gen {V₀ V Y : Subgroup G} {hV : IsElemAbelian 2 V}
    {W₁ W₂ : Subgroup (Vtil V₀ V hV)} (hsup : W₁ ⊔ W₂ = ⊤) (hYle : Y ≤ V₀) :
    c23nePBlock Y V₀ V hV hYle W₁ ⊔ c23nePBlock Y V₀ V hV hYle W₂ = ⊤ := by
  rw [eq_top_iff]
  intro q _
  have hqsup : c23neProj Y V₀ V hV hYle q ∈ W₁ ⊔ W₂ := by
    rw [hsup]; trivial
  obtain ⟨w₁, hw₁, w₂, hw₂, hq_eq⟩ := Subgroup.mem_sup.1 hqsup
  obtain ⟨q₁, hq₁⟩ := c23neProj_surjective hV hYle w₁
  obtain ⟨q₂, hq₂⟩ := c23neProj_surjective hV hYle w₂
  have hz : q * (q₁ * q₂)⁻¹ ∈ imgTil Y V hV V₀ := by
    rw [← c23neProj_ker hV hYle, MonoidHom.mem_ker, map_mul, map_inv, map_mul, hq₁, hq₂,
      hq_eq, mul_inv_cancel]
  have hq_eq2 : (q₁ * q₂) * (q * (q₁ * q₂)⁻¹) = q := by
    rw [← mul_assoc, mul_comm (q₁ * q₂) q, mul_assoc, mul_inv_cancel, mul_one]
  rw [show q = (q₁ * q₂) * (q * (q₁ * q₂)⁻¹) from hq_eq2.symm]
  refine Subgroup.mul_mem _ ?_ ?_
  · exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (by rw [c23ne_mem_pBlock_iff, hq₁]; exact hw₁))
      (Subgroup.mem_sup_right (by rw [c23ne_mem_pBlock_iff, hq₂]; exact hw₂))
  · exact Subgroup.mem_sup_left (c23ne_ker_le_pBlock hV hYle W₁ hz)

private theorem c23ne_conj_mem_preTil {Y V : Subgroup G} {hV : IsElemAbelian 2 V}
    {K : Subgroup G} (hKs : K ≤ stabTil Y V) {Cn : Subgroup (Vtil Y V hV)}
    (hCninv : ∀ a ∈ barSub Y V hV K, ∀ y ∈ Cn, a y ∈ Cn) :
    ∀ k ∈ K, ∀ c ∈ preTil Y V hV Cn, k * c * k⁻¹ ∈ preTil Y V hV Cn := by
  intro k hk c hc
  have hkY : k ∈ stabTil Y V := hKs hk
  have hcV : c ∈ V := preTil_le Y V hV Cn hc
  have hcCn : mkTil Y V hV (IntMod.mk hV ⟨c, hcV⟩) ∈ Cn :=
    (mem_preTil_iff_of_mem Y V hV Cn hcV).1 hc
  have hact : actTil Y V hV ⟨k, hkY⟩ (mkTil Y V hV (IntMod.mk hV ⟨c, hcV⟩)) ∈ Cn :=
    hCninv _ (actTil_mem_barSub Y V hV hk hkY) _ hcCn
  have hy : mkTil Y V hV (actStab Y V hV ⟨k, hkY⟩ (IntMod.mk hV ⟨c, hcV⟩)) ∈ Cn := by
    rwa [actTil_mk Y V hV ⟨k, hkY⟩ (IntMod.mk hV ⟨c, hcV⟩)] at hact
  have hval : (actStab Y V hV ⟨k, hkY⟩ (IntMod.mk hV ⟨c, hcV⟩)).val = k * c * k⁻¹ :=
    actStab_apply_val Y V hV ⟨k, hkY⟩ (IntMod.mk hV ⟨c, hcV⟩)
  rw [← hval]
  exact (mem_preTil_iff_of_mem Y V hV Cn
    (actStab Y V hV ⟨k, hkY⟩ (IntMod.mk hV ⟨c, hcV⟩)).val_mem).2 hy

private theorem c23ne_cross_fix_one {Y V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {K : Subgroup G} {W : Subgroup (Vtil V₀ V hV)} {A : Subgroup (MulAut (Vtil V₀ V hV))}
    (hWfix : ∀ a ∈ A, ∀ y ∈ W, a y = y) (hYle : Y ≤ V₀) (hKbar : barSub V₀ V hV K = A)
    (hKperf : ⁅K, K⁆ = K) (hKs : K ≤ stabTil Y V)
    (hequiv : ∃ ρ : ↥(barSub Y V hV K) ≃* ↥(barSub V₀ V hV K),
      ∀ (a : ↥(barSub Y V hV K)) (q : Vtil Y V hV),
        c23neProj Y V₀ V hV hYle ((a : MulAut (Vtil Y V hV)) q) =
          ((ρ a : ↥(barSub V₀ V hV K)) : MulAut (Vtil V₀ V hV))
            (c23neProj Y V₀ V hV hYle q))
    (hZfix : imgTil Y V hV V₀ ≤ fixV (barSub Y V hV K)) :
    ∀ k ∈ barSub Y V hV K, ∀ p ∈ c23nePBlock Y V₀ V hV hYle W,
      (k : MulAut (Vtil Y V hV)) p = p := by
  refine c23ne_cross_centralizes (K := barSub Y V hV K)
    (P := c23nePBlock Y V₀ V hV hYle W) (Z := imgTil Y V hV V₀)
    (c23ne_barSub_perfect hKperf hKs) ?_ ?_
  · intro k' hk' p' hp'
    obtain ⟨ρ, hρ⟩ := hequiv
    have hprojp' : c23neProj Y V₀ V hV hYle p' ∈ W :=
      (c23ne_mem_pBlock_iff hV hYle _ p').1 hp'
    have h1 : c23neProj Y V₀ V hV hYle (k' p') = c23neProj Y V₀ V hV hYle p' := by
      rw [hρ ⟨k', hk'⟩ p']
      exact hWfix _ (hKbar ▸ (ρ ⟨k', hk'⟩).2) _ hprojp'
    rw [← c23neProj_ker hV hYle, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  · intro k' hk' z hz
    exact hZfix hz k' hk'

private theorem c23ne_split_of_complement_gen {D : Data G} {V₀ V L Y : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : G} {K₁ K₂ : Subgroup G}
    (hctx : C23NeCtx D V₀ V L hV x K₁ K₂) (hMstab : D.M ≤ stabTil V₀ V) (hV₀V : V₀ ≤ V)
    (hYle : Y ≤ V₀) (hYstab : D.M ≤ stabTil Y V)
    (hK₁M : K₁ ≤ D.M) (hK₂M : K₂ ≤ D.M)
    (hcross₁ : ∀ k ∈ barSub Y V hV K₂,
        ∀ p ∈ c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV L), k p = p)
    (hcross₂ : ∀ k ∈ barSub Y V hV K₁,
        ∀ p ∈ c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV (conjSubgroup L x)), k p = p)
    (htransport : barSub Y V hV K₂ =
        (barSub Y V hV K₁).map (MulAut.conj (actTil Y V hV ⟨x, hYstab hctx.hxM⟩)⁻¹).toMonoidHom ∧
      c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV (conjSubgroup L x)) =
        (c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV L)).map
          (actTil Y V hV ⟨x, hYstab hctx.hxM⟩)⁻¹.toMonoidHom)
    (hsupBlocks : c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV L) ⊔
        c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV (conjSubgroup L x)) = ⊤)
    (hc : ∃ C : Subgroup (Vtil Y V hV),
      C ≤ c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV L) ∧
      C ⊓ imgTil Y V hV V₀ = ⊥ ∧
      C ⊔ imgTil Y V hV V₀ = c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV L) ∧
      ∀ a ∈ barSub Y V hV K₁, ∀ c ∈ C, (a : MulAut (Vtil Y V hV)) c ∈ C) :
    C23NeSplit V₀ V Y (K₁ ⊔ K₂) := by
  set Z : Subgroup (Vtil Y V hV) := imgTil Y V hV V₀ with hZ
  set P₁ : Subgroup (Vtil Y V hV) :=
    c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV L) with hP₁
  set P₂ : Subgroup (Vtil Y V hV) :=
    c23nePBlock Y V₀ V hV hYle (wTil V₀ V hV (conjSubgroup L x)) with hP₂
  set φ : MulAut (Vtil Y V hV) := actTil Y V hV ⟨x, hYstab hctx.hxM⟩ with hφ
  obtain ⟨C₁, hC₁P, hC₁Zinf, hC₁Zsup, hC₁inv⟩ := hc
  obtain ⟨hK₂', hP₂'⟩ := htransport
  let C₂ : Subgroup (Vtil Y V hV) := C₁.map φ⁻¹.toMonoidHom
  let Cn : Subgroup (Vtil Y V hV) := C₁ ⊔ C₂
  have hC₂P : C₂ ≤ P₂ := by
    change C₁.map φ⁻¹.toMonoidHom ≤ P₂
    rw [hP₂']
    exact Subgroup.map_mono hC₁P
  have hC₂inv : ∀ a ∈ barSub Y V hV K₂, ∀ c ∈ C₂, a c ∈ C₂ := by
    intro a ha c hc
    rw [hK₂'] at ha
    obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.1 ha
    change c ∈ C₁.map φ⁻¹.toMonoidHom at hc
    obtain ⟨c₁, hc₁, rfl⟩ := Subgroup.mem_map.1 hc
    refine Subgroup.mem_map.2 ⟨a₁ c₁, hC₁inv a₁ ha₁ c₁ hc₁, ?_⟩
    change φ⁻¹ (a₁ c₁) = ((MulAut.conj φ⁻¹) a₁) (φ⁻¹ c₁)
    simp only [MulAut.conj_apply, MulAut.mul_apply, inv_inv, MulAut.apply_inv_self]
  have hfix₁₂ : ∀ a ∈ barSub Y V hV K₂, ∀ c ∈ C₁, a c = c := by
    intro a ha c hc
    exact hcross₁ a ha c (hC₁P hc)
  have hfix₂₁ : ∀ a ∈ barSub Y V hV K₁, ∀ c ∈ C₂, a c = c := by
    intro a ha c hc
    change c ∈ C₁.map φ⁻¹.toMonoidHom at hc
    obtain ⟨c₁, hc₁, rfl⟩ := Subgroup.mem_map.1 hc
    exact hcross₂ a ha (φ⁻¹ c₁) (hC₂P (Subgroup.mem_map.2 ⟨c₁, hc₁, rfl⟩))
  have hZφ : Z.map φ.toMonoidHom = Z := by
    rw [hZ, hφ]
    exact c23ne_map_imgTil hV (hMstab hctx.hxM) (hYstab hctx.hxM)
  have hZφinv : Z.map φ⁻¹.toMonoidHom = Z := by
    have h := congrArg (fun S : Subgroup (Vtil Y V hV) => S.map φ⁻¹.toMonoidHom) hZφ
    rw [Subgroup.map_map] at h
    have hcomp : φ⁻¹.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext q
      show φ⁻¹ (φ q) = q
      rw [MulAut.inv_apply]
      exact MulEquiv.symm_apply_apply φ q
    rw [hcomp, Subgroup.map_id] at h
    exact h.symm
  have hC₂Zinf : C₂ ⊓ Z = ⊥ := by
    change C₁.map φ⁻¹.toMonoidHom ⊓ Z = ⊥
    rw [← hZφinv, ← Subgroup.map_inf C₁ Z φ⁻¹.toMonoidHom (φ⁻¹).injective, hC₁Zinf,
      Subgroup.map_bot]
  have hC₂Zsup : C₂ ⊔ Z = P₂ := by
    change C₁.map φ⁻¹.toMonoidHom ⊔ Z = P₂
    rw [← hZφinv, ← Subgroup.map_sup, hC₁Zsup, ← hP₂']
  have hCnZinf : Cn ⊓ Z = ⊥ := by
    apply le_antisymm _ bot_le
    intro u hu
    obtain ⟨huCn, huZ⟩ := Subgroup.mem_inf.1 hu
    change u ∈ C₁ ⊔ C₂ at huCn
    obtain ⟨c₁, hc₁, c₂, hc₂, hu_eq⟩ := Subgroup.mem_sup.1 huCn
    have hproj_u : c23neProj Y V₀ V hV hYle u = 1 := by
      rw [hZ, ← c23neProj_ker hV hYle] at huZ
      exact MonoidHom.mem_ker.1 huZ
    have hsum : c23neProj Y V₀ V hV hYle c₁ * c23neProj Y V₀ V hV hYle c₂ = 1 := by
      rw [← map_mul, hu_eq]; exact hproj_u
    have hpc₁eq : c23neProj Y V₀ V hV hYle c₁ =
        (c23neProj Y V₀ V hV hYle c₂)⁻¹ := by
      calc c23neProj Y V₀ V hV hYle c₁
          = c23neProj Y V₀ V hV hYle c₁ * c23neProj Y V₀ V hV hYle c₂ *
              (c23neProj Y V₀ V hV hYle c₂)⁻¹ := by group
        _ = 1 * (c23neProj Y V₀ V hV hYle c₂)⁻¹ := by rw [hsum]
        _ = (c23neProj Y V₀ V hV hYle c₂)⁻¹ := one_mul _
    have hpc₁ : c23neProj Y V₀ V hV hYle c₁ ∈ wTil V₀ V hV L :=
      (c23ne_mem_pBlock_iff hV hYle _ c₁).1 (hC₁P hc₁)
    have hpc₂ : c23neProj Y V₀ V hV hYle c₂ ∈ wTil V₀ V hV (conjSubgroup L x) :=
      (c23ne_mem_pBlock_iff hV hYle _ c₂).1 (hC₂P hc₂)
    have hpc₁inf : c23neProj Y V₀ V hV hYle c₁ ∈
        wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) :=
      ⟨hpc₁, by rw [hpc₁eq]; exact (wTil V₀ V hV (conjSubgroup L x)).inv_mem hpc₂⟩
    rw [hctx.core.inf_eq, Subgroup.mem_bot] at hpc₁inf
    have hc₁Z : c₁ ∈ Z := by
      rw [hZ, ← c23neProj_ker hV hYle, MonoidHom.mem_ker]
      exact hpc₁inf
    have hc₁bot : c₁ = 1 := by
      have h : c₁ ∈ (⊥ : Subgroup (Vtil Y V hV)) := by
        rw [← hC₁Zinf]; exact ⟨hc₁, hc₁Z⟩
      exact Subgroup.mem_bot.1 h
    rw [hc₁bot, one_mul] at hu_eq
    have hc₂Z : c₂ ∈ Z := by rw [hu_eq]; exact huZ
    have hc₂bot : c₂ = 1 := by
      have h : c₂ ∈ (⊥ : Subgroup (Vtil Y V hV)) := by
        rw [← hC₂Zinf]; exact ⟨hc₂, hc₂Z⟩
      exact Subgroup.mem_bot.1 h
    exact Subgroup.mem_bot.2 (by rw [← hu_eq, hc₂bot])
  have hCnZsup : Cn ⊔ Z = ⊤ := by
    change C₁ ⊔ C₂ ⊔ Z = ⊤
    calc C₁ ⊔ C₂ ⊔ Z = (C₁ ⊔ Z) ⊔ (C₂ ⊔ Z) := by ac_rfl
      _ = P₁ ⊔ P₂ := by rw [hC₁Zsup, hC₂Zsup]
      _ = ⊤ := hsupBlocks
  have hCninv₁ : ∀ a ∈ barSub Y V hV K₁, ∀ y ∈ Cn, a y ∈ Cn := by
    intro a ha y hy
    change y ∈ C₁ ⊔ C₂ at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (hC₁inv a ha y₁ hy₁))
      (Subgroup.mem_sup_right (by rw [hfix₂₁ a ha y₂ hy₂]; exact hy₂))
  have hCninv₂ : ∀ a ∈ barSub Y V hV K₂, ∀ y ∈ Cn, a y ∈ Cn := by
    intro a ha y hy
    change y ∈ C₁ ⊔ C₂ at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup.1 hy
    rw [map_mul]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (by rw [hfix₁₂ a ha y₁ hy₁]; exact hy₁))
      (Subgroup.mem_sup_right (hC₂inv a ha y₂ hy₂))
  have hYleC : Y ≤ preTil Y V hV Cn := by
    intro y hy
    have hyV : y ∈ V := hV₀V (hYle hy)
    rw [mem_preTil_iff_of_mem Y V hV Cn hyV]
    have h1 : mkTil Y V hV (IntMod.mk hV ⟨y, hyV⟩) = mkTil Y V hV (1 : IntMod V hV) := by
      rw [mkTil_eq_iff]
      change y * (1 : IntMod V hV).val⁻¹ ∈ Y
      simpa using hy
    rw [h1, map_one]
    exact Cn.one_mem
  have hCleV : preTil Y V hV Cn ≤ V := preTil_le Y V hV Cn
  have hCinf : preTil Y V hV Cn ⊓ V₀ = Y := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvC, hvV₀⟩ := Subgroup.mem_inf.1 hv
      have hvV : v ∈ V := preTil_le Y V hV Cn hvC
      have hmk : mkTil Y V hV (IntMod.mk hV ⟨v, hvV⟩) ∈ Cn :=
        (mem_preTil_iff_of_mem Y V hV Cn hvV).1 hvC
      have hmkZ : mkTil Y V hV (IntMod.mk hV ⟨v, hvV⟩) ∈ Z := by
        rw [hZ, mem_imgTil]
        exact ⟨IntMod.mk hV ⟨v, hvV⟩, hvV₀, rfl⟩
      have hbot : mkTil Y V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
          (⊥ : Subgroup (Vtil Y V hV)) := by
        rw [← hCnZinf]; exact ⟨hmk, hmkZ⟩
      have hmk1 : mkTil Y V hV (IntMod.mk hV ⟨v, hvV⟩) = 1 := Subgroup.mem_bot.1 hbot
      have h1 : mkTil Y V hV (IntMod.mk hV ⟨v, hvV⟩) = mkTil Y V hV (1 : IntMod V hV) := by
        rw [hmk1, map_one]
      rw [mkTil_eq_iff] at h1
      have hval : (IntMod.mk hV ⟨v, hvV⟩).val = v := rfl
      rw [hval, IntMod.val_one] at h1
      simpa using h1
    · exact le_inf hYleC hYle
  have hCsup : preTil Y V hV Cn ⊔ V₀ = V := by
    apply le_antisymm
    · exact sup_le hCleV hV₀V
    · intro v hv
      have hmk : mkTil Y V hV (IntMod.mk hV ⟨v, hv⟩) ∈ Cn ⊔ Z := by
        rw [hCnZsup]; trivial
      obtain ⟨c, hcCn, z, hzZ, hcz⟩ := Subgroup.mem_sup.1 hmk
      obtain ⟨c'', hc''mk⟩ := mkTil_surjective Y V hV c
      have hc''C : c''.val ∈ preTil Y V hV Cn :=
        (mem_preTil Y V hV Cn).2 ⟨c'', rfl, hc''mk ▸ hcCn⟩
      rw [hZ] at hzZ
      obtain ⟨z', hz'V₀, hz'eq⟩ := (mem_imgTil Y V hV V₀ z).1 hzZ
      have heq : mkTil Y V hV (IntMod.mk hV ⟨v, hv⟩) = mkTil Y V hV (c'' * z') := by
        rw [← hcz, ← hc''mk, ← hz'eq, map_mul]
      rw [mkTil_eq_iff] at heq
      have hyV₀ : v * (c'' * z').val⁻¹ ∈ V₀ := hYle heq
      have hv_prod : c''.val * z'.val * (v * (c'' * z').val⁻¹) = v := by
        change (c'' * z').val * (v * (c'' * z').val⁻¹) = v
        haveI := hV.1
        have hcomm : (c'' * z').val * v = v * (c'' * z').val := by
          have := mul_comm' (⟨(c'' * z').val, (c'' * z').val_mem⟩ : ↥V) (⟨v, hv⟩ : ↥V)
          simpa using congrArg Subtype.val this
        rw [← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [← hv_prod]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
      · exact Subgroup.mem_sup_left hc''C
      · exact Subgroup.mem_sup_right hz'V₀
      · exact Subgroup.mem_sup_right hyV₀
  have hinv : ∀ k ∈ K₁ ⊔ K₂, ∀ c ∈ preTil Y V hV Cn, k * c * k⁻¹ ∈ preTil Y V hV Cn := by
    have hnorm₁ : K₁ ≤ Subgroup.normalizer (preTil Y V hV Cn : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro c
      constructor
      · intro hc
        exact c23ne_conj_mem_preTil (fun k hk => hYstab (hK₁M hk)) hCninv₁ k hk c hc
      · intro hc
        have hkc := c23ne_conj_mem_preTil (fun k hk => hYstab (hK₁M hk)) hCninv₁
          k⁻¹ (K₁.inv_mem hk) (k * c * k⁻¹) hc
        have h1 : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
        rwa [h1] at hkc
    have hnorm₂ : K₂ ≤ Subgroup.normalizer (preTil Y V hV Cn : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro c
      constructor
      · intro hc
        exact c23ne_conj_mem_preTil (fun k hk => hYstab (hK₂M hk)) hCninv₂ k hk c hc
      · intro hc
        have hkc := c23ne_conj_mem_preTil (fun k hk => hYstab (hK₂M hk)) hCninv₂
          k⁻¹ (K₂.inv_mem hk) (k * c * k⁻¹) hc
        have h1 : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
        rwa [h1] at hkc
    have hnorm : K₁ ⊔ K₂ ≤ Subgroup.normalizer (preTil Y V hV Cn : Set G) := sup_le hnorm₁ hnorm₂
    intro k hk c hc
    exact (Subgroup.mem_normalizer_iff.1 (hnorm hk) c).1 hc
  exact ⟨preTil Y V hV Cn, hYleC, hCleV, hCinf, hCsup, hinv⟩

theorem c23ne_pBlock_fix_eq {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊓
        fixV (barSub (c23neY V K₁ K₂) V hV K₁) = imgTil (c23neY V K₁ K₂) V hV V₀ := by
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal h.ctx.mem₁.1
  have hK₁₀ : K₁ ≤ centralizer (V₀ : Set G) := le_sup_left.trans h.ctx.cent₀
  apply le_antisymm
  · intro p hp
    obtain ⟨hpP, hpfix⟩ := Subgroup.mem_inf.1 hp
    have hprojp : c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le p ∈ wTil V₀ V hV L :=
      (c23ne_mem_pBlock_iff hV h.Y_le _ p).1 hpP
    obtain ⟨ρ, hρ⟩ := c23ne_equiv_bar h.ctx h.stab h.Y_le h.Y_norm rfl hK₁M le_sup_left
    have hfix : c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le p ∈
        fixV (barSub V₀ V hV L) := by
      rw [mem_fixV]
      intro b hb
      rw [← h.ctx.bar₁] at hb
      obtain ⟨a, haeq⟩ := ρ.surjective ⟨b, hb⟩
      have h1 := hρ a p
      rw [mem_fixV.1 hpfix a a.2, haeq] at h1
      exact h1.symm
    have hmem : c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le p ∈
        wTil V₀ V hV L ⊓ fixV (barSub V₀ V hV L) := ⟨hprojp, hfix⟩
    rw [c23ne_fix_eq_bot_of_natQuot h.nat, Subgroup.mem_bot] at hmem
    rw [← c23neProj_ker hV h.Y_le, MonoidHom.mem_ker]
    exact hmem
  · intro p hp
    exact Subgroup.mem_inf.2 ⟨c23ne_ker_le_pBlock hV h.Y_le _ hp,
      c23ne_imgTil_le_fixV hV hK₁₀ hp⟩

theorem c23ne_cross_fix {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    (∀ k ∈ barSub (c23neY V K₁ K₂) V hV K₂,
        ∀ p ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L),
          (k : MulAut (Vtil (c23neY V K₁ K₂) V hV)) p = p) ∧
      (∀ k ∈ barSub (c23neY V K₁ K₂) V hV K₁,
        ∀ p ∈ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le
          (wTil V₀ V hV (conjSubgroup L x)),
          (k : MulAut (Vtil (c23neY V K₁ K₂) V hV)) p = p) := by
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal h.ctx.mem₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal h.ctx.mem₂.1
  have hK₁s : K₁ ≤ stabTil (c23neY V K₁ K₂) V := hK₁M.trans h.stabY
  have hK₂s : K₂ ≤ stabTil (c23neY V K₁ K₂) V := hK₂M.trans h.stabY
  constructor
  · refine c23ne_cross_fix_one (K := K₂) (W := wTil V₀ V hV L)
      (A := barSub V₀ V hV (conjSubgroup L x)) h.ctx.core.triv₂ h.Y_le h.ctx.bar₂
      h.ctx.mem₂.2.1 hK₂s ?_ ?_
    · exact c23ne_equiv_bar h.ctx h.stab h.Y_le h.Y_norm rfl hK₂M le_sup_right
    · exact c23ne_imgTil_le_fixV hV (le_sup_right.trans h.ctx.cent₀)
  · refine c23ne_cross_fix_one (K := K₁) (W := wTil V₀ V hV (conjSubgroup L x))
      (A := barSub V₀ V hV L) h.ctx.core.triv₁ h.Y_le h.ctx.bar₁
      h.ctx.mem₁.2.1 hK₁s ?_ ?_
    · exact c23ne_equiv_bar h.ctx h.stab h.Y_le h.Y_norm rfl hK₁M le_sup_left
    · exact c23ne_imgTil_le_fixV hV (le_sup_left.trans h.ctx.cent₀)

theorem c23ne_split_of_complement {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : G} {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂)
    (hc : ∃ C : Subgroup (Vtil (c23neY V K₁ K₂) V hV),
      C ≤ c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ∧
      C ⊓ imgTil (c23neY V K₁ K₂) V hV V₀ = ⊥ ∧
      C ⊔ imgTil (c23neY V K₁ K₂) V hV V₀ =
        c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ∧
      ∀ a ∈ barSub (c23neY V K₁ K₂) V hV K₁,
        ∀ c ∈ C, (a : MulAut (Vtil (c23neY V K₁ K₂) V hV)) c ∈ C) :
    C23NeSplit V₀ V (c23neY V K₁ K₂) (K₁ ⊔ K₂) :=
  c23ne_split_of_complement_gen h.ctx h.stab h.pf.le h.Y_le h.stabY
    (uc22p22a_le_of_isSubnormal h.ctx.mem₁.1) (uc22p22a_le_of_isSubnormal h.ctx.mem₂.1)
    (c23ne_cross_fix h).1 (c23ne_cross_fix h).2
    (c23ne_transport h.stab h.ctx h.Y_le h.stabY)
    (c23ne_pBlock_sup_gen h.ctx.core.sup_eq h.Y_le) hc

theorem c23ne_pBlock_nat {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    Nonempty (NatQuot3 (barSub (c23neY V K₁ K₂) V hV K₁)
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L))
      (imgTil (c23neY V K₁ K₂) V hV V₀)) := by
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal h.ctx.mem₁.1
  obtain ⟨ρ, hρ⟩ := c23ne_equiv_bar h.ctx h.stab h.Y_le h.Y_norm rfl hK₁M le_sup_left
  have hnat : Nonempty (NatQuot3 (barSub V₀ V hV K₁) (wTil V₀ V hV L) ⊥) := by
    rw [h.ctx.bar₁]
    exact h.nat
  have h1 := c23ne_natQuot3_of_hom (c23neProj (c23neY V K₁ K₂) V₀ V hV h.Y_le)
    (c23neProj_surjective hV h.Y_le) ρ hρ hnat
  rwa [c23neProj_ker hV h.Y_le] at h1

theorem c23ne_pBlock_perf {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    commSub (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L))
        (barSub (c23neY V K₁ K₂) V hV K₁) =
      c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) := by
  by_contra hne
  obtain ⟨hle, hinf, hsup, hinv⟩ := c23ne_complement_of_proper (c23ne_pBlock_nat h)
    (c23ne_ker_le_pBlock hV h.Y_le (wTil V₀ V hV L)) (c23ne_card_imgTil h) hne
  exact h.nonsplit (c23ne_split_of_complement h ⟨_, hle, hinf, hsup, hinv⟩)

theorem c23ne_block₁ {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : G}
    {K₁ K₂ : Subgroup G} (h : C23NeNs D V₀ V L hV x K₁ K₂) :
    C23ABlock (barSub (c23neY V K₁ K₂) V hV K₁)
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L))
      (c23nePBlock (c23neY V K₁ K₂) V₀ V hV h.Y_le (wTil V₀ V hV L) ⊓
        fixV (barSub (c23neY V K₁ K₂) V hV K₁)) where
  nat := by
    rw [c23ne_pBlock_fix_eq h]
    exact c23ne_pBlock_nat h
  perf := c23ne_pBlock_perf h
  fix := rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
