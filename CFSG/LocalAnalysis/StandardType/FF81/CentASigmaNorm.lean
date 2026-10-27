module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.StandardType.FF81.CentAO2
import CFSG.LocalAnalysis.StandardType.FF81.CentANormUi
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelGen
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelAut
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelRootAut
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelUnip

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin CFSG.Open

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 m) (ZMod 2)}

private theorem caSigN_mem_liftSub_iff (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (g : GL (BlkIdx 1 m) (ZMod 2)) :
    g ∈ K ↔ ((φ.symm g : ↥Y) : G) ∈ liftSub φ K := by
  constructor
  · intro hg
    exact mem_liftSub.mpr ⟨(φ.symm g).2, by simpa using hg⟩
  · intro hg
    simpa using (mem_liftSub.mp hg).2

private theorem caSigN_liftSub_eq_iff {K K' : Subgroup (GL (BlkIdx 1 m) (ZMod 2))} :
    liftSub φ K = liftSub φ K' ↔ K = K' := by
  constructor
  · intro hK
    ext g
    rw [caSigN_mem_liftSub_iff (φ := φ) K g, caSigN_mem_liftSub_iff (φ := φ) K' g, hK]
  · rintro rfl
    rfl

private theorem caSigN_liftSub_map_conj_of_mem {K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))}
    {a : G} (ha : a ∈ Y) :
    (liftSub φ K).map (MulAut.conj a) =
      liftSub φ (K.map (MulAut.conj (φ ⟨a, ha⟩))) := by
  have h := liftSub_map_conj (φ := φ) K (φ ⟨a, ha⟩)
  rw [MulEquiv.symm_apply_apply] at h
  exact h.symm

private theorem caSigN_liftSub_normalizer_eq (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2)))
    (hNle : Subgroup.normalizer (liftSub φ K : Set G) ≤ Y) :
    liftSub φ (Subgroup.normalizer (K : Set (GL (BlkIdx 1 m) (ZMod 2)))) =
      Subgroup.normalizer (liftSub φ K : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxY, hxN⟩ := mem_liftSub.mp hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [caSigN_liftSub_map_conj_of_mem (φ := φ) (K := K) hxY]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN]
  · intro x hx
    have hxY : x ∈ Y := hNle hx
    refine mem_liftSub.mpr ⟨hxY, ?_⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply (caSigN_liftSub_eq_iff (φ := φ)).mp
    rw [← caSigN_liftSub_map_conj_of_mem (φ := φ) (K := K) hxY]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx

theorem exists_sigma_of_swap (hchar : IsCharTwoType G) (hS : CentASetting m Y L R b t φ) {h : G}
    (hh : h ∈ Subgroup.centralizer ({t} : Set G))
    (h12 : (liftSub φ (uOne m)).map (MulAut.conj h).toMonoidHom = liftSub φ (uTwo m))
    (h21 : (liftSub φ (uTwo m)).map (MulAut.conj h).toMonoidHom = liftSub φ (uOne m)) :
    ∃ σ ∈ Subgroup.centralizer ({t} : Set G), σ * σ = 1 ∧
      ∃ hσY : ∀ y ∈ Y, σ * y * σ⁻¹ ∈ Y,
        ∀ y : ↥Y, φ ⟨σ * (y : G) * σ⁻¹, hσY (y : G) y.2⟩ = sigmaStd m (φ y) := by
  have hm1 : 1 ≤ m := by
    rcases hS.m_cases with rfl | rfl <;> norm_num
  let N1 : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) := Subgroup.normalizer (uOne m : Set _)
  let N2 : Subgroup (GL (BlkIdx 1 m) (ZMod 2)) := Subgroup.normalizer (uTwo m : Set _)
  have hN1eq : liftSub φ N1 = Subgroup.normalizer (liftSub φ (uOne m) : Set G) :=
    caSigN_liftSub_normalizer_eq (φ := φ) (K := uOne m) (normalizer_liftSub_uOne_le hchar hS)
  have hN2eq : liftSub φ N2 = Subgroup.normalizer (liftSub φ (uTwo m) : Set G) :=
    caSigN_liftSub_normalizer_eq (φ := φ) (K := uTwo m) (normalizer_liftSub_uTwo_le hchar hS)
  have hYeq : Y = liftSub φ N1 ⊔ liftSub φ N2 := by
    calc
      Y = liftSub φ (⊤ : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) :=
        (liftSub_top (φ := φ)).symm
      _ = liftSub φ (N1 ⊔ N2) := by rw [← normalizer_uOne_sup_normalizer_uTwo hm1]
      _ = liftSub φ N1 ⊔ liftSub φ N2 := liftSub_sup N1 N2
  have hN1map : (liftSub φ N1).map (MulAut.conj h).toMonoidHom = liftSub φ N2 := by
    rw [hN1eq, Subgroup.map_equiv_normalizer_eq, h12, ← hN2eq]
  have hN2map : (liftSub φ N2).map (MulAut.conj h).toMonoidHom = liftSub φ N1 := by
    rw [hN2eq, Subgroup.map_equiv_normalizer_eq, h21, ← hN1eq]
  have hYmap : Y.map (MulAut.conj h).toMonoidHom = Y := by
    calc
      Y.map (MulAut.conj h).toMonoidHom =
          (liftSub φ N1 ⊔ liftSub φ N2).map (MulAut.conj h).toMonoidHom :=
        congrArg (fun T => T.map (MulAut.conj h).toMonoidHom) hYeq
      _ = (liftSub φ N1).map (MulAut.conj h).toMonoidHom ⊔
          (liftSub φ N2).map (MulAut.conj h).toMonoidHom := Subgroup.map_sup _ _ _
      _ = liftSub φ N2 ⊔ liftSub φ N1 := by rw [hN1map, hN2map]
      _ = liftSub φ N1 ⊔ liftSub φ N2 := sup_comm _ _
      _ = Y := hYeq.symm
  have hYmem : ∀ a ∈ Y, h * a * h⁻¹ ∈ Y := by
    intro a ha
    have hmem : h * a * h⁻¹ ∈ Y.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, by
        show (MulAut.conj h) a = h * a * h⁻¹
        rw [MulAut.conj_apply]⟩
    rwa [hYmap] at hmem
  have hYmap_inv : Y.map (MulAut.conj h⁻¹).toMonoidHom = Y := by
    conv_lhs => rw [← hYmap]
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id G := by
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hYmem_inv : ∀ a ∈ Y, h⁻¹ * a * h ∈ Y := by
    intro a ha
    have hmem : h⁻¹ * a * h ∈ Y.map (MulAut.conj h⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, by
        show (MulAut.conj h⁻¹) a = h⁻¹ * a * h
        rw [MulAut.conj_apply]
        group⟩
    rwa [hYmap_inv] at hmem
  let ch : MulAut ↥Y :=
    MulEquiv.mk'
      { toFun := fun a => ⟨h * (a : G) * h⁻¹, hYmem a a.2⟩
        invFun := fun a => ⟨h⁻¹ * (a : G) * h, hYmem_inv a a.2⟩
        left_inv := by
          intro a
          ext
          change h⁻¹ * (h * (a : G) * h⁻¹) * h = (a : G)
          group
        right_inv := by
          intro a
          ext
          change h * (h⁻¹ * (a : G) * h) * h⁻¹ = (a : G)
          group }
      (by
        intro a b
        ext
        change h * ((a : G) * (b : G)) * h⁻¹ =
          (h * (a : G) * h⁻¹) * (h * (b : G) * h⁻¹)
        group)
  let α : MulAut (GL (BlkIdx 1 m) (ZMod 2)) := φ.symm.trans (ch.trans φ)
  have hα_apply (g : GL (BlkIdx 1 m) (ZMod 2)) :
      α g = φ ⟨h * ((φ.symm g : ↥Y) : G) * h⁻¹, hYmem _ (φ.symm g).2⟩ := rfl
  have htj : (φ.symm (jGL 1 m) : ↥Y) = ⟨t, hS.t_mem⟩ := by
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, hS.φ_t]
  have hαj : α (jGL 1 m) = jGL 1 m := by
    rw [hα_apply]
    have hch : (⟨h * ((φ.symm (jGL 1 m) : ↥Y) : G) * h⁻¹,
        hYmem _ (φ.symm (jGL 1 m)).2⟩ : ↥Y) = ⟨t, hS.t_mem⟩ := by
      ext
      rw [htj]
      have hcomm : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.mp hh
      calc
        h * t * h⁻¹ = (h * t) * h⁻¹ := rfl
        _ = (t * h) * h⁻¹ := by rw [hcomm]
        _ = t := by group
    rw [hch, hS.φ_t]
  have hmap_liftSub (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) :
      (liftSub φ K).map (MulAut.conj h).toMonoidHom = liftSub φ (K.map α.toMonoidHom) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨huY, huK⟩ := mem_liftSub.mp hu
      have hmem : MulAut.conj h u ∈ Y := by
        rw [MulAut.conj_apply]
        exact hYmem u huY
      refine mem_liftSub.mpr ⟨hmem, ?_⟩
      rw [Subgroup.mem_map]
      refine ⟨φ ⟨u, huY⟩, huK, ?_⟩
      have hval : (⟨MulAut.conj h u, hmem⟩ : ↥Y) = ⟨h * u * h⁻¹, hYmem u huY⟩ := by
        ext
        change MulAut.conj h u = h * u * h⁻¹
        rw [MulAut.conj_apply]
      have hαu : α (φ ⟨u, huY⟩) = φ ⟨h * u * h⁻¹, hYmem u huY⟩ := by
        simpa using hα_apply (φ ⟨u, huY⟩)
      change α (φ ⟨u, huY⟩) = φ ⟨(MulAut.conj h) u, hmem⟩
      rw [hval]
      exact hαu
    · intro hx
      obtain ⟨hxY, hxK⟩ := mem_liftSub.mp hx
      obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hxK
      refine Subgroup.mem_map.mpr ⟨((φ.symm k : ↥Y) : G), ?_, ?_⟩
      · exact mem_liftSub.mpr ⟨(φ.symm k).2, by simpa using hkK⟩
      · have hmem : h * ((φ.symm k : ↥Y) : G) * h⁻¹ ∈ Y := hYmem _ (φ.symm k).2
        have hsub : (⟨h * ((φ.symm k : ↥Y) : G) * h⁻¹, hmem⟩ : ↥Y) = ⟨x, hxY⟩ := by
          apply φ.injective
          have hleft : φ ⟨h * ((φ.symm k : ↥Y) : G) * h⁻¹, hmem⟩ = α k :=
            (hα_apply k).symm
          rw [hleft]
          simpa using hkx
        simpa [MulAut.conj_apply] using congrArg Subtype.val hsub
  have huOne_map : (uOne m).map α.toMonoidHom = uTwo m := by
    apply (caSigN_liftSub_eq_iff (φ := φ)).mp
    rw [← hmap_liftSub (uOne m)]
    exact h12
  have huTwo_map : (uTwo m).map α.toMonoidHom = uOne m := by
    apply (caSigN_liftSub_eq_iff (φ := φ)).mp
    rw [← hmap_liftSub (uTwo m)]
    exact h21
  rcases exists_eq_conj_or_conj_inverseTranspose hm1 α with ⟨A, hA | hA⟩
  · have hAcent : A ∈ Cent 1 m := by
      change A ∈ Subgroup.centralizer ({jGL 1 m} : Set (GL (BlkIdx 1 m) (ZMod 2)))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hA (jGL 1 m)
      rw [hαj] at h
      calc
        A * jGL 1 m = (A * jGL 1 m * A⁻¹) * A := by group
        _ = jGL 1 m * A := by rw [← h]
    have hle : (uOne m).map α.toMonoidHom ≤ uOne m := by
      rintro g ⟨u, hu, rfl⟩
      change α u ∈ uOne m
      rw [hA u]
      exact conj_mem_uOne hAcent hu
    have hle' : uTwo m ≤ uOne m := by
      rw [← huOne_map]
      exact hle
    exact absurd hle' (not_uTwo_le_uOne hm1)
  · obtain ⟨y, hyCent, hyconj⟩ := exists_cent_eq_conj_sigmaStd α hA hαj
    let yG : G := ((φ.symm y : ↥Y) : G)
    have hyGY : yG ∈ Y := (φ.symm y).2
    have hyGlift : yG ∈ liftSub φ (Cent 1 m) :=
      mem_liftSub.mpr ⟨hyGY, by simpa [yG] using hyCent⟩
    have hyGcomm : yG * t = t * yG := ((mem_liftSub_cent hS).mp hyGlift).2
    have hyGcomm_inv : yG⁻¹ * t = t * yG⁻¹ := by
      have h := congrArg (fun z => yG⁻¹ * z * yG⁻¹) hyGcomm
      simpa [mul_assoc] using h.symm
    let σ : G := yG⁻¹ * h
    have hσH : σ ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hht : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.mp hh
      change yG⁻¹ * h * t = t * (yG⁻¹ * h)
      calc
        yG⁻¹ * h * t = yG⁻¹ * (h * t) := by group
        _ = yG⁻¹ * (t * h) := by rw [hht]
        _ = (yG⁻¹ * t) * h := by group
        _ = (t * yG⁻¹) * h := by rw [hyGcomm_inv]
        _ = t * (yG⁻¹ * h) := by group
    have hσYmem : ∀ a ∈ Y, σ * a * σ⁻¹ ∈ Y := by
      intro a ha
      have hform : σ * a * σ⁻¹ = yG⁻¹ * (h * a * h⁻¹) * yG := by
        change yG⁻¹ * h * a * (yG⁻¹ * h)⁻¹ = yG⁻¹ * (h * a * h⁻¹) * yG
        group
      rw [hform]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hyGY) (hYmem a ha)) hyGY
    have hσact : ∀ a : ↥Y, φ ⟨σ * (a : G) * σ⁻¹, hσYmem a a.2⟩ =
        sigmaStd m (φ a) := by
      intro a
      have hyGφ : φ ⟨yG, hyGY⟩ = y := by
        simpa [yG] using φ.apply_symm_apply y
      have hconj : φ ⟨h * (a : G) * h⁻¹, hYmem a a.2⟩ = α (φ a) := by
        rw [hα_apply, φ.symm_apply_apply]
      have hsub : (⟨σ * (a : G) * σ⁻¹, hσYmem a a.2⟩ : ↥Y) =
          ⟨yG, hyGY⟩⁻¹ * ⟨h * (a : G) * h⁻¹, hYmem a a.2⟩ * ⟨yG, hyGY⟩ := by
        ext
        change yG⁻¹ * h * (a : G) * (yG⁻¹ * h)⁻¹ =
          yG⁻¹ * (h * (a : G) * h⁻¹) * yG
        group
      rw [hsub, map_mul, map_mul, map_inv, hyGφ, hconj, hyconj (φ a)]
      group
    have hσ2comm : ∀ a ∈ Y, σ * σ * a = a * (σ * σ) := by
      intro a ha
      let b : ↥Y := ⟨σ * a * σ⁻¹, hσYmem a ha⟩
      have hstep : φ ⟨σ * (b : G) * σ⁻¹, hσYmem b b.2⟩ = φ ⟨a, ha⟩ := by
        rw [hσact b, hσact ⟨a, ha⟩, sigmaStd_sigmaStd]
      have hEq : σ * (b : G) * σ⁻¹ = a := by
        have hsub : (⟨σ * (b : G) * σ⁻¹, hσYmem b b.2⟩ : ↥Y) = ⟨a, ha⟩ :=
          φ.injective hstep
        exact congrArg Subtype.val hsub
      have hEq2 : σ * σ * a * σ⁻¹ * σ⁻¹ = a := by
        calc
          σ * σ * a * σ⁻¹ * σ⁻¹ = σ * (σ * a * σ⁻¹) * σ⁻¹ := by group
          _ = a := hEq
      calc
        σ * σ * a = (σ * σ * a * σ⁻¹ * σ⁻¹) * (σ * σ) := by group
        _ = a * (σ * σ) := by rw [hEq2]
    have hσ2H : σ * σ ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hσt : σ * t = t * σ := Subgroup.mem_centralizer_singleton_iff.mp hσH
      calc
        σ * σ * t = σ * (σ * t) := by group
        _ = σ * (t * σ) := by rw [hσt]
        _ = (σ * t) * σ := by group
        _ = (t * σ) * σ := by rw [hσt]
        _ = t * (σ * σ) := by group
    have hcommU : ∀ u ∈ liftSub φ (uSub 1 m),
        σ * σ * u * (σ * σ)⁻¹ * u⁻¹ ∈ Subgroup.zpowers t := by
      intro u hu
      have huY : u ∈ Y := liftSub_le (uSub 1 m) hu
      have hone : σ * σ * u * (σ * σ)⁻¹ * u⁻¹ = 1 := by
        have h1 : σ * σ * u * (σ * σ)⁻¹ = u := by
          rw [hσ2comm u huY]
          group
        rw [h1, mul_inv_cancel]
      rw [hone]
      exact Subgroup.one_mem _
    have hσ2U : σ * σ ∈ liftSub φ (uSub 1 m) :=
      mem_liftSub_uSub_of_commutator hchar hS hσ2H hcommU
    have hσ2Y : σ * σ ∈ Y := liftSub_le (uSub 1 m) hσ2U
    have hσ2one : σ * σ = 1 :=
      eq_one_of_forall_commute_of_mem φ hσ2Y hσ2comm
    exact ⟨σ, hσH, hσ2one, hσYmem, hσact⟩

end CFSG.StandardType.FF81.CentA

end
