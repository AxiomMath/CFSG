module

public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.SimsD1TransMod
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.Quasithin.H13

open Subgroup

variable {A G : Type} [Group A] [Group G]

@[expose] noncomputable def equivMapOfInjectiveOn (f : A →* G) {W V : Subgroup A} (hWV : W ≤ V)
    (hV : V ⊓ f.ker = ⊥) : ↥W ≃* ↥(W.map f) :=
  MulEquiv.ofBijective
    ((f.comp W.subtype).codRestrict (W.map f) fun w => Subgroup.mem_map_of_mem f w.2)
    ⟨by
      intro x y hxy
      have hmem : ((x : A)⁻¹ * (y : A)) ∈ V ⊓ f.ker := by
        refine ⟨V.mul_mem (V.inv_mem (hWV x.2)) (hWV y.2), ?_⟩
        have hxy' : f (x : A) = f (y : A) := congrArg Subtype.val hxy
        exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy', inv_mul_cancel])
      rw [hV, Subgroup.mem_bot] at hmem
      exact Subtype.ext (inv_mul_eq_one.mp hmem)
    , by
      rintro ⟨y, hy⟩
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨w, hw⟩, rfl⟩⟩

@[simp] theorem equivMapOfInjectiveOn_apply (f : A →* G) {W V : Subgroup A} (hWV : W ≤ V)
    (hV : V ⊓ f.ker = ⊥) (w : ↥W) :
    ((equivMapOfInjectiveOn f hWV hV w : ↥(W.map f)) : G) = f w := rfl

private theorem mulAut_congr_conjAct_eq (f : A →* G) {V : Subgroup A} {W : Subgroup G}
    (e : ↥V ≃* ↥W) (he : ∀ v : ↥V, ((e v : ↥W) : G) = f v) {h : A}
    (hh : h ∈ Subgroup.normalizer (V : Set A))
    (y : ↥(Subgroup.normalizer (W : Set G))) (hy : (y : G) = f h) :
    MulAut.congr e (conjAct V ⟨h, hh⟩) = conjAct W y := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  have hstep : MulAut.congr e (conjAct V ⟨h, hh⟩) (e v) = e (conjAct V ⟨h, hh⟩ v) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hstep, he (conjAct V ⟨h, hh⟩ v),
    CFSG.Quasithin.SimsD1.TransMod.coe_conjAct_apply,
    CFSG.Quasithin.SimsD1.TransMod.coe_conjAct_apply,
    he v, hy, map_mul, map_mul, map_inv]

private theorem autOn_map_of_equiv_aux (f : A →* G) {H V : Subgroup A} {W : Subgroup G}
    (e : ↥V ≃* ↥W) (he : ∀ v : ↥V, ((e v : ↥W) : G) = f v) (hW : V.map f = W)
    (hH : H ≤ Subgroup.normalizer (V : Set A)) :
    autOn (H.map f) W = (autOn H V).map (MulAut.congr e).toMonoidHom := by
  ext σ
  constructor
  · intro hσ
    have hσ' : σ ∈ Subgroup.map (conjAct W)
        ((H.map f).subgroupOf (Subgroup.normalizer (W : Set G))) := by
      simpa only [autOn] using hσ
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hσ'
    have hyH : (y : G) ∈ H.map f := by
      simpa only [Subgroup.mem_subgroupOf] using hy
    obtain ⟨h, hhH, hfh⟩ := Subgroup.mem_map.mp hyH
    have hhN : h ∈ Subgroup.normalizer (V : Set A) := hH hhH
    refine Subgroup.mem_map.mpr ⟨conjAct V ⟨h, hhN⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨⟨h, hhN⟩, Subgroup.mem_subgroupOf.mpr hhH, rfl⟩
    · exact mulAut_congr_conjAct_eq f e he hhN y hfh.symm
  · rintro ⟨a, ha, rfl⟩
    rw [autOn] at ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    have hzH : (z : A) ∈ H := by
      simpa only [Subgroup.mem_subgroupOf] using hz
    have hzN : f (z : A) ∈ Subgroup.normalizer (W : Set G) := by
      have h := Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f z.2)
      rwa [hW] at h
    refine Subgroup.mem_map.mpr ⟨⟨f (z : A), hzN⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem f hzH)
    · exact (mulAut_congr_conjAct_eq f e he z.2 ⟨f (z : A), hzN⟩ rfl).symm

theorem autOn_map_of_equiv (f : A →* G) {H V : Subgroup A} (e : ↥V ≃* ↥(V.map f))
    (he : ∀ v : ↥V, ((e v : ↥(V.map f)) : G) = f v)
    (hH : H ≤ Subgroup.normalizer (V : Set A)) :
    autOn (H.map f) (V.map f) = (autOn H V).map (MulAut.congr e).toMonoidHom :=
  autOn_map_of_equiv_aux f e he rfl hH

theorem IsXSectionIso₂.of_map_bot {X J K : Subgroup A} (f : A →* G)
    (eJ : ↥J ≃* ↥(J.map f)) (heJ : ∀ j : ↥J, ((eJ j : ↥(J.map f)) : G) = f j)
    (eK : ↥K ≃* ↥(K.map f)) (heK : ∀ k : ↥K, ((eK k : ↥(K.map f)) : G) = f k)
    (h : IsXSectionIso₂ (X.map f) (J.map f) ⊥ (K.map f) ⊥) :
    IsXSectionIso₂ X J ⊥ K ⊥ := by
  obtain ⟨hNJ, hNK, e, he⟩ := h
  have hNJ' : ((⊥ : Subgroup A).subgroupOf J).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  have hNK' : ((⊥ : Subgroup A).subgroupOf K).Normal := by
    rw [Subgroup.bot_subgroupOf]; infer_instance
  let eJq : ↥J ⧸ (⊥ : Subgroup A).subgroupOf J ≃*
      ↥(J.map f) ⧸ (⊥ : Subgroup G).subgroupOf (J.map f) :=
    QuotientGroup.congr _ _ eJ (by simp)
  let eKq : ↥K ⧸ (⊥ : Subgroup A).subgroupOf K ≃*
      ↥(K.map f) ⧸ (⊥ : Subgroup G).subgroupOf (K.map f) :=
    QuotientGroup.congr _ _ eK (by simp)
  have eJq_mk : ∀ j : ↥J, eJq (QuotientGroup.mk j) = QuotientGroup.mk (eJ j) :=
    fun j => QuotientGroup.congr_mk _ _ eJ (by simp) j
  have eKq_mk : ∀ k : ↥K, eKq (QuotientGroup.mk k) = QuotientGroup.mk (eK k) :=
    fun k => QuotientGroup.congr_mk _ _ eK (by simp) k
  refine ⟨hNJ', hNK', eJq.trans (e.trans eKq.symm), ?_⟩
  intro x hx j k hj hk hjk
  have h1 : e (QuotientGroup.mk (eJ j)) = QuotientGroup.mk (eK k) := by
    have hjk' := congrArg eKq hjk
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      eJq_mk, eKq_mk] at hjk'
    exact hjk'
  have hj' : f x * (eJ j : G) * (f x)⁻¹ ∈ J.map f := by
    have hmem : f (x * (j : A) * x⁻¹) ∈ J.map f := Subgroup.mem_map_of_mem f hj
    rw [map_mul, map_mul, map_inv, ← heJ j] at hmem
    exact hmem
  have hk' : f x * (eK k : G) * (f x)⁻¹ ∈ K.map f := by
    have hmem : f (x * (k : A) * x⁻¹) ∈ K.map f := Subgroup.mem_map_of_mem f hk
    rw [map_mul, map_mul, map_inv, ← heK k] at hmem
    exact hmem
  have h2 := he (f x) (Subgroup.mem_map_of_mem f hx) (eJ j) (eK k) hj' hk' h1
  have hjeq : eJ ⟨x * (j : A) * x⁻¹, hj⟩ =
      ⟨f x * (eJ j : G) * (f x)⁻¹, hj'⟩ := by
    refine Subtype.ext ?_
    calc ((eJ ⟨x * (j : A) * x⁻¹, hj⟩ : ↥(J.map f)) : G)
        = f (x * (j : A) * x⁻¹) := heJ _
      _ = f x * (eJ j : G) * (f x)⁻¹ := by
        rw [map_mul, map_mul, map_inv, ← heJ j]
  have hkeq : eK ⟨x * (k : A) * x⁻¹, hk⟩ =
      ⟨f x * (eK k : G) * (f x)⁻¹, hk'⟩ := by
    refine Subtype.ext ?_
    calc ((eK ⟨x * (k : A) * x⁻¹, hk⟩ : ↥(K.map f)) : G)
        = f (x * (k : A) * x⁻¹) := heK _
      _ = f x * (eK k : G) * (f x)⁻¹ := by
        rw [map_mul, map_mul, map_inv, ← heK k]
  have h3 : e (QuotientGroup.mk (eJ ⟨x * (j : A) * x⁻¹, hj⟩)) =
      QuotientGroup.mk (eK ⟨x * (k : A) * x⁻¹, hk⟩) := by
    rw [hjeq, hkeq]
    exact h2
  change eKq.symm (e (eJq (QuotientGroup.mk ⟨x * (j : A) * x⁻¹, hj⟩))) =
    QuotientGroup.mk ⟨x * (k : A) * x⁻¹, hk⟩
  rw [eJq_mk, h3, ← eKq_mk ⟨x * (k : A) * x⁻¹, hk⟩, MulEquiv.symm_apply_apply]

theorem IsNaturalSumUnder.of_map {n : ℕ} {L V : Subgroup A} (f : A →* G)
    (hV : V ⊓ f.ker = ⊥) (hL : L ≤ Subgroup.normalizer (V : Set A))
    (h : IsNaturalSumUnder n (L.map f) (V.map f)) : IsNaturalSumUnder n L V := by
  classical
  obtain ⟨k, W, hk, hW, hiso, hind, hsup⟩ := h
  let W' : Fin k → Subgroup A := fun i => V ⊓ (W i).comap f
  have hW'_le : ∀ i, W' i ≤ V := fun i => inf_le_left
  have hW'_map : ∀ i, (W' i).map f = W i := by
    intro i
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨v, hvV, hvy⟩ := Subgroup.mem_map.mp ((hW i).1 hy)
      refine Subgroup.mem_map.mpr ⟨v, ⟨hvV, ?_⟩, hvy⟩
      exact Subgroup.mem_comap.mpr (by rwa [hvy])
  let e : ∀ i, ↥(W' i) ≃* ↥(W i) := fun i =>
    (equivMapOfInjectiveOn f (hW'_le i) hV).trans (MulEquiv.subgroupCongr (hW'_map i))
  have he : ∀ (i) (v : ↥(W' i)), ((e i v : ↥(W i)) : G) = f v := by
    intro i v
    simp only [e, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      equivMapOfInjectiveOn_apply]
  have hLnorm : ∀ i, L ≤ Subgroup.normalizer (W' i : Set A) := by
    intro i l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxV, hxW⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hL hl) x).mp hxV, ?_⟩
      have hfl : f l ∈ Subgroup.normalizer (W i : Set G) :=
        (hW i).2.1 (Subgroup.mem_map_of_mem f hl)
      exact Subgroup.mem_comap.mpr (by
        have h := (Subgroup.mem_normalizer_iff.mp hfl (f x)).mp hxW
        simpa only [map_mul, map_inv] using h)
    · rintro ⟨hxV, hxW⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hL hl) x).mpr hxV, ?_⟩
      have hfl : f l ∈ Subgroup.normalizer (W i : Set G) :=
        (hW i).2.1 (Subgroup.mem_map_of_mem f hl)
      refine (Subgroup.mem_normalizer_iff.mp hfl (f x)).mpr ?_
      have hxW' := Subgroup.mem_comap.mp hxW
      simpa only [map_mul, map_inv] using hxW'
  have hmap_iSup : ∀ i, (⨆ j, ⨆ (_ : j ≠ i), W' j).map f =
      ⨆ j, ⨆ (_ : j ≠ i), W j := by
    intro i
    simp only [Subgroup.map_iSup, hW'_map]
  have hind' : iSupIndep W' := by
    intro i
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxi, hxsup⟩ := Subgroup.mem_inf.mp hx
    have hxV : x ∈ V := hW'_le i hxi
    have hfx : f x ∈ W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) := by
      refine ⟨?_, ?_⟩
      · rw [← hW'_map i]
        exact Subgroup.mem_map_of_mem f hxi
      · rw [← hmap_iSup i]
        exact Subgroup.mem_map_of_mem f hxsup
    have hzero : f x = 1 := by
      have h := disjoint_iff.mp (hind i)
      rw [h] at hfx
      simpa using hfx
    have hmem : x ∈ V ⊓ f.ker := ⟨hxV, hzero⟩
    rw [hV] at hmem
    simpa using hmem
  have hsup' : (⨆ i, W' i) = V := by
    refine le_antisymm (iSup_le hW'_le) ?_
    intro x hx
    have hfx : f x ∈ (⨆ i, W' i).map f := by
      have hmap : (⨆ i, W' i).map f = ⨆ i, W i := by
        simp only [Subgroup.map_iSup, hW'_map]
      rw [hmap, hsup]
      exact Subgroup.mem_map_of_mem f hx
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hfx
    have hyV : y ∈ V := iSup_le hW'_le hy
    have hyx : y = x := by
      have hmem : y⁻¹ * x ∈ V ⊓ f.ker := by
        refine ⟨V.mul_mem (V.inv_mem hyV) hx, ?_⟩
        exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hfy, inv_mul_cancel])
      rw [hV, Subgroup.mem_bot] at hmem
      exact inv_mul_eq_one.mp hmem
    rwa [hyx] at hy
  refine ⟨k, W', hk, ?_, ?_, hind', hsup'⟩
  · intro i
    obtain ⟨hcomm, hBNi⟩ := (hW i).2.2
    haveI : IsMulCommutative ↥(W i) := hcomm
    have hcomm' : IsMulCommutative ↥(W' i) :=
      CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv (e i).symm hcomm
    haveI : IsMulCommutative ↥(W' i) := hcomm'
    letI : CommGroup ↥(W i) := IsMulCommutative.instCommGroup
    letI : CommGroup ↥(W' i) := IsMulCommutative.instCommGroup
    refine ⟨hW'_le i, hLnorm i, hcomm', ?_⟩
    have haut : autOn (L.map f) (W i) =
        (autOn L (W' i)).map (MulAut.congr (e i)).toMonoidHom :=
      autOn_map_of_equiv_aux f (e i) (he i) (hW'_map i) (hLnorm i)
    obtain ⟨K, hKfield, hKfinite, hKcard, hReal⟩ := hBNi
    have hReal' : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)).Realizes
        ((autOn L (W' i)).map (MulAut.congr (e i)).toMonoidHom) ⊤ ⊥ := by
      rwa [← haut]
    have hReal'' := CFSG.Quasithin.H.LU.realizes_map
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n K)) (e i).symm hReal'
    rw [Subgroup.map_map, CFSG.Quasithin.SimsD1.TransMod.congr_symm_comp_congr,
      Subgroup.map_id] at hReal''
    exact ⟨K, hKfield, hKfinite, hKcard, hReal''⟩
  · intro i j
    have hh : IsXSectionIso₂ (L.map f) ((W' i).map f) ⊥ ((W' j).map f) ⊥ := by
      simpa only [hW'_map i, hW'_map j] using hiso i j
    exact IsXSectionIso₂.of_map_bot f _
      (fun v => equivMapOfInjectiveOn_apply f (hW'_le i) hV v) _
      (fun v => equivMapOfInjectiveOn_apply f (hW'_le j) hV v) hh

end CFSG.Quasithin.H13
