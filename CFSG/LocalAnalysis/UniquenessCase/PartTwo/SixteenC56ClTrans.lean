module

public import CFSG.Quasithin.Background.ElemAbTransport
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Trans

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem aSet_map_congr_equiv_iff (φ : W ≃* W') (k : ℕ) (X A : Subgroup (MulAut W)) :
    A.map (MulAut.congr φ).toMonoidHom ∈ E3.aSet k (X.map (MulAut.congr φ).toMonoidHom) ↔
      A ∈ E3.aSet k X := by
  have hinj : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  have hsurj : Function.Surjective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).surjective
  have hmQ : ∀ A B : Subgroup (MulAut W), E3.mQuot (A.map (MulAut.congr φ).toMonoidHom)
      (B.map (MulAut.congr φ).toMonoidHom) = E3.mQuot A B := fun A B => by
    unfold E3.mQuot
    rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]
  constructor
  · rintro ⟨hAX, hA1, hAe, hAc⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hinj).1 hAX, fun h => hA1 ?_,
      (FixVLat.isElemAbelian2_map_congr_iff φ).1 hAe, fun B hB hm => ?_⟩
    · rw [h]; exact Subgroup.map_bot _
    · have h1 := hAc (B.map (MulAut.congr φ).toMonoidHom) (Subgroup.map_mono hB)
        (by rw [hmQ]; exact hm)
      rw [fixV_map_congr_equiv, fixV_map_congr_equiv] at h1
      exact Subgroup.map_injective φ.injective h1
  · rintro ⟨hAX, hA1, hAe, hAc⟩
    refine ⟨Subgroup.map_mono hAX, fun h => hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h),
      (FixVLat.isElemAbelian2_map_congr_iff φ).2 hAe, fun B' hB' hm => ?_⟩
    set B := B'.comap (MulAut.congr φ).toMonoidHom with hB
    have hBA : B ≤ A := fun b hb => (Subgroup.mem_map_iff_mem hinj).1 (hB' hb)
    have hB'e : B.map (MulAut.congr φ).toMonoidHom = B' :=
      Subgroup.map_comap_eq_self_of_surjective hsurj _
    rw [← hB'e] at hm ⊢
    rw [hmQ] at hm
    rw [fixV_map_congr_equiv, fixV_map_congr_equiv, hAc B hBA hm]

end Trans

@[expose] def OmegaModel.ofEquiv {W W' : Type} [CommGroup W] [CommGroup W'] (S : OmegaModel W)
    (φ : W' ≃* W) : OmegaModel W' :=
  { K := S.K, field := S.field, fin := S.fin, charTwo := S.charTwo, four_le := S.four_le,
    e := φ.trans S.e }

theorem OmegaModel.ofEquiv_card_K {W W' : Type} [CommGroup W] [CommGroup W'] (S : OmegaModel W)
    (φ : W' ≃* W) : Nat.card (S.ofEquiv φ).K = Nat.card S.K := rfl

theorem OmegaModel.omega_ofEquiv {W W' : Type} [CommGroup W] [CommGroup W'] (S : OmegaModel W)
    (φ : W' ≃* W) :
    (S.ofEquiv φ).omega = S.omega.map (MulAut.congr φ.symm).toMonoidHom := by
  have hpt : ∀ γ : GL OmI S.K, (S.ofEquiv φ).actHom γ = (MulAut.congr φ.symm) (S.actHom γ) :=
    fun γ => MulEquiv.ext fun x => rfl
  ext x
  simp only [OmegaModel.omega, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨S.actHom γ, ⟨γ, hγ, rfl⟩, (hpt γ).symm⟩
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, hpt γ⟩

theorem map_le_normalizer_map_iff {M M' : Type*} [Group M] [Group M'] (f : M ≃* M')
    (X H : Subgroup M) :
    X.map f.toMonoidHom ≤ Subgroup.normalizer ((H.map f.toMonoidHom : Subgroup M') : Set M') ↔
      X ≤ Subgroup.normalizer (H : Set M) := by
  have hmem : ∀ (K : Subgroup M) (x : M'), x ∈ K.map f.toMonoidHom ↔ f.symm x ∈ K :=
    fun K x => Subgroup.mem_map_equiv
  constructor
  · intro h x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have h1 := Subgroup.mem_normalizer_iff.1 (h ⟨x, hx, rfl⟩) (f n)
    rw [hmem, hmem] at h1
    simpa using h1
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_normalizer_iff]
    intro n'
    have h1 := Subgroup.mem_normalizer_iff.1 (h hx) (f.symm n')
    rw [hmem, hmem]
    simpa using h1

variable {G : Type} [Group G]

@[expose] noncomputable def intModConj (V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G) :
    IntMod V hV ≃* IntMod (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g) where
  toFun v := IntMod.mk (E3.isElemAbelian_conjSubgroup hV g)
    ⟨g⁻¹ * v.val * g, by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using v.val_mem⟩
  invFun w := IntMod.mk hV ⟨g * w.val * g⁻¹, mem_conjSubgroup_iff.1 w.val_mem⟩
  left_inv v := by
    apply IntMod.val_injective
    show g * (g⁻¹ * v.val * g) * g⁻¹ = v.val
    group
  right_inv w := by
    apply IntMod.val_injective
    show g⁻¹ * (g * w.val * g⁻¹) * g = w.val
    group
  map_mul' a b := by
    apply IntMod.val_injective
    show g⁻¹ * (a.val * b.val) * g = (g⁻¹ * a.val * g) * (g⁻¹ * b.val * g)
    group

theorem intModConj_val (V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G) (v : IntMod V hV) :
    (intModConj V hV g v).val = g⁻¹ * v.val * g := rfl

theorem convI_conj {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G)
    (k : Subgroup.normalizer (V : Set G))
    (k' : Subgroup.normalizer (conjSubgroup V g : Set G)) (hk : (k' : G) = g⁻¹ * (k : G) * g) :
    convI (E3.isElemAbelian_conjSubgroup hV g) k' =
      MulAut.congr (intModConj V hV g) (convI hV k) := by
  apply MulEquiv.ext
  intro w
  apply IntMod.val_injective
  rw [convI_apply_val]
  show _ = (intModConj V hV g (convI hV k ((intModConj V hV g).symm w))).val
  rw [intModConj_val, convI_apply_val]
  have hs : ((intModConj V hV g).symm w).val = g * w.val * g⁻¹ := rfl
  rw [hs, hk]
  group

theorem autI_conjSubgroup {V : Subgroup G} (hV : IsElemAbelian 2 V) (K : Subgroup G) (g : G) :
    autI (E3.isElemAbelian_conjSubgroup hV g) (conjSubgroup K g) =
      (autI hV K).map (MulAut.congr (intModConj V hV g)).toMonoidHom := by
  ext φ'
  rw [mem_autI, Subgroup.mem_map]
  constructor
  · rintro ⟨k', hk'K, hk'⟩
    have hkN : g * (k' : G) * g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      have h : (k' : G) ∈ conjSubgroup (Subgroup.normalizer (V : Set G)) g := by
        rw [E3.conjSubgroup_normalizer]
        exact k'.2
      exact mem_conjSubgroup_iff.1 h
    refine ⟨convI hV ⟨g * (k' : G) * g⁻¹, hkN⟩, ?_, ?_⟩
    · exact convI_mem_autI hV (mem_conjSubgroup_iff.1 hk'K) hkN
    · rw [← hk']
      exact (convI_conj hV g ⟨_, hkN⟩ k' (by simp [mul_assoc])).symm
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hφ
    have hk'N : g⁻¹ * (k : G) * g ∈
        Subgroup.normalizer ((conjSubgroup V g : Subgroup G) : Set G) := by
      rw [← E3.conjSubgroup_normalizer, mem_conjSubgroup_iff]
      have h := k.2
      simpa [mul_assoc] using h
    refine ⟨⟨g⁻¹ * (k : G) * g, hk'N⟩, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hkK
    · exact convI_conj hV g k _ rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
