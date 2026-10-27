module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {H H' : Type} [Group H] [Group H'] {p r : ℕ} {SD SS SD' SS' : LargeEvenLabel → Prop}

theorem GGSecFiveBNativeAt.map_mulEquiv (α : H ≃* H') {T : Subgroup H}
    (h : GGSecFiveBNativeAt H p r SD SS T) :
    GGSecFiveBNativeAt H' p r SD SS (T.map α.toMonoidHom) := by
  obtain ⟨Θ, hΘ, hnat⟩ := h
  set eT : ↥T ≃* ↥(T.map α.toMonoidHom) :=
    Subgroup.equivMapOfInjective T α.toMonoidHom α.injective with heT
  set Θ' : (Fin r → Multiplicative (ZMod p)) ≃* ↥(T.map α.toMonoidHom) := Θ.trans eT with hΘ'
  have hcoord (f : Fin r → Multiplicative (ZMod p)) : (Θ' f : H') = α (Θ f : H) := by
    rw [hΘ', heT, MulEquiv.trans_apply]
    exact Subgroup.coe_equivMapOfInjective_apply T α.toMonoidHom α.injective (Θ f)
  refine ⟨Θ', ?_, ?_⟩
  · intro g' hg'
    have hg : ∀ s ∈ T, α.symm g' * s * (α.symm g')⁻¹ ∈ T := by
      intro s hs
      have h1 : g' * α s * g'⁻¹ ∈ T.map α.toMonoidHom :=
        hg' (α s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp h1
      have h2 : g' * α s * g'⁻¹ = α (α.symm g' * s * (α.symm g')⁻¹) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← α.injective (hye.trans h2)]
      exact hy
    have hfun : (fun f => Θ'.symm ⟨g' * (Θ' f : H') * g'⁻¹, hg' _ (Θ' f).2⟩) =
        fun f => Θ.symm ⟨α.symm g' * (Θ f : H) * (α.symm g')⁻¹, hg _ (Θ f).2⟩ := by
      funext f
      apply Θ'.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply]
      have hR : (Θ' (Θ.symm ⟨α.symm g' * (Θ f : H) * (α.symm g')⁻¹,
            hg _ (Θ f).2⟩) : H') = α (α.symm g' * (Θ f : H) * (α.symm g')⁻¹) := by
        rw [hΘ', heT, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        exact Subgroup.coe_equivMapOfInjective_apply T α.toMonoidHom α.injective _
      change g' * (Θ' f : H') * g'⁻¹ =
        (Θ' (Θ.symm ⟨α.symm g' * (Θ f : H) * (α.symm g')⁻¹, hg _ (Θ f).2⟩) : H')
      rw [hR, hcoord f, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hfun]
    exact hΘ (α.symm g') hg
  · rintro t' J' hJ' hcard'
    set t : ↥T := eT.symm t' with ht
    set J : Subgroup H := J'.map α.symm.toMonoidHom with hJdef
    have ht' : (t' : H') = α (t : H) := by
      have h1 : eT t = t' := MulEquiv.apply_symm_apply eT t'
      rw [← h1]
      exact Subgroup.coe_equivMapOfInjective_apply T α.toMonoidHom α.injective t
    have hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({(t : H)} : Set H)) := by
      have hOpen : CFSG.Open.IsComponentOf J
          ((Subgroup.centralizer ({(t' : H')} : Set H')).map α.symm.toMonoidHom) := by
        have hmapc := CFSG.isComponentOf_map_mulEquiv α.symm (isComponentOf_iff_open.mp hJ')
        simpa only [hJdef] using hmapc
      rw [isComponentOf_iff_open]
      convert hOpen using 1
      rw [← CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq α.symm
        ({(t' : H')} : Set H')]
      simp only [Set.image_singleton]
      rw [show α.symm (t' : H') = (t : H) from by rw [ht', MulEquiv.symm_apply_apply]]
    have hcent : (Subgroup.centralizer (J : Set H)).map α.toMonoidHom =
        Subgroup.centralizer (J' : Set H') := by
      rw [← CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq α (J : Set H)]
      congr 1
      rw [hJdef]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
        rw [← hzy]
        simpa using hz
      · intro hx
        exact ⟨α.symm x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩
    have hJmap : J.map α.toMonoidHom = J' := by
      rw [hJdef, Subgroup.map_map]
      simp
    have hcard : Nat.card ↥(T ⊓ Subgroup.centralizer (J : Set H)) = p := by
      rw [← hcard']
      have hinf : T.map α.toMonoidHom ⊓ Subgroup.centralizer (J' : Set H') =
          (T ⊓ Subgroup.centralizer (J : Set H)).map α.toMonoidHom := by
        rw [← hcent, ← Subgroup.map_inf_eq T (Subgroup.centralizer (J : Set H))
          α.toMonoidHom α.injective]
      rw [hinf, Nat.card_congr (Subgroup.equivMapOfInjective
        (T ⊓ Subgroup.centralizer (J : Set H)) α.toMonoidHom α.injective).toEquiv]
    have hcoordt : Θ'.symm t' = Θ.symm t := by
      rw [hΘ', ht]
      rfl
    rcases hnat t J hJ hcard with
      ⟨hd, lab, hlab, hlam, hGlab, hcen⟩ | ⟨hs, lab, hlab, hlam, hGlab⟩
    · refine Or.inl ⟨?_, lab, hlab, hlam, ?_, ?_⟩
      · rwa [hcoordt]
      · rw [← hJmap]
        exact ggHasLabel_quotCenter_of_mulEquiv
          (Subgroup.equivMapOfInjective J α.toMonoidHom α.injective) hGlab
      · intro h
        rw [← hJmap, ← Subgroup.map_center_eq
          (Subgroup.equivMapOfInjective J α.toMonoidHom α.injective), hcen h, Subgroup.map_bot]
    · refine Or.inr ⟨?_, lab, hlab, hlam, ?_⟩
      · rwa [hcoordt]
      · rw [← hJmap]
        exact ggHasLabel_quotCenter_of_mulEquiv
          (Subgroup.equivMapOfInjective J α.toMonoidHom α.injective) hGlab

theorem GGSecFiveBNativeAt.of_torus (τ : (Fin r → Multiplicative (ZMod p)) →* H)
    (hτ : Function.Injective τ)
    (hsign : ∀ g : H, (∀ s ∈ τ.range, g * s * g⁻¹ ∈ τ.range) →
      ∃ u : (Fin r → Multiplicative (ZMod p)) → (Fin r → Multiplicative (ZMod p)),
        SpCoord.IsSignedPerm u ∧ ∀ f, g * τ f * g⁻¹ = τ (u f))
    (hcomp : ∀ (f : Fin r → Multiplicative (ZMod p)) (J : Subgroup H),
      CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({τ f} : Set H)) →
      Nat.card ↥(τ.range ⊓ Subgroup.centralizer (J : Set H)) = p →
        (GGCoordDense f ∧ ∃ lab, SD lab ∧ LargeEvenInLambda2 lab ∧
            GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
            (lab = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥)) ∨
          (GGCoordSparse f ∧ ∃ lab, SS lab ∧ LargeEvenInLambda2 lab ∧
            GGHasLabel lab (↥J ⧸ Subgroup.center ↥J))) :
    GGSecFiveBNativeAt H p r SD SS τ.range := by
  set Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥τ.range := MonoidHom.ofInjective hτ with hΘ
  have hΘapply (f : Fin r → Multiplicative (ZMod p)) : (Θ f : H) = τ f := by
    rw [hΘ]
    exact MonoidHom.ofInjective_apply hτ
  refine ⟨Θ, ?_, ?_⟩
  · intro g hg
    obtain ⟨u, hu, huapp⟩ := hsign g hg
    have hfun : (fun f => Θ.symm ⟨g * (Θ f : H) * g⁻¹, hg _ (Θ f).2⟩) = u := by
      funext f
      apply Θ.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply]
      simpa only [hΘapply f, hΘapply (u f)] using huapp f
    rw [hfun]
    exact hu
  · rintro t J hJ hcard
    have ht : (t : H) = τ (Θ.symm t) := by
      rw [← hΘapply (Θ.symm t), MulEquiv.apply_symm_apply]
    rw [ht] at hJ
    exact hcomp (Θ.symm t) J hJ hcard

theorem GGSecFiveBNativeRow.of_std {T₀ : Subgroup H} (h₀ : GGSecFiveBNativeAt H p r SD SS T₀)
    (hconj : ∀ T : Subgroup H, IsElemAbelian p T → Nat.card T = p ^ r →
      ∃ α : H ≃* H, T = T₀.map α.toMonoidHom) :
    GGSecFiveBNativeRow H p r SD SS := by
  intro T hT hcard
  obtain ⟨α, hα⟩ := hconj T hT hcard
  rw [hα]
  exact h₀.map_mulEquiv α

theorem GGSecFiveBNativeRow.of_mulEquiv (α : H ≃* H') (h : GGSecFiveBNativeRow H p r SD SS) :
    GGSecFiveBNativeRow H' p r SD SS := by
  intro T' hT' hcard'
  have hT : IsElemAbelian p (T'.map α.symm.toMonoidHom) := hT'.map α.symm.toMonoidHom
  have hcard : Nat.card (T'.map α.symm.toMonoidHom) = p ^ r := by
    rw [← hcard', Nat.card_congr (Subgroup.equivMapOfInjective T' α.symm.toMonoidHom
      α.symm.injective).toEquiv]
  have hmap : (T'.map α.symm.toMonoidHom).map α.toMonoidHom = T' := by
    rw [Subgroup.map_map]
    simp
  have hAt := h _ hT hcard
  simpa only [hmap] using hAt.map_mulEquiv α

theorem GGSecFiveBNativeSparseAt.map_mulEquiv (α : H ≃* H') {T : Subgroup H}
    (h : GGSecFiveBNativeSparseAt H p r T) :
    GGSecFiveBNativeSparseAt H' p r (T.map α.toMonoidHom) := by
  obtain ⟨Θ, hΘ, hsp⟩ := h
  set eT : ↥T ≃* ↥(T.map α.toMonoidHom) :=
    Subgroup.equivMapOfInjective T α.toMonoidHom α.injective with heT
  set Θ' : (Fin r → Multiplicative (ZMod p)) ≃* ↥(T.map α.toMonoidHom) := Θ.trans eT with hΘ'
  have hcoord (f : Fin r → Multiplicative (ZMod p)) : (Θ' f : H') = α (Θ f : H) := by
    rw [hΘ', heT, MulEquiv.trans_apply]
    exact Subgroup.coe_equivMapOfInjective_apply T α.toMonoidHom α.injective (Θ f)
  refine ⟨Θ', ?_, ?_⟩
  · intro g' hg'
    have hg : ∀ s ∈ T, α.symm g' * s * (α.symm g')⁻¹ ∈ T := by
      intro s hs
      have h1 : g' * α s * g'⁻¹ ∈ T.map α.toMonoidHom :=
        hg' (α s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
      obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp h1
      have h2 : g' * α s * g'⁻¹ = α (α.symm g' * s * (α.symm g')⁻¹) := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← α.injective (hye.trans h2)]
      exact hy
    have hfun : (fun f => Θ'.symm ⟨g' * (Θ' f : H') * g'⁻¹, hg' _ (Θ' f).2⟩) =
        fun f => Θ.symm ⟨α.symm g' * (Θ f : H) * (α.symm g')⁻¹, hg _ (Θ f).2⟩ := by
      funext f
      apply Θ'.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply]
      have hR : (Θ' (Θ.symm ⟨α.symm g' * (Θ f : H) * (α.symm g')⁻¹,
            hg _ (Θ f).2⟩) : H') = α (α.symm g' * (Θ f : H) * (α.symm g')⁻¹) := by
        rw [hΘ', heT, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        exact Subgroup.coe_equivMapOfInjective_apply T α.toMonoidHom α.injective _
      change g' * (Θ' f : H') * g'⁻¹ =
        (Θ' (Θ.symm ⟨α.symm g' * (Θ f : H) * (α.symm g')⁻¹, hg _ (Θ f).2⟩) : H')
      rw [hR, hcoord f, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hfun]
    exact hΘ (α.symm g') hg
  · rintro t' ht' hsp'
    set t : ↥T := eT.symm t' with ht
    have htα : (t' : H') = α (t : H) := by
      have h1 : eT t = t' := MulEquiv.apply_symm_apply eT t'
      rw [← h1]
      exact Subgroup.coe_equivMapOfInjective_apply T α.toMonoidHom α.injective t
    have htne : t ≠ 1 := by
      intro h1
      apply ht'
      rw [← MulEquiv.apply_symm_apply eT t', ← ht, h1, map_one]
    have hcoordt : Θ'.symm t' = Θ.symm t := by
      rw [hΘ', ht]
      rfl
    have hsp_t : GGCoordSparse (Θ.symm t) := by
      rwa [← hcoordt]
    obtain ⟨K, hK, huniq, hcent, h7⟩ := hsp t htne hsp_t
    refine ⟨K.map α.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · have hOpen : CFSG.Open.IsComponentOf K
          (Subgroup.centralizer ({(t : H)} : Set H)) := isComponentOf_iff_open.mp hK
      have himg := CFSG.isComponentOf_map_mulEquiv α hOpen
      rw [isComponentOf_iff_open]
      convert himg using 1
      rw [← CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq α
        ({(t : H)} : Set H)]
      simp only [Set.image_singleton]
      rw [← htα]
    · intro K'' hK''
      have hOpen : CFSG.Open.IsComponentOf K''
          (Subgroup.centralizer ({(t' : H')} : Set H')) := isComponentOf_iff_open.mp hK''
      have himg := CFSG.isComponentOf_map_mulEquiv α.symm hOpen
      have hback : CFSG.Assembly.IsComponentOf (K''.map α.symm.toMonoidHom)
          (Subgroup.centralizer ({(t : H)} : Set H)) := by
        rw [isComponentOf_iff_open]
        convert himg using 1
        rw [← CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq α.symm
          ({(t' : H')} : Set H')]
        simp only [Set.image_singleton]
        rw [show α.symm (t' : H') = (t : H) from by
          rw [htα, MulEquiv.symm_apply_apply]]
      have hEqK := huniq _ hback
      have hmapback : (K''.map α.symm.toMonoidHom).map α.toMonoidHom = K'' := by
        rw [Subgroup.map_map]
        simp
      rw [← hmapback, hEqK]
    · have hcentK : Subgroup.centralizer ((K.map α.toMonoidHom : Subgroup H') : Set H') =
          (Subgroup.centralizer (K : Set H)).map α.toMonoidHom := by
        rw [← CFSG.OrderReductions.NormalizerAuxiliary.centralizer_image_eq α (K : Set H)]
        congr 1
      have hEq : T.map α.toMonoidHom ⊓
            Subgroup.centralizer ((K.map α.toMonoidHom : Subgroup H') : Set H') =
          (T ⊓ Subgroup.centralizer (K : Set H)).map α.toMonoidHom := by
        rw [hcentK, ← Subgroup.map_inf_eq T (Subgroup.centralizer (K : Set H))
          α.toMonoidHom α.injective]
      calc
        T.map α.toMonoidHom ⊓
            Subgroup.centralizer ((K.map α.toMonoidHom : Subgroup H') : Set H') =
            (T ⊓ Subgroup.centralizer (K : Set H)).map α.toMonoidHom := hEq
        _ = (Subgroup.zpowers (t : H)).map α.toMonoidHom := by rw [hcent]
        _ = Subgroup.zpowers (α (t : H)) := MonoidHom.map_zpowers α.toMonoidHom (t : H)
        _ = Subgroup.zpowers (t' : H') := by rw [htα]
    · rw [← Nat.card_congr
        (Subgroup.equivMapOfInjective K α.toMonoidHom α.injective).toEquiv]
      exact h7

theorem GGSecFiveBNativeSparseAt.of_torus (τ : (Fin r → Multiplicative (ZMod p)) →* H)
    (hτ : Function.Injective τ)
    (hsign : ∀ g : H, (∀ s ∈ τ.range, g * s * g⁻¹ ∈ τ.range) →
      ∃ u : (Fin r → Multiplicative (ZMod p)) → (Fin r → Multiplicative (ZMod p)),
        SpCoord.IsSignedPerm u ∧ ∀ f, g * τ f * g⁻¹ = τ (u f))
    (hsparse : ∀ f : Fin r → Multiplicative (ZMod p), f ≠ 1 → GGCoordSparse f →
      ∃ K : Subgroup H,
        CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({τ f} : Set H)) ∧
        (∀ K' : Subgroup H,
          CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({τ f} : Set H)) → K' = K) ∧
        τ.range ⊓ Subgroup.centralizer (K : Set H) = Subgroup.zpowers (τ f) ∧ 7 ∣ Nat.card K) :
    GGSecFiveBNativeSparseAt H p r τ.range := by
  set Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥τ.range := MonoidHom.ofInjective hτ with hΘ
  have hΘapply (f : Fin r → Multiplicative (ZMod p)) : (Θ f : H) = τ f := by
    rw [hΘ]
    exact MonoidHom.ofInjective_apply hτ
  refine ⟨Θ, ?_, ?_⟩
  · intro g hg
    obtain ⟨u, hu, huapp⟩ := hsign g hg
    have hfun : (fun f => Θ.symm ⟨g * (Θ f : H) * g⁻¹, hg _ (Θ f).2⟩) = u := by
      funext f
      apply Θ.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply]
      simpa only [hΘapply f, hΘapply (u f)] using huapp f
    rw [hfun]
    exact hu
  · rintro t ht hsp
    have htH : (t : H) = τ (Θ.symm t) := by
      rw [← hΘapply (Θ.symm t), MulEquiv.apply_symm_apply]
    have htne : Θ.symm t ≠ 1 := by
      intro h1
      apply ht
      rw [← MulEquiv.apply_symm_apply Θ t, h1, map_one]
    obtain ⟨K, hK, huniq, hcent, h7⟩ := hsparse (Θ.symm t) htne hsp
    rw [← htH] at hK huniq hcent
    exact ⟨K, hK, huniq, hcent, h7⟩

theorem GGSecFiveBNativeSparseRow.of_std {T₀ : Subgroup H} (h₀ : GGSecFiveBNativeSparseAt H p r T₀)
    (hconj : ∀ T : Subgroup H, IsElemAbelian p T → Nat.card T = p ^ r →
      ∃ α : H ≃* H, T = T₀.map α.toMonoidHom) :
    GGSecFiveBNativeSparseRow H p r := by
  intro T hT hcard
  obtain ⟨α, hα⟩ := hconj T hT hcard
  rw [hα]
  exact h₀.map_mulEquiv α

theorem GGSecFiveBNativeSparseRow.of_mulEquiv (α : H ≃* H') (h : GGSecFiveBNativeSparseRow H p r) :
    GGSecFiveBNativeSparseRow H' p r := by
  intro T' hT' hcard'
  have hT : IsElemAbelian p (T'.map α.symm.toMonoidHom) := hT'.map α.symm.toMonoidHom
  have hcard : Nat.card (T'.map α.symm.toMonoidHom) = p ^ r := by
    rw [← hcard', Nat.card_congr (Subgroup.equivMapOfInjective T' α.symm.toMonoidHom
      α.symm.injective).toEquiv]
  have hmap : (T'.map α.symm.toMonoidHom).map α.toMonoidHom = T' := by
    rw [Subgroup.map_map]
    simp
  have hAt := h _ hT hcard
  simpa only [hmap] using hAt.map_mulEquiv α

end CFSG.StandardType

end
