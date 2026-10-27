module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixModel
public import CFSG.Quasithin.H13.VolIAltCoverSixData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Open Subgroup Equiv
open CFSG.Quasithin.H13.VolI

private theorem s1611e3_permAct_allOnes (n : ℕ) (σ : Perm (Fin n)) :
    permAct n σ (allOnes n) = allOnes n := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply]
  rfl

private theorem s1611e3_coreAct_sixZ (σ : Perm (Fin 6)) :
    coreAct 6 σ sixZ = sixZ := by
  apply Subtype.ext
  rw [coreAct_coe]
  exact s1611e3_permAct_allOnes 6 σ

private theorem s1611e3_coreAct_zpowers_sixZ (σ : Perm (Fin 6)) {x : SixE6}
    (hx : x ∈ Subgroup.zpowers sixZ) : coreAct 6 σ x = x := by
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← hz, map_zpow, s1611e3_coreAct_sixZ]

private theorem s1611e3_quotientRange_apply {A B : Type*} [Group A] [Group B]
    (f : A →* B) {I : Subgroup B} (hf : f.range = I) (a : A) :
    (((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hf))
        (QuotientGroup.mk a) : B) = f a := by
  show (MulEquiv.subgroupCongr hf (QuotientGroup.quotientKerEquivRange f
      (QuotientGroup.mk a)) : B) = f a
  rw [show QuotientGroup.quotientKerEquivRange f (QuotientGroup.mk a) =
      ⟨f a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ from rfl]
  rfl

theorem s1611e3_six_not_inner {W' : Type} [CommGroup W'] [Finite W'] {L' : Subgroup (MulAut W')}
    {I₁ I₂ : Subgroup W'} (hinf : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (ρ₁ ρ₂ : ↥(alternatingGroup (Fin 6)) →* ↥L') (β₁ β₂ : SixE6 →* W')
    (hβ₁ : β₁.range = I₁) (hβ₂ : β₂.range = I₂)
    (hk₁ : β₁.ker = Subgroup.zpowers sixZ) (hk₂ : β₂.ker = Subgroup.zpowers sixZ)
    (he₁ : ∀ (a : ↥(alternatingGroup (Fin 6))) (x : SixE6),
      β₁ (CFSG.Quasithin.H13.VolI.act6 a x) = ((ρ₁ a : ↥L') : MulAut W') (β₁ x))
    (he₂ : ∀ (a : ↥(alternatingGroup (Fin 6))) (x : SixE6),
      β₂ (CFSG.Quasithin.H13.VolI.act6 a x) = ((ρ₂ a : ↥L') : MulAut W') (β₂ x))
    (hL₁ : Function.Surjective ρ₁) (hL₂ : Function.Surjective ρ₂)
    {s : Perm (Fin 6)}
    (hs : ∀ a : ↥(alternatingGroup (Fin 6)), ∃ b : ↥(alternatingGroup (Fin 6)),
      (b : Perm (Fin 6)) = s * (a : Perm (Fin 6)) * s⁻¹ ∧ ρ₂ a = ρ₁ b) :
    ∃ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), I₁.map ψ.toMonoidHom = I₂ := by
  classical
  let P : MulAut SixE6 := coreAct 6 s⁻¹
  let P' : MulAut SixE6 := coreAct 6 s
  have hfix₂ : ∀ y : SixE6, P (P' y) = y := by
    intro y
    show coreAct 6 s⁻¹ (coreAct 6 s y) = y
    simp only [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hfix₁ : ∀ y : SixE6, P' (P y) = y := by
    intro y
    show coreAct 6 s (coreAct 6 s⁻¹ y) = y
    simp only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hker_le : ∀ x ∈ β₁.ker, P x ∈ β₂.ker := by
    intro x hx
    rw [hk₁] at hx
    rw [hk₂]
    rw [show P x = x from s1611e3_coreAct_zpowers_sixZ s⁻¹ hx]
    exact hx
  have hPmap : (β₁.ker).map P.toMonoidHom = β₂.ker := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hker_le x hx
    · intro y hy
      rw [hk₂] at hy
      refine Subgroup.mem_map.mpr ⟨P' y, ?_, ?_⟩
      · rw [hk₁]
        rw [show P' y = y from s1611e3_coreAct_zpowers_sixZ s hy]
        exact hy
      · show P (P' y) = y
        exact hfix₂ y
  let q : SixE6 ⧸ β₁.ker ≃* SixE6 ⧸ β₂.ker :=
    QuotientGroup.congr β₁.ker β₂.ker P hPmap
  let e₁ : SixE6 ⧸ β₁.ker ≃* ↥I₁ :=
    (QuotientGroup.quotientKerEquivRange β₁).trans (MulEquiv.subgroupCongr hβ₁)
  let e₂ : SixE6 ⧸ β₂.ker ≃* ↥I₂ :=
    (QuotientGroup.quotientKerEquivRange β₂).trans (MulEquiv.subgroupCongr hβ₂)
  let f₁ : ↥I₁ ≃* ↥I₂ := e₁.symm.trans (q.trans e₂)
  let f₂ : ↥I₂ ≃* ↥I₁ := f₁.symm
  have m₁ : ∀ x : SixE6, β₁ x ∈ I₁ := fun x => by
    rw [← hβ₁]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  have m₂ : ∀ x : SixE6, β₂ x ∈ I₂ := fun x => by
    rw [← hβ₂]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩
  have he₁_mk : ∀ x : SixE6, e₁ (QuotientGroup.mk x) = ⟨β₁ x, m₁ x⟩ := by
    intro x
    apply Subtype.ext
    exact s1611e3_quotientRange_apply β₁ hβ₁ x
  have he₂_mk : ∀ y : SixE6, e₂ (QuotientGroup.mk y) = ⟨β₂ y, m₂ y⟩ := by
    intro y
    apply Subtype.ext
    exact s1611e3_quotientRange_apply β₂ hβ₂ y
  have hf₁_val : ∀ z : SixE6,
      ((f₁ (e₁ (QuotientGroup.mk z)) : ↥I₂) : W') = β₂ (P z) := by
    intro z
    have hq : f₁ (e₁ (QuotientGroup.mk z)) = e₂ (q (QuotientGroup.mk z)) := by
      simp only [f₁, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hq, QuotientGroup.congr_mk β₁.ker β₂.ker P hPmap z]
    exact s1611e3_quotientRange_apply β₂ hβ₂ (P z)
  have hf₁_apply : ∀ x : SixE6, ((f₁ ⟨β₁ x, m₁ x⟩ : ↥I₂) : W') = β₂ (P x) := by
    intro x
    rw [← he₁_mk x]
    exact hf₁_val x
  have hf₂_val : ∀ z : SixE6,
      ((f₂ (e₂ (QuotientGroup.mk z)) : ↥I₁) : W') = β₁ (P' z) := by
    intro z
    have hq : f₁ (e₁ (QuotientGroup.mk (P' z))) = e₂ (QuotientGroup.mk z) := by
      apply Subtype.ext
      rw [hf₁_val (P' z), hfix₂ z]
      exact (s1611e3_quotientRange_apply β₂ hβ₂ z).symm
    have hsymm : f₂ (e₂ (QuotientGroup.mk z)) = e₁ (QuotientGroup.mk (P' z)) := by
      change f₁.symm (e₂ (QuotientGroup.mk z)) = e₁ (QuotientGroup.mk (P' z))
      rw [← hq, MulEquiv.symm_apply_apply]
    rw [hsymm]
    exact s1611e3_quotientRange_apply β₁ hβ₁ (P' z)
  have hf₂_apply : ∀ y : SixE6, ((f₂ ⟨β₂ y, m₂ y⟩ : ↥I₁) : W') = β₁ (P' y) := by
    intro y
    rw [← he₂_mk y]
    exact hf₂_val y
  have hdisj : Disjoint I₁ I₂ := disjoint_iff.2 hinf
  let mulHom : ↥I₁ × ↥I₂ →* W' :=
    { toFun := fun g => (g.1 : W') * (g.2 : W')
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        ac_rfl }
  have hmul_inj : Function.Injective mulHom := Subgroup.mul_injective_of_disjoint hdisj
  have hmul_surj : Function.Surjective mulHom := by
    intro w
    have hw : w ∈ I₁ ⊔ I₂ := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, hprod⟩ := Subgroup.mem_sup.1 hw
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hprod⟩
  let mulEquiv : ↥I₁ × ↥I₂ ≃* W' := MulEquiv.ofBijective mulHom ⟨hmul_inj, hmul_surj⟩
  have hdisj₂ : Disjoint I₂ I₁ := disjoint_iff.2 (by rw [inf_comm, hinf])
  let mulHom₂ : ↥I₂ × ↥I₁ →* W' :=
    { toFun := fun g => (g.1 : W') * (g.2 : W')
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        ac_rfl }
  have hmul_inj₂ : Function.Injective mulHom₂ := Subgroup.mul_injective_of_disjoint hdisj₂
  have hmul_surj₂ : Function.Surjective mulHom₂ := by
    intro w
    have hw : w ∈ I₂ ⊔ I₁ := by rw [sup_comm, hsup]; exact Subgroup.mem_top w
    obtain ⟨y, hy, z, hz, hprod⟩ := Subgroup.mem_sup.1 hw
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), hprod⟩
  let mulEquiv₂ : ↥I₂ × ↥I₁ ≃* W' := MulEquiv.ofBijective mulHom₂ ⟨hmul_inj₂, hmul_surj₂⟩
  let ψ : W' ≃* W' := mulEquiv.symm.trans ((MulEquiv.prodCongr f₁ f₂).trans mulEquiv₂)
  have hψ_apply : ∀ (i₁ : ↥I₁) (i₂ : ↥I₂),
      ψ ((i₁ : W') * (i₂ : W')) = (f₁ i₁ : W') * (f₂ i₂ : W') := by
    intro i₁ i₂
    change ((MulEquiv.prodCongr f₁ f₂).trans mulEquiv₂)
        (mulEquiv.symm (mulEquiv (i₁, i₂))) = (f₁ i₁ : W') * (f₂ i₂ : W')
    simp only [MulEquiv.symm_apply_apply]
    rfl
  refine ⟨ψ, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro ℓ hℓ
    obtain ⟨b, hb⟩ := hL₁ ⟨ℓ, hℓ⟩
    have hb' : ((ρ₁ b : ↥L') : MulAut W') = ℓ := congrArg Subtype.val hb
    let a : ↥(alternatingGroup (Fin 6)) :=
      ⟨s⁻¹ * (b : Perm (Fin 6)) * s,
        (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem
          (b : Perm (Fin 6)) b.2 s⁻¹⟩
    have ha : (a : Perm (Fin 6)) = s⁻¹ * (b : Perm (Fin 6)) * s := rfl
    have hρ : ρ₂ a = ρ₁ b := by
      obtain ⟨c, hc, hcρ⟩ := hs a
      have hcb : c = b := Subtype.ext (by rw [hc, ha]; group)
      rw [hcρ, hcb]
    have hgroup : act6 a = P * act6 b * P' := by
      show coreAct 6 (a : Perm (Fin 6)) =
        coreAct 6 s⁻¹ * coreAct 6 (b : Perm (Fin 6)) * coreAct 6 s
      rw [ha, map_mul, map_mul]
    have hact : ∀ y, P (act6 b y) = act6 a (P y) := by
      intro y
      rw [hgroup, MulAut.mul_apply, MulAut.mul_apply, hfix₁ y]
    have hact₂ : ∀ y, P' (act6 a y) = act6 b (P' y) := by
      intro y
      rw [hgroup, MulAut.mul_apply, MulAut.mul_apply, hfix₁ (act6 b (P' y))]
    have hpres₁ : ∀ i ∈ I₁, (ℓ : MulAut W') (i : W') ∈ I₁ := by
      intro i hi
      have hi' : i ∈ β₁.range := by rwa [hβ₁]
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hi'
      rw [show (ℓ : MulAut W') (β₁ x) = β₁ (act6 b x) from by
        rw [← hb']
        exact (he₁ b x).symm]
      rw [← hβ₁]
      exact MonoidHom.mem_range.2 ⟨act6 b x, rfl⟩
    have hpres₂ : ∀ i ∈ I₂, (ℓ : MulAut W') (i : W') ∈ I₂ := by
      intro i hi
      have hi' : i ∈ β₂.range := by rwa [hβ₂]
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hi'
      rw [show (ℓ : MulAut W') (β₂ y) = β₂ (act6 a y) from by
        rw [← hb', ← hρ]
        exact (he₂ a y).symm]
      rw [← hβ₂]
      exact MonoidHom.mem_range.2 ⟨act6 a y, rfl⟩
    have hf₁_comm : ∀ i : ↥I₁,
        (f₁ ⟨(ℓ : MulAut W') (i : W'), hpres₁ i i.2⟩ : W') =
          (ℓ : MulAut W') ((f₁ i : ↥I₂) : W') := by
      intro i
      obtain ⟨x, rfl⟩ : ∃ x : SixE6, e₁ (QuotientGroup.mk x) = i := by
        obtain ⟨z, rfl⟩ := e₁.surjective i
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨x, rfl⟩
      rw [he₁_mk x]
      have hℓ_val : (ℓ : MulAut W') (β₁ x) = β₁ (act6 b x) := by
        rw [← hb']
        exact (he₁ b x).symm
      have harg : (⟨(ℓ : MulAut W') (β₁ x),
            hpres₁ (β₁ x) (m₁ x)⟩ : ↥I₁) =
          ⟨β₁ (act6 b x), m₁ (act6 b x)⟩ := Subtype.ext hℓ_val
      rw [harg, hf₁_apply (act6 b x), hf₁_apply x]
      have hℓβ : (ℓ : MulAut W') (β₂ (P x)) = β₂ (act6 a (P x)) := by
        rw [← hb', ← hρ]
        exact (he₂ a (P x)).symm
      rw [hℓβ, hact x]
    have hf₂_comm : ∀ i : ↥I₂,
        (f₂ ⟨(ℓ : MulAut W') (i : W'), hpres₂ i i.2⟩ : W') =
          (ℓ : MulAut W') ((f₂ i : ↥I₁) : W') := by
      intro i
      obtain ⟨y, rfl⟩ : ∃ y : SixE6, e₂ (QuotientGroup.mk y) = i := by
        obtain ⟨z, rfl⟩ := e₂.surjective i
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨y, rfl⟩
      rw [he₂_mk y]
      have hℓ_val₂ : (ℓ : MulAut W') (β₂ y) = β₂ (act6 a y) := by
        rw [← hb', ← hρ]
        exact (he₂ a y).symm
      have harg₂ : (⟨(ℓ : MulAut W') (β₂ y),
            hpres₂ (β₂ y) (m₂ y)⟩ : ↥I₂) =
          ⟨β₂ (act6 a y), m₂ (act6 a y)⟩ := Subtype.ext hℓ_val₂
      rw [harg₂, hf₂_apply (act6 a y), hf₂_apply y]
      have hℓβ₂ : (ℓ : MulAut W') (β₁ (P' y)) = β₁ (act6 b (P' y)) := by
        rw [← hb']
        exact (he₁ b (P' y)).symm
      rw [hℓβ₂, hact₂ y]
    apply MulEquiv.ext
    intro w
    have hw : w ∈ I₁ ⊔ I₂ := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨i₁, hi₁, i₂, hi₂, hw_eq⟩ := Subgroup.mem_sup.1 hw
    rw [← hw_eq]
    calc (ℓ * ψ) (i₁ * i₂)
        = ℓ (ψ (i₁ * i₂)) := by rw [MulAut.mul_apply]
      _ = ℓ ((f₁ ⟨i₁, hi₁⟩ : W') * (f₂ ⟨i₂, hi₂⟩ : W')) := by
            rw [hψ_apply ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩]
      _ = ℓ (f₁ ⟨i₁, hi₁⟩ : W') * ℓ (f₂ ⟨i₂, hi₂⟩ : W') := map_mul ℓ _ _
      _ = (f₁ ⟨(ℓ : MulAut W') i₁, hpres₁ i₁ hi₁⟩ : W') *
            (f₂ ⟨(ℓ : MulAut W') i₂, hpres₂ i₂ hi₂⟩ : W') := by
            rw [hf₁_comm ⟨i₁, hi₁⟩, hf₂_comm ⟨i₂, hi₂⟩]
      _ = (ψ * ℓ) (i₁ * i₂) := by
            rw [MulAut.mul_apply, map_mul]
            exact (hψ_apply ⟨(ℓ : MulAut W') i₁, hpres₁ i₁ hi₁⟩
              ⟨(ℓ : MulAut W') i₂, hpres₂ i₂ hi₂⟩).symm
  · apply le_antisymm
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Subgroup.mem_map.1 hy
      have h := hψ_apply ⟨i, hi⟩ 1
      simp only [Subgroup.coe_one, mul_one, map_one] at h
      change ψ (i : W') ∈ I₂
      rw [h]
      exact (f₁ ⟨i, hi⟩).2
    · intro y hy
      obtain ⟨i₁, hi₁⟩ := f₁.surjective ⟨y, hy⟩
      refine Subgroup.mem_map.2 ⟨(i₁ : W'), i₁.2, ?_⟩
      have h := hψ_apply i₁ 1
      simp only [Subgroup.coe_one, mul_one, map_one] at h
      change ψ (i₁ : W') = y
      rw [h]
      exact congrArg Subtype.val hi₁

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
