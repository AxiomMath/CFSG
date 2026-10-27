module

public import CFSG.Quasithin.Background.F918Z8Def
public import CFSG.Quasithin.Background.F918H0
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Conjugation

variable {W : Type} [CommGroup W]

theorem d321b_conjAutSub_mul (a b : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub (a * b) X = conjAutSub a (conjAutSub b X) := by
  ext x
  simp only [mem_conjAutSub_iff]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

theorem d321b_commV_conjAutSub (g : MulAut W) (K : Subgroup (MulAut W)) :
    commV (conjAutSub g K) = (commV K).map g.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq K g

theorem d321b_fixV_conjAutSub (g : MulAut W) (A : Subgroup (MulAut W)) :
    fixV (conjAutSub g A) = (fixV A).map g.toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq A g

theorem d321b_map_map_inv (g : MulAut W) (U : Subgroup W) :
    (U.map g.toMonoidHom).map g⁻¹.toMonoidHom = U := by
  ext x
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    simpa using hu
  · intro hx
    exact ⟨g x, ⟨x, hx, rfl⟩, by simp⟩

theorem d321b_isSumMod_symm {C A B Tot : Subgroup W} (h : IsSumMod C A B Tot) :
    IsSumMod C B A Tot := by
  refine ⟨?_, ?_⟩
  · rw [h.1, sup_comm A B]
  · rw [inf_comm]
    exact h.2

end Conjugation

section Transport

variable {W : Type} [CommGroup W]

@[expose] noncomputable def d321b_conjEquiv (g : MulAut W) (H : Subgroup (MulAut W)) :
    ↥H ≃* ↥(conjAutSub g H) :=
  Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem d321b_conjEquiv_coe (g : MulAut W) (H : Subgroup (MulAut W)) (h : ↥H) :
    ((d321b_conjEquiv g H h : ↥(conjAutSub g H)) : MulAut W) = g * (h : MulAut W) * g⁻¹ := by
  rfl

@[expose] noncomputable def d321b_mapEquiv (g : MulAut W) (U : Subgroup W) :
    ↥U ≃* ↥(U.map g.toMonoidHom) :=
  Subgroup.equivMapOfInjective U g.toMonoidHom g.injective

theorem d321b_mapEquiv_coe (g : MulAut W) (U : Subgroup W) (u : ↥U) :
    ((d321b_mapEquiv g U u : ↥(U.map g.toMonoidHom)) : W) = g (u : W) := by
  rfl

theorem d321b_realizes_map (g : MulAut W) {D : FFModel} {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    D.RealizesVia (conjAutSub g H) (U.map g.toMonoidHom) (Z.map g.toMonoidHom)
      ((d321b_conjEquiv g H).toMonoidHom.comp π) := by
  obtain ⟨hsurj, hZU, hkerSec, hUinv, hZinv, hsecInv, hkerInv, β, hβs, hβk, hβe⟩ := h
  refine ⟨(d321b_conjEquiv g H).surjective.comp hsurj, Subgroup.map_mono hZU, hkerSec, ?_, ?_,
    hsecInv, hkerInv, β.comp (d321b_mapEquiv g U).symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro ⟨h', hh'⟩ _ ⟨u, hu, rfl⟩
    have h1 : g⁻¹ * h' * g ∈ H := mem_conjAutSub_iff.1 hh'
    refine ⟨(g⁻¹ * h' * g) u, hUinv ⟨_, h1⟩ u hu, ?_⟩
    simp [MulAut.mul_apply]
  · rintro ⟨h', hh'⟩ _ ⟨z, hz, rfl⟩
    have h1 : g⁻¹ * h' * g ∈ H := mem_conjAutSub_iff.1 hh'
    refine ⟨(g⁻¹ * h' * g) z, hZinv ⟨_, h1⟩ z hz, ?_⟩
    simp [MulAut.mul_apply]
  · exact hβs.comp (d321b_mapEquiv g U).symm.surjective
  · intro u'
    obtain ⟨u, rfl⟩ := (d321b_mapEquiv g U).surjective u'
    have h1 : (g (u : W) ∈ Z.map g.toMonoidHom) ↔ (u : W) ∈ Z :=
      Subgroup.mem_map_iff_mem (f := g.toMonoidHom) g.injective
    rw [d321b_mapEquiv_coe, h1]
    show β ((d321b_mapEquiv g U).symm (d321b_mapEquiv g U u)) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply]
    exact hβk u
  · intro γ u' m hu' hm hβu
    obtain ⟨u, rfl⟩ := (d321b_mapEquiv g U).surjective u'
    have hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U := hUinv (π γ) u u.2
    have h1 : ((((d321b_conjEquiv g H).toMonoidHom.comp π) γ : ↥(conjAutSub g H)) : MulAut W) =
        g * ((π γ : ↥H) : MulAut W) * g⁻¹ := d321b_conjEquiv_coe g H (π γ)
    have heq : (⟨(((d321b_conjEquiv g H).toMonoidHom.comp π) γ : MulAut W)
          (d321b_mapEquiv g U u : W), hu'⟩ : ↥(U.map g.toMonoidHom)) =
        d321b_mapEquiv g U ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ := by
      refine Subtype.ext ?_
      change ((((d321b_conjEquiv g H).toMonoidHom.comp π) γ : ↥(conjAutSub g H)) : MulAut W)
          (d321b_mapEquiv g U u : W) =
        (d321b_mapEquiv g U ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ : W)
      rw [h1, d321b_mapEquiv_coe, d321b_mapEquiv_coe]
      simp [MulAut.mul_apply]
    have hβu' : β u = QuotientGroup.mk m := by
      have : β ((d321b_mapEquiv g U).symm (d321b_mapEquiv g U u)) = QuotientGroup.mk m := hβu
      rwa [MulEquiv.symm_apply_apply] at this
    have key := hβe γ u m hu hm hβu'
    rw [heq]
    show β ((d321b_mapEquiv g U).symm (d321b_mapEquiv g U _)) = _
    rw [MulEquiv.symm_apply_apply]
    exact key

theorem d321b_directSum_map (g : MulAut W) {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    {D : FFModel} {k : ℕ} (h : DirectSumOfCopies L U Z D k) :
    DirectSumOfCopies (conjAutSub g L) (U.map g.toMonoidHom) (Z.map g.toMonoidHom) D k := by
  obtain ⟨I, π, hZI, hind, hsup, hreal⟩ := h
  refine ⟨fun i => (I i).map g.toMonoidHom, (d321b_conjEquiv g L).toMonoidHom.comp π,
    fun i => Subgroup.map_mono (hZI i), fun i => ?_, ?_, fun i => d321b_realizes_map g (hreal i)⟩
  · have h1 : (⨆ (j : Fin k) (_ : j ≠ i), (I j).map g.toMonoidHom) =
        (⨆ (j : Fin k) (_ : j ≠ i), I j).map g.toMonoidHom := by
      simp only [Subgroup.map_iSup]
    rw [h1, ← Subgroup.map_sup, ← Subgroup.map_inf _ _ _ g.injective, hind i]
  · rw [← hsup, Subgroup.map_sup, Subgroup.map_iSup]

end Transport

section Shapes

variable {W : Type} [CommGroup W]

theorem d321b_two_conj (g : MulAut W) {L : Subgroup (MulAut W)} (h : D321Two L) :
    D321Two (conjAutSub g L) := by
  refine And.intro (isPSL_congr (d321b_conjEquiv g L) h.1) ?_
  have h1 := d321b_directSum_map g h.2
  rw [d321b_commV_conjAutSub]
  simpa [Subgroup.map_bot] using h1

theorem d321b_three_conj (g : MulAut W) {Mp L : Subgroup (MulAut W)}
    (hg : (fixV Mp).map g.toMonoidHom = fixV Mp) (h : D321Three Mp L) :
    D321Three Mp (conjAutSub g L) := by
  obtain ⟨n, hpsl, K, hK, hfin, hcard, hds⟩ := h
  refine ⟨n, isPSL_congr (d321b_conjEquiv g L) hpsl, K, hK, hfin, hcard, ?_⟩
  have h1 := d321b_directSum_map g hds
  rw [Subgroup.map_inf _ _ _ g.injective, hg] at h1
  rw [d321b_commV_conjAutSub]
  exact h1

end Shapes

section Symmetry

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d321b_conj_conj (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L) :
    conjAutSub t (conjAutSub t L) = L := by
  rcases (hL38 W M Mp T L V hstd t htT htL hMp).2.2.2 (t * t) (T.mul_mem htT htT) with h | h
  · rwa [d321b_conjAutSub_mul] at h
  · exfalso
    rw [d321b_conjAutSub_mul] at h
    have h' : conjAutSub t L = L := by
      have := congrArg (conjAutSub t⁻¹) h
      rwa [conjAutSub_inv_conjAutSub, conjAutSub_inv_conjAutSub] at this
    exact htL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h')

theorem d321b_fixV_map_inv (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L) :
    (fixV Mp).map t⁻¹.toMonoidHom = fixV Mp := by
  have h1 := d321b_conj_conj hL38 hstd htT htL hMp
  have h2 : conjAutSub t⁻¹ L = conjAutSub t L := by
    have := congrArg (conjAutSub t⁻¹) h1
    rw [conjAutSub_inv_conjAutSub] at this
    exact this.symm
  have h3 : conjAutSub t⁻¹ Mp = Mp := by
    have e1 : conjAutSub t⁻¹ (L ⊔ conjAutSub t L) =
        conjAutSub t⁻¹ L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := Subgroup.map_sup _ _ _
    rw [hMp, e1, h2, conjAutSub_inv_conjAutSub, sup_comm]
  rw [← d321b_fixV_conjAutSub, h3]

theorem d321_concl_symm (hL38 : D3L38) (hstd : D3Std M Mp T L V) (htT : t ∈ T)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (h : D321Concl Mp (conjAutSub t L) t⁻¹) : D321Concl Mp L t := by
  have hLL : conjAutSub t⁻¹ (conjAutSub t L) = L := conjAutSub_inv_conjAutSub L t
  have hLt2 := d321b_conj_conj hL38 hstd htT htL hMp
  have hfix := d321b_fixV_map_inv hL38 hstd htT htL hMp
  unfold D321Concl at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [d321b_commV_conjAutSub, d321b_map_map_inv] at h1
    exact d321b_isSumMod_symm h1
  · rw [hLL] at h2
    have h2' := Subgroup.map_mono (f := t.toMonoidHom) h2
    rw [← d321b_commV_conjAutSub, hLt2, ← d321b_fixV_conjAutSub] at h2'
    exact h2'
  · rcases h3 with h3 | h3
    · left
      have := d321b_two_conj t⁻¹ h3
      rwa [hLL] at this
    · right
      have := d321b_three_conj t⁻¹ hfix h3
      rwa [hLL] at this

end Symmetry

end CFSG.Quasithin
