module

public import CFSG.Quasithin.Background.AutOnFixV
public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Vol2.Ch10SecABasicOrbit

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

section Internal

variable {G : Type} [Group G]

theorem coe_conjAct_apply' {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = g * v * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V (Subgroup.inclusion le_rfl g) v

theorem mem_autOn_iff' {X V : Subgroup G} {φ : MulAut ↥V} :
    φ ∈ autOn X V ↔ ∃ g : Subgroup.normalizer (V : Set G), (g : G) ∈ X ∧ conjAct V g = φ :=
  CFSG.Quasithin.AutOn.mem_autOn_iff

theorem autOn_sup_eq {V X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    autOn (X ⊔ Y) V = autOn X V ⊔ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hX hY

theorem commV_autOn_eq {V X : Subgroup G} [IsMulCommutative ↥V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    commV (autOn X V) = (⁅V, X⁆).subgroupOf V :=
  CFSG.Quasithin.AutOn.commV_autOn_eq hXV

theorem mem_fixV_autOn {V X : Subgroup G} [IsMulCommutative ↥V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    v ∈ fixV (autOn X V) ↔ (v : G) ∈ Subgroup.centralizer (X : Set G) :=
  CFSG.Quasithin.AutOn.mem_fixV_autOn_iff hXV v

theorem conj_conjAct {V : Subgroup G} (s n : Subgroup.normalizer (V : Set G)) :
    MulAut.conj (conjAct V s)⁻¹ (conjAct V n) = conjAct V (s⁻¹ * n * s) := by
  rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]

theorem autOn_conjugate {V X : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (V : Set G)) :
    autOn (CFSG.conjugate X t) V =
      (autOn X V).map (MulAut.conj (conjAct V ⟨t, ht⟩)⁻¹).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autOn_iff'.mp hφ
    rw [mem_conjugate_iff] at hg
    set n : Subgroup.normalizer (V : Set G) := ⟨t, ht⟩ * g * ⟨t, ht⟩⁻¹ with hn
    refine ⟨conjAct V n, mem_autOn_iff'.mpr ⟨n, hg, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, conj_conjAct]
    congr 1
    rw [hn]
    group
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autOn_iff'.mp hψ
    refine mem_autOn_iff'.mpr ⟨⟨t, ht⟩⁻¹ * g * ⟨t, ht⟩, ?_, ?_⟩
    · rw [mem_conjugate_iff]
      simpa [mul_assoc] using hg
    · rw [MulEquiv.coe_toMonoidHom, conj_conjAct]

theorem subgroupOf_conjugate {V W : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) :
    (CFSG.conjugate W t).subgroupOf V =
      (W.subgroupOf V).map (conjAct V ⟨t, ht⟩)⁻¹.toMonoidHom := by
  have hinv : ∀ v : ↥V, (((conjAct V ⟨t, ht⟩)⁻¹ v : ↥V) : G) = t⁻¹ * v * t := by
    intro v
    rw [← map_inv, coe_conjAct_apply']
    simp
  ext v
  rw [Subgroup.mem_subgroupOf, mem_conjugate_iff]
  constructor
  · intro hv
    refine ⟨conjAct V ⟨t, ht⟩ v, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_conjAct_apply']
      exact hv
    · show ((conjAct V ⟨t, ht⟩)⁻¹ * conjAct V ⟨t, ht⟩) v = v
      rw [inv_mul_cancel, MulAut.one_apply]
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
    rw [MulEquiv.coe_toMonoidHom, hinv]
    simpa [mul_assoc] using hw

end Internal

section Transport

variable {V : Type} [CommGroup V]

@[expose] noncomputable def conjEquivMap (H : Subgroup (MulAut V)) (σ : MulAut V) :
    ↥H ≃* ↥(H.map (MulAut.conj σ).toMonoidHom) :=
  Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective

theorem realizesVia_map_conj {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (σ : MulAut V) :
    D.RealizesVia (H.map (MulAut.conj σ).toMonoidHom) (U.map σ.toMonoidHom)
      (Z.map σ.toMonoidHom) ((conjEquivMap H σ).toMonoidHom.comp π) := by
  obtain ⟨hπ, hZU, hks, hU, hZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hconj : ∀ (x : MulAut V) (v : V), (MulAut.conj σ x) (σ v) = σ (x v) := by
    intro x v
    simp [MulAut.conj_apply, MulAut.mul_apply]
  refine ⟨(conjEquivMap H σ).surjective.comp hπ, Subgroup.map_mono hZU, hks, ?_, ?_, hsec,
    hker, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩ _ ⟨u, hu, rfl⟩
    exact ⟨x u, hU ⟨x, hx⟩ u hu, (hconj x u).symm⟩
  · rintro ⟨_, x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    exact ⟨x z, hZ ⟨x, hx⟩ z hz, (hconj x z).symm⟩
  · set e : ↥U ≃* ↥(U.map σ.toMonoidHom) :=
      Subgroup.equivMapOfInjective U σ.toMonoidHom σ.injective with he
    have hev : ∀ u : ↥U, ((e u : ↥(U.map σ.toMonoidHom)) : V) = σ u := fun u =>
      Subgroup.coe_equivMapOfInjective_apply U σ.toMonoidHom σ.injective u
    refine ⟨β.comp e.symm.toMonoidHom, hβs.comp e.symm.surjective, fun u => ?_, ?_⟩
    · obtain ⟨u, rfl⟩ := e.surjective u
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply]
      rw [hβk u, hev]
      constructor
      · intro hz
        exact ⟨u, hz, rfl⟩
      · rintro ⟨z, hz, hzu⟩
        rwa [← σ.injective hzu]
    · intro γ u m hu hm hβum
      obtain ⟨u, rfl⟩ := e.surjective u
      have hβum' : β u = QuotientGroup.mk m := by
        change β (e.symm (e u)) = _ at hβum
        rwa [MulEquiv.symm_apply_apply] at hβum
      have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hU (π γ) u u.2
      have h1 := hβe γ u m hu' hm hβum'
      have h2 : e.symm ⟨_, hu⟩ = ⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ := by
        rw [MulEquiv.symm_apply_eq]
        apply Subtype.ext
        change (MulAut.conj σ ((π γ : ↥H) : MulAut V)) ((e u : ↥(U.map σ.toMonoidHom)) : V) =
          ((e ⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥(U.map σ.toMonoidHom)) : V)
        rw [hev, hev, hconj]
      change β (e.symm ⟨_, hu⟩) = _
      rw [h2]
      exact h1

theorem directSumOfCopies_map_conj {D : FFModel} {H : Subgroup (MulAut V)} {U : Subgroup V}
    {k : ℕ} (h : DirectSumOfCopies H U ⊥ D k) (σ : MulAut V) :
    DirectSumOfCopies (H.map (MulAut.conj σ).toMonoidHom) (U.map σ.toMonoidHom) ⊥ D k := by
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := h
  refine ⟨fun i => (I i).map σ.toMonoidHom, (conjEquivMap H σ).toMonoidHom.comp π,
    fun _ => bot_le, fun i => ?_, ?_, fun i => ?_⟩
  · have h := congrArg (Subgroup.map σ.toMonoidHom) (hind i)
    rw [Subgroup.map_inf_eq _ _ σ.toMonoidHom σ.injective, Subgroup.map_sup, Subgroup.map_bot,
      Subgroup.map_iSup] at h
    simp only [Subgroup.map_iSup] at h
    exact h
  · rw [← hsup, Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup]
  · have h := realizesVia_map_conj (hreal i) σ
    rwa [Subgroup.map_bot] at h

theorem commV_map_conj (H : Subgroup (MulAut V)) (σ : MulAut V) :
    commV (H.map (MulAut.conj σ).toMonoidHom) = (commV H).map σ.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq H σ

end Transport

end CFSG.Quasithin.Vol2.Ch10.SecA
