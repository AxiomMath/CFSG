module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporKRest_generating_of_closure {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (S : Sylow p K) {x₀ x : K} (hx : IsConj x₀ x) (T : Set K)
    (hT : ∀ z ∈ T, ∃ g : K, ∃ y ∈ (S : Subgroup K), g⁻¹ * x₀ * g = y ∧
      z ∈ Subgroup.centralizer ({y} : Set K))
    (hgen : Subgroup.closure ((S : Set K) ∪ T) = ⊤) : SporKRestGenerating p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : MulAction.IsPretransitive K (Sylow p K) :=
    Sylow.isPretransitive_of_finite (p := p) (G := K)
  intro Y hY hctrl
  obtain ⟨S', hS'Y⟩ := hY
  obtain ⟨c, hc⟩ := MulAction.IsPretransitive.exists_smul_eq (M := K) (α := Sylow p K) S' S
  let a : MulAut K := MulAut.conj c
  have hS : (S : Subgroup K) = (S' : Subgroup K).map a.toMonoidHom := by
    have hc' : ((c • S' : Sylow p K) : Subgroup K) = (S : Subgroup K) :=
      congrArg (fun P : Sylow p K => (P : Subgroup K)) hc
    rw [← hc']
    ext x
    change x ∈ (((c • S' : Sylow p K) : Set K)) ↔
      x ∈ (((S' : Subgroup K).map a.toMonoidHom) : Set K)
    rw [Sylow.coe_smul, Subgroup.coe_map]
    simp only [Set.mem_smul_set, Set.mem_image, MulAut.conj_apply]
    constructor <;> rintro ⟨y, hy, hyx⟩ <;> exact ⟨y, hy, hyx⟩
  have hSY₁ : (S : Subgroup K) ≤ Y.map a.toMonoidHom := by
    rw [hS]
    exact Subgroup.map_mono hS'Y
  have hconj : IsConj x (a x) :=
    isConj_iff.mpr ⟨c, by simp [a, MulAut.conj_apply]⟩
  obtain ⟨e, he⟩ := isConj_iff.mp (hx.trans hconj)
  have hmem : ∀ z : K, z ∈ Y.map a.toMonoidHom ↔ a⁻¹ z ∈ Y := by
    intro z
    rw [Subgroup.mem_map_equiv]
    rfl
  have hctrl₁ : SporKRestControlsAt (a x) (Y.map a.toMonoidHom) := by
    intro g hg
    rw [hmem] at hg ⊢
    have hcomp : a⁻¹ (g⁻¹ * a x * g) = (a⁻¹ g)⁻¹ * x * (a⁻¹ g) := by
      simp [a, MulAut.conj_apply]
      group
    rw [hcomp] at hg
    exact hctrl (a⁻¹ g) hg
  have hcl : Subgroup.closure ((S : Set K) ∪ T) ≤ Y.map a.toMonoidHom := by
    rw [Subgroup.closure_le, Set.union_subset_iff]
    constructor
    · intro s hs
      exact hSY₁ hs
    · intro z hz
      obtain ⟨g, y, hyS, hgy, hzcent⟩ := hT z hz
      have hx₀ : x₀ = e⁻¹ * a x * e := by
        calc x₀ = e⁻¹ * (e * x₀ * e⁻¹) * e := by group
          _ = e⁻¹ * (a x) * e := by rw [he]
      have hy_eq : y = (e * g)⁻¹ * a x * (e * g) := by
        rw [← hgy, hx₀]
        group
      have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp hzcent
      have hzy' : z⁻¹ * y * z = y := by
        rw [mul_assoc, ← hzy]
        group
      have heg : e * g ∈ Y.map a.toMonoidHom := by
        apply hctrl₁
        rw [← hy_eq]
        exact hSY₁ hyS
      have hw : (e * g) * z ∈ Y.map a.toMonoidHom := by
        apply hctrl₁
        have hc1 : ((e * g) * z)⁻¹ * a x * ((e * g) * z) = z⁻¹ * y * z := by
          rw [hy_eq]
          group
        rw [hc1, hzy']
        exact hSY₁ hyS
      have hz_eq : z = (e * g)⁻¹ * ((e * g) * z) := by group
      rw [hz_eq]
      exact (Y.map a.toMonoidHom).mul_mem ((Y.map a.toMonoidHom).inv_mem heg) hw
  have hYtop : Y.map a.toMonoidHom = ⊤ :=
    eq_top_iff.mpr (by rw [← hgen]; exact hcl)
  rw [← Subgroup.comap_map_eq_self_of_injective (f := a.toMonoidHom) a.injective Y, hYtop,
    Subgroup.comap_top]

theorem SporKRestGenerating.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {p : ℕ}
    {x : K} (h : SporKRestGenerating p x) : SporKRestGenerating p (e x) := by
  intro Y' hY' hctrl'
  obtain ⟨S', hS'⟩ := hY'
  have hrange : (S' : Subgroup K') ≤ e.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr e.surjective]
    exact le_top
  have hctrl : SporKRestControlsAt x (Y'.comap e.toMonoidHom) := by
    intro g hg
    rw [Subgroup.mem_comap] at hg ⊢
    have hthis : e.toMonoidHom (g⁻¹ * x * g) = (e g)⁻¹ * e x * e g := by
      simp [map_mul, map_inv]
    rw [hthis] at hg
    exact hctrl' (e g) hg
  have hinj : Function.Injective e.toMonoidHom := by
    intro a b hab
    exact e.injective (by simpa using hab)
  have hYtop : Y'.comap e.toMonoidHom = ⊤ :=
    h (Y'.comap e.toMonoidHom)
      ⟨S'.comapOfInjective e.toMonoidHom hinj hrange,
        by rw [Sylow.coe_comapOfInjective]; exact Subgroup.comap_mono hS'⟩ hctrl
  rw [Subgroup.eq_top_iff'] at hYtop ⊢
  intro y
  obtain ⟨x₀, rfl⟩ := e.surjective y
  exact hYtop x₀

theorem SporKRestCover.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {p : ℕ}
    (h : SporKRestCover p K) : SporKRestCover p K' := by
  intro E' hE' hcard
  have hcardE : Nat.card (E'.comap e.toMonoidHom) = Nat.card E' := by
    have h1 := Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
      (K := E'.comap e.toMonoidHom)
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr e.surjective, top_inf_eq] at h1
    exact h1.symm
  have hE : IsElemAbelian p (E'.comap e.toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨fun u v => ?_⟩⟩
      apply Subtype.ext
      apply e.injective
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val
        (hE'.1.is_comm.comm ⟨e ↑u, (Subgroup.mem_comap.mp u.2)⟩
          ⟨e ↑v, (Subgroup.mem_comap.mp v.2)⟩)
    · intro u hu
      rw [Subgroup.mem_comap] at hu
      have hup : (e u) ^ p = 1 := hE'.2 (e u) hu
      apply e.injective
      rw [map_pow, hup, map_one]
  obtain ⟨x, hxE, hxne, hxgen⟩ :=
    h (E'.comap e.toMonoidHom) hE (by rw [hcardE]; exact hcard)
  refine ⟨e x, (Subgroup.mem_comap.mp hxE), ?_, ?_⟩
  · intro hx1
    apply hxne
    apply e.injective
    rw [hx1, map_one]
  · exact SporKRestGenerating.of_mulEquiv e hxgen

end CFSG.StandardType.SporadicShape
