module

public import CFSG.Quasithin.Vol2.Ch11SecC37Syl
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

theorem mem_of_fix_of_sum {U : Type*} [CommGroup U] [Finite U] (σ : MulAut U) {C : Subgroup U}
    (hC : ∀ c ∈ C, σ c = c) {k : ℕ} (W : Fin k → Subgroup U)
    (hWσ : ∀ i, ∀ w ∈ W i, σ w ∈ W i) (hsup : (C ⊔ ⨆ i, W i) = ⊤)
    (hfpf : ∀ i, ∀ u ∈ W i, σ u * u⁻¹ ∈ C → u ∈ C) :
    ∀ u : U, σ u * u⁻¹ ∈ C → u ∈ C := by
  have hσC : C ≤ C.comap σ.toMonoidHom := fun c hc => by
    show σ c ∈ C
    rw [hC c hc]
    exact hc
  set σb : U ⧸ C →* U ⧸ C := QuotientGroup.map C C σ.toMonoidHom hσC with hσb
  set f : U ⧸ C →* U ⧸ C := σb / MonoidHom.id (U ⧸ C) with hf
  have hfmk : ∀ u : U, f (u : U ⧸ C) = ((σ u * u⁻¹ : U) : U ⧸ C) := by
    intro u
    rw [hf, MonoidHom.div_apply, hσb, QuotientGroup.map_mk, MonoidHom.id_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, div_eq_mul_inv]
    rfl
  have hrange : ∀ i, (W i).map (QuotientGroup.mk' C) ≤ f.range := by
    intro i y hy
    set Wb := (W i).map (QuotientGroup.mk' C) with hWb
    have hmaps : ∀ x ∈ Wb, f x ∈ Wb := by
      rintro _ ⟨u, hu, rfl⟩
      rw [QuotientGroup.mk'_apply, hfmk]
      exact ⟨_, (W i).mul_mem (hWσ i u hu) ((W i).inv_mem hu), rfl⟩
    let g : ↥Wb → ↥Wb := fun x => ⟨f x, hmaps x x.2⟩
    have hg : Function.Injective g := by
      intro x y hxy
      have h1 : f (x * y⁻¹ : ↥Wb) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
          show f x = f y from congrArg Subtype.val hxy, mul_inv_cancel]
      obtain ⟨u, hu, hux⟩ := (x * y⁻¹ : ↥Wb).2
      rw [← hux, QuotientGroup.mk'_apply, hfmk, QuotientGroup.eq_one_iff] at h1
      have h2 := hfpf i u hu h1
      have h3 : ((x * y⁻¹ : ↥Wb) : U ⧸ C) = 1 := by
        rw [← hux, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact h2
      have h4 : x * y⁻¹ = 1 := Subtype.ext h3
      exact mul_inv_eq_one.mp h4
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hg) ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  have hftop : f.range = ⊤ := by
    rw [eq_top_iff]
    have h1 : (⊤ : Subgroup (U ⧸ C)) = (C ⊔ ⨆ i, W i).map (QuotientGroup.mk' C) := by
      rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    rw [h1, Subgroup.map_sup, Subgroup.map_iSup]
    refine sup_le ?_ (iSup_le hrange)
    rintro _ ⟨c, hc, rfl⟩
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc]
    exact f.range.one_mem
  have hfinj : Function.Injective f :=
    Finite.injective_iff_surjective.mpr (MonoidHom.range_eq_top.mp hftop)
  intro u hu
  have h1 : f (u : U ⧸ C) = f 1 := by
    rw [hfmk, map_one, QuotientGroup.eq_one_iff]
    exact hu
  exact (QuotientGroup.eq_one_iff u).mp (hfinj h1)

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem mem_centralizer_of_fix (hG16 : ASInputs.AS_G_1_6) (hAS : FactAStarSylow)
    (hFPF : FactSL2NatFPF) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) {d : G} (hdK : d ∈ oTwoUpper H)
    (hdodd : Odd (orderOf d)) (hdV : d ∉ Subgroup.centralizer (VZ T H : Set G)) {v : G}
    (hv : v ∈ VZ T H) (hfix : d * v * d⁻¹ = v) :
    v ∈ Subgroup.centralizer (oTwoUpper H : Set G) := by
  have hc : IsMulCommutative ↥(VZ T H) := s.isElemAbelian_VZ.1
  have hKV := K_le_normalizer_VZ T H
  set σ := conjAct (VZ T H) ⟨d, hKV hdK⟩ with hσ
  have hσK : σ ∈ autOn (oTwoUpper H) (VZ T H) := conjAct_mem_autOn hKV hdK
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hdV
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h2 := congrArg Subtype.val (congrArg (fun φ : MulAut ↥(VZ T H) => φ ⟨w, hw⟩) h1)
    simp only [MulAut.one_apply] at h2
    rw [hσ, coe_conjAct_apply] at h2
    change d * w * d⁻¹ = w at h2
    calc w * d = d * w * d⁻¹ * d := by rw [h2]
      _ = d * w := by group
  have hσodd : Odd (orderOf σ) := by
    refine hdodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [hσ, ← map_pow]
    have : (⟨d, hKV hdK⟩ : ↥(Subgroup.normalizer (VZ T H : Set G))) ^ orderOf d = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨k, W, hCW, -, hsup, hnat⟩ :=
    s.kStar_decomposition hG16 hAS hF h1102 hG2 h1122 h1134 h1135 h1136
  have hfpf : ∀ i, ∀ u ∈ W i, σ u * u⁻¹ ∈ fixV (autOn (oTwoUpper H) (VZ T H)) →
      u ∈ fixV (autOn (oTwoUpper H) (VZ T H)) := by
    intro i
    obtain ⟨K', _, _, hK', π, hπ⟩ := hnat i
    exact hFPF K' n s.two_le hK' ↥(VZ T H) _ (W i) _ π hπ σ hσK hσodd hσ1
  have hWσ : ∀ i, ∀ w ∈ W i, σ w ∈ W i := by
    intro i w hw
    obtain ⟨K', _, _, -, π, hπ⟩ := hnat i
    exact hπ.2.2.2.1 ⟨σ, hσK⟩ w hw
  have hCσ : ∀ c ∈ fixV (autOn (oTwoUpper H) (VZ T H)), σ c = c := fun c hc => hc σ hσK
  have key := mem_of_fix_of_sum σ hCσ W hWσ hsup hfpf ⟨v, hv⟩ (by
      have h1 : σ ⟨v, hv⟩ = ⟨v, hv⟩ := by
        apply Subtype.ext
        rw [hσ, coe_conjAct_apply]
        exact hfix
      rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _)
  rw [B51.fixV_autOn hKV] at key
  exact key

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
