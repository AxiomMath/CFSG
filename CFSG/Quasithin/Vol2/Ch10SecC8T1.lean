module

public import CFSG.Quasithin.Vol2.Ch10SecC8X
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Vol2.Ch10SecBL32Over

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_mem_inf_acts_fsuUL (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hD : ∀ γ, ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
      autOn (T ⊓ L) (fsuUL T L I) ↔ γ ∈ SecB.L32.U3) {s : G} (hs : s ∈ T1 T L) :
    ∃ d ∈ T ⊓ L, ∀ v ∈ fsuUL T L I, s * v * s⁻¹ = d * v * d⁻¹ := by
  obtain ⟨x₀, hx₀, -, hx₀s⟩ := acts_as_inner_fsuUL hyp h1011 h3 hs
  have hLN := le_normalizer_fsuUL T L I
  have hsN : s ∈ Subgroup.normalizer (fsuUL T L I : Set G) := T1_le_normalizer_fsuUL T L I hs
  have hinv : ∀ v ∈ fsuUL T L I, s⁻¹ * v * s = x₀⁻¹ * v * x₀ := by
    intro v hv
    have hw : x₀⁻¹ * v * x₀ ∈ fsuUL T L I := by
      have := (Subgroup.mem_normalizer_iff.mp (hLN (L.inv_mem hx₀)) v).mp hv
      rwa [inv_inv] at this
    have h1 := hx₀s _ hw
    have e : x₀ * (x₀⁻¹ * v * x₀) * x₀⁻¹ = v := by group
    rw [e] at h1
    calc s⁻¹ * v * s = s⁻¹ * (s * (x₀⁻¹ * v * x₀) * s⁻¹) * s := by rw [h1]
      _ = x₀⁻¹ * v * x₀ := by group
  have hconj : ∀ d ∈ T ⊓ L, ∀ v ∈ fsuUL T L I,
      (x₀ * d * x₀⁻¹) * v * (x₀ * d * x₀⁻¹)⁻¹ = (s * d * s⁻¹) * v * (s * d * s⁻¹)⁻¹ := by
    intro d hd v hv
    have hw1 : s⁻¹ * v * s ∈ fsuUL T L I := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) v).mp hv
      rwa [inv_inv] at this
    have hw : d * (s⁻¹ * v * s) * d⁻¹ ∈ fsuUL T L I :=
      (Subgroup.mem_normalizer_iff.mp (hLN hd.2) _).mp hw1
    calc (x₀ * d * x₀⁻¹) * v * (x₀ * d * x₀⁻¹)⁻¹ =
        x₀ * (d * (x₀⁻¹ * v * x₀) * d⁻¹) * x₀⁻¹ := by group
      _ = x₀ * (d * (s⁻¹ * v * s) * d⁻¹) * x₀⁻¹ := by rw [hinv v hv]
      _ = s * (d * (s⁻¹ * v * s) * d⁻¹) * s⁻¹ := (hx₀s _ hw).symm
      _ = (s * d * s⁻¹) * v * (s * d * s⁻¹)⁻¹ := by group
  obtain ⟨γ, hγ⟩ := D.π_surj ⟨conjAct (fsuUL T L I) ⟨x₀, hLN hx₀⟩,
    SecB.mem_autOn_iff.mpr ⟨⟨x₀, hLN hx₀⟩, hx₀, rfl⟩⟩
  have hγU : γ ∈ SecB.L32.U3 := by
    refine SecB.L32.normalizer_U3_aux γ fun u hu => ?_
    have hu' := (hD u).mpr ((SecB.L32.mem_uList_iff u).mp hu)
    obtain ⟨⟨d, hdN⟩, hdTL, hdu⟩ := SecB.mem_autOn_iff.mp hu'
    have hsd : s * d * s⁻¹ ∈ T ⊓ L :=
      ⟨T.mul_mem (T.mul_mem hs.1 hdTL.1) (T.inv_mem hs.1),
        (Subgroup.mem_normalizer_iff.mp hs.2 d).mp hdTL.2⟩
    have key : ((D.π (γ * u * γ⁻¹) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) =
        conjAct (fsuUL T L I) (⟨x₀, hLN hx₀⟩ * ⟨d, hdN⟩ * (⟨x₀, hLN hx₀⟩)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hγ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        ← hdu, map_mul, map_mul, map_inv]
    have key2 : conjAct (fsuUL T L I) (⟨x₀, hLN hx₀⟩ * ⟨d, hdN⟩ * (⟨x₀, hLN hx₀⟩)⁻¹) =
        conjAct (fsuUL T L I) ⟨s * d * s⁻¹, hLN hsd.2⟩ := by
      ext v
      change (x₀ * d * x₀⁻¹) * (v : G) * (x₀ * d * x₀⁻¹)⁻¹ =
        (s * d * s⁻¹) * (v : G) * (s * d * s⁻¹)⁻¹
      exact hconj d hdTL v v.2
    rw [← SecB.L32.mem_U3, ← hD, key, key2]
    exact SecB.mem_autOn_iff.mpr ⟨⟨s * d * s⁻¹, hLN hsd.2⟩, hsd, rfl⟩
  obtain ⟨⟨d, hdN⟩, hdTL, hdx⟩ := SecB.mem_autOn_iff.mp ((hD γ).mpr hγU)
  refine ⟨d, hdTL, fun v hv => ?_⟩
  rw [hx₀s v hv]
  have h1 := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨v, hv⟩ : ↥(fsuUL T L I)) : G)) hdx
  rw [hγ] at h1
  exact h1.symm

theorem exists_mem_inf_acts_V2 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hD : ∀ γ, ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
      autOn (T ⊓ L) (fsuUL T L I) ↔ γ ∈ SecB.L32.U3) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ T1 T L) :
    ∃ d ∈ T ⊓ CFSG.conjugate L t, ∀ w ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆,
      s * w * s⁻¹ = d * w * d⁻¹ := by
  have hs' : t * s * t⁻¹ ∈ T1 T L := map_conj_le_T1 h37 h38 hyp ht htn le_rfl ⟨s, hs, rfl⟩
  obtain ⟨d', hd', hd's⟩ := exists_mem_inf_acts_fsuUL hyp h1011 h3 D hD hs'
  refine ⟨t⁻¹ * d' * t, Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hd'.1) ht, ?_⟩,
    fun w hw => ?_⟩
  · rw [SecA.mem_conjugate_iff]
    have e : t * (t⁻¹ * d' * t) * t⁻¹ = d' := by group
    rw [e]
    exact hd'.2
  · have hw' : t * w * t⁻¹ ∈ fsuUL T L I := by
      rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)] at hw
      exact SecA.mem_conjugate_iff.mp hw
    have h1 := hd's _ hw'
    calc s * w * s⁻¹ = t⁻¹ * ((t * s * t⁻¹) * (t * w * t⁻¹) * (t * s * t⁻¹)⁻¹) * t := by group
      _ = t⁻¹ * (d' * (t * w * t⁻¹) * d'⁻¹) * t := by rw [h1]
      _ = (t⁻¹ * d' * t) * w * (t⁻¹ * d' * t)⁻¹ := by group

omit [Finite G] in
theorem mem_of_le_eqSet {a b : G} {X : Subgroup G}
    (h : ∀ x ∈ X, a * x * a⁻¹ = b * x * b⁻¹) {Y : Subgroup G}
    (hY : ∀ y ∈ Y, a * y * a⁻¹ = b * y * b⁻¹)
    {x : G} (hx : x ∈ X ⊔ Y) : a * x * a⁻¹ = b * x * b⁻¹ := by
  let E : Subgroup G :=
    { carrier := {x | a * x * a⁻¹ = b * x * b⁻¹}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change a * x * a⁻¹ = b * x * b⁻¹ at hx
        change a * y * a⁻¹ = b * y * b⁻¹ at hy
        change a * (x * y) * a⁻¹ = b * (x * y) * b⁻¹
        calc a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
          _ = (b * x * b⁻¹) * (b * y * b⁻¹) := by rw [hx, hy]
          _ = b * (x * y) * b⁻¹ := by group
      inv_mem' := fun {x} hx => by
        change a * x * a⁻¹ = b * x * b⁻¹ at hx
        change a * x⁻¹ * a⁻¹ = b * x⁻¹ * b⁻¹
        calc a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
          _ = (b * x * b⁻¹)⁻¹ := by rw [hx]
          _ = b * x⁻¹ * b⁻¹ := by group }
  have hle : X ⊔ Y ≤ E := sup_le (fun x hx => h x hx) (fun y hy => hY y hy)
  exact hle hx

theorem exists_decomp_T1 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) [IsMulCommutative ↥(fsuUL T L I)]
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hD : ∀ γ, ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
      autOn (T ⊓ L) (fsuUL T L I) ↔ γ ∈ SecB.L32.U3) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {s : G} (hs : s ∈ T1 T L) :
    ∃ d₁ ∈ T ⊓ L, ∃ d₂ ∈ T ⊓ CFSG.conjugate L t, ∀ v ∈ fsuVM T L I,
      s * v * s⁻¹ = (d₁ * d₂) * v * (d₁ * d₂)⁻¹ := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1, hV2, -⟩ := hdec t ht htn
  obtain ⟨d₁, hd₁, h₁⟩ := exists_mem_inf_acts_fsuUL hyp h1011 h3 D hD hs
  obtain ⟨d₂, hd₂, h₂⟩ := exists_mem_inf_acts_V2 h37 h38 hyp h1011 h3 D hD ht htn hs
  refine ⟨d₁, hd₁, d₂, hd₂, fun v hv => ?_⟩
  rw [hVeq] at hv
  refine mem_of_le_eqSet (fun x hx => ?_) (fun y hy => ?_) hv
  · have hc : d₂ * x * d₂⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp (hV1 hx) d₂ hd₂.2, mul_inv_cancel_right]
    rw [h₁ x hx]
    calc d₁ * x * d₁⁻¹ = d₁ * (d₂ * x * d₂⁻¹) * d₁⁻¹ := by rw [hc]
      _ = (d₁ * d₂) * x * (d₁ * d₂)⁻¹ := by group
  · have hy' : d₂ * y * d₂⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
      rw [← h₂ y hy]
      exact (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator
        (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I))
        (T1_le_normalizer_conjugate h37 h38 hyp ht htn) hs) y).mp hy
    have hc : d₁ * (d₂ * y * d₂⁻¹) * d₁⁻¹ = d₂ * y * d₂⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV2 hy') d₁ hd₁.2, mul_inv_cancel_right]
    rw [h₂ y hy]
    calc d₂ * y * d₂⁻¹ = d₁ * (d₂ * y * d₂⁻¹) * d₁⁻¹ := hc.symm
      _ = (d₁ * d₂) * y * (d₁ * d₂)⁻¹ := by group

theorem mem_centralizer_fsuL0_of_inf (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {v : G}
    (hv : v ∈ fsuUL T L I) (hvc : ∀ d ∈ T ⊓ L, d * v * d⁻¹ = v) :
    v ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
  obtain ⟨hc, hnat⟩ := h3.2
  obtain ⟨D⟩ := hnat.toL3Coord
  have hS : QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) (fsuUL T L I))
      (autOn L (fsuUL T L I)) :=
    QuasithinUnique.Setup.isSylowTwoOf_autOn (SecA.isSylowTwoOf_inf hyp.fsu.maximal.1)
      (le_normalizer_fsuUL T L I)
  have hfix := fixV_sylow_fsuUL h37 h38 hyp h1011 h484 D hnat hne hS
  have h1 : (⟨v, hv⟩ : ↥(fsuUL T L I)) ∈ fixV (autOn (T ⊓ L) (fsuUL T L I)) := by
    rw [mem_fixV]
    intro g hg
    obtain ⟨⟨d, hdN⟩, hdTL, rfl⟩ := SecB.mem_autOn_iff.mp hg
    exact Subtype.ext (hvc d hdTL)
  rw [hfix] at h1
  exact h1

theorem fsuVM_inf_centralizer_T1_le (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) :
    fsuVM T L I ⊓ Subgroup.centralizer (T1 T L : Set G) ≤ fsuCVM T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1, hV2, -⟩ := hdec t ht htn
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hV2V : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hLtN : CFSG.conjugate L t ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (SecA.le_fsuL0 T L)).mp
      (SecA.normal_fsuL0 hyp.fsu.maximal.1)) (SecA.conjugate_le_fsuL0 ht hx)
  rintro v ⟨hv, hvc⟩
  have hv' : v ∈ (↑(fsuUL T L I ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆) : Set G) := by
    rw [← hVeq]
    exact hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_of_le_fsuVM hyp hV2V hV1V)] at hv'
  obtain ⟨v₁, hv₁, v₂, hv₂, hvv⟩ := hv'
  have hvv' : v₁ * v₂ = v := hvv
  have hcT : ∀ d ∈ T1 T L, d * v * d⁻¹ = v := fun d hd => by
    rw [Subgroup.mem_centralizer_iff.mp hvc d hd, mul_inv_cancel_right]
  have h1 : v₁ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    refine mem_centralizer_fsuL0_of_inf h37 h38 hyp h1011 h484 h3 hne hv₁ fun d hd => ?_
    have hdv2 : d * v₂ * d⁻¹ = v₂ := by
      rw [Subgroup.mem_centralizer_iff.mp (hV2 hv₂) d hd.2, mul_inv_cancel_right]
    have hdv := hcT d ⟨hd.1, Subgroup.le_normalizer hd.2⟩
    rw [← hvv'] at hdv
    have e : d * (v₁ * v₂) * d⁻¹ = (d * v₁ * d⁻¹) * (d * v₂ * d⁻¹) := by group
    rw [e, hdv2] at hdv
    exact mul_right_cancel hdv
  have h2 : v₂ ∈ Subgroup.centralizer (fsuL0 T L : Set G) := by
    have hw : t * v₂ * t⁻¹ ∈ fsuUL T L I := by
      have := hv₂
      rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht)] at this
      exact SecA.mem_conjugate_iff.mp this
    have hw' := mem_centralizer_fsuL0_of_inf h37 h38 hyp h1011 h484 h3 hne hw fun d hd => by
      have hd' : t⁻¹ * d * t ∈ T ⊓ CFSG.conjugate L t := by
        refine Subgroup.mem_inf.mpr ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hd.1) ht, ?_⟩
        rw [SecA.mem_conjugate_iff]
        have e : t * (t⁻¹ * d * t) * t⁻¹ = d := by group
        rw [e]
        exact hd.2
      have hdv1 : (t⁻¹ * d * t) * v₁ * (t⁻¹ * d * t)⁻¹ = v₁ := by
        rw [Subgroup.mem_centralizer_iff.mp (hV1 hv₁) _ hd'.2, mul_inv_cancel_right]
      have hdv := hcT _ ⟨hd'.1, hLtN hd'.2⟩
      rw [← hvv'] at hdv
      have e : (t⁻¹ * d * t) * (v₁ * v₂) * (t⁻¹ * d * t)⁻¹ =
          ((t⁻¹ * d * t) * v₁ * (t⁻¹ * d * t)⁻¹) * ((t⁻¹ * d * t) * v₂ * (t⁻¹ * d * t)⁻¹) := by
        group
      rw [e, hdv1] at hdv
      have h3' := mul_left_cancel hdv
      calc d * (t * v₂ * t⁻¹) * d⁻¹ = t * ((t⁻¹ * d * t) * v₂ * (t⁻¹ * d * t)⁻¹) * t⁻¹ := by
            group
        _ = t * v₂ * t⁻¹ := by rw [h3']
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : t * x * t⁻¹ ∈ fsuL0 T L :=
      (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L ht) x).mp hx
    have hc := Subgroup.mem_centralizer_iff.mp hw' _ hx'
    have e1 : x * v₂ = t⁻¹ * ((t * x * t⁻¹) * (t * v₂ * t⁻¹)) * t := by group
    have e2 : v₂ * x = t⁻¹ * ((t * v₂ * t⁻¹) * (t * x * t⁻¹)) * t := by group
    rw [e1, e2, hc]
  rw [← hvv']
  exact ⟨(fsuVM T L I).mul_mem (hV1V hv₁) (hV2V hv₂), Subgroup.mul_mem _ h1 h2⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
