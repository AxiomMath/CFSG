module

public import CFSG.Quasithin.EmptyFaithful.SBd9Lie
public import CFSG.Quasithin.EmptyFaithful.SBd14Lie
public import CFSG.Quasithin.EmptyFaithful.SBd14Ind
public import CFSG.Quasithin.EmptyFaithful.SBd14Tr

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin CFSG.Quasithin.SBd9
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_borelModel {L Q : Subgroup G}
    (hZ : centerOf L = CFSG.Open.pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hmodel : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (ρ : ↥L →* projectiveSL 3 K),
      Nat.card K = 4 ∧ IsBorelModel L Q ρ := by
  obtain ⟨-, K, _, hKfin, hcard, ⟨e⟩⟩ := hmodel
  have hK4 : Nat.card K = 4 := by rw [hcard]; norm_num
  have : CharP K 2 := LinearFieldFour.charP_two_of_card_eq_four hK4
  let e' := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  let ρ₀ : ↥L →* projectiveSL 3 K := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hsurj₀ : Function.Surjective ρ₀ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : ρ₀.ker = Subgroup.center ↥L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective, QuotientGroup.ker_mk']
  have hZp : IsPGroup 2 (Subgroup.center ↥L) := by
    have h1 : IsPGroup 2 ↥(centerOf L) := by
      rw [hZ]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    rw [centerOf_eq_map] at h1
    exact h1.of_equiv ((Subgroup.center ↥L).equivMapOfInjective L.subtype L.subtype_injective).symm
  have hT : IsSylowTwoOf ((Q.subgroupOf L).map ρ₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hQ) ρ₀ hsurj₀
  obtain ⟨φ, hφ⟩ := SzN2.exists_mulEquiv_map_eq isSylowTwoOf_projUnitriangular hT
  refine ⟨K, inferInstance, hKfin, inferInstance, φ.toMonoidHom.comp ρ₀, hK4, ?_⟩
  exact
    { surj := φ.surjective.comp hsurj₀
      ker_eq := by rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, hker₀]
      two := by
        rw [MonoidHom.ker_comp_of_injective _ _ φ.injective, hker₀]
        exact hZp
      map_eq := by rw [← Subgroup.map_map]; exact hφ }

omit [Finite G] in
theorem mem_sup_of_commute' {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have e : A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [e] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihx
    obtain ⟨a', ha', b', hb', rfl⟩ := ihy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have := h a' ha' b hb
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← this]
      _ = a * a' * (b * b') := by group
  | inv x hx ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ih
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a ha b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a * b = b * a := this
        calc b⁻¹ * a⁻¹ = (a * b)⁻¹ := by group
          _ = (b * a)⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem commutator_mul_central {c₁ c₂ q₁ q₂ : G} (h1 : q₁ * c₂ = c₂ * q₁) (h2 : q₁ * q₂ = q₂ * q₁)
    (h3 : q₂ * c₁ = c₁ * q₂) : ⁅c₁ * q₁, c₂ * q₂⁆ = ⁅c₁, c₂⁆ := by
  have h3' : q₂ * c₁⁻¹ = c₁⁻¹ * q₂ := by
    have := congrArg (fun z => c₁⁻¹ * z * c₁⁻¹) h3
    simpa [mul_assoc] using this.symm
  have h2' : q₁ * q₂⁻¹ = q₂⁻¹ * q₁ := by
    have := congrArg (fun z => q₂⁻¹ * z * q₂⁻¹) h2
    simpa [mul_assoc] using this.symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc c₁ * q₁ * (c₂ * q₂) * (q₁⁻¹ * c₁⁻¹) * (q₂⁻¹ * c₂⁻¹)
      = c₁ * (q₁ * c₂) * q₂ * q₁⁻¹ * c₁⁻¹ * q₂⁻¹ * c₂⁻¹ := by group
    _ = c₁ * (c₂ * q₁) * q₂ * q₁⁻¹ * c₁⁻¹ * q₂⁻¹ * c₂⁻¹ := by rw [h1]
    _ = c₁ * c₂ * (q₁ * q₂ * q₁⁻¹) * c₁⁻¹ * q₂⁻¹ * c₂⁻¹ := by group
    _ = c₁ * c₂ * q₂ * c₁⁻¹ * q₂⁻¹ * c₂⁻¹ := by
        rw [h2]; group
    _ = c₁ * c₂ * (q₂ * c₁⁻¹) * q₂⁻¹ * c₂⁻¹ := by group
    _ = c₁ * c₂ * (c₁⁻¹ * q₂) * q₂⁻¹ * c₂⁻¹ := by rw [h3']
    _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by group

omit [Finite G] in
theorem IsCorner.inv' {K : Type} [Field K] {y : projectiveSL 3 K} (h : IsCorner y) :
    IsCorner y⁻¹ := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨-c, ?_⟩
  have h1 : proj 3 K (corner c) * proj 3 K (corner (-c)) = 1 := by
    rw [← map_mul, ← corner_add, add_neg_cancel, corner_zero, map_one]
  exact inv_eq_of_mul_eq_one_right h1

theorem lie_outer {L Q V₂ : Subgroup G} {d : G}
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = CFSG.Open.pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hmodel : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L))
    (hdL : d ∈ Subgroup.normalizer (L : Set G)) (hdQ : d ∈ Subgroup.normalizer (Q : Set G))
    (hd3 : d ^ 3 = 1) (hout : d ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hVQ : V₂ ≤ Q) (hVc : ∀ v ∈ V₂, ∀ q ∈ Q, v * q = q * v) (hV4 : Nat.card V₂ = 4)
    (hVZ : ∀ v ∈ V₂, v ∈ centerOf L → v = 1) (hdV : ∀ v ∈ V₂, d * v * d⁻¹ = v) :
    (∀ x ∈ Q, ⁅x, d⁆ ∈ V₂ ⊔ centerOf L → x ∈ V₂ ⊔ centerOf L) ∧
      Q ≤ ⁅Q, Subgroup.zpowers d⁆ := by
  classical
  obtain ⟨K, _, _, _, ρ, hK, hρ⟩ := exists_borelModel hZ hQ hmodel
  have hQL : Q ≤ L := hQ.1
  have hVL : V₂ ≤ L := hVQ.trans hQL
  have hCL : centerOf L ≤ L := fun z hz => hz.1
  have hZQ : centerOf L ≤ Q := hρ.center_le hQ
  have hρ1 : ∀ (x : G) (hx : x ∈ L), ρ ⟨x, hx⟩ = 1 ↔ x ∈ centerOf L := fun x hx =>
    hρ.eq_one_iff ⟨x, hx⟩
  have hρQ : ∀ (x : G) (hx : x ∈ L), ρ ⟨x, hx⟩ ∈ projUnitriangular 3 K ↔ x ∈ Q := fun x hx =>
    hρ.mem_iff hQ ⟨x, hx⟩
  have hVcorner : ∀ (v : G) (hv : v ∈ V₂), IsCorner (ρ ⟨v, hVL hv⟩) := by
    intro v hv
    have hvc : v ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq' => (hVc v hv q hq').symm
    exact exists_corner_of_mem_centralizer (hρ.mem_centralizer (hVL hv) hvc)
  have hVsurj : ∀ y : projectiveSL 3 K, IsCorner y → ∃ (v : G) (hv : v ∈ V₂), ρ ⟨v, hVL hv⟩ = y := by
    let g : ↥V₂ → projectiveSL 3 K := fun v => ρ ⟨v.1, hVL v.2⟩
    have hg_inj : Function.Injective g := by
      intro v w hvw
      have hvw' : ρ ⟨v.1, hVL v.2⟩ = ρ ⟨w.1, hVL w.2⟩ := hvw
      have hvwL : (v : G) * (w : G)⁻¹ ∈ V₂ := V₂.mul_mem v.2 (V₂.inv_mem w.2)
      have h1 : ρ ⟨(v : G) * (w : G)⁻¹, hVL hvwL⟩ = 1 := by
        have : (⟨(v : G) * (w : G)⁻¹, hVL hvwL⟩ : ↥L) =
            ⟨v.1, hVL v.2⟩ * (⟨w.1, hVL w.2⟩)⁻¹ := rfl
        rw [this, map_mul, map_inv, hvw', mul_inv_cancel]
      have h2 := hVZ _ hvwL ((hρ1 _ _).mp h1)
      exact Subtype.ext (mul_inv_eq_one.mp h2)
    set S : Set (projectiveSL 3 K) := {y | IsCorner y} with hSdef
    have hSrange : S = Set.range (fun c : K => proj 3 K (corner c)) := by
      ext y
      simp [S, IsCorner, eq_comm]
    have hS4 : Nat.card S = 4 := by
      rw [hSrange, Nat.card_range_of_injective proj_corner_injective, hK]
    have hrange_sub : Set.range g ⊆ S := by
      rintro _ ⟨v, rfl⟩
      exact hVcorner v.1 v.2
    have hrange4 : Nat.card (Set.range g) = 4 := by
      rw [Nat.card_range_of_injective hg_inj, hV4]
    have heq : Set.range g = S :=
      Set.eq_of_subset_of_ncard_le hrange_sub
        (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hS4, hrange4])
        (Set.toFinite S)
    intro y hy
    have hy' : y ∈ Set.range g := heq ▸ hy
    obtain ⟨v, hv⟩ := hy'
    exact ⟨v.1, v.2, hv⟩
  have hcorner_mem : ∀ (x : G) (hx : x ∈ L), IsCorner (ρ ⟨x, hx⟩) → x ∈ V₂ ⊔ centerOf L := by
    intro x hx h
    obtain ⟨v, hv, hρv⟩ := hVsurj _ h
    have hxv : x * v⁻¹ ∈ L := L.mul_mem hx (L.inv_mem (hVL hv))
    have h1 : ρ ⟨x * v⁻¹, hxv⟩ = 1 := by
      have : (⟨x * v⁻¹, hxv⟩ : ↥L) = ⟨x, hx⟩ * (⟨v, hVL hv⟩)⁻¹ := rfl
      rw [this, map_mul, map_inv, hρv, mul_inv_cancel]
    have h2 : x * v⁻¹ ∈ centerOf L := (hρ1 _ _).mp h1
    have : x = (x * v⁻¹) * v := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup h2 hv
  have hmem_corner : ∀ (x : G) (hx : x ∈ L), x ∈ V₂ ⊔ centerOf L → IsCorner (ρ ⟨x, hx⟩) := by
    intro x hx hmem
    have hcomm : ∀ a ∈ V₂, ∀ b ∈ centerOf L, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp hb.2 a (hVL ha)
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute' hcomm hmem
    have hbL : b ∈ L := hb.1
    have h1 : ρ ⟨a * b, hx⟩ = ρ ⟨a, hVL ha⟩ := by
      have e : (⟨a * b, hx⟩ : ↥L) = ⟨a, hVL ha⟩ * ⟨b, hbL⟩ := rfl
      rw [e, map_mul, (hρ1 _ _).mpr hb, mul_one]
    rw [h1]
    exact hVcorner a ha
  set φd : MulAut ↥L := L.normalizerMonoidHom ⟨d, hdL⟩ with hφd
  have hφ : ∀ x : ↥L, ((φd x : ↥L) : G) = d * (x : G) * d⁻¹ := fun x =>
    L.normalizerMonoidHom_apply_apply_coe ⟨d, hdL⟩ x
  obtain ⟨α, hα⟩ := exists_induced_aut hρ.surj hρ.ker_eq φd
  have hα3 : α ^ 3 = 1 := by
    ext p
    obtain ⟨x, rfl⟩ := hρ.surj p
    have e : φd (φd (φd x)) = x := by
      apply Subtype.ext
      rw [hφ, hφ, hφ]
      have hd3' : d * d * d = 1 := by rw [← pow_three']; exact hd3
      calc d * (d * (d * (x : G) * d⁻¹) * d⁻¹) * d⁻¹
          = (d * d * d) * (x : G) * (d * d * d)⁻¹ := by group
        _ = x := by rw [hd3']; group
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    rw [hα, hα, hα, e]
  have hαout : α ∉ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    intro hin
    obtain ⟨x₀, hx₀⟩ := exists_conj_of_induced_inner hρ.surj hρ.ker_eq hq.1 φd α hα hin
    apply hout
    have hw : (x₀ : G)⁻¹ * d ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg Subtype.val (hx₀ ⟨x, hx⟩)
      rw [hφ] at h2
      have h2' : d * x * d⁻¹ = (x₀ : G) * x * (x₀ : G)⁻¹ := h2
      calc x * ((x₀ : G)⁻¹ * d) = (x₀ : G)⁻¹ * ((x₀ : G) * x * (x₀ : G)⁻¹) * d := by group
        _ = (x₀ : G)⁻¹ * (d * x * d⁻¹) * d := by rw [h2']
        _ = ((x₀ : G)⁻¹ * d) * x := by group
    have e : d = (x₀ : G) * ((x₀ : G)⁻¹ * d) := by group
    rw [e]
    exact Subgroup.mul_mem_sup x₀.2 hw
  have hρQ' : ∀ x : ↥L, ρ x ∈ projUnitriangular 3 K ↔ (x : G) ∈ Q := fun x => hρQ x.1 x.2
  have hU : ∀ y, y ∈ projUnitriangular 3 K ↔ α y ∈ projUnitriangular 3 K := by
    intro y
    obtain ⟨x, rfl⟩ := hρ.surj y
    rw [hα, hρQ' x, hρQ' (φd x), hφ]
    exact Subgroup.mem_normalizer_iff.mp hdQ (x : G)
  have hι : ∀ c : K, α (proj 3 K (corner c)) = proj 3 K (corner c) := by
    intro c
    obtain ⟨v, hv, hρv⟩ := hVsurj _ ⟨c, rfl⟩
    rw [← hρv, hα]
    congr 1
    apply Subtype.ext
    rw [hφ]
    exact hdV v hv
  obtain ⟨a, b, ha, hb, hW⟩ := weights_of_outer hK hα3 hαout hU hι
  have hcommL : ∀ x : ↥L, (((x * (φd x)⁻¹ : ↥L)) : G) = ⁅(x : G), d⁆ := fun x => by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ, commutatorElement_def]
    group
  have hρcomm : ∀ x : ↥L, ρ (x * (φd x)⁻¹) = ρ x * (α (ρ x))⁻¹ := fun x => by
    rw [map_mul, map_inv, hα]
  have hA : ∀ x ∈ Q, ⁅x, d⁆ ∈ V₂ ⊔ centerOf L → x ∈ V₂ ⊔ centerOf L := by
    intro x hxQ hmem
    have hxL : x ∈ L := hQL hxQ
    have hcL : ⁅x, d⁆ ∈ L := (sup_le hVL hCL) hmem
    have hcorner : IsCorner (ρ ⟨x, hxL⟩ * (α (ρ ⟨x, hxL⟩))⁻¹) := by
      rw [← hρcomm]
      have : ρ (⟨x, hxL⟩ * (φd ⟨x, hxL⟩)⁻¹) = ρ ⟨⁅x, d⁆, hcL⟩ :=
        congrArg ρ (Subtype.ext (hcommL ⟨x, hxL⟩))
      rw [this]
      exact hmem_corner _ hcL hmem
    have hg : ρ ⟨x, hxL⟩ ∈ projUnitriangular 3 K := (hρQ x hxL).mpr hxQ
    exact hcorner_mem x hxL (inj_mod_corner ha hb hW hg hcorner)
  have hdec : ∀ x ∈ Q, ∃ y ∈ Q, ⁅y, d⁆⁻¹ * x ∈ V₂ ⊔ centerOf L := by
    intro x hxQ
    have hxL : x ∈ L := hQL hxQ
    have hg : ρ ⟨x, hxL⟩ ∈ projUnitriangular 3 K := (hρQ x hxL).mpr hxQ
    obtain ⟨u, hu, y₀, hy₀, huy⟩ := surj_mod_corner ha hb hW hg
    obtain ⟨y', rfl⟩ := hρ.surj u
    have hy'Q : (y' : G) ∈ Q := (hρQ' y').mp hu
    refine ⟨y', hy'Q, ?_⟩
    let z : ↥L := (y' * (φd y')⁻¹)⁻¹ * ⟨x, hxL⟩
    have hzG : (z : G) = ⁅(y' : G), d⁆⁻¹ * x := by
      simp only [z, Subgroup.coe_mul, Subgroup.coe_inv, hcommL]
    have hz : ρ z = y₀⁻¹ := by
      have h1 : ρ z = α (ρ y') * (ρ y')⁻¹ * ρ ⟨x, hxL⟩ := by
        simp only [z, map_mul, map_inv, hα]
        group
      have h2 : (ρ y')⁻¹ = (α (ρ y'))⁻¹ * y₀⁻¹ * (ρ ⟨x, hxL⟩)⁻¹ := by
        calc (ρ y')⁻¹ = (ρ ⟨x, hxL⟩ * y₀ * α (ρ y'))⁻¹ := congrArg Inv.inv huy
          _ = _ := by group
      rw [h1, h2]
      group
    have hcz : IsCorner (ρ ⟨(z : G), z.2⟩) := by
      have : ρ ⟨(z : G), z.2⟩ = ρ z := rfl
      rw [this, hz]
      exact hy₀.inv'
    rw [← hzG]
    exact hcorner_mem _ z.2 hcz
  have hQLsyl := isSylowTwoOf_top_subgroupOf hQ
  obtain ⟨hQLp, hQLidx⟩ := K1.isSylowTwoOf_top_iff.mp hQLsyl
  have hZcomm : centerOf L ≤ ⁅Q, Q⁆ := by
    intro z hz
    have hzL : z ∈ L := hz.1
    have hzc : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := (mem_centerOf_iff).mp hz
    have hzQ : (⟨z, hzL⟩ : ↥L) ∈ Q.subgroupOf L := Subgroup.mem_subgroupOf.mpr (hZQ hz)
    have h1 := mem_commutator_of_central hq.1 hQLp hQLidx hzc hzQ
    have h2 : (z : G) ∈ Subgroup.map L.subtype ⁅Q.subgroupOf L, Q.subgroupOf L⁆ :=
      ⟨⟨z, hzL⟩, h1, rfl⟩
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQL] at h2
  have hVcomm : V₂ ≤ ⁅Q, Q⁆ := by
    intro v hv
    obtain ⟨c, hc⟩ := hVcorner v hv
    obtain ⟨a₁, ha₁, b₁, hb₁, hab⟩ := exists_comm_corner (K := K) c
    obtain ⟨a', rfl⟩ := hρ.surj a₁
    obtain ⟨b', rfl⟩ := hρ.surj b₁
    have ha'Q : (a' : G) ∈ Q := (hρQ' a').mp ha₁
    have hb'Q : (b' : G) ∈ Q := (hρQ' b').mp hb₁
    have hcommQ : ⁅(a' : G), (b' : G)⁆ ∈ ⁅Q, Q⁆ := Subgroup.commutator_mem_commutator ha'Q hb'Q
    have hcL : ⁅(a' : G), (b' : G)⁆ ∈ L := (⁅a', b'⁆ : ↥L).2
    have h1 : ρ ⟨⁅(a' : G), (b' : G)⁆, hcL⟩ = ρ ⟨v, hVL hv⟩ := by
      rw [hc, ← hab]
      have : (⟨⁅(a' : G), (b' : G)⁆, hcL⟩ : ↥L) = ⁅a', b'⁆ := rfl
      rw [this, map_commutatorElement]
      rfl
    have hvz : (⁅(a' : G), (b' : G)⁆)⁻¹ * v ∈ centerOf L := by
      have hmem : (⁅(a' : G), (b' : G)⁆)⁻¹ * v ∈ L := L.mul_mem (L.inv_mem hcL) (hVL hv)
      apply (hρ1 _ hmem).mp
      have : (⟨(⁅(a' : G), (b' : G)⁆)⁻¹ * v, hmem⟩ : ↥L) =
          (⟨⁅(a' : G), (b' : G)⁆, hcL⟩ : ↥L)⁻¹ * ⟨v, hVL hv⟩ := rfl
      rw [this, map_mul, map_inv, h1, inv_mul_cancel]
    have : v = ⁅(a' : G), (b' : G)⁆ * ((⁅(a' : G), (b' : G)⁆)⁻¹ * v) := by group
    rw [this]
    exact ⁅Q, Q⁆.mul_mem hcommQ (hZcomm hvz)
  refine ⟨hA, ?_⟩
  set Q₁ : Subgroup G := ⁅Q, Subgroup.zpowers d⁆ with hQ₁
  set Q₀ : Subgroup G := V₂ ⊔ centerOf L with hQ₀
  have hQ₀Q : Q₀ ≤ Q := sup_le hVQ hZQ
  have hQ₀c : ∀ q₀ ∈ Q₀, ∀ q ∈ Q, q₀ * q = q * q₀ := by
    have hle : Q₀ ≤ Subgroup.centralizer (Q : Set G) := by
      refine sup_le (fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq' => (hVc v hv q hq').symm)
        (fun z hz => Subgroup.mem_centralizer_iff.mpr fun q hq' => ?_)
      exact Subgroup.mem_centralizer_iff.mp hz.2 q (hQL hq')
    intro q₀ hq₀ q hq'
    exact (Subgroup.mem_centralizer_iff.mp (hle hq₀) q hq').symm
  have hQ₁Q : Q₁ ≤ Q := by
    refine Subgroup.commutator_le.mpr fun y hy w hw => ?_
    have hwN : w ∈ Subgroup.normalizer (Q : Set G) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact Subgroup.zpow_mem _ hdQ n
    have h1 : w * y⁻¹ * w⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hwN _).mp (Q.inv_mem hy)
    have : ⁅y, w⁆ = y * (w * y⁻¹ * w⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact Q.mul_mem hy h1
  have hdec' : ∀ x ∈ Q, ∃ c ∈ Q₁, ∃ q₀ ∈ Q₀, x = c * q₀ := by
    intro x hx
    obtain ⟨y, hy, hq₀⟩ := hdec x hx
    refine ⟨⁅y, d⁆, Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers d), _, hq₀, ?_⟩
    group
  have hQQ : ⁅Q, Q⁆ ≤ Q₁ := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨c₁, hc₁, q₁, hq₁, rfl⟩ := hdec' a ha
    obtain ⟨c₂, hc₂, q₂, hq₂, rfl⟩ := hdec' b hb
    rw [commutator_mul_central (hQ₀c q₁ hq₁ c₂ (hQ₁Q hc₂)) (hQ₀c q₁ hq₁ q₂ (hQ₀Q hq₂))
      (hQ₀c q₂ hq₂ c₁ (hQ₁Q hc₁))]
    exact Q₁.mul_mem (Q₁.mul_mem (Q₁.mul_mem hc₁ hc₂) (Q₁.inv_mem hc₁)) (Q₁.inv_mem hc₂)
  intro x hx
  obtain ⟨c, hc, q₀, hq₀, rfl⟩ := hdec' x hx
  exact Q₁.mul_mem hc (hQQ (sup_le hVcomm hZcomm hq₀))

end CFSG.Quasithin.SBd14
