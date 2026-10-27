module

public import CFSG.Quasithin.Vol2.Ch9KGFFG24U
public import CFSG.LieType.Chevalley.G2FieldFourCoverRoots
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.G24

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

theorem exists_eq_mul_inv_of_card {G : Type*} [Group G] (σ : G →* G)
    (hσσ : ∀ x, σ (σ x) = x) {U : Subgroup G} [Finite U] (hσU : ∀ x ∈ U, σ x ∈ U)
    (hcard : Nat.card U = Nat.card {v : G // v ∈ U ∧ σ v = v} *
      Nat.card {u : G // u ∈ U ∧ u * σ u = 1})
    {u : G} (hu : u ∈ U) (h1 : u * σ u = 1) : ∃ v ∈ U, u = v * (σ v)⁻¹ := by
  let H : Subgroup G := U ⊓ σ.eqLocus (MonoidHom.id G)
  let T := {u : G // u ∈ U ∧ u * σ u = 1}
  have : Finite T := Finite.of_injective (fun t : T => (⟨t.1, t.2.1⟩ : U)) fun a b h => by
    apply Subtype.ext
    exact (congrArg Subtype.val h :)
  have hT : ∀ v : ↥U, (v : G) * (σ v)⁻¹ ∈ U ∧ (v : G) * (σ v)⁻¹ * σ ((v : G) * (σ v)⁻¹) = 1 := by
    intro v
    refine ⟨U.mul_mem v.2 (U.inv_mem (hσU _ v.2)), ?_⟩
    rw [map_mul, map_inv, hσσ]
    group
  let φ : ↥U → T := fun v => ⟨(v : G) * (σ v)⁻¹, hT v⟩
  have hφ : ∀ v w : ↥U, φ v = φ w ↔ v⁻¹ * w ∈ H.subgroupOf U := by
    intro v w
    rw [Subgroup.mem_subgroupOf]
    change _ ↔ (v : G)⁻¹ * w ∈ U ∧ σ ((v : G)⁻¹ * w) = (v : G)⁻¹ * w
    rw [map_mul, map_inv]
    constructor
    · intro h
      have h' : (v : G) * (σ v)⁻¹ = w * (σ w)⁻¹ := congrArg Subtype.val h
      refine ⟨U.mul_mem (U.inv_mem v.2) w.2, ?_⟩
      calc (σ v)⁻¹ * σ w = (v : G)⁻¹ * ((v : G) * (σ v)⁻¹) * σ w := by group
        _ = (v : G)⁻¹ * (w * (σ w)⁻¹) * σ w := by rw [h']
        _ = (v : G)⁻¹ * w := by group
    · rintro ⟨-, h'⟩
      apply Subtype.ext
      change (v : G) * (σ v)⁻¹ = w * (σ w)⁻¹
      calc (v : G) * (σ v)⁻¹ = (v : G) * ((σ v)⁻¹ * σ w) * (σ w)⁻¹ := by group
        _ = (v : G) * ((v : G)⁻¹ * w) * (σ w)⁻¹ := by rw [h']
        _ = w * (σ w)⁻¹ := by group
  let ψ : ↥U ⧸ H.subgroupOf U → T := Quotient.lift φ fun v w hvw =>
    (hφ v w).mpr (QuotientGroup.leftRel_apply.mp hvw)
  have hψ : Function.Injective ψ := by
    intro q r hqr
    induction q using Quotient.inductionOn with | h v => ?_
    induction r using Quotient.inductionOn with | h w => ?_
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hφ v w).mp hqr))
  have hHc : Nat.card ↥(H.subgroupOf U) = Nat.card {v : G // v ∈ U ∧ σ v = v} :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans
      (Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl))
  have hpos : 0 < Nat.card ↥(H.subgroupOf U) := Nat.card_pos
  have hQc : Nat.card T = Nat.card (↥U ⧸ H.subgroupOf U) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf U)
    rw [hcard, ← hHc] at h
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h, Nat.mul_comm]
  obtain ⟨q, hq⟩ := (hψ.bijective_of_nat_card_le hQc.le).2 ⟨u, hu, h1⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨v, v.2, (congrArg Subtype.val hq).symm⟩

@[expose] def LangCond {K : Type} [Field K] (a b c d e f : K) : Prop :=
  a + a ^ 2 = 0 ∧ b + b ^ 2 = 0 ∧ c + b * a ^ 2 + c ^ 2 = 0 ∧ d + b * (a ^ 2) ^ 2 + d ^ 2 = 0 ∧
    e + b * (a ^ 2) ^ 3 + c * (a ^ 2) ^ 2 + d * a ^ 2 + e ^ 2 = 0 ∧
    f + b ^ 2 * (a ^ 2) ^ 3 + b * c * (a ^ 2) ^ 2 + c ^ 2 * a ^ 2 +
      b ^ 2 * (e + b * (a ^ 2) ^ 3 + c * (a ^ 2) ^ 2 + d * a ^ 2) +
        c ^ 2 * (d + b * (a ^ 2) ^ 2) + f ^ 2 = 0

@[expose] def FixCond {K : Type} [Field K] (a b c d e f : K) : Prop :=
  a ^ 2 = a ∧ b ^ 2 = b ∧ c ^ 2 = c ∧ d ^ 2 = d ∧ e ^ 2 = e ∧ f ^ 2 = f

instance (a b c d e f : CFSG.Fischer.F4) : Decidable (LangCond a b c d e f) := by
  unfold LangCond
  infer_instance

instance (a b c d e f : CFSG.Fischer.F4) : Decidable (FixCond a b c d e f) := by
  unfold FixCond
  infer_instance

theorem card_langCond_F4 : Fintype.card {t : CFSG.Fischer.F4 × CFSG.Fischer.F4 ×
    CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 //
      LangCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} = 64 := by
  decide +kernel

theorem card_fixCond_F4 : Fintype.card {t : CFSG.Fischer.F4 × CFSG.Fischer.F4 ×
    CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 //
      FixCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} = 64 := by
  decide +kernel

theorem card_sq_eq_self_F4 : Fintype.card {c : CFSG.Fischer.F4 // c ^ 2 = c} = 2 := by
  decide +kernel

section Transfer

variable {K L : Type} [Field K] [Field L]

theorem langCond_map (ρ : K ≃+* L) (a b c d e f : K) :
    LangCond a b c d e f ↔ LangCond (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) := by
  unfold LangCond
  simp only [← map_pow, ← map_mul, ← map_add, map_eq_zero_iff _ ρ.injective]

theorem fixCond_map (ρ : K ≃+* L) (a b c d e f : K) :
    FixCond a b c d e f ↔ FixCond (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) := by
  unfold FixCond
  simp only [← map_pow, ρ.injective.eq_iff]

theorem nonempty_ringEquiv_F4 (hK : Nat.card K = 4) : Nonempty (K ≃+* CFSG.Fischer.F4) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hK]
  exact ⟨FiniteField.ringEquivOfCardEq hc⟩

@[expose] def prod6 {α β : Type} (e : α ≃ β) :
    α × α × α × α × α × α ≃ β × β × β × β × β × β :=
  e.prodCongr (e.prodCongr (e.prodCongr (e.prodCongr (e.prodCongr e))))

theorem card_langCond (hK : Nat.card K = 4) :
    Nat.card {t : K × K × K × K × K × K //
      LangCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} = 64 := by
  obtain ⟨ρ⟩ := nonempty_ringEquiv_F4 hK
  have e : {t : K × K × K × K × K × K //
      LangCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} ≃
      {t : CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 ×
        CFSG.Fischer.F4 × CFSG.Fischer.F4 //
          LangCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} :=
    (prod6 ρ.toEquiv).subtypeEquiv fun t => langCond_map ρ _ _ _ _ _ _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_langCond_F4

theorem card_fixCond (hK : Nat.card K = 4) :
    Nat.card {t : K × K × K × K × K × K //
      FixCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} = 64 := by
  obtain ⟨ρ⟩ := nonempty_ringEquiv_F4 hK
  have e : {t : K × K × K × K × K × K //
      FixCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} ≃
      {t : CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 ×
        CFSG.Fischer.F4 × CFSG.Fischer.F4 //
          FixCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} :=
    (prod6 ρ.toEquiv).subtypeEquiv fun t => fixCond_map ρ _ _ _ _ _ _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_fixCond_F4

theorem card_sq_eq_self (hK : Nat.card K = 4) : Nat.card {c : K // c ^ 2 = c} = 2 := by
  obtain ⟨ρ⟩ := nonempty_ringEquiv_F4 hK
  have e : {c : K // c ^ 2 = c} ≃ {c : CFSG.Fischer.F4 // c ^ 2 = c} :=
    ρ.toEquiv.subtypeEquiv fun c => by
      change c ^ 2 = c ↔ ρ c ^ 2 = ρ c
      rw [← map_pow, ρ.injective.eq_iff]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_sq_eq_self_F4

end Transfer

section Lang

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem card_posUnipotent_four
    (hK : Nat.card K = 4) : Nat.card ↥(posUnipotent .G2 K) = 4096 := by
  rw [card_posUnipotent, G2FieldFour.ncard_posRoots, hK]
  norm_num

omit [CharP K 2] in
theorem card_fixed
    (hK : Nat.card K = 4) (δ : K →+* K) (hδ : ∀ c, δ c = c ^ 2) :
    Nat.card {v : ModGL .G2 K //
      v ∈ posUnipotent .G2 K ∧ Units.map (entrywiseHom δ) v = v} = 64 := by
  rw [← card_fixCond hK]
  symm
  let f : {t : K × K × K × K × K × K //
      FixCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} →
      {v : ModGL .G2 K // v ∈ posUnipotent .G2 K ∧ Units.map (entrywiseHom δ) v = v} :=
    fun t => ⟨g2N t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2,
      g2N_mem_posUnipotent _ _ _ _ _ _, by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := t.2
        simp only [units_map_entrywiseHom_g2N, hδ]
        rw [h1, h2, h3, h4, h5, h6]⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun t s hts => ?_, fun v => ?_⟩)
  · have h' : g2N t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2 =
        g2N s.1.1 s.1.2.1 s.1.2.2.1 s.1.2.2.2.1 s.1.2.2.2.2.1 s.1.2.2.2.2.2 :=
      (congrArg Subtype.val hts :)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective h'
    exact Subtype.ext (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))))
  · obtain ⟨x, hxU, hx⟩ := v
    obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hxU
    simp only [units_map_entrywiseHom_g2N, hδ] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective hx
    exact ⟨⟨(A, B, C, D, E, F), h1, h2, h3, h4, h5, h6⟩, rfl⟩

theorem card_lang
    (hK : Nat.card K = 4) (δ : K →+* K) (hδ : ∀ c, δ c = c ^ 2) :
    Nat.card {u : ModGL .G2 K //
      u ∈ posUnipotent .G2 K ∧ u * Units.map (entrywiseHom δ) u = 1} = 64 := by
  rw [← card_langCond hK]
  symm
  let f : {t : K × K × K × K × K × K //
      LangCond t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2} →
      {u : ModGL .G2 K // u ∈ posUnipotent .G2 K ∧ u * Units.map (entrywiseHom δ) u = 1} :=
    fun t => ⟨g2N t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2,
      g2N_mem_posUnipotent _ _ _ _ _ _, by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := t.2
        simp only [units_map_entrywiseHom_g2N, hδ]
        rw [g2N_mul_g2N, ← g2N_zero]
        exact g2N_eq_g2N h1 h2 h3 h4 h5 h6⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun t s hts => ?_, fun v => ?_⟩)
  · have h' : g2N t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2 =
        g2N s.1.1 s.1.2.1 s.1.2.2.1 s.1.2.2.2.1 s.1.2.2.2.2.1 s.1.2.2.2.2.2 :=
      (congrArg Subtype.val hts :)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective h'
    exact Subtype.ext (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))))
  · obtain ⟨x, hxU, hx⟩ := v
    obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hxU
    simp only [units_map_entrywiseHom_g2N, hδ] at hx
    rw [g2N_mul_g2N, ← g2N_zero] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective hx
    exact ⟨⟨(A, B, C, D, E, F), h1, h2, h3, h4, h5, h6⟩, rfl⟩

omit [CharP K 2] in
theorem units_map_entrywiseHom_sq_involutive (hK : Nat.card K = 4) (δ : K →+* K)
    (hδ : ∀ c, δ c = c ^ 2) (x : ModGL .G2 K) :
    Units.map (entrywiseHom δ) (Units.map (entrywiseHom δ) x) = x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hδδ : δ.comp δ = RingHom.id K := by
    let : Fintype K := Fintype.ofFinite K
    have h4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
    refine RingHom.ext fun c => ?_
    have hc := FiniteField.pow_card c
    rw [h4] at hc
    rw [RingHom.comp_apply, hδ, hδ, ← pow_mul, RingHom.id_apply]
    exact hc
  apply Units.ext
  change entrywise δ (entrywise δ (x : Module.End K (RootModule .G2 K))) = x
  rw [entrywise_entrywise, hδδ, entrywise_id]

theorem exists_eq_mul_inv_of_mul_entrywise_eq_one
    (hK : Nat.card K = 4) (δ : K →+* K) (hδ : ∀ c, δ c = c ^ 2) {u : ModGL .G2 K}
    (hu : u ∈ posUnipotent .G2 K) (h1 : u * Units.map (entrywiseHom δ) u = 1) :
    ∃ v ∈ posUnipotent .G2 K, u = v * (Units.map (entrywiseHom δ) v)⁻¹ := by
  have hUc := card_posUnipotent_four hK
  have : Finite ↥(posUnipotent .G2 K) := Nat.finite_of_card_ne_zero (by rw [hUc]; norm_num)
  refine exists_eq_mul_inv_of_card (Units.map (entrywiseHom δ))
    (units_map_entrywiseHom_sq_involutive hK δ hδ) (fun x hx => ?_) ?_ hu h1
  · obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hx
    rw [units_map_entrywiseHom_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  · rw [hUc, card_fixed hK δ hδ, card_lang hK δ hδ]

end Lang

end CFSG.Quasithin.H13.Ch9.KGFF.G24
