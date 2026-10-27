module

public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.Quasithin.SmithCurtis

theorem sum_sum_eq_sum_mult {ι α N : Type*} [AddCommMonoid N] [DecidableEq α]
    {I : Finset ι} {T : Finset α} (S : ι → Finset α) (hsub : ∀ c ∈ I, S c ⊆ T) (f : α → N) :
    ∑ c ∈ I, ∑ d ∈ S c, f d = ∑ d ∈ T, (I.filter fun c => d ∈ S c).card • f d := by
  have h1 : ∀ c ∈ I, ∑ d ∈ S c, f d = ∑ d ∈ T, if d ∈ S c then f d else 0 := by
    intro c hc
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub c hc)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const]

theorem sum_sum_eq_of_cover {ι α M : Type*} [AddCommMonoid M] [DecidableEq α]
    {I : Finset ι} {T : Finset α} (S : ι → Finset α) (hsub : ∀ c ∈ I, S c ⊆ T)
    (hcov : ∀ d ∈ T, ∃ c ∈ I, d ∈ S c) (hcard : ∑ c ∈ I, (S c).card = T.card) (f : α → M) :
    ∑ c ∈ I, ∑ d ∈ S c, f d = ∑ d ∈ T, f d := by
  have hmult : ∀ d ∈ T, (I.filter fun c => d ∈ S c).card = 1 := by
    have hle : ∀ d ∈ T, 1 ≤ (I.filter fun c => d ∈ S c).card := by
      intro d hd
      obtain ⟨c, hc, hdc⟩ := hcov d hd
      exact Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hdc⟩⟩
    have hsum : ∑ d ∈ T, 1 = ∑ d ∈ T, (I.filter fun c => d ∈ S c).card := by
      have h := sum_sum_eq_sum_mult S hsub fun _ => (1 : ℕ)
      simp only [smul_eq_mul, mul_one] at h
      rw [← h, ← Finset.card_eq_sum_ones, ← hcard]
      exact Finset.sum_congr rfl fun c _ => Finset.card_eq_sum_ones _
    exact fun d hd => ((Finset.sum_eq_sum_iff_of_le hle).mp hsum d hd).symm
  rw [sum_sum_eq_sum_mult S hsub f]
  exact Finset.sum_congr rfl fun d hd => by rw [hmult d hd, one_smul]

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

@[expose] noncomputable def heckeDeg (U : Subgroup G) (g : G) : ℕ :=
  (U.map (MulAut.conj g).toMonoidHom).relIndex U

variable [Finite G]

@[expose] noncomputable def dcos (U : Subgroup G) (g : G) : Finset (G ⧸ U) :=
  (Set.toFinite {c : G ⧸ U | ∃ u ∈ U, c = ((u * g : G) : G ⧸ U)}).toFinset

theorem mem_dcos {U : Subgroup G} {g : G} {c : G ⧸ U} :
    c ∈ dcos U g ↔ ∃ u ∈ U, c = ((u * g : G) : G ⧸ U) :=
  Set.Finite.mem_toFinset _

@[expose] noncomputable def hecke (U : Subgroup G) (g : G) : V →ₗ[k] V :=
  ∑ c ∈ dcos U g, ρ c.out

theorem hecke_apply (U : Subgroup G) (g : G) (v : V) :
    hecke ρ U g v = ∑ c ∈ dcos U g, ρ c.out v := by
  rw [hecke, LinearMap.sum_apply]

omit [Finite G] in
theorem out_act {U : Subgroup G} {m : V} (hm : m ∈ fixSub ρ U) (x : G) :
    ρ ((x : G ⧸ U).out) m = ρ x m := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul U x
  rw [e, ← act_mul, hm h h.2]

omit [Finite G] in
theorem out_act' {U : Subgroup G} {m : V} (hm : m ∈ fixSub ρ U) (x : G) (c : G ⧸ U) :
    ρ ((x • c).out) m = ρ (x * c.out) m := by
  rw [← out_act ρ hm (x * c.out)]
  congr 3
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rfl

theorem smul_mem_dcos {U : Subgroup G} {g u : G} (hu : u ∈ U) {c : G ⧸ U}
    (hc : c ∈ dcos U g) : u • c ∈ dcos U g := by
  obtain ⟨u', hu', rfl⟩ := mem_dcos.mp hc
  exact mem_dcos.mpr ⟨u * u', mul_mem hu hu', by rw [MulAction.Quotient.smul_coe, smul_eq_mul,
    mul_assoc]⟩

theorem hecke_mem_fixSub {U : Subgroup G} (g : G) {m : V} (hm : m ∈ fixSub ρ U) :
    hecke ρ U g m ∈ fixSub ρ U := by
  intro u hu
  rw [hecke_apply, map_sum]
  simp only [act_mul, ← out_act' ρ hm]
  exact Finset.sum_nbij' (fun c => u • c) (fun c => u⁻¹ • c)
    (fun c hc => smul_mem_dcos hu hc) (fun c hc => smul_mem_dcos (inv_mem hu) hc)
    (fun c _ => inv_smul_smul u c) (fun c _ => smul_inv_smul u c) fun c _ => rfl

theorem hecke_of_normalizes {U : Subgroup G} {g : G} (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) {m : V}
    (hm : m ∈ fixSub ρ U) : hecke ρ U g m = ρ g m := by
  have hd : dcos U g = {((g : G) : G ⧸ U)} := by
    ext c
    rw [mem_dcos, Finset.mem_singleton]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [QuotientGroup.eq]
      have e : (u * g)⁻¹ * g = (g⁻¹ * u * g)⁻¹ := by group
      rw [e]
      exact inv_mem (hg u hu)
    · rintro rfl
      exact ⟨1, one_mem _, by rw [one_mul]⟩
  rw [hecke_apply, hd, Finset.sum_singleton, out_act ρ hm]

theorem hecke_one {U : Subgroup G} {m : V} (hm : m ∈ fixSub ρ U) : hecke ρ U 1 m = m := by
  rw [hecke_of_normalizes ρ (fun u hu => by rwa [inv_one, one_mul, mul_one]) hm, map_one,
    Module.End.one_apply]

theorem hecke_mul_left {U : Subgroup G} {h : G} (hh : ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (hh' : ∀ u ∈ U, h⁻¹ * u * h ∈ U) (g : G) {m : V} (hm : m ∈ fixSub ρ U) :
    hecke ρ U (h * g) m = ρ h (hecke ρ U g m) := by
  rw [hecke_apply, hecke_apply, map_sum]
  simp only [act_mul, ← out_act' ρ hm]
  symm
  refine Finset.sum_nbij' (fun c => h • c) (fun c => h⁻¹ • c) (fun c hc => ?_) (fun c hc => ?_)
    (fun c _ => inv_smul_smul h c) (fun c _ => smul_inv_smul h c) fun c _ => rfl
  · obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
    refine mem_dcos.mpr ⟨h * u * h⁻¹, hh u hu, ?_⟩
    rw [MulAction.Quotient.smul_coe, smul_eq_mul]
    group
  · obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
    refine mem_dcos.mpr ⟨h⁻¹ * u * h, hh' u hu, ?_⟩
    rw [MulAction.Quotient.smul_coe, smul_eq_mul]
    group

@[expose] noncomputable def rmul (U : Subgroup G) (h : G) (hh : ∀ u ∈ U, h⁻¹ * u * h ∈ U) :
    G ⧸ U → G ⧸ U :=
  Quotient.map' (· * h) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have e : (a * h)⁻¹ * (b * h) = h⁻¹ * (a⁻¹ * b) * h := by group
    rw [e]
    exact hh _ hab

omit [Finite G] in
theorem rmul_mk (U : Subgroup G) (h : G) (hh : ∀ u ∈ U, h⁻¹ * u * h ∈ U) (x : G) :
    rmul U h hh (x : G ⧸ U) = ((x * h : G) : G ⧸ U) := rfl

theorem hecke_mul_right {U : Subgroup G} {h : G} (hh : ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (hh' : ∀ u ∈ U, h⁻¹ * u * h ∈ U) (g : G) {m : V} (hm : m ∈ fixSub ρ U) :
    hecke ρ U (g * h) m = hecke ρ U g (ρ h m) := by
  have hhm : ρ h m ∈ fixSub ρ U := act_mem_fixSub ρ hh' hm
  have hinv : ∀ u ∈ U, (h⁻¹)⁻¹ * u * h⁻¹ ∈ U := fun u hu => by rw [inv_inv]; exact hh u hu
  rw [hecke_apply, hecke_apply]
  refine Finset.sum_nbij' (rmul U h⁻¹ hinv) (rmul U h hh') (fun c hc => ?_) (fun c hc => ?_)
    (fun c _ => ?_) (fun c _ => ?_) fun c _ => ?_
  · obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
    exact mem_dcos.mpr ⟨u, hu, by rw [rmul_mk]; group⟩
  · obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hc
    exact mem_dcos.mpr ⟨u, hu, by rw [rmul_mk]; group⟩
  · induction c using QuotientGroup.induction_on with
    | H x => rw [rmul_mk, rmul_mk, inv_mul_cancel_right]
  · induction c using QuotientGroup.induction_on with
    | H x => rw [rmul_mk, rmul_mk, mul_inv_cancel_right]
  · induction c using QuotientGroup.induction_on with
    | H x =>
      rw [rmul_mk, out_act ρ hm, out_act ρ hhm, act_mul, inv_mul_cancel_right]

theorem card_dcos (U : Subgroup G) (g : G) : (dcos U g).card = heckeDeg U g := by
  have hset : ((dcos U g : Finset (G ⧸ U)) : Set (G ⧸ U)) =
      MulAction.orbit U ((g : G) : G ⧸ U) := by
    ext c
    rw [Finset.mem_coe, mem_dcos, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, by rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, by rw [Subgroup.smul_def, MulAction.Quotient.smul_coe, smul_eq_mul]⟩
  have hstab : MulAction.stabilizer U ((g : G) : G ⧸ U) =
      (U.map (MulAut.conj g).toMonoidHom).subgroupOf U := by
    ext u
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def,
      MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    constructor
    · intro h
      refine ⟨g⁻¹ * u * g, ?_, by simp [MulAut.conj_apply]; group⟩
      have e : g⁻¹ * u * g = ((u * g)⁻¹ * g)⁻¹ := by group
      rw [e]
      exact inv_mem h
    · rintro ⟨x, hx, e⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      have e2 : ((u : G) * g)⁻¹ * g = x⁻¹ := by rw [← e]; group
      rw [e2]
      exact inv_mem hx
  rw [heckeDeg, Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, ← hset,
    Set.ncard_coe_finset]

theorem hecke_hecke {U : Subgroup G} {g g' : G}
    (hmul : ∀ u ∈ U, ∃ a ∈ U, ∃ b ∈ U, g * u * g' = a * (g * g') * b)
    (hdeg : heckeDeg U g * heckeDeg U g' = heckeDeg U (g * g'))
    {m : V} (hm : m ∈ fixSub ρ U) : hecke ρ U g (hecke ρ U g' m) = hecke ρ U (g * g') m := by
  classical
  set S : G ⧸ U → Finset (G ⧸ U) := fun c => (dcos U g').image fun c' => c.out • c'
  have hinner : ∀ c : G ⧸ U, ρ c.out (hecke ρ U g' m) = ∑ d ∈ S c, ρ d.out m := by
    intro c
    rw [hecke_apply, map_sum, Finset.sum_image fun a _ b _ hab => MulAction.injective _ hab]
    simp only [act_mul, out_act' ρ hm]
  rw [hecke_apply, Finset.sum_congr rfl fun c _ => hinner c, hecke_apply]
  refine sum_sum_eq_of_cover S (fun c hc d hd => ?_) (fun d hd => ?_) ?_ _
  · obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨u₁, hu₁, rfl⟩ := mem_dcos.mp hc
    obtain ⟨u₂, hu₂, rfl⟩ := mem_dcos.mp hc'
    obtain ⟨v₁, hv₁⟩ := QuotientGroup.mk_out_eq_mul U (u₁ * g)
    obtain ⟨a, ha, b, hb, e⟩ := hmul (v₁ * u₂) (mul_mem v₁.2 hu₂)
    refine mem_dcos.mpr ⟨u₁ * a, mul_mem hu₁ ha, ?_⟩
    rw [hv₁, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have e2 : (u₁ * g * v₁ * (u₂ * g'))⁻¹ * (u₁ * a * (g * g')) = b⁻¹ := by
      have e3 : u₁ * g * v₁ * (u₂ * g') = u₁ * (g * (v₁ * u₂) * g') := by group
      rw [e3, e]
      group
    rw [e2]
    exact inv_mem hb
  · obtain ⟨u, hu, rfl⟩ := mem_dcos.mp hd
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul U (u * g)
    refine ⟨((u * g : G) : G ⧸ U), mem_dcos.mpr ⟨u, hu, rfl⟩, Finset.mem_image.mpr
      ⟨((v⁻¹ : U) * g' : G), mem_dcos.mpr ⟨_, (v⁻¹ : U).2, rfl⟩, ?_⟩⟩
    rw [hv, MulAction.Quotient.smul_coe, smul_eq_mul]
    congr 1
    simp only [InvMemClass.coe_inv]
    group
  · have hS : ∀ c : G ⧸ U, (S c).card = heckeDeg U g' := fun c => by
      rw [Finset.card_image_of_injective _ (MulAction.injective _), card_dcos]
    simp only [hS, Finset.sum_const, smul_eq_mul, card_dcos]
    exact hdeg

end CFSG.Quasithin.SmithCurtis
