module

public import CFSG.Monster.Existence.TwoPoint.CoPairOrbit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.CoPair

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge
  CFSG.Monster.Existence.CoPair.Native

attribute [local instance] kvLeft

section Generic

variable {G X : Type*} [Group G] [MulAction G X]

theorem exists_equivariant_hom {n : ℕ} {Ω : Set X} (hΩ : Ω.Finite) (p : X → Fin n)
    (hp : ∀ j : Fin n, ∃ x ∈ Ω, p x = j) (a b : G) (σa σb : Equiv.Perm (Fin n))
    (ha : ∀ x ∈ Ω, a • x ∈ Ω ∧ p (a • x) = σa (p x))
    (hb : ∀ x ∈ Ω, b • x ∈ Ω ∧ p (b • x) = σb (p x)) :
    ∃ Φ : Subgroup.closure ({a, b} : Set G) →* Equiv.Perm (Fin n),
      Φ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = σa ∧
      Φ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ = σb := by
  classical
  let D : Subgroup G :=
    { carrier := {g | (∀ x ∈ Ω, g • x ∈ Ω) ∧
        ∃ σ : Equiv.Perm (Fin n), ∀ x ∈ Ω, p (g • x) = σ (p x)}
      one_mem' := ⟨fun x hx => by simpa using hx, 1, fun x _ => by simp⟩
      mul_mem' := fun {g h} hg hh => by
        refine ⟨fun x hx => ?_, ?_⟩
        · rw [mul_smul]
          exact hg.1 _ (hh.1 x hx)
        · obtain ⟨σ, hσ⟩ := hg.2
          obtain ⟨τ, hτ⟩ := hh.2
          refine ⟨σ * τ, fun x hx => ?_⟩
          rw [mul_smul, hσ _ (hh.1 x hx), hτ x hx]
          rfl
      inv_mem' := fun {g} hg => by
        have hinv : ∀ x ∈ Ω, g⁻¹ • x ∈ Ω := fun x hx => by
          have : g ∈ VisCert.invSubgroup Ω hΩ := hg.1
          exact (VisCert.invSubgroup Ω hΩ).inv_mem this x hx
        refine ⟨hinv, ?_⟩
        obtain ⟨σ, hσ⟩ := hg.2
        refine ⟨σ⁻¹, fun x hx => ?_⟩
        have h1 := hσ (g⁻¹ • x) (hinv x hx)
        rw [smul_inv_smul] at h1
        rw [h1]
        simp }
  have haD : a ∈ D := ⟨fun x hx => (ha x hx).1, σa, fun x hx => (ha x hx).2⟩
  have hbD : b ∈ D := ⟨fun x hx => (hb x hx).1, σb, fun x hx => (hb x hx).2⟩
  have hle : Subgroup.closure ({a, b} : Set G) ≤ D :=
    (Subgroup.closure_le _).2 (by rintro _ (rfl | rfl) <;> assumption)
  have huniq : ∀ (g : G) (σ τ : Equiv.Perm (Fin n)), (∀ x ∈ Ω, p (g • x) = σ (p x)) →
      (∀ x ∈ Ω, p (g • x) = τ (p x)) → σ = τ := by
    intro g σ τ h1 h2
    ext j
    obtain ⟨x, hx, rfl⟩ := hp j
    rw [← h1 x hx, ← h2 x hx]
  let φ : Subgroup.closure ({a, b} : Set G) → Equiv.Perm (Fin n) :=
    fun g => Classical.choose (hle g.2).2
  have hφ : ∀ (g : Subgroup.closure ({a, b} : Set G)), ∀ x ∈ Ω,
      p ((g : G) • x) = φ g (p x) := fun g => Classical.choose_spec (hle g.2).2
  refine ⟨{ toFun := φ, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · exact huniq ((1 : Subgroup.closure ({a, b} : Set G)) : G) _ 1 (hφ 1) (fun x _ => by simp)
  · intro g h
    refine huniq ((g * h : Subgroup.closure ({a, b} : Set G)) : G) _ (φ g * φ h) (hφ _)
      fun x hx => ?_
    rw [Subgroup.coe_mul, mul_smul, hφ g _ ((hle h.2).1 x hx), hφ h x hx]
    rfl
  · exact huniq a _ σa (hφ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩)
      (fun x hx => (ha x hx).2)
  · exact huniq b _ σb (hφ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩)
      (fun x hx => (hb x hx).2)

theorem range_eq_closure {a b : G} {n : ℕ} {σa σb : Equiv.Perm (Fin n)}
    (Φ : Subgroup.closure ({a, b} : Set G) →* Equiv.Perm (Fin n))
    (h1 : Φ ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = σa)
    (h2 : Φ ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ = σb) :
    Φ.range = Subgroup.closure {σa, σb} := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [h1]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [h2]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => exact (Φ.map_one ▸ Subgroup.one_mem _ : Φ 1 ∈ _)
    | mul x y hx hy ihx ihy =>
      have := Subgroup.mul_mem _ ihx ihy
      rwa [← map_mul] at this
    | inv x hx ih =>
      have := Subgroup.inv_mem _ ih
      rwa [← map_inv] at this
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, h1⟩
    · exact ⟨_, h2⟩

end Generic

@[expose] def labFun (n : ℕ) (hn : 0 < n) (F : Set ℕ) (f : ℕ → ℕ) (x : L2) : Fin n :=
  open Classical in
  if h : ∃ v ∈ F, dec v = x then ⟨f (Classical.choose h) % n, Nat.mod_lt _ hn⟩ else ⟨0, hn⟩

theorem labFun_dec {n : ℕ} (hn : 0 < n) {F : Set ℕ} (hF : ∀ v ∈ F, v < 2 ^ 24) (f : ℕ → ℕ)
    {v : ℕ} (hv : v ∈ F) : labFun n hn F f (dec v) = ⟨f v % n, Nat.mod_lt _ hn⟩ := by
  classical
  have h : ∃ w ∈ F, dec w = dec v := ⟨v, hv, rfl⟩
  rw [labFun, dite_eq_left h]
  obtain ⟨hw, hdec⟩ := Classical.choose_spec h
  have := dec_injective (hF _ hw) (hF _ hv) hdec
  simp only [this]

theorem eqPoint_spec {a b : List ℕ} {σa σb : ℕ → ℕ} {n : ℕ} {pl : ℕ → ℕ} {v : ℕ}
    (h : eqPoint a b σa σb n pl v = true) (hv : pl v ≠ 0) :
    1 ≤ pl v ∧ pl v ≤ n ∧ actXY a v < 2 ^ 24 ∧ actXY b v < 2 ^ 24 ∧
      pl (actXY a v) = σa (pl v - 1) + 1 ∧ pl (actXY b v) = σb (pl v - 1) + 1 := by
  unfold eqPoint at h
  have h0 : (pl v == 0) = false := by simpa using hv
  simpa only [h0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, and_assoc] using h

theorem exists_hom_of_eqCheck
    {a b : List ℕ} {σa σb : ℕ → ℕ} {n chunks : ℕ} {T : EqTables}
    (hn : 0 < n) (hc : 0 < chunks) (h : eqCheck a b σa σb n T chunks = true)
    (τa τb : Equiv.Perm (Fin n)) (hτa : ∀ i : Fin n, (τa i : ℕ) = σa i)
    (hτb : ∀ i : Fin n, (τb i : ℕ) = σb i) :
    ∃ Φ : Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0)) →* Equiv.Perm (Fin n),
      Φ ⟨(xyK a)⁻¹, Subgroup.subset_closure (Set.mem_insert _ _)⟩ = τa ∧
      Φ ⟨(xyK b)⁻¹, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ = τb := by
  simp only [eqCheck, Bool.and_eq_true] at h
  obtain ⟨hpar, hrep⟩ := h
  have hpt := VisCert.parAll_spec hc hpar
  have hrep' := (VisCert.allFrom_iff _ 0 n).1 hrep
  let pl : ℕ → ℕ := rd16 T.pl
  let F : Set ℕ := {v | v < 2 ^ 24 ∧ pl v ≠ 0}
  let f : ℕ → ℕ := fun v => pl v - 1
  have hFlt : ∀ v ∈ F, v < 2 ^ 24 := fun v hv => hv.1
  have hspec : ∀ v ∈ F, 1 ≤ pl v ∧ pl v ≤ n ∧ actXY a v < 2 ^ 24 ∧ actXY b v < 2 ^ 24 ∧
      pl (actXY a v) = σa (pl v - 1) + 1 ∧ pl (actXY b v) = σb (pl v - 1) + 1 :=
    fun v hv => eqPoint_spec (hpt v hv.1) hv.2
  have hFa : ∀ v ∈ F, actXY a v ∈ F ∧ f (actXY a v) = σa (f v) := fun v hv => by
    obtain ⟨-, -, ha, -, hpa, -⟩ := hspec v hv
    exact ⟨⟨ha, by omega⟩, by simp only [f]; omega⟩
  have hFb : ∀ v ∈ F, actXY b v ∈ F ∧ f (actXY b v) = σb (f v) := fun v hv => by
    obtain ⟨-, -, -, hb, -, hpb⟩ := hspec v hv
    exact ⟨⟨hb, by omega⟩, by simp only [f]; omega⟩
  have hflt : ∀ v ∈ F, f v < n := fun v hv => by
    obtain ⟨h1, h2, -⟩ := hspec v hv
    simp only [f]
    omega
  have hjF : ∀ j : Fin n, ∃ v ∈ F, f v = j := fun j => by
    have hj := hrep' j j.2
    simp only [zero_add, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hj
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨T.rep[(j : ℕ)]!, ⟨hj1, ?_⟩, ?_⟩
    · show rd16 T.pl T.rep[(j : ℕ)]! ≠ 0
      omega
    · show rd16 T.pl T.rep[(j : ℕ)]! - 1 = j
      omega
  have hΩ : (dec '' F).Finite :=
    ((Set.finite_lt_nat (2 ^ 24)).subset fun v hv => hv.1).image dec
  have hlab : ∀ v ∈ F, (labFun n hn F f (dec v)).val = f v := fun v hv => by
    rw [labFun_dec hn hFlt f hv]
    exact Nat.mod_eq_of_lt (hflt v hv)
  obtain ⟨Φ, h1, h2⟩ := exists_equivariant_hom (G := Kstab v0) (X := L2) hΩ (labFun n hn F f)
    (fun j => by
      obtain ⟨v, hv, hfv⟩ := hjF j
      exact ⟨dec v, ⟨v, hv, rfl⟩, Fin.ext (by rw [hlab v hv, hfv])⟩)
    (xyK a)⁻¹ (xyK b)⁻¹ τa τb
    (fun x ⟨v, hv, hx⟩ => by
      subst hx
      rw [kvLeft_inv_smul, kOp_xyK_dec]
      obtain ⟨hmem, hfa⟩ := hFa v hv
      refine ⟨⟨_, hmem, rfl⟩, Fin.ext ?_⟩
      rw [hlab _ hmem, hfa, hτa, hlab v hv])
    (fun x ⟨v, hv, hx⟩ => by
      subst hx
      rw [kvLeft_inv_smul, kOp_xyK_dec]
      obtain ⟨hmem, hfb⟩ := hFb v hv
      refine ⟨⟨_, hmem, rfl⟩, Fin.ext ?_⟩
      rw [hlab _ hmem, hfb, hτb, hlab v hv])
  exact ⟨Φ, h1, h2⟩

theorem kvStab_equiv_of_eqCheck
    {a b : List ℕ} {σa σb : ℕ → ℕ} {n chunks : ℕ} {T : EqTables}
    (hn : 0 < n) (hc : 0 < chunks) (h : eqCheck a b σa σb n T chunks = true)
    (τa τb : Equiv.Perm (Fin n)) (hτa : ∀ i : Fin n, (τa i : ℕ) = σa i)
    (hτb : ∀ i : Fin n, (τb i : ℕ) = σb i) {w : ℕ} (hwa : actXY a w = w) (hwb : actXY b w = w)
    {H : Subgroup (Equiv.Perm (Fin n))} (hH : Subgroup.closure {τa, τb} = H)
    (hcard : Nat.card (kvStab (dec w)) = Nat.card H) :
    Nonempty (kvStab (dec w) ≃* H) := by
  obtain ⟨Φ, h1, h2⟩ := exists_hom_of_eqCheck hn hc h τa τb hτa hτb
  have hA : Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0)) ≤ kvStab (dec w) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (kvStab (dec w)).inv_mem (by rw [mem_kvStab, kOp_xyK_dec, hwa])
    · exact (kvStab (dec w)).inv_mem (by rw [mem_kvStab, kOp_xyK_dec, hwb])
  have hrange : Φ.range = H := (range_eq_closure Φ h1 h2).trans hH
  have hle : Nat.card H ≤
      Nat.card ↥(Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0))) := by
    rw [← hrange]
    exact Nat.card_le_card_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hAeq : Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0)) = kvStab (dec w) :=
    Subgroup.eq_of_le_of_card_ge hA (by rw [hcard]; exact hle)
  have hcardA : Nat.card ↥(Subgroup.closure ({(xyK a)⁻¹, (xyK b)⁻¹} : Set (Kstab v0))) =
      Nat.card H := by
    rw [hAeq, hcard]
  have hbij : Function.Bijective Φ.rangeRestrict := by
    refine Φ.rangeRestrict_surjective.bijective_of_nat_card_le ?_
    rw [hrange, hcardA]
  exact ⟨(MulEquiv.subgroupCongr hAeq.symm).trans
    ((MulEquiv.ofBijective Φ.rangeRestrict hbij).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.Monster.Existence.CoPair
