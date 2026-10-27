module

public import CFSG.Quasithin.H13.L32AStRec
public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.H6

variable {G : Type} [Group G]

structure SecMod (L X Y : Subgroup G) (θ : ↥L →* Γ) : Prop where
  le : Y ≤ X
  normX : L ≤ Subgroup.normalizer (X : Set G)
  normY : L ≤ Subgroup.normalizer (Y : Set G)
  comm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ Y
  sq : ∀ a ∈ X, a ^ 2 ∈ Y
  surj : Function.Surjective θ
  ker : ∀ l : ↥L, θ l = 1 → ∀ x ∈ X, (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ Y
  faithful : ∀ l : ↥L, (∀ x ∈ X, (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ Y) → θ l = 1

namespace SecMod

variable {L X Y : Subgroup G} {θ : ↥L →* Γ}

theorem normal (D : SecMod L X Y θ) : (Y.subgroupOf X).Normal := by
  refine ⟨fun n hn x => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 := D.comm _ x.2 _ (D.le hn)
  have e : ((x * n * x⁻¹ : ↥X) : G) = ((x : G) * n * (x : G)⁻¹ * (n : G)⁻¹) * n := by
    push_cast
    group
  rw [e]
  exact mul_mem h1 hn

@[expose] def conjX (D : SecMod L X Y θ) (l : ↥L) : ↥X →* ↥X where
  toFun x := ⟨(l : G) * x * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (D.normX l.2) x).mp x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem coe_conjX (D : SecMod L X Y θ) (l : ↥L) (x : ↥X) :
    ((D.conjX l x : ↥X) : G) = (l : G) * x * (l : G)⁻¹ := rfl


theorem mk_eq_mk_iff (D : SecMod L X Y θ) (a b : ↥X) :
    (QuotientGroup.mk a : ↥X ⧸ Y.subgroupOf X) = QuotientGroup.mk b ↔
      (a : G) * (b : G)⁻¹ ∈ Y := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hY : ∀ (c : ↥X) (y : G), y ∈ Y → (c : G) * y * (c : G)⁻¹ ∈ Y := fun c y hy => by
    have := D.normal.conj_mem ⟨y, D.le hy⟩ (Subgroup.mem_subgroupOf.mpr hy) c
    rwa [Subgroup.mem_subgroupOf] at this
  push_cast
  constructor
  · intro h
    have := hY a _ (inv_mem h)
    rwa [show (a : G) * ((a : G)⁻¹ * b)⁻¹ * (a : G)⁻¹ = a * (b : G)⁻¹ by group] at this
  · intro h
    have := hY a⁻¹ _ (inv_mem h)
    rwa [show ((a⁻¹ : ↥X) : G) * ((a : G) * (b : G)⁻¹)⁻¹ * ((a⁻¹ : ↥X) : G)⁻¹ =
      (a : G)⁻¹ * b by push_cast; group] at this

theorem exists_steinberg [Finite G] (D : SecMod L X Y θ) (h65 : VolI_H_6_5) {m : G} (hm : m ∈ X)
    (hmT : ∀ l : ↥L, θ l ∈ H6.borel → (l : G) * m * (l : G)⁻¹ * m⁻¹ ∈ Y)
    (hgen : ∀ s ∈ X,
      s ∈ Subgroup.closure ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)))
    {W : Subgroup G}
    (hW : W = Subgroup.closure ({y | ∃ l : ↥L, θ l ∈ Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪
      (Y : Set G)))
    (hWY : Y.relIndex W = 4) {x : ↥L} (hx3 : θ x ^ 3 = 1) (hx1 : θ x ≠ 1) {C : Subgroup G}
    (hC : ∀ s, s ∈ C ↔ s ∈ X ∧ (x : G) * s * (x : G)⁻¹ * s⁻¹ ∈ Y)
    (hidx : Y.relIndex X = 64 * Y.relIndex C) :
    ∃ χ : ↥X →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
      χ.ker = Y.subgroupOf X ∧ (∀ s, RuType.IsTraceZero (Multiplicative.toAdd (χ s))) ∧
      (∀ A, RuType.IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
      ∀ (l : ↥L) (s t : ↥X), (t : G) = l * s * (l : G)⁻¹ →
        χ t = Multiplicative.ofAdd (RuType.stAct (θ l) (Multiplicative.toAdd (χ s))) := by
  classical
  have hN : (Y.subgroupOf X).Normal := D.normal
  set N := Y.subgroupOf X with hNdef
  have hle : ∀ l : ↥L, N ≤ N.comap (D.conjX l) := fun l n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_conjX]
    exact (Subgroup.mem_normalizer_iff.mp (D.normY l.2) _).mp (Subgroup.mem_subgroupOf.mp hn)
  let actQ : ↥L → (↥X ⧸ N) →* (↥X ⧸ N) := fun l => QuotientGroup.map N N (D.conjX l) (hle l)
  have hactQ : ∀ (l : ↥L) (s : ↥X),
      actQ l (QuotientGroup.mk s) = QuotientGroup.mk (D.conjX l s) := fun _ _ => rfl
  let actM : ↥L →* AddMonoid.End (Additive (↥X ⧸ N)) :=
    { toFun := fun l => MonoidHom.toAdditive (actQ l)
      map_one' := by
        apply AddMonoidHom.ext
        intro q
        induction q using QuotientGroup.induction_on with
        | H s =>
        show Additive.ofMul (actQ 1 (QuotientGroup.mk s)) = Additive.ofMul (QuotientGroup.mk s)
        rw [hactQ]
        congr 2
        apply Subtype.ext
        simp [coe_conjX]
      map_mul' := fun l l' => by
        apply AddMonoidHom.ext
        intro q
        induction q using QuotientGroup.induction_on with
        | H s =>
        show Additive.ofMul (actQ (l * l') (QuotientGroup.mk s)) =
          Additive.ofMul (actQ l (actQ l' (QuotientGroup.mk s)))
        rw [hactQ, hactQ, hactQ]
        congr 2
        apply Subtype.ext
        simp only [coe_conjX, Subgroup.coe_mul]
        group }
  have hactM : ∀ (l : ↥L) (s : ↥X), actM l (Additive.ofMul (QuotientGroup.mk s)) =
      Additive.ofMul (QuotientGroup.mk (D.conjX l s)) := fun _ _ => rfl
  have hker : θ.ker ≤ actM.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    apply AddMonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H s =>
    show actM l (Additive.ofMul (QuotientGroup.mk s)) = Additive.ofMul (QuotientGroup.mk s)
    rw [hactM]
    congr 1
    rw [D.mk_eq_mk_iff, coe_conjX]
    exact D.ker l hl s s.2
  have hact_eq : ∀ l l' : ↥L, θ l = θ l' → actM l = actM l' := by
    intro l l' h
    have h1 : l'⁻¹ * l ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h3 := hker h1
    rw [MonoidHom.mem_ker] at h3
    calc actM l = actM (l' * (l'⁻¹ * l)) := by rw [mul_inv_cancel_left]
      _ = actM l' := by rw [map_mul, h3, mul_one]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ →* AddMonoid.End (Additive (↥X ⧸ N)), ∀ l : ↥L, ρ (θ l) = actM l := by
    refine ⟨{ toFun := fun g => actM (Function.surjInv D.surj g)
              map_one' := ?_
              map_mul' := fun g g' => ?_ }, fun l => ?_⟩
    · show actM (Function.surjInv D.surj 1) = 1
      rw [hact_eq _ 1 (by rw [Function.surjInv_eq D.surj, map_one]), map_one]
    · show actM (Function.surjInv D.surj (g * g')) =
        actM (Function.surjInv D.surj g) * actM (Function.surjInv D.surj g')
      rw [← map_mul]
      exact hact_eq _ _ (by rw [map_mul, Function.surjInv_eq D.surj, Function.surjInv_eq D.surj,
        Function.surjInv_eq D.surj])
    · exact hact_eq _ _ (Function.surjInv_eq D.surj (θ l))
  have hρmk : ∀ (l : ↥L) (s : ↥X), ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
      Additive.ofMul (QuotientGroup.mk (D.conjX l s)) := fun l s => by rw [hρ]; rfl
  have : Finite (Additive (↥X ⧸ N)) := Finite.of_equiv _ Additive.ofMul
  set m0 : Additive (↥X ⧸ N) := Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩) with hm0
  have h2 : ∀ y : Additive (↥X ⧸ N), y + y = 0 := by
    intro y
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective y
    induction q using QuotientGroup.induction_on with
    | H s =>
    rw [← ofMul_mul, ← QuotientGroup.mk_mul, ← ofMul_one, ← QuotientGroup.mk_one]
    congr 1
    rw [D.mk_eq_mk_iff]
    have := D.sq _ s.2
    simpa [pow_two] using this
  have hfaith : ∀ g : Γ, (∀ y : Additive (↥X ⧸ N), ρ g y = y) → g = 1 := by
    intro g hg
    obtain ⟨l, rfl⟩ := D.surj g
    apply D.faithful l
    intro s hs
    have h1 := hg (Additive.ofMul (QuotientGroup.mk ⟨s, hs⟩))
    rw [hρmk] at h1
    have h3 := Additive.ofMul.injective h1
    rw [D.mk_eq_mk_iff, coe_conjX] at h3
    exact h3
  have hmT' : ∀ t ∈ H6.borel, ρ t m0 = m0 := by
    intro t ht
    obtain ⟨l, rfl⟩ := D.surj t
    rw [hm0, hρmk]
    congr 1
    rw [D.mk_eq_mk_iff, coe_conjX]
    exact hmT l ht
  have hmkY : ∀ (z : G) (hz : z ∈ Y),
      (Additive.ofMul (QuotientGroup.mk ⟨z, D.le hz⟩ : ↥X ⧸ N) : Additive (↥X ⧸ N)) = 0 := by
    intro z hz
    rw [← ofMul_one, ← QuotientGroup.mk_one]
    congr 1
    rw [D.mk_eq_mk_iff]
    simpa using hz
  have hclos : ∀ (P : AddSubgroup (Additive (↥X ⧸ N))) (Sg : Set G) (hSg : Sg ⊆ X),
      (∀ z (hz : z ∈ Sg), (Additive.ofMul
        (QuotientGroup.mk ⟨z, Set.mem_of_mem_of_subset hz hSg⟩ : ↥X ⧸ N) :
        Additive (↥X ⧸ N)) ∈ P) →
      ∀ z ∈ Subgroup.closure Sg, ∃ hz : z ∈ X,
        (Additive.ofMul (QuotientGroup.mk ⟨z, hz⟩ : ↥X ⧸ N) : Additive (↥X ⧸ N)) ∈ P := by
    intro P Sg hSg hP z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz => exact ⟨Set.mem_of_mem_of_subset hz hSg, hP z hz⟩
    | one =>
      refine ⟨one_mem _, ?_⟩
      rw [show (⟨1, one_mem X⟩ : ↥X) = 1 from rfl, QuotientGroup.mk_one, ofMul_one]
      exact zero_mem _
    | mul a b _ _ iha ihb =>
      obtain ⟨ha, ha'⟩ := iha
      obtain ⟨hb, hb'⟩ := ihb
      refine ⟨mul_mem ha hb, ?_⟩
      rw [show (⟨a * b, mul_mem ha hb⟩ : ↥X) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl,
        QuotientGroup.mk_mul, ofMul_mul]
      exact add_mem ha' hb'
    | inv a _ iha =>
      obtain ⟨ha, ha'⟩ := iha
      refine ⟨inv_mem ha, ?_⟩
      rw [show (⟨a⁻¹, inv_mem ha⟩ : ↥X) = (⟨a, ha⟩)⁻¹ from rfl, QuotientGroup.mk_inv,
        ofMul_inv]
      exact neg_mem ha'
  have hgen' : AddSubgroup.closure (Set.range fun g : Γ => ρ g m0) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective y
    induction q using QuotientGroup.induction_on with
    | H s =>
    have hSg : ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)) ⊆ X := by
      rintro _ (⟨l, rfl⟩ | hy)
      · exact (D.conjX l ⟨m, hm⟩).2
      · exact D.le hy
    obtain ⟨hz, h⟩ := hclos (AddSubgroup.closure (Set.range fun g : Γ => ρ g m0)) _ hSg
      (fun z hz => by
      rcases hz with ⟨l, rfl⟩ | hzY
      · refine AddSubgroup.subset_closure ⟨θ l, ?_⟩
        show ρ (θ l) (Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩)) = _
        rw [hρmk]
        rfl
      · rw [hmkY z hzY]
        exact zero_mem _) s (hgen s s.2)
    exact h
  have hcardImg : ∀ Z : Subgroup G, Z ≤ X →
      Nat.card ↥(((Z.subgroupOf X).map (QuotientGroup.mk' N)).toAddSubgroup) = Y.relIndex Z := by
    intro Z hZX
    have e : Nat.card ↥(((Z.subgroupOf X).map (QuotientGroup.mk' N)).toAddSubgroup) =
        Nat.card ↥((Z.subgroupOf X).map (QuotientGroup.mk' N)) :=
      Nat.card_congr (Additive.toMul.subtypeEquiv fun _ => Iff.rfl)
    rw [e, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hNdef,
      Subgroup.relIndex_subgroupOf hZX]
  have hl' : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m0 = y}) = 4 := by
    have hSg : ({y | ∃ l : ↥L, θ l ∈ Ll ∧ (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)) ⊆ X := by
      rintro _ (⟨l, -, rfl⟩ | hy)
      · exact (D.conjX l ⟨m, hm⟩).2
      · exact D.le hy
    have hWX : W ≤ X := by
      rw [hW, Subgroup.closure_le]
      exact hSg
    have heq : AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m0 = y} =
        ((W.subgroupOf X).map (QuotientGroup.mk' N)).toAddSubgroup := by
      apply le_antisymm
      · rw [AddSubgroup.closure_le]
        rintro _ ⟨g, hg, rfl⟩
        obtain ⟨l, rfl⟩ := D.surj g
        rw [hm0, hρmk]
        refine ⟨D.conjX l ⟨m, hm⟩, (Subgroup.mem_subgroupOf.mpr ?_ : _ ∈ W.subgroupOf X), rfl⟩
        rw [coe_conjX, hW]
        exact Subgroup.subset_closure (Or.inl ⟨l, hg, rfl⟩)
      · rintro y ⟨w, hw, hwy⟩
        have hw' : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
        rw [hW] at hw'
        obtain ⟨hz, h⟩ := hclos (AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m0 = y}) _ hSg
          (fun z hz => by
          rcases hz with ⟨l, hl, rfl⟩ | hzY
          · refine AddSubgroup.subset_closure ⟨θ l, hl, ?_⟩
            show ρ (θ l) (Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩)) = _
            rw [hρmk]
            rfl
          · rw [hmkY z hzY]
            exact zero_mem _) w hw'
        have e : y = Additive.ofMul (QuotientGroup.mk w) := by
          rw [← ofMul_toMul y, ← hwy]
          rfl
        rw [e]
        exact h
    rw [heq, hcardImg W hWX, hWY]
  have hidx' : Nat.card (Additive (↥X ⧸ N)) =
      64 * Nat.card {y : Additive (↥X ⧸ N) // ρ (θ x) y = y} := by
    have hCX : C ≤ X := fun s hs => ((hC s).mp hs).1
    have hYC : Y ≤ C := fun y hy => (hC y).mpr ⟨D.le hy, mul_mem
      ((Subgroup.mem_normalizer_iff.mp (D.normY x.2) y).mp hy) (inv_mem hy)⟩
    have h1 : Nat.card (Additive (↥X ⧸ N)) = Y.relIndex X :=
      Nat.card_congr Additive.toMul
    have h3 : Nat.card {y : Additive (↥X ⧸ N) // ρ (θ x) y = y} = Y.relIndex C := by
      rw [← hcardImg C hCX]
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun y => ?_)
      obtain ⟨q, rfl⟩ := Additive.ofMul.surjective y
      induction q using QuotientGroup.induction_on with
      | H s =>
      simp only [Equiv.refl_apply]
      rw [hρmk, Additive.mem_toAddSubgroup]
      constructor
      · intro hs
        have h4 := Additive.ofMul.injective hs
        rw [D.mk_eq_mk_iff, coe_conjX] at h4
        exact ⟨s, Subgroup.mem_subgroupOf.mpr ((hC s).mpr ⟨s.2, h4⟩), rfl⟩
      · rintro ⟨s', hs', hss'⟩
        have hs'C := (hC _).mp (Subgroup.mem_subgroupOf.mp hs')
        have hss : (QuotientGroup.mk s' : ↥X ⧸ N) = QuotientGroup.mk s := hss'
        rw [D.mk_eq_mk_iff] at hss
        have hsC : (s : G) ∈ C := by
          have := mul_mem (inv_mem (hYC hss)) (Subgroup.mem_subgroupOf.mp hs')
          rwa [show ((s' : G) * (s : G)⁻¹)⁻¹ * s' = s * (s' : G)⁻¹ * s' by group,
            inv_mul_cancel_right] at this
        congr 1
        rw [D.mk_eq_mk_iff, coe_conjX]
        exact ((hC s).mp hsC).2
    rw [h1, h3, hidx]
  obtain ⟨f, hf, hfe⟩ := isoMod_st_of_index h65 h2 hfaith hmT' hgen' hl' hx3 hx1 hidx'
  set e := AddEquiv.ofBijective f hf with hedef
  have he : ∀ (g : Γ) (y : Additive (↥X ⧸ N)), e.symm (ρ g y) = ρSt g (e.symm y) := by
    intro g y
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    show ρ g y = f (ρSt g (e.symm y))
    rw [hfe]
    congr 1
    exact (e.apply_symm_apply y).symm
  let χ : ↥X →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    { toFun := fun s => Multiplicative.ofAdd
        ((e.symm (Additive.ofMul (QuotientGroup.mk s)) : St) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      map_one' := by
        rw [QuotientGroup.mk_one, ofMul_one, map_zero]
        rfl
      map_mul' := fun a b => by
        rw [QuotientGroup.mk_mul, ofMul_mul, map_add, AddSubgroup.coe_add, ofAdd_add] }
  have hχ : ∀ s : ↥X, χ s = Multiplicative.ofAdd
      ((e.symm (Additive.ofMul (QuotientGroup.mk s)) : St) : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    fun _ => rfl
  refine ⟨χ, ?_, fun s => ?_, fun A hA => ?_, fun l s t hst => ?_⟩
  · ext s
    rw [MonoidHom.mem_ker, hχ, Subgroup.mem_subgroupOf]
    constructor
    · intro hs
      have h4 : (e.symm (Additive.ofMul (QuotientGroup.mk s)) : St) = 0 := by
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd hs
      have h5 : (Additive.ofMul (QuotientGroup.mk s) : Additive (↥X ⧸ N)) = 0 := by
        rw [← e.apply_symm_apply (Additive.ofMul (QuotientGroup.mk s)), h4, map_zero]
      have h6 := Additive.ofMul.injective (h5.trans ofMul_one.symm)
      rw [← QuotientGroup.mk_one, D.mk_eq_mk_iff] at h6
      simpa using h6
    · intro hs
      rw [hmkY _ hs, map_zero]
      rfl
  · rw [hχ, toAdd_ofAdd]
    exact (e.symm (Additive.ofMul (QuotientGroup.mk s))).2
  · obtain ⟨q, hq⟩ := Additive.ofMul.surjective (e ⟨A, hA⟩)
    induction q using QuotientGroup.induction_on with
    | H s =>
    refine ⟨s, ?_⟩
    rw [hχ, hq, AddEquiv.symm_apply_apply]
  · have ht : t = D.conjX l s := Subtype.ext (by rw [hst, coe_conjX])
    rw [hχ, hχ, ht, ← hρmk, he, toAdd_ofAdd]
    rfl

end SecMod

end CFSG.Quasithin.H13.L32A
