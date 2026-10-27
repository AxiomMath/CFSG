module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFrames

section Induced

variable {C G : Type} [Group C] [Group G] [Finite C] (χ : C →* G) (hχ : Function.Injective χ)

include hχ in
theorem exists_inducedAut {g : G} (hg : g ∈ Subgroup.normalizer (χ.range : Set G)) :
    ∃ α : MulAut C, ∀ x, χ (α x) = g * χ x * g⁻¹ := by
  have hmem : ∀ x, ∃ y, χ y = g * χ x * g⁻¹ := fun x =>
    (Subgroup.mem_normalizer_iff.mp hg (χ x)).mp ⟨x, rfl⟩
  choose α₀ hα₀ using hmem
  have hmul : ∀ x y, α₀ (x * y) = α₀ x * α₀ y := fun x y => hχ (by
    rw [hα₀, map_mul, map_mul, hα₀, hα₀]
    group)
  have hinj : Function.Injective α₀ := fun x y hxy => hχ (by
    have h1 := hα₀ x
    rw [hxy, hα₀] at h1
    calc χ x = g⁻¹ * (g * χ x * g⁻¹) * g := by group
      _ = g⁻¹ * (g * χ y * g⁻¹) * g := by rw [h1]
      _ = χ y := by group)
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' α₀ hmul) (Finite.injective_iff_bijective.mp hinj),
    hα₀⟩

omit [Finite C] in
theorem inducedAut_pow {g : G} {α : MulAut C} (hα : ∀ x, χ (α x) = g * χ x * g⁻¹) (k : ℕ)
    (x : C) : χ ((α ^ k) x) = g ^ k * χ x * (g ^ k)⁻¹ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hα, pow_succ]
    group

include hχ in
omit [Finite C] in
theorem inducedAut_pow_eq_one {g : G} {α : MulAut C} (hα : ∀ x, χ (α x) = g * χ x * g⁻¹)
    {k : ℕ} (hg : g ^ k = 1) : α ^ k = 1 :=
  MulEquiv.ext fun x => hχ (by rw [inducedAut_pow χ hα, hg]; simp)

end Induced

section Light

variable {τ : Tag} {L : Type} [Field L] {p : ℕ} [NeZero p]

theorem frameDiag_mem_adjointGroup
    (hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L) (ζ : Lˣ) (hζ : ζ ^ p = 1)
    (s : Fin τ.rank → ZMod p) : frameDiag (τ := τ) ζ hζ s ∈ adjointGroup τ L :=
  CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (hfull _)

omit [NeZero p] in
theorem mem_torusPow_iff_coe {x : adjointGroup τ L} :
    x ∈ TableBExc.torusPow τ L p ↔ (x : ModGL τ L) ∈ splitPow τ L p := by
  rw [TableBExc.mem_torusPow]
  refine and_congr Iff.rfl ⟨fun h => by rw [← Subgroup.coe_pow, h, OneMemClass.coe_one],
    fun h => Subtype.ext (by rw [Subgroup.coe_pow, h, OneMemClass.coe_one])⟩

@[expose] noncomputable def frameHom
    (hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L) (ζ : Lˣ) (hζ : ζ ^ p = 1)
    (k : adjointGroup τ L) : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ L where
  toFun s := k⁻¹ * ⟨frameDiag ζ hζ (Multiplicative.toAdd s),
    frameDiag_mem_adjointGroup hfull ζ hζ _⟩ * k
  map_one' := by
    refine Subtype.ext ?_
    simp [frameDiag_zero]
  map_mul' x y := by
    refine Subtype.ext ?_
    simp only [toAdd_mul, Subgroup.coe_mul, Subgroup.coe_inv, frameDiag_add]
    group

theorem coe_frameHom (hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (k : adjointGroup τ L) (s : Fin τ.rank → ZMod p) :
    (frameHom hfull ζ hζ k (.ofAdd s) : ModGL τ L) = (k : ModGL τ L)⁻¹ * frameDiag ζ hζ s * k :=
  rfl


end Light

section Frame

variable {τ : Tag} {L : Type} [Field L] [Finite L] {p : ℕ} [Fact p.Prime]


omit [Finite L] [Fact p.Prime] in
theorem exists_weyl_of_normalizes {a : adjointGroup τ L}
    (ha : ∀ x : adjointGroup τ L, x ∈ TableBExc.torusPow τ L p ↔
      a * x * a⁻¹ ∈ TableBExc.torusPow τ L p) :
    ∃ w : WeylGroup τ, ∀ v ∈ splitPow τ L p, (a : ModGL τ L) * v * (a : ModGL τ L)⁻¹ =
      canonicalRep (coxeterSystem τ) L w * v * (canonicalRep (coxeterSystem τ) L w)⁻¹ := by
  refine CFSG.RankThree.PartOne.K133H.exists_conj_eq_canonicalRep_of_mem_normalizer
    (fun v hv => hv.1) (Subgroup.mem_inf.mpr ⟨a.2, Subgroup.mem_set_normalizer_iff.mpr ?_⟩)
  intro h
  constructor
  · intro hh
    have hC : h ∈ adjointGroup τ L := CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hh.1
    have h1 := (ha ⟨h, hC⟩).mp (mem_torusPow_iff_coe.mpr hh)
    exact mem_torusPow_iff_coe.mp h1
  · intro hh
    have hC' : (a : ModGL τ L) * h * (a : ModGL τ L)⁻¹ ∈ adjointGroup τ L :=
      CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup hh.1
    have hC : h ∈ adjointGroup τ L := by
      have := mul_mem (mul_mem (inv_mem a.2) hC') a.2
      simpa [mul_assoc] using this
    have h1 : a * ⟨h, hC⟩ * a⁻¹ ∈ TableBExc.torusPow τ L p := mem_torusPow_iff_coe.mpr hh
    exact mem_torusPow_iff_coe.mp ((ha ⟨h, hC⟩).mpr h1)

theorem exists_weylFrame {G : Type} [Group G]
    (hfull : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Lˣ} (hζo : orderOf ζ = p)
    (χ : adjointGroup τ L →* G) (hχ : Function.Injective χ) (k : adjointGroup τ L)
    {Bs : Subgroup G}
    (hBs : ∀ b, b ∈ Bs ↔ ∃ v ∈ TableBExc.torusPow τ L p, b = χ (k⁻¹ * v * k))
    (hfix : ∀ α : MulAut (adjointGroup τ L), α ^ p = 1 → ∃ a : adjointGroup τ L,
      ∀ v ∈ TableBExc.torusPow τ L p, α v = a * v * a⁻¹) :
    ∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  classical
  have : Finite (adjointGroup τ L) := generated_group_finite τ L
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  set V := TableBExc.torusPow τ L p with hV
  set t : (Fin τ.rank → ZMod p) → adjointGroup τ L := fun s =>
    ⟨frameDiag ζ hζ s, frameDiag_mem_adjointGroup hfull ζ hζ s⟩ with ht
  have htV : ∀ s, t s ∈ V := fun s => mem_torusPow_iff_coe.mpr (frameDiag_mem hfull ζ hζ s)
  refine ⟨χ.comp (frameHom hfull ζ hζ k), ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : k⁻¹ * t (Multiplicative.toAdd x) * k = k⁻¹ * t (Multiplicative.toAdd y) * k :=
      hχ hxy
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact Multiplicative.toAdd.injective
      (frameDiag_injective hζo hζ hdet (congrArg Subtype.val h2))
  · ext b
    rw [hBs]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨t (Multiplicative.toAdd s), htV _, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨s, hs⟩ := exists_frameDiag_of_mem hζo hζ hdet (mem_torusPow_iff_coe.mp hv)
      refine ⟨.ofAdd s, ?_⟩
      have htv : t s = v := Subtype.ext hs
      show χ (k⁻¹ * t s * k) = χ (k⁻¹ * v * k)
      rw [htv]
  · intro g hgN hgB hgp
    obtain ⟨α, hα⟩ := exists_inducedAut χ hχ hgN
    have hαp : α ^ p = 1 := inducedAut_pow_eq_one χ hχ hα hgp
    set α' : MulAut (adjointGroup τ L) := MulAut.conj k * α * MulAut.conj k⁻¹ with hα'
    have hα'apply : ∀ x, α' x = k * α (k⁻¹ * x * k) * k⁻¹ := fun x => by
      rw [hα', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, inv_inv]
    have hα'p : α' ^ p = 1 := by
      rw [hα', map_inv, conj_pow, hαp, mul_one, mul_inv_cancel]
    obtain ⟨a, ha⟩ := hfix α' hα'p
    have hα'V : ∀ v ∈ V, α' v ∈ V := by
      intro v hv
      have h1 : χ (k⁻¹ * v * k) ∈ Bs := (hBs _).mpr ⟨v, hv, rfl⟩
      have h2 : g * χ (k⁻¹ * v * k) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB _).mp h1
      rw [← hα] at h2
      obtain ⟨v', hv', hv'eq⟩ := (hBs _).mp h2
      have h3 : α (k⁻¹ * v * k) = k⁻¹ * v' * k := hχ hv'eq
      have h4 : k * (k⁻¹ * v' * k) * k⁻¹ = v' := by group
      rw [hα'apply, h3, h4]
      exact hv'
    have hiter : ∀ j : ℕ, ∀ v ∈ V, (α' ^ j) v ∈ V := by
      intro j
      induction j with
      | zero => intro v hv; simpa using hv
      | succ j ih => intro v hv; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hα'V v hv)
    have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have hnorm : ∀ x : adjointGroup τ L, x ∈ V ↔ a * x * a⁻¹ ∈ V := by
      intro x
      constructor
      · intro hx
        rw [← ha x hx]
        exact hα'V x hx
      · intro hx
        set y := (α' ^ (p - 1)) (a * x * a⁻¹) with hy
        have hyV : y ∈ V := hiter _ _ hx
        have h1 : α' y = a * x * a⁻¹ := by
          rw [hy, ← MulAut.mul_apply, mul_pow_sub_one hp0, hα'p, MulAut.one_apply]
        rw [ha y hyV] at h1
        have h2 : y = x := mul_left_cancel (mul_right_cancel h1)
        rw [← h2]
        exact hyV
    obtain ⟨w, hw⟩ := exists_weyl_of_normalizes hnorm
    refine ⟨w, fun s => ?_⟩
    have h1 : α' (t s) = t (TableBExc.torusAct τ p w s) := by
      rw [ha _ (htV s)]
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show (a : ModGL τ L) * frameDiag ζ hζ s * (a : ModGL τ L)⁻¹ =
        frameDiag ζ hζ (TableBExc.torusAct τ p w s)
      rw [hw _ (frameDiag_mem hfull ζ hζ s), canonicalRep_conj_frameDiag]
    have h2 : α (k⁻¹ * t s * k) = k⁻¹ * α' (t s) * k := by
      rw [hα'apply]
      group
    show g * χ (k⁻¹ * t s * k) * g⁻¹ = χ (k⁻¹ * t (TableBExc.torusAct τ p w s) * k)
    rw [← hα, h2, h1]

end Frame

end ExcFrames

end CFSG.StandardType
