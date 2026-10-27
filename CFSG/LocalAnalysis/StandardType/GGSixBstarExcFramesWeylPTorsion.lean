module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFrames

section Light

variable {τ : Tag} {L : Type} [Field L] {p : ℕ} [NeZero p]

theorem frameDiag_mem_torusGroup_of_fullp
    (hfullp : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ L)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    frameDiag (τ := τ) ζ hζ s ∈ torusGroup τ L :=
  hfullp _ fun i => by
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem frameDiag_mem_of_fullp
    (hfullp : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ L)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    frameDiag (τ := τ) ζ hζ s ∈ splitPow τ L p :=
  ⟨frameDiag_mem_torusGroup_of_fullp hfullp ζ hζ s, frameDiag_pow ζ hζ s⟩

theorem frameDiag_mem_adjointGroup_of_fullp
    (hfullp : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ L)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    frameDiag (τ := τ) ζ hζ s ∈ adjointGroup τ L :=
  CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
    (frameDiag_mem_torusGroup_of_fullp hfullp ζ hζ s)

@[expose] noncomputable def frameHomP
    (hfullp : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ L)
    (ζ : Lˣ) (hζ : ζ ^ p = 1) (k : adjointGroup τ L) :
    Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ L where
  toFun s := k⁻¹ * ⟨frameDiag ζ hζ (Multiplicative.toAdd s),
    frameDiag_mem_adjointGroup_of_fullp hfullp ζ hζ _⟩ * k
  map_one' := by
    refine Subtype.ext ?_
    simp [frameDiag_zero]
  map_mul' x y := by
    refine Subtype.ext ?_
    simp only [toAdd_mul, Subgroup.coe_mul, Subgroup.coe_inv, frameDiag_add]
    group

end Light

section Frame

variable {τ : Tag} {L : Type} [Field L] [Finite L] {p : ℕ} [Fact p.Prime]


theorem exists_weylFrame_of_fullp {G : Type} [Group G]
    (hfullp : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ L)
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
    ⟨frameDiag ζ hζ s, frameDiag_mem_adjointGroup_of_fullp hfullp ζ hζ s⟩ with ht
  have htV : ∀ s, t s ∈ V := fun s =>
    mem_torusPow_iff_coe.mpr (frameDiag_mem_of_fullp hfullp ζ hζ s)
  refine ⟨χ.comp (frameHomP hfullp ζ hζ k), ?_, ?_, ?_⟩
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
      rw [hw _ (frameDiag_mem_of_fullp hfullp ζ hζ s), canonicalRep_conj_frameDiag]
    have h2 : α (k⁻¹ * t s * k) = k⁻¹ * α' (t s) * k := by
      rw [hα'apply]
      group
    show g * χ (k⁻¹ * t s * k) * g⁻¹ = χ (k⁻¹ * t (TableBExc.torusAct τ p w s) * k)
    rw [← hα, h2, h1]

theorem exists_weylFrame_of_toral_fullp {K : Type} [Field K] [Finite K]
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) (hpq : p ∣ Nat.card K - 1)
    (hfullp : ∀ a : Fin τ.rank → Kˣ, (∀ i, a i ^ p = 1) → rootDiagUnit τ a ∈ torusGroup τ K)
    (hfix : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 → ∃ a : adjointGroup τ K,
      ∀ v ∈ TableBExc.torusPow τ K p, α v = a * v * a⁻¹)
    {G : Type} [Group G] (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ)
    {Bs : Subgroup G} (hBsR : Bs ≤ χ.range)
    (hT : ∃ c : adjointGroup τ K,
      (Bs.comap χ).map (MulAut.conj c).toMonoidHom = TableBExc.torusPow τ K p) :
    ∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  obtain ⟨c, hc⟩ := hT
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  refine exists_weylFrame_of_fullp hfullp hdet hζo χ hχ c (fun b => ?_) hfix
  constructor
  · intro hb
    obtain ⟨e, rfl⟩ := hBsR hb
    refine ⟨c * e * c⁻¹, ?_, by rw [show c⁻¹ * (c * e * c⁻¹) * c = e by group]⟩
    rw [← hc]
    exact ⟨e, hb, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    rw [← hc] at hv
    obtain ⟨e, he, rfl⟩ := hv
    have h1 : c⁻¹ * (MulAut.conj c).toMonoidHom e * c = e := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h1]
    exact he

end Frame

end ExcFrames

end CFSG.StandardType
