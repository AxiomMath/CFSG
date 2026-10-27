module

public import CFSG.RankThree.GF2n.Smith81.Orth213ClassDefs
public import CFSG.RankThree.GF2n.Smith81.Orth28Route

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def imgSet (C : OrthCtx M Q Z B) (S : Subgroup G) :
    Set ((C.ι → C.K) × (C.ι → C.K)) :=
  {p | ∃ y ∈ S, C.φ (C.M₀.π y) = p}

theorem card_root_outside (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) {S : Subgroup G} (hSQ : S ≤ Q) (hZS : Z ≤ S) :
    Nat.card {y : G // y ∈ S ∧ y ∉ Z ∧ IsConj z y} =
      Nat.card Z * tCount C.qU (imgSet C S) := by
  have H := hc.ctx.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hsurj : ∀ p : {p : (C.ι → C.K) × (C.ι → C.K) // p ∈ imgSet C S ∧ PairTypeA C.qU p},
      ∃ y, y ∈ S ∧ C.φ (C.M₀.π y) = p.1 := fun p => p.2.1
  choose σ hσS hσφ using hsurj
  have hZ0 : ∀ y ∈ Q, C.M₀.π y = 0 ↔ y ∈ Z := fun y hy => C.M₀.π_ker y hy
  have hp0 : ∀ p : (C.ι → C.K) × (C.ι → C.K), PairTypeA C.qU p → p ≠ 0 := fun p hp h0 => by
    obtain ⟨c₁, c₂, u, hc12, hu, -, rfl⟩ := hp
    rw [Prod.mk_eq_zero] at h0
    rcases hc12 with h | h
    · exact hu ((smul_eq_zero.mp h0.1).resolve_left h)
    · exact hu ((smul_eq_zero.mp h0.2).resolve_left h)
  have hnotZ : ∀ y ∈ Q, PairTypeA C.qU (C.φ (C.M₀.π y)) → y ∉ Z := fun y hy hp hyZ => by
    apply hp0 _ hp
    rw [(hZ0 y hy).mpr hyZ, map_zero]
  let F : ({p : (C.ι → C.K) × (C.ι → C.K) // p ∈ imgSet C S ∧ PairTypeA C.qU p} × Z) →
      {y : G // y ∈ S ∧ y ∉ Z ∧ IsConj z y} := fun pz =>
    ⟨σ pz.1 * (pz.2 : G), S.mul_mem (hσS pz.1) (hZS pz.2.2), by
      have hπ : C.φ (C.M₀.π (σ pz.1 * (pz.2 : G))) = pz.1.1 := by
        rw [C.M₀.π_mul _ (hSQ (hσS pz.1)) _ (hZQ pz.2.2), (hZ0 _ (hZQ pz.2.2)).mpr pz.2.2,
          add_zero, hσφ pz.1]
      have hQ : σ pz.1 * (pz.2 : G) ∈ Q := Q.mul_mem (hSQ (hσS pz.1)) (hZQ pz.2.2)
      refine ⟨hnotZ _ hQ (hπ ▸ pz.1.2.2), ?_⟩
      exact (C.hF.root z hz hz1 _ hQ (hnotZ _ hQ (hπ ▸ pz.1.2.2))).mpr (hπ ▸ pz.1.2.2)⟩
  have hFinj : Function.Injective F := by
    rintro ⟨p, z₁⟩ ⟨p', z₂⟩ h
    have h1 : σ p * (z₁ : G) = σ p' * (z₂ : G) := congrArg Subtype.val h
    have hπ : ∀ (r : _) (z' : Z), C.φ (C.M₀.π (σ r * (z' : G))) = r.1 := fun r z' => by
      rw [C.M₀.π_mul _ (hSQ (hσS r)) _ (hZQ z'.2), (hZ0 _ (hZQ z'.2)).mpr z'.2, add_zero,
        hσφ r]
    have hpp : p = p' := Subtype.ext (by rw [← hπ p z₁, h1, hπ p' z₂])
    subst hpp
    have : (z₁ : G) = (z₂ : G) := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have hFsurj : Function.Surjective F := by
    rintro ⟨y, hyS, hyZ, hyc⟩
    have hyQ : y ∈ Q := hSQ hyS
    have hpure : PairTypeA C.qU (C.φ (C.M₀.π y)) := (C.hF.root z hz hz1 y hyQ hyZ).mp hyc
    let p : {p : (C.ι → C.K) × (C.ι → C.K) // p ∈ imgSet C S ∧ PairTypeA C.qU p} :=
      ⟨C.φ (C.M₀.π y), ⟨y, hyS, rfl⟩, hpure⟩
    have hπeq : C.M₀.π (σ p) = C.M₀.π y := C.φ.injective (hσφ p)
    have hσy : (σ p)⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff C.M₀ (hSQ (hσS p)) hyQ).mp hπeq
    refine ⟨(p, ⟨(σ p)⁻¹ * y, hσy⟩), Subtype.ext ?_⟩
    show σ p * ((σ p)⁻¹ * y) = y
    group
  have hbij : Function.Bijective F := ⟨hFinj, hFsurj⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hbij), Nat.card_prod, mul_comm]
  rfl

theorem card_root_add_one (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) {S : Subgroup G} (hSQ : S ≤ Q) (hZS : Z ≤ S) :
    Nat.card {y : G // y ∈ S ∧ (y = 1 ∨ IsConj z y)} =
      Nat.card Z * (tCount C.qU (imgSet C S) + 1) := by
  classical
  have H := hc.ctx.hyp
  have hout := card_root_outside hc C hz hz1 hSQ hZS
  let R := {y : G // y ∈ S ∧ (y = 1 ∨ IsConj z y)}
  have hZconj : ∀ y ∈ Z, y ≠ 1 → IsConj z y := fun y hy hy1 => by
    obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hy hy1
    exact isConj_iff.mpr ⟨m, hm⟩
  have e1 : {y : R // (y : G) ∈ Z} ≃ Z :=
    { toFun := fun y => ⟨y.1.1, y.2⟩
      invFun := fun y => ⟨⟨y.1, hZS y.2, by
        by_cases h1 : (y : G) = 1
        · exact Or.inl h1
        · exact Or.inr (hZconj _ y.2 h1)⟩, y.2⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }
  have e2 : {y : R // (y : G) ∉ Z} ≃ {y : G // y ∈ S ∧ y ∉ Z ∧ IsConj z y} :=
    { toFun := fun y => ⟨y.1.1, y.1.2.1, y.2, by
        rcases y.1.2.2 with h | h
        · exact (y.2 (by rw [h]; exact Z.one_mem)).elim
        · exact h⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, Or.inr y.2.2.2⟩, y.2.2.1⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }
  have e3 := (Equiv.sumCompl (fun y : R => (y : G) ∈ Z)).symm
  rw [Nat.card_congr e3, Nat.card_sum, Nat.card_congr e1, Nat.card_congr e2, hout]
  ring

theorem tCount_eq_of_conj (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) {S S₁ : Subgroup G} (hSQ : S ≤ Q) (hZS : Z ≤ S) (hS₁Q : S₁ ≤ Q)
    (hZS₁ : Z ≤ S₁) {g : G} (hg : ∀ y, y ∈ S₁ ↔ g * y * g⁻¹ ∈ S) :
    tCount C.qU (imgSet C S) = tCount C.qU (imgSet C S₁) := by
  have h1 := card_root_add_one hc C hz hz1 hSQ hZS
  have h2 := card_root_add_one hc C hz hz1 hS₁Q hZS₁
  have e : {y : G // y ∈ S₁ ∧ (y = 1 ∨ IsConj z y)} ≃ {y : G // y ∈ S ∧ (y = 1 ∨ IsConj z y)} :=
    { toFun := fun y => ⟨g * y.1 * g⁻¹, (hg _).mp y.2.1, by
        rcases y.2.2 with h | h
        · exact Or.inl (by rw [h]; group)
        · exact Or.inr (h.trans (isConj_iff.mpr ⟨g, by group⟩))⟩
      invFun := fun y => ⟨g⁻¹ * y.1 * g, (hg _).mpr (by
          have : g * (g⁻¹ * y.1 * g) * g⁻¹ = y.1 := by group
          rw [this]; exact y.2.1), by
        rcases y.2.2 with h | h
        · exact Or.inl (by rw [h]; group)
        · exact Or.inr (h.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩))⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }
  rw [← Nat.card_congr e, h2] at h1
  have := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  omega

end CFSG.RankThree.GF2n.Smith81.OrthClass
