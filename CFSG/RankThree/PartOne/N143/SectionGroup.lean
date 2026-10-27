module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G Q : Type} [Group G] [Group Q] (f : G →* Q)

theorem disjoint_ker_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsPGroup p E) (hk : ¬ p ∣ Nat.card f.ker) : Disjoint E f.ker := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hn]
  exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)

theorem injective_subgroupMap_of_disjoint {E : Subgroup G} (h : Disjoint E f.ker) :
    Function.Injective (f.subgroupMap E) := by
  intro x y hxy
  have hfxy : f (x : G) = f (y : G) := congrArg Subtype.val hxy
  have hmem : ((x : G)⁻¹ * (y : G)) ∈ E ⊓ f.ker :=
    Subgroup.mem_inf.2 ⟨E.mul_mem (E.inv_mem x.2) y.2,
      MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hfxy, inv_mul_cancel])⟩
  have h1 : (x : G)⁻¹ * (y : G) = 1 :=
    Subgroup.disjoint_def.1 h (Subgroup.mem_inf.1 hmem).1 (Subgroup.mem_inf.1 hmem).2
  exact Subtype.ext (inv_mul_eq_one.1 h1)

@[expose] noncomputable def mapEquiv {E : Subgroup G} (h : Disjoint E f.ker) : E ≃* E.map f :=
  MulEquiv.ofBijective (f.subgroupMap E)
    ⟨injective_subgroupMap_of_disjoint f h, f.subgroupMap_surjective E⟩

theorem mapEquiv_apply_coe {E : Subgroup G} (h : Disjoint E f.ker) (e : E) :
    ((mapEquiv f h e : E.map f) : Q) = f (e : G) := rfl

theorem card_map_of_disjoint_ker {E : Subgroup G} (h : Disjoint E f.ker) :
    Nat.card (E.map f) = Nat.card E :=
  (Nat.card_congr (mapEquiv f h).toEquiv).symm

theorem isPGroup_map_subgroup {p : ℕ} {S : Subgroup G} (h : IsPGroup p S) :
    IsPGroup p (S.map f) := by
  rintro ⟨_, y, hy, rfl⟩
  obtain ⟨k, hk⟩ := h ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun z : S => f (z : G)) hk
  simpa using this

theorem map_le_normalizer_map {E S : Subgroup G} (h : E ≤ Subgroup.normalizer (S : Set G)) :
    E.map f ≤ Subgroup.normalizer ((S.map f : Subgroup Q) : Set Q) :=
  (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map f)

theorem section_data [Finite G] {p : ℕ} (hp : p.Prime) (hk : ¬ p ∣ Nat.card f.ker)
    {E S : Subgroup G} (hE : IsElementaryAbelian p E) (hS2 : IsPGroup 2 S)
    (hN : E ≤ Subgroup.normalizer (S : Set G)) (hC : ⁅S, E⁆ = S) (hSk : ¬ S ≤ f.ker) :
    IsElementaryAbelian p (E.map f) ∧ Nat.card (E.map f) = Nat.card E ∧
      IsPGroup 2 (S.map f) ∧ S.map f ≠ ⊥ ∧
      E.map f ≤ Subgroup.normalizer ((S.map f : Subgroup Q) : Set Q) ∧
      ⁅S.map f, E.map f⁆ = S.map f := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := by
    have := hE
    exact IsElementaryAbelian.isPGroup p E
  have hdis := disjoint_ker_of_isPGroup f hp hEp hk
  refine ⟨?_, card_map_of_disjoint_ker f hdis, isPGroup_map_subgroup f hS2, ?_,
    map_le_normalizer_map f hN, ?_⟩
  · have := hE
    exact IsElementaryAbelian.map f
  · intro hbot
    exact hSk ((Subgroup.map_eq_bot_iff S).1 hbot)
  · rw [← Subgroup.map_commutator, hC]

theorem torusWeyl_card_dvd [Finite G] {E : Subgroup G} (h : Disjoint E f.ker) :
    Nat.card (torusWeyl E) ∣ Nat.card (torusWeyl (E.map f)) := by
  let ψ := mapEquiv f h
  let ρ : MulAut E ≃* MulAut (E.map f) := MulAut.congr ψ
  have hle : (torusWeyl E).map ρ.toMonoidHom ≤ torusWeyl (E.map f) := by
    intro y hy
    obtain ⟨φ, hφ, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hφ
    refine ⟨⟨f n, Subgroup.le_normalizer_map f ⟨n, n.2, rfl⟩⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    obtain ⟨e, rfl⟩ := ψ.surjective x
    have h1 : (ρ.toMonoidHom (E.normalizerMonoidHom n)) (ψ e) =
        ψ ((E.normalizerMonoidHom n) e) := by
      change MulAut.congr ψ _ _ = _
      rw [MulAut.congr_apply]
      simp
    rw [h1]
    apply Subtype.ext
    change f (n : G) * f (e : G) * (f (n : G))⁻¹ = f ((n : G) * (e : G) * (n : G)⁻¹)
    simp
  have h1 : Nat.card ((torusWeyl E).map ρ.toMonoidHom) = Nat.card (torusWeyl E) :=
    Subgroup.card_map_of_injective ρ.injective
  rw [← h1]
  exact Subgroup.card_dvd_of_le hle

theorem torusWeyl_factorization_le [Finite G] {E : Subgroup G} (h : Disjoint E f.ker) (q : ℕ) :
    (Nat.card (torusWeyl E)).factorization q ≤
      (Nat.card (torusWeyl (E.map f))).factorization q := by
  have : Finite (E.map f) := Finite.of_equiv E (mapEquiv f h).toEquiv
  have h1 : Nat.card (torusWeyl E) ≠ 0 := Nat.card_pos.ne'
  have h2 : Nat.card (torusWeyl (E.map f)) ≠ 0 := Nat.card_pos.ne'
  exact (Nat.factorization_le_iff_dvd h1 h2).2 (torusWeyl_card_dvd f h) q

end CFSG.RankThree.PartOne.N143
