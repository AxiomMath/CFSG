module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

section Inflate

variable {G : Type*} [Group G] {N : Type*} [Group N]

theorem mem_map_inl_iff (D : Subgroup G) (x : G × N) :
    x ∈ D.map (MonoidHom.inl G N) ↔ x.1 ∈ D ∧ x.2 = 1 := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨hd, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x.1, h1, Prod.ext rfl h2.symm⟩

theorem prod_mem_normalizer_map_inl {D : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer D)
    (c : N) :
    (g, c) ∈ Subgroup.normalizer
      ((D.map (MonoidHom.inl G N) : Subgroup (G × N)) : Set (G × N)) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [mem_map_inl_iff, mem_map_inl_iff]
  have h1 : ((g, c) * x * (g, c)⁻¹).1 = g * x.1 * g⁻¹ := rfl
  have h2 : ((g, c) * x * (g, c)⁻¹).2 = c * x.2 * c⁻¹ := rfl
  rw [h1, h2, ← hg x.1]
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨hx1, by rw [hx2]; group⟩
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    have : x.2 = c⁻¹ * (c * x.2 * c⁻¹) * c := by group
    rw [this, hx2]
    group

theorem map_inf_centralizer_singleton {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) (D : Subgroup G) (s : G) :
    D.map f ⊓ Subgroup.centralizer ({f s} : Set G') =
      (D ⊓ Subgroup.centralizer ({s} : Set G)).map f := by
  ext y
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, hy⟩
    refine ⟨d, ⟨hd, Subgroup.mem_centralizer_singleton_iff.2 (hf ?_)⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hy
  · rintro ⟨d, ⟨hd, hdc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hd, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hdc]

end Inflate

theorem isElementaryAbelian_prod_top {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {C : Type*}
    [CommGroup C] {A : Subgroup G} (hA : Nat.card A = p) (hC : Nat.card C = p) :
    IsElementaryAbelian p ↥(A.prod (⊤ : Subgroup C)) ∧
      Nat.card ↥(A.prod (⊤ : Subgroup C)) = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hcomm : IsMulCommutative A := inferInstance
  refine ⟨?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact congrArg Subtype.val (hcomm.is_comm.comm
          (⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩ : A) ⟨y.1.1, (Subgroup.mem_prod.1 y.2).1⟩)
      · exact mul_comm _ _
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · have h : (⟨x.1.1, (Subgroup.mem_prod.1 x.2).1⟩ : A) ^ Nat.card A = 1 :=
          pow_card_eq_one'
        rw [hA] at h
        exact congrArg Subtype.val h
      · have h : x.1.2 ^ Nat.card C = 1 := pow_card_eq_one'
        rw [hC] at h
        exact h
  · rw [Nat.card_congr (Subgroup.prodEquiv A ⊤).toEquiv, Nat.card_prod, hA, Subgroup.card_top, hC]
    ring

theorem fixedRankTwo_of_order_five (hET32 : ExtraspecialThirtyTwoFixedRankTwoAction)
    {G : Type} [Group G] [Finite G] {q : ℕ} {A R D : Subgroup G} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq5 : q ≠ 5) (hA : Nat.card A = 5) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hR : IsExtraspecialPGroup 2 R) (hR32 : Nat.card R = 32)
    (ha : ∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R →
      ⁅a, r⁆ ∉ inSubgroup Subgroup.center R)
    (hD : R ⊔ A ≤ Subgroup.normalizer (D : Set G)) (hDq : IsPGroup q D)
    (hDe : ∀ x ∈ D, x ^ q = 1) (hDc : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    ⁅D, R⁆ = D ∧ (inSubgroup frattini D).relIndex D = q ^ 4 ∧ IsQDShape q D := by
  set C : Type := Multiplicative (ZMod 5) with hCdef
  have hC : Nat.card C = 5 := by
    rw [hCdef, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  set ι : G →* G × C := MonoidHom.inl G C with hι
  have hιinj : Function.Injective ι := fun a b h => (Prod.ext_iff.1 h).1
  set A' : Subgroup (G × C) := A.prod ⊤ with hA'
  obtain ⟨hA'el, hA'card⟩ := isElementaryAbelian_prod_top (by norm_num : Nat.Prime 5) hA hC
  have hA'card' : Nat.card A' = 25 := by rw [hA'card]; norm_num
  have hιA : ∀ a ∈ A, ι a ∈ A' := fun a ha => Subgroup.mem_prod.2 ⟨ha, Subgroup.mem_top _⟩
  obtain ⟨a, haA, hafp⟩ := ha
  have hres := hET32 (G × C) q A' (R.map ι) (D.map ι) hq hq2 hq5 hA'el hA'card'
    (fun x hx => by
      obtain ⟨a, c⟩ := x
      exact prod_mem_normalizer_map_inl (hAR (Subgroup.mem_prod.1 hx).1) c)
    (isExtraspecialPGroup_of_mulEquiv (R.equivMapOfInjective ι hιinj) hR)
    (by rw [Subgroup.card_map_of_injective hιinj, hR32])
    ⟨ι a, hιA a haA, by
      rw [inSubgroup_center_map ι hιinj R]
      rintro _ ⟨r, hr, rfl⟩ hrZ hmem
      refine hafp r hr (fun h => hrZ (Subgroup.mem_map_of_mem ι h)) ?_
      rw [← map_commutatorElement] at hmem
      exact (Subgroup.mem_map_iff_mem hιinj).1 hmem⟩
    (sup_le
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact prod_mem_normalizer_map_inl (hD (Subgroup.mem_sup_left hr)) 1)
      (by
        rintro ⟨a, c⟩ ha
        exact prod_mem_normalizer_map_inl (hD (Subgroup.mem_sup_right
          (Subgroup.mem_prod.1 ha).1)) c))
    (hDq.map ι)
    (by
      rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, hDe d hd, map_one])
    (by rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hDc, Subgroup.map_bot])
    (by
      rw [eq_bot_iff]
      rintro _ ⟨⟨r, hr, rfl⟩, hx⟩
      have hr1 : r ∈ R ⊓ Subgroup.centralizer (D : Set G) :=
        ⟨hr, Subgroup.mem_centralizer_iff.2 fun d hd => hιinj (by
          rw [map_mul, map_mul]
          exact Subgroup.mem_centralizer_iff.1 hx (ι d) (Subgroup.mem_map_of_mem ι hd))⟩
      rw [hRD, Subgroup.mem_bot] at hr1
      rw [hr1, map_one]
      exact Subgroup.one_mem _)
    (by
      rintro _ ⟨s, hs, rfl⟩ hs1
      rw [map_inf_centralizer_singleton ι hιinj, OddCore37.pRank_map_eq ι hιinj hq]
      exact hrank s hs (fun h => hs1 (by rw [h, map_one])))
  obtain ⟨h1, h2, h3⟩ := hres
  refine ⟨?_, ?_, ?_⟩
  · apply Subgroup.map_injective hιinj
    rw [Subgroup.map_commutator]
    exact h1
  · rw [OddCore37.inSubgroup_frattini_map ι hιinj D] at h2
    rwa [Subgroup.relIndex_map_map_of_injective _ _ hιinj] at h2
  · exact (OddCore37.isQDShape_map_iff ι hιinj q D).1 h3

end CFSG.RankThree.PartOne.Torsion37
