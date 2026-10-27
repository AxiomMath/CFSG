module

public import CFSG.RankThree.PartOne.NF7J.LRoots2
public import CFSG.RankThree.PartOne.NF7J.Sp4Anti

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.SP4C
  CFSG.RankThree.PartOne.HESS
open scoped commutatorElement

section Moved

variable {G : Type} [Group G]

theorem refl_inv_of_mem_moved {E : Subgroup G} {t : MulAut E} (ht : t * t = 1)
    (hc : ∀ x y : E, x * y = y * x) {y : E} (hy : y ∈ autMoved E t) : t y = y⁻¹ := by
  have hinv : ∀ e : E, t (t e) = e := fun e => by
    have := congrArg (fun φ : MulAut E => φ e) ht
    simpa using this
  unfold autMoved at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    rw [map_mul, hinv, map_inv, _root_.mul_inv_rev, inv_inv, hc]
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul, ha, hb, _root_.mul_inv_rev, hc]
  | inv a _ ha =>
    rw [map_inv, ha]

theorem refl_inv_of_mem_movedInG {E : Subgroup G} {t : MulAut E} (ht : t * t = 1)
    (hc : ∀ x y : E, x * y = y * x) {x : G} (hx : x ∈ autMovedInG E t) (hxE : x ∈ E) :
    ((t ⟨x, hxE⟩ : E) : G) = x⁻¹ := by
  obtain ⟨y, hy, hyx⟩ := hx
  have h1 : y = ⟨x, hxE⟩ := Subtype.ext hyx
  rw [h1] at hy
  have := refl_inv_of_mem_moved ht hc hy
  rw [this]
  rfl

variable [Finite G]

omit [Finite G] in
theorem card_moved {p : ℕ} {E : Subgroup G} {t : MulAut E} (ht : IsAutReflection p E t) :
    Nat.card (autMovedInG E t) = p := by
  unfold autMovedInG
  rw [Subgroup.card_map_of_injective E.subtype_injective]
  exact ht.2

end Moved

namespace RFrame

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K)

theorem lam_mem_torus7_of_mem_E {x : ↥L} (hx : (x : G) ∈ E) : F.lam x ∈ torus7 p K := by
  have h1 : x ∈ (E ⊓ L).subgroupOf L := ⟨hx, x.2⟩
  have h2 : F.ε x ∈ (torus7 p K).map (spQ K) := by
    rw [← F.tor]
    exact ⟨x, h1, rfl⟩
  exact (F.ε_mem_map_iff _ x).1 h2

theorem card_inf_kZero_r₀ (hp : p.Prime) :
    Nat.card ↥(E ⊓ kZero p E F.r₀) = p := by
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨F.ζ, F.hζ⟩
  have heq : E ⊓ kZero p E F.r₀ = (torus7 p K ⊓ (spBlock (K := K)).range).map F.rgHom := by
    ext g
    constructor
    · rintro ⟨hgE, hgK⟩
      have hgL : g ∈ L := F.le₀ hgK
      set x : ↥L := ⟨g, hgL⟩ with hx
      rw [F.kZero_r₀_eq] at hgK
      obtain ⟨t, ht, hte⟩ := hgK
      have htl : t = F.lam x := F.rgHom_injective (by rw [hte, F.rgHom_lam])
      refine ⟨t, ⟨?_, ht⟩, hte⟩
      rw [htl]
      exact F.lam_mem_torus7_of_mem_E hgE
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨F.rgHom_mem_E ht1, ?_⟩
      rw [F.kZero_r₀_eq]
      exact ⟨t, ht2, rfl⟩
  rw [heq, Subgroup.card_map_of_injective F.rgHom_injective]
  exact card_torus7_inf_range hp.pos hζex

theorem card_inf_kZero_r₁ (hp : p.Prime) :
    Nat.card ↥(E ⊓ kZero p E F.r₁) = p := by
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨F.ζ, F.hζ⟩
  have heq : E ⊓ kZero p E F.r₁ = (torus7 p K ⊓ (spBlock' (K := K)).range).map F.rgHom := by
    ext g
    constructor
    · rintro ⟨hgE, hgK⟩
      have hgL : g ∈ L := F.le₁ hgK
      set x : ↥L := ⟨g, hgL⟩ with hx
      rw [F.kZero_r₁_eq] at hgK
      obtain ⟨t, ht, hte⟩ := hgK
      have htl : t = F.lam x := F.rgHom_injective (by rw [hte, F.rgHom_lam])
      refine ⟨t, ⟨?_, ht⟩, hte⟩
      rw [htl]
      exact F.lam_mem_torus7_of_mem_E hgE
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨F.rgHom_mem_E ht1, ?_⟩
      rw [F.kZero_r₁_eq]
      exact ⟨t, ht2, rfl⟩
  rw [heq, Subgroup.card_map_of_injective F.rgHom_injective]
  exact card_torus7_inf_range' hp.pos hζex

theorem b₀_mem_moved (hp : p.Prime) : F.b₀ ∈ autMovedInG E F.r₀ := by
  have hle : autMovedInG E F.r₀ ≤ E ⊓ kZero p E F.r₀ :=
    le_inf (Subgroup.map_subtype_le _) F.kfat₀.2.2.2.1
  have heq : autMovedInG E F.r₀ = E ⊓ kZero p E F.r₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_moved F.r₀_ref.1, F.card_inf_kZero_r₀ hp]
  rw [heq]
  exact ⟨F.phi₀_hmat_mem_E, F.phi₀_range ▸ ⟨_, rfl⟩⟩

theorem b₁_mem_moved (hp : p.Prime) : F.b₁ ∈ autMovedInG E F.r₁ := by
  have hle : autMovedInG E F.r₁ ≤ E ⊓ kZero p E F.r₁ :=
    le_inf (Subgroup.map_subtype_le _) F.kfat₁.2.2.2.1
  have heq : autMovedInG E F.r₁ = E ⊓ kZero p E F.r₁ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_moved F.r₁_ref.1, F.card_inf_kZero_r₁ hp]
  rw [heq]
  exact ⟨F.phi₁_hmat_mem_E, F.phi₁_range ▸ ⟨_, rfl⟩⟩

theorem conjBy_rgHom {t : ↥(spRev K)} {j j' : Fin 8}
    (h : (octSub K j).map (MulAut.conj t).toMonoidHom = octSub K j') :
    conjBy (F.rgHom t) (F.rg j) = F.rg j' := by
  unfold conjBy rg
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem conj_rg_r₀ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) {k : G}
    (hk : k ∈ Subgroup.normalizer (E : Set G)) (hkK : k ∈ kZero p E F.r₀)
    (hkr : conjAut E k hk = F.r₀) (j : Fin 8) : conjBy k (F.rg j) = F.rg (wperm 1 j) := by
  obtain ⟨X, hX⟩ : ∃ X, F.phi₀ X = k := by
    rw [← F.phi₀_range] at hkK
    exact hkK
  have hbE : F.b₀ ∈ E := F.phi₀_hmat_mem_E
  have hsq : F.r₀ * F.r₀ = 1 := by
    have := pow_orderOf_eq_one F.r₀
    rwa [F.r₀_ref.1.1, sq] at this
  have h1 : ((F.r₀ ⟨F.b₀, hbE⟩ : E) : G) = F.b₀⁻¹ :=
    refl_inv_of_mem_movedInG hsq hc (F.b₀_mem_moved hp) hbE
  have h2 : k * F.b₀ * k⁻¹ = F.b₀⁻¹ := by
    have := Equivariance.coe_conjAut hk ⟨F.b₀, hbE⟩
    rw [hkr, h1] at this
    exact this.symm
  have h3 : X * hmat F.ζ = (hmat F.ζ)⁻¹ * X := by
    apply F.phi₀_injective
    rw [map_mul, map_mul, map_inv, hX]
    show k * F.b₀ = F.b₀⁻¹ * k
    calc k * F.b₀ = (k * F.b₀ * k⁻¹) * k := by group
      _ = F.b₀⁻¹ * k := by rw [h2]
  obtain ⟨h00, h11⟩ := antidiag_of_inv (F.hζ2 h5) h3
  obtain ⟨u, hu⟩ := spBlock_anti h00 h11
  have hk' : k = F.rgHom (spDiag K (u, 1) * wEl 1) := by
    rw [← hu, ← hX]
    rfl
  rw [hk']
  refine F.conjBy_rgHom (conj_octSub_eq _ fun s => ?_)
  exact conj_spDiag_wEl_octEl 1 u 1 j s

theorem conj_rg_r₁ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) {k : G}
    (hk : k ∈ Subgroup.normalizer (E : Set G)) (hkK : k ∈ kZero p E F.r₁)
    (hkr : conjAut E k hk = F.r₁) (j : Fin 8) : conjBy k (F.rg j) = F.rg (wperm 0 j) := by
  obtain ⟨X, hX⟩ : ∃ X, F.phi₁ X = k := by
    rw [← F.phi₁_range] at hkK
    exact hkK
  have hbE : F.b₁ ∈ E := F.phi₁_hmat_mem_E
  have hsq : F.r₁ * F.r₁ = 1 := by
    have := pow_orderOf_eq_one F.r₁
    rwa [F.r₁_ref.1.1, sq] at this
  have h1 : ((F.r₁ ⟨F.b₁, hbE⟩ : E) : G) = F.b₁⁻¹ :=
    refl_inv_of_mem_movedInG hsq hc (F.b₁_mem_moved hp) hbE
  have h2 : k * F.b₁ * k⁻¹ = F.b₁⁻¹ := by
    have := Equivariance.coe_conjAut hk ⟨F.b₁, hbE⟩
    rw [hkr, h1] at this
    exact this.symm
  have h3 : X * hmat F.ζ = (hmat F.ζ)⁻¹ * X := by
    apply F.phi₁_injective
    rw [map_mul, map_mul, map_inv, hX]
    show k * F.b₁ = F.b₁⁻¹ * k
    calc k * F.b₁ = (k * F.b₁ * k⁻¹) * k := by group
      _ = F.b₁⁻¹ * k := by rw [h2]
  obtain ⟨h00, h11⟩ := antidiag_of_inv (F.hζ2 h5) h3
  obtain ⟨u, hu⟩ := spBlock'_anti h00 h11
  have hk' : k = F.rgHom (spDiag K (u, u⁻¹) * wEl 0) := by
    rw [← hu, ← hX]
    rfl
  rw [hk']
  refine F.conjBy_rgHom (conj_octSub_eq _ fun s => ?_)
  exact conj_spDiag_wEl_octEl 0 u u⁻¹ j s

omit [Finite G] in
theorem mem_rootGp_conj_iff {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) {t : MulAut E}
    {S : Subgroup G} :
    S ∈ RootGp p E f (conjAut E w hw * t * (conjAut E w hw)⁻¹) ↔ conjBy w⁻¹ S ∈ RootGp p E f t := by
  constructor
  · intro h
    have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
    have h1 := conjBy_mem_rootGp hw' h
    have h2 : conjAut E w⁻¹ hw' * (conjAut E w hw * t * (conjAut E w hw)⁻¹) *
        (conjAut E w⁻¹ hw')⁻¹ = t := by
      rw [Equivariance.conjAut_inv hw]
      group
    rwa [h2] at h1
  · intro h
    have := conjBy_mem_rootGp hw h
    rwa [Equivariance.conjBy_conjBy_inv] at this

theorem rootGp_n₂ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) :
    RootGp p E f (F.r₁ * F.r₀ * F.r₁⁻¹) = {F.rg 2, F.rg 6} := by
  obtain ⟨k, hk, hkK, hkr⟩ := F.kfat₁.2.2.2.2
  have hkr' : conjAut E k hk = F.r₁ := hkr
  have hconj := fun j => F.conj_rg_r₁ hp h5 hc hk hkK hkr' j
  have hn : F.r₁ * F.r₀ * F.r₁⁻¹ = conjAut E k hk * F.r₀ * (conjAut E k hk)⁻¹ := by rw [hkr']
  rw [hn]
  ext S
  rw [mem_rootGp_conj_iff hk, F.rootGp_r₀ h5]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left
      have := congrArg (conjBy k) h
      rw [Equivariance.conjBy_conjBy_inv, hconj] at this
      rw [this]
      rfl
    · right
      have := congrArg (conjBy k) h
      rw [Equivariance.conjBy_conjBy_inv, hconj] at this
      rw [this]
      rfl
  · rintro (h | h)
    · left
      have e' : conjBy k (F.rg 0) = F.rg 2 := hconj 0
      rw [h, ← e', Equivariance.conjBy_inv_conjBy]
    · right
      have e' : conjBy k (F.rg 4) = F.rg 6 := hconj 4
      rw [h, ← e', Equivariance.conjBy_inv_conjBy]

theorem rootGp_n₁ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) :
    RootGp p E f (F.r₀ * F.r₁ * F.r₀⁻¹) = {F.rg 5, F.rg 1} := by
  obtain ⟨k, hk, hkK, hkr⟩ := F.kfat₀.2.2.2.2
  have hkr' : conjAut E k hk = F.r₀ := hkr
  have hconj := fun j => F.conj_rg_r₀ hp h5 hc hk hkK hkr' j
  have hn : F.r₀ * F.r₁ * F.r₀⁻¹ = conjAut E k hk * F.r₁ * (conjAut E k hk)⁻¹ := by rw [hkr']
  rw [hn]
  ext S
  rw [mem_rootGp_conj_iff hk, F.rootGp_r₁ h5]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left
      have := congrArg (conjBy k) h
      rw [Equivariance.conjBy_conjBy_inv, hconj] at this
      rw [this]
      rfl
    · right
      have := congrArg (conjBy k) h
      rw [Equivariance.conjBy_conjBy_inv, hconj] at this
      rw [this]
      rfl
  · rintro (h | h)
    · left
      have e' : conjBy k (F.rg 7) = F.rg 5 := hconj 7
      rw [h, ← e', Equivariance.conjBy_inv_conjBy]
    · right
      have e' : conjBy k (F.rg 3) = F.rg 1 := hconj 3
      rw [h, ← e', Equivariance.conjBy_inv_conjBy]

end RFrame

end CFSG.RankThree.PartOne.NF7J
