module

public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.RankThree.CentralLiftU.UnitaryTriBasic

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.CentralExt (liftSubgroup mem_liftSubgroup_iff liftSubgroup_le_comap
  pLift_mem_liftSubgroup map_pLift eq_one_of_mem_ker exists_orderOf_eq_pow_of_mem)

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {r ε : ℕ}

section Borel

theorem isPGroup_hypUnitriangular (hε : ε ≤ 1) : IsPGroup ℓ (hypUnitriangular h r ε) := by
  have : Fact ℓ.Prime := ⟨h.prime⟩
  refine IsPGroup.of_card (n := f * ((2 * r + ε) * (2 * r + ε - 1) / 2)) ?_
  rw [card_hypUnitriangular h hε, ← pow_mul]

theorem isPGroup_simpleKerU (hε : ε ≤ 1) (i : Fin r) : IsPGroup ℓ (simpleKerU h r ε i) :=
  (isPGroup_hypUnitriangular hε).to_le (simpleKerU_le i)

theorem hypUnitriangular_inf_hypTorus : hypUnitriangular h r ε ⊓ hypTorus h r ε = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hU, a, d, -, -, hm⟩
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  rw [hm, Subgroup.coe_one, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  have := apply_self_of_mem hU x
  rw [hm, diagonal_apply_eq] at this
  exact this

theorem conj_mem_hypUnitriangular_of_mem_hypBorel (hε : ε ≤ 1) {b u : hypSU h r ε}
    (hb : b ∈ hypBorel h r ε) (hu : u ∈ hypUnitriangular h r ε) :
    b * u * b⁻¹ ∈ hypUnitriangular h r ε := by
  have hN := normal_hypUnitriangular (h := h) (r := r) hε
  have hu' : (⟨u, hypUnitriangular_le_hypBorel h hu⟩ : hypBorel h r ε) ∈
      (hypUnitriangular h r ε).subgroupOf (hypBorel h r ε) := hu
  exact hN.conj_mem _ hu' ⟨b, hb⟩

theorem hypBorel_le_sup (hε : ε ≤ 1) (hr : 1 ≤ r) :
    hypBorel h r ε ≤ hypUnitriangular h r ε ⊔ hypTorus h r ε := by
  intro b hb
  set a := hypDiagHom h r ε hε ⟨b, hb⟩
  obtain ⟨t, htT, ht⟩ : ∃ (t : hypSU h r ε) (htT : t ∈ hypTorus h r ε),
      hypDiagHom h r ε hε ⟨t, hypTorus_le_hypBorel h htT⟩ = a := by
    have key : ∀ (d : Fin ε → Kˣ), (∀ k, h.norm (d k : K) = 1) → torusRatio h a d = 1 →
        ∃ (t : hypSU h r ε) (htT : t ∈ hypTorus h r ε),
          hypDiagHom h r ε hε ⟨t, hypTorus_le_hypBorel h htT⟩ = a := by
      intro d hd hp
      obtain ⟨g, hgT, hg⟩ := torusMat_mem_hypSU h a hd hp
      refine ⟨g, hgT, funext fun i => Units.ext ?_⟩
      rw [coe_hypDiagHom]
      change ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i)
        (.inl i) = _
      rw [hg, diagonal_apply_eq]
      rfl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · have ha : a ∈ evenDiagGroup h r := by
        rw [← range_hypDiagHom_even]
        exact ⟨_, rfl⟩
      refine key isEmptyElim (fun k => isEmptyElim k) ?_
      rw [torusRatio, Fin.prod_univ_zero, mul_one]
      exact mem_evenDiagGroup.1 ha
    · have hnorm : h.norm ((ratioHom h r a)⁻¹ : Kˣ) = 1 := by
        have : ratioHom h r a ∈ (Units.map h.normHom).ker := by
          rw [← range_ratioHom hr]
          exact ⟨a, rfl⟩
        rw [UnitaryFieldData.mem_ker_normUnits] at this
        rw [Units.val_inv_eq_inv_val, norm_inv_eq h, this, inv_one]
      refine key (fun _ => (ratioHom h r a)⁻¹) (fun _ => hnorm) ?_
      rw [torusRatio, ← coe_ratioHom, Fin.prod_univ_one, ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
  have hu : b * t⁻¹ ∈ hypUnitriangular h r ε := by
    have hk : (⟨b, hb⟩ * (⟨t, hypTorus_le_hypBorel h htT⟩ : hypBorel h r ε)⁻¹ :
        hypBorel h r ε) ∈ (hypDiagHom h r ε hε).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ht, mul_inv_cancel]
    rw [ker_hypDiagHom hε, Subgroup.mem_subgroupOf] at hk
    exact hk
  rw [show b = (b * t⁻¹) * t by group]
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right htT)

end Borel

section Lifts

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} [Fact ℓ.Prime]
  (hcen : π.ker ≤ Subgroup.center R)
include hcen

theorem mem_liftSubgroup_of {V : Subgroup (hypSU h r ε)} (hV : IsPGroup ℓ V) {x : R}
    (hx : π x ∈ V) (hxo : ∃ n : ℕ, orderOf x = ℓ ^ n) : x ∈ liftSubgroup ℓ π V :=
  (mem_liftSubgroup_iff hcen hV).2 ⟨hx, hxo⟩

theorem liftSubgroup_mono {V W : Subgroup (hypSU h r ε)} (hW : IsPGroup ℓ W) (hVW : V ≤ W) :
    liftSubgroup ℓ π V ≤ liftSubgroup ℓ π W := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := (mem_liftSubgroup_iff hcen (hW.to_le hVW)).1 hx
  exact mem_liftSubgroup_of hcen hW (hVW hx1) hx2

theorem conj_mem_liftSubgroup {V W : Subgroup (hypSU h r ε)} (hV : IsPGroup ℓ V)
    (hW : IsPGroup ℓ W) {e : R} (he : ∀ u ∈ V, π e * u * (π e)⁻¹ ∈ W) {x : R}
    (hx : x ∈ liftSubgroup ℓ π V) : e * x * e⁻¹ ∈ liftSubgroup ℓ π W := by
  obtain ⟨hx1, n, hn⟩ := (mem_liftSubgroup_iff hcen hV).1 hx
  refine mem_liftSubgroup_of hcen hW ?_ ⟨n, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact he _ hx1
  · rw [← hn]
    exact MulEquiv.orderOf_eq (MulAut.conj e) x

theorem mem_normalizer_liftSubgroup {V : Subgroup (hypSU h r ε)} (hV : IsPGroup ℓ V) {e : R}
    (he : ∀ u ∈ V, π e * u * (π e)⁻¹ ∈ V) (he' : ∀ u ∈ V, (π e)⁻¹ * u * π e ∈ V) :
    e ∈ Subgroup.normalizer (liftSubgroup ℓ π V : Set R) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_liftSubgroup hcen hV hV he, fun hx => ?_⟩
  have := conj_mem_liftSubgroup hcen hV hV (e := e⁻¹) (fun u hu => by
    rw [map_inv, inv_inv]
    exact he' u hu) hx
  simpa [mul_assoc] using this

end Lifts

section BorelLift

variable {R : Type*} [Group R] [Finite R] {π : R →* hypSU h r ε} [Fact ℓ.Prime]
  (hcen : π.ker ≤ Subgroup.center R) (hε : ε ≤ 1) {H : Subgroup R}
  (hHT : ∀ y ∈ H, π y ∈ hypTorus h r ε)
include hcen hε hHT

theorem le_normalizer_liftU :
    H ≤ Subgroup.normalizer (liftSubgroup ℓ π (hypUnitriangular h r ε) : Set R) := fun y hy =>
  mem_normalizer_liftSubgroup hcen (isPGroup_hypUnitriangular hε)
    (fun u hu => conj_mem_hypUnitriangular_of_mem_hypBorel hε
      (hypTorus_le_hypBorel h (hHT y hy)) hu)
    (fun u hu => by
      have := conj_mem_hypUnitriangular_of_mem_hypBorel hε
        (hypTorus_le_hypBorel h (inv_mem (hHT y hy))) hu
      rwa [inv_inv] at this)

theorem mem_liftBorel_iff {x : R} :
    x ∈ liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H ↔
      ∃ u ∈ liftSubgroup ℓ π (hypUnitriangular h r ε), ∃ y ∈ H, x = u * y := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_normalizer_liftU hcen hε hHT), Set.mem_mul]
  exact ⟨fun ⟨u, hu, y, hy, e⟩ => ⟨u, hu, y, hy, e.symm⟩,
    fun ⟨u, hu, y, hy, e⟩ => ⟨u, hu, y, hy, e.symm⟩⟩

variable (hπ : Function.Surjective π) (hC : ¬ℓ ∣ Nat.card π.ker)

include hπ hC in
theorem map_liftBorel (hr : 1 ≤ r) (hTH : ∀ t ∈ hypTorus h r ε, ∃ y ∈ H, π y = t) :
    (liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H).map π = hypBorel h r ε := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, sup_le_iff]
    refine ⟨fun x hx => hypUnitriangular_le_hypBorel h
      (liftSubgroup_le_comap hcen (isPGroup_hypUnitriangular hε) hx),
      fun y hy => hypTorus_le_hypBorel h (hHT y hy)⟩
  · refine (hypBorel_le_sup hε hr).trans (sup_le ?_ ?_)
    · intro u hu
      exact ⟨_, Subgroup.mem_sup_left (pLift_mem_liftSubgroup hπ hcen hC
        (isPGroup_hypUnitriangular hε) hu),
        map_pLift hπ hC (exists_orderOf_eq_pow_of_mem (isPGroup_hypUnitriangular hε) ⟨u, hu⟩)⟩
    · intro t ht
      obtain ⟨y, hy, rfl⟩ := hTH t ht
      exact ⟨y, Subgroup.mem_sup_right hy, rfl⟩

include hC in
theorem injective_pi_liftBorel (hinj : Set.InjOn π H) :
    Function.Injective
      (π.comp (liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, hx⟩ h1
  have h1' : π x = 1 := h1
  obtain ⟨u, hu, y, hy, rfl⟩ := (mem_liftBorel_iff hcen hε hHT).1 hx
  have huy : π u = (π y)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact h1')
  have hmem : π u ∈ hypUnitriangular h r ε ⊓ hypTorus h r ε :=
    Subgroup.mem_inf.2 ⟨liftSubgroup_le_comap hcen (isPGroup_hypUnitriangular hε) hu, by
      rw [huy]
      exact inv_mem (hHT y hy)⟩
  rw [hypUnitriangular_inf_hypTorus, Subgroup.mem_bot] at hmem
  obtain ⟨-, n, hn⟩ := (mem_liftSubgroup_iff hcen (isPGroup_hypUnitriangular hε)).1 hu
  have hu1 : u = 1 := eq_one_of_mem_ker hC hmem (n := n) (by rw [← hn, pow_orderOf_eq_one])
  have hy1 : π y = 1 := by rw [hmem, eq_comm, inv_eq_one] at huy; exact huy
  have hy2 : y = 1 := hinj hy (one_mem H) (hy1.trans (map_one π).symm)
  apply Subtype.ext
  simp [hu1, hy2]

theorem mem_liftBorel_iff_root (i : Fin r) {X : Set R}
    (hXU : ∀ x ∈ X, x ∈ liftSubgroup ℓ π (hypUnitriangular h r ε))
    (hdec : ∀ u ∈ hypUnitriangular h r ε, ∃ x ∈ X, (π x)⁻¹ * u ∈ simpleKerU h r ε i) {x : R} :
    x ∈ liftSubgroup ℓ π (hypUnitriangular h r ε) ⊔ H ↔
      ∃ x' ∈ X, ∃ u ∈ liftSubgroup ℓ π (simpleKerU h r ε i), ∃ y ∈ H, x = x' * u * y := by
  constructor
  · intro hx
    obtain ⟨u, hu, y, hy, rfl⟩ := (mem_liftBorel_iff hcen hε hHT).1 hx
    obtain ⟨x', hx', hdx⟩ := hdec (π u)
      (liftSubgroup_le_comap hcen (isPGroup_hypUnitriangular hε) hu)
    refine ⟨x', hx', x'⁻¹ * u, ?_, y, hy, by group⟩
    have hmem : x'⁻¹ * u ∈ liftSubgroup ℓ π (hypUnitriangular h r ε) :=
      mul_mem (inv_mem (hXU x' hx')) hu
    obtain ⟨-, hn⟩ := (mem_liftSubgroup_iff hcen (isPGroup_hypUnitriangular hε)).1 hmem
    refine mem_liftSubgroup_of hcen (isPGroup_simpleKerU hε i) ?_ hn
    rw [map_mul, map_inv]
    exact hdx
  · rintro ⟨x', hx', u, hu, y, hy, rfl⟩
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (hXU x' hx')) (Subgroup.mem_sup_left ?_))
      (Subgroup.mem_sup_right hy)
    exact liftSubgroup_mono hcen (isPGroup_hypUnitriangular hε) (simpleKerU_le i) hu

end BorelLift

end CFSG.RankThree.CentralLiftU
