module

public import CFSG.Walter.W67.Section6.Core62C
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.Walter.W67.Sec65

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External

theorem hallPResidual_ne_top_of_quot {r : ℕ} [Fact r.Prime] {N X D : Subgroup G}
    (hXN : X ≤ N) (hDX : D ≤ X) (hDN : N ≤ Subgroup.normalizer (D : Set G))
    (hXr : IsPGroup r X) (hXc : Nat.card X = r ^ (Nat.card N).factorization r) (hDX' : D ≠ X)
    (hcent : ∀ n ∈ N, n ∈ Subgroup.normalizer (X : Set G) → ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ D) :
    hallPResidual r N ≠ ⊤ := by
  have : (D.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDN
  set q := QuotientGroup.mk' (D.subgroupOf N) with hq
  have hX'c : Nat.card (X.subgroupOf N) = r ^ (Nat.card N).factorization r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv, hXc]
  set P : Sylow r N := Sylow.ofCard (X.subgroupOf N) hX'c with hP
  set Pb : Sylow r (N ⧸ D.subgroupOf N) := P.mapSurjective (QuotientGroup.mk'_surjective _)
    with hPb
  have hPb' : (Pb : Subgroup (N ⧸ D.subgroupOf N)) = (X.subgroupOf N).map q := by
    rw [hPb, Sylow.coe_mapSurjective, hP, Sylow.coe_ofCard]
  have hqD : ∀ m : N, q m = 1 ↔ (m : G) ∈ D := fun m => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmem : ∀ m : N, q m ∈ (Pb : Subgroup (N ⧸ D.subgroupOf N)) ↔ (m : G) ∈ X := by
    intro m
    rw [hPb', Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxm⟩
      have h1 : q (x⁻¹ * m) = 1 := by rw [map_mul, map_inv, hxm, inv_mul_cancel]
      have h2 : ((x⁻¹ * m : N) : G) ∈ X := hDX ((hqD _).mp h1)
      have h3 : (m : G) = x * ((x⁻¹ * m : N) : G) := by simp
      rw [h3]
      exact X.mul_mem hx h2
    · intro hm
      exact ⟨m, hm, rfl⟩
  have hnc : Subgroup.normalizer ((Pb : Subgroup (N ⧸ D.subgroupOf N)) : Set (N ⧸ D.subgroupOf N))
      ≤ Subgroup.centralizer
        ((Pb : Subgroup (N ⧸ D.subgroupOf N)) : Set (N ⧸ D.subgroupOf N)) := by
    intro y hy
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf N) y
    have hnX : (n : G) ∈ Subgroup.normalizer (X : Set G) := by
      apply JT.mem_normalizer_of_conj_mem
      intro x hx
      have h1 := (Subgroup.mem_normalizer_iff.mp hy _).mp ((hmem ⟨x, hXN hx⟩).mpr hx)
      rw [← hq, ← map_inv, ← map_mul, ← map_mul, hmem] at h1
      exact h1
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf N) z
    have hm : (m : G) ∈ X := (hmem m).mp hz
    have h1 : q (n * m * n⁻¹ * m⁻¹) = 1 := (hqD _).mpr (hcent n n.2 hnX m hm)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  obtain ⟨K, hKn, -, hKidx, -, -, -, -, hinf, -, -⟩ :=
    GroupTheory.burnside_normal_complement Pb hnc
  have hPbr : IsPGroup r (Pb : Subgroup (N ⧸ D.subgroupOf N)) := by
    rw [hPb']
    exact (hXr.comap_subtype (K := N)).map q
  have hpq : IsPGroup r ((N ⧸ D.subgroupOf N) ⧸ K) := by
    obtain ⟨k, hk⟩ := hPbr.exists_card_eq
    exact IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card, hKidx, hk])
  have hle := hallPResidual_le_ker_of_isPGroup ((QuotientGroup.mk' K).comp q) hpq
  intro htop
  apply hDX'
  refine le_antisymm hDX fun x hx => ?_
  have h1 : (⟨x, hXN hx⟩ : N) ∈ ((QuotientGroup.mk' K).comp q).ker :=
    hle (by rw [htop]; exact Subgroup.mem_top _)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  have h2 : q ⟨x, hXN hx⟩ ∈ K ⊓ (Pb : Subgroup (N ⧸ D.subgroupOf N)) :=
    ⟨h1, (hmem _).mpr hx⟩
  rw [hinf, Subgroup.mem_bot, hqD] at h2
  exact h2

theorem false_of_normalizer_eq_sup (hperf : commutator G = ⊤) {X U : Subgroup G} {ρ e : G}
    (hXc : Nat.card X = 7 ^ (Nat.card G).factorization 7) (hX : IsPGroup 7 X)
    (hUX : U ≤ X) (hUZ : X ≤ Subgroup.centralizer (U : Set G))
    (hXU : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ U)
    (hρ : ρ ^ 3 = 1) (hρX : ρ ∈ Subgroup.normalizer (X : Set G))
    (hρU : ρ ∈ Subgroup.normalizer (U : Set G))
    (hN : Subgroup.normalizer (X : Set G) = X ⊔ Subgroup.zpowers ρ)
    (he : e ∈ X) (heρ : ρ * e = e * ρ) (heU : e ^ 3 ∉ U) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set P : Sylow 7 G := Sylow.ofCard X hXc with hP
  have hPX : (P : Subgroup G) = X := Sylow.coe_ofCard _ _
  have hEngel : ∀ u z : G, u ∈ (P : Subgroup G) → z ∈ (P : Subgroup G) →
      engelSymbol (7 - 1) u z = 1 := by
    intro u z hu hz
    rw [hPX] at hu hz
    have hc : inverseFirstCommutator u z ∈ U := by
      have := hXU u⁻¹ (X.inv_mem hu) z⁻¹ (X.inv_mem hz)
      simpa [inverseFirstCommutator] using this
    have hcz := Subgroup.mem_centralizer_iff.mp (hUZ hz) _ hc
    change iteratedInverseFirstCommutator (3 + 1) (inverseFirstCommutator u z) z = 1
    exact Sec52.iterated_eq_one hcz 3
  have htop := Sec6.hallPResidual_normalizer_eq_top hperf P (Sec6.weaklyClosedIn_self P)
    (Or.inl hEngel)
  rw [hPX] at htop
  have hXc' : Nat.card X = 7 ^ (Nat.card (Subgroup.normalizer (X : Set G))).factorization 7 := by
    have h1 : Nat.card X ∣ Nat.card (Subgroup.normalizer (X : Set G)) :=
      Subgroup.card_dvd_of_le Subgroup.le_normalizer
    rw [hXc] at h1
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
    have h3 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (X : Set G))) 7
    rw [hXc, le_antisymm h3 h2]
  have hUn : (U.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hUZ.trans (Subgroup.centralizer_le_normalizer _))
  have hcomm : ∀ a b : X ⧸ U.subgroupOf X, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hXU (y : G)⁻¹ (X.inv_mem y.2) (x : G)⁻¹ (X.inv_mem x.2)
    simpa [mul_assoc] using this
  let : CommGroup (X ⧸ U.subgroupOf X) :=
    { (inferInstance : Group (X ⧸ U.subgroupOf X)) with mul_comm := hcomm }
  set π := QuotientGroup.mk' (U.subgroupOf X) with hπ
  have hπ1 : ∀ x : X, π x = 1 ↔ (x : G) ∈ U := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hρX' : ρ⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hρX
  have hρU' : ρ⁻¹ ∈ Subgroup.normalizer (U : Set G) := Subgroup.inv_mem _ hρU
  let c : X →* X :=
    { toFun := fun x => ⟨ρ * x * ρ⁻¹, (Subgroup.mem_normalizer_iff.mp hρX x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  let c' : X →* X :=
    { toFun := fun x => ⟨ρ⁻¹ * x * ρ, by
        simpa using (Subgroup.mem_normalizer_iff.mp hρX' x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hρρ : ρ * ρ = ρ⁻¹ := eq_inv_iff_mul_eq_one.mpr (by rw [← pow_three', hρ])
  have hcc : ∀ x : X, c (c x) = c' x := fun x => by
    apply Subtype.ext
    change ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * x * ρ
    have hρρ' : ρ⁻¹ * ρ⁻¹ = ρ := by rw [← mul_inv_rev, hρρ, inv_inv]
    calc ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = (ρ * ρ) * x * (ρ⁻¹ * ρ⁻¹) := by group
      _ = ρ⁻¹ * x * ρ := by rw [hρρ, hρρ']
  have hc'c : ∀ x : X, c' (c x) = x := fun x => by
    apply Subtype.ext
    change ρ⁻¹ * (ρ * x * ρ⁻¹) * ρ = x
    group
  set ν : X →* X ⧸ U.subgroupOf X := π * π.comp c * π.comp c' with hν
  have hνc : ∀ x : X, ν (c x) = ν x := fun x => by
    simp only [hν, MonoidHom.mul_apply, MonoidHom.comp_apply, hcc, hc'c]
    rw [mul_assoc (π x), mul_comm (π x)]
  have hνU : ∀ x : X, (x : G) ∈ U → ν x = 1 := fun x hx => by
    have h1 : π x = 1 := (hπ1 x).mpr hx
    have h2 : π (c x) = 1 := (hπ1 _).mpr ((Subgroup.mem_normalizer_iff.mp hρU x).mp hx)
    have h3 : π (c' x) = 1 := (hπ1 _).mpr (by
      change ρ⁻¹ * (x : G) * ρ ∈ U
      simpa using (Subgroup.mem_normalizer_iff.mp hρU' x).mp hx)
    simp only [hν, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, h2, h3, mul_one]
  set D : Subgroup G := ν.ker.map X.subtype with hD
  have hmemD : ∀ x : X, (x : G) ∈ D ↔ ν x = 1 := fun x => by
    rw [hD, ← Subgroup.coe_subtype, Subgroup.mem_map_iff_mem X.subtype_injective,
      MonoidHom.mem_ker]
  have hDX : D ≤ X := Subgroup.map_subtype_le _
  have hUD : U ≤ D := fun u hu => (hmemD ⟨u, hUX hu⟩).mpr (hνU _ hu)
  have hDX' : D ≠ X := by
    intro hDXe
    have h1 : ν ⟨e, he⟩ = 1 := (hmemD ⟨e, he⟩).mp (by rw [hDXe]; exact he)
    have h2 : c ⟨e, he⟩ = ⟨e, he⟩ := Subtype.ext (by
      change ρ * e * ρ⁻¹ = e
      rw [heρ, mul_inv_cancel_right])
    have h3 : c' ⟨e, he⟩ = ⟨e, he⟩ := Subtype.ext (by
      change ρ⁻¹ * e * ρ = e
      rw [mul_assoc, ← heρ, inv_mul_cancel_left])
    simp only [hν, MonoidHom.mul_apply, MonoidHom.comp_apply, h2, h3, ← map_mul, hπ1] at h1
    apply heU
    rw [pow_three']
    exact h1
  have hDN : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (D : Set G) := by
    rw [hN]
    refine sup_le (fun g hg => ?_) (Subgroup.zpowers_le.mpr ?_)
    · apply JT.mem_normalizer_of_conj_mem
      intro h hh
      have hhX := hDX hh
      have h1 := (hmemD ⟨h, hhX⟩).mp hh
      have h2 := (hmemD (⟨g, hg⟩ * ⟨h, hhX⟩ * (⟨g, hg⟩ : X)⁻¹)).mpr (by
        rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel])
      exact h2
    · apply JT.mem_normalizer_of_conj_mem
      intro h hh
      have hhX := hDX hh
      exact (hmemD (c ⟨h, hhX⟩)).mpr ((hνc _).trans ((hmemD ⟨h, hhX⟩).mp hh))
  let S : Subgroup G :=
    { carrier := {n | n ∈ Subgroup.normalizer (X : Set G) ∧ ∀ x ∈ X, n * x * n⁻¹ * x⁻¹ ∈ D}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun x hx => ?_⟩
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDN ha) _).mp (hb' x hx)) (ha' x hx)
      one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun x hx => ?_⟩
        have hy : a⁻¹ * x * a ∈ X := by
          simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) x).mp hx
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by
          group
        rw [e]
        exact D.inv_mem (ha' _ hy) }
  have hXS : X ≤ S := fun g hg => ⟨Subgroup.le_normalizer hg, fun x hx => hUD (hXU g hg x hx)⟩
  have hρS : ρ ∈ S := ⟨hρX, fun x hx => (hmemD (c ⟨x, hx⟩ * (⟨x, hx⟩ : X)⁻¹)).mpr (by
    rw [map_mul, hνc, map_inv, mul_inv_cancel])⟩
  have hNS : Subgroup.normalizer (X : Set G) ≤ S := by
    rw [hN]
    exact sup_le hXS (Subgroup.zpowers_le.mpr hρS)
  exact hallPResidual_ne_top_of_quot Subgroup.le_normalizer hDX hDN hX hXc' hDX'
    (fun n hn _ => (hNS hn).2) htop

end CFSG.Walter.W67.Sec65
