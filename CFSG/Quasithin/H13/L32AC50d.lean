module

public import CFSG.Quasithin.H13.L32AC50c
public import CFSG.Quasithin.H13.L32A770o

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem oTwoUpper_idem' (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2)

theorem oTwoUpper_sup_of_sylow {X S : Subgroup G} (hS : IsSylowTwoOf S X) :
    oTwoUpper X ⊔ S = X := by
  have hKX : oTwoUpper X ≤ X := oTwoUpper_le X
  refine le_antisymm (sup_le hKX hS.1) ?_
  have h1 : (oTwoUpper X ⊔ S).relIndex X ∣ S.relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X le_sup_right
  have h2 : (oTwoUpper X ⊔ S).relIndex X ∣ (oTwoUpper X).relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X le_sup_left
  have h3 : ∃ m : ℕ, (oTwoUpper X).relIndex X = 2 ^ m := by
    have hn : ((oTwoUpper X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr (le_normalizer_oTwoUpper X)
    have hp : IsPGroup 2 (↥X ⧸ (oTwoUpper X).subgroupOf X) := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X h.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hk
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    exact ⟨m, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]⟩
  obtain ⟨m, hm⟩ := h3
  rw [hm] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hj0 : j = 0 := by
    by_contra hne
    apply hS.2.2
    have h2d : 2 ∣ (oTwoUpper X ⊔ S).relIndex X := by
      rw [hj]
      exact dvd_pow_self 2 hne
    exact h2d.trans h1
  rw [hj0, pow_zero] at hj
  exact Subgroup.relIndex_eq_one.mp hj

@[expose] def preim (π : ↥H →* Equiv.Perm (Fin 7)) (R : Subgroup (Equiv.Perm (Fin 7))) :
    Subgroup G :=
  (R.comap π).map H.subtype

omit [Finite G] in
theorem mem_preim {π : ↥H →* Equiv.Perm (Fin 7)} {R : Subgroup (Equiv.Perm (Fin 7))} {g : G} :
    g ∈ preim π R ↔ ∃ hg : g ∈ H, π ⟨g, hg⟩ ∈ R := by
  constructor
  · rintro ⟨⟨x, hx⟩, hxR, rfl⟩
    exact ⟨hx, hxR⟩
  · rintro ⟨hg, hgR⟩
    exact ⟨⟨g, hg⟩, hgR, rfl⟩

omit [Finite G] in
theorem preim_le (π : ↥H →* Equiv.Perm (Fin 7)) (R : Subgroup (Equiv.Perm (Fin 7))) :
    preim π R ≤ H :=
  Subgroup.map_subtype_le _

theorem pCore_le_T (S : Setting147 G T L V H) :
    CFSG.Open.pCore 2 ↥H ≤ T.subgroupOf H := by
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (L32A.pCoreOf_le_of_le S.hyp hTH ⟨x, hx, rfl⟩)

theorem exists_lift_three {π : ↥H →* Equiv.Perm (Fin 7)} {R : Subgroup (Equiv.Perm (Fin 7))}
    (hRr : R ≤ π.range) {y : Equiv.Perm (Fin 7)} (hy : y ∈ R) (hy3 : y ^ 3 = 1) :
    ∃ u ∈ oTwoUpper (preim π R), ∃ hu : u ∈ H, π ⟨u, hu⟩ = y := by
  obtain ⟨h, hh⟩ := hRr hy
  have hX : (h : G) ∈ preim π R := mem_preim.mpr ⟨h.2, by rw [hh]; exact hy⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper (preim π R) hX
  refine ⟨((h : G) ^ 2 ^ k) ^ 2 ^ k, Subgroup.pow_mem _ hk _, H.pow_mem (H.pow_mem h.2 _) _, ?_⟩
  obtain ⟨q, hq⟩ := L32NSet14.exists_four_pow k
  have e : (⟨((h : G) ^ 2 ^ k) ^ 2 ^ k, H.pow_mem (H.pow_mem h.2 _) _⟩ : ↥H) = h ^ 4 ^ k := by
    apply Subtype.ext
    have h4 : 2 ^ k * 2 ^ k = 4 ^ k := by
      rw [← mul_pow]
      norm_num
    show ((h : G) ^ 2 ^ k) ^ 2 ^ k = ((h ^ 4 ^ k : ↥H) : G)
    rw [Subgroup.coe_pow, ← pow_mul, h4]
  rw [e, map_pow, hh, ← hq, pow_add, pow_one, pow_mul, hy3, one_pow, mul_one]

theorem s3_preim (S : Setting147 G T L V H) {π : ↥H →* Equiv.Perm (Fin 7)}
    (hker : π.ker = CFSG.Open.pCore 2 ↥H) {R : Subgroup (Equiv.Perm (Fin 7))}
    (hTR : (T.subgroupOf H).map π ≤ R) (hRr : R ≤ π.range)
    (h3 : ((T.subgroupOf H).map π).relIndex R = 3)
    (hn : ¬ R ≤ Subgroup.normalizer
      (((T.subgroupOf H).map π : Subgroup (Equiv.Perm (Fin 7))) : Set (Equiv.Perm (Fin 7)))) :
    oTwoUpper (oTwoUpper (preim π R)) = oTwoUpper (preim π R) ∧
      T ≤ Subgroup.normalizer (oTwoUpper (preim π R) : Set G) ∧
      quasithinO2QuotientIso (oTwoUpper (preim π R) ⊔ T) (Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := preim π R with hXdef
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hTX : T ≤ X := fun t ht => mem_preim.mpr ⟨hTH ht, hTR ⟨⟨t, hTH ht⟩, ht, rfl⟩⟩
  have hXH : X ≤ H := preim_le π R
  have hkerT : π.ker ≤ T.subgroupOf H := hker ▸ pCore_le_T S
  have hX3 : T.relIndex X = 3 := by
    have e1 : (T.subgroupOf H).relIndex (X.subgroupOf H) = T.relIndex X :=
      Subgroup.relIndex_subgroupOf hXH
    have e2 : X.subgroupOf H = R.comap π :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have e3 : ((T.subgroupOf H).map π).comap π = T.subgroupOf H :=
      Subgroup.comap_map_eq_self hkerT
    have e4 : (R.comap π).map π = R := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr hRr]
    rw [← e1, e2, ← e3, Subgroup.relIndex_comap, e4, h3]
  have hTsylX : IsSylowTwoOf T X := by
    refine ⟨hTX, hTsyl.2.1, fun h2 => hTsyl.2.2 ?_⟩
    have h1 : T.relIndex X * X.relIndex H = T.relIndex H :=
      Subgroup.relIndex_mul_relIndex T X H hTX hXH
    show 2 ∣ T.relIndex H
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _
  have hsup : oTwoUpper X ⊔ T = X := oTwoUpper_sup_of_sylow hTsylX
  refine ⟨oTwoUpper_idem' X, hTX.trans (le_normalizer_oTwoUpper X), ?_⟩
  rw [hsup]
  have hnX : ¬ X ≤ Subgroup.normalizer (T : Set G) := by
    intro hXN
    apply hn
    intro r hr
    obtain ⟨h, rfl⟩ := hRr hr
    have hhX : (h : G) ∈ X := mem_preim.mpr ⟨h.2, hr⟩
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ s : ↥H, s ∈ T.subgroupOf H → h * s * h⁻¹ ∈ T.subgroupOf H := fun s hs => by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hXN hhX) s).mp hs
    have key' : ∀ s : ↥H, s ∈ T.subgroupOf H → h⁻¹ * s * h ∈ T.subgroupOf H := fun s hs => by
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXN hhX)) s).mp hs
      simpa using this
    intro p
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨h * s * h⁻¹, key s hs, by simp [map_mul, map_inv]⟩
    · rintro ⟨s, hs, hsp⟩
      refine ⟨h⁻¹ * s * h, key' s hs, ?_⟩
      rw [map_mul, map_mul, map_inv, hsp]
      group
  obtain ⟨e⟩ := L32A.nonempty_quotient_perm_three hTX hTsyl.2.1 hX3 hnX
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

omit [Finite G] in
theorem relIndex_eq_card_map {U I Z : Subgroup G} {W : Type*} [Group W] (β : ↥U →* W)
    (hker : β.ker = I.subgroupOf U) (hZU : Z ≤ U) :
    I.relIndex Z = Nat.card ((Z.subgroupOf U).map β) := by
  set Z' := Z.subgroupOf U with hZ'
  set φ : ↥Z' →* W := β.comp Z'.subtype with hφ
  have hrange : φ.range = Z'.map β := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerφ : φ.ker = (I.subgroupOf U).subgroupOf Z' := by
    ext z
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf]
    rfl
  rw [← Subgroup.relIndex_subgroupOf hZU, Subgroup.relIndex, ← hkerφ, Subgroup.index_ker,
    hrange]

end CFSG.Quasithin.H13.L32A.C
