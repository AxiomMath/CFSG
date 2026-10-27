module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.Ch3g316

open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_mem_of_le_normalizer {K Q : Subgroup G}
    (hQn : K ≤ Subgroup.normalizer (Q : Set G)) {k q : G} (hk : k ∈ K) (hq : q ∈ Q) :
    k * q * k⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hQn hk) q).mp hq

omit [Finite G] in
private theorem exists_subgroup_commutator_mem {K Q : Subgroup G}
    (hQn : K ≤ Subgroup.normalizer (Q : Set G)) (x : G) :
    ∃ X : Subgroup G, ∀ c : G, c ∈ X ↔ c ∈ K ∧ c * x * c⁻¹ * x⁻¹ ∈ Q := by
  refine ⟨{ carrier := {c | c ∈ K ∧ c * x * c⁻¹ * x⁻¹ ∈ Q}
            one_mem' := ⟨K.one_mem, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun c => Iff.rfl⟩
  · rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, ?_⟩
    have h := Q.mul_mem (conj_mem_of_le_normalizer hQn haK hb) ha
    convert h using 1
    group
  · rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, ?_⟩
    have h := conj_mem_of_le_normalizer hQn (K.inv_mem haK) (Q.inv_mem ha)
    convert h using 1
    group

theorem exists_mem_normalizer_conj_mod {K P Q : Subgroup G} (hP : IsSylowTwoOf P K)
    (hQn : K ≤ Subgroup.normalizer (Q : Set G)) (hPQ : ⁅P, P⁆ ≤ Q) {x u : G} (hx : x ∈ P)
    (hu : u ∈ K) (hux : u * x * u⁻¹ ∈ P) :
    ∃ n ∈ K ⊓ Subgroup.normalizer (P : Set G), (n⁻¹ * x * n)⁻¹ * (u * x * u⁻¹) ∈ Q := by
  obtain ⟨X, hX⟩ := exists_subgroup_commutator_mem hQn x
  have hXK : X ≤ K := fun c hc => ((hX c).1 hc).1
  have hPX : P ≤ X := fun p hp =>
    (hX p).2 ⟨hP.1 hp, hPQ (Subgroup.commutator_mem_commutator hp hx)⟩
  have hP' : IsSylowTwoOf (B6.conjSub u⁻¹ P) K := by
    have h := B6.isSylowTwoOf_conjSub hP u⁻¹
    rwa [B6.conjSub_eq_self (Subgroup.le_normalizer (K.inv_mem hu))] at h
  have hP'X : B6.conjSub u⁻¹ P ≤ X := by
    intro y hy
    rw [B6.mem_conjSub, inv_inv] at hy
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, y = u⁻¹ * p * u := ⟨u * y * u⁻¹, hy, by group⟩
    refine (hX _).2 ⟨K.mul_mem (K.mul_mem (K.inv_mem hu) (hP.1 hp)) hu, ?_⟩
    have hq : p * (u * x * u⁻¹) * p⁻¹ * (u * x * u⁻¹)⁻¹ ∈ Q :=
      hPQ (Subgroup.commutator_mem_commutator hp hux)
    have h := conj_mem_of_le_normalizer hQn (K.inv_mem hu) hq
    convert h using 1
    group
  obtain ⟨c, hcX, hc⟩ := B6.isSylowTwoOf_exists_conj (B6.isSylowTwoOf_mono hP' hP'X hXK)
    (B6.isSylowTwoOf_mono hP hPX hXK)
  have hnN : c * u⁻¹ ∈ Subgroup.normalizer (P : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show B6.conjSub (c * u⁻¹) P = P
    rw [B6.conjSub_mul, ← hc]
  refine ⟨c * u⁻¹, ⟨K.mul_mem (hXK hcX) (K.inv_mem hu), hnN⟩, ?_⟩
  · have h1 := ((hX c⁻¹).1 (X.inv_mem hcX)).2
    have h2 := conj_mem_of_le_normalizer hQn (K.inv_mem (hP.1 hx)) (Q.inv_mem h1)
    have h3 := conj_mem_of_le_normalizer hQn hu h2
    convert h3 using 1
    group

private theorem le_focalSubgroup_of_residual {H : Type} [Group H] [Finite H] (S : Sylow 2 H)
    (hH : ∀ N : Subgroup H, N.Normal → (∀ y : H, ∃ k : ℕ, y ^ 2 ^ k ∈ N) → N = ⊤) :
    (S : Subgroup H) ≤ S.focalSubgroup := by
  have hker : S.transferFocal.ker = ⊤ := by
    refine hH _ (MonoidHom.normal_ker _) fun y => ?_
    obtain ⟨k, hk⟩ := (S.isPGroup'.to_quotient S.focalSubgroupOf) (S.transferFocal y)
    exact ⟨k, by simpa [MonoidHom.mem_ker, map_pow] using hk⟩
  intro s hs
  obtain ⟨y, hy⟩ := Subgroup.transferFocal_surjective S (QuotientGroup.mk ⟨s, hs⟩)
  have hy1 : S.transferFocal y = 1 := MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top y)
  rw [hy1] at hy
  have := (QuotientGroup.eq_one_iff _).mp hy.symm
  simpa [Subgroup.focalSubgroupOf_def, Subgroup.mem_subgroupOf] using this

private theorem le_focalSubgroup_subgroupOf {K P : Subgroup G} (hP : IsSylowTwoOf P K)
    (hK : twoResidual K = K) : P.subgroupOf K ≤ Subgroup.focalSubgroup (P.subgroupOf K) := by
  have h := le_focalSubgroup_of_residual (B6.toSylow2 hP) ?_
  · rwa [B6.toSylow2_coe] at h
  · intro N hN hN2
    have hNn : K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)]
      have h : (N.map K.subtype).subgroupOf K = N :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective N
      rw [h]
      exact hN
    have hle : twoResidual K ≤ N.map K.subtype :=
      twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le N) hNn fun y hy => by
        obtain ⟨k, hk⟩ := hN2 ⟨y, hy⟩
        exact ⟨k, ⟨_, hk, rfl⟩⟩
    rw [eq_top_iff]
    intro y _
    have hyK : (y : G) ∈ twoResidual K := by
      rw [hK]
      exact y.2
    obtain ⟨y', hy', hyy⟩ := hle hyK
    have hy'y : y' = y := Subtype.ext hyy
    exact hy'y ▸ hy'

theorem sylow_le_sup_of_fusion {K P Q D : Subgroup G} (hP : IsSylowTwoOf P K)
    (hK : twoResidual K = K) (_hQP : Q ≤ P) (hQn : K ≤ Subgroup.normalizer (Q : Set G))
    (hPQ : ⁅P, P⁆ ≤ Q)
    (hD : ∀ t ∈ P, ∀ y ∈ K ⊓ Subgroup.normalizer (P : Set G), t⁻¹ * (y * t * y⁻¹) ∈ D) :
    P ≤ D ⊔ Q := by
  have hfoc := le_focalSubgroup_subgroupOf hP hK
  have hsub : Subgroup.focalSubgroup (P.subgroupOf K) ≤ (D ⊔ Q).subgroupOf K := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro _ ⟨hgS, x, hxS, u, rfl⟩
    have hxP : (x : G) ∈ P := hxS
    have hgP : x.1 * u.1 * x.1⁻¹ * u.1⁻¹ ∈ P := hgS
    have hux : u.1 * x.1 * u.1⁻¹ ∈ P := by
      have h := P.inv_mem (P.mul_mem (P.inv_mem hxP) hgP)
      simpa [mul_assoc] using h
    obtain ⟨n, ⟨hnK, hnN⟩, hr⟩ := exists_mem_normalizer_conj_mod hP hQn hPQ hxP u.2 hux
    have hd := hD x.1⁻¹ (P.inv_mem hxP) n⁻¹ ⟨K.inv_mem hnK, (Subgroup.normalizer _).inv_mem hnN⟩
    have hq := conj_mem_of_le_normalizer hQn (hP.1 hxP) (Q.inv_mem hr)
    have key : x.1 * u.1 * x.1⁻¹ * u.1⁻¹ = (x.1 * ((n⁻¹ * x.1 * n)⁻¹ * (u.1 * x.1 * u.1⁻¹))⁻¹ *
        x.1⁻¹) * (x.1⁻¹⁻¹ * (n⁻¹ * x.1⁻¹ * n⁻¹⁻¹)) := by
      group
    show x.1 * u.1 * x.1⁻¹ * u.1⁻¹ ∈ D ⊔ Q
    rw [key, sup_comm]
    exact Subgroup.mul_mem_sup hq hd
  intro g hg
  exact hsub (hfoc (show (⟨g, hP.1 hg⟩ : K) ∈ P.subgroupOf K from hg))

end CFSG.Quasithin.Ch3g316
