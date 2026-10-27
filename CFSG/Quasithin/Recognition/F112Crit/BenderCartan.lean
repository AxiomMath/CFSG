module

public import CFSG.Quasithin.Recognition.F112Crit.BenderLocalOf
public import CFSG.Quasithin.Background.RonanF13CoverAux

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

variable {K : Type*} [Group K] {q i e : ℕ} {P : Subgroup K} {t : K}

theorem BenderCore.commute_of_mem_cartan (h : BenderCore q i e P t) {p d : K} (hp : p ∈ P)
    (hd : d ∈ cartan P t) (hfix : (p * t)⁻¹ * d * (p * t) ∈ borel P) : p * d = d * p := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  have hdM : d ∈ borel P := hd.1
  have hpM : p ∈ borel P := le_borel P hp
  have h1 : p⁻¹ * d * p ∈ cartan P t := by
    refine Subgroup.mem_inf.mpr
      ⟨(borel P).mul_mem ((borel P).mul_mem ((borel P).inv_mem hpM) hdM) hpM, ?_⟩
    rw [mem_conjugate_iff_mul_inv]
    have e1 : t * (p⁻¹ * d * p) * t⁻¹ = (p * t)⁻¹ * d * (p * t) := by
      rw [mul_inv_rev, hti]
      group
    rw [e1]
    exact hfix
  have h2 : d⁻¹ * (p⁻¹ * d * p) ∈ P ⊓ cartan P t := by
    refine Subgroup.mem_inf.mpr ⟨?_, (cartan P t).mul_mem ((cartan P t).inv_mem hd) h1⟩
    have hdi : d⁻¹ ∈ normalizer (P : Set K) := (borel P).inv_mem hdM
    have h3 : d⁻¹ * p⁻¹ * d⁻¹⁻¹ ∈ P := (mem_normalizer_iff.mp hdi p⁻¹).mp (P.inv_mem hp)
    rw [inv_inv] at h3
    have h4 := P.mul_mem h3 hp
    simpa only [mul_assoc] using h4
  rw [h.inf_eq, mem_bot] at h2
  have h5 : p⁻¹ * d * p = d := by
    have h6 := congrArg (d * ·) h2
    simpa [mul_assoc] using h6
  calc p * d = p * (p⁻¹ * d * p) := by rw [h5]
    _ = d * p := by group

theorem BenderCore.eq_one_of_forall_commute [Finite K] (h : BenderCore q i e P t) (hq : 3 ≤ q)
    (hP : IsPGroup 2 P) {p : K} (hp : p ∈ P) (hpD : ∀ d ∈ cartan P t, p * d = d * p) :
    p = 1 := by
  by_contra hp1
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hpk : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpk
  have hord1 : orderOf p ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hord1 (by simpa using hj)
  have h2 : 2 ∣ orderOf p := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  have hpos : orderOf p ≠ 0 := (orderOf_pos p).ne'
  set z := p ^ (orderOf p / 2) with hzdef
  have hz : orderOf z = 2 := orderOf_pow_orderOf_div hpos h2
  have hz2 : z * z = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  have hzroot : z ∈ rootCenter P := h.mem_rootCenter_of_mul_self (P.pow_mem hp _) hz2
  have hle : cartan P t ≤ cartan P t ⊓ centralizer ({z} : Set K) := fun d hd =>
    ⟨hd, mem_centralizer_singleton_iff.mpr
      ((Commute.pow_left (hpD d hd) _ : Commute (p ^ (orderOf p / 2)) d).symm.eq)⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [h.card_cartan, h.card_cartan_inf_centralizer hzroot hz1] at hcard
  have hDpos : 0 < Nat.card (cartan P t) := Nat.card_pos
  rw [h.card_cartan] at hDpos
  have he : 0 < e := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hDpos
  have h2e : 2 * e ≤ (q - 1) * e := Nat.mul_le_mul_right e (by omega)
  omega

theorem BenderCore.mem_borel_or_of_cartan [Finite K] (h : BenderCore q i e P t) (hq : 3 ≤ q)
    (hP : IsPGroup 2 P) {y : K} (hy : ∀ d ∈ cartan P t, y⁻¹ * d * y ∈ borel P) :
    y ∈ borel P ∨ t⁻¹ * y ∈ borel P := by
  by_cases hyM : y ∈ borel P
  · exact Or.inl hyM
  obtain ⟨p, hp, m, hm, rfl⟩ := h.bruhat hyM
  have hD : ∀ d ∈ cartan P t, p * d = d * p := fun d hd => by
    refine h.commute_of_mem_cartan hp hd ?_
    have e1 : (p * t)⁻¹ * d * (p * t) = m * ((p * t * m)⁻¹ * d * (p * t * m)) * m⁻¹ := by group
    rw [e1]
    exact (borel P).mul_mem ((borel P).mul_mem hm (hy d hd)) ((borel P).inv_mem hm)
  obtain rfl := h.eq_one_of_forall_commute hq hP hp hD
  right
  simpa [mul_assoc] using hm

theorem BenderCore.mem_borel_or_of_forall [Finite K] (h : BenderCore q i e P t) (hq : 3 ≤ q)
    (hP : IsPGroup 2 P) {x y : K} (hx : x ∉ borel P)
    (hy : ∀ d ∈ borel P, x⁻¹ * d * x ∈ borel P → y⁻¹ * d * y ∈ borel P) :
    y ∈ borel P ∨ x⁻¹ * y ∈ borel P := by
  have hti : t⁻¹ = t := inv_eq_of_mul_self h.sq_eq_one
  obtain ⟨p₀, hp₀, m₀, hm₀, rfl⟩ := h.bruhat hx
  have hp₀M : p₀ ∈ borel P := le_borel P hp₀
  have key : ∀ d ∈ cartan P t, (p₀⁻¹ * y)⁻¹ * d * (p₀⁻¹ * y) ∈ borel P := by
    intro d hd
    have htd : t⁻¹ * d * t ∈ borel P := by
      have h1 := mem_conjugate_iff_mul_inv.mp hd.2
      rw [hti] at h1
      rw [hti]
      exact h1
    have hd' : p₀ * d * p₀⁻¹ ∈ borel P :=
      (borel P).mul_mem ((borel P).mul_mem hp₀M hd.1) ((borel P).inv_mem hp₀M)
    have hx' : (p₀ * t * m₀)⁻¹ * (p₀ * d * p₀⁻¹) * (p₀ * t * m₀) ∈ borel P := by
      have e1 : (p₀ * t * m₀)⁻¹ * (p₀ * d * p₀⁻¹) * (p₀ * t * m₀) =
          m₀⁻¹ * (t⁻¹ * d * t) * m₀ := by group
      rw [e1]
      exact (borel P).mul_mem ((borel P).mul_mem ((borel P).inv_mem hm₀) htd) hm₀
    have e2 : (p₀⁻¹ * y)⁻¹ * d * (p₀⁻¹ * y) = y⁻¹ * (p₀ * d * p₀⁻¹) * y := by group
    rw [e2]
    exact hy _ hd' hx'
  rcases h.mem_borel_or_of_cartan hq hP key with h1 | h1
  · left
    have h2 := (borel P).mul_mem hp₀M h1
    simpa using h2
  · right
    have e3 : (p₀ * t * m₀)⁻¹ * y = m₀⁻¹ * (t⁻¹ * (p₀⁻¹ * y)) := by group
    rw [e3]
    exact (borel P).mul_mem ((borel P).inv_mem hm₀) h1

theorem BenderCore.eq_one_of_mem_borel_inf [Finite K] (h : BenderCore q i e P t) {x g : K}
    (hx : x ∉ borel P) (hg : g ∈ borel P) (hxg : x⁻¹ * g * x ∈ borel P) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have hxinv : x⁻¹ ∉ borel P := fun hm => hx (by simpa using (borel P).inv_mem hm)
  have hodd := h.strong.2.2 x⁻¹ hxinv
  have hmem : g ∈ borel P ⊓ conjugate (borel P) x⁻¹ := by
    refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
    rw [mem_conjugate_iff_mul_inv, inv_inv]
    exact hxg
  exact CFSG.Quasithin.RonanF13.eq_one_of_odd_orderOf_of_pow'
    (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hmem)) hk

end CFSG.GH74.Uniqueness.Bender

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)
open CFSG.GH74.Uniqueness.Bender

structure IsCartanQuot (K : Type*) [Group K] : Prop where
  fix_two : ∀ P : Sylow 2 K, ∀ x y : K,
    x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    (∀ d ∈ Subgroup.normalizer ((P : Subgroup K) : Set K),
      x⁻¹ * d * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) →
      y⁻¹ * d * y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) →
    y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ∨
      x⁻¹ * y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)
  two_elt : ∀ P : Sylow 2 K, ∀ x g : K,
    x ∉ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    g ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    x⁻¹ * g * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) →
    ∀ k : ℕ, g ^ 2 ^ k = 1 → g = 1

theorem BenderType.isCartanQuot {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) : IsCartanQuot K where
  fix_two := by
    intro P x y hx hy
    obtain ⟨t, hc⟩ := h.exists_benderCore P
    have hn : 2 ≤ n := by
      rcases h.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, ha, rfl⟩ | ⟨-, -, hn⟩
      · exact hn
      · omega
      · exact hn
    have hq : 3 ≤ 2 ^ n :=
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact hc.mem_borel_or_of_forall hq P.isPGroup' hx hy
  two_elt := by
    intro P x g hx hg hxg k hk
    obtain ⟨t, hc⟩ := (h.exists_benderCore P)
    exact hc.eq_one_of_mem_borel_inf hx hg hxg hk

theorem IsCartanQuot.of_surjective {K K' : Type*} [Group K] [Group K'] [Finite K] (f : K →* K')
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) (h : IsCartanQuot K') : IsCartanQuot K := by
  have hN : ∀ (P : Sylow 2 K) (a : K),
      a ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ↔
        f a ∈ Subgroup.normalizer (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') :=
    fun P a => by
      rw [Sylow.coe_mapSurjective]
      exact ⟨fun ha => Subgroup.le_normalizer_map f ⟨a, ha, rfl⟩,
        fun ha => RonanF13.mem_normalizer_of_central_cover f hker hodd P.isPGroup' ha⟩
  refine ⟨fun P x y hx hy => ?_, fun P x g hx hg hxg k hk => ?_⟩
  · have h1 := h.fix_two (P.mapSurjective hf) (f x) (f y) (fun hx' => hx ((hN P x).mpr hx'))
      (fun d' hd' hxd' => by
        obtain ⟨d, rfl⟩ := hf d'
        have h2 := hy d ((hN P d).mpr hd') ((hN P _).mpr (by simpa [map_mul, map_inv] using hxd'))
        simpa [map_mul, map_inv] using (hN P _).mp h2)
    rcases h1 with h1 | h1
    · exact Or.inl ((hN P y).mpr h1)
    · exact Or.inr ((hN P _).mpr (by simpa [map_mul, map_inv] using h1))
  · have h1 : f g = 1 := h.two_elt (P.mapSurjective hf) (f x) (f g)
      (fun hx' => hx ((hN P x).mpr hx')) ((hN P g).mp hg)
      (by simpa [map_mul, map_inv] using (hN P _).mp hxg) k (by rw [← map_pow, hk, map_one])
    exact RonanF13.eq_one_of_odd_orderOf_of_pow' (hodd g h1) hk

theorem IsCartanQuot.of_mulEquiv {K K' : Type*} [Group K] [Group K'] [Finite K] (e : K ≃* K')
    (h : IsCartanQuot K') : IsCartanQuot K := by
  have hker : ∀ z ∈ e.toMonoidHom.ker, z = 1 := fun z hz => e.injective (by simpa using hz)
  exact IsCartanQuot.of_surjective e.toMonoidHom e.surjective
    (fun z hz => by rw [hker z hz]; exact Subgroup.one_mem _)
    (fun z hz => by rw [hker z hz, orderOf_one]; exact odd_one) h

theorem isCartanQuot_of_listed {K : Type} [Group K] [Finite K]
    (hK : IsRankOneListed K) (hs : ¬ Group.IsSolvable K) : IsCartanQuot K := by
  rcases cases_of_listed_of_not_isSolvable hK hs with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩
  · exact BenderType.isCartanQuot (BenderType.linear n hn e)
  · exact BenderType.isCartanQuot
      (BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    let π : StatedSU 3 (2 ^ n) F →* StatedProj (StatedSU 3 (2 ^ n) F) :=
      QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    haveI : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
    refine IsCartanQuot.of_mulEquiv e (IsCartanQuot.of_surjective π hπ ?_ ?_
      (BenderType.isCartanQuot hB))
    · show π.ker ≤ _
      rw [QuotientGroup.ker_mk']
      exact statedSU_scalars_le_center
    · intro z hz
      rw [QuotientGroup.ker_mk'] at hz
      exact statedSU_three_scalars_odd z hz
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact BenderType.isCartanQuot (hB.of_mulEquiv e.symm)

namespace BenderLocalOf

section CartanLift

variable {G : Type} [Group G] [Finite G] {X T : Subgroup G}
variable (hC : IsCartanQuot (oTwoQuot ↥X)) (hT : IsSylowTwoOf T X)
include hC hT

theorem lift_fix_two {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hxN : x ∉ Subgroup.normalizer (T : Set G))
    (hd : ∀ d ∈ X, d ∈ Subgroup.normalizer (T : Set G) →
      x⁻¹ * d * x ∈ Subgroup.normalizer (T : Set G) →
      y⁻¹ * d * y ∈ Subgroup.normalizer (T : Set G)) :
    y ∈ Subgroup.normalizer (T : Set G) ∨ x⁻¹ * y ∈ Subgroup.normalizer (T : Set G) := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, QuotientGroup.mk' (pCore 2 ↥X) z ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) ↔
        (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  have h1 := hC.fix_two P (QuotientGroup.mk' _ ⟨x, hx⟩) (QuotientGroup.mk' _ ⟨y, hy⟩)
    (fun h => hxN ((hmem _).mp h)) (fun d' hd' hxd' => by
      obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥X) d'
      have h2 : (x : G)⁻¹ * d * x ∈ Subgroup.normalizer (T : Set G) := by
        have h3 := (hmem (⟨x, hx⟩⁻¹ * d * ⟨x, hx⟩)).mp (by simpa [map_mul, map_inv] using hxd')
        simpa using h3
      have h4 := hd d d.2 ((hmem d).mp hd') h2
      have h5 := (hmem (⟨y, hy⟩⁻¹ * d * ⟨y, hy⟩)).mpr (by simpa using h4)
      simpa [map_mul, map_inv] using h5)
  rcases h1 with h1 | h1
  · exact Or.inl ((hmem ⟨y, hy⟩).mp h1)
  · right
    have h2 := (hmem (⟨x, hx⟩⁻¹ * ⟨y, hy⟩)).mp (by simpa [map_mul, map_inv] using h1)
    simpa using h2

theorem lift_two_elt {x g : G} (hx : x ∈ X) (hg : g ∈ X)
    (hxN : x ∉ Subgroup.normalizer (T : Set G)) (hgN : g ∈ Subgroup.normalizer (T : Set G))
    (hxg : x⁻¹ * g * x ∈ Subgroup.normalizer (T : Set G)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ pCoreOf 2 X := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, QuotientGroup.mk' (pCore 2 ↥X) z ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) ↔
        (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  have hk' : (⟨g, hg⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hxg' := (hmem (⟨x, hx⟩⁻¹ * ⟨g, hg⟩ * ⟨x, hx⟩)).mpr (by simpa using hxg)
  have h1 := hC.two_elt P (QuotientGroup.mk' _ ⟨x, hx⟩) (QuotientGroup.mk' _ ⟨g, hg⟩)
    (fun h => hxN ((hmem _).mp h)) ((hmem _).mpr hgN)
    (by simpa [map_mul, map_inv] using hxg') k (by rw [← map_pow, hk', map_one])
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (F1.mem_pCore_iff_coe _).mp h1

end CartanLift

end BenderLocalOf

section Local

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

structure CartanLocal {G₀ G₁ G₂ : Subgroup G} (μ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) :
    Prop where
  fix_two : ∀ δ ∈ nbrs μ, ∀ δ' ∈ nbrs μ, δ ≠ δ' → ∀ ε ∈ nbrs μ,
    L ⊓ stab δ ⊓ stab δ' ≤ stab ε → ε = δ ∨ ε = δ'
  two_elt : ∀ δ ∈ nbrs μ, ∀ δ' ∈ nbrs μ, δ ≠ δ' → ∀ g ∈ L ⊓ stab δ ⊓ stab δ',
    ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ ballStab 1 μ

theorem CartanLocal.smul {G₀ G₁ G₂ : Subgroup G} {μ : CosetGeom G₀ G₁ G₂} {L : Subgroup G}
    (h : CartanLocal μ L) (g : ↥G₀) : CartanLocal (g • μ) (conjSub (g : G) L) where
  fix_two := by
    intro δ hδ δ' hδ' hne ε hε hle
    obtain ⟨d, rfl⟩ : ∃ d, δ = g • d := ⟨g⁻¹ • δ, by simp⟩
    obtain ⟨d', rfl⟩ : ∃ d', δ' = g • d' := ⟨g⁻¹ • δ', by simp⟩
    obtain ⟨c, rfl⟩ : ∃ c, ε = g • c := ⟨g⁻¹ • ε, by simp⟩
    have hd : d ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ
    have hd' : d' ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ'
    have hc : c ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
    rw [CosetGeom.stab_smul, CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf,
      ← conjSub_inf] at hle
    rcases h.fix_two d hd d' hd' (fun h' => hne (by rw [h'])) c hc
        ((conjSub_le_conjSub_iff (g : G)).mp hle) with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])
  two_elt := by
    intro δ hδ δ' hδ' hne x hx k hk
    obtain ⟨d, rfl⟩ : ∃ d, δ = g • d := ⟨g⁻¹ • δ, by simp⟩
    obtain ⟨d', rfl⟩ : ∃ d', δ' = g • d' := ⟨g⁻¹ • δ', by simp⟩
    have hd : d ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ
    have hd' : d' ∈ nbrs μ := (CosetGeom.smul_adj g).mp hδ'
    rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, ← conjSub_inf, mem_conjSub] at hx
    rw [CosetGeom.ballStab_smul, mem_conjSub]
    refine h.two_elt d hd d' hd' (fun h' => hne (by rw [h'])) _ hx k ?_
    have e1 := conj_pow (a := (g : G)⁻¹) (b := x) (i := 2 ^ k)
    rw [inv_inv] at e1
    rw [e1, hk]
    group

end Local

namespace BenderLocalOf

variable {G : Type} [Group G] {L₁ L₂ S Z : Subgroup G} [Finite G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem mem_stab_smul_γ₁_iff (hs : Setting L₁ L₂ S Z) {a : ↥(L₁ ⊔ L₂ ⊔ S)} (ha : (a : G) ∈ L₂)
    {w : G} (hw : w ∈ L₂) :
    w ∈ stab (a • ν₁) ↔
      (a : G)⁻¹ * w * a ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
  rw [CosetGeom.stab_smul, mem_conjSub, stab_γ₁_eq hs]
  exact mem_P₁_iff hs (L₂.mul_mem (L₂.mul_mem (L₂.inv_mem ha) hw) ha)

theorem smul_γ₁_eq_smul_iff (hs : Setting L₁ L₂ S Z) {a c : ↥(L₁ ⊔ L₂ ⊔ S)} (ha : (a : G) ∈ L₂)
    (hc : (c : G) ∈ L₂) :
    a • ν₁ = c • ν₁ ↔
      (a : G)⁻¹ * c ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
  rw [smul_eq_smul_iff_mem_stab, stab_γ₁_eq hs]
  exact mem_P₁_iff hs (L₂.mul_mem (L₂.inv_mem ha) hc)

variable {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂))
include hK hC

theorem cartan_fix_two (hs : Setting L₁ L₂ S Z) {δ δ' ε : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S)
    (P₁ L₁ L₂ S)} (hδ : δ ∈ nbrs ν₀) (hδ' : δ' ∈ nbrs ν₀) (hne : δ ≠ δ') (hε : ε ∈ nbrs ν₀)
    (hle : oddGen L₂ ⊓ stab δ ⊓ stab δ' ≤ stab ε) : ε = δ ∨ ε = δ' := by
  obtain ⟨a, ha, rfl⟩ := exists_smul_γ₁_eq hK hs hδ
  obtain ⟨b, hb, rfl⟩ := exists_smul_γ₁_eq hK hs hδ'
  obtain ⟨c, hc, rfl⟩ := exists_smul_γ₁_eq hK hs hε
  have ha₂ : (a : G) ∈ L₂ := MS93.oddGen_le L₂ ha
  have hb₂ : (b : G) ∈ L₂ := MS93.oddGen_le L₂ hb
  have hc₂ : (c : G) ∈ L₂ := MS93.oddGen_le L₂ hc
  have hab : (a : G)⁻¹ * b ∈ L₂ := L₂.mul_mem (L₂.inv_mem ha₂) hb₂
  have hac : (a : G)⁻¹ * c ∈ L₂ := L₂.mul_mem (L₂.inv_mem ha₂) hc₂
  have hxN : (a : G)⁻¹ * b ∉ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := fun h =>
    hne ((smul_γ₁_eq_smul_iff hs ha₂ hb₂).mpr h)
  have hker : ∀ {o : G}, o ∈ pCoreOf 2 L₂ → ∀ {μ}, μ ∈ nbrs ν₀ → o ∈ stab μ := fun ho _ hμ =>
    CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hμ).le
      (pCoreOf_le_ballStab hs ho)
  have key := lift_fix_two hC (isSylowTwoOf_inf hs) hab hac hxN (fun d hd hdN hbd => by
    set w := (a : G) * d * (a : G)⁻¹ with hw
    have hw₂ : w ∈ L₂ := L₂.mul_mem (L₂.mul_mem ha₂ hd) (L₂.inv_mem ha₂)
    have hwa : w ∈ stab (a • ν₁) := (mem_stab_smul_γ₁_iff hs ha₂ hw₂).mpr (by
      rw [hw]
      simpa [mul_assoc] using hdN)
    have hwb : w ∈ stab (b • ν₁) := (mem_stab_smul_γ₁_iff hs hb₂ hw₂).mpr (by
      have e1 : (b : G)⁻¹ * w * b = ((a : G)⁻¹ * b)⁻¹ * d * ((a : G)⁻¹ * b) := by
        rw [hw]
        group
      rw [e1]
      exact hbd)
    obtain ⟨l, hl, o, ho, hlo⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
      ((MS93.oddGen_le L₂).trans (le_normalizer_pCoreOf 2 L₂))).mp
        (le_oddGen_sup_pCoreOf hK hw₂)
    have hl' : l = w * o⁻¹ := by rw [hlo]; group
    have hlc : l ∈ stab (c • ν₁) := hle ⟨⟨hl, by
      rw [hl']
      exact (stab _).mul_mem hwa ((stab _).inv_mem (hker ho hδ))⟩, by
      rw [hl']
      exact (stab _).mul_mem hwb ((stab _).inv_mem (hker ho hδ'))⟩
    have hwc : w ∈ stab (c • ν₁) := by
      rw [hlo]
      exact (stab _).mul_mem hlc (hker ho hε)
    have h1 := (mem_stab_smul_γ₁_iff hs hc₂ hw₂).mp hwc
    have e2 : ((a : G)⁻¹ * c)⁻¹ * d * ((a : G)⁻¹ * c) = (c : G)⁻¹ * w * c := by
      rw [hw]
      group
    rw [e2]
    exact h1)
  rcases key with h1 | h1
  · exact Or.inl ((smul_γ₁_eq_smul_iff hs ha₂ hc₂).mpr h1).symm
  · right
    refine ((smul_γ₁_eq_smul_iff hs hb₂ hc₂).mpr ?_).symm
    have e3 : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * c) = (b : G)⁻¹ * c := by group
    rw [← e3]
    exact h1

theorem cartan_two_elt (hs : Setting L₁ L₂ S Z) {δ δ' : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S)
    (P₁ L₁ L₂ S)} (hδ : δ ∈ nbrs ν₀) (hδ' : δ' ∈ nbrs ν₀) (hne : δ ≠ δ') {g : G}
    (hg : g ∈ oddGen L₂ ⊓ stab δ ⊓ stab δ') {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ ballStab 1 ν₀ := by
  obtain ⟨a, ha, rfl⟩ := exists_smul_γ₁_eq hK hs hδ
  obtain ⟨b, hb, rfl⟩ := exists_smul_γ₁_eq hK hs hδ'
  have ha₂ : (a : G) ∈ L₂ := MS93.oddGen_le L₂ ha
  have hb₂ : (b : G) ∈ L₂ := MS93.oddGen_le L₂ hb
  have hg₂ : g ∈ L₂ := MS93.oddGen_le L₂ hg.1.1
  have hab : (a : G)⁻¹ * b ∈ L₂ := L₂.mul_mem (L₂.inv_mem ha₂) hb₂
  have hxN : (a : G)⁻¹ * b ∉ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := fun h =>
    hne ((smul_γ₁_eq_smul_iff hs ha₂ hb₂).mpr h)
  have hg'₂ : (a : G)⁻¹ * g * a ∈ L₂ := L₂.mul_mem (L₂.mul_mem (L₂.inv_mem ha₂) hg₂) ha₂
  have hgN := (mem_stab_smul_γ₁_iff hs ha₂ hg₂).mp hg.1.2
  have hbg : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * g * a) * ((a : G)⁻¹ * b) ∈
      Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
    have e1 : ((a : G)⁻¹ * b)⁻¹ * ((a : G)⁻¹ * g * a) * ((a : G)⁻¹ * b) = (b : G)⁻¹ * g * b := by
      group
    rw [e1]
    exact (mem_stab_smul_γ₁_iff hs hb₂ hg₂).mp hg.2
  have hk' : ((a : G)⁻¹ * g * a) ^ 2 ^ k = 1 := by
    have e2 := conj_pow (a := (a : G)⁻¹) (b := g) (i := 2 ^ k)
    rw [inv_inv] at e2
    rw [e2, hk]
    group
  have h1 := lift_two_elt hC (isSylowTwoOf_inf hs) hab hg'₂ hxN hgN hbg hk'
  have h2 : g ∈ pCoreOf 2 L₂ := by
    have h3 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L₂ ha₂) _).mp h1
    simpa [mul_assoc] using h3
  exact pCoreOf_le_ballStab hs h2

end BenderLocalOf

namespace Setting

variable {G : Type} [Group G] {L₁ L₂ S Z : Subgroup G} [Finite G]

open CosetGeom (γ₀)

theorem cartanLocal (hs : Setting L₁ L₂ S Z) {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
    (hC : IsCartanQuot (oTwoQuot ↥L₂)) :
    CartanLocal (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) (oddGen L₂) where
  fix_two := fun _ hδ _ hδ' hne _ hε hle => BenderLocalOf.cartan_fix_two hK hC hs hδ hδ' hne hε hle
  two_elt := fun _ hδ _ hδ' hne _ hg _ hk => BenderLocalOf.cartan_two_elt hK hC hs hδ hδ' hne hg hk

end Setting

end CFSG.Quasithin.F112Crit

end
