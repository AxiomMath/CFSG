module

public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.A4V

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutatorMap_mul {Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z) {y y' : G} (hy : y ∈ Q) (hy' : y' ∈ Q) :
    c * (y * y') * c⁻¹ * (y * y')⁻¹ =
      (c * y * c⁻¹ * y⁻¹) * (c * y' * c⁻¹ * y'⁻¹) := by
  have hcomm : y * (c * y' * c⁻¹ * y'⁻¹) = (c * y' * c⁻¹ * y'⁻¹) * y :=
    (hZc _ (hcZ y' hy') y hy).symm
  calc
    c * (y * y') * c⁻¹ * (y * y')⁻¹
        = (c * y * c⁻¹ * y⁻¹) * (y * (c * y' * c⁻¹ * y'⁻¹)) * y⁻¹ := by group
    _ = (c * y * c⁻¹ * y⁻¹) * ((c * y' * c⁻¹ * y'⁻¹) * y) * y⁻¹ := by rw [hcomm]
    _ = (c * y * c⁻¹ * y⁻¹) * (c * y' * c⁻¹ * y'⁻¹) := by group

private theorem commutatorMap_conj {H Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hcQ : c ∈ Q)
    (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z) {g y : G} (hg : g ∈ H) (hy : y ∈ Q) :
    c * (g * y * g⁻¹) * c⁻¹ * (g * y * g⁻¹)⁻¹ =
      g * (c * y * c⁻¹ * y⁻¹) * g⁻¹ := by
  set z := g * c * g⁻¹ * c⁻¹ with hzdef
  set y' := g * y * g⁻¹ with hy'def
  have hzZ : z ∈ Z := hc g hg
  have hy'Q : y' ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHQ hg) y).mp hy
  have hgc : g * c * g⁻¹ = z * c := by rw [hzdef]; group
  have hzc : z * c = c * z := hZc z hzZ c hcQ
  have hzy : z * y' = y' * z := hZc z hzZ y' hy'Q
  have hzc' : z * c⁻¹ = c⁻¹ * z := hZc z hzZ c⁻¹ (Q.inv_mem hcQ)
  have hmain : g * (c * y * c⁻¹ * y⁻¹) * g⁻¹ =
      c * (g * y * g⁻¹) * c⁻¹ * (g * y * g⁻¹)⁻¹ := by
    calc
      g * (c * y * c⁻¹ * y⁻¹) * g⁻¹
          = (g * c * g⁻¹) * y' * (g * c * g⁻¹)⁻¹ * y'⁻¹ := by
              rw [hy'def]; group
      _ = (z * c) * y' * (z * c)⁻¹ * y'⁻¹ := by rw [hgc]
      _ = z * c * y' * c⁻¹ * z⁻¹ * y'⁻¹ := by group
      _ = c * z * y' * c⁻¹ * z⁻¹ * y'⁻¹ := by rw [hzc]
      _ = c * (z * y') * c⁻¹ * z⁻¹ * y'⁻¹ := by group
      _ = c * (y' * z) * c⁻¹ * z⁻¹ * y'⁻¹ := by rw [hzy]
      _ = c * y' * z * c⁻¹ * z⁻¹ * y'⁻¹ := by group
      _ = c * y' * (z * c⁻¹) * z⁻¹ * y'⁻¹ := by group
      _ = c * y' * (c⁻¹ * z) * z⁻¹ * y'⁻¹ := by rw [hzc']
      _ = c * y' * c⁻¹ * z * z⁻¹ * y'⁻¹ := by group
      _ = c * y' * c⁻¹ * y'⁻¹ := by group
  exact hmain.symm

private theorem commutatorMap_mem_of_fixed {H Q Z : Subgroup G} {c : G}
    (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z) (hQH : Q ≤ H) {y : G} (hy : y ∈ Q) :
    c * y * c⁻¹ * y⁻¹ ∈ Z := by
  have h := Z.inv_mem (hc y (hQH hy))
  rwa [show (y * c * y⁻¹ * c⁻¹)⁻¹ = c * y * c⁻¹ * y⁻¹ by group] at h

private def commutatorMapHom {Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z) : ↥Q →* G where
  toFun y := c * (y : G) * c⁻¹ * (y : G)⁻¹
  map_one' := by simp
  map_mul' y y' := commutatorMap_mul hZc hcZ y.2 y'.2

private theorem commutatorMapHom_eq_one_iff_mem_centralizer {Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z) {y : G} (hy : y ∈ Q) :
    commutatorMapHom hZc hcZ ⟨y, hy⟩ = 1 ↔
      y ∈ Subgroup.centralizer ({c} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  change c * y * c⁻¹ * y⁻¹ = 1 ↔ y * c = c * y
  constructor
  · intro h
    have h' : c * y = y * c := by
      have := congrArg (fun t => t * (y * c)) h
      simpa [mul_assoc] using this
    exact h'.symm
  · intro h
    rw [← h]
    group

private theorem commutatorMapHom_eq_of_mem_centralizer {Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (hab : a * b⁻¹ ∈ Q ⊓ Subgroup.centralizer ({c} : Set G)) :
    commutatorMapHom hZc hcZ ⟨a, ha⟩ = commutatorMapHom hZc hcZ ⟨b, hb⟩ := by
  have hk : commutatorMapHom hZc hcZ ⟨a * b⁻¹, hab.1⟩ = 1 :=
    (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hab.1).mpr hab.2
  have hprod : commutatorMapHom hZc hcZ ⟨a, ha⟩ *
      (commutatorMapHom hZc hcZ ⟨b, hb⟩)⁻¹ = 1 := by
    have hsub : (⟨a * b⁻¹, hab.1⟩ : ↥Q) = ⟨a, ha⟩ * ⟨b, hb⟩⁻¹ := rfl
    have h2 : commutatorMapHom hZc hcZ (⟨a, ha⟩ * ⟨b, hb⟩⁻¹) = 1 := by
      rw [← hsub]
      exact hk
    simpa [map_mul, map_inv] using h2
  exact mul_inv_eq_one.mp hprod

private theorem isNormalIn_centralizer {H Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hQH : Q ≤ H)
    (hcQ : c ∈ Q) (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z) :
    IsNormalIn H Q (Q ⊓ Subgroup.centralizer ({c} : Set G)) := by
  refine ⟨inf_le_left, ?_⟩
  intro g hg x hx
  have hxQ : x ∈ Q := hx.1
  have hxc : c * x = x * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hHQ hg) x).mp hxQ, ?_⟩
  have hconj := commutatorMap_conj hZc hHQ hcQ hc hg hxQ
  have hx1 : c * x * c⁻¹ * x⁻¹ = 1 := by
    rw [hxc]
    group
  rw [hx1] at hconj
  have hconj1 : c * (g * x * g⁻¹) * c⁻¹ * (g * x * g⁻¹)⁻¹ = 1 := by
    simpa using hconj
  have hcomm : c * (g * x * g⁻¹) = (g * x * g⁻¹) * c := by
    have := congrArg (fun t => t * ((g * x * g⁻¹) * c)) hconj1
    simpa [mul_assoc] using this
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm

private def commutatorModHom (K Q T Z : Subgroup G) {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z) :
    ↥(centralizerMod K Q T) →* G where
  toFun y := c * (y : G) * c⁻¹ * (y : G)⁻¹
  map_one' := by simp
  map_mul' y y' := commutatorMap_mul hZc hcZ
    (centralizerMod_le_left K Q T y.2) (centralizerMod_le_left K Q T y'.2)

theorem exists_commutator_eq_of_minimal {H Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hQH : Q ≤ H)
    (hstep : IsChiefStep H Q ⊥ Z) (hcQ : c ∈ Q) (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z)
    (hne : ∃ y ∈ Q, c * y ≠ y * c) :
    ∀ z ∈ Z, ∃ y ∈ Q, c * y * c⁻¹ * y⁻¹ = z := by
  have hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z :=
    fun y hy => commutatorMap_mem_of_fixed hc hQH hy
  let φ := commutatorMapHom hZc hcZ
  have hIle : φ.range ≤ Z := by
    rintro u ⟨y, rfl⟩
    exact hcZ y y.2
  have hInorm : IsNormalIn H Q φ.range := by
    refine ⟨hIle.trans hstep.1.1, ?_⟩
    intro g hg u hu
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hu
    have hgyQ : g * (y : G) * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHQ hg) (y : G)).mp y.2
    refine MonoidHom.mem_range.mpr ⟨⟨g * (y : G) * g⁻¹, hgyQ⟩, ?_⟩
    exact commutatorMap_conj hZc hHQ hcQ hc hg y.2
  rcases hstep.2.2.2 φ.range hInorm bot_le hIle with hbot | htop
  · exfalso
    obtain ⟨y, hyQ, hcy⟩ := hne
    have hφne : φ ⟨y, hyQ⟩ ≠ 1 := by
      intro h1
      have hcy' : y ∈ Subgroup.centralizer ({c} : Set G) :=
        (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hyQ).mp h1
      exact hcy (Subgroup.mem_centralizer_singleton_iff.mp hcy').symm
    have hφmem : φ ⟨y, hyQ⟩ ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact MonoidHom.mem_range.mpr ⟨⟨y, hyQ⟩, rfl⟩
    exact hφne (Subgroup.mem_bot.mp hφmem)
  · intro z hz
    have hzrange : z ∈ φ.range := by
      rw [htop]
      exact hz
    obtain ⟨y, hyz⟩ := MonoidHom.mem_range.mp hzrange
    exact ⟨(y : G), y.2, hyz⟩

theorem isChiefStep_centralizer_of_commutatorMap {H Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hQH : Q ≤ H)
    (hstep : IsChiefStep H Q ⊥ Z) (hnc : ¬ IsCentralStep H ⊥ Z) (hcQ : c ∈ Q)
    (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z)
    (hsurj : ∀ z ∈ Z, ∃ y ∈ Q, c * y * c⁻¹ * y⁻¹ = z) :
    IsChiefStep H Q (Q ⊓ Subgroup.centralizer ({c} : Set G)) Q ∧
      ¬ IsCentralStep H (Q ⊓ Subgroup.centralizer ({c} : Set G)) Q := by
  have hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z :=
    fun y hy => commutatorMap_mem_of_fixed hc hQH hy
  let φ := commutatorMapHom hZc hcZ
  let K : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G)
  change IsChiefStep H Q K Q ∧ ¬ IsCentralStep H K Q
  have hKQ : K ≤ Q := inf_le_left
  have hKn : IsNormalIn H Q K := isNormalIn_centralizer hZc hHQ hQH hcQ hc
  have hKlt : K < Q := by
    refine lt_of_le_of_ne hKQ ?_
    intro hKQeq
    have hZne : Z ≠ ⊥ := hstep.2.2.1.ne'
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨y, hyQ, hφy⟩ := hsurj z hzZ
    have hφy' : φ ⟨y, hyQ⟩ = z := hφy
    have hφne : φ ⟨y, hyQ⟩ ≠ 1 := by
      rw [hφy']
      exact hz1'
    have hyNotK : y ∉ K := by
      intro hyK
      exact hφne ((commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hyQ).mpr hyK.2)
    exact hyNotK (hKQeq.symm ▸ hyQ)
  have hmax : ∀ K' : Subgroup G, IsNormalIn H Q K' → K ≤ K' → K' ≤ Q →
      K' = K ∨ K' = Q := by
    intro K' hK'n hKK' hK'Q
    let J : Subgroup G := (K'.subgroupOf Q).map φ
    have hJleZ : J ≤ Z := by
      intro u hu
      rcases Subgroup.mem_map.mp hu with ⟨y, -, rfl⟩
      exact hcZ (y : G) y.2
    have hJn : IsNormalIn H Q J := by
      refine ⟨hJleZ.trans hstep.1.1, ?_⟩
      intro g hg u hu
      rcases Subgroup.mem_map.mp hu with ⟨y, hy, rfl⟩
      have hyK' : (y : G) ∈ K' := Subgroup.mem_subgroupOf.mp hy
      have hgyQ : g * (y : G) * g⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hHQ hg) (y : G)).mp y.2
      have hgyK' : g * (y : G) * g⁻¹ ∈ K' := hK'n.2 g hg (y : G) hyK'
      refine Subgroup.mem_map.mpr
        ⟨⟨g * (y : G) * g⁻¹, hgyQ⟩, Subgroup.mem_subgroupOf.mpr hgyK', ?_⟩
      exact commutatorMap_conj hZc hHQ hcQ hc hg y.2
    rcases hstep.2.2.2 J hJn bot_le hJleZ with hJbot | hJZ
    · left
      refine le_antisymm ?_ hKK'
      intro x hxK'
      have hxQ : x ∈ Q := hK'Q hxK'
      have hxJ : φ ⟨x, hxQ⟩ ∈ J :=
        Subgroup.mem_map.mpr
          ⟨⟨x, hxQ⟩, Subgroup.mem_subgroupOf.mpr hxK', rfl⟩
      rw [hJbot, Subgroup.mem_bot] at hxJ
      exact ⟨hxQ, (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hxQ).mp hxJ⟩
    · right
      refine le_antisymm hK'Q ?_
      intro x hxQ
      have hxJ : φ ⟨x, hxQ⟩ ∈ J := by
        rw [hJZ]
        exact hcZ x hxQ
      rcases Subgroup.mem_map.mp hxJ with ⟨k', hk'mem, hk'eq⟩
      have hk'K' : (k' : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk'mem
      have hk'Q : (k' : G) ∈ Q := k'.2
      have hkK : (k' : G)⁻¹ * x ∈ K := by
        have hxinvQ : (k' : G)⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hk'Q) hxQ
        refine ⟨hxinvQ, ?_⟩
        have hφ1 : φ ⟨(k' : G)⁻¹ * x, hxinvQ⟩ = 1 := by
          have hsub : (⟨(k' : G)⁻¹ * x, hxinvQ⟩ : ↥Q) =
              (⟨k', hk'Q⟩ : ↥Q)⁻¹ * ⟨x, hxQ⟩ := rfl
          rw [hsub, map_mul, map_inv, hk'eq]
          group
        exact (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hxinvQ).mp hφ1
      have hxK' : (k' : G) * ((k' : G)⁻¹ * x) ∈ K' :=
        K'.mul_mem hk'K' (hKK' hkK)
      simpa [mul_assoc] using hxK'
  refine ⟨⟨?_, hKn, hKlt, hmax⟩, ?_⟩
  ·
    refine ⟨le_refl Q, ?_⟩
    intro g hg x hx
    exact (Subgroup.mem_normalizer_iff.mp (hHQ hg) x).mp hx
  ·
    intro hcent
    apply hnc
    intro g hg z hz
    obtain ⟨y, hyQ, hφy⟩ := hsurj z hz
    have hφy' : φ ⟨y, hyQ⟩ = z := hφy
    have hgyQ : g * y * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHQ hg) y).mp hyQ
    have hk : g * y * g⁻¹ * y⁻¹ ∈ K := hcent g hg y hyQ
    have hφk : φ ⟨g * y * g⁻¹ * y⁻¹, Q.mul_mem hgyQ (Q.inv_mem hyQ)⟩ = 1 :=
      (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ
        (Q.mul_mem hgyQ (Q.inv_mem hyQ))).mpr hk.2
    have h1 : φ ⟨g * y * g⁻¹, hgyQ⟩ = φ ⟨y, hyQ⟩ := by
      have hsub : (⟨g * y * g⁻¹ * y⁻¹, Q.mul_mem hgyQ (Q.inv_mem hyQ)⟩ : ↥Q) =
          ⟨g * y * g⁻¹, hgyQ⟩ * ⟨y, hyQ⟩⁻¹ := rfl
      have hprod : φ (⟨g * y * g⁻¹, hgyQ⟩ * ⟨y, hyQ⟩⁻¹) = 1 := by
        rw [← hsub]
        exact hφk
      have h' : φ ⟨g * y * g⁻¹, hgyQ⟩ * (φ ⟨y, hyQ⟩)⁻¹ = 1 := by
        simpa [map_mul, map_inv] using hprod
      exact mul_inv_eq_one.mp h'
    have h2 : φ ⟨g * y * g⁻¹, hgyQ⟩ = g * φ ⟨y, hyQ⟩ * g⁻¹ :=
      commutatorMap_conj hZc hHQ hcQ hc hg hyQ
    have hgz : g * z * g⁻¹ = z := by
      calc
        g * z * g⁻¹ = g * φ ⟨y, hyQ⟩ * g⁻¹ := by rw [← hφy']
        _ = φ ⟨g * y * g⁻¹, hgyQ⟩ := h2.symm
        _ = φ ⟨y, hyQ⟩ := h1
        _ = z := hφy'
    rw [Subgroup.mem_bot]
    rw [hgz]
    group

theorem relIndex_centralizerMod_centralizer_eq_card {H Q Z T : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hQH : Q ≤ H) (hTH : T ≤ H) (hcQ : c ∈ Q)
    (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z)
    (hsurj : ∀ z ∈ Z, ∃ y ∈ Q, c * y * c⁻¹ * y⁻¹ = z) :
    (Q ⊓ Subgroup.centralizer ({c} : Set G)).relIndex
        (centralizerMod (Q ⊓ Subgroup.centralizer ({c} : Set G)) Q T) =
      Nat.card ↥(Z ⊓ Subgroup.centralizer (T : Set G)) := by
  have hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z :=
    fun y hy => commutatorMap_mem_of_fixed hc hQH hy
  let K : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G)
  let C : Subgroup G := centralizerMod K Q T
  change K.relIndex C = Nat.card ↥(Z ⊓ Subgroup.centralizer (T : Set G))
  have hKn : IsNormalIn H Q K := isNormalIn_centralizer hZc hHQ hQH hcQ hc
  have hNK : H ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (fun x hx => hKn.2 g hg x hx)
      (fun x hx => by simpa using hKn.2 g⁻¹ (H.inv_mem hg) x hx)
  have hKC : K ≤ C := by
    intro k hk
    refine ⟨hk.1, hNK (hQH hk.1), ?_⟩
    intro t ht
    have htH : t ∈ H := hTH ht
    have h1 : t * k * t⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hNK htH) k).mp hk
    have h2 : t * k * t⁻¹ * k⁻¹ ∈ K := K.mul_mem h1 (K.inv_mem hk)
    have h3 : k * t * k⁻¹ * t⁻¹ = (t * k * t⁻¹ * k⁻¹)⁻¹ := by group
    rw [h3]
    exact K.inv_mem h2
  let ψ := commutatorModHom K Q T Z hZc hcZ
  have hψker : ψ.ker = K.subgroupOf C := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hyQ : (y : G) ∈ Q := centralizerMod_le_left K Q T y.2
      change commutatorMapHom hZc hcZ ⟨(y : G), hyQ⟩ = 1 at h
      exact ⟨hyQ, (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hyQ).mp h⟩
    · intro h
      have hyQ : (y : G) ∈ Q := centralizerMod_le_left K Q T y.2
      change commutatorMapHom hZc hcZ ⟨(y : G), hyQ⟩ = 1
      exact (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hyQ).mpr h.2
  have hψrange : ψ.range = Z ⊓ Subgroup.centralizer (T : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro u ⟨y, rfl⟩
      have hyQ : (y : G) ∈ Q := centralizerMod_le_left K Q T y.2
      change c * (y : G) * c⁻¹ * (y : G)⁻¹ ∈ Z ⊓ Subgroup.centralizer (T : Set G)
      refine ⟨hcZ (y : G) hyQ, ?_⟩
      change c * (y : G) * c⁻¹ * (y : G)⁻¹ ∈ Subgroup.centralizer (T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have htH : t ∈ H := hTH ht
      have htyQ : t * (y : G) * t⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hHQ htH) (y : G)).mp hyQ
      have hab : t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ K := by
        have hcomm : (y : G) * t * (y : G)⁻¹ * t⁻¹ ∈ K := y.2.2.2 t ht
        have h3 : t * (y : G) * t⁻¹ * (y : G)⁻¹ =
            ((y : G) * t * (y : G)⁻¹ * t⁻¹)⁻¹ := by group
        rw [h3]
        exact K.inv_mem hcomm
      have hφeq := commutatorMapHom_eq_of_mem_centralizer hZc hcZ htyQ hyQ hab
      have hH2 := commutatorMap_conj hZc hHQ hcQ hc htH hyQ
      have htu : t * (c * (y : G) * c⁻¹ * (y : G)⁻¹) * t⁻¹ =
          c * (y : G) * c⁻¹ * (y : G)⁻¹ := by
        rw [← hH2]
        exact hφeq
      calc
        t * (c * (y : G) * c⁻¹ * (y : G)⁻¹)
            = (t * (c * (y : G) * c⁻¹ * (y : G)⁻¹) * t⁻¹) * t := by group
        _ = (c * (y : G) * c⁻¹ * (y : G)⁻¹) * t := by rw [htu]
    · rintro z ⟨hzZ, hzT⟩
      obtain ⟨y, hyQ, hφy⟩ := hsurj z hzZ
      have hφy' : commutatorMapHom hZc hcZ ⟨(y : G), hyQ⟩ = z := hφy
      have hyN : (y : G) ∈ Subgroup.normalizer (K : Set G) := hNK (hQH hyQ)
      have hyC : y ∈ C := by
        refine ⟨hyQ, hyN, ?_⟩
        intro t ht
        have htH : t ∈ H := hTH ht
        have htyQ : t * (y : G) * t⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hHQ htH) (y : G)).mp hyQ
        have hφeq : commutatorMapHom hZc hcZ ⟨t * (y : G) * t⁻¹, htyQ⟩ =
            commutatorMapHom hZc hcZ ⟨(y : G), hyQ⟩ := by
          have hH2 := commutatorMap_conj hZc hHQ hcQ hc htH hyQ
          have hcz : t * z = z * t := Subgroup.mem_centralizer_iff.mp hzT t ht
          calc
            commutatorMapHom hZc hcZ ⟨t * (y : G) * t⁻¹, htyQ⟩
                = t * (commutatorMapHom hZc hcZ ⟨(y : G), hyQ⟩) * t⁻¹ := hH2
            _ = t * z * t⁻¹ := by rw [hφy']
            _ = z := by rw [hcz]; group
            _ = commutatorMapHom hZc hcZ ⟨(y : G), hyQ⟩ := hφy'.symm
        have hk : t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ K := by
          have hABQ : t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ Q :=
            Q.mul_mem htyQ (Q.inv_mem hyQ)
          refine ⟨hABQ, ?_⟩
          have hφ1 : commutatorMapHom hZc hcZ
              ⟨t * (y : G) * t⁻¹ * (y : G)⁻¹, hABQ⟩ = 1 := by
            have hsub : (⟨t * (y : G) * t⁻¹ * (y : G)⁻¹, hABQ⟩ : ↥Q) =
                ⟨t * (y : G) * t⁻¹, htyQ⟩ * ⟨(y : G), hyQ⟩⁻¹ := rfl
            rw [hsub, map_mul, map_inv, hφeq]
            group
          exact (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hABQ).mp hφ1
        have h3 : (y : G) * t * (y : G)⁻¹ * t⁻¹ =
            (t * (y : G) * t⁻¹ * (y : G)⁻¹)⁻¹ := by group
        rw [h3]
        exact K.inv_mem hk
      refine ⟨⟨(y : G), hyC⟩, ?_⟩
      change c * (y : G) * c⁻¹ * (y : G)⁻¹ = z
      exact hφy
  have hKrel : K.relIndex C = ψ.ker.relIndex ⊤ := by
    have h1 : K.relIndex C = (K.subgroupOf C).index := rfl
    have h2 : (K.subgroupOf C).index = ψ.ker.index := by rw [hψker]
    have h3 : ψ.ker.index = ψ.ker.relIndex ⊤ :=
      (Subgroup.relIndex_top_right ψ.ker).symm
    exact h1.trans (h2.trans h3)
  calc
    K.relIndex C = ψ.ker.relIndex ⊤ := hKrel
    _ = Nat.card ((⊤ : Subgroup ↥C).map ψ) := Subgroup.relIndex_ker ⊤ ψ
    _ = Nat.card ψ.range := by rw [Subgroup.map_top]
    _ = Nat.card ↥(Z ⊓ Subgroup.centralizer (T : Set G)) := by rw [hψrange]

theorem mem_omegaOneCenterOf_of_central_fixed {H Q : Subgroup G} {c : G} (hQ : IsPGroup 2 Q)
    (hCH : omegaOneCenterOf Q ⊓ Subgroup.centralizer (H : Set G) = ⊥) (hcQ : c ∈ Q)
    (hcc : ∀ y ∈ Q, c * y = y * c)
    (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ omegaOneCenterOf Q) :
    c ∈ omegaOneCenterOf Q := by
  have hc2Q : c ^ 2 ∈ Q := Q.pow_mem hcQ 2
  have hc2center : c ^ 2 ∈ centerOf Q := by
    refine ⟨hc2Q, ?_⟩
    change c ^ 2 ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc
      y * c ^ 2 = (y * c) * c := by rw [pow_two]; group
      _ = (c * y) * c := by rw [← hcc y hy]
      _ = c * (y * c) := by group
      _ = c * (c * y) := by rw [← hcc y hy]
      _ = c ^ 2 * y := by rw [pow_two]; group
  have hccenter : c ∈ centerOf Q := by
    refine ⟨hcQ, ?_⟩
    change c ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcc y hy).symm
  have hc2centH : c ^ 2 ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    set z := g * c * g⁻¹ * c⁻¹ with hzdef
    have hzΩ : z ∈ omegaOneCenterOf Q := hc g hg
    have hz2 : z ^ 2 = 1 := A4.sq_eq_one_of_mem_omegaOneCenterOf hzΩ
    have hzc : z * c = c * z :=
      ((Subgroup.mem_centralizer_iff.mp (A4.omegaOneCenterOf_le_centerOf Q hzΩ).2) c hcQ).symm
    have hgc : g * c * g⁻¹ = z * c := by rw [hzdef]; group
    have hconj : g * c ^ 2 * g⁻¹ = c ^ 2 := by
      calc
        g * c ^ 2 * g⁻¹ = (g * c * g⁻¹) * (g * c * g⁻¹) := by
          rw [pow_two]; group
        _ = (z * c) * (z * c) := by rw [hgc]
        _ = z * (c * z) * c := by group
        _ = z * (z * c) * c := by rw [← hzc]
        _ = z ^ 2 * c ^ 2 := by rw [pow_two, pow_two]; group
        _ = c ^ 2 := by rw [hz2, one_mul]
    calc
      g * c ^ 2 = (g * c ^ 2 * g⁻¹) * g := by group
      _ = c ^ 2 * g := by rw [hconj]
  have hc2eq1 : c ^ 2 = 1 := by
    by_contra hc2ne
    let T : Subgroup G := Subgroup.zpowers (c ^ 2)
    have hTp : IsPGroup 2 T := hQ.to_le (Subgroup.zpowers_le.mpr hc2Q)
    have hTne : T ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hc2ne
    have h2dvd : 2 ∣ Nat.card ↥T := by
      rcases hTp.card_eq_or_dvd with h1 | h2
      · exact absurd (Subgroup.eq_bot_of_card_eq T h1) hTne
      · exact h2
    obtain ⟨d, hdord⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 h2dvd
    have hdcenter : (d : G) ∈ centerOf Q := (Subgroup.zpowers_le.mpr hc2center) d.2
    have hdcentH : (d : G) ∈ Subgroup.centralizer (H : Set G) :=
      (Subgroup.zpowers_le.mpr hc2centH) d.2
    have hdordG : orderOf (d : G) = 2 := by
      rwa [Subgroup.orderOf_coe]
    have hd2 : (d : G) ^ 2 = 1 := by
      rw [← hdordG]
      exact pow_orderOf_eq_one (d : G)
    have hd1 : (d : G) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hdordG
      exact absurd hdordG (by norm_num)
    have hmem : (d : G) ∈ omegaOneCenterOf Q ⊓ Subgroup.centralizer (H : Set G) :=
      ⟨Subgroup.subset_closure ⟨hdcenter, hd2⟩, hdcentH⟩
    rw [hCH, Subgroup.mem_bot] at hmem
    exact hd1 hmem
  exact Subgroup.subset_closure ⟨hccenter, hc2eq1⟩

end CFSG.Quasithin.Stroth
