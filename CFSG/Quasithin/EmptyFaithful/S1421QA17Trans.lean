module

public import CFSG.Quasithin.EmptyFaithful.S1421QA17Transfer
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421QA17

section Transport

variable {G : Type} [Group G] {Mc : Subgroup G} {Y : Type} [Group Y] {ψ : ↥Mc →* Y}

theorem mem_map_subgroupOf {A : Subgroup G} {y : Y} :
    y ∈ (A.subgroupOf Mc).map ψ ↔ ∃ x : ↥Mc, (x : G) ∈ A ∧ ψ x = y := by
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_map_subgroupOf (hψ : Function.Injective ψ) {A : Subgroup G} (hA : A ≤ Mc) :
    Nat.card ((A.subgroupOf Mc).map ψ) = Nat.card A := by
  rw [Subgroup.card_map_of_injective hψ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv

theorem map_subgroupOf_inf (hψ : Function.Injective ψ) (A B : Subgroup G) :
    ((A ⊓ B).subgroupOf Mc).map ψ = (A.subgroupOf Mc).map ψ ⊓ (B.subgroupOf Mc).map ψ := by
  have h : (A ⊓ B).subgroupOf Mc = A.subgroupOf Mc ⊓ B.subgroupOf Mc :=
    Subgroup.comap_inf _ _ _
  rw [h, Subgroup.map_inf _ _ ψ hψ]

theorem map_subgroupOf_centralizer (hψ : Function.Injective ψ) (A : Subgroup G) (j : ↥Mc) :
    ((A ⊓ Subgroup.centralizer ({(j : G)} : Set G)).subgroupOf Mc).map ψ =
      (A.subgroupOf Mc).map ψ ⊓ Subgroup.centralizer ({ψ j} : Set Y) := by
  ext y
  rw [Subgroup.mem_inf, mem_map_subgroupOf, mem_map_subgroupOf]
  constructor
  · rintro ⟨x, ⟨hxA, hxc⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxj : x * j = j * x := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxc)
    rw [← map_mul, ← map_mul, hxj]
  · rintro ⟨⟨x, hxA, rfl⟩, hc⟩
    refine ⟨x, ⟨hxA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hψ h1)

@[expose] noncomputable def equivMapSubgroupOf (hψ : Function.Injective ψ) {A : Subgroup G}
    (hA : A ≤ Mc) : ↥A ≃* ↥((A.subgroupOf Mc).map ψ) :=
  (Subgroup.subgroupOfEquivOfLe hA).symm.trans ((A.subgroupOf Mc).equivMapOfInjective ψ hψ)

variable [Finite G] [IsSimpleGroup G]

theorem false_of_residual (hR : AutJ2OuterInvolution) (hnc : ∃ a b : G, a * b ≠ b * a)
    {K1 T : Subgroup G} {z : G} (hY : Nonempty (Y ≃* MulAut quasithinJ2))
    (hψ : Function.Injective ψ) (hTM : T ≤ Mc) (hK1M : K1 ≤ Mc) (hTS : IsSylowTwoOf T ⊤)
    (hzT : z ∈ T) (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzc : ∀ t ∈ T, t * z = z * t)
    (hMz : Subgroup.centralizer ({z} : Set G) = Mc)
    (hK1p : ⁅K1, K1⁆ = K1) (hcard : Nat.card T = 2 * Nat.card ↥(T ⊓ K1))
    (hYS : IsSylowTwoOf ((T.subgroupOf Mc).map ψ) ⊤) : False := by
  obtain ⟨e⟩ := hY
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  set TY := (T.subgroupOf Mc).map ψ with hTYdef
  set N := (K1.subgroupOf Mc).map ψ with hNdef
  have hK1pMc : ⁅K1.subgroupOf Mc, K1.subgroupOf Mc⁆ = K1.subgroupOf Mc := by
    have h1 : (⁅K1.subgroupOf Mc, K1.subgroupOf Mc⁆).map Mc.subtype = K1 := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK1M, hK1p]
    have h2 : (K1.subgroupOf Mc).map Mc.subtype = K1 := Subgroup.map_subgroupOf_eq_of_le hK1M
    exact Subgroup.map_injective Mc.subtype_injective (h1.trans h2.symm)
  have hNperf : ⁅N, N⁆ = N := by
    rw [hNdef, ← Subgroup.map_commutator, hK1pMc]
  have hTYcard : Nat.card TY = Nat.card T := card_map_subgroupOf hψ hTM
  have hTYN : TY ⊓ N = ((T ⊓ K1).subgroupOf Mc).map ψ := (map_subgroupOf_inf hψ T K1).symm
  have hNcard : Nat.card TY = 2 * Nat.card ↥(TY ⊓ N) := by
    rw [hTYN, card_map_subgroupOf hψ (inf_le_left.trans hTM), hTYcard]
    exact hcard
  obtain ⟨jY, hjYT, hjYN, hjY2, hjY32, hZ, hP, hNE⟩ := hR Y TY N ⟨e⟩ hYS hNperf hNcard
  obtain ⟨j', hj'T, hj'⟩ := mem_map_subgroupOf.mp hjYT
  have hjT : (j' : G) ∈ T := hj'T
  have hjU : (j' : G) ∉ T ⊓ K1 := fun h => hjYN (hj' ▸ mem_map_subgroupOf.mpr ⟨j', h.2, rfl⟩)
  have hj2 : (j' : G) ^ 2 = 1 := by
    have : ψ (j' ^ 2) = ψ 1 := by rw [map_pow, hj', hjY2, map_one]
    simpa using congrArg Subtype.val (hψ this)
  set C := T ⊓ Subgroup.centralizer ({(j' : G)} : Set G) with hC
  have hCM : C ≤ Mc := inf_le_left.trans hTM
  have hCY : (C.subgroupOf Mc).map ψ = TY ⊓ Subgroup.centralizer ({jY} : Set Y) := by
    rw [hC, map_subgroupOf_centralizer hψ T j', hj']
  have hC32 : Nat.card C = 32 := by
    rw [← card_map_subgroupOf hψ hCM, hCY]
    exact hjY32
  have hzMc : z ∈ Mc := hTM hzT
  set z' : ↥Mc := ⟨z, hzMc⟩ with hz'
  have hwT : ψ z' ∈ TY := mem_map_subgroupOf.mpr ⟨z', hzT, rfl⟩
  have hwc : ∀ t ∈ TY, t * ψ z' = ψ z' * t := by
    intro t ht
    obtain ⟨x, hxT, rfl⟩ := mem_map_subgroupOf.mp ht
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hzc x hxT))
  have hw1 : ψ z' ≠ 1 := fun h => hz1 (by
    have : z' = 1 := hψ (h.trans (map_one ψ).symm)
    simpa [hz'] using congrArg Subtype.val this)
  obtain ⟨⟨yY, hyY, hyY2⟩, hZ2⟩ := hZ (ψ z') hwT hwc hw1
  obtain ⟨y', hy'C, rfl⟩ := mem_map_subgroupOf.mp (hCY ▸ hyY)
  have hzy : (y' : G) ^ 2 = z := by
    have : ψ (y' ^ 2) = ψ z' := by rw [map_pow, hyY2]
    simpa [hz'] using congrArg Subtype.val (hψ this)
  have hzC : z ∈ C := ⟨hzT, Subgroup.mem_centralizer_singleton_iff.mpr (hzc _ hjT).symm⟩
  have hN : ∀ g ∈ Subgroup.normalizer (C : Set G), g * z = z * g := by
    intro g hg
    have hxC : g * z * g⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hg z).mp hzC
    have hyC : g * (y' : G) * g⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hg y').mp hy'C
    have hx2 : (g * z * g⁻¹) ^ 2 = 1 := by
      calc (g * z * g⁻¹) ^ 2 = g * (z * z) * g⁻¹ := by rw [sq]; group
        _ = 1 := by rw [hz2]; group
    have hxsq : (g * (y' : G) * g⁻¹) ^ 2 = g * z * g⁻¹ := by
      rw [conj_pow, hzy]
    have hxM : g * z * g⁻¹ ∈ Mc := hCM hxC
    have hyM : g * (y' : G) * g⁻¹ ∈ Mc := hCM hyC
    have hxY : ψ ⟨g * z * g⁻¹, hxM⟩ ∈ TY ⊓ Subgroup.centralizer ({jY} : Set Y) :=
      hCY ▸ mem_map_subgroupOf.mpr ⟨_, hxC, rfl⟩
    have hyY' : ψ ⟨g * (y' : G) * g⁻¹, hyM⟩ ∈ TY ⊓ Subgroup.centralizer ({jY} : Set Y) :=
      hCY ▸ mem_map_subgroupOf.mpr ⟨_, hyC, rfl⟩
    have hx2Y : ψ ⟨g * z * g⁻¹, hxM⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨g * z * g⁻¹, hxM⟩ : ↥Mc) ^ 2 = 1 from Subtype.ext hx2, map_one]
    have hsqY : ψ ⟨g * (y' : G) * g⁻¹, hyM⟩ ^ 2 = ψ ⟨g * z * g⁻¹, hxM⟩ := by
      rw [← map_pow]
      exact congrArg ψ (Subtype.ext hxsq)
    rcases hZ2 _ hxY hx2Y ⟨_, hyY', hsqY⟩ with h1 | h1
    · exfalso
      have : (⟨g * z * g⁻¹, hxM⟩ : ↥Mc) = 1 := hψ (h1.trans (map_one ψ).symm)
      have h2 : g * z * g⁻¹ = 1 := congrArg Subtype.val this
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · have : (⟨g * z * g⁻¹, hxM⟩ : ↥Mc) = z' := hψ h1
      have h2 : g * z * g⁻¹ = z := congrArg Subtype.val this
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [h2]
  have hS : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({(j' : G)} : Set G) →
      P ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 2 P → C ≤ P → P ≤ C := by
    intro P hPj hPz hP2 hCP
    have hPM : P ≤ Mc := hMz ▸ hPz
    have hP2' : IsPGroup 2 (P.subgroupOf Mc) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
    have hle : (P.subgroupOf Mc).map ψ ≤ Subgroup.centralizer ({jY} : Set Y) := by
      rintro _ ⟨x, hx, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← hj', ← map_mul, ← map_mul]
      refine congrArg ψ (Subtype.ext ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPj hx)
    have h32 := hP _ hle (hP2'.map ψ)
    rw [card_map_subgroupOf hψ hPM] at h32
    exact (Subgroup.eq_of_le_of_card_ge hCP (by omega)).ge
  have hE : ∀ k ∈ T ⊓ K1, k ^ 2 = 1 → k ≠ 1 →
      ¬ ∃ f : ↥(T ⊓ Subgroup.centralizer ({k} : Set G)) →*
        ↥(T ⊓ Subgroup.centralizer ({(j' : G)} : Set G)), Function.Injective f := by
    intro k hk hk2 hk1 ⟨f, hf⟩
    have hkM : k ∈ Mc := hTM hk.1
    set k' : ↥Mc := ⟨k, hkM⟩ with hk'
    have hkTY : ψ k' ∈ TY ⊓ N :=
      ⟨mem_map_subgroupOf.mpr ⟨k', hk.1, rfl⟩, mem_map_subgroupOf.mpr ⟨k', hk.2, rfl⟩⟩
    have hk2Y : ψ k' ^ 2 = 1 := by
      rw [← map_pow, show k' ^ 2 = 1 from Subtype.ext hk2, map_one]
    have hk1Y : ψ k' ≠ 1 := fun h => hk1 (by
      have : k' = 1 := hψ (h.trans (map_one ψ).symm)
      simpa [hk'] using congrArg Subtype.val this)
    refine hNE (ψ k') hkTY hk2Y hk1Y ?_
    have hAK : T ⊓ Subgroup.centralizer ({k} : Set G) ≤ Mc := inf_le_left.trans hTM
    have hAeq : ((T ⊓ Subgroup.centralizer ({(k' : G)} : Set G)).subgroupOf Mc).map ψ =
        TY ⊓ Subgroup.centralizer ({ψ k'} : Set Y) := map_subgroupOf_centralizer hψ T k'
    let eK : ↥(T ⊓ Subgroup.centralizer ({k} : Set G)) ≃*
        ↥(TY ⊓ Subgroup.centralizer ({ψ k'} : Set Y)) :=
      (equivMapSubgroupOf hψ hAK).trans (MulEquiv.subgroupCongr hAeq)
    let eC : ↥C ≃* ↥(TY ⊓ Subgroup.centralizer ({jY} : Set Y)) :=
      (equivMapSubgroupOf hψ hCM).trans (MulEquiv.subgroupCongr hCY)
    exact ⟨eC.toMonoidHom.comp (f.comp eK.symm.toMonoidHom),
      eC.injective.comp (hf.comp eK.symm.injective)⟩
  have hrel : (T ⊓ K1).relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := T ⊓ K1) (K := T)
    rw [inf_eq_left.mpr (inf_le_left : T ⊓ K1 ≤ T), hcard] at h1
    have hpos : 0 < Nat.card ↥(T ⊓ K1) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  exact S1421QA17.false_of_outer_involution hnc hTS inf_le_left hrel hjT hjU hj2 hN hS hE

end Transport

end S1421QA17

end CFSG.Quasithin
