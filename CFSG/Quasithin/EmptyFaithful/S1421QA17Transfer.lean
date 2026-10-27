module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421QA17

variable {G : Type} [Group G] [Finite G]

theorem eq_of_inf_normalizer_le {P S : Subgroup G} (hP : IsPGroup 2 P) (hSP : S ≤ P)
    (hN : P ⊓ Subgroup.normalizer (S : Set G) ≤ S) : S = P := by
  by_contra hne
  have hIPlt : S.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    refine le_antisymm hSP fun x hx => ?_
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
  have hlt : S.subgroupOf P < Subgroup.normalizer ((S.subgroupOf P : Subgroup P) : Set P) :=
    hnc _ hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  exact hxnot (Subgroup.mem_subgroupOf.mpr (hN ⟨x.2, hxNorm⟩))

theorem isSylowTwoOf_inf_centralizer {T : Subgroup G} (hT : IsPGroup 2 T) {z j : G}
    (hN : ∀ g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) :
      Set G), g * z = z * g)
    (hS : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({j} : Set G) →
      P ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 2 P →
      T ⊓ Subgroup.centralizer ({j} : Set G) ≤ P → P ≤ T ⊓ Subgroup.centralizer ({j} : Set G)) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({j} : Set G)) (Subgroup.centralizer ({j} : Set G)) := by
  set C := T ⊓ Subgroup.centralizer ({j} : Set G) with hC
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨inf_le_right, hT.to_le inf_le_left, fun P hPj hP hCP => ?_⟩
  by_contra hPC
  have hne : ¬ P ⊓ Subgroup.normalizer (C : Set G) ≤ C := fun hle =>
    hPC (le_of_eq (eq_of_inf_normalizer_le hP hCP hle).symm)
  obtain ⟨x, ⟨hxP, hxN⟩, hxC⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hCz : C ≤ Subgroup.centralizer ({z} : Set G) := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hN c (Subgroup.le_normalizer hc))
  have hP' : P ⊓ Subgroup.normalizer (C : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤ C :=
    hS _ (inf_le_left.trans (inf_le_left.trans hPj)) inf_le_right
      (hP.to_le (inf_le_left.trans inf_le_left)) (le_inf (le_inf hCP Subgroup.le_normalizer) hCz)
      |>.trans le_rfl
  have hxz : x ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hN x hxN)
  exact hxC (hP' ⟨⟨hxP, hxN⟩, hxz⟩)

theorem false_of_outer_involution [IsSimpleGroup G] (hnc : ∃ a b : G, a * b ≠ b * a)
    {T U : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hUT : U ≤ T) (hUi : U.relIndex T = 2)
    {z j : G} (hjT : j ∈ T) (hjU : j ∉ U) (hj2 : j ^ 2 = 1)
    (hN : ∀ g ∈ Subgroup.normalizer ((T ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) :
      Set G), g * z = z * g)
    (hS : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({j} : Set G) →
      P ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 2 P →
      T ⊓ Subgroup.centralizer ({j} : Set G) ≤ P → P ≤ T ⊓ Subgroup.centralizer ({j} : Set G))
    (hE : ∀ k ∈ U, k ^ 2 = 1 → k ≠ 1 →
      ¬ ∃ f : ↥(T ⊓ Subgroup.centralizer ({k} : Set G)) →*
        ↥(T ⊓ Subgroup.centralizer ({j} : Set G)), Function.Injective f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTG, hT2, hTidx⟩ := hT
  set C := T ⊓ Subgroup.centralizer ({j} : Set G) with hC
  have hSyl : IsSylowTwoOf C (Subgroup.centralizer ({j} : Set G)) :=
    isSylowTwoOf_inf_centralizer hT2 hN hS
  have hj1 : j ≠ 1 := fun h => hjU (h ▸ U.one_mem)
  have key : ∀ g : G, g⁻¹ * j * g ∉ U := by
    intro g hgU
    set k := g⁻¹ * j * g with hk
    have hk2 : k ^ 2 = 1 := by
      have : k = g⁻¹ * j * g⁻¹⁻¹ := by rw [hk, inv_inv]
      rw [this, conj_pow, hj2]
      group
    have hk1 : k ≠ 1 := fun h => hj1 (by
      have : j = g * k * g⁻¹ := by rw [hk]; group
      rw [this, h]
      group)
    set Ck := T ⊓ Subgroup.centralizer ({k} : Set G) with hCk
    have hCkj : conjSub g Ck ≤ Subgroup.centralizer ({j} : Set G) := by
      intro x hx
      rw [mem_conjSub] at hx
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc x * j = g * ((g⁻¹ * x * g) * k) * g⁻¹ := by rw [hk]; group
        _ = g * (k * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
        _ = j * x := by rw [hk]; group
    have hCk2 : IsPGroup 2 (conjSub g Ck) := (hT2.to_le inf_le_left).map _
    obtain ⟨c, hc, hconj⟩ := F7.isSylowTwoOf_exists_conj_le hSyl hCkj hCk2
    have hmem : ∀ x : ↥Ck, (c⁻¹ * g) * (x : G) * (c⁻¹ * g)⁻¹ ∈ C := by
      intro x
      have h1 : g * (x : G) * g⁻¹ ∈ conjSub g Ck := by
        rw [mem_conjSub, show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group]
        exact x.2
      have h2 := hconj h1
      rw [mem_conjSub] at h2
      simpa [mul_assoc] using h2
    let f : ↥Ck →* ↥C := ((MulAut.conj (c⁻¹ * g)).toMonoidHom.comp Ck.subtype).codRestrict C hmem
    refine hE k hgU hk2 hk1 ⟨f, fun x y hxy => ?_⟩
    have h1 : (c⁻¹ * g) * (x : G) * (c⁻¹ * g)⁻¹ = (c⁻¹ * g) * (y : G) * (c⁻¹ * g)⁻¹ :=
      congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h1)
  have hx2 : ∀ y ∈ T, y ∉ U → orderOf j ≤ orderOf y := by
    intro y hyT hyU
    have hj : orderOf j = 2 := orderOf_eq_prime hj2 hj1
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
    have hy0 : 0 < orderOf y := orderOf_pos y
    have hy1' : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    rw [hj]
    omega
  have hTidx' : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hTidx
  obtain ⟨N, hNn, hNi⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hT2 hTidx'
    hUT hUi hjT hjU hx2 key
  rcases hNn.eq_bot_or_eq_top with h | h
  · rw [h, Subgroup.index_bot] at hNi
    have hprime : Nat.Prime (Nat.card G) := by rw [hNi]; exact Nat.prime_two
    have : Fact (Nat.card G).Prime := ⟨hprime⟩
    have : IsCyclic G := isCyclic_of_prime_card rfl
    let _ : CommGroup G := IsCyclic.commGroup
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (mul_comm a b)
  · rw [h, Subgroup.index_top] at hNi
    omega

end S1421QA17

end CFSG.Quasithin
