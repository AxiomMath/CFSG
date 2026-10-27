module

public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.OrderingMax

public section

namespace CFSG.Quasithin.S14110

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneCenter_le_self (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun w hw => hw.1.1

theorem centralizer_singleton_le_mc {T Mc : Subgroup G} (h : quasithinQTFE14Cat G T Mc) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Mc := by
  have hzT : z ∈ T := omegaOneCenter_le_self T hz
  set P : Subgroup G := Subgroup.zpowers z with hP
  have hPp : IsPGroup 2 P := h.sylow.1.to_le (Subgroup.zpowers_le.mpr hzT)
  have hP1 : P ≠ ⊥ := by
    intro hb
    exact hz1 ((Subgroup.zpowers_eq_bot).mp hb)
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have : Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (P : Set G) := by
      rw [hP, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [this]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨M'', hM'', hNM''⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (P : Set G)) ⟨P, hP1, hPp, rfl⟩
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M'' := by
    refine le_trans ?_ (hCN.trans hNM'')
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hM''eq : M'' = Mc := h.mc_unique M'' hM'' hCZ
  rw [← hM''eq]
  exact hCN.trans hNM''

theorem exists_mem_omegaOneCenter_of_normalized {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hU : U ≠ ⊥) (hn : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ quasithinOmegaOneCenter T := by
  have hTnil : Group.IsNilpotent T := hT.isNilpotent
  have hUTn : (U.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr hn
  have hU' : U.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hU')
  have hwU : (w : G) ∈ U := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1
  have hwc : ∀ y ∈ T, (y : G) * w = w * y := fun y hy => by
    have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨k, hk⟩ := hT w
  have hk' : (w : G) ^ 2 ^ k = 1 := by simpa using congrArg (fun u : T => (u : G)) hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_of_pow_eq_one hk' : orderOf (w : G) ∣ 2 ^ k)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hw1' (orderOf_eq_one_iff.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  set z : G := (w : G) ^ 2 ^ i with hz
  have hzU : z ∈ U := Subgroup.pow_mem U hwU _
  have hzT : z ∈ T := Subgroup.pow_mem T w.2 _
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, ← hj]
    exact pow_orderOf_eq_one _
  have hz1 : z ≠ 1 := by
    intro h1
    have : orderOf (w : G) ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at this
    have := Nat.le_of_dvd (by positivity) this
    have h2 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨z, hzU, hz1, Subgroup.subset_closure ⟨⟨hzT, ?_⟩, hz2⟩⟩
  show z ∈ Subgroup.centralizer (T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Commute.pow_right (show Commute y (w : G) from hwc y hy) _).eq

omit [Finite G] in
theorem conj_mem_centralizer {M X₀ : Subgroup G} (hn : M ≤ Subgroup.normalizer (X₀ : Set G))
    {m k : G} (hm : m ∈ M) (hk : k ∈ Subgroup.centralizer (X₀ : Set G)) :
    m * k * m⁻¹ ∈ Subgroup.centralizer (X₀ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : m⁻¹ * x * m ∈ X₀ := by
    have := (Subgroup.mem_normalizer_iff.1 (hn (M.inv_mem hm)) x).1 hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hk _ hx'
  calc x * (m * k * m⁻¹) = m * ((m⁻¹ * x * m) * k) * m⁻¹ := by group
    _ = m * (k * (m⁻¹ * x * m)) * m⁻¹ := by rw [h1]
    _ = m * k * m⁻¹ * x := by group

theorem eq_mc_of_centralizer_ne_bot {T Mc M X₀ U : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hX₀M : X₀ ≤ M) (hX₀n : M ≤ Subgroup.normalizer (X₀ : Set G))
    (hcen : ∀ z ∈ X₀, (∀ y ∈ X₀, z * y = y * z) → z = 1)
    (hUX : U ≤ X₀) (hU : U ≠ ⊥) (hUel : ∀ u ∈ U, u ^ 2 = 1)
    (hUn : M ≤ Subgroup.normalizer (U : Set G))
    (hfact : ∀ m ∈ M, ∃ k ∈ M ⊓ Subgroup.centralizer (X₀ : Set G), ∃ x ∈ X₀, ∃ t ∈ T,
      m = k * x * t)
    (hCT : T ⊓ Subgroup.centralizer (X₀ : Set G) ≠ ⊥) :
    M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hTM : T ≤ M := hM.2
  have hUp : IsPGroup 2 U := fun u => ⟨1, by
    have := hUel u u.2
    simpa [Subtype.ext_iff] using this⟩
  have hUT : U ≤ T := by
    have := (le_pCoreOf_of_le_normalizer 2 (hUX.trans hX₀M) hUn hUp).trans
      (pCoreOf_two_le_sylow M S (hS ▸ hTM))
    rwa [hS] at this
  obtain ⟨z₀, hz₀U, hz₀1, hz₀Z⟩ :=
    exists_mem_omegaOneCenter_of_normalized h.sylow.1 hUT hU (hTM.trans hUn)
  have hCTn : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (X₀ : Set G) : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key : ∀ s ∈ T, ∀ g ∈ T ⊓ Subgroup.centralizer (X₀ : Set G),
        s * g * s⁻¹ ∈ T ⊓ Subgroup.centralizer (X₀ : Set G) := fun s hs g hg =>
      Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem hs hg.1) (T.inv_mem hs),
        conj_mem_centralizer hX₀n (hTM hs) hg.2⟩
    constructor
    · exact key t ht g
    · intro hg
      have := key t⁻¹ (T.inv_mem ht) _ hg
      simpa [mul_assoc] using this
  obtain ⟨z₁, hz₁C, hz₁1, hz₁Z⟩ :=
    exists_mem_omegaOneCenter_of_normalized h.sylow.1 inf_le_left hCT hCTn
  have hX₀Mc : X₀ ≤ Mc := fun x hx =>
    centralizer_singleton_le_mc h hz₁Z hz₁1 (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hz₁C.2 x hx)
  have hKMc : M ⊓ Subgroup.centralizer (X₀ : Set G) ≤ Mc := fun k hk =>
    centralizer_singleton_le_mc h hz₀Z hz₀1 (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hk.2 z₀ (hUX hz₀U)).symm)
  have hMMc : M ≤ Mc := by
    intro m hm
    obtain ⟨k, hk, x, hx, t, ht, rfl⟩ := hfact m hm
    exact Mc.mul_mem (Mc.mul_mem (hKMc hk) (hX₀Mc hx)) (h.t_le_mc ht)
  refine ⟨(hM.1.2 Mc h.mc_max.1 hMMc).symm, ?_⟩
  have hz01 : z₀ ≠ z₁ := by
    intro heq
    apply hz₀1
    apply hcen z₀ (hUX hz₀U)
    intro y hy
    have := Subgroup.mem_centralizer_iff.1 hz₁C.2 y hy
    rw [heq]
    exact this.symm
  classical
  have h01 : (1 : quasithinOmegaOneCenter T) ≠ ⟨z₀, hz₀Z⟩ := fun e =>
    hz₀1 (by simpa using (congrArg Subtype.val e).symm)
  have h02 : (1 : quasithinOmegaOneCenter T) ≠ ⟨z₁, hz₁Z⟩ := fun e =>
    hz₁1 (by simpa using (congrArg Subtype.val e).symm)
  have h12 : (⟨z₀, hz₀Z⟩ : quasithinOmegaOneCenter T) ≠ ⟨z₁, hz₁Z⟩ := fun e =>
    hz01 (congrArg Subtype.val e)
  have hcard : ({1, ⟨z₀, hz₀Z⟩, ⟨z₁, hz₁Z⟩} : Finset (quasithinOmegaOneCenter T)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, ⟨z₀, hz₀Z⟩, ⟨z₁, hz₁Z⟩, h01, h02, h12, rfl⟩
  have : Fintype (quasithinOmegaOneCenter T) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  calc 2 < 3 := by norm_num
    _ = ({1, ⟨z₀, hz₀Z⟩, ⟨z₁, hz₁Z⟩} : Finset (quasithinOmegaOneCenter T)).card := hcard.symm
    _ ≤ Fintype.card (quasithinOmegaOneCenter T) := Finset.card_le_univ _

theorem centralizer_eq_bot_of_centralizer_inf_eq_bot {T Mc M X₀ : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hX₀n : M ≤ Subgroup.normalizer (X₀ : Set G))
    (hCT : T ⊓ Subgroup.centralizer (X₀ : Set G) = ⊥) :
    M ⊓ Subgroup.centralizer (X₀ : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hTM : T ≤ M := hM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M hM.1.1 ⟨S, hS ▸ hTM⟩
  have hQT : pCoreOf 2 M ≤ T := by
    have := pCoreOf_two_le_sylow M S (hS ▸ hTM)
    rwa [hS] at this
  rw [eq_bot_iff]
  intro k hk
  have hkQ : k ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqM : q ∈ M := pCoreOf_le 2 M hq
    have hkn : k ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M hk.1
    have h1 : k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 M := (Subgroup.mem_normalizer_iff.1 hkn q⁻¹).1 (inv_mem hq)
    have h2 : q * k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 M := by
      have : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hq h1
    have h3 : q * k * q⁻¹ * k⁻¹ ∈ Subgroup.centralizer (X₀ : Set G) :=
      Subgroup.mul_mem _ (conj_mem_centralizer hX₀n hqM hk.2) (inv_mem hk.2)
    have h4 : q * k * q⁻¹ * k⁻¹ ∈ T ⊓ Subgroup.centralizer (X₀ : Set G) := ⟨hQT h2, h3⟩
    rw [hCT, Subgroup.mem_bot] at h4
    calc q * k = (q * k * q⁻¹ * k⁻¹) * k * q := by group
      _ = k * q := by rw [h4]; group
  have hkT : k ∈ T := hQT (hF ⟨hk.1, hkQ⟩)
  have : k ∈ T ⊓ Subgroup.centralizer (X₀ : Set G) := ⟨hkT, hk.2⟩
  rwa [hCT] at this

end CFSG.Quasithin.S14110
