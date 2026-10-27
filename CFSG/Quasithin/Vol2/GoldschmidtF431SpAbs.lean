module

import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7

section Basic

variable {G : Type*} [Group G]

theorem mem_centerOf_iff {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ t ∈ X, t * x = x * t := by
  unfold centerOf
  rw [Subgroup.mem_inf]
  exact and_congr_right fun _ => Subgroup.mem_centralizer_iff

def ConjTo (n : G) (Q Q' : Subgroup G) : Prop := ∀ x : G, x ∈ Q' ↔ n⁻¹ * x * n ∈ Q

theorem conjTo_iff_normalizer {n : G} {Q : Subgroup G} :
    ConjTo n Q Q ↔ n ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (n * x * n⁻¹)
    rw [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at this
    exact this.symm
  · intro h x
    have := h (n⁻¹ * x * n)
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
    exact this.symm

theorem pCoreOf_conj_mem {H : Subgroup G} {g q : G} (hg : g ∈ H) (hq : q ∈ pCoreOf 2 H) :
    g * q * g⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨p, hp, rfl⟩ := hq
  have hn := (LieType.BorelTits.pCore_normal 2 (G := ↥H)).conj_mem p hp ⟨g, hg⟩
  exact ⟨_, hn, rfl⟩

end Basic

section Burnside

variable {G : Type*} [Group G] [Finite G]

theorem exists_normalizer_conj_of_central {T : Subgroup G} (hT : IsSylowTwoOf T ⊤) {u v g : G}
    (hu : u ∈ centerOf T) (hv : v ∈ centerOf T) (h : g * u * g⁻¹ = v) :
    ∃ n ∈ Subgroup.normalizer (T : Set G), n * u * n⁻¹ = v := by
  set C := Subgroup.centralizer ({v} : Set G) with hC
  have hu' := mem_centerOf_iff.mp hu
  have hv' := mem_centerOf_iff.mp hv
  have hTC : T ≤ C := fun t ht => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hv'.2 t ht
  set T' : Subgroup G := T.map (MulAut.conj g).toMonoidHom with hT'
  have htop : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective
  have hT'S : IsSylowTwoOf T' ⊤ := by
    have := F7.isSylowTwoOf_conj hT g
    unfold CFSG.Quasithin.conjSub at this
    rwa [htop] at this
  have hT'C : T' ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    rw [← h]
    have := hu'.2 t ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * t * g⁻¹ * (g * u * g⁻¹) = g * (t * u) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [this]
      _ = g * u * g⁻¹ * (g * t * g⁻¹) := by group
  obtain ⟨c, hcC, hc⟩ := IsSylowTwoOf.exists_conj
    (F7.isSylowTwoOf_mono_right hT hTC le_top) (F7.isSylowTwoOf_mono_right hT'S hT'C le_top)
  have hcv : v * c = c * v := (Subgroup.mem_centralizer_singleton_iff.mp hcC).symm
  have hcT : ∀ x, x ∈ T' ↔ ∃ t ∈ T, c * t * c⁻¹ = x := fun x => by
    rw [hc, Subgroup.mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hgT : ∀ x, x ∈ T' ↔ ∃ t ∈ T, g * t * g⁻¹ = x := fun x => by
    rw [hT', Subgroup.mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨t, ht, hte⟩ := (hcT (g * x * g⁻¹)).mp ((hgT _).mpr ⟨x, hx, rfl⟩)
      have : c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = t := by
        calc c⁻¹ * g * x * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
          _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hte]
          _ = t := by group
      rw [this]
      exact ht
    · intro hx
      obtain ⟨s, hs, hse⟩ := (hgT (c * (c⁻¹ * g * x * (c⁻¹ * g)⁻¹) * c⁻¹)).mp
        ((hcT _).mpr ⟨_, hx, rfl⟩)
      have h1 : g * s * g⁻¹ = g * x * g⁻¹ := by
        rw [hse]
        group
      have : s = x := mul_left_cancel (mul_right_cancel h1)
      rw [← this]
      exact hs
  · calc c⁻¹ * g * u * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * u * g⁻¹) * c := by group
      _ = c⁻¹ * v * c := by rw [h]
      _ = c⁻¹ * (v * c) := by group
      _ = c⁻¹ * (c * v) := by rw [hcv]
      _ = v := by group

end Burnside

structure SpShape {G : Type*} [Group G] (T : Subgroup G) (Q : Fin 2 → Subgroup G) : Prop where
  Q_le : ∀ j, Q j ≤ T
  Q_norm : ∀ j, T ≤ Subgroup.normalizer (Q j : Set G)
  Q_abel : ∀ j, ∀ x ∈ Q j, ∀ y ∈ Q j, x * y = y * x
  Z_le : ∀ j, centerOf T ≤ Q j
  Z_sq : ∀ z ∈ centerOf T, z ^ 2 = 1
  inv_mem : ∀ x ∈ T, x ^ 2 = 1 → ∃ j, x ∈ Q j
  cen : ∀ j, ∀ x ∈ Q j, x ∉ centerOf T → ∀ y ∈ T, y * x = x * y → y ∈ Q j
  ex : ∀ j, ∃ x ∈ Q j, x ∉ centerOf T ∧ x ^ 2 = 1

namespace SpShape

variable {G : Type*} [Group G] {T : Subgroup G} {Q : Fin 2 → Subgroup G}

theorem conj_mem (S : SpShape T Q) {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) (j : Fin 2) :
    ∃ k, ConjTo n (Q j) (Q k) := by
  obtain ⟨x₀, hx₀Q, hx₀Z, hx₀2⟩ := S.ex j
  have hx₀T : x₀ ∈ T := S.Q_le j hx₀Q
  have hnT := Subgroup.mem_normalizer_iff.mp hn
  set y : G := n * x₀ * n⁻¹ with hy
  have hyT : y ∈ T := (hnT x₀).mp hx₀T
  have hy2 : y ^ 2 = 1 := by
    have h1 : x₀ * x₀ = 1 := by rw [← sq]; exact hx₀2
    have : y ^ 2 = n * (x₀ * x₀) * n⁻¹ := by rw [hy, sq]; group
    rw [this, h1]
    group
  have hyZ : y ∉ centerOf T := by
    intro hyc
    apply hx₀Z
    rw [mem_centerOf_iff] at hyc ⊢
    refine ⟨hx₀T, fun t ht => ?_⟩
    have h1 := hyc.2 (n * t * n⁻¹) ((hnT t).mp ht)
    have h2 : n * (t * x₀) * n⁻¹ = n * (x₀ * t) * n⁻¹ := by
      calc n * (t * x₀) * n⁻¹ = (n * t * n⁻¹) * (n * x₀ * n⁻¹) := by group
        _ = (n * x₀ * n⁻¹) * (n * t * n⁻¹) := h1
        _ = n * (x₀ * t) * n⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨k, hk⟩ := S.inv_mem y hyT hy2
  refine ⟨k, fun x => ⟨fun hxk => ?_, fun hxj => ?_⟩⟩
  ·
    have hxT : x ∈ T := S.Q_le k hxk
    have hc : x * y = y * x := S.Q_abel k x hxk y hk
    have hT' : n⁻¹ * x * n ∈ T := by
      refine (hnT (n⁻¹ * x * n)).mpr ?_
      rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group]
      exact hxT
    refine S.cen j x₀ hx₀Q hx₀Z _ hT' ?_
    calc n⁻¹ * x * n * x₀ = n⁻¹ * (x * (n * x₀ * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x₀ * n⁻¹) * x) * n := by rw [← hy, hc]
      _ = x₀ * (n⁻¹ * x * n) := by group
  · have hxjT : n⁻¹ * x * n ∈ T := S.Q_le j hxj
    have hxT : x ∈ T := by
      have := (hnT (n⁻¹ * x * n)).mp hxjT
      rwa [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
    refine S.cen k y hk hyZ x hxT ?_
    have hc : n⁻¹ * x * n * x₀ = x₀ * (n⁻¹ * x * n) := S.Q_abel j _ hxj x₀ hx₀Q
    calc x * y = n * (n⁻¹ * x * n * x₀) * n⁻¹ := by rw [hy]; group
      _ = n * (x₀ * (n⁻¹ * x * n)) * n⁻¹ := by rw [hc]
      _ = y * x := by rw [hy]; group


theorem fin_two_eq : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a = c := by decide

theorem normalizer_le (S : SpShape T Q) (hT : IsSylowTwoOf T ⊤) {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) (j : Fin 2) :
    n ∈ Subgroup.normalizer (Q j : Set G) := by
  by_contra hnj
  obtain ⟨k, hk⟩ := S.conj_mem hn j
  obtain ⟨l, hl⟩ := S.conj_mem hn k
  have hkj : k ≠ j := by
    rintro rfl
    exact hnj (conjTo_iff_normalizer.mp hk)
  have hlk : l ≠ k := by
    rintro rfl
    apply hnj
    refine conjTo_iff_normalizer.mp fun x => ?_
    have hQ : ∀ y, y ∈ Q j ↔ y ∈ Q l := fun y => by
      have h1 := hk (n * y * n⁻¹)
      have h2 := hl (n * y * n⁻¹)
      rw [show n⁻¹ * (n * y * n⁻¹) * n = y by group] at h1 h2
      exact h1.symm.trans h2
    rw [hQ x]
    exact hk x
  have hlj : l = j := fin_two_eq l k j hlk hkj
  subst hlj
  have hn2 : n * n ∈ Subgroup.normalizer (Q l : Set G) := by
    refine conjTo_iff_normalizer.mp fun x => ?_
    rw [hl x, hk (n⁻¹ * x * n), show n⁻¹ * (n⁻¹ * x * n) * n = (n * n)⁻¹ * x * (n * n) by group]
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hSyl : IsSylowTwoOf T N := F7.isSylowTwoOf_mono_right hT hTN le_top
  have hodd : ¬ 2 ∣ (T.subgroupOf N).index := F7.isSylowTwoOf_odd_relIndex hSyl
  have : (T.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hpow := Subgroup.pow_index_mem (T.subgroupOf N) (⟨n, hn⟩ : N)
  have hpowT : n ^ (T.subgroupOf N).index ∈ T := by
    rw [Subgroup.mem_subgroupOf] at hpow
    simpa using hpow
  obtain ⟨r, hr⟩ : Odd (T.subgroupOf N).index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have h1 : n ^ (T.subgroupOf N).index ∈ Subgroup.normalizer (Q l : Set G) := S.Q_norm l hpowT
  have h2 : n ^ ((T.subgroupOf N).index + 1) ∈ Subgroup.normalizer (Q l : Set G) := by
    have : n ^ ((T.subgroupOf N).index + 1) = (n * n) ^ (r + 1) := by
      rw [hr, ← sq, ← pow_mul]
      congr 1
    rw [this]
    exact Subgroup.pow_mem _ hn2 _
  have h3 : n = n ^ ((T.subgroupOf N).index + 1) * (n ^ (T.subgroupOf N).index)⁻¹ := by group
  exact hnj (h3 ▸ Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ h1))

end SpShape


section Centralizer

variable {G : Type*} [Group G] [Finite G] {T : Subgroup G} {Q : Fin 2 → Subgroup G}

theorem SpShape.centralizer_cases (S : SpShape T Q) (hT : IsSylowTwoOf T ⊤) {u : G}
    (hu : u ∈ centerOf T) (hchar : CharTwo (Subgroup.centralizer ({u} : Set G))) :
    (∃ j, Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (Q j : Set G)) ∨
      ∀ g ∈ Subgroup.centralizer ({u} : Set G), ∀ z ∈ centerOf T, g * z * g⁻¹ ∈ centerOf T := by
  set M := Subgroup.centralizer ({u} : Set G) with hM
  set Qu := pCoreOf 2 M with hQu
  have hu' := mem_centerOf_iff.mp hu
  have hTM : T ≤ M := fun t ht => by
    rw [hM, Subgroup.mem_centralizer_singleton_iff]
    exact hu'.2 t ht
  have hSylM : IsSylowTwoOf T M := F7.isSylowTwoOf_mono_right hT hTM le_top
  have hQuT : Qu ≤ T := F7.isSylowTwoOf_pCoreOf_le hSylM
  have hZQu : ∀ z ∈ centerOf T, z ∈ Qu := fun z hz => by
    have hz' := mem_centerOf_iff.mp hz
    refine hchar ⟨?_, ?_⟩
    · show z ∈ Subgroup.centralizer ({u} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hz'.2 u hu'.1).symm
    · show z ∈ Subgroup.centralizer (Qu : Set G)
      rw [Subgroup.mem_centralizer_iff]
      exact fun q hq => hz'.2 q (hQuT hq)
  by_cases hA : ∀ x ∈ Qu, (∀ y ∈ Qu, y * x = x * y) → x ^ 2 = 1 → x ∈ centerOf T
  · right
    intro g hg z hz
    have hz' := mem_centerOf_iff.mp hz
    have h1 : g * z * g⁻¹ ∈ Qu := pCoreOf_conj_mem hg (hZQu z hz)
    have h2 : ∀ y ∈ Qu, y * (g * z * g⁻¹) = (g * z * g⁻¹) * y := by
      intro y hy
      have hy' : g⁻¹ * y * g ∈ Qu := by
        have := pCoreOf_conj_mem (M.inv_mem hg) hy
        simpa using this
      have := hz'.2 _ (hQuT hy')
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = (g * z * g⁻¹) * y := by group
    have h3 : (g * z * g⁻¹) ^ 2 = 1 := by
      have e : z * z = 1 := by rw [← sq]; exact S.Z_sq z hz
      calc (g * z * g⁻¹) ^ 2 = g * (z * z) * g⁻¹ := by rw [sq]; group
        _ = 1 := by rw [e]; group
    exact hA _ h1 h2 h3
  · left
    have hA' : ∃ x ∈ Qu, (∀ y ∈ Qu, y * x = x * y) ∧ x ^ 2 = 1 ∧ x ∉ centerOf T := by
      by_contra hcon
      exact hA fun x hx hc h2 => by
        by_contra hx'
        exact hcon ⟨x, hx, hc, h2, hx'⟩
    obtain ⟨x₀, hx₀Q, hx₀c, hx₀2, hx₀Z⟩ := hA'

    obtain ⟨j, hj⟩ := S.inv_mem x₀ (hQuT hx₀Q) hx₀2
    refine ⟨j, ?_⟩
    have hQuj : Qu ≤ Q j := fun y hy => S.cen j x₀ hj hx₀Z y (hQuT hy) (hx₀c y hy)
    have hQjM : Q j ≤ M := fun q hq => by
      rw [hM, Subgroup.mem_centralizer_singleton_iff]
      exact S.Q_abel j q hq u (S.Z_le j hu)
    have hQju : Q j ≤ Qu := fun q hq => by
      refine hchar ⟨hQjM hq, ?_⟩
      show q ∈ Subgroup.centralizer (Qu : Set G)
      rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => S.Q_abel j y (hQuj hy) q hq
    have hEq : Qu = Q j := le_antisymm hQuj hQju
    intro g hg
    rw [← hEq]
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => pCoreOf_conj_mem hg hx, fun hx => ?_⟩
    have := pCoreOf_conj_mem (M.inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

end Centralizer

end CFSG.Quasithin.H13.F431
