module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3B1
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3B2a
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Lev
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V1

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section B2b

private theorem leviOfL3_le_centralizer_L3B2b {G : Type*} [Group G] (N : Subgroup G) (z : G) :
    leviOfL3 N z ≤ N ⊓ Subgroup.centralizer ({z} : Set G) := by
  unfold leviOfL3
  refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

private theorem conj_mem_leviOfL3_L3B2b {G : Type*} [Group G] (N : Subgroup G) (z c x : G)
    (hc : c ∈ N ⊓ Subgroup.centralizer ({z} : Set G)) (hx : x ∈ leviOfL3 N z) :
    c * x * c⁻¹ ∈ leviOfL3 N z := by
  obtain ⟨hcN, hcz⟩ := Subgroup.mem_inf.mp hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hcz
  have hcz' : Commute c z := hcz
  have hmap : (N ⊓ Subgroup.centralizer ({z} : Set G)).map (MulAut.conj c).toMonoidHom ≤
      N ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨hwN, hwz⟩ := Subgroup.mem_inf.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hwz
    have hwz' : Commute w z := hwz
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show c * w * c⁻¹ ∈ N
      exact mul_mem (mul_mem hcN hwN) (inv_mem hcN)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      show c * w * c⁻¹ * z = z * (c * w * c⁻¹)
      exact ((hcz'.mul_left hwz').mul_left hcz'.inv_left).eq
  unfold leviOfL3 at hx ⊢
  have key : (⁅N ⊓ Subgroup.centralizer ({z} : Set G),
      N ⊓ Subgroup.centralizer ({z} : Set G)⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom ≤
      ⁅N ⊓ Subgroup.centralizer ({z} : Set G), N ⊓ Subgroup.centralizer ({z} : Set G)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  exact key (Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hx)

private theorem isPGroup_subgroupOf_L3B2b {G : Type*} [Group G] {p : ℕ} {S K : Subgroup G}
    (hS : IsPGroup p ↥S) : IsPGroup p ↥(S.subgroupOf K) := by
  intro x
  obtain ⟨n, hn⟩ := hS ⟨((x : ↥K) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have h := congrArg Subtype.val hn
  simpa using h

private theorem isPGroup_map_L3B2b {G G' : Type*} [Group G] [Group G'] {p : ℕ} (f : G →* G')
    {H : Subgroup G} (hH : IsPGroup p ↥H) : IsPGroup p ↥(H.map f) := by
  intro d
  obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp d.2
  obtain ⟨n, hn⟩ := hH ⟨x, hx⟩
  refine ⟨n, Subtype.ext ?_⟩
  have hx1 : x ^ p ^ n = 1 := by
    have h := congrArg Subtype.val hn
    simpa using h
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hxd, ← map_pow, hx1, map_one]

private theorem relIndex_map_range_L3B2b {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H : Subgroup G) (hker : f.ker ≤ H) : (H.map f).relIndex f.range = H.index := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, sup_eq_left.mpr hker, top_sup_eq,
    Subgroup.relIndex_top_right]

private theorem map_conj_zpowers_L3B2b {G G' : Type*} [Group G] [Group G'] {M : Subgroup G}
    (σ : ↥M →* G') {y : G} (hy : y ∈ M) (g : ↥M)
    (hg : (g : G) * y * (g : G)⁻¹ ∈ Subgroup.zpowers y) :
    σ g * σ ⟨y, hy⟩ * (σ g)⁻¹ ∈ Subgroup.zpowers (σ ⟨y, hy⟩) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hconj : g * ⟨y, hy⟩ * g⁻¹ = (⟨y, hy⟩ : ↥M) ^ m := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    exact hm.symm
  rw [← map_inv, ← map_mul, ← map_mul, hconj, map_zpow]
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩

private theorem not_two_dvd_index_levi_L3B2b {G : Type} [Group G] [Finite G] {N S : Subgroup G}
    {z : G} (hS : IsSylowTwoOf S N) (hSz : ∀ s ∈ S, Commute s z) :
    ¬ 2 ∣ (S.subgroupOf (leviOfL3 N z)).index := by
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = N ⊓ Subgroup.centralizer ({z} : Set G) := ⟨_, rfl⟩
  have hCN : C ≤ N := by
    rw [hCdef]
    exact inf_le_left
  have hSC : S ≤ C := by
    intro s hs
    rw [hCdef]
    exact Subgroup.mem_inf.mpr ⟨hS.1 hs, Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩
  have hKC : leviOfL3 N z ≤ C := by
    rw [hCdef]
    exact leviOfL3_le_centralizer_L3B2b N z
  have hKnorm : ∀ c ∈ C, ∀ x ∈ leviOfL3 N z, c * x * c⁻¹ ∈ leviOfL3 N z := by
    intro c hc x hx
    rw [hCdef] at hc
    exact conj_mem_leviOfL3_L3B2b N z c x hc hx
  haveI hKcN : ((leviOfL3 N z).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff hKC).mpr (fun h k hh hk => hKnorm k hk h hh)
  have hSc2 : IsPGroup 2 ↥(S.subgroupOf C) := isPGroup_subgroupOf_L3B2b hS.2.1
  have hSC_idx : ¬ 2 ∣ (S.subgroupOf C).index := by
    have h1 : S.relIndex C * C.relIndex N = S.relIndex N :=
      Subgroup.relIndex_mul_relIndex S C N hSC hCN
    intro hd
    exact hS.2.2 (dvd_trans hd (Dvd.intro _ h1))
  have hTs : IsSylowTwoOf (S.subgroupOf C) ((leviOfL3 N z).subgroupOf C ⊔ S.subgroupOf C) := by
    refine ⟨le_sup_right, hSc2, ?_⟩
    intro hd
    have h3 : (S.subgroupOf C).relIndex ((leviOfL3 N z).subgroupOf C ⊔ S.subgroupOf C) ∣
        (S.subgroupOf C).index :=
      Subgroup.relIndex_dvd_index_of_le le_sup_right
    exact hSC_idx (dvd_trans hd h3)
  have hKS := isSylowTwoOf_inf_normal614 hKcN hTs
  have hchain : (((S.subgroupOf C) ⊓ (leviOfL3 N z).subgroupOf C).subgroupOf
      ((leviOfL3 N z).subgroupOf C)).index = (S.subgroupOf (leviOfL3 N z)).index := by
    have e1 : ((S.subgroupOf C) ⊓ (leviOfL3 N z).subgroupOf C).relIndex
        ((leviOfL3 N z).subgroupOf C) = (S.subgroupOf C).relIndex ((leviOfL3 N z).subgroupOf C) :=
      Subgroup.inf_relIndex_right _ _
    have e2 : (S.subgroupOf C).relIndex ((leviOfL3 N z).subgroupOf C) =
        S.relIndex (leviOfL3 N z) := Subgroup.relIndex_subgroupOf hKC
    exact e1.trans e2
  rw [← hchain]
  exact hKS.2.2

end B2b

theorem false_of_L3FusFacts_five {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (h : L3FusFacts N 5) {y : G} {S : Subgroup G}
    (hyN : y ∈ N) (hy5 : orderOf y = 5) (hS : IsSylowTwoOf S N)
    (hSy : S ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hSc : ¬ S ≤ Subgroup.centralizer ({y} : Set G)) : False := by
  obtain ⟨z, hzS, hz2, -, hSz, hyK⟩ :=
    exists_involution_of_sylow_normalizes Nat.prime_five le_rfl h hyN hy5 hS hSy hSc
  have hzN : z ∈ N := hS.1 hzS
  have hK : IsL3Levi (leviOfL3 N z) z 5 := (h.levi z hzN hz2).1
  have hKidx : ¬ 2 ∣ (S.subgroupOf (leviOfL3 N z)).index :=
    not_two_dvd_index_levi_L3B2b hS hSz
  obtain ⟨F, _, _, σ, hF5, hσK, hσonto, hσker⟩ :=
    hK.exists_action Nat.prime_five le_rfl
  have hKo : IsOddPrimePower (Nat.card F) := by
    unfold IsOddPrimePower
    exact ⟨5, 1, Nat.prime_five, ⟨2, by norm_num⟩, le_rfl, by rw [hF5, pow_one]⟩
  have hcard : 3 < Nat.card F := by
    rw [hF5]
    norm_num
  have hyn : y ∈ Subgroup.normalizer (leviOfL3 N z : Set G) := Subgroup.le_normalizer hyK
  have hy5' : y ^ 5 = 1 := by
    rw [← hy5]
    exact pow_orderOf_eq_one y
  have hy1 : σ ⟨y, hyn⟩ ≠ 1 := by
    intro h1
    have hc : y ∈ Subgroup.centralizer (leviOfL3 N z : Set G) := hσker y hyn h1
    have hcen : (⟨y, hyK⟩ : ↥(leviOfL3 N z)) ∈ Subgroup.center ↥(leviOfL3 N z) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc (g : G) g.2
    rcases (hK.mem_center_iff ⟨y, hyK⟩).mp hcen with h2 | h2
    · have h3 : y = 1 := h2
      rw [h3, orderOf_one] at hy5
      norm_num at hy5
    · have h3 : y = z := h2
      rw [h3, hz2] at hy5
      norm_num at hy5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hσy5 : σ ⟨y, hyn⟩ ^ 5 = 1 := by
    have h5 : (⟨y, hyn⟩ : ↥(Subgroup.normalizer (leviOfL3 N z : Set G))) ^ 5 = 1 :=
      Subtype.ext (by simpa using hy5')
    rw [← map_pow, h5, map_one]
  have hy₂5 : orderOf (σ ⟨y, hyn⟩) = 5 := orderOf_eq_prime hσy5 hy1
  have hy₂N : σ ⟨y, hyn⟩ ∈ pGammaL2PSLRange F := hσK y hyK
  obtain ⟨f, hf⟩ : ∃ f : ↥(leviOfL3 N z) →* PGammaL2 F,
      ∀ k : ↥(leviOfL3 N z), f k = σ ⟨(k : G), Subgroup.le_normalizer k.2⟩ :=
    ⟨σ.comp (Subgroup.inclusion (Subgroup.le_normalizer :
      leviOfL3 N z ≤ Subgroup.normalizer (leviOfL3 N z : Set G))), fun k => rfl⟩
  have hfP : f.range = pGammaL2PSLRange F := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [hf k]
      exact hσK k.1 k.2
    · intro x hx
      obtain ⟨g, hg, rfl⟩ := hσonto x hx
      exact MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, hf ⟨g, hg⟩⟩
  have hker : f.ker ≤ S.subgroupOf (leviOfL3 N z) := by
    intro k hk
    rw [MonoidHom.mem_ker, hf k] at hk
    have hc : (k : G) ∈ Subgroup.centralizer (leviOfL3 N z : Set G) := hσker _ _ hk
    have hcen : k ∈ Subgroup.center ↥(leviOfL3 N z) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc (g : G) g.2
    rw [Subgroup.mem_subgroupOf]
    rcases (hK.mem_center_iff k).mp hcen with h2 | h2
    · rw [h2]
      exact S.one_mem
    · rw [h2]
      exact hzS
  have hDle : (S.subgroupOf (leviOfL3 N z)).map f ≤ pGammaL2PSLRange F := by
    intro d hd
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hd
    rw [← hfP]
    exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
  have hDrel : ((S.subgroupOf (leviOfL3 N z)).map f).relIndex (pGammaL2PSLRange F) =
      (S.subgroupOf (leviOfL3 N z)).index := by
    rw [← hfP]
    exact relIndex_map_range_L3B2b f _ hker
  have hDs : IsSylowTwoOf ((S.subgroupOf (leviOfL3 N z)).map f) (pGammaL2PSLRange F) := by
    refine ⟨hDle, isPGroup_map_L3B2b f (isPGroup_subgroupOf_L3B2b hS.2.1), ?_⟩
    show ¬ 2 ∣ (((S.subgroupOf (leviOfL3 N z)).map f).relIndex (pGammaL2PSLRange F))
    rw [hDrel]
    exact hKidx
  have hDy : (S.subgroupOf (leviOfL3 N z)).map f ≤
      Subgroup.normalizer (Subgroup.zpowers (σ ⟨y, hyn⟩) : Set (PGammaL2 F)) := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hd
    have hkS : (k : G) ∈ S := Subgroup.mem_subgroupOf.mp hk
    have hkN : (k : G) * y * (k : G)⁻¹ ∈ Subgroup.zpowers y :=
      (Subgroup.mem_normalizer_iff.mp (hSy hkS) y).mp (Subgroup.mem_zpowers y)
    have hkN' : (k : G)⁻¹ * y * ((k : G)⁻¹)⁻¹ ∈ Subgroup.zpowers y :=
      (Subgroup.mem_normalizer_iff.mp (hSy (S.inv_mem hkS)) y).mp (Subgroup.mem_zpowers y)
    apply mem_normalizer_zpowers_of_conj614
    · rw [hf k]
      exact map_conj_zpowers_L3B2b σ hyn ⟨(k : G), Subgroup.le_normalizer k.2⟩ hkN
    · have h2 := map_conj_zpowers_L3B2b σ hyn (⟨(k : G), Subgroup.le_normalizer k.2⟩⁻¹) hkN'
      rw [map_inv, inv_inv] at h2
      rw [hf k]
      exact h2
  exact false_of_le_normalizer_five614 hKo hcard (Or.inl hF5) hDs hy₂N hy₂5 hDy

end CFSG.Quasithin.H13
