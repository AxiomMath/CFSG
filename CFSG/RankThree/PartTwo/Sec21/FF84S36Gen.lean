module

public import CFSG.Walter.Cited.SuzukiCases
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure F6Data (b : G) (L B : Subgroup G) (b₁ b₂ t : G) : Prop where
  sec : FF84Sec3 b L B b₁ b₂
  ht : orderOf t = 2
  htL : t ∈ CenS L
  htb : t * b * t⁻¹ = b⁻¹
  hN : Subgroup.closure {b, t} ⊔ L = Nor (Subgroup.zpowers b)

theorem S36_comm_of_cen {x c : G} (h : x ∈ Cen c) : c * x = x * c :=
  (Subgroup.mem_centralizer_singleton_iff.1 h).symm

theorem S36_mem_cen_of {x c : G} (h : c * x = x * c) : x ∈ Cen c :=
  Subgroup.mem_centralizer_singleton_iff.2 h.symm

theorem S36_sq_of_orderOf_two {t : G} (ht : orderOf t = 2) : t ^ 2 = 1 := by
  rw [← ht]
  exact pow_orderOf_eq_one t

theorem S36_sq_eq_inv {b₂ : G} (h3 : b₂ ^ 3 = 1) : b₂ ^ 2 = b₂⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← pow_succ']; exact h3)

theorem S36_sq_zpowers {t : G} (ht : orderOf t = 2) {z : G} (hz : z ∈ Subgroup.zpowers t) :
    z ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have ht2 : t ^ ((2 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    exact S36_sq_of_orderOf_two ht
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, ht2, one_zpow]

theorem S36_isPGroup_zpowers {t : G} (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using S36_sq_zpowers ht g.2

theorem S36_isPGroup_mono {N P : Subgroup G} (hP : IsPGroup 2 P) (h : N ≤ P) :
    IsPGroup 2 N := by
  intro g
  obtain ⟨k, hk⟩ := hP ⟨g, h g.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem S36_op2_le (H : Subgroup G) : Op 2 H ≤ H := by
  intro x hx
  have hx' : x ∈ (pCore 2 H).map H.subtype := hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx'
  exact y.2

theorem S36_op2_isPGroup (H : Subgroup G) : IsPGroup 2 (Op 2 H) := by
  intro g
  have hg2 : (g : G) ∈ (pCore 2 H).map H.subtype := g.2
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hg2
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨y, hy⟩
  have h2 : (y : G) ^ 2 ^ k = 1 := by
    have h1 := congrArg (fun z : ↥(pCore 2 H) => ((z : H) : G)) hk
    simpa using h1
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [show (g : G) = (y : G) from hyg.symm]
  exact h2

theorem S36_op2_of_normal {H N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hp : IsPGroup 2 N) : N ≤ Op 2 H := by
  have hp' : IsPGroup 2 (N.subgroupOf H) := by
    intro g
    obtain ⟨k, hk⟩ := hp ⟨(g : G), Subgroup.mem_subgroupOf.1 g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have hle : N.subgroupOf H ≤ pCore 2 H := le_sSup ⟨hN, hp'⟩
  intro x hx
  show x ∈ (pCore 2 H).map H.subtype
  exact Subgroup.mem_map.2 ⟨⟨x, hNH hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem S36_op2_conj {H : Subgroup G} {g x : G} (hg : g ∈ H) (hx : x ∈ Op 2 H) :
    g * x * g⁻¹ ∈ Op 2 H := by
  have hx' : x ∈ (pCore 2 H).map H.subtype := hx
  show g * x * g⁻¹ ∈ (pCore 2 H).map H.subtype
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx'
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : H) * y * (⟨g, hg⟩ : H)⁻¹, ?_, ?_⟩
  · exact (pCore_normal (p := 2) (G := H)).conj_mem y hy _
  · simp

theorem S36_zpowers_op2 {H : Subgroup G} {t : G} (ht : orderOf t = 2) (htH : t ∈ H)
    (hcomm : ∀ g ∈ H, Commute g t) : Subgroup.zpowers t ≤ Op 2 H := by
  apply S36_op2_of_normal (Subgroup.zpowers_le.2 htH)
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : (g : G) * t ^ k = t ^ k * (g : G) := ((hcomm (g : G) g.2).zpow_right k).eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hk, hc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
  · exact S36_isPGroup_zpowers ht

theorem S36_centre_trivial {K : Subgroup G} (hK : Nat.card K = 60) (hKs : IsSimpleGroup K)
    {z : G} (hz : z ∈ K) (hc : ∀ k ∈ K, z * k = k * z) : z = 1 := by
  have h := CFSG.Walter.Suzuki.eq_one_of_central_of_card_sixty (X := K) hK
    (z := (⟨z, hz⟩ : K)) (fun y => Subtype.ext (hc y y.2))
  exact congrArg Subtype.val h

theorem S36_cen_le_nor (c' : G) : Cen c' ≤ Nor (Subgroup.zpowers c') := by
  have fwd : ∀ y ∈ Cen c', ∀ n ∈ Subgroup.zpowers c', y * n * y⁻¹ ∈ Subgroup.zpowers c' := by
    intro y hy n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : y * c' * y⁻¹ = c' := by
      have := S36_comm_of_cen hy
      rw [← this]
      group
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← conj_zpow, hc]⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact fwd x hx n
  · intro hn
    have h := fwd x⁻¹ (Subgroup.inv_mem _ hx) _ hn
    have e : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
    rwa [e] at h

theorem S36_closure_zpowers {b t x : G} (hb3 : orderOf b = 3) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (hx : x ∈ Subgroup.closure ({b, t} : Set G))
    (hxt : t * x = x * t) : x ∈ Subgroup.zpowers t := by
  have hsub : Subgroup.closure ({b, t} : Set G) ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers t := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hfwd : ∀ n ∈ Subgroup.zpowers b, t * n * t⁻¹ ∈ Subgroup.zpowers b := by
    intro n hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
    have h := conj_zpow (a := t) (b := b) (i := k)
    rw [htb, inv_zpow] at h
    rw [← h, zpow_neg]
  have htN : Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hfwd n
    · intro hn
      have h := hfwd _ hn
      have e : t * (t * n * t⁻¹) * t⁻¹ = n := by
        have : t * (t * n * t⁻¹) * t⁻¹ = (t * t) * n * (t * t)⁻¹ := by group
        rw [this, ← pow_two, S36_sq_of_orderOf_two ht2]
        simp
      rwa [e] at h
  have hx' : x ∈ (↑(Subgroup.zpowers b ⊔ Subgroup.zpowers t) : Set G) := hsub hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ htN, Set.mem_mul] at hx'
  obtain ⟨y, hy, z, hz, hyz⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  have key : t * b ^ i = b ^ (-i) * t := by
    have h := conj_zpow (a := t) (b := b) (i := i)
    rw [htb, inv_zpow, ← zpow_neg] at h
    calc t * b ^ i = t * b ^ i * t⁻¹ * t := by group
      _ = b ^ (-i) * t := by rw [← h]
  have hcomm_tj : t * t ^ j = t ^ j * t := ((Commute.refl t).zpow_right j).eq
  rw [← hyz] at hxt
  rw [← hyz]
  have e1 : b ^ (-i) * (t * t ^ j) = b ^ i * (t * t ^ j) := by
    calc b ^ (-i) * (t * t ^ j) = (t * b ^ i) * t ^ j := by rw [key, mul_assoc]
      _ = t * (b ^ i * t ^ j) := by rw [mul_assoc]
      _ = b ^ i * t ^ j * t := hxt
      _ = b ^ i * (t * t ^ j) := by rw [mul_assoc, ← hcomm_tj]
  have hbi : b ^ (-i) = b ^ i := mul_right_cancel e1
  have h2i : b ^ (2 * i) = 1 := by
    calc b ^ (2 * i) = b ^ i * b ^ i := by rw [two_mul, zpow_add]
      _ = b ^ (-i) * b ^ i := by rw [hbi]
      _ = 1 := by rw [zpow_neg, inv_mul_cancel]
  have hdvd : ((orderOf b : ℕ) : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.2 h2i
  rw [hb3] at hdvd
  have h3i : (3 : ℤ) ∣ i := by
    push_cast at hdvd
    omega
  have hbi1 : b ^ i = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.1
    rw [hb3]
    exact_mod_cast h3i
  rw [hbi1, one_mul]
  exact Subgroup.mem_zpowers_iff.2 ⟨j, rfl⟩

theorem S36_cen_eq {b t c' : G} {L : Subgroup G} (hb3 : orderOf b = 3) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (hbL : ∀ l ∈ L, b * l = l * b) (htL : ∀ l ∈ L, t * l = l * t)
    (hN : Subgroup.closure ({b, t} : Set G) ⊔ L = Nor (Subgroup.zpowers b)) (hcL : c' ∈ L)
    (hC : Cen c' ≤ Nor (Subgroup.zpowers b)) :
    Cen t ⊓ Cen c' = Subgroup.zpowers t ⊔ (L ⊓ Cen c') := by
  have hD : Subgroup.closure ({b, t} : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rcases hy with rfl | rfl
    · intro l hl; exact (hbL l hl).symm
    · intro l hl; exact (htL l hl).symm
  have hLN : Subgroup.closure ({b, t} : Set G) ≤ Nor L :=
    hD.trans (Subgroup.centralizer_le_normalizer _)
  have hsplit : ∀ x ∈ Nor (Subgroup.zpowers b), ∃ g ∈ Subgroup.closure ({b, t} : Set G),
      ∃ l ∈ L, x = g * l := by
    intro x hx
    rw [← hN] at hx
    have hx' : x ∈ (↑(Subgroup.closure ({b, t} : Set G) ⊔ L) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN, Set.mem_mul] at hx'
    obtain ⟨g, hg, l, hl, hgl⟩ := hx'
    exact ⟨g, hg, l, hl, hgl.symm⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨hxt, hxc⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨g, hg, l, hl, rfl⟩ := hsplit _ (hC hxc)
    have hxt' : t * (g * l) = (g * l) * t := S36_comm_of_cen hxt
    have hxc' : c' * (g * l) = (g * l) * c' := S36_comm_of_cen hxc
    have hlt : t * l = l * t := htL l hl
    have hgt : t * g = g * t := by
      have h1 : t * g * l = g * t * l := by
        calc t * g * l = t * (g * l) := mul_assoc _ _ _
          _ = (g * l) * t := hxt'
          _ = g * (l * t) := mul_assoc _ _ _
          _ = g * (t * l) := by rw [hlt]
          _ = g * t * l := (mul_assoc _ _ _).symm
      exact mul_right_cancel h1
    have hgc : c' * g = g * c' := Subgroup.mem_centralizer_iff.1 (hD hg) c' hcL
    have hlc : c' * l = l * c' := by
      have h1 : g * (c' * l) = g * (l * c') := by
        calc g * (c' * l) = (g * c') * l := (mul_assoc _ _ _).symm
          _ = (c' * g) * l := by rw [← hgc]
          _ = c' * (g * l) := mul_assoc _ _ _
          _ = (g * l) * c' := hxc'
          _ = g * (l * c') := mul_assoc _ _ _
      exact mul_left_cancel h1
    have hgz := S36_closure_zpowers hb3 ht2 htb hg hgt
    exact mul_mem (Subgroup.mem_sup_left hgz)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hl, S36_mem_cen_of hlc⟩))
  · apply sup_le
    · exact Subgroup.zpowers_le.2 (Subgroup.mem_inf.2
        ⟨S36_mem_cen_of rfl, S36_mem_cen_of (htL c' hcL).symm⟩)
    · intro x hx
      obtain ⟨hxL, hxc⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨S36_mem_cen_of (htL x hxL), hxc⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
