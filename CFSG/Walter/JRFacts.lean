module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Walter.AStar.N1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.Walter

open scoped MatrixGroups
open CFSG.GorensteinWalter

open scoped IsMulCommutative in
theorem eq_one_of_mem_sylow_of_commute_normalizer_of_simple {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    [IsMulCommutative (S : Subgroup G)] {z : G} (hzS : z ∈ S)
    (hz : ∀ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * z = z * n) : z = 1 := by
  classical
  let φ : G →* S := MonoidHom.transfer (MonoidHom.id S)
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ hk
    obtain ⟨n, hn, heq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S (z ^ k) g₀
      (S.toSubgroup.pow_mem hzS k) hk
    rw [heq]
    have hc : Commute n (z ^ k) := Commute.pow_right (hz n hn) k
    rw [mul_assoc, ← hc.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hφz : φ z = ⟨z ^ (S : Subgroup G).index, _⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id S) z key
  have hker : φ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      apply (MonoidHom.ker_eq_bot_iff φ).mp h
      rw [map_mul, map_mul, mul_comm]
    · exact h
  have h1 : z ^ (S : Subgroup G).index = 1 := by
    have h : φ z = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top z)
    rw [hφz] at h
    exact congrArg Subtype.val h
  have h2 : orderOf z ∣ Nat.card (S : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hzS
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h2 S.card_coprime_index) (orderOf_dvd_of_pow_eq_one h1))

theorem disjoint_orbit_of_not_mem {A X : Type*} [Group A] [MulAction A X] {x y : X}
    (hy : y ∉ MulAction.orbit A x) : Disjoint (MulAction.orbit A x) (MulAction.orbit A y) := by
  rw [Set.disjoint_left]
  intro w hwx hwy
  have h1 : MulAction.orbit A w = MulAction.orbit A x := MulAction.orbit_eq_iff.mpr hwx
  have h2 : MulAction.orbit A w = MulAction.orbit A y := MulAction.orbit_eq_iff.mpr hwy
  exact hy (MulAction.orbit_eq_iff.mp (h2.symm.trans h1))

theorem orbit_eq_of_ncard_eq_seven {A X : Type*} [Group A] [MulAction A X] [Finite X]
    (T : Set X) (hT : T.ncard = 7) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hodd : ∀ x ∈ T, Odd (MulAction.orbit A x).ncard ∧ (MulAction.orbit A x).ncard ≠ 1) :
    ∀ x ∈ T, MulAction.orbit A x = T := by
  have hsub : ∀ x ∈ T, MulAction.orbit A x ⊆ T := by
    rintro x hx _ ⟨a, rfl⟩
    exact hTinv a x hx
  have hge : ∀ x ∈ T, 3 ≤ (MulAction.orbit A x).ncard := by
    intro x hx
    obtain ⟨⟨k, hk⟩, h1⟩ := hodd x hx
    omega
  intro x hx
  by_contra hne
  have hlt : (MulAction.orbit A x).ncard < 7 :=
    hT ▸ Set.ncard_lt_ncard (LE.le.ssubset_of_ne (hsub x hx) hne)
  obtain ⟨y, hyT, hyx⟩ : ∃ y ∈ T, y ∉ MulAction.orbit A x := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm (hsub x hx) h)
  have hxy : (MulAction.orbit A x ∪ MulAction.orbit A y).ncard =
      (MulAction.orbit A x).ncard + (MulAction.orbit A y).ncard :=
    Set.ncard_union_eq (disjoint_orbit_of_not_mem hyx)
  have hxyle : (MulAction.orbit A x ∪ MulAction.orbit A y).ncard ≤ 7 :=
    hT ▸ Set.ncard_le_ncard (Set.union_subset (hsub x hx) (hsub y hyT))
  have hx3 : (MulAction.orbit A x).ncard = 3 := by
    obtain ⟨⟨k, hk⟩, _⟩ := hodd x hx
    have := hge y hyT
    omega
  have hy3 : (MulAction.orbit A y).ncard = 3 := by
    obtain ⟨⟨k, hk⟩, _⟩ := hodd y hyT
    have := hge x hx
    omega
  obtain ⟨z, hzT, hzxy⟩ : ∃ z ∈ T, z ∉ MulAction.orbit A x ∪ MulAction.orbit A y := by
    by_contra h
    push Not at h
    have := Set.ncard_le_ncard h
    omega
  have hdz : Disjoint (MulAction.orbit A x ∪ MulAction.orbit A y) (MulAction.orbit A z) :=
    Disjoint.union_left (disjoint_orbit_of_not_mem fun h => hzxy (Or.inl h))
      (disjoint_orbit_of_not_mem fun h => hzxy (Or.inr h))
  have hall := Set.ncard_union_eq hdz
  have hallle : (MulAction.orbit A x ∪ MulAction.orbit A y ∪ MulAction.orbit A z).ncard ≤ 7 :=
    hT ▸ Set.ncard_le_ncard (Set.union_subset (Set.union_subset (hsub x hx) (hsub y hyT))
      (hsub z hzT))
  have := hge z hzT
  omega

theorem sylow_two_card_eight_transitive {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) (hS : IsMulCommutative (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 8) :
    (∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y) ∧
    ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      g ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      g ^ 7 ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
        ∃ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = y := by
  classical
  set Sg := (S : Subgroup G) with hSg
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set φ : N →* MulAut Sg := Sg.normalizerMonoidHom with hφ
  set A : Subgroup (MulAut Sg) := φ.range with hA
  have hφapp : ∀ (n : N) (x : Sg), ((φ n x : Sg) : G) = (n : G) * (x : G) * (n : G)⁻¹ :=
    fun _ _ => rfl
  have hcommS : ∀ a b : Sg, a * b = b * a := fun a b => hS.is_comm.comm a b
  have hAodd : Odd (Nat.card A) := by
    have hSN : Sg ≤ N := Subgroup.le_normalizer
    have hker : Sg.subgroupOf N ≤ φ.ker := by
      rw [hφ, Subgroup.normalizerMonoidHom_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hcommS ⟨y, hy⟩ ⟨x, hx⟩)
    have h1 : φ.ker.index = Nat.card A := Subgroup.index_ker φ
    have h2 : φ.ker.index ∣ (Sg.subgroupOf N).index := Subgroup.index_dvd_of_le hker
    have h3 : (Sg.subgroupOf N).index ∣ Sg.index := Subgroup.relIndex_dvd_index_of_le hSN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    rw [← h1] at h
    exact S.not_dvd_index (h.trans (h2.trans h3))
  have hfix : ∀ x : Sg, (∀ a : A, a • x = x) → x = 1 := by
    intro x hx
    apply Subtype.ext
    have : IsMulCommutative (S : Subgroup G) := hS
    refine eq_one_of_mem_sylow_of_commute_normalizer_of_simple hnonab S x.2 ?_
    intro n hn
    have h := congrArg Subtype.val (hx ⟨φ ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩)
    change (n : G) * x * n⁻¹ = x at h
    calc n * (x : G) = (n * x * n⁻¹) * n := by group
      _ = x * n := by rw [h]
  set T : Set Sg := {x | x ≠ 1} with hT
  have hTcard : T.ncard = 7 := by
    have : T = (Set.univ : Set Sg) \ {1} := by ext; simp [hT]
    rw [this, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcard]
  have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := by
    intro a x hx h
    apply hx
    have h' : (a : MulAut Sg) x = (a : MulAut Sg) 1 := by rw [map_one]; exact h
    exact (a : MulAut Sg).injective h'
  have horbit : ∀ x ∈ T, MulAction.orbit A x = T := by
    apply orbit_eq_of_ncard_eq_seven T hTcard hTinv
    intro x hx
    have hdvd : (MulAction.orbit A x).ncard ∣ Nat.card A := by
      rw [← MulAction.index_stabilizer]
      exact Subgroup.index_dvd_card _
    refine ⟨Odd.of_dvd_nat hAodd hdvd, fun h1 => hx (hfix x ?_)⟩
    intro a
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp h1
    have hxo : x ∈ MulAction.orbit A x := MulAction.mem_orbit_self x
    have hao : a • x ∈ MulAction.orbit A x := MulAction.mem_orbit x a
    rw [hy] at hxo hao
    rw [Set.mem_singleton_iff] at hxo hao
    rw [hao, hxo]
  have htrans : ∀ x ∈ Sg, x ≠ 1 → ∀ y ∈ Sg, y ≠ 1 → ∃ n ∈ N, n * x * n⁻¹ = y := by
    intro x hx hx1 y hy hy1
    have hxT : (⟨x, hx⟩ : Sg) ∈ T := fun h => hx1 (congrArg Subtype.val h)
    have hyT : (⟨y, hy⟩ : Sg) ∈ T := fun h => hy1 (congrArg Subtype.val h)
    rw [← horbit _ hxT] at hyT
    obtain ⟨⟨a, n, rfl⟩, ha⟩ := hyT
    exact ⟨n, n.2, congrArg Subtype.val ha⟩
  refine ⟨htrans, ?_⟩
  obtain ⟨x0, hx0⟩ : ∃ x0 : Sg, x0 ∈ T := by
    by_contra h
    push Not at h
    have : T = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
    rw [this, Set.ncard_empty] at hTcard
    omega
  have h7 : 7 ∣ Nat.card A := by
    have := MulAction.index_stabilizer A x0
    rw [horbit x0 hx0, hTcard] at this
    rw [← this]
    exact Subgroup.index_dvd_card _
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨π, hπ⟩ := exists_prime_orderOf_dvd_card' (G := A) 7 h7
  obtain ⟨n, hn⟩ := π.2
  have hφn : orderOf (φ n) = 7 := by rw [hn, Subgroup.orderOf_coe, hπ]
  have hker : ∀ m : N, φ m = 1 → (m : G) ∈ Subgroup.centralizer (Sg : Set G) := by
    intro m hm
    have : m ∈ φ.ker := hm
    rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨n, n.2, ?_, ?_, ?_⟩
  · intro hnC
    have : φ n = 1 := by
      ext x
      rw [hφapp]
      change (n : G) * x * (n : G)⁻¹ = x
      rw [(Subgroup.mem_centralizer_iff.mp hnC x x.2).symm, mul_inv_cancel_right]
    rw [this, orderOf_one] at hφn
    omega
  · have h := hker (n ^ 7) (by rw [map_pow, ← hφn, pow_orderOf_eq_one])
    simpa using h
  ·
    have : Fintype Sg := Fintype.ofFinite Sg
    set σ : Equiv.Perm Sg := MulAut.toPerm Sg (φ n) with hσ
    have hσord : orderOf σ = 7 := by
      rw [hσ, orderOf_injective (MulAut.toPerm Sg) (fun a b h => by
        ext x; exact congrArg Subtype.val (Equiv.congr_fun h x)), hφn]
    have hcyc : σ.IsCycle := by
      apply Equiv.Perm.isCycle_of_prime_order' (by rw [hσord]; decide)
      rw [hσord, ← Nat.card_eq_fintype_card, hcard]
      norm_num
    have hsupp : σ.support.card = 7 := by rw [← hcyc.orderOf, hσord]
    have hmove : ∀ x : Sg, x ≠ 1 → σ x ≠ x := by
      intro x hx hσx
      have h1 : σ 1 = 1 := map_one (φ n)
      have hsub : σ.support ⊆ (Finset.univ.erase (1 : Sg)).erase x := by
        intro y hy
        rw [Equiv.Perm.mem_support] at hy
        refine Finset.mem_erase.mpr ⟨fun h => hy (h ▸ hσx), Finset.mem_erase.mpr
          ⟨fun h => hy (h ▸ h1), Finset.mem_univ y⟩⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hcard, hsupp] at this
      omega
    intro x hx hx1 y hy hy1
    have hx1' : (⟨x, hx⟩ : Sg) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hy1' : (⟨y, hy⟩ : Sg) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := hcyc.exists_pow_eq (hmove _ hx1') (hmove _ hy1')
    refine ⟨k, ?_⟩
    have h := congrArg Subtype.val hk
    rw [hσ, ← map_pow, ← map_pow] at h
    change ((φ (n ^ k) ⟨x, hx⟩ : Sg) : G) = y at h
    rw [hφapp] at h
    simpa using h

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {t c : G} (ht : orderOf t = 2)
    (hc : c ∈ Subgroup.zpowers t) : c = 1 ∨ c = t := by
  obtain ⟨k, rfl⟩ := hc
  simp only
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem mem_normalizer_of_mem_centralizer {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (H : Set G)) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_centralizer_iff] at hx
  constructor
  · intro hh
    rw [← hx h hh, mul_inv_cancel_right]
    exact hh
  · intro hh
    have := hx _ hh
    have heq : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [this]
        _ = x * h * x⁻¹ := by group
    rw [heq]
    exact hh

theorem mod_eight_of_psl2_order_factorization_two {q : ℕ} (hq : Odd q) (hq1 : 1 < q)
    (h : (q * (q ^ 2 - 1) / 2).factorization 2 = 2) : q % 8 = 3 ∨ q % 8 = 5 := by
  have hq8 : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
    have := Nat.odd_iff.mp hq
    omega
  rcases hq8 with h8 | h8 | h8 | h8
  · exfalso
    rw [psl2_order_two_factorization_split hq hq1 (Nat.even_iff.mpr (by omega))] at h
    have h4 : 2 ^ 2 ∣ (q - 1) / 2 := ⟨(q - 1) / 8, by omega⟩
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h4
    omega
  · exact Or.inl h8
  · exact Or.inr h8
  · exfalso
    rw [psl2_order_two_factorization_nonsplit hq hq1 (Nat.odd_iff.mpr (by omega))] at h
    have h4 : 2 ^ 2 ∣ (q + 1) / 2 := ⟨(q + 1) / 8, by omega⟩
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h4
    omega

theorem psl2_exists_mul_ne_mul (K : Type*) [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ a b : PSL(2, K), a * b ≠ b * a := by
  have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK
  by_contra h
  push Not at h
  have hZ : Subgroup.center PSL(2, K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact h _ _
  rw [psl2_center_eq_bot] at hZ
  exact bot_ne_top hZ

theorem exists_mul_ne_mul_of_mulEquiv_psl2 {G : Type*} [Group G] {K : Type*} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) {L : Subgroup G} (e : L ≃* PSL(2, K)) :
    ∃ a b : L, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := psl2_exists_mul_ne_mul K hK
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

section JR

variable {G : Type} [Group G] [Finite G]

theorem IsTypeJR.sylow_two_of_mem (hG : IsTypeJR G) (S : Sylow 2 G) {t : G}
    (htS : t ∈ (S : Subgroup G)) (ht : orderOf t = 2) {p f : ℕ} [Fact p.Prime] (L : Subgroup G)
    (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (hLC : L ≤ Subgroup.centralizer ({t} : Set G))
    (hLn : (L.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (e : L ≃* PSL(2, GaloisField p f))
    (hCL : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers t) :
    Nat.card ((S : Subgroup G) ⊓ L : Subgroup G) = 4 ∧
      (∀ x ∈ (S : Subgroup G), x ^ 2 = 1) ∧ Nat.card (S : Subgroup G) = 8 ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) := by
  classical
  set K := GaloisField p f
  have hK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set Sg := (S : Subgroup G) with hSg
  have hS : IsMulCommutative Sg := hG.2.1 S
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have : IsSimpleGroup PSL(2, K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have : IsSimpleGroup L := e.isSimpleGroup
  have hLnonab : ∃ a b : L, a * b ≠ b * a :=
    exists_mul_ne_mul_of_mulEquiv_psl2 (by rw [GaloisField.card p f hf.ne']; omega) e
  have hSC : Sg ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hS.is_comm.comm ⟨s, hs⟩ ⟨t, htS⟩))
  have hCN : C ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mp hLn
  have hinner := exists_inner_of_sylow_le_normalizer hG.2.1 L hLnonab S (hSC.trans hCN)
  have htCL : t ∈ Subgroup.centralizer (L : Set G) :=
    (show t ∈ C ⊓ Subgroup.centralizer (L : Set G) from hCL ▸ Subgroup.mem_zpowers t).2
  have htL : t ∉ L := by
    intro htL
    have hZ : (⟨t, htL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp htCL) g g.2)
    rw [center_eq_bot_of_isSimpleGroup hLnonab, Subgroup.mem_bot] at hZ
    have h1 : t = 1 := congrArg Subtype.val hZ
    rw [h1, orderOf_one] at ht
    omega
  have hdich : ∀ s ∈ Sg, s ∈ L ∨ s * t ∈ L := by
    intro s hs
    obtain ⟨k, hkL, hk⟩ := hinner s hs
    have hc : k⁻¹ * s ∈ C ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨C.mul_mem (C.inv_mem (hLC hkL)) (hSC hs), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * (k⁻¹ * s) = k⁻¹ * (k * x * k⁻¹) * s := by group
        _ = k⁻¹ * (s * x * s⁻¹) * s := by rw [hk x hx]
        _ = k⁻¹ * s * x := by group
    rw [hCL] at hc
    rcases eq_one_or_eq_of_mem_zpowers ht hc with h | h
    · left
      rw [← inv_mul_eq_one.mp h]
      exact hkL
    · right
      rw [inv_mul_eq_iff_eq_mul.mp h, mul_assoc, ht2, mul_one]
      exact hkL
  have hSLp : IsPGroup 2 ((Sg ⊓ L).subgroupOf L) :=
    (S.isPGroup'.to_inf_left (K := L)).comap_subtype
  obtain ⟨P0, hP0⟩ := hSLp.exists_le_sylow
  set P : Subgroup G := (P0 : Subgroup L).map L.subtype with hP
  have hPL : P ≤ L := Subgroup.map_subtype_le _
  have hSLP : Sg ⊓ L ≤ P := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, hP0 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hPp : IsPGroup 2 P := P0.isPGroup'.map L.subtype
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htN : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]
    apply mem_normalizer_of_mem_centralizer
    exact Subgroup.centralizer_le (show (P : Set G) ⊆ L from hPL) htCL
  have hQp : IsPGroup 2 (P ⊔ Subgroup.zpowers t : Subgroup G) := by
    rw [sup_comm]
    exact htp.to_sup_of_normal_right' hPp htN
  have hSQ : Sg ≤ P ⊔ Subgroup.zpowers t := by
    intro s hs
    rcases hdich s hs with h | h
    · exact le_sup_left (a := P) (hSLP ⟨hs, h⟩)
    · have hst : s * t ∈ P := hSLP ⟨Sg.mul_mem hs htS, h⟩
      have : s = (s * t) * t := by rw [mul_assoc, ht2, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (le_sup_left (a := P) hst)
        (le_sup_right (a := P) (Subgroup.mem_zpowers t))
  have hPS : P ≤ Sg :=
    calc P ≤ P ⊔ Subgroup.zpowers t := le_sup_left
      _ = Sg := S.is_maximal' hQp hSQ
  have hPeq : Sg ⊓ L = P := le_antisymm hSLP (le_inf hPS hPL)
  let Q : Sylow 2 PSL(2, K) := P0.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup PSL(2, K)) = (P0 : Subgroup L).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  let eQ : (P0 : Subgroup L) ≃* (Q : Subgroup PSL(2, K)) :=
    (e.subgroupMap (P0 : Subgroup L)).trans (MulEquiv.subgroupCongr hQ.symm)
  let eP : (P0 : Subgroup L) ≃* P :=
    Subgroup.equivMapOfInjective (P0 : Subgroup L) L.subtype L.subtype_injective
  have hQcomm : ∀ a b : (Q : Subgroup PSL(2, K)), a * b = b * a := by
    intro a b
    apply eQ.symm.injective
    apply eP.injective
    rw [map_mul, map_mul, map_mul, map_mul]
    have ha := hPS (eP (eQ.symm a)).2
    have hb := hPS (eP (eQ.symm b)).2
    have h := congrArg (fun x : Sg => (x : G)) (hS.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    exact Subtype.ext h
  obtain ⟨m, hm, ⟨d⟩⟩ :=
    psl2_odd_hasDihedralSylowTwo_model K (isOddPrimePower_of_card hK hp hf) Q
  have hdcomm : IsMulCommutative (DihedralGroup (2 ^ m)) := ⟨⟨fun x y => d.symm.injective (by
    rw [map_mul, map_mul]; exact hQcomm _ _)⟩⟩
  have h2m : 2 ^ m = 2 := by
    rcases DihedralGroup.commutative_iff.mp hdcomm with h | h
    · exfalso
      have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega
    · exact h
  rw [h2m] at d
  have hQcard : Nat.card (Q : Subgroup PSL(2, K)) = 4 :=
    (Nat.card_congr d.toEquiv).trans DihedralGroup.nat_card
  have hQexp : ∀ y : (Q : Subgroup PSL(2, K)), y ^ 2 = 1 := by
    intro y
    apply d.injective
    rw [map_pow, map_one]
    have := Monoid.pow_exponent_eq_one (d y)
    rwa [IsKleinFour.exponent_two] at this
  have hSLcard : Nat.card (Sg ⊓ L : Subgroup G) = 4 := by
    rw [hPeq, ← Nat.card_congr eP.toEquiv, Nat.card_congr eQ.toEquiv, hQcard]
  have hSLexp : ∀ x ∈ Sg ⊓ L, x ^ 2 = 1 := by
    intro x hx
    rw [hPeq] at hx
    obtain ⟨a, ha⟩ := eP.surjective ⟨x, hx⟩
    have h' : a ^ 2 = 1 := eQ.injective (by rw [map_pow, map_one]; exact hQexp (eQ a))
    have hx' : ((eP a : P) : G) = x := congrArg Subtype.val ha
    rw [← hx', ← Subgroup.coe_pow, ← map_pow, h', map_one, Subgroup.coe_one]
  have hfact : (Nat.card PSL(2, K)).factorization 2 = 2 := by
    have h := Q.card_eq_multiplicity
    rw [hQcard] at h
    have h' : 2 ^ 2 = 2 ^ (Nat.card PSL(2, K)).factorization 2 := by rw [← h]; norm_num
    exact (Nat.pow_right_injective le_rfl h').symm
  rw [psl2_card_formula K (isOddPrimePower_of_card hK hp hf), hK] at hfact
  have hmod := mod_eight_of_psl2_order_factorization_two hp.pow (by omega) hfact
  have hSexp : ∀ x ∈ Sg, x ^ 2 = 1 := by
    intro x hx
    rcases hdich x hx with h | h
    · exact hSLexp x ⟨hx, h⟩
    · have h1 := hSLexp (x * t) ⟨Sg.mul_mem hx htS, h⟩
      have hcomm : Commute x t := congrArg Subtype.val (hS.is_comm.comm ⟨x, hx⟩ ⟨t, htS⟩)
      rwa [hcomm.mul_pow, pow_two t, ht2, mul_one] at h1
  have hindex : L.relIndex Sg = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htS⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hdich b b.2 with h | h
    · exact Or.inr ⟨h, fun h' => htL (by simpa using L.mul_mem (L.inv_mem h) h')⟩
    · exact Or.inl ⟨h, fun h' => htL (by simpa using L.mul_mem (L.inv_mem h') h)⟩
  have hScard : Nat.card Sg = 8 := by
    have := Subgroup.relIndex_mul_card L Sg
    rw [hindex, inf_comm, hSLcard] at this
    omega
  exact ⟨hSLcard, hSexp, hScard, hmod⟩

omit [Finite G] in
theorem IsTypeJR.exists_mul_ne_mul (hG : IsTypeJR G) {t : G} (ht : orderOf t = 2) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨-, p, f, hpf, L, -, hf, h5, -, -, ⟨e⟩, -⟩ := hG.2.2 t ht
  obtain ⟨a, b, hab⟩ :=
    exists_mul_ne_mul_of_mulEquiv_psl2 (by rw [GaloisField.card p f hf.ne']; omega) e
  exact ⟨a, b, fun h => hab (Subtype.ext h)⟩

theorem IsTypeJR.sylow_two (hG : IsTypeJR G) (h2 : 2 ∣ Nat.card G) (S : Sylow 2 G) :
    IsElementaryAbelian 2 (S : Subgroup G) ∧ Nat.card (S : Subgroup G) = 8 := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (S.dvd_card_of_dvd_card h2)
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨-, p, f, hpf, L, hp, hf, h5, hLC, hLn, ⟨e⟩, hCL⟩ := hG.2.2 t ht'
  obtain ⟨-, hexp, hcard, -⟩ := hG.sylow_two_of_mem S t.2 ht' L hp hf h5 hLC hLn e hCL
  refine ⟨{ toIsMulCommutative := hG.2.1 S, exponent_dvd_p := ?_ }, hcard⟩
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro g
  exact Subtype.ext (hexp g g.2)

theorem IsTypeJR.mod_eight (hG : IsTypeJR G) {t : G} (ht : orderOf t = 2) {p f : ℕ}
    [Fact p.Prime] (L : Subgroup G) (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f)
    (hLC : L ≤ Subgroup.centralizer ({t} : Set G))
    (hLn : (L.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (e : L ≃* PSL(2, GaloisField p f))
    (hCL : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers t) :
    p ^ f % 8 = 3 ∨ p ^ f % 8 = 5 := by
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := htp.exists_le_sylow
  exact (hG.sylow_two_of_mem S (hS (Subgroup.mem_zpowers t)) ht L hp hf h5 hLC hLn e hCL).2.2.2

omit [Finite G] in
theorem IsTypeJR.center_centralizer (hG : IsTypeJR G) {t : G} (ht : orderOf t = 2) :
    (Subgroup.center (Subgroup.centralizer ({t} : Set G))).map
      (Subgroup.centralizer ({t} : Set G)).subtype = Subgroup.zpowers t := by
  obtain ⟨-, p, f, hpf, L, -, -, -, hLC, -, -, hCL⟩ := hG.2.2 t ht
  apply le_antisymm
  · rw [← hCL]
    rintro _ ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x, hLC hx⟩)
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_map.mpr ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
      Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

theorem IsTypeJR.normalizer_sylow_two_transitive (hG : IsTypeJR G) (h2 : 2 ∣ Nat.card G)
    (S : Sylow 2 G) :
    ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y := by
  have : IsSimpleGroup G := hG.1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2
  exact (sylow_two_card_eight_transitive (hG.exists_mul_ne_mul ht) S (hG.2.1 S)
    (hG.sylow_two h2 S).2).1

theorem IsTypeJR.isConj_of_orderOf_eq_two (hG : IsTypeJR G) {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  have h2 : 2 ∣ Nat.card G := hx ▸ orderOf_dvd_natCard x
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hyp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Sx, hSx⟩ := hxp.exists_le_sylow
  obtain ⟨Sy, hSy⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sx Sy
  have hxS : x ∈ (Sx : Subgroup G) := hSx (Subgroup.mem_zpowers x)
  have hyS : y ∈ ((g • Sx : Sylow 2 G) : Subgroup G) := hg ▸ hSy (Subgroup.mem_zpowers y)
  have hy' : g⁻¹ * y * g ∈ (Sx : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    simpa [MulAut.smul_def, MulAut.conj_apply] using hyS
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx
  have hy1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply (show y ≠ 1 by rintro rfl; simp at hy)
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨n, -, hn⟩ := hG.normalizer_sylow_two_transitive h2 Sx x hxS hx1 _ hy' hy1
  refine isConj_iff.mpr ⟨g * n, ?_⟩
  calc g * n * x * (g * n)⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [hn]
    _ = y := by group

theorem IsTypeJR.exists_normalizer_sylow_two_transitive (hG : IsTypeJR G) (h2 : 2 ∣ Nat.card G)
    (S : Sylow 2 G) :
    ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      g ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      g ^ 7 ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
        ∃ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = y := by
  have : IsSimpleGroup G := hG.1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2
  exact (sylow_two_card_eight_transitive (hG.exists_mul_ne_mul ht) S (hG.2.1 S)
    (hG.sylow_two h2 S).2).2

theorem IsTypeJR.two_dvd_card (hG : IsTypeJR G) (hnonab : ∃ a b : G, a * b ≠ b * a) :
    2 ∣ Nat.card G :=
  have : IsSimpleGroup G := hG.1
  (even_card_of_isSimpleGroup hnonab).two_dvd

theorem IsTypeJR.sylow_two_of_nonabelian (hG : IsTypeJR G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) :
    IsElementaryAbelian 2 (S : Subgroup G) ∧ Nat.card (S : Subgroup G) = 8 :=
  hG.sylow_two (hG.two_dvd_card hnonab) S

theorem IsTypeJR.normalizer_sylow_two_transitive_of_nonabelian (hG : IsTypeJR G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) :
    ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n * x * n⁻¹ = y :=
  hG.normalizer_sylow_two_transitive (hG.two_dvd_card hnonab) S

theorem IsTypeJR.exists_normalizer_sylow_two_transitive_of_nonabelian (hG : IsTypeJR G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) :
    ∃ g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      g ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      g ^ 7 ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      ∀ x ∈ (S : Subgroup G), x ≠ 1 → ∀ y ∈ (S : Subgroup G), y ≠ 1 →
        ∃ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = y :=
  hG.exists_normalizer_sylow_two_transitive (hG.two_dvd_card hnonab) S

end JR

end CFSG.Walter
