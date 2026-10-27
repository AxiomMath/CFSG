module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

private theorem exists_mul_of_mem_sup_of_normal_subgroupOf {G : Type} [Group G]
    {C K Z : Subgroup G} (hK : (K.subgroupOf C).Normal) (hKC : K ≤ C) (hZC : Z ≤ C)
    (hsup : K ⊔ Z = C) {y : G} (hy : y ∈ C) :
    ∃ k ∈ K, ∃ z ∈ Z, k * z = y := by
  have hKinst : (K.subgroupOf C).Normal := hK
  have hsub : K.subgroupOf C ⊔ Z.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKC hZC, hsup, Subgroup.subgroupOf_self]
  have hy' : (⟨y, hy⟩ : ↥C) ∈ K.subgroupOf C ⊔ Z.subgroupOf C := by
    rw [hsub]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup_of_normal_left.mp hy'
  exact ⟨k, Subgroup.mem_subgroupOf.mp hk, z, Subgroup.mem_subgroupOf.mp hz,
    congrArg Subtype.val hkz⟩

private theorem cube_eq_one_of_mem_sup_zpowers {G : Type} [Group G] {a b x : G}
    (hab : Commute a b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : x ^ 3 = 1 := by
  have hcomm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right hab n).eq.symm)).trans (Subgroup.centralizer_le_normalizer _)
  change x ∈ (↑(Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Set G) at hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcomm, Set.mem_mul] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  have hya : y ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hy).trans
      (orderOf_dvd_iff_pow_eq_one.mpr ha))
  have hzb : z ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_mem_zpowers hz).trans
      (orderOf_dvd_iff_pow_eq_one.mpr hb))
  have hyz : Commute y z := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (Commute.zpow_right hab n) m
  rw [Commute.mul_pow hyz 3, hya, hzb, mul_one]

private theorem mem_zpowers_of_mem_inf_of_cube_eq_one {G : Type} [Group G] [Finite G]
    {b₀ : G} {K : Subgroup G} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    {w : G} (hw : w ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))
    (hw3 : w ^ 3 = 1) : w ∈ Subgroup.zpowers b₀ := by
  obtain ⟨hwC, hwK⟩ := Subgroup.mem_inf.mp hw
  set S : Subgroup G := Subgroup.zpowers w ⊔ Subgroup.zpowers b₀ with hS
  have hb₀K : b₀ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hSle : S ≤ Subgroup.centralizer (K : Set G) := by
    rw [hS]
    exact sup_le (Subgroup.zpowers_le.mpr hwK) (Subgroup.zpowers_le.mpr hb₀K)
  have hPw : IsPGroup 3 (Subgroup.zpowers w : Subgroup G) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [pow_one, Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hw3)
  have hPb : IsPGroup 3 (Subgroup.zpowers b₀ : Subgroup G) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [pow_one, Nat.card_zpowers, hb₀])
  have hwcomm : Commute w b₀ := Subgroup.mem_centralizer_singleton_iff.mp hwC
  have hwcentral : w ∈ Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right hwcomm i).eq.symm
  have hcomm : Subgroup.zpowers w ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) :=
    (Subgroup.zpowers_le.mpr hwcentral).trans (Subgroup.centralizer_le_normalizer _)
  have hSP : IsPGroup 3 S := by
    rw [hS]
    exact hPw.to_sup_of_normal_right' hPb hcomm
  have hcycS : IsCyclic ↥S := hcyc S hSle hSP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥S)
  have hg3 : g ^ 3 = 1 := by
    have h3 : (g : G) ^ 3 = 1 :=
      cube_eq_one_of_mem_sup_zpowers hwcomm hw3 hb₀3 g.2
    exact Subtype.ext h3
  have hSdvd : Nat.card ↥S ∣ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_iff_pow_eq_one.mpr hg3
  have hbS : Subgroup.zpowers b₀ ≤ S := by rw [hS]; exact le_sup_right
  have h3dvd : 3 ∣ Nat.card ↥S := by
    have := Subgroup.card_dvd_of_le hbS
    rwa [Nat.card_zpowers, hb₀] at this
  have hScard : Nat.card ↥S = 3 := Nat.dvd_antisymm hSdvd h3dvd
  have hSeq : S = Subgroup.zpowers b₀ :=
    (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers b₀) (K := S) hbS
      (by rw [hScard, Nat.card_zpowers, hb₀])).symm
  have hwS : w ∈ S := by rw [hS]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  rwa [hSeq] at hwS

private theorem not_exists_pow_three_eq_of_mem_inf {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hE : IsElemAbelian 3 E) (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hself : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K)
    (hN : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))
    (hout : Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))) :
    ¬ ∃ x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G), x ^ 3 = b₀ := by
  classical
  rintro ⟨x, hxZ, hx3⟩
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hC
  set Z₀ : Subgroup G :=
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) with hZ₀
  obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hxZ
  have hb₀E : b₀ ∈ E := by
    rw [← hsup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hb₀K : b₀ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  have hxE : x ∈ Subgroup.centralizer (E : Set G) := by
    refine Subgroup.zpowers_le.mp (Subgroup.le_centralizer_iff.mp ?_)
    rw [← hsup]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hxC) m).eq
    · intro e he
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left
        (Commute.symm (Subgroup.mem_centralizer_iff.mp hxK e he.2)) m).eq
  have hyE : ∀ n ∈ Subgroup.normalizer (E : Set G),
      n * x * n⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hninv : n⁻¹ * h * n ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) h).mp hh
    have hxcomm : (n⁻¹ * h * n) * x = x * (n⁻¹ * h * n) :=
      Subgroup.mem_centralizer_iff.mp hxE (n⁻¹ * h * n) hninv
    calc h * (n * x * n⁻¹) = n * ((n⁻¹ * h * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * h * n)) * n⁻¹ := by rw [hxcomm]
      _ = (n * x * n⁻¹) * h := by group
  apply hN
  intro n hn
  have hyC : n * x * n⁻¹ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hyE n hn) b₀ hb₀E).symm
  obtain ⟨k, hkK, z, hzZ, hkz⟩ :=
    exists_mul_of_mem_sup_of_normal_subgroupOf hKn hKC inf_le_left hout.symm (hyC)
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hzZ).2
  have hk_cent : k ∈ Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hey : Commute e (n * x * n⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hyE n hn) e he.1
    have hez : Commute e z := Subgroup.mem_centralizer_iff.mp hzK e he.2
    have hek : Commute e k := by
      have hk_eq : k = (n * x * n⁻¹) * z⁻¹ := by rw [← hkz]; group
      rw [hk_eq]
      exact hey.mul_right hez.inv_right
    exact hek.eq
  have hk_inf : k ∈ E ⊓ K := by
    rw [← hself]
    exact ⟨hk_cent, hkK⟩
  have hk3 : k ^ 3 = 1 := hE.2 k hk_inf.1
  have hzk : Commute k z := Subgroup.mem_centralizer_iff.mp hzK k hkK
  have hy3 : (n * x * n⁻¹) ^ 3 = n * b₀ * n⁻¹ := by rw [conj_pow, hx3]
  have hyz3 : (n * x * n⁻¹) ^ 3 = z ^ 3 := by
    rw [← hkz, hzk.mul_pow 3, hk3, one_mul]
  have hw_eq : n * b₀ * n⁻¹ = z ^ 3 := by rw [← hy3, hyz3]
  have hwZ : n * b₀ * n⁻¹ ∈ Z₀ := by
    rw [hw_eq]
    exact Subgroup.pow_mem _ hzZ 3
  have hw3 : (n * b₀ * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hb₀3]; group
  have hw_zpow : n * b₀ * n⁻¹ ∈ Subgroup.zpowers b₀ := by
    refine mem_zpowers_of_mem_inf_of_cube_eq_one hb₀ hKC hcyc ?_ hw3
    rwa [← hZ₀]
  have hwcard : Nat.card (Subgroup.zpowers (n * b₀ * n⁻¹)) = Nat.card (Subgroup.zpowers b₀) := by
    rw [Nat.card_zpowers, Nat.card_zpowers]
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj n) b₀
  have hwzpow : Subgroup.zpowers (n * b₀ * n⁻¹) = Subgroup.zpowers b₀ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw_zpow) (by rw [hwcard])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  simpa [MulAut.conj_apply] using hwzpow

theorem not_nine_dvd_card_inf_centralizer {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hE : IsElemAbelian 3 E) (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hself : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K)
    (hN : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))
    (hout : Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))) :
    ¬ 9 ∣ Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) := by
  intro h9
  set Z₀ : Subgroup G :=
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) with hZ₀
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Z₀) 3 (n := 2) (by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact h9)
  have hHle : H.map Z₀.subtype ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.map_subtype_le H).trans inf_le_right
  have hHcard' : Nat.card (H.map Z₀.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Z₀.subtype_injective, hHcard]
  have hHP : IsPGroup 3 (H.map Z₀.subtype) := IsPGroup.of_card hHcard'
  have hcycH : IsCyclic ↥(H.map Z₀.subtype) := hcyc _ hHle hHP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(H.map Z₀.subtype))
  set y : G := (g : G) with hy
  have hyZ : y ∈ Z₀ := Subgroup.map_subtype_le H g.2
  have hyord : orderOf y = 9 := by
    rw [hy, ← Subgroup.orderOf_mk (g : G) g.2, orderOf_eq_card_of_forall_mem_zpowers hg,
      Subgroup.card_map_of_injective Z₀.subtype_injective, hHcard]
    norm_num
  have hy3Z : y ^ 3 ∈ Z₀ := Subgroup.pow_mem _ hyZ 3
  have hy3cube : (y ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 by norm_num, ← hyord]
    exact pow_orderOf_eq_one y
  have hy3ne : y ^ 3 ≠ 1 := by
    intro h
    have h3 : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hyord] at h3
    norm_num at h3
  have hy3_zpow : y ^ 3 ∈ Subgroup.zpowers b₀ := by
    refine mem_zpowers_of_mem_inf_of_cube_eq_one hb₀ hKC hcyc ?_ hy3cube
    rwa [← hZ₀]
  have hy3ord : orderOf (y ^ 3) = 3 := orderOf_eq_prime hy3cube hy3ne
  have hzpow_eq : Subgroup.zpowers (y ^ 3) = Subgroup.zpowers b₀ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy3_zpow)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hy3ord, hb₀])
  have hb₀_mem : b₀ ∈ Subgroup.zpowers (y ^ 3) := by
    rw [hzpow_eq]
    exact Subgroup.mem_zpowers b₀
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb₀_mem
  refine not_exists_pow_three_eq_of_mem_inf hb₀ hKC hKn hcyc hE hsup hself hN hout
    ⟨y ^ m, ?_, ?_⟩
  · rw [← hZ₀]
    exact Subgroup.zpow_mem _ hyZ m
  · calc (y ^ m) ^ 3 = (y ^ m) ^ (3 : ℤ) := (zpow_natCast _ _).symm
      _ = y ^ (m * 3) := (zpow_mul y m 3).symm
      _ = y ^ (3 * m) := by rw [Int.mul_comm]
      _ = (y ^ (3 : ℤ)) ^ m := zpow_mul y 3 m
      _ = b₀ := by simpa using hm

theorem exists_centralizer_eq_sup_of_eq_sup_centralizer {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hE : IsElemAbelian 3 E) (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hself : Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K)
    (hN : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))
    (hout : Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({b₀} : Set G) ∧
      (R.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R ∧
      Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({b₀} : Set G) with hC
  set Z₀ : Subgroup G :=
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) with hZ₀
  have hZ₀leC : Z₀ ≤ C := by rw [hZ₀, hC]; exact inf_le_left
  have hnot9 : ¬ 9 ∣ Nat.card Z₀ :=
    not_nine_dvd_card_inf_centralizer hb₀ hKC hKn hcyc hE hsup hself hN hout
  have hb₀C : b₀ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hb₀K : b₀ ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)
  have hb₀Z : b₀ ∈ Z₀ := by rw [hZ₀]; exact ⟨hb₀C, hb₀K⟩
  have hb₀Zle : Subgroup.zpowers b₀ ≤ Z₀ := Subgroup.zpowers_le.mpr hb₀Z
  have hZ₀_cent : Z₀ ≤ Subgroup.centralizer (Subgroup.zpowers b₀ : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hzC : z ∈ Subgroup.centralizer ({b₀} : Set G) :=
      (Subgroup.mem_inf.mp (by rwa [hZ₀] at hz)).1
    exact (Commute.zpow_left (Commute.symm (Subgroup.mem_centralizer_singleton_iff.mp hzC)) i).eq
  have hNZ : ((Subgroup.zpowers b₀).subgroupOf Z₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hb₀Zle).mpr
      (hZ₀_cent.trans (Subgroup.centralizer_le_normalizer _))
  set N : Subgroup ↥Z₀ := (Subgroup.zpowers b₀).subgroupOf Z₀ with hN
  have hNnorm : N.Normal := hNZ
  have hNcard : Nat.card N = 3 := by
    rw [hN]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hb₀Zle).toEquiv).trans
      (by rw [Nat.card_zpowers, hb₀])
  have hnotdvd_index : ¬ 3 ∣ N.index := by
    intro h3
    apply hnot9
    have h3m : 3 * 3 ∣ Nat.card Z₀ := by
      have h' : 3 * 3 ∣ Nat.card N * N.index := by
        rw [hNcard]
        exact Nat.mul_dvd_mul_left 3 h3
      rwa [N.card_mul_index] at h'
    rwa [show (3 : ℕ) * 3 = 9 by norm_num] at h3m
  have hCoprime : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr hnotdvd_index
  obtain ⟨H, hHcomp⟩ := Subgroup.exists_right_complement'_of_coprime hCoprime
  set R : Subgroup G := H.map Z₀.subtype with hR
  have hRleZ : R ≤ Z₀ := by rw [hR]; exact Subgroup.map_subtype_le H
  have hRleC : R ≤ C := hRleZ.trans hZ₀leC
  have hRcard : Nat.card R = Nat.card H := by
    rw [hR]
    exact Subgroup.card_map_of_injective Z₀.subtype_injective
  have hHcard : Nat.card H = N.index := hHcomp.symm.index_eq_card.symm
  have hRnotdvd : ¬ 3 ∣ Nat.card R := by
    rw [hRcard, hHcard]
    exact hnotdvd_index
  have hZcard : Nat.card Z₀ = 3 * Nat.card R := by
    have h := hHcomp.card_mul_card
    rw [hNcard, ← hRcard] at h
    exact h.symm
  have hZR : Z₀ = R ⊔ Subgroup.zpowers b₀ := by
    have hNmap : N.map Z₀.subtype = Subgroup.zpowers b₀ := by
      rw [hN]
      exact Subgroup.map_subgroupOf_eq_of_le hb₀Zle
    have h := congrArg (fun T : Subgroup ↥Z₀ => T.map Z₀.subtype) hHcomp.sup_eq_top
    rw [Subgroup.map_sup, hNmap, ← hR, Subgroup.map_top, Subgroup.range_subtype, sup_comm] at h
    exact h.symm
  have hZ₀normal : (Z₀.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZ₀leC]
    intro w z hwZ hzC
    have hwZ' := hwZ
    rw [hZ₀] at hwZ'
    obtain ⟨hwC, hwK⟩ := Subgroup.mem_inf.mp hwZ'
    have hwC₀ : w ∈ Subgroup.centralizer ({b₀} : Set G) := hwC
    have hzC₀ : z ∈ Subgroup.centralizer ({b₀} : Set G) := hzC
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hzb : MulAut.conj z b₀ = b₀ := by
        rw [MulAut.conj_apply]
        have hz : z * b₀ = b₀ * z := Subgroup.mem_centralizer_singleton_iff.mp hzC₀
        rw [hz, mul_assoc, mul_inv_cancel, mul_one]
      have hcomm : Commute (z * w * z⁻¹) b₀ := by
        have h := Commute.map (Subgroup.mem_centralizer_singleton_iff.mp hwC₀)
          (MulAut.conj z).toMonoidHom
        simpa [MulAut.conj_apply, hzb] using h
      exact hcomm.eq
    · have hCn : C ≤ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
      have hzN : z ∈ Subgroup.normalizer (K : Set G) := hCn hzC
      have hKmap : K.map (MulAut.conj z).toMonoidHom = K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hzN
      have hKimage : (MulAut.conj z).toMonoidHom '' (K : Set G) = (K : Set G) := by
        have := congrArg (fun T : Subgroup G => (T : Set G)) hKmap
        rwa [Subgroup.coe_map] at this
      have hmem : z * w * z⁻¹ ∈
          (Subgroup.centralizer (K : Set G)).map (MulAut.conj z).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨w, hwK, by simp [MulAut.conj_apply]⟩
      have hle := Subgroup.map_centralizer_le_centralizer_image (K : Set G)
        (MulAut.conj z).toMonoidHom
      rw [hKimage] at hle
      exact hle hmem
  have hchar : ∀ w ∈ Z₀, ¬ 3 ∣ orderOf w → w ∈ R := by
    intro w hwZ hw3
    have hw' : (⟨w, hwZ⟩ : ↥Z₀) ∈ N ⊔ H := by
      rw [hHcomp.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, h, hh, hnh⟩ := Subgroup.mem_sup_of_normal_left.mp hw'
    have hnz : (n : G) ∈ Subgroup.zpowers b₀ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hb₀Zle]
      exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    have hhR : (h : G) ∈ R := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hw_eq : (n : G) * (h : G) = w := congrArg Subtype.val hnh
    have hhZ : (h : G) ∈ Z₀ := hRleZ hhR
    have hhb : Commute b₀ (h : G) := by
      have hhC : (h : G) ∈ Subgroup.centralizer ({b₀} : Set G) := hZ₀leC hhZ
      exact (Subgroup.mem_centralizer_singleton_iff.mp hhC).symm
    have hn_comm_h : Commute (n : G) (h : G) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hnz
      rw [← hi]
      exact Commute.zpow_left hhb i
    have hhm : (h : G) ^ Nat.card R = 1 := by
      have h1 : orderOf (h : G) ∣ Nat.card R := by
        rw [← Subgroup.orderOf_mk (h : G) hhR]
        exact orderOf_dvd_natCard _
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have hwdiv : orderOf w ∣ Nat.card R := by
      have hdiv : orderOf w ∣ Nat.card Z₀ := by
        rw [← Subgroup.orderOf_mk w hwZ]
        exact orderOf_dvd_natCard _
      rw [hZcard] at hdiv
      have hcop : Nat.Coprime (orderOf w) 3 :=
        ((Nat.prime_three.coprime_iff_not_dvd).mpr hw3).symm
      exact hcop.dvd_of_dvd_mul_left hdiv
    have hwm : w ^ Nat.card R = 1 := orderOf_dvd_iff_pow_eq_one.mp hwdiv
    have hnm : (n : G) ^ Nat.card R = 1 := by
      have h1 : ((n : G) * (h : G)) ^ Nat.card R = 1 := by
        rw [hw_eq]
        exact hwm
      rw [hn_comm_h.mul_pow, hhm, mul_one] at h1
      exact h1
    have hn3 : orderOf (n : G) ∣ 3 := by
      have h := orderOf_dvd_of_mem_zpowers hnz
      rwa [hb₀] at h
    have hnm_dvd : orderOf (n : G) ∣ Nat.card R :=
      orderOf_dvd_iff_pow_eq_one.mpr hnm
    have hn_one : (n : G) = 1 := by
      have hcop : Nat.Coprime 3 (Nat.card R) :=
        (Nat.prime_three.coprime_iff_not_dvd).mpr hRnotdvd
      have hgcd : orderOf (n : G) ∣ Nat.gcd 3 (Nat.card R) := Nat.dvd_gcd hn3 hnm_dvd
      rw [hcop.gcd_eq_one, Nat.dvd_one] at hgcd
      exact orderOf_eq_one_iff.mp hgcd
    have : w ∈ R := by
      rw [← hw_eq, hn_one, one_mul]
      exact hhR
    exact this
  have hRnormal : (R.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRleC]
    intro r c hrR hcC
    have hrZ : r ∈ Z₀ := hRleZ hrR
    have hcrZ : c * r * c⁻¹ ∈ Z₀ :=
      (Subgroup.normal_subgroupOf_iff hZ₀leC).mp hZ₀normal r c hrZ hcC
    have hord : orderOf (c * r * c⁻¹) = orderOf r := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj c) r
    have hr3 : ¬ 3 ∣ orderOf r := by
      intro h3
      apply hRnotdvd
      have hrdiv : orderOf r ∣ Nat.card R := by
        rw [← Subgroup.orderOf_mk r hrR]
        exact orderOf_dvd_natCard _
      exact h3.trans hrdiv
    exact hchar (c * r * c⁻¹) hcrZ (by rwa [hord])
  refine ⟨R, hRleC, hRnormal, hRnotdvd, ?_⟩
  calc C = K ⊔ Z₀ := hout
    _ = K ⊔ (R ⊔ Subgroup.zpowers b₀) := by rw [hZR]
    _ = R ⊔ (Subgroup.zpowers b₀ ⊔ K) := by
      rw [← sup_assoc, sup_comm K R, sup_assoc, sup_comm K (Subgroup.zpowers b₀)]

@[expose] def RowOutAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E →
      RecOut r B b₀ → Fus42 B b₀ →
      Subgroup.centralizer ({b₀} : Set G) =
        K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))

theorem rowCentAt_of_rowOutAt {r : Row} (h : RowOutAt r) : RowCentAt r := by
  intro G _ _ b₀ K E hstd B hB hrec hfus
  exact exists_centralizer_eq_sup_of_eq_sup_centralizer
    hstd.2.1.1.1
    hstd.2.1.1.2.1
    hstd.2.1.1.2.2.1
    hstd.2.1.1.2.2.2.2.2.1
    hstd.2.1.2.1.2.1
    hstd.2.2.2.2.1
    hstd.2.2.2.2.2.2.2
    (hB.1 ▸ hfus.1)
    (h G b₀ K E hstd B hB hrec hfus)

end CFSG.StandardType.FrameRoute.FS81
