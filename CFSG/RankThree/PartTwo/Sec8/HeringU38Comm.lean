module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38Setup
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Tools
public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (thetaQuotMulAut compAction InducesOuterTheta)
open scoped commutatorElement

@[expose] def u38Fix {Ū : Type*} [Group Ū] (φ : MulAut Ū) : Subgroup Ū :=
  φ.toMonoidHom.eqLocus (MonoidHom.id Ū)

theorem mem_u38Fix {Ū : Type*} [Group Ū] {φ : MulAut Ū} {x : Ū} :
    x ∈ u38Fix φ ↔ φ x = x := Iff.rfl

@[expose] def u38Comm {Ū : Type*} [Group Ū] (T : Subgroup Ū) (β : MulAut Ū) : Subgroup Ū :=
  Subgroup.closure {y | ∃ w ∈ T, y = w * (β w)⁻¹}

@[expose] def U38SylModel : Prop :=
  ∀ (Ū : Type) [Group Ū] [Finite Ū], IsUnitaryTwo Ū 3 →
    ∀ α β : MulAut Ū, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α → ¬ KFacts.IsInnerAut α →
      Nat.card (u38Fix α) = 216 → (∃ u ∈ u38Fix α, u ^ 4 = 1 ∧ u ^ 2 ≠ 1) →
      β ≠ 1 → 7 ∣ Nat.card (u38Fix β) →
      ∃ T : Subgroup Ū, T ≤ u38Fix α ∧ Nat.card T = 8 ∧ (∀ x ∈ T, β x ∈ T) ∧
        T ≤ u38Comm T β

theorem barCentralizer_eq_u38Fix {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) :
    barCentralizer (Subgroup.zpowers a) L =
      u38Fix (thetaQuotMulAut L (compAction L ⟨a, ha⟩)) := by
  ext y
  rw [KFacts.mem_barCentralizer_zpowers_iff ha]
  rfl

variable {G : Type} [Group G] [Finite G]

theorem mem_commutator_of_u38Syl {L : Subgroup G} {a b : G}
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hbN : b ∈ Subgroup.normalizer (L : Set G))
    (ha3 : a ^ 3 = 1) (hab : a * b = b * a)
    (hθodd : Odd (Nat.card ((aschbacherSolvableCore 3 L).map L.subtype)))
    (T : Subgroup (L ⧸ aschbacherSolvableCore 3 L))
    (hTM : T ≤ barCentralizer (Subgroup.zpowers a) L) (hT8 : Nat.card T = 8)
    (hM : Nat.card (barCentralizer (Subgroup.zpowers a) L) = 216)
    (hTβ : ∀ x ∈ T, thetaQuotMulAut L (compAction L ⟨b, hbN⟩) x ∈ T)
    (hTc : T ≤ u38Comm T (thetaQuotMulAut L (compAction L ⟨b, hbN⟩)))
    {t : G} (htC : t ∈ L ⊓ Subgroup.centralizer ({a} : Set G)) (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) :
    t ∈ ⁅L ⊓ Subgroup.centralizer ({a} : Set G), Subgroup.zpowers b⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set β := thetaQuotMulAut L (compAction L ⟨b, hbN⟩) with hβ
  set C : Subgroup G := L ⊓ Subgroup.centralizer ({a} : Set G) with hC
  set N : Subgroup G := ⁅C, Subgroup.zpowers b⁆ with hN
  set q : L →* L ⧸ θ := QuotientGroup.mk' θ with hq
  have hcomm : Commute a b := hab
  have hgC : ∀ g ∈ Subgroup.normalizer (L : Set G), Commute a g → ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hgN hag x hx
    obtain ⟨hxL, hxa⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hgN x).mp hxL, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxa ⊢
    have hxa' : Commute x a := hxa
    exact (((hag.symm.mul_left hxa').mul_left hag.symm.inv_left)).eq
  have hbk : ∀ k : ℤ, ∀ z ∈ C, b ^ k * z * (b ^ k)⁻¹ ∈ C := fun k z hz =>
    hgC (b ^ k) (Subgroup.zpow_mem _ hbN k) (hcomm.zpow_right k) z hz
  have hNC : N ≤ C := by
    rw [hN, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [commutatorElement_def]
    have : x * b ^ k * x⁻¹ * (b ^ k)⁻¹ = x * (b ^ k * x⁻¹ * (b ^ k)⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx (hbk k x⁻¹ (Subgroup.inv_mem _ hx))
  have hNconj : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := fun c hc n hn =>
    HeringU38.commutator_conj_mem C b hc hn
  have hlift : ∀ w ∈ barCentralizer (Subgroup.zpowers a) L, ∃ x : L, (x : G) ∈ C ∧ q x = w := by
    intro w hw
    rw [← KFacts.imageModTheta_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hβq : ∀ x : L, β (q x) = q (compAction L ⟨b, hbN⟩ x) := fun x =>
    Sec4.thetaQuotMulAut_mk (compAction L ⟨b, hbN⟩) x
  set Nbar : Subgroup (L ⧸ θ) := imageModTheta L N with hNbar
  have hmemNbar : ∀ x : L, (x : G) ∈ N → q x ∈ Nbar := fun x hx =>
    ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hTN : T ≤ Nbar := by
    refine hTc.trans ?_
    unfold u38Comm
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hxC, rfl⟩ := hlift w (hTM hw)
    rw [hβq]
    have hxb : ((x * (compAction L ⟨b, hbN⟩ x)⁻¹ : L) : G) = ⁅(x : G), b⁆ := by
      show (x : G) * (b * x * b⁻¹)⁻¹ = _
      rw [commutatorElement_def]
      group
    have : q x * (q (compAction L ⟨b, hbN⟩ x))⁻¹ = q (x * (compAction L ⟨b, hbN⟩ x)⁻¹) := by
      rw [map_mul, map_inv]
    rw [this]
    apply hmemNbar
    rw [hxb]
    exact Subgroup.commutator_mem_commutator hxC (Subgroup.mem_zpowers b)
  set M := barCentralizer (Subgroup.zpowers a) L with hMdef
  have hMN : M ≤ Subgroup.normalizer (Nbar : Set (L ⧸ θ)) := by
    have key : ∀ m ∈ M, ∀ z ∈ Nbar, m * z * m⁻¹ ∈ Nbar := by
      intro m hm z hz
      obtain ⟨x, hxC, rfl⟩ := hlift m hm
      have hz' : z ∈ (N.subgroupOf L).map q := hz
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hz'
      have hn' : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
      have hxn : ((x * n * x⁻¹ : L) : G) ∈ N := hNconj _ hxC _ hn'
      have : q x * q n * (q x)⁻¹ = q (x * n * x⁻¹) := by rw [map_mul, map_mul, map_inv]
      rw [this]
      exact hmemNbar _ hxn
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact key m hm z
    · intro hz
      have := key m⁻¹ (Subgroup.inv_mem _ hm) _ hz
      simpa [mul_assoc] using this
  have htL : t ∈ L := (Subgroup.mem_inf.mp htC).1
  set z : L ⧸ θ := q ⟨t, htL⟩ with hz
  have hzM : z ∈ M := by
    rw [hMdef, ← KFacts.imageModTheta_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩]
    exact ⟨⟨t, htL⟩, Subgroup.mem_subgroupOf.mpr htC, rfl⟩
  have hz2 : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := ht2
    refine ⟨k, ?_⟩
    rw [hz, ← map_pow]
    have : ((⟨t, htL⟩ : L) ^ 2 ^ k : L) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hS8 : Nat.card (T.subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hT8, hM]
    norm_num [Nat.factorization]
  let S : Sylow 2 M := Sylow.ofCard (T.subgroupOf M) hS8
  have hSN : (S : Subgroup M).map M.subtype ≤ Nbar := by
    show (T.subgroupOf M).map M.subtype ≤ Nbar
    rw [Subgroup.map_subgroupOf_eq_of_le hTM]
    exact hTN
  have hzN : z ∈ Nbar := Item89Res2.mem_of_sylow_le hMN S hSN hzM hz2
  have hzN' : z ∈ (N.subgroupOf L).map q := hzN
  obtain ⟨n', hn', hqn⟩ := Subgroup.mem_map.mp hzN'
  have hn'N : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
  have hθ' : n'⁻¹ * (⟨t, htL⟩ : L) ∈ θ := by
    have h1 : (n' : L ⧸ θ) = ((⟨t, htL⟩ : L) : L ⧸ θ) := hqn
    exact QuotientGroup.eq.mp h1
  have hθ'G : (n' : G)⁻¹ * t ∈ θ.map L.subtype := ⟨n'⁻¹ * ⟨t, htL⟩, hθ', rfl⟩
  have hθ'C : (n' : G)⁻¹ * t ∈ C :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hNC hn'N)) htC
  have hodd : Odd (orderOf ((n' : G)⁻¹ * t)) := by
    have h1 : orderOf ((n' : G)⁻¹ * t) ∣ Nat.card (θ.map L.subtype) := by
      have := orderOf_dvd_natCard (⟨_, hθ'G⟩ : θ.map L.subtype)
      rwa [← Subgroup.orderOf_coe] at this
    exact Odd.of_dvd_nat hθodd h1
  have hnorm : (n' : G)⁻¹ * t ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hNconj _ hθ'C _ hh
    · intro hh
      have := hNconj _ (Subgroup.inv_mem _ hθ'C) _ hh
      simpa [mul_assoc] using this
  exact HeringU38.mem_of_mul_odd hnorm hn'N hodd (by group) ht2

theorem u38_pow_eq_one {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    {m : ℕ} (hxm : x ^ m = 1) : thetaQuotMulAut L (compAction L ⟨x, hx⟩) ^ m = 1 := by
  have h : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ m = 1 :=
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hxm)
  rw [← map_pow, ← map_pow, h, map_one, map_one]

theorem u38_mul_comm {L : Subgroup G} {a b : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hab : a * b = b * a) :
    thetaQuotMulAut L (compAction L ⟨a, ha⟩) * thetaQuotMulAut L (compAction L ⟨b, hb⟩) =
      thetaQuotMulAut L (compAction L ⟨b, hb⟩) * thetaQuotMulAut L (compAction L ⟨a, ha⟩) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  exact Subtype.ext hab


theorem kF87UBComm_of (h45 : Sec4.Item4_5) (hM : U38SylModel) : KF87UBComm := by
  intro G _ _ A c L a b X n h hU t htC ht2
  classical
  obtain ⟨haN, hbN, ha3, hb3, hab, haL, hCa, hu4, hβ1, h7, hθodd⟩ := u38_pair_data h45 h hU
  obtain ⟨hx, hnot⟩ := haL
  obtain ⟨T, hTα, hT8, hTβ, hTc⟩ := hM (L ⧸ aschbacherSolvableCore 3 L) hU
    (thetaQuotMulAut L (compAction L ⟨a, haN⟩)) (thetaQuotMulAut L (compAction L ⟨b, hbN⟩))
    (u38_pow_eq_one haN ha3) (u38_pow_eq_one hbN hb3) (u38_mul_comm haN hbN hab)
    (fun hin => hnot hin)
    (by rw [← barCentralizer_eq_u38Fix haN]; exact hCa)
    (by
      obtain ⟨u, hu, h4, h2⟩ := hu4
      exact ⟨u, by rwa [barCentralizer_eq_u38Fix haN] at hu, h4, h2⟩)
    hβ1 (by rw [← barCentralizer_eq_u38Fix hbN]; exact h7)
  exact mem_commutator_of_u38Syl haN hbN ha3 hab hθodd T
    (by rw [barCentralizer_eq_u38Fix haN]; exact hTα) hT8 hCa hTβ hTc htC ht2

end CFSG.RankThree.PartTwo.Sec8
