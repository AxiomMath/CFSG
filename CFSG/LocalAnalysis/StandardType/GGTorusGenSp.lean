module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpModel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)

private theorem isComponentOf_comap_of_le_range {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) {L K : Subgroup Y}
    (h : CFSG.Assembly.IsComponentOf L K) (hK : K ≤ f.range) :
    CFSG.Assembly.IsComponentOf (L.comap f) (K.comap f) := by
  have hL : L ≤ f.range := h.1.trans hK
  have hmap : (L.comap f).map f = L := Subgroup.map_comap_eq_self hL
  have hq : CFSG.Assembly.IsQuasisimple ((L.comap f).map f) := by
    rw [hmap]
    exact h.2.2
  exact ⟨Subgroup.comap_mono h.1, CFSG.Assembly.IsSubnormal.comap f h.2.1,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv ((L.comap f).equivMapOfInjective f hf) hq⟩

private theorem mem_centralizer_mul_iff {M : Type*} [Group M] {L' : Subgroup M} {z x y : M}
    (hz : z ∈ Subgroup.centralizer (L' : Set M)) (hy : y ∈ L') :
    y ∈ Subgroup.centralizer ({z * x} : Set M) ↔
      y ∈ Subgroup.centralizer ({x} : Set M) := by
  have hyz : y * z = z * y := Subgroup.mem_centralizer_iff.mp hz y hy
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * x = z⁻¹ * (z * y) * x := by group
      _ = z⁻¹ * (y * z) * x := by rw [hyz]
      _ = z⁻¹ * (y * (z * x)) := by group
      _ = z⁻¹ * ((z * x) * y) := by rw [h]
      _ = x * y := by group
  · intro h
    calc y * (z * x) = (y * z) * x := by group
      _ = (z * y) * x := by rw [hyz]
      _ = z * (y * x) := by group
      _ = z * (x * y) := by rw [h]
      _ = (z * x) * y := by group

private theorem inf_centralizer_map_eq {A M : Type*} [Group A] [Group M] (φ : A →* M)
    (hφi : Function.Injective φ) {L' : Subgroup M} (hφL : φ.range = L') (x : A) :
    L' ⊓ Subgroup.centralizer ({φ x} : Set M) =
      (Subgroup.centralizer ({x} : Set A)).map φ := by
  ext y
  constructor
  · rintro ⟨hyL, hyc⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp (hφL ▸ hyL)
    have hyc' : φ a * φ x = φ x * φ a := Subgroup.mem_centralizer_singleton_iff.mp hyc
    refine Subgroup.mem_map.mpr ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    apply hφi
    rw [map_mul, map_mul]
    exact hyc'
  · rintro ⟨a, ha, rfl⟩
    have ha' : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp ha
    refine ⟨hφL ▸ MonoidHom.mem_range.mpr ⟨a, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc φ a * φ x = φ (a * x) := (map_mul _ _ _).symm
      _ = φ (x * a) := by rw [ha']
      _ = φ x * φ a := map_mul _ _ _

private theorem inf_centralizer_sup_eq_map {A M : Type*} [Group A] [Group M] (φ : A →* M)
    (hφi : Function.Injective φ) {L' D' Cc : Subgroup M} (hφL : φ.range = L')
    {dm : M} {x : A} {z₀ : M} (hz₀ : z₀ ∈ Subgroup.centralizer (L' : Set M))
    (hzeq : dm = z₀ * φ x) (hCc : Cc ≤ Subgroup.centralizer (L' : Set M))
    (hD : D' = Subgroup.zpowers dm ⊔ Cc) :
    L' ⊓ Subgroup.centralizer (D' : Set M) = (Subgroup.centralizer ({x} : Set A)).map φ := by
  have hmem : dm ∈ D' := by
    rw [hD]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers dm)
  have hmid : L' ⊓ Subgroup.centralizer (D' : Set M) =
      L' ⊓ Subgroup.centralizer ({φ x} : Set M) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨hyL, hyD⟩
      refine ⟨hyL, ?_⟩
      have hydm : dm * y = y * dm := Subgroup.mem_centralizer_iff.mp hyD dm hmem
      have h2 : y * (z₀ * φ x) = (z₀ * φ x) * y := by
        rw [← hzeq]
        exact hydm.symm
      exact (mem_centralizer_mul_iff hz₀ hyL).mp (Subgroup.mem_centralizer_singleton_iff.mpr h2)
    · rintro y ⟨hyL, hyx⟩
      have hyx' : y * φ x = φ x * y := Subgroup.mem_centralizer_singleton_iff.mp hyx
      have hzy : y * z₀ = z₀ * y := Subgroup.mem_centralizer_iff.mp hz₀ y hyL
      have hcomm : dm * y = y * dm := by
        rw [hzeq]
        calc (z₀ * φ x) * y = z₀ * (φ x * y) := by group
          _ = z₀ * (y * φ x) := by rw [hyx']
          _ = (z₀ * y) * φ x := by group
          _ = (y * z₀) * φ x := by rw [hzy]
          _ = y * (z₀ * φ x) := by group
      have hsup : Subgroup.zpowers dm ⊔ Cc ≤ Subgroup.centralizer ({y} : Set M) := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact hcomm
        · intro w hw
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp (hCc hw) y hyL).symm
      refine ⟨hyL, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro w hw
      rw [hD] at hw
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hw)
  rw [hmid, inf_centralizer_map_eq φ hφi hφL x]


private theorem mem_centralizer_of_mem_center {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {M : Type} [Group M] {L' E : Subgroup M} {φ : StatedSp m K →* M}
    (hm : 2 ≤ m) (hφi : Function.Injective φ) (hφL : φ.range = L')
    {z : M} (hz : z ∈ L' ⊓ Subgroup.centralizer (L' : Set M)) :
    z ∈ Subgroup.centralizer (E : Set M) := by
  have hmemφ : ∀ l : StatedSp m K, φ l ∈ L' := fun l =>
    hφL ▸ MonoidHom.mem_range.mpr ⟨l, rfl⟩
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hφL ▸ hz.1)
  have hgZ : g ∈ Subgroup.center (StatedSp m K) := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply hφi
    rw [map_mul, map_mul, hg]
    exact Subgroup.mem_centralizer_iff.mp hz.2 (φ l) (hmemφ l)
  have hg1 : g = 1 := by
    have hbot : Subgroup.center (StatedSp m K) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := m) (F := K)
        (by omega)
    rw [hbot] at hgZ
    exact Subgroup.mem_bot.mp hgZ
  have hz1 : z = 1 := by rw [← hg, hg1, map_one]
  refine Subgroup.mem_centralizer_iff.mpr ?_
  simp [hz1]

private theorem exists_diagSp_eq_of_mem {K : Type} [Field K] {m : ℕ} [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {M : Type} [Group M]
    {L' E : Subgroup M} {φ : StatedSp m K →* M} (hφi : Function.Injective φ)
    (hφL : φ.range = L') (hTE : ∀ t : Fin m → Kˣ, t ^ p = 1 → φ (diagSp K m t) ∈ E)
    {c : M} (hc : c ∈ L' ⊓ Subgroup.centralizer (E : Set M)) {k : ℕ} (hck : c ^ p ^ k = 1) :
    ∃ y : Fin m → Kˣ, φ (diagSp K m y) = c ∧ y ^ p ^ k = 1 := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hφL ▸ hc.1)
  have hgcomm : ∀ t : Fin m → Kˣ, t ^ p = 1 → Commute g (diagSp K m t) := by
    intro t ht
    apply hφi
    rw [map_mul, map_mul, hg]
    exact (Subgroup.mem_centralizer_iff.mp hc.2 (φ (diagSp K m t)) (hTE t ht)).symm
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn] at hpK
    have hn0 : (n : ℕ) ≠ 0 := by
      have := n.pos
      omega
    have h1 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 hn0
    have h2 : 2 ∣ 2 ^ (n : ℕ) - (2 ^ (n : ℕ) - 1) := Nat.dvd_sub h1 hpK
    rw [Nat.sub_sub_self (Nat.one_le_two_pow)] at h2
    omega
  obtain ⟨y, hy⟩ : ∃ y : Fin m → Kˣ, diagSp K m y = g :=
    MonoidHom.mem_range.mp (mem_range_diagSp_of_commute_pTorsion hp hp2 hpK hgcomm)
  refine ⟨y, by rw [hy, hg], ?_⟩
  apply diagSp_injective
  rw [map_pow, map_one, hy]
  apply hφi
  rw [map_pow, map_one, hg, hck]

private theorem eq_sup_zpowers_of_le {M : Type} [Group M] {L' E E₁ D' : Subgroup M} {dm : M}
    (hdec : ∀ x ∈ E, ∃ e₁ ∈ E₁, ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = e₁ * z)
    (hD'E : D' ≤ E) (hCD' : E ⊓ Subgroup.centralizer (L' : Set M) ≤ D')
    (hD'E₁ : D' ⊓ E₁ = Subgroup.zpowers dm) :
    D' = Subgroup.zpowers dm ⊔ (E ⊓ Subgroup.centralizer (L' : Set M)) := by
  refine le_antisymm ?_ (sup_le ?_ hCD')
  · intro x hx
    obtain ⟨e₁, he₁, z, hz, rfl⟩ := hdec x (hD'E hx)
    have hzD : z ∈ D' := hCD' hz
    have he₁D : e₁ ∈ D' := by
      have h1 : (e₁ * z) * z⁻¹ ∈ D' := D'.mul_mem hx (D'.inv_mem hzD)
      rwa [show e₁ * z * z⁻¹ = e₁ from by group] at h1
    have he₁z : e₁ ∈ Subgroup.zpowers dm := by
      rw [← hD'E₁]
      exact ⟨he₁D, he₁⟩
    exact mul_mem (Subgroup.mem_sup_left he₁z) (Subgroup.mem_sup_right hz)
  · rw [← hD'E₁]
    exact inf_le_left

private theorem exists_component_of_centralizer {K : Type} [Field K] {m : ℕ} {M : Type}
    [Group M] {L' E D' J' : Subgroup M} {dm : M} {φ : StatedSp m K →* M} {p : ℕ}
    (hφi : Function.Injective φ) (hφL : φ.range = L')
    (hEφ : ∀ e ∈ E, ∃ t : Fin m → Kˣ, t ^ p = 1 ∧
      e * (φ (diagSp K m t))⁻¹ ∈ Subgroup.centralizer (L' : Set M))
    (hD'E : D' ≤ E) (hD' : D' = Subgroup.zpowers dm ⊔ (E ⊓ Subgroup.centralizer (L' : Set M)))
    (hJ : CFSG.Assembly.IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M))) :
    ∃ t₀ : Fin m → Kˣ, t₀ ^ p = 1 ∧
      CFSG.Assembly.IsComponentOf (J'.comap φ)
        (Subgroup.centralizer ({diagSp K m t₀} : Set (StatedSp m K))) := by
  have hdmem : dm ∈ D' := by
    rw [hD']
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers dm)
  obtain ⟨t₀, ht₀p, ht₀⟩ := hEφ dm (hD'E hdmem)
  refine ⟨t₀, ht₀p, ?_⟩
  have hKeq : L' ⊓ Subgroup.centralizer (D' : Set M) =
      (Subgroup.centralizer ({diagSp K m t₀} : Set (StatedSp m K))).map φ :=
    inf_centralizer_sup_eq_map φ hφi hφL ht₀ (by group) inf_le_right hD'
  have h := isComponentOf_comap_of_le_range φ hφi hJ (by rw [hφL]; exact inf_le_left)
  rwa [hKeq, Subgroup.comap_map_eq_self_of_injective hφi] at h

private theorem zpowers_diagSp_isPGroup {K : Type} [Field K] {m : ℕ} {p : ℕ} {M : Type}
    [Group M] {E E₁ L' J' : Subgroup M} {φ : StatedSp m K →* M} (hp : p.Prime)
    (hφL : φ.range = L') (hE₁E : E₁ ≤ E)
    (hEφ : ∀ e ∈ E, ∃ t : Fin m → Kˣ, t ^ p = 1 ∧
      e * (φ (diagSp K m t))⁻¹ ∈ Subgroup.centralizer (L' : Set M))
    {x : Fin m → Kˣ} {k : ℕ} (hxk : x ^ p ^ k = 1) (hφx : φ (diagSp K m x) ∈ J') :
    IsPGroup p (Subgroup.zpowers (φ (diagSp K m x))) ∧
      Subgroup.zpowers (φ (diagSp K m x)) ≤ Subgroup.centralizer (E₁ : Set M) ∧
      Subgroup.zpowers (φ (diagSp K m x)) ≤ J' := by
  have hdl : ∀ t : Fin m → Kˣ, t ^ p = 1 →
      Commute (φ (diagSp K m t)) (φ (diagSp K m x)) := fun t _ =>
    Commute.map (Commute.map (mul_comm t x) (diagSp K m)) φ
  have hxk' : (φ (diagSp K m x)) ^ p ^ k = 1 := by
    rw [← map_pow, ← map_pow, hxk, map_one, map_one]
  refine ⟨?_, ?_, Subgroup.zpowers_le.mpr hφx⟩
  · obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hxk')
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro e he
    obtain ⟨t, ht, htC⟩ := hEφ e (hE₁E he)
    have hzc : Commute (e * (φ (diagSp K m t))⁻¹) (φ (diagSp K m x)) :=
      (Subgroup.mem_centralizer_iff.mp htC (φ (diagSp K m x))
        (hφL ▸ MonoidHom.mem_range.mpr ⟨diagSp K m x, rfl⟩)).symm
    have hee : e = (e * (φ (diagSp K m t))⁻¹) * φ (diagSp K m t) := by group
    rw [hee]
    exact hzc.mul_left (hdl t ht)

private theorem image_spSignedPermSp_le_normalizer {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {p : ℕ} {M : Type} [Group M] {L' E E₁ : Subgroup M} {φ : StatedSp m K →* M}
    (hφL : φ.range = L')
    (hTE : ∀ t : Fin m → Kˣ, t ^ p = 1 → φ (diagSp K m t) ∈ E)
    (hEφ : ∀ e ∈ E, ∃ t : Fin m → Kˣ, t ^ p = 1 ∧
      e * (φ (diagSp K m t))⁻¹ ∈ Subgroup.centralizer (L' : Set M))
    (hN : Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (E₁ : Set M)) :
    φ '' (spSignedPermSp K m : Set (StatedSp m K)) ⊆ Subgroup.normalizer (E₁ : Set M) := by
  rintro _ ⟨w, hw, rfl⟩
  exact hN (spSignedPermSp_map_mem_normalizer hφL hTE hEφ hw)

private theorem diagSp_mem_closure_image {K : Type} [Field K] {m : ℕ} [Finite K] [CharP K 2]
    {p : ℕ} {M : Type} [Group M] (φ : StatedSp m K →* M) {x y : Fin m → Kˣ} {j : Fin m}
    {k : ℕ} (hxj : ∀ u : Kˣ, (∃ k : ℕ, u ^ p ^ k = 1) → u ∈ Subgroup.zpowers (x j))
    (hyk : y ^ p ^ k = 1) :
    φ (diagSp K m y) ∈ Subgroup.closure (⋃ n ∈ (φ '' (spSignedPermSp K m : Set (StatedSp m K))),
      (fun s : M => n * s * n⁻¹) '' (Subgroup.zpowers (φ (diagSp K m x)) : Set M)) := by
  have hyi : ∀ i, y i ∈ Subgroup.zpowers (x j) := fun i => hxj (y i) ⟨k, by
    have h1 := congrFun hyk i
    simpa using h1⟩
  have h0 : φ (diagSp K m y) ∈ Subgroup.map φ (Subgroup.closure
      (⋃ w ∈ (spSignedPermSp K m : Set (StatedSp m K)),
        (fun z => w * z * w⁻¹) '' (Subgroup.zpowers (diagSp K m x) : Set (StatedSp m K)))) :=
    Subgroup.mem_map.mpr ⟨_, diagSp_mem_closure_signedConj x y j hyi, rfl⟩
  rw [MonoidHom.map_closure] at h0
  refine Subgroup.closure_mono ?_ h0
  rintro _ ⟨wz, hwz, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hwz ⊢
  obtain ⟨w, hw, z₁, hz₁, rfl⟩ := hwz
  refine ⟨φ w, ⟨w, hw, rfl⟩, φ z₁, ?_, ?_⟩
  · have h1 : φ z₁ ∈ (Subgroup.zpowers (diagSp K m x)).map φ :=
      Subgroup.mem_map.mpr ⟨z₁, hz₁, rfl⟩
    rwa [MonoidHom.map_zpowers] at h1
  · rw [← map_inv, ← map_mul, ← map_mul]

theorem ggTorusGenTableBRk_Sp {K : Type} [Field K] {m : ℕ}
    [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hm : 2 ≤ m) :
    GGTorusGenTableBRk p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (m + 1) := by
  intro M _ _ L' E E₁ D' J' dm θ hE hpos hr hC hE₁E hE₁C hcard hN hD'E hCD' hD'E₁ hd1 hJ
  classical
  obtain ⟨φ, hφi, hφL, hTE, hEφ⟩ := exists_model_of_position_Sp hp hpK hm hpos hr
  obtain ⟨hdec, hcent⟩ := exists_mul_of_complement_position hp hpos hC hE₁E hE₁C hcard
  refine ⟨?_, ?_⟩
  · intro z hz _
    exact mem_centralizer_of_mem_center hm hφi hφL hz
  intro c hc hcp _
  obtain ⟨k, hk⟩ := hcp
  obtain ⟨y, hy, hyk⟩ :=
    exists_diagSp_eq_of_mem hp hpK hφi hφL hTE ⟨hc.1, hcent hc⟩ hk
  obtain ⟨t₀, -, hJ0⟩ := exists_component_of_centralizer hφi hφL hEφ hD'E
    (eq_sup_zpowers_of_le hdec hD'E hCD' hD'E₁) hJ
  obtain ⟨x, j, ⟨k', hxk'⟩, hxj, hdxJ⟩ :=
    exists_diagSp_mem_of_isComponentOf_centralizer_Sp p t₀ hJ0
  obtain ⟨hSpg, hScent, hSJ⟩ :=
    zpowers_diagSp_isPGroup hp hφL hE₁E hEφ hxk' (Subgroup.mem_comap.mp hdxJ)
  refine ⟨Subgroup.zpowers (φ (diagSp K m x)),
    φ '' (spSignedPermSp K m : Set (StatedSp m K)), hSpg, hScent, hSJ,
    image_spSignedPermSp_le_normalizer hφL hTE hEφ hN, ?_⟩
  simpa only [hy] using diagSp_mem_closure_image φ hxj hyk

private theorem recipeSymplectic_torusGenTableB {l n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 2 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGTorusGenTableB p R I := by
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusGenTableB_of_rk (r := l + 1) hp (by omega)
    (TableBSymp.ggTorusLift_symplectic (m := l) hp hp2 hpq (by omega))
    (ggTorusGenTableBRk_Sp (K := K) (m := l) hp hpq hl)

theorem largeEvenLabelAll_torusGenTableB_symplectic
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTableBSympLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    exact recipeSymplectic_torusGenTableB hp hp2 hpn hlab.2.1 hQ

end CFSG.StandardType
