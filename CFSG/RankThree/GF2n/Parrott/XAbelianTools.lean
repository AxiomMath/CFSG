module

public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer
public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Sylow
public import CFSG.GroupTheory.ConjOrderThree
public import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Cover

omit [Finite G] in
theorem commutative_of_closure_cover {X A : Subgroup G} {x k : G} (hx : x ∈ X) (hk : k ∈ X)
    (hxk : x * k = k * x) (hAA : ∀ a ∈ X ⊓ A, ∀ a' ∈ X ⊓ A, a * a' = a' * a)
    (hxA : ∀ a ∈ X ⊓ A, x * a = a * x) (hkA : ∀ a ∈ X ⊓ A, k * a = a * k)
    (hcov : ∀ g ∈ X, ∃ c ∈ Subgroup.closure ({x, k} : Set G), c⁻¹ * g ∈ A) :
    ∀ g ∈ X, ∀ g' ∈ X, g * g' = g' * g := by
  set S : Subgroup G := Subgroup.closure ({x, k} : Set G) with hS
  have hSX : S ≤ X := by
    rw [hS, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hx
    · exact hk
  have hSy : ∀ y ∈ ({x, k} : Set G), ∀ c ∈ S, c * y = y * c := by
    intro y hy c hc
    have hle : S ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hS, Subgroup.closure_le]
      intro e he
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hy with rfl | rfl <;> rcases he with rfl | rfl
      · rfl
      · exact hxk.symm
      · exact hxk
      · rfl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
  have hSS : ∀ c ∈ S, ∀ c' ∈ S, c * c' = c' * c := by
    intro c hc c' hc'
    have hle : S ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hS, Subgroup.closure_le]
      intro e he
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hSy e he c hc).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc')).symm
  have hSA : ∀ c ∈ S, ∀ a ∈ X ⊓ A, c * a = a * c := by
    intro c hc a ha
    have hle : S ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [hS, Subgroup.closure_le]
      intro e he
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases he with rfl | rfl
      · exact hxA a ha
      · exact hkA a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
  intro g hg g' hg'
  obtain ⟨c, hc, hca⟩ := hcov g hg
  obtain ⟨c', hc', hca'⟩ := hcov g' hg'
  have hmem : ∀ (c g : G), c ∈ S → g ∈ X → c⁻¹ * g ∈ A → c⁻¹ * g ∈ X ⊓ A := fun c g hc hg hca =>
    Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem (hSX hc)) hg, hca⟩
  have ha := hmem c g hc hg hca
  have ha' := hmem c' g' hc' hg' hca'
  have e1 : g = c * (c⁻¹ * g) := by group
  have e2 : g' = c' * (c'⁻¹ * g') := by group
  have hcomm : Commute (c * (c⁻¹ * g)) (c' * (c'⁻¹ * g')) :=
    Commute.mul_left
      (Commute.mul_right (hSS c hc c' hc') (hSA c hc _ ha'))
      (Commute.mul_right (hSA c' hc' _ ha).symm (hAA _ ha _ ha'))
  rw [← e1, ← e2] at hcomm
  exact hcomm.eq

end Cover

section Conj

theorem isSylowOf_map_conj_centralizer {g : G} (hg : g ∈ H z) {ρ x : G} {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    IsSylowOf 2 (X.map (MulAut.conj g).toMonoidHom)
      (centralizer ({g * ρ * g⁻¹} : Set G) ⊓ H z ⊓ centralizer ({g * x * g⁻¹} : Set G)) := by
  have hker : ¬ 2 ∣ Nat.card ↥(MonoidHom.ker (MulAut.conj g).toMonoidHom) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective, Subgroup.card_bot]
    norm_num
  have h1 := isSylowOf_map_of_not_dvd_card_ker (MulAut.conj g).toMonoidHom
    (MulAut.conj g).surjective Nat.prime_two hker hX
  have hmap : (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G)).map
      (MulAut.conj g).toMonoidHom =
      centralizer ({g * ρ * g⁻¹} : Set G) ⊓ H z ⊓ centralizer ({g * x * g⁻¹} : Set G) := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨m, ⟨⟨hmρ, hmH⟩, hmx⟩, rfl⟩
      refine ⟨⟨?_, (H z).mul_mem ((H z).mul_mem hg hmH) ((H z).inv_mem hg)⟩, ?_⟩
      · calc g * m * g⁻¹ * (g * ρ * g⁻¹) = g * (m * ρ) * g⁻¹ := by group
          _ = g * (ρ * m) * g⁻¹ := by rw [hmρ]
          _ = g * ρ * g⁻¹ * (g * m * g⁻¹) := by group
      · calc g * m * g⁻¹ * (g * x * g⁻¹) = g * (m * x) * g⁻¹ := by group
          _ = g * (x * m) * g⁻¹ := by rw [hmx]
          _ = g * x * g⁻¹ * (g * m * g⁻¹) := by group
    · rintro ⟨⟨hyρ, hyH⟩, hyx⟩
      refine ⟨g⁻¹ * y * g, ⟨⟨?_, (H z).mul_mem ((H z).mul_mem ((H z).inv_mem hg) hyH) hg⟩, ?_⟩,
        by group⟩
      · calc g⁻¹ * y * g * ρ = g⁻¹ * (y * (g * ρ * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * ρ * g⁻¹) * y) * g := by rw [hyρ]
          _ = ρ * (g⁻¹ * y * g) := by group
      · calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyx]
          _ = x * (g⁻¹ * y * g) := by group
  rw [← hmap]
  exact h1

omit [Finite G] in
theorem commute_of_map_conj {X : Subgroup G} (g : G)
    (hX : ∀ a ∈ X.map (MulAut.conj g).toMonoidHom, ∀ b ∈ X.map (MulAut.conj g).toMonoidHom,
      a * b = b * a) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  intro a ha b hb
  have h1 := hX _ (Subgroup.mem_map_of_mem _ ha) _ (Subgroup.mem_map_of_mem _ hb)
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul]
  exact h1

omit [Finite G] in
theorem mem_isSylowOf_centralizer_inf_of_orderOf_two {ρ x : G}
    (hxρ : x ∈ centralizer ({ρ} : Set G)) (hxH : x ∈ H z) (hx2 : orderOf x = 2) {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    x ∈ X := by
  have hxM : x ∈ centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G) :=
    ⟨⟨hxρ, hxH⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hcent : ∀ c ∈ centralizer ({ρ} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G),
      c ∈ centralizer (Subgroup.zpowers x : Set G) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact (Commute.zpow_left
      (show Commute x c from (mem_centralizer_singleton_iff.mp hc.2).symm) k).eq
  have hle : Subgroup.zpowers x ≤ X := le_isSylowOf_of_isPGroup_of_le_normalizer hX
    (Subgroup.zpowers_le.mpr hxM)
    (fun c hc => centralizer_le_normalizer (Subgroup.zpowers x) (hcent c hc)) hxp
  exact hle (Subgroup.mem_zpowers x)

end Conj

section Inversion

omit [Finite G] in
private theorem commute_of_sq_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) : a * b = b * a := by
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
  exact h1.symm

theorem mul_conj_inv_eq_inv_of_fixed (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {x : G} (hxH : x ∈ H z) (hxx : x * x = 1)
    (hV : fixDimV h ⟨x, hxH⟩ = 4) {j : G} (hj : j ∈ J z)
    (hfix : conjV h ⟨x, hxH⟩ (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩) :
    x * j * x⁻¹ = j⁻¹ := by
  obtain ⟨ū, hū⟩ := exists_mul_inv_eq_of_fixDimV_eq_four h hxH hxx hV hfix
  obtain ⟨u, rfl⟩ := QuotientV.pi_surjective z ū
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  let j' : J z := conjJ' z ⟨x, hxH⟩ u * u⁻¹
  have hj'G : (j' : G) = x * (u : G) * x⁻¹ * (u : G)⁻¹ := by
    simp only [j', Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
  have hpi : QuotientV.pi z j' = QuotientV.pi z ⟨j, hj⟩ := by
    show QuotientV.pi z (conjJ' z ⟨x, hxH⟩ u * u⁻¹) = _
    rw [map_mul, map_inv, ← conjV_mk h ⟨x, hxH⟩ u]
    exact hū
  have hxjx : x * (j' : G) * x⁻¹ = (j' : G)⁻¹ := by
    rw [hj'G, hxinv]
    calc x * (x * (u : G) * x * (u : G)⁻¹) * x = (x * x) * (u : G) * x * (u : G)⁻¹ * x := by
          group
      _ = (u : G) * x * (u : G)⁻¹ * x := by rw [hxx, one_mul]
      _ = (x * (u : G) * x * (u : G)⁻¹)⁻¹ := by
          have e : (x * (u : G) * x * (u : G)⁻¹)⁻¹ = (u : G) * x⁻¹ * (u : G)⁻¹ * x⁻¹ := by group
          rw [e, hxinv]
  have hcJ : (j' : G)⁻¹ * j ∈ J z := (J z).mul_mem ((J z).inv_mem j'.2) hj
  have hc : (j' : G)⁻¹ * j ∈ centerIn (J z) := by
    refine (pi_eq_one_iff_mem_centerIn hcJ).mp ?_
    have : (⟨(j' : G)⁻¹ * j, hcJ⟩ : J z) = j'⁻¹ * ⟨j, hj⟩ := rfl
    rw [this, map_mul, map_inv, hpi, inv_mul_cancel]
  have hcc : ((j' : G)⁻¹ * j) * ((j' : G)⁻¹ * j) = 1 := centerIn_J_sq h hc
  have hxc : ((j' : G)⁻¹ * j) * x = x * ((j' : G)⁻¹ * j) :=
    mem_centralizer_singleton_iff.mp (centerIn_J_le_centralizer_of_mem_H hZ hxH hc)
  have hcj : (j' : G) * ((j' : G)⁻¹ * j) = ((j' : G)⁻¹ * j) * (j' : G) :=
    Subgroup.mem_centralizer_iff.mp hc.2 (j' : G) j'.2
  set c : G := (j' : G)⁻¹ * j with hcdef
  have hjeq : j = (j' : G) * c := by rw [hcdef]; group
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hxcx : x * c * x⁻¹ = c := by
    calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [← hxc]
      _ = c := by group
  have hcomm : (j' : G)⁻¹ * c = c * (j' : G)⁻¹ := (show Commute (j' : G) c from hcj).inv_left.eq
  calc x * j * x⁻¹ = (x * (j' : G) * x⁻¹) * (x * c * x⁻¹) := by rw [hjeq]; group
    _ = (j' : G)⁻¹ * c := by rw [hxjx, hxcx]
    _ = c * (j' : G)⁻¹ := hcomm
    _ = c⁻¹ * (j' : G)⁻¹ := by rw [hcinv]
    _ = ((j' : G) * c)⁻¹ := by group
    _ = j⁻¹ := by rw [← hjeq]

theorem conjV_pi_eq_of_commute (h : Tim79a.ParrottHyp z) {x : ↥(H z)} {b : G} (hb : b ∈ J z)
    (hxb : (x : G) * b = b * (x : G)) :
    conjV h x (QuotientV.pi z ⟨b, hb⟩) = QuotientV.pi z ⟨b, hb⟩ :=
  mem_autFixedSubgroup.mp (pi_mem_autFixedSubgroup_conjV h hb hxb)

theorem mul_self_eq_one_of_commute (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {x : G} (hxH : x ∈ H z) (hxx : x * x = 1)
    (hV : fixDimV h ⟨x, hxH⟩ = 4) {j : G} (hj : j ∈ J z) (hjx : j * x = x * j) :
    j * j = 1 := by
  have h1 := mul_conj_inv_eq_inv_of_fixed h hZ hxH hxx hV hj
    (conjV_pi_eq_of_commute h hj hjx.symm)
  have h2 : x * j * x⁻¹ = j := by
    calc x * j * x⁻¹ = j * x * x⁻¹ := by rw [← hjx]
      _ = j := by group
  rw [h2] at h1
  exact mul_eq_one_iff_eq_inv.mpr h1

theorem commute_of_commute_of_fixDimV_eq_four (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {x : G} (hxH : x ∈ H z) (hxx : x * x = 1)
    (hV : fixDimV h ⟨x, hxH⟩ = 4) {a b : G} (ha : a ∈ J z) (hb : b ∈ J z) (hax : a * x = x * a)
    (hbx : b * x = x * b) : a * b = b * a := by
  refine commute_of_sq_eq_one (mul_self_eq_one_of_commute h hZ hxH hxx hV ha hax)
    (mul_self_eq_one_of_commute h hZ hxH hxx hV hb hbx)
    (mul_self_eq_one_of_commute h hZ hxH hxx hV ((J z).mul_mem ha hb) ?_)
  calc a * b * x = a * (x * b) := by rw [mul_assoc, hbx]
    _ = x * a * b := by rw [← mul_assoc, hax]
    _ = x * (a * b) := by rw [mul_assoc]

end Inversion

section Relation

variable (h : Tim79a.ParrottHyp z)

theorem pi_relation (x s : ↥(H z)) {j m c : G} (hj : j ∈ J z) (hm : m ∈ J z)
    (hc : c ∈ centerIn (J z))
    (hrel : j * (s : G) = ((x : G) * j * (x : G)⁻¹) * c * (m * (s : G) * m⁻¹)) :
    QuotientV.pi z ⟨j, hj⟩ =
      conjV h x (QuotientV.pi z ⟨j, hj⟩) * QuotientV.pi z ⟨m, hm⟩ *
        conjV h s (QuotientV.pi z ⟨m, hm⟩) := by
  have hxj : (x : G) * j * (x : G)⁻¹ ∈ J z := H_conj_mem_J x hj
  have hsm : (s : G) * m * (s : G)⁻¹ ∈ J z := H_conj_mem_J s hm
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  have hinv : ∀ v : QuotientV.V z, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have hjeq : (⟨j, hj⟩ : J z) = ⟨(x : G) * j * (x : G)⁻¹, hxj⟩ * ⟨c, hc.1⟩ *
      (⟨m, hm⟩ * ⟨(s : G) * m * (s : G)⁻¹, hsm⟩⁻¹) := by
    apply Subtype.ext
    show j = ((x : G) * j * (x : G)⁻¹) * c * (m * ((s : G) * m * (s : G)⁻¹)⁻¹)
    calc j = (j * (s : G)) * (s : G)⁻¹ := by group
      _ = (((x : G) * j * (x : G)⁻¹) * c * (m * (s : G) * m⁻¹)) * (s : G)⁻¹ := by rw [hrel]
      _ = _ := by group
  have h1 := congrArg (QuotientV.pi z) hjeq
  rw [map_mul, map_mul, map_mul, map_inv, (pi_eq_one_iff_mem_centerIn hc.1).mpr hc, mul_one,
    ← conjV_pi_conj h x hj, ← conjV_pi_conj h s hm, hinv, ← mul_assoc] at h1
  exact h1

end Relation

section Lift

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem exists_conj_of_orderOf_three_of_qH_eq (K : Subgroup ↥(H z)) {g g' : ↥(H z)} (hg : g ∈ K)
    (hg' : g' ∈ K) (hg3 : orderOf g = 3) (hg'3 : orderOf g' = 3) (hq : qH D g = qH D g') :
    ∃ j ∈ K, qH D j = 1 ∧ g' = j * g * j⁻¹ := by
  have hcos : (⟨g', hg'⟩ : ↥K) * (⟨g, hg⟩ : ↥K)⁻¹ ∈ ((J z).subgroupOf (H z)).subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    change g' * g⁻¹ ∈ (J z).subgroupOf (H z)
    rw [J_mem_iff D, map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨j, hj, hjconj⟩ := CFSG.GroupTheory.exists_conj_of_order_three_of_mul_inv_mem
    (isPGroup_J_subgroupOf (z := z)).comap_subtype
    (by rw [Subgroup.orderOf_mk, hg'3]) (by rw [Subgroup.orderOf_mk, hg3]) hcos
  refine ⟨(j : ↥(H z)), j.2, (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mp hj), ?_⟩
  exact (congrArg Subtype.val hjconj).symm

theorem exists_zpow_orderOf_three_of_qH (y : ↥(H z)) (hy : orderOf (qH D y) = 3) :
    ∃ n : ℤ, orderOf (y ^ n) = 3 ∧ qH D (y ^ n) = qH D y := by
  classical
  have h3dvd : 3 ∣ orderOf y := by
    have h1 := orderOf_map_dvd (qH D) y
    rwa [hy] at h1
  set k : ℕ := orderOf (y ^ 3) with hk
  have hk_eq : k = orderOf y / 3 := by
    rw [hk, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) h3dvd]
  have hz0ord : orderOf (y ^ k) = 3 := by
    rw [hk_eq]
    exact orderOf_pow_orderOf_div (x := y) (n := 3) (orderOf_pos y).ne' h3dvd
  have hq0 : qH D (y ^ k) = (qH D y) ^ k := map_pow _ _ _
  have hne : (qH D y) ^ k ≠ 1 := by
    intro h1
    rw [← hq0] at h1
    have hJmem : y ^ k ∈ (J z).subgroupOf (H z) := (J_mem_iff D _).mpr h1
    have hJ2 : IsPGroup 2 ((J z).subgroupOf (H z)) := isPGroup_J_subgroupOf (z := z)
    have hne1 : (⟨y ^ k, hJmem⟩ : ↥((J z).subgroupOf (H z))) ≠ 1 := by
      intro h2
      have h3 : y ^ k = 1 := by simpa using congrArg Subtype.val h2
      rw [h3, orderOf_one] at hz0ord
      exact absurd hz0ord (by norm_num)
    have h2dvd := hJ2.dvd_orderOf hne1
    rw [Subgroup.orderOf_mk, hz0ord] at h2dvd
    exact (by norm_num : ¬ (2 ∣ 3)) h2dvd
  have hmod : (qH D y) ^ k = (qH D y) ^ (k % 3) := by rw [← pow_mod_orderOf, hy]
  have hkmod : k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : k % 3 ≠ 0 := by
      intro h0
      apply hne
      rw [hmod, h0, pow_zero]
    omega
  rcases hkmod with h1 | h2
  · refine ⟨k, ?_, ?_⟩
    · rw [zpow_natCast]
      exact hz0ord
    · rw [zpow_natCast, hq0, hmod, h1, pow_one]
  · refine ⟨-(k : ℤ), ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, orderOf_inv]
      exact hz0ord
    · have hx3 : (qH D y) ^ 3 = 1 := by
        rw [← hy]
        exact pow_orderOf_eq_one _
      rw [zpow_neg, zpow_natCast, map_inv, hq0, hmod, h2]
      apply inv_eq_of_mul_eq_one_left
      rw [← pow_succ']
      exact hx3

theorem inv_mul_mem_J_of_qH_eq {c g : G} (hc : c ∈ H z) (hg : g ∈ H z)
    (hq : qH D ⟨c, hc⟩ = qH D ⟨g, hg⟩) : c⁻¹ * g ∈ J z := by
  have h1 : (⟨c, hc⟩ : ↥(H z))⁻¹ * ⟨g, hg⟩ ∈ (J z).subgroupOf (H z) :=
    (J_mem_iff D _).2 (by rw [map_mul, map_inv, hq, inv_mul_cancel])
  exact Subgroup.mem_subgroupOf.mp h1

end Lift

end CFSG.RankThree.GF2n.Parrott
