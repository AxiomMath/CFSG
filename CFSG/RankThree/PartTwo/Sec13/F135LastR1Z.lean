module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG
open scoped commutatorElement

theorem r1_exists_involution_lift {X : Type*} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hOodd : Odd (Nat.card O)) {a : X ⧸ O} (ha : a ≠ 1) (ha2 : a * a = 1) :
    ∃ z : X, z * z = 1 ∧ z ≠ 1 ∧ (z : X ⧸ O) = a := by
  obtain ⟨y', hy'⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, -, ⟨r, hr⟩, hψy⟩ := exists_two_part (QuotientGroup.mk' O) ha2 y' hy'
  have hyq : (y : X ⧸ O) = a := hψy
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact ha (hψy.symm.trans (map_one _))
  have hw : y * y ∈ O := (QuotientGroup.eq_one_iff (y * y)).mp <| by
    rw [QuotientGroup.mk_mul, hyq, ha2]
  have hyy : (y * y) ^ 2 ^ r = 1 := by
    rw [← sq, ← pow_mul, pow_mul', hr, one_pow]
  have hcop : Nat.Coprime (2 ^ r) (Nat.card O) :=
    Nat.Coprime.pow_left r ((Nat.prime_two.coprime_iff_not_dvd).mpr hOodd.not_two_dvd_nat)
  have hdvd : orderOf (y * y) ∣ Nat.gcd (2 ^ r) (Nat.card O) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyy) (Subgroup.orderOf_dvd_natCard O hw)
  rw [Nat.Coprime.gcd_eq_one hcop] at hdvd
  exact ⟨y, orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd), hy1, hyq⟩

theorem r1_exists_conj_of_two {X : Type*} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hOodd : Odd (Nat.card O)) {x y : X} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x : X ⧸ O) = (y : X ⧸ O)) : ∃ h ∈ O, h * x * h⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : ¬ 2 ∣ Nat.card O := hOodd.not_two_dvd_nat
  have hker : ∀ g : X, (QuotientGroup.mk' O) g = 1 ↔ g ∈ O :=
    fun g => QuotientGroup.eq_one_iff g
  have hxy' : (QuotientGroup.mk' O) x = (QuotientGroup.mk' O) y := hxy
  have hmem : ∀ h ∈ O, y * h * x⁻¹ ∈ O := fun h hh => by
    rw [← hker] at hh ⊢
    rw [map_mul, map_mul, hh, mul_one, map_inv, hxy', mul_inv_cancel]
  have hmem' : ∀ h ∈ O, y⁻¹ * h * x ∈ O := fun h hh => by
    rw [← hker] at hh ⊢
    rw [map_mul, map_mul, hh, mul_one, map_inv, hxy', inv_mul_cancel]
  let σ : Equiv.Perm O :=
    { toFun := fun h => ⟨y * h * x⁻¹, hmem h h.2⟩
      invFun := fun h => ⟨y⁻¹ * h * x, hmem' h h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc]) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext h
    simp only [pow_one, Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq]
    change y * (y * h * x⁻¹) * x⁻¹ = h
    have hx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx, inv_one]
    calc y * (y * (h : X) * x⁻¹) * x⁻¹ = (y * y) * h * (x⁻¹ * x⁻¹) := by group
      _ = h := by rw [hx', hy, one_mul, mul_one]
  have : Fintype O := Fintype.ofFinite O
  have hcard : ¬ 2 ∣ Fintype.card O := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨h, hh⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  have h1 : y * (h : X) * x⁻¹ = h := congrArg Subtype.val hh
  refine ⟨h, h.2, ?_⟩
  calc (h : X) * x * (h : X)⁻¹ = y * (h : X) * x⁻¹ * x * (h : X)⁻¹ := by rw [h1]
    _ = y := by group

theorem r1_frattini {X : Type*} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hOodd : Odd (Nat.card O)) {z : X} (hz2 : z * z = 1)
    (hzc : ∀ x : X, x * z * x⁻¹ * z⁻¹ ∈ O) (x : X) :
    ∃ o ∈ O, ∃ c ∈ Subgroup.centralizer ({z} : Set X), x = o * c := by
  have hy2 : (x * z * x⁻¹) * (x * z * x⁻¹) = 1 := by
    calc (x * z * x⁻¹) * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hmemO : z⁻¹ * (x * z * x⁻¹) ∈ O := by
    have h1 := Subgroup.Normal.conj_mem inferInstance _ (hzc x) z⁻¹
    have e : z⁻¹ * (x * z * x⁻¹ * z⁻¹) * z⁻¹⁻¹ = z⁻¹ * (x * z * x⁻¹) := by group
    rwa [e] at h1
  have hyz : (z : X ⧸ O) = ((x * z * x⁻¹ : X) : X ⧸ O) := QuotientGroup.eq.mpr hmemO
  obtain ⟨h, hhO, hh⟩ := r1_exists_conj_of_two O hOodd hz2 hy2 hyz
  refine ⟨h, hhO, h⁻¹ * x, ?_, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h⁻¹ * x * z = h⁻¹ * (x * z * x⁻¹) * x := by group
    _ = h⁻¹ * (h * z * h⁻¹) * x := by rw [hh]
    _ = z * (h⁻¹ * x) := by group

theorem r1_perfect_of_sup_eq_top {X : Type*} [Group X] (O : Subgroup X) [O.Normal] (Y : Subgroup X)
    (hXY : ∀ x : X, ∃ o ∈ O, ∃ y ∈ Y, x = o * y) (hperf : Group.IsPerfect (X ⧸ O)) :
    Group.IsPerfect (Y ⧸ O.subgroupOf Y) := by
  let φ : Y →* X ⧸ O := (QuotientGroup.mk' O).comp Y.subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, ho, y, hy, rfl⟩ := hXY x
    refine ⟨⟨y, hy⟩, ?_⟩
    have ho1 : (o : X ⧸ O) = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    show (y : X ⧸ O) = ((o * y : X) : X ⧸ O)
    rw [QuotientGroup.mk_mul, ho1, one_mul]
  have hker : φ.ker = O.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (y : X)
  let e : Y ⧸ O.subgroupOf Y ≃* X ⧸ O :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem r1c_eq_one_or_eq_of_natCard_two {G : Type*} [Group G] (S : Subgroup G)
    (hS : Nat.card S = 2) {a : G} (ha : a ∈ S) (ha1 : a ≠ 1) {g : G} (hg : g ∈ S) :
    g = 1 ∨ g = a := by
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hS
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  · right
    have hA : (⟨a, ha⟩ : S) = u := hu ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
    have hG : (⟨g, hg⟩ : S) = u := hu ⟨g, hg⟩ (fun h => hg1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (hG.trans hA.symm)

theorem r1c_odd_subgroupOf {X : Type*} [Group X] (O Y : Subgroup X) (hO : Odd (Nat.card O)) :
    Odd (Nat.card (O.subgroupOf Y)) :=
  Odd.of_dvd_nat hO
    (Subgroup.card_comap_dvd_of_injective O Y.subtype (Subgroup.subtype_injective Y))

theorem r1_L_data {X : Type*} [Group X] [Finite X] (O θ : Subgroup X) [O.Normal] [θ.Normal]
    (hOodd : Odd (Nat.card O)) (hperf : Group.IsPerfect (X ⧸ O))
    (hcenter : Nat.card (Subgroup.center (X ⧸ O)) = 2)
    (e : X ⧸ θ ≃* alternatingGroup (Fin 7))
    (hθ : (Subgroup.center (X ⧸ O)).comap (QuotientGroup.mk' O) = θ) :
    ∃ z : X, z * z = 1 ∧ z ≠ 1 ∧ (∀ x : X, x * z * x⁻¹ * z⁻¹ ∈ O) ∧
      Odd (Nat.card (O.subgroupOf (Subgroup.centralizer ({z} : Set X)))) ∧
      Group.IsPerfect (↥(Subgroup.centralizer ({z} : Set X)) ⧸
        O.subgroupOf (Subgroup.centralizer ({z} : Set X))) ∧
      ∃ ψ : ↥(Subgroup.centralizer ({z} : Set X)) →* alternatingGroup (Fin 7),
        Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.zpowers (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
          ↥(Subgroup.centralizer ({z} : Set X))) ⊔
          O.subgroupOf (Subgroup.centralizer ({z} : Set X)) := by
  obtain ⟨s, hs, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center (X ⧸ O))).mp hcenter
  have hs2 : s ^ 2 = 1 := by
    have h := orderOf_dvd_natCard s
    rw [hcenter] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hsq : (s : X ⧸ O) * (s : X ⧸ O) = 1 := by
    simpa [pow_two] using congrArg Subtype.val hs2
  have ha1 : (s : X ⧸ O) ≠ 1 := fun h => hs (Subtype.ext h)
  obtain ⟨z, hz2, hz1, hza⟩ := r1_exists_involution_lift O hOodd ha1 hsq
  have hzc : ∀ x : X, x * z * x⁻¹ * z⁻¹ ∈ O := by
    intro x
    refine (QuotientGroup.eq_one_iff _).mp ?_
    have hcom : (x : X ⧸ O) * (s : X ⧸ O) = (s : X ⧸ O) * (x : X ⧸ O) :=
      Subgroup.mem_center_iff.mp s.2 (x : X ⧸ O)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hza]
    rw [hcom]
    group
  have hXY : ∀ x : X, ∃ o ∈ O, ∃ y ∈ Subgroup.centralizer ({z} : Set X), x = o * y :=
    fun x => r1_frattini O hOodd hz2 hzc x
  have hperfY := r1_perfect_of_sup_eq_top O (Subgroup.centralizer ({z} : Set X)) hXY hperf
  have hoddY := r1c_odd_subgroupOf O (Subgroup.centralizer ({z} : Set X)) hOodd
  have hOθ : ∀ o ∈ O, o ∈ θ := by
    intro o ho
    rw [← hθ, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff o).mpr ho]
    exact one_mem _
  refine ⟨z, hz2, hz1, hzc, hoddY, hperfY, e.toMonoidHom.comp
    ((QuotientGroup.mk' θ).comp (Subgroup.centralizer ({z} : Set X)).subtype), ?_, ?_⟩
  ·
    intro t
    obtain ⟨w, rfl⟩ := e.surjective t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨o, ho, c, hc, hxoc⟩ := r1_frattini O hOodd hz2 hzc x
    refine ⟨⟨c, hc⟩, ?_⟩
    have hmod : ((x : X) : X ⧸ θ) = ((c : X) : X ⧸ θ) := by
      rw [hxoc, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr (hOθ o ho), one_mul]
    show e ((c : X) : X ⧸ θ) = e ((x : X) : X ⧸ θ)
    rw [hmod]
  ·
    intro y hy
    have hy' : e ((y : X) : X ⧸ θ) = 1 := MonoidHom.mem_ker.mp hy
    have h1 : ((y : X) : X ⧸ θ) = 1 := e.injective (by rw [hy', map_one])
    have hyθ : (y : X) ∈ θ := (QuotientGroup.eq_one_iff _).mp h1
    have hyc : ((y : X) : X ⧸ O) ∈ Subgroup.center (X ⧸ O) := by
      rw [← hθ] at hyθ
      exact Subgroup.mem_comap.mp hyθ
    rcases r1c_eq_one_or_eq_of_natCard_two (Subgroup.center (X ⧸ O)) hcenter s.2 ha1 hyc with
      h | h
    ·
      have hyO : (y : X) ∈ O := (QuotientGroup.eq_one_iff _).mp h
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hyO)
    ·
      have hzy : z * (y : X) ∈ O := by
        refine (QuotientGroup.eq_one_iff _).mp ?_
        rw [QuotientGroup.mk_mul, hza, h, hsq]
      have hzY : z ∈ Subgroup.centralizer ({z} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have hzyY : z * (y : X) ∈ Subgroup.centralizer ({z} : Set X) := mul_mem hzY y.2
      have hw : (⟨z * (y : X), hzyY⟩ : ↥(Subgroup.centralizer ({z} : Set X))) ∈
          O.subgroupOf (Subgroup.centralizer ({z} : Set X)) :=
        Subgroup.mem_subgroupOf.mpr hzy
      have hprod := Subgroup.mul_mem_sup
        (Subgroup.mem_zpowers (⟨z, hzY⟩ : ↥(Subgroup.centralizer ({z} : Set X)))) hw
      have heq : (⟨z, hzY⟩ : ↥(Subgroup.centralizer ({z} : Set X))) * ⟨z * (y : X), hzyY⟩ = y :=
        Subtype.ext (by simp [← mul_assoc, hz2])
      rw [heq] at hprod
      exact hprod

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
