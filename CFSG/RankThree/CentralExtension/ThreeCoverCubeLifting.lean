module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian


public noncomputable section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped IsMulCommutative

variable {L T : Type*} [Group L] [Group T]

section Cubes

variable {Z : Subgroup L}

theorem commute_of_le_center (hZ : Z ≤ center L) (a b : Z) : Commute a b :=
  Subtype.ext (mem_center_iff.1 (hZ b.2) a)

@[expose] def centralCubes (hZ : Z ≤ center L) : Subgroup Z where
  carrier := {w | ∃ z : Z, z ^ 3 = w}
  one_mem' := ⟨1, one_pow 3⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, (commute_of_le_center hZ a b).mul_pow 3⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, inv_pow a 3⟩

theorem mem_centralCubes (hZ : Z ≤ center L) {w : Z} :
    w ∈ centralCubes hZ ↔ ∃ z : Z, z ^ 3 = w :=
  Iff.rfl

instance centralCubes_normal (hZ : Z ≤ center L) : (centralCubes hZ).Normal :=
  ⟨fun _ hn g => by
    obtain ⟨z, rfl⟩ := hn
    exact ⟨z, by rw [(commute_of_le_center hZ g (z ^ 3)).eq, mul_inv_cancel_right]⟩⟩

theorem pow_three_eq_one_quotient (hZ : Z ≤ center L) (w : Z ⧸ centralCubes hZ) : w ^ 3 = 1 := by
  induction w using QuotientGroup.induction_on with
  | H z => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact ⟨z, rfl⟩

end Cubes

section ClassTwo

theorem mul_pow_three_of_central {x y c : L} (hc : y * x = x * y * c) (hcc : c ∈ center L)
    (hx : x ^ 3 ∈ center L) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hcom : ∀ g : L, Commute c g := fun g => (mem_center_iff.1 hcc g).symm
  have hcx : x⁻¹ * c * x = c := by rw [mul_assoc, (hcom x).eq, inv_mul_cancel_left]
  have h1 : x⁻¹ * y * x = y * c := by
    rw [mul_assoc, hc, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : x⁻¹ * x⁻¹ * y * x * x = y * c * c := by
    calc x⁻¹ * x⁻¹ * y * x * x = x⁻¹ * (x⁻¹ * y * x) * x := by simp only [mul_assoc]
      _ = x⁻¹ * (y * c) * x := by rw [h1]
      _ = (x⁻¹ * y * x) * (x⁻¹ * c * x) := by group
      _ = y * c * c := by rw [h1, hcx]
  have h3 : x⁻¹ * x⁻¹ * x⁻¹ * y * x * x * x = y * c * c * c := by
    calc x⁻¹ * x⁻¹ * x⁻¹ * y * x * x * x = x⁻¹ * (x⁻¹ * x⁻¹ * y * x * x) * x := by
          simp only [mul_assoc]
      _ = x⁻¹ * (y * c * c) * x := by rw [h2]
      _ = (x⁻¹ * y * x) * (x⁻¹ * c * x) * (x⁻¹ * c * x) := by group
      _ = y * c * c * c := by rw [h1, hcx]
  have hc3 : c * c * c = 1 := by
    have hx' : y * (x * x * x) = (x * x * x) * y := by
      rw [← pow_three']; exact mem_center_iff.1 hx y
    have hy : x⁻¹ * x⁻¹ * x⁻¹ * y * x * x * x = y := by
      calc x⁻¹ * x⁻¹ * x⁻¹ * y * x * x * x = (x * x * x)⁻¹ * (y * (x * x * x)) := by group
        _ = (x * x * x)⁻¹ * ((x * x * x) * y) := by rw [hx']
        _ = y := inv_mul_cancel_left _ _
    rw [h3, mul_assoc, mul_assoc] at hy
    have h := mul_eq_left.1 hy
    rwa [← mul_assoc] at h
  calc (x * y) ^ 3 = (x * x * x) * (x⁻¹ * x⁻¹ * y * x * x) * (x⁻¹ * y * x) * y := by
        rw [pow_three']; group
    _ = (x * x * x) * (y * c * c) * (y * c) * y := by rw [h2, h1]
    _ = (x * x * x) * y * ((c * c) * y) * c * y := by simp only [mul_assoc]
    _ = (x * x * x) * y * (y * (c * c)) * c * y := by
        rw [((hcom y).mul_left (hcom y)).eq]
    _ = (x * x * x) * y * y * ((c * c * c) * y) := by simp only [mul_assoc]
    _ = (x * x * x) * y * y * (y * (c * c * c)) := by
        rw [(((hcom y).mul_left (hcom y)).mul_left (hcom y)).eq]
    _ = x ^ 3 * y ^ 3 := by rw [hc3, mul_one, pow_three', pow_three']; simp only [mul_assoc]

end ClassTwo

variable {π : L →* T}

section CubeClass

variable (hπ : Function.Surjective π) (hZ : π.ker ≤ center L)

theorem pow_three_mem_ker {x : L} (hx : π x ^ 3 = 1) : x ^ 3 ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_pow, hx]

@[expose] def cubeClass (t : T) : π.ker ⧸ centralCubes hZ :=
  haveI := Classical.propDecidable (t ^ 3 = 1)
  if h : t ^ 3 = 1 then
    QuotientGroup.mk ⟨Function.surjInv hπ t ^ 3,
      pow_three_mem_ker (by rw [Function.surjInv_eq hπ]; exact h)⟩
  else 1

theorem cubeClass_apply (x : L) (hx : x ^ 3 ∈ π.ker) :
    cubeClass hπ hZ (π x) = QuotientGroup.mk (⟨x ^ 3, hx⟩ : π.ker) := by
  have ht : π x ^ 3 = 1 := by rw [← map_pow]; exact hx
  rw [cubeClass, dite_eq_left ht, QuotientGroup.eq]
  have hc : (Function.surjInv hπ (π x))⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hπ (π x), inv_mul_cancel]
  refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, Subgroup.coe_mul, InvMemClass.coe_inv]
  generalize Function.surjInv hπ (π x) = y at hc ⊢
  have hcomm : Commute y (y⁻¹ * x) := mem_center_iff.1 (hZ hc) y
  rw [show x ^ 3 = (y * (y⁻¹ * x)) ^ 3 by rw [mul_inv_cancel_left], hcomm.mul_pow,
    inv_mul_cancel_left]

theorem cubeClass_conj (g t : T) (ht : t ^ 3 = 1) :
    cubeClass hπ hZ (g * t * g⁻¹) = cubeClass hπ hZ t := by
  obtain ⟨x, rfl⟩ := hπ t
  obtain ⟨y, rfl⟩ := hπ g
  have hx : x ^ 3 ∈ π.ker := pow_three_mem_ker ht
  have heq : (y * x * y⁻¹) ^ 3 = x ^ 3 := by
    rw [conj_pow, mem_center_iff.1 (hZ hx) y, mul_inv_cancel_right]
  have hyx : (y * x * y⁻¹) ^ 3 ∈ π.ker := heq ▸ hx
  rw [← map_inv, ← map_mul, ← map_mul, cubeClass_apply hπ hZ _ hyx, cubeClass_apply hπ hZ _ hx]
  congr 1
  exact Subtype.ext heq

theorem cubeClass_inv (t : T) (ht : t ^ 3 = 1) :
    cubeClass hπ hZ t⁻¹ = (cubeClass hπ hZ t)⁻¹ := by
  obtain ⟨x, rfl⟩ := hπ t
  have hx : x ^ 3 ∈ π.ker := pow_three_mem_ker ht
  have hx' : x⁻¹ ^ 3 ∈ π.ker := by rw [inv_pow]; exact π.ker.inv_mem hx
  rw [← map_inv, cubeClass_apply hπ hZ _ hx', cubeClass_apply hπ hZ _ hx, ← QuotientGroup.mk_inv]
  congr 1
  exact Subtype.ext (inv_pow x 3)

theorem cubeClass_mul {E : Subgroup T} [IsElementaryAbelian 3 E] {t u : T} (ht : t ∈ E)
    (hu : u ∈ E) : cubeClass hπ hZ (t * u) = cubeClass hπ hZ t * cubeClass hπ hZ u := by
  have ht3 : t ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hu3 : u ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  have htu : t * u = u * t := by
    have := mul_comm (⟨t, ht⟩ : E) ⟨u, hu⟩
    exact Subtype.ext_iff.1 this
  obtain ⟨x, rfl⟩ := hπ t
  obtain ⟨y, rfl⟩ := hπ u
  have hx : x ^ 3 ∈ π.ker := pow_three_mem_ker ht3
  have hy : y ^ 3 ∈ π.ker := pow_three_mem_ker hu3
  set c := (x * y)⁻¹ * (y * x) with hcdef
  have hcker : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_inv, map_mul, map_mul, htu, inv_mul_cancel]
  have hc : y * x = x * y * c := by rw [hcdef, mul_inv_cancel_left]
  have hxy : (x * y) ^ 3 = x ^ 3 * y ^ 3 := mul_pow_three_of_central hc (hZ hcker) (hZ hx)
  have hxy' : (x * y) ^ 3 ∈ π.ker := hxy ▸ π.ker.mul_mem hx hy
  rw [← map_mul, cubeClass_apply hπ hZ _ hxy', cubeClass_apply hπ hZ _ hx,
    cubeClass_apply hπ hZ _ hy, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hxy

theorem cubeClass_eq_one_iff (t : T) (ht : t ^ 3 = 1) :
    cubeClass hπ hZ t = 1 ↔ ∃ x, π x = t ∧ x ^ 3 = 1 := by
  constructor
  · intro h1
    obtain ⟨x, rfl⟩ := hπ t
    have hx : x ^ 3 ∈ π.ker := pow_three_mem_ker ht
    rw [cubeClass_apply hπ hZ x hx, QuotientGroup.eq_one_iff] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : (z : L) ^ 3 = x ^ 3 := by simpa using congrArg Subtype.val hz
    refine ⟨x * (z : L)⁻¹, by rw [map_mul, map_inv, z.2, inv_one, mul_one], ?_⟩
    have hcomm : Commute x (z : L)⁻¹ := mem_center_iff.1 (hZ (inv_mem z.2)) x
    rw [hcomm.mul_pow, inv_pow, hz', mul_inv_cancel]
  · rintro ⟨x, rfl, hx3⟩
    have hx : x ^ 3 ∈ π.ker := by rw [hx3]; exact π.ker.one_mem
    rw [cubeClass_apply hπ hZ x hx, QuotientGroup.eq_one_iff]
    exact ⟨1, Subtype.ext (by simp [hx3])⟩

@[expose] def cubeClassHom (E : Subgroup T) [IsElementaryAbelian 3 E] :
    E →* π.ker ⧸ centralCubes hZ where
  toFun t := cubeClass hπ hZ t
  map_one' := by
    rw [OneMemClass.coe_one, cubeClass_eq_one_iff hπ hZ 1 (one_pow 3)]
    exact ⟨1, map_one π, one_pow 3⟩
  map_mul' t u := by
    rw [Subgroup.coe_mul]
    exact cubeClass_mul hπ hZ t.2 u.2

theorem cubeClassHom_apply (E : Subgroup T) [IsElementaryAbelian 3 E] (t : E) :
    cubeClassHom hπ hZ E t = cubeClass hπ hZ t :=
  rfl

theorem mem_ker_cubeClassHom_iff (E : Subgroup T) [IsElementaryAbelian 3 E] (t : E) :
    t ∈ (cubeClassHom hπ hZ E).ker ↔ ∃ x, π x = t ∧ x ^ 3 = 1 := by
  rw [MonoidHom.mem_ker, cubeClassHom_apply]
  exact cubeClass_eq_one_iff hπ hZ t (elemPow_eq_one_of_isElementaryAbelian _ t.2)

theorem exists_orderOf_lift_iff (t : T) (ht : orderOf t = 3) :
    (∃ x, π x = t ∧ orderOf x = 3) ↔ cubeClass hπ hZ t = 1 := by
  have ht3 : t ^ 3 = 1 := ht ▸ pow_orderOf_eq_one t
  rw [cubeClass_eq_one_iff hπ hZ t ht3]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · rintro ⟨x, hx, hxo⟩
    exact ⟨x, hx, hxo ▸ pow_orderOf_eq_one x⟩
  · rintro ⟨x, hx, hx3⟩
    refine ⟨x, hx, orderOf_eq_prime hx3 fun h1 => ?_⟩
    rw [h1, map_one] at hx
    rw [← hx, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem cubeClass_eq_one_of_isConj_inv (t : T) (ht : t ^ 3 = 1) (hconj : IsConj t t⁻¹) :
    cubeClass hπ hZ t = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have h1 : (cubeClass hπ hZ t)⁻¹ = cubeClass hπ hZ t := by
    rw [← cubeClass_inv hπ hZ t ht, ← hg, cubeClass_conj hπ hZ g t ht]
  set w := cubeClass hπ hZ t
  have hw2 : w * w = 1 := by nth_rewrite 2 [← h1]; exact mul_inv_cancel w
  have h3 := pow_three_eq_one_quotient hZ w
  rwa [pow_three', hw2, one_mul] at h3

theorem exists_isElementaryAbelian_lift_of_cubeClassHom_eq_one
    {L T : Type*} [Group L] [Group T] [Finite L]
    {π : L →* T} (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center L)
    {E : Subgroup T} [IsElementaryAbelian 3 E]
    (hcomm : ∀ x y : L, x ∈ E.comap π → y ∈ E.comap π → x * y = y * x)
    (hclass : cubeClassHom hπ hZ E = 1)
    (hkerexp : ∀ z ∈ π.ker, z ^ 3 = 1) :
    ∃ U : Subgroup L, IsElementaryAbelian 3 U ∧ U.map π = E ∧
      π.ker ≤ U ∧ Nat.card U = Nat.card π.ker * Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite T := Finite.of_surjective π hπ
  let P : Subgroup L := E.comap π
  have hPcomm : IsMulCommutative P :=
    ⟨⟨fun x y => Subtype.ext (hcomm x y x.2 y.2)⟩⟩
  letI : IsMulCommutative P := hPcomm
  letI : CommGroup P := IsMulCommutative.instCommGroup
  let K : Subgroup P := (powMonoidHom 3 : P →* P).ker
  have hKexp : ∀ k : K, k ^ 3 = 1 := by
    intro k
    have hk : (k : P) ∈ (powMonoidHom 3 : P →* P).ker := k.2
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hk
    exact Subtype.ext hk
  have hKelem : IsElementaryAbelian 3 K :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hKexp }
  let U : Subgroup L := K.map P.subtype
  have hUelem : IsElementaryAbelian 3 U :=
    IsElementaryAbelian.map_subtype (p := 3) (K := P) (H := K)
  have hker_le : π.ker ≤ U := by
    intro z hz
    have hzP : z ∈ P := by
      change π z ∈ E
      rw [MonoidHom.mem_ker.mp hz]
      exact E.one_mem
    have hzK : (⟨z, hzP⟩ : P) ∈ K := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      exact Subtype.ext (hkerexp z hz)
    exact Subgroup.mem_map.mpr ⟨⟨z, hzP⟩, hzK, rfl⟩
  have hmap : U.map π = E := by
    apply le_antisymm
    · rintro _ ⟨x, hxU, rfl⟩
      obtain ⟨p, hpK, rfl⟩ := hxU
      change π (p : L) ∈ E
      exact p.2
    · intro e he
      have hclass_e : cubeClassHom hπ hZ E ⟨e, he⟩ = 1 := by
        simpa [hclass]
      have hker_e : (⟨e, he⟩ : E) ∈ (cubeClassHom hπ hZ E).ker := by
        rw [MonoidHom.mem_ker]
        exact hclass_e
      obtain ⟨x, hπx, hx3⟩ :=
        (mem_ker_cubeClassHom_iff hπ hZ E ⟨e, he⟩).1 hker_e
      have hxP : x ∈ P := by
        change π x ∈ E
        rw [hπx]
        exact he
      have hxK : (⟨x, hxP⟩ : P) ∈ K := by
        rw [MonoidHom.mem_ker, powMonoidHom_apply]
        exact Subtype.ext hx3
      refine Subgroup.mem_map.mpr ⟨x, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, hxK, rfl⟩
      · simpa using hπx
  refine ⟨U, hUelem, hmap, hker_le, ?_⟩
  have hker_card : Nat.card (π.domRestrict U).ker = Nat.card π.ker := by
    rw [MonoidHom.ker_domRestrict (K := U) π]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  have hrange : (π.domRestrict U).range = E := by
    rw [MonoidHom.domRestrict_range, hmap]
  have hcard := Subgroup.card_ker_mul_card_range (π.domRestrict U)
  rw [hker_card, hrange] at hcard
  exact hcard.symm

end CubeClass

section TwoLift

theorem mem_of_two_power_of_map_mem (hZ : π.ker ≤ center L) (hZ3 : IsPGroup 3 π.ker)
    {U : Subgroup L} (hU : IsPGroup 2 U) {g : L} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (hgU : π g ∈ U.map π) : g ∈ U := by
  obtain ⟨u, hu, hπu⟩ := hgU
  obtain ⟨j, hj⟩ := hU ⟨u, hu⟩
  have hj' : u ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  set z := g * u⁻¹ with hz
  have hzker : z ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hπu, mul_inv_cancel]
  have hzc : Commute z u := (mem_center_iff.1 (hZ hzker) u).symm
  have hgzu : g = z * u := by rw [hz, inv_mul_cancel_right]
  have hm : z ^ 2 ^ (k + j) = 1 := by
    have h1 : g ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul, hg, one_pow]
    have h2 : u ^ 2 ^ (k + j) = 1 := by rw [pow_add, mul_comm, pow_mul, hj', one_pow]
    rw [hgzu, hzc.mul_pow, h2, mul_one] at h1
    exact h1
  obtain ⟨i, hi⟩ := hZ3 ⟨z, hzker⟩
  have hi' : z ^ 3 ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hcop : Nat.Coprime (2 ^ (k + j)) (3 ^ i) := Nat.Coprime.pow _ _ (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hi')
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  rw [hgzu, hd, one_mul]
  exact hu

theorem le_of_two_lift (hZ : π.ker ≤ center L) (hZ3 : IsPGroup 3 π.ker) {U U' : Subgroup L}
    (hU : IsPGroup 2 U) (hU' : IsPGroup 2 U') (h : U'.map π ≤ U.map π) : U' ≤ U := by
  intro g hg
  obtain ⟨k, hk⟩ := hU' ⟨g, hg⟩
  exact mem_of_two_power_of_map_mem hZ hZ3 hU (by simpa using congrArg Subtype.val hk)
    (h (mem_map_of_mem π hg))

theorem exists_unique_two_lift [Finite L] (hπ : Function.Surjective π) (hZ : π.ker ≤ center L)
    (hZ3 : IsPGroup 3 π.ker) {V : Subgroup T} (hV : IsPGroup 2 V) :
    ∃! U : Subgroup L, IsPGroup 2 U ∧ U.map π = V ∧ Nat.card U = Nat.card V := by
  have : Finite T := Finite.of_surjective π hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hV
  set K := V.comap π with hKdef
  have hKV : K.map π = V := map_comap_eq_self_of_surjective hπ V
  have hdvd : Nat.card V ∣ Nat.card K := by
    have h := card_dvd_of_surjective (π.subgroupMap_surjective K)
    rwa [hKV] at h
  rw [hb] at hdvd
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set U := P.map K.subtype with hUdef
  have hUcard : Nat.card U = 2 ^ b := by
    rw [hUdef, card_map_of_injective K.subtype_injective, hP]
  have hU2 : IsPGroup 2 U := IsPGroup.of_card hUcard
  have hUK : U ≤ K := map_subtype_le P
  have hdisj : Disjoint π.ker U := IsPGroup.disjoint_of_coprime hZ3 hU2 (by norm_num)
  have hinj : Function.Injective (π.domRestrict U) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : (u : L) ∈ π.ker := hu
    exact Subtype.ext (disjoint_iff_inf_le.1 hdisj ⟨hu', u.2⟩)
  have hmapcard : Nat.card (U.map π) = Nat.card U := by
    rw [← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hUV : U.map π = V := by
    refine eq_of_le_of_card_ge (map_le_iff_le_comap.2 hUK) ?_
    rw [hmapcard, hUcard, hb]
  refine ⟨U, ⟨hU2, hUV, by rw [hUcard, hb]⟩, ?_⟩
  rintro U' ⟨hU'2, hU'V, -⟩
  exact le_antisymm (le_of_two_lift hZ hZ3 hU2 hU'2 (hU'V.trans hUV.symm).le)
    (le_of_two_lift hZ hZ3 hU'2 hU2 (hUV.trans hU'V.symm).le)

theorem two_lift_structure (hZ : π.ker ≤ center L) (hZ3 : IsPGroup 3 π.ker) {U : Subgroup L}
    (hU : IsPGroup 2 U) {V : Subgroup T} (hUV : U.map π = V) :
    π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
      (normalizer (V : Set T)).comap π = normalizer (U : Set L) ∧
      (π.domRestrict (normalizer (U : Set L))).ker.map (normalizer (U : Set L)).subtype =
        π.ker := by
  have hdisj : Disjoint π.ker U := IsPGroup.disjoint_of_coprime hZ3 hU (by norm_num)
  have hpow : ∀ g ∈ U, ∃ k : ℕ, g ^ 2 ^ k = 1 := fun g hg => by
    obtain ⟨k, hk⟩ := hU ⟨g, hg⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hmemU : ∀ g : L, (∃ k : ℕ, g ^ 2 ^ k = 1) → π g ∈ V → g ∈ U := by
    rintro g ⟨k, hk⟩ hg
    exact mem_of_two_power_of_map_mem hZ hZ3 hU hk (hUV ▸ hg)
  have hπU : ∀ g ∈ U, π g ∈ V := fun g hg => hUV ▸ mem_map_of_mem π hg
  refine ⟨disjoint_iff.1 hdisj, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le (fun k hk => ?_) (fun u hu => hπU u hu)) (fun k hk => ?_)
    · rw [mem_comap, (MonoidHom.mem_ker).1 hk]
      exact V.one_mem
    · have hk' : π k ∈ U.map π := hUV ▸ hk
      obtain ⟨u, hu, hπu⟩ := hk'
      have hc : k * u⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπu, mul_inv_cancel]
      have h := mul_mem_sup hc hu
      rwa [inv_mul_cancel_right] at h
  · ext x
    rw [mem_comap]
    constructor
    · intro hx
      rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, hk⟩ := hpow h hh
        refine hmemU _ ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩ ?_
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.1 hx (π h)).1 (hπU h hh)
      · intro hh
        obtain ⟨k, hk⟩ := hpow _ hh
        have hk' : h ^ 2 ^ k = 1 := by
          rw [conj_pow] at hk
          have h' := congrArg (fun g => x⁻¹ * g * x) hk
          simpa [mul_assoc] using h'
        refine hmemU h ⟨k, hk'⟩ ?_
        have h1 := hπU _ hh
        rw [map_mul, map_mul, map_inv] at h1
        exact (mem_normalizer_iff.1 hx (π h)).2 h1
    · intro hx
      have h := le_normalizer_map (H := U) π (mem_map_of_mem π hx)
      rwa [hUV] at h
  · rw [MonoidHom.ker_domRestrict, subgroupOf_map_subtype]
    refine inf_eq_left.2 fun z hz => ?_
    rw [mem_normalizer_iff]
    intro h
    rw [← mem_center_iff.1 (hZ hz) h, mul_inv_cancel_right]

theorem lift_mem_normalizer (hZ : π.ker ≤ center L) (hZ3 : IsPGroup 3 π.ker)
    {U : Subgroup L} (hU : IsPGroup 2 U) {V : Subgroup T} (hUV : U.map π = V)
    {E : Subgroup T} (hEV : E ≤ normalizer (V : Set T)) {x : L} (hx : π x ∈ E) :
    x ∈ normalizer (U : Set L) := by
  rw [← (two_lift_structure hZ hZ3 hU hUV).2.2.1]
  exact hEV hx

theorem cubeClass_injOn_and_normalizer_eq_centralizer (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center L) (hZ3 : IsPGroup 3 π.ker) {U : Subgroup L} (hU : IsPGroup 2 U)
    {V : Subgroup T} (hUV : U.map π = V)
    (hno : ∀ x ∈ normalizer (U : Set L), x ^ 3 = 1 → x ∈ π.ker) (E : Subgroup T)
    [IsElementaryAbelian 3 E] (hEV : E ≤ normalizer (V : Set T)) :
    Set.InjOn (cubeClass hπ hZ) E ∧ normalizer (E : Set T) = centralizer (E : Set T) := by
  have hinj : Set.InjOn (cubeClass hπ hZ) E := by
    intro t ht t' ht' htt'
    have ht'3 : t' ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian t' ht'
    have hmem : t * t'⁻¹ ∈ E := E.mul_mem ht (E.inv_mem ht')
    have h3 : (t * t'⁻¹) ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hmem
    have h1 : cubeClass hπ hZ (t * t'⁻¹) = 1 := by
      rw [cubeClass_mul hπ hZ ht (E.inv_mem ht'), cubeClass_inv hπ hZ t' ht'3, htt',
        mul_inv_cancel]
    obtain ⟨x, hx, hx3⟩ := (cubeClass_eq_one_iff hπ hZ _ h3).1 h1
    have hxN := lift_mem_normalizer hZ hZ3 hU hUV hEV (hx ▸ hmem)
    have hxk := hno x hxN hx3
    rw [MonoidHom.mem_ker, hx] at hxk
    exact mul_inv_eq_one.1 hxk
  refine ⟨hinj, le_antisymm (fun g hg => ?_) (centralizer_le_normalizer _)⟩
  rw [mem_centralizer_iff]
  intro h hh
  have hgh : g * h * g⁻¹ ∈ E := (mem_normalizer_iff.1 hg h).1 hh
  have h3 : h ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian h hh
  have heq := hinj hgh hh (cubeClass_conj hπ hZ g h h3)
  exact (mul_inv_eq_iff_eq_mul.1 heq).symm

end TwoLift

end CFSG.RankThree.CentralExtension
