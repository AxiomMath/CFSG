module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddReeTICount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup

section

variable {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y}

omit [Finite Y] in
private theorem orderOf_eq_seven_of_mem {X : Subgroup Y} (hX : Nat.card X = 7)
    {x : Y} (hx : x ∈ X) (hx1 : x ≠ 1) : orderOf x = 7 := by
  have hdvd : orderOf x ∣ 7 := by
    simpa [hX] using Subgroup.orderOf_dvd_natCard X hx
  rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

private theorem exists_ne_one_of_card_seven {X : Subgroup Y} (hX : Nat.card X = 7) :
    ∃ x ∈ X, x ≠ 1 := by
  have : Fintype ↥X := Fintype.ofFinite _
  have h1 : 1 < Fintype.card ↥X := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card h1 (1 : ↥X)
  exact ⟨(x : Y), x.2, fun hcon => hx (Subtype.ext hcon)⟩

omit [Finite Y] in
private theorem le_centralizer_self_of_card_seven {X : Subgroup Y} (hX : Nat.card X = 7) :
    X ≤ centralizer (X : Set Y) := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : IsCyclic ↥X := isCyclic_of_prime_card (p := 7) hX
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥X) (⟨x, hx⟩ : ↥X))

private theorem not_inverts_of_mem_normalizer (h : TICountHyp S) {X' : Subgroup Y}
    (hX' : Nat.card X' = 7) (hX'N : X' ≤ normalizer ((S : Subgroup Y) : Set Y))
    {y : Y} (hyN : y ∈ normalizer ((S : Subgroup Y) : Set Y)) (hy : orderOf y = 2) :
    ¬ (∀ x ∈ X', y * x * y⁻¹ = x⁻¹) := by
  intro hinv
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_seven hX'
  have hyS : y ∈ (S : Subgroup Y) := h.mem_of_mem_normalizer hy hyN
  have hxN : x ∈ normalizer ((S : Subgroup Y) : Set Y) := hX'N hx
  have hxy : x * y⁻¹ * x⁻¹ ∈ (S : Subgroup Y) := by
    rw [Subgroup.mem_normalizer_iff] at hxN
    exact (hxN y⁻¹).mp (Subgroup.inv_mem _ hyS)
  have hmul : y * (x * y⁻¹ * x⁻¹) ∈ (S : Subgroup Y) :=
    Subgroup.mul_mem _ hyS hxy
  have heq : y * (x * y⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ := by
    calc y * (x * y⁻¹ * x⁻¹) = (y * x * y⁻¹) * x⁻¹ := by group
      _ = x⁻¹ * x⁻¹ := by rw [hinv x hx]
  have hmem : x⁻¹ * x⁻¹ ∈ (S : Subgroup Y) := heq ▸ hmul
  have h8 : orderOf (x⁻¹ * x⁻¹) ∣ 8 := by
    simpa [h.card_eight] using Subgroup.orderOf_dvd_natCard (S : Subgroup Y) hmem
  have hx7 : orderOf x = 7 := orderOf_eq_seven_of_mem hX' hx hx1
  have h7 : orderOf (x⁻¹ * x⁻¹) ∣ 7 := by
    have hpow : x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by simp [pow_two, mul_inv_rev]
    rw [hpow, orderOf_inv]
    calc orderOf (x ^ 2) ∣ orderOf x := orderOf_pow_dvd 2
      _ = 7 := hx7
  have hone : orderOf (x⁻¹ * x⁻¹) = 1 := by
    have hd : orderOf (x⁻¹ * x⁻¹) ∣ 1 := by
      have := Nat.dvd_gcd h8 h7
      simpa using this
    exact Nat.dvd_one.mp hd
  have hinv2 : x⁻¹ * x⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  have hx2 : x * x = 1 := by
    have hcon := congrArg Inv.inv hinv2
    simpa [mul_inv_rev] using hcon
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have : 7 ∣ 2 := by simp [hx7] at hdvd
  norm_num at this

private theorem inverts_of_normalizes_card_seven {G : Type} [Group G] [Finite G] {X' : Subgroup G}
    (hX' : Nat.card X' = 7) {y : G} (hy2 : orderOf y = 2)
    (hyN : ∀ x ∈ X', y * x * y⁻¹ ∈ X')
    (hnc : ¬ ∀ x ∈ X', y * x = x * y) :
    ∀ x ∈ X', y * x * y⁻¹ = x⁻¹ := by
  have hy2' : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2] at h
    simpa [pow_two] using h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2'
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    simp
  have hxord : orderOf x = 7 := orderOf_eq_seven_of_mem hX' hx hx1
  have hz2mem : (y * x) ^ 2 ∈ X' := by
    rw [pow_two]
    have h1 : (y * x) * (y * x) = (y * x * y⁻¹) * x := by
      rw [hyinv]
      group
    rw [h1]
    exact X'.mul_mem (hyN x hx) hx
  have hcases : orderOf (y * x) = 1 ∨ orderOf (y * x) = 2 ∨
      orderOf (y * x) = 7 ∨ orderOf (y * x) = 14 := by
    have hpow : orderOf ((y * x) ^ 2) = orderOf (y * x) / Nat.gcd (orderOf (y * x)) 2 :=
      orderOf_pow' (x := y * x) (n := 2) (by norm_num)
    have hdvd7 : orderOf ((y * x) ^ 2) ∣ 7 := by
      rw [← hX']
      exact Subgroup.orderOf_dvd_natCard X' hz2mem
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h1 | h1
    · have hz2 : (y * x) ^ 2 = 1 := orderOf_eq_one_iff.mp h1
      have hdvd2 : orderOf (y * x) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [h1] at hpow
      have hg : Nat.gcd (orderOf (y * x)) 2 = 1 ∨ Nat.gcd (orderOf (y * x)) 2 = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right (orderOf (y * x)) 2) with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hmul : orderOf (y * x) = 7 * Nat.gcd (orderOf (y * x)) 2 := by
        calc orderOf (y * x) = orderOf (y * x) / Nat.gcd (orderOf (y * x)) 2 *
              Nat.gcd (orderOf (y * x)) 2 := (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
          _ = 7 * Nat.gcd (orderOf (y * x)) 2 := by rw [← hpow]
      rcases hg with h | h
      · exact Or.inr (Or.inr (Or.inl (by rw [hmul, h])))
      · exact Or.inr (Or.inr (Or.inr (by rw [hmul, h])))
  rcases hcases with h1 | h2 | h7 | h14
  · exfalso
    have hz1 : y * x = 1 := orderOf_eq_one_iff.mp h1
    have hyX : y ∈ X' := by
      have hxy : y = x⁻¹ := by
        have hc := congrArg (fun t => t * x⁻¹) hz1
        simpa [mul_assoc] using hc
      rw [hxy]
      exact X'.inv_mem hx
    have hdvd : orderOf y ∣ Nat.card X' := Subgroup.orderOf_dvd_natCard X' hyX
    rw [hy2, hX'] at hdvd
    norm_num at hdvd
  · have hz2 : (y * x) * (y * x) = 1 := by
      have h := pow_orderOf_eq_one (y * x)
      rw [h2] at h
      simpa [pow_two] using h
    have h3 : y * x * y = x⁻¹ := by
      have hc := congrArg (fun t => t * x⁻¹) hz2
      simpa [mul_assoc] using hc
    rwa [hyinv]
  · exfalso
    have hz7one : (y * x) ^ 7 = 1 := by
      rw [← h7]
      exact pow_orderOf_eq_one (y * x)
    have hzX : y * x ∈ X' := by
      have hz8 : y * x = ((y * x) ^ 2) ^ 4 := by
        rw [← pow_mul, show (2 * 4 : ℕ) = 7 + 1 from rfl, pow_succ, hz7one, one_mul]
      rw [hz8]
      exact Subgroup.pow_mem _ hz2mem 4
    have hyX : y ∈ X' := by
      have hy : y = (y * x) * x⁻¹ := by group
      rw [hy]
      exact Subgroup.mul_mem _ hzX (X'.inv_mem hx)
    have hdvd : orderOf y ∣ Nat.card X' := Subgroup.orderOf_dvd_natCard X' hyX
    rw [hy2, hX'] at hdvd
    norm_num at hdvd
  · exfalso
    have hz2ord : orderOf ((y * x) ^ 2) = 7 := by
      rw [orderOf_pow' (x := y * x) (n := 2) (by norm_num), h14]
      norm_num
    have hz2card : Nat.card ↥(Subgroup.zpowers ((y * x) ^ 2)) = 7 := by
      rw [Nat.card_zpowers, hz2ord]
    have hz2eq : Subgroup.zpowers ((y * x) ^ 2) = X' := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz2mem) ?_
      rw [hz2card, hX']
    have hxmem : x ∈ Subgroup.zpowers (y * x) := by
      have hx2 : x ∈ Subgroup.zpowers ((y * x) ^ 2) := by rw [hz2eq]; exact hx
      exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers (y * x) 2) hx2
    have hymem : y ∈ Subgroup.zpowers (y * x) := by
      have h : (y * x) * x⁻¹ ∈ Subgroup.zpowers (y * x) :=
        Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.inv_mem _ hxmem)
      simpa using h
    have hcomm : y * x = x * y := by
      have : IsCyclic ↥(Subgroup.zpowers (y * x)) := Subgroup.isCyclic_zpowers (y * x)
      exact congrArg Subtype.val (mul_comm' ⟨y, hymem⟩ ⟨x, hxmem⟩)
    have hxgen : Subgroup.zpowers x = X' := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_
      rw [Nat.card_zpowers, hxord, hX']
    apply hnc
    intro x' hx'
    have hx'x : x' ∈ Subgroup.zpowers x := by rw [hxgen]; exact hx'
    have hmem : x ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm
    have hz := Subgroup.zpowers_le.mpr hmem hx'x
    rw [Subgroup.mem_centralizer_iff] at hz
    exact hz y (by simp)

private theorem exists_conj_eq_of_card_seven {N : Subgroup Y} (hN : Nat.card N = 168)
    {P Q : Subgroup Y} (hPN : P ≤ N) (hQN : Q ≤ N) (hP : Nat.card P = 7)
    (hQ : Nat.card Q = 7) :
    ∃ g ∈ N, Q = P.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let P₀ : Subgroup ↥N := P.subgroupOf N
  let Q₀ : Subgroup ↥N := Q.subgroupOf N
  have hP₀card : Nat.card ↥P₀ = 7 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv).trans hP
  have hQ₀card : Nat.card ↥Q₀ = 7 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv).trans hQ
  have hP₀idx : ¬ 7 ∣ P₀.index := by
    have h := Subgroup.card_mul_index P₀
    rw [hP₀card, hN] at h
    have hidx : P₀.index = 24 := by omega
    rw [hidx]
    norm_num
  have hQ₀idx : ¬ 7 ∣ Q₀.index := by
    have h := Subgroup.card_mul_index Q₀
    rw [hQ₀card, hN] at h
    have hidx : Q₀.index = 24 := by omega
    rw [hidx]
    norm_num
  let P' : Sylow 7 ↥N := (IsPGroup.of_card (G := ↥P₀) (n := 1) (by
    rw [hP₀card]; norm_num)).toSylow hP₀idx
  let Q' : Sylow 7 ↥N := (IsPGroup.of_card (G := ↥Q₀) (n := 1) (by
    rw [hQ₀card]; norm_num)).toSylow hQ₀idx
  have hP'coe : (P' : Subgroup ↥N) = P₀ := rfl
  have hQ'coe : (Q' : Subgroup ↥N) = Q₀ := rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N P' Q'
  have hsub : ((g • P' : Sylow 7 ↥N) : Subgroup ↥N) =
      P₀.map (MulAut.conj (g : ↥N)).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, hP'coe]
    rfl
  have hleft : (P₀.map (MulAut.conj (g : ↥N)).toMonoidHom).map N.subtype =
      P.map (MulAut.conj ((g : ↥N) : Y)).toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : N.subtype.comp (MulAut.conj (g : ↥N)).toMonoidHom =
        (MulAut.conj ((g : ↥N) : Y)).toMonoidHom.comp N.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hPN]
  refine ⟨((g : ↥N) : Y), g.2, ?_⟩
  have hQeq : (((g • P' : Sylow 7 ↥N) : Subgroup ↥N)) = Q₀ := by
    rw [hg, hQ'coe]
  calc Q = Q₀.map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hQN).symm
    _ = (((g • P' : Sylow 7 ↥N) : Subgroup ↥N)).map N.subtype := by rw [hQeq]
    _ = P.map (MulAut.conj ((g : ↥N) : Y)).toMonoidHom := by rw [hsub]; exact hleft

omit [Finite Y] in
private theorem conj_mem_centralizer {X : Subgroup Y} (g : Y) {z : Y}
    (hz : z ∈ centralizer (X : Set Y)) :
    MulAut.conj g z ∈ centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro h hh
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
  have := hz x hx
  show MulAut.conj g x * (MulAut.conj g) z = (MulAut.conj g) z * MulAut.conj g x
  rw [← map_mul, ← map_mul, this]

omit [Finite Y] in
private theorem conj_symm_mem_centralizer {X : Subgroup Y} (g : Y) {z : Y}
    (hz : z ∈ centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y)) :
    (MulAut.conj g).symm z ∈ centralizer (X : Set Y) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro x hx
  have hmem : MulAut.conj g x ∈ ((X.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have h := hz (MulAut.conj g x) hmem
  show x * (MulAut.conj g).symm z = (MulAut.conj g).symm z * x
  have h2 := congrArg (MulAut.conj g).symm h
  simpa [MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc] using h2

omit [Finite Y] in
private theorem card_centralizer_map_conj {X : Subgroup Y} (g : Y) :
    Nat.card (centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y)) =
      Nat.card (centralizer (X : Set Y)) := by
  have e : ↥(centralizer (X : Set Y)) ≃
      ↥(centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y)) :=
    { toFun := fun z => ⟨MulAut.conj g z.1, conj_mem_centralizer g z.2⟩
      invFun := fun z => ⟨(MulAut.conj g).symm z.1, conj_symm_mem_centralizer g z.2⟩
      left_inv := fun z => Subtype.ext (MulEquiv.symm_apply_apply (MulAut.conj g) (z : Y))
      right_inv := fun z => Subtype.ext (MulEquiv.apply_symm_apply (MulAut.conj g) (z : Y)) }
  exact (Nat.card_congr e).symm


private def Inv {G : Type*} [Group G] (X' : Subgroup G) : Set G :=
  {y : G | orderOf y = 2 ∧ ∀ x ∈ X', y * x * y⁻¹ = x⁻¹}

private theorem card_centralizer_of_mem (h : TICountHyp S) {X : Subgroup Y}
    (hX7 : Nat.card X = 7) (hXN : X ≤ normalizer ((S : Subgroup Y) : Set Y))
    {X' : Subgroup Y} (hX' : Nat.card X' = 7)
    (hX'N : X' ≤ normalizer ((S : Subgroup Y) : Set Y)) :
    Nat.card (centralizer (X' : Set Y)) = Nat.card (centralizer (X : Set Y)) := by
  obtain ⟨g, -, hg⟩ := exists_conj_eq_of_card_seven h.card_normalizer hXN hX'N hX7 hX'
  rw [hg]
  exact card_centralizer_map_conj (X := X) g

private theorem conj_u_orderOf {G : Type} [Group G] {g u : G} (hu2 : orderOf u = 2) :
    orderOf (g * u * g⁻¹) = 2 := by
  have hsem : SemiconjBy g u (g * u * g⁻¹) := by
    show g * u = (g * u * g⁻¹) * g
    group
  rw [← SemiconjBy.orderOf_eq g hsem]
  exact hu2

omit [Finite Y] in
private theorem conj_u_inverts_centralizer {X X' : Subgroup Y} {g u : Y}
    (huC : ∀ c ∈ centralizer (X : Set Y), u * c * u⁻¹ = c⁻¹)
    (hg : X' = X.map (MulAut.conj g).toMonoidHom) :
    ∀ z ∈ centralizer (X' : Set Y), (g * u * g⁻¹) * z * (g * u * g⁻¹)⁻¹ = z⁻¹ := by
  intro z hz
  rw [hg] at hz
  set z₀ : Y := (MulAut.conj g).symm z with hz₀def
  have hz₀eq : (MulAut.conj g) z₀ = z := by
    rw [hz₀def]
    exact MulEquiv.apply_symm_apply (MulAut.conj g) z
  have hz₀mem : z₀ ∈ centralizer (X : Set Y) := conj_symm_mem_centralizer g hz
  have h := huC z₀ hz₀mem
  have hz' : z = g * z₀ * g⁻¹ := by rw [← hz₀eq, MulAut.conj_apply]
  have hz'' : z⁻¹ = g * z₀⁻¹ * g⁻¹ := by rw [hz']; group
  calc g * u * g⁻¹ * z * (g * u * g⁻¹)⁻¹
      = g * (u * z₀ * u⁻¹) * g⁻¹ := by rw [hz']; group
    _ = g * z₀⁻¹ * g⁻¹ := by rw [h]
    _ = z⁻¹ := hz''.symm

private theorem mem_inv_mul_of_mem_centralizer {X' : Subgroup Y} {u' : Y}
    (hu'2 : orderOf u' = 2)
    (hu'C : ∀ z ∈ centralizer (X' : Set Y), u' * z * u'⁻¹ = z⁻¹)
    (hX' : Nat.card X' = 7) {z : Y} (hz : z ∈ centralizer (X' : Set Y)) :
    z * u' ∈ Inv X' := by
  have hu'X : ∀ x ∈ X', u' * x * u'⁻¹ = x⁻¹ := fun x hx =>
    hu'C x (le_centralizer_self_of_card_seven hX' hx)
  have hu'2' : u' * u' = 1 := by
    have h := pow_orderOf_eq_one u'
    rw [hu'2] at h
    simpa [pow_two] using h
  refine ⟨?_, ?_⟩
  · have hzu : u' * z * u'⁻¹ = z⁻¹ := hu'C z hz
    have hsq : (z * u') ^ 2 = 1 := by
      rw [pow_two]
      calc (z * u') * (z * u') = z * (u' * z * u'⁻¹) * (u' * u') := by group
        _ = z * z⁻¹ * (u' * u') := by rw [hzu]
        _ = 1 := by rw [hu'2']; group
    refine orderOf_eq_prime hsq ?_
    intro h1
    have hu'C' : u' ∈ centralizer (X' : Set Y) := by
      have h2 : u' = z⁻¹ := by
        have hc := congrArg (fun t => z⁻¹ * t) h1
        simpa [mul_assoc] using hc
      rw [h2]
      exact Subgroup.inv_mem _ hz
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_seven hX'
    have hcomm : x * u' = u' * x := (Subgroup.mem_centralizer_iff.mp hu'C') x hx
    have h1' : u' * x * u'⁻¹ = x := by rw [hcomm.symm]; group
    have hxx : x = x⁻¹ := h1'.symm.trans (hu'X x hx)
    have hx2 : x * x = 1 := by
      nth_rewrite 2 [hxx]
      exact mul_inv_cancel x
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
    have hx7 := orderOf_eq_seven_of_mem hX' hx hx1
    have hcon : 7 ∣ 2 := by
      simp [hx7] at hdvd
    norm_num at hcon
  · intro x hx
    have hcomm : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hz) x hx
    have h1 : u' * x * u'⁻¹ = x⁻¹ := hu'X x hx
    have hz' : z * x = x * z := hcomm.symm
    calc z * u' * x * (z * u')⁻¹
        = z * (u' * x * u'⁻¹) * z⁻¹ := by group
      _ = z * x⁻¹ * z⁻¹ := by rw [h1]
      _ = x⁻¹ := by
          have h3 : x = z * x * z⁻¹ := by
            have hc := congrArg (fun t => t * z⁻¹) hz'
            simpa [mul_assoc] using hc.symm
          have h4 : x⁻¹ = z * x⁻¹ * z⁻¹ := by
            have hc := congrArg Inv.inv h3
            simpa [mul_assoc] using hc
          exact h4.symm

omit [Finite Y] in
private theorem mem_centralizer_mul_inv_of_mem_inv {X' : Subgroup Y} {u' : Y}
    (hu'X : ∀ x ∈ X', u' * x * u'⁻¹ = x⁻¹) {y : Y} (hy : y ∈ Inv X') :
    y * u'⁻¹ ∈ centralizer (X' : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hyinv : y * x * y⁻¹ = x⁻¹ := hy.2 x hx
  have huinv : u'⁻¹ * x * u' = x⁻¹ := by
    have h1 : x = u'⁻¹ * x⁻¹ * u' := by
      have hcong := congrArg (fun t => u'⁻¹ * t * u') (hu'X x hx)
      simpa [mul_assoc] using hcong
    have h2 : x⁻¹ = u'⁻¹ * x * u' := by
      have hcong := congrArg Inv.inv h1
      simpa [mul_assoc] using hcong
    exact h2.symm
  have hconj : (y * u'⁻¹) * x * (y * u'⁻¹)⁻¹ = x := by
    calc (y * u'⁻¹) * x * (y * u'⁻¹)⁻¹
        = y * (u'⁻¹ * x * u') * y⁻¹ := by group
      _ = y * x⁻¹ * y⁻¹ := by rw [huinv]
      _ = (y * x * y⁻¹)⁻¹ := by group
      _ = x := by rw [hyinv]; group
  have h2 : (y * u'⁻¹) * x = x * (y * u'⁻¹) := by
    calc (y * u'⁻¹) * x = ((y * u'⁻¹) * x * (y * u'⁻¹)⁻¹) * (y * u'⁻¹) := by group
      _ = x * (y * u'⁻¹) := by rw [hconj]
  exact h2.symm

private theorem eq_of_card_seven_of_card_subgroup {D : Subgroup Y}
    (hD : Nat.card D = 7 ∨ Nat.card D = 21) {P Q : Subgroup Y} (hPD : P ≤ D) (hQD : Q ≤ D)
    (hP : Nat.card P = 7) (hQ : Nat.card Q = 7) : P = Q := by
  rcases hD with hD | hD
  · have hP' : P = D := Subgroup.eq_of_le_of_card_ge hPD (by rw [hD, hP])
    have hQ' : Q = D := Subgroup.eq_of_le_of_card_ge hQD (by rw [hD, hQ])
    rw [hP', hQ']
  · by_cases hinf : P ⊓ Q = ⊥
    · exfalso
      have hmem : ∀ pq : ↥P × ↥Q, (pq.1 : Y) * (pq.2 : Y) ∈ D := fun pq =>
        D.mul_mem (hPD pq.1.2) (hQD pq.2.2)
      have hinj : Function.Injective
          (fun pq : ↥P × ↥Q => (⟨(pq.1 : Y) * (pq.2 : Y), hmem pq⟩ : ↥D)) := by
        rintro ⟨p1, q1⟩ ⟨p2, q2⟩ hab
        have hab' : (p1 : Y) * (q1 : Y) = (p2 : Y) * (q2 : Y) := congrArg Subtype.val hab
        have hmem1 : (p2 : Y)⁻¹ * (p1 : Y) ∈ P := P.mul_mem (P.inv_mem p2.2) p1.2
        have hmem2 : (p2 : Y)⁻¹ * (p1 : Y) ∈ Q := by
          have h : (p2 : Y)⁻¹ * (p1 : Y) = (q2 : Y) * (q1 : Y)⁻¹ := by
            have hc := congrArg (fun t => (p2 : Y)⁻¹ * t) hab'
            have hc2 := congrArg (fun t => t * (q1 : Y)⁻¹) hc
            simpa [mul_assoc] using hc2
          rw [h]
          exact Q.mul_mem q2.2 (Q.inv_mem q1.2)
        have hbot : (p2 : Y)⁻¹ * (p1 : Y) ∈ (⊥ : Subgroup Y) := by
          rw [← hinf]
          exact Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
        have hone : (p2 : Y)⁻¹ * (p1 : Y) = 1 := by simpa using hbot
        have hp : p1 = p2 := by
          apply Subtype.ext
          have hc := congrArg (fun t => (p2 : Y) * t) hone
          simpa [mul_assoc] using hc
        have hq : q1 = q2 := by
          apply Subtype.ext
          have hb : (p1 : Y) = (p2 : Y) := congrArg Subtype.val hp
          have hc := congrArg (fun t => (p2 : Y)⁻¹ * t) hab'
          simpa [hb, mul_assoc] using hc
        exact Prod.ext hp hq
      have hcard := Nat.card_le_card_of_injective
        (fun pq : ↥P × ↥Q => (⟨(pq.1 : Y) * (pq.2 : Y), hmem pq⟩ : ↥D)) hinj
      have h49 : Nat.card (↥P × ↥Q) = 7 * 7 := by rw [Nat.card_prod, hP, hQ]
      rw [h49, hD] at hcard
      norm_num at hcard
    · have hdvd : Nat.card ↥(P ⊓ Q) ∣ 7 := by
        have h := Subgroup.card_dvd_of_le (H := P ⊓ Q) (K := P) inf_le_left
        rwa [hP] at h
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hinf
      · have hle : P ≤ Q := by
          have hEq : P ⊓ Q = P :=
            Subgroup.eq_of_le_of_card_ge (H := P ⊓ Q) (K := P) inf_le_left (by rw [h1, hP])
          rw [← hEq]
          exact inf_le_right
        exact Subgroup.eq_of_le_of_card_ge hle (by rw [hP, hQ])

private theorem inv_subset_involutions (h : TICountHyp S) {X' : Subgroup Y}
    (hX' : Nat.card X' = 7) (hX'N : X' ≤ normalizer ((S : Subgroup Y) : Set Y)) :
    Inv X' ⊆ {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} := by
  intro y hy
  exact ⟨hy.1, fun hyN => not_inverts_of_mem_normalizer h hX' hX'N hyN hy.1 hy.2⟩

private theorem odd_card_inf_conj (h : TICountHyp S) {y : Y}
    (hyN : y ∉ normalizer ((S : Subgroup Y) : Set Y)) :
    Odd (Nat.card ↥(normalizer ((S : Subgroup Y) : Set Y) ⊓
      (normalizer ((S : Subgroup Y) : Set Y)).map (MulAut.conj y).toMonoidHom)) := by
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let D : Subgroup Y := N ⊓ N.map (MulAut.conj y).toMonoidHom
  show Odd (Nat.card D)
  have hDodd : Odd (Nat.card D) := by
    have hnot : ¬ 2 ∣ Nat.card D := by
      intro h2dvd
      have : Fintype ↥D := Fintype.ofFinite _
      obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card (G := ↥D) 2 (by
        rw [← Nat.card_eq_fintype_card]; exact h2dvd)
      have hdY2 : orderOf (d : Y) = 2 := by rw [Subgroup.orderOf_coe, hd]
      have hdN : (d : Y) ∈ N := (Subgroup.mem_inf.mp d.2).1
      have hdS : (d : Y) ∈ (S : Subgroup Y) := h.mem_of_mem_normalizer hdY2 hdN
      obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.mp ((Subgroup.mem_inf.mp d.2).2 :
        (d : Y) ∈ N.map (MulAut.conj y).toMonoidHom)
      have hn' : y * n * y⁻¹ = (d : Y) := hn
      have hnd : y⁻¹ * (d : Y) * y = n := by
        rw [← hn']
        group
      have hn2 : orderOf n = 2 := by
        have hsem : SemiconjBy y⁻¹ (d : Y) (y⁻¹ * (d : Y) * y) := by
          show y⁻¹ * (d : Y) = (y⁻¹ * (d : Y) * y) * y⁻¹
          group
        have hinv : orderOf (y⁻¹ * (d : Y) * y) = orderOf (d : Y) := by
          rw [← SemiconjBy.orderOf_eq y⁻¹ hsem]
        rw [← hnd, hinv, hdY2]
      have hnS : n ∈ (S : Subgroup Y) := h.mem_of_mem_normalizer hn2 hnN
      have hdSyl : (d : Y) ∈ ((y • S : Sylow 2 Y) : Subgroup Y) := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        exact Subgroup.mem_map.mpr ⟨n, hnS, hn⟩
      have heq : S = y • S := h.sylow_eq_of_mem hdY2 hdS hdSyl
      exact hyN (Sylow.smul_eq_iff_mem_normalizer.mp heq.symm)
    rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact hDodd

private theorem seven_le_card_inf_conj (h : TICountHyp S) {y : Y} (hy2 : orderOf y = 2)
    (hyN : y ∉ normalizer ((S : Subgroup Y) : Set Y)) :
    7 ≤ Nat.card ↥(normalizer ((S : Subgroup Y) : Set Y) ⊓
      (normalizer ((S : Subgroup Y) : Set Y)).map (MulAut.conj y).toMonoidHom) := by
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let D : Subgroup Y := N ⊓ N.map (MulAut.conj y).toMonoidHom
  show 7 ≤ Nat.card D
  have hy2' : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2] at h
    simpa [pow_two] using h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2'
  have hDmem : ∀ z : Y, z ∈ D ↔ z ∈ N ∧ ∃ n ∈ N, MulAut.conj y n = z := by
    intro z
    show z ∈ N ⊓ N.map (MulAut.conj y).toMonoidHom ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    rfl
  have hDge7 : 7 ≤ Nat.card D := by
    have hW := h.seven_le_card_inv_coset hy2 hyN
    have hw2 : ∀ w : Y, w ∈ {w : Y | orderOf w = 2 ∧ w * y⁻¹ ∈ N} → w⁻¹ = w := by
      intro w hw
      have h := pow_orderOf_eq_one w
      rw [hw.1] at h
      exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using h)
    have himg : (fun w : Y => w * y) '' {w : Y | orderOf w = 2 ∧ w * y⁻¹ ∈ N} ⊆ (D : Set Y) := by
      rintro _ ⟨w, hw, rfl⟩
      change w * y ∈ (D : Set Y)
      refine (hDmem (w * y)).mpr ⟨?_, y * w, ?_, ?_⟩
      · simpa [hyinv] using hw.2
      · have hmem : (w * y)⁻¹ ∈ N := N.inv_mem (by simpa [hyinv] using hw.2)
        simpa [mul_inv_rev, hyinv, hw2 w hw] using hmem
      · show y * (y * w) * y⁻¹ = w * y
        rw [hyinv]
        calc y * (y * w) * y = (y * y) * w * y := by group
          _ = w * y := by rw [hy2']; group
    calc 7 ≤ (Set.ncard {w : Y | orderOf w = 2 ∧ w * y⁻¹ ∈ N}) := hW
      _ = (Set.ncard ((fun w : Y => w * y) '' {w : Y | orderOf w = 2 ∧ w * y⁻¹ ∈ N})) := by
            rw [Set.ncard_image_of_injective _ (fun a b h => mul_right_cancel h)]
      _ ≤ Set.ncard (D : Set Y) := Set.ncard_le_ncard himg
      _ = Nat.card D := (Nat.card_coe_set_eq (D : Set Y)).symm
  exact hDge7

private theorem exists_unique_inv_of_mem (h : TICountHyp S) {X : Subgroup Y}
    (hX7 : Nat.card X = 7) (hXN : X ≤ normalizer ((S : Subgroup Y) : Set Y))
    (hCXo : Odd (Nat.card (centralizer (X : Set Y))))
    {y : Y} (hy2 : orderOf y = 2) (hyN : y ∉ normalizer ((S : Subgroup Y) : Set Y)) :
    ∃ Xy : Subgroup Y, Nat.card Xy = 7 ∧
      Xy ≤ normalizer ((S : Subgroup Y) : Set Y) ∧
      (∀ x ∈ Xy, y * x * y⁻¹ = x⁻¹) ∧
      ∀ X' : Subgroup Y, Nat.card X' = 7 →
        X' ≤ normalizer ((S : Subgroup Y) : Set Y) →
        (∀ x ∈ X', y * x * y⁻¹ = x⁻¹) → X' = Xy := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let N : Subgroup Y := normalizer ((S : Subgroup Y) : Set Y)
  let D : Subgroup Y := N ⊓ N.map (MulAut.conj y).toMonoidHom
  have hy2' : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2] at h
    simpa [pow_two] using h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2'
  have hDmem : ∀ z : Y, z ∈ D ↔ z ∈ N ∧ ∃ n ∈ N, MulAut.conj y n = z := by
    intro z
    show z ∈ N ⊓ N.map (MulAut.conj y).toMonoidHom ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    rfl
  have hDodd : Odd (Nat.card D) := odd_card_inf_conj h hyN
  have hDge7 : 7 ≤ Nat.card D := seven_le_card_inf_conj h hy2 hyN
  have hDdvd : Nat.card D ∣ 168 := by
    have hdvdN := Subgroup.card_dvd_of_le (inf_le_left : D ≤ N)
    rwa [show Nat.card N = 168 from h.card_normalizer] at hdvdN
  have hDcases : Nat.card D = 7 ∨ Nat.card D = 21 := by
    have hDdvd21 : Nat.card D ∣ 21 := by
      have hcop : (Nat.card D).Coprime 8 := by
        have h2 : (Nat.card D).Coprime 2 := Nat.coprime_two_right.mpr hDodd
        have := h2.pow_right 3
        simpa using this
      have h168 : (168 : ℕ) = 21 * 8 := by norm_num
      rw [h168] at hDdvd
      exact hcop.dvd_of_dvd_mul_right hDdvd
    have hle21 : Nat.card D ≤ 21 := Nat.le_of_dvd (by norm_num) hDdvd21
    have hdiv : Nat.divisors 21 = {1, 3, 7, 21} := by decide
    have hmem : Nat.card D ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨hDdvd21, by norm_num⟩
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hDy : D.map (MulAut.conj y).toMonoidHom = D := by
    have hff : (N.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom = N := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y).toMonoidHom =
          MonoidHom.id Y := by
        ext x
        show y * (y * x * y⁻¹) * y⁻¹ = x
        have hyinv2 : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hy2', inv_one]
        calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y⁻¹ * y⁻¹) := by group
          _ = x := by rw [hy2', hyinv2]; group
      rw [hcomp, Subgroup.map_id]
    show (N ⊓ N.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom = D
    rw [Subgroup.map_inf N (N.map (MulAut.conj y).toMonoidHom) (MulAut.conj y).toMonoidHom
        (MulAut.conj y).injective, hff, inf_comm]
  have h7dvd : 7 ∣ Nat.card D := by
    rcases hDcases with hD | hD
    · rw [hD]
    · rw [hD]; norm_num
  have : Fintype ↥D := Fintype.ofFinite _
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card (G := ↥D) 7 (by
    rw [← Nat.card_eq_fintype_card]; exact h7dvd)
  let Xy : Subgroup Y := Subgroup.zpowers (g₀ : Y)
  have hXycard : Nat.card Xy = 7 := by
    show Nat.card (Subgroup.zpowers (g₀ : Y)) = 7
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg₀]
  have hXyD : Xy ≤ D := Subgroup.zpowers_le.mpr g₀.2
  have hXyN : Xy ≤ N := hXyD.trans inf_le_left
  have hXyconj : Xy.map (MulAut.conj y).toMonoidHom = Xy := by
    have hle : Xy.map (MulAut.conj y).toMonoidHom ≤ D := by
      rw [← hDy]
      exact Subgroup.map_mono hXyD
    have hcard : Nat.card (Xy.map (MulAut.conj y).toMonoidHom) = 7 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hXycard]
    exact eq_of_card_seven_of_card_subgroup hDcases hle hXyD hcard hXycard
  have hnotcent : ¬ ∀ x ∈ Xy, y * x = x * y := by
    intro hc
    have hyC : y ∈ centralizer (Xy : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hc x hx).symm
    have h2dvd : 2 ∣ Nat.card (centralizer (Xy : Set Y)) := by
      have h := Subgroup.orderOf_dvd_natCard (centralizer (Xy : Set Y)) hyC
      rwa [hy2] at h
    rw [card_centralizer_of_mem h hX7 hXN hXycard hXyN] at h2dvd
    obtain ⟨k, hk⟩ := hCXo
    obtain ⟨m, hm⟩ := h2dvd
    omega
  have hinverts : ∀ x ∈ Xy, y * x * y⁻¹ = x⁻¹ := by
    apply inverts_of_normalizes_card_seven hXycard hy2 ?_ hnotcent
    intro x hx
    have h2 : MulAut.conj y x ∈ Xy.map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [hXyconj] at h2
  refine ⟨Xy, hXycard, hXyN, hinverts, ?_⟩
  intro X' hX' hX'N hinv'
  have hX'D : X' ≤ D := by
    intro x hx
    rw [hDmem]
    refine ⟨hX'N hx, x⁻¹, hX'N (X'.inv_mem hx), ?_⟩
    show y * x⁻¹ * y⁻¹ = x
    rw [← hinv' x hx]
    have hyinv2 : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hy2', inv_one]
    calc y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y⁻¹ * y⁻¹) := by group
      _ = x := by rw [hy2', hyinv2]; group
  exact eq_of_card_seven_of_card_subgroup hDcases hX'D hXyD hX' hXycard


private theorem dvd_count (h : TICountHyp S) {X : Subgroup Y} (hX7 : Nat.card X = 7)
    (hXN : X ≤ normalizer ((S : Subgroup Y) : Set Y))
    (hCXo : Odd (Nat.card (centralizer (X : Set Y))))
    (hu : ∃ u : Y, orderOf u = 2 ∧ ∀ c ∈ centralizer (X : Set Y), u * c * u⁻¹ = c⁻¹) :
    Nat.card (centralizer (X : Set Y)) ∣
      Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} := by
  classical
  obtain ⟨u, hu2, huC⟩ := hu
  let I : Set Y := {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)}
  let S7 : Set (Subgroup Y) :=
    {X' : Subgroup Y | Nat.card X' = 7 ∧ X' ≤ normalizer ((S : Subgroup Y) : Set Y)}
  let C : Subgroup Y := centralizer (X : Set Y)
  have hex : ∀ y : ↥I, ∃ X' : ↥S7, (y : Y) ∈ Inv (X' : Subgroup Y) := by
    intro y
    obtain ⟨Xy, hXy7, hXyN, hinv, -⟩ := exists_unique_inv_of_mem h hX7 hXN hCXo y.2.1 y.2.2
    exact ⟨⟨Xy, hXy7, hXyN⟩, y.2.1, hinv⟩
  let F : ↥I → ↥S7 := fun y => Classical.choose (hex y)
  have hFspec : ∀ y : ↥I, (y : Y) ∈ Inv (F y : Subgroup Y) := fun y => Classical.choose_spec (hex y)
  have hFuniq : ∀ (y : ↥I) (X' : ↥S7), (y : Y) ∈ Inv (X' : Subgroup Y) → X' = F y := by
    intro y X' hX'
    obtain ⟨Xy, hXy7, hXyN, hinv, huniq⟩ := exists_unique_inv_of_mem h hX7 hXN hCXo y.2.1 y.2.2
    exact Subtype.ext ((huniq X' X'.2.1 X'.2.2 hX'.2).trans
      (huniq (F y) (F y).2.1 (F y).2.2 (hFspec y).2).symm)
  have hexg : ∀ X' : ↥S7, ∃ g ∈ normalizer ((S : Subgroup Y) : Set Y),
      (X' : Subgroup Y) = X.map (MulAut.conj g).toMonoidHom := by
    intro X'
    exact exists_conj_eq_of_card_seven h.card_normalizer hXN X'.2.2 hX7 X'.2.1
  let Gc : ↥S7 → Y := fun X' => Classical.choose (hexg X')
  have hGspec : ∀ X' : ↥S7, Gc X' ∈ normalizer ((S : Subgroup Y) : Set Y) ∧
      (X' : Subgroup Y) = X.map (MulAut.conj (Gc X')).toMonoidHom :=
    fun X' => Classical.choose_spec (hexg X')
  let U : ↥S7 → Y := fun X' => Gc X' * u * (Gc X')⁻¹
  have hUord : ∀ X' : ↥S7, orderOf (U X') = 2 := fun X' => conj_u_orderOf hu2
  have hUinv : ∀ X' : ↥S7, ∀ z ∈ centralizer ((X' : Subgroup Y) : Set Y),
      U X' * z * (U X')⁻¹ = z⁻¹ :=
    fun X' => conj_u_inverts_centralizer huC (hGspec X').2
  have hinvMemInv : ∀ p : ↥S7 × ↥C,
      MulAut.conj (Gc p.1) (p.2 : Y) * U p.1 ∈ Inv (p.1 : Subgroup Y) := by
    intro p
    have hmem : MulAut.conj (Gc p.1) (p.2 : Y) ∈
        centralizer ((p.1 : Subgroup Y) : Set Y) := by
      rw [(hGspec p.1).2]
      exact conj_mem_centralizer (Gc p.1) p.2.2
    exact mem_inv_mul_of_mem_centralizer (hUord p.1) (hUinv p.1) p.1.2.1 hmem
  have hinvMem : ∀ p : ↥S7 × ↥C, MulAut.conj (Gc p.1) (p.2 : Y) * U p.1 ∈ I :=
    fun p => inv_subset_involutions h p.1.2.1 p.1.2.2 (hinvMemInv p)
  have htoMem : ∀ y : ↥I,
      (MulAut.conj (Gc (F y))).symm ((y : Y) * (U (F y))⁻¹) ∈ centralizer (X : Set Y) := by
    intro y
    have hX'C : (F y : Subgroup Y) ≤ centralizer ((F y : Subgroup Y) : Set Y) :=
      le_centralizer_self_of_card_seven (F y).2.1
    have hUX : ∀ x ∈ (F y : Subgroup Y), U (F y) * x * (U (F y))⁻¹ = x⁻¹ := fun x hx =>
      hUinv (F y) x (hX'C hx)
    have hmem : (y : Y) * (U (F y))⁻¹ ∈ centralizer ((F y : Subgroup Y) : Set Y) :=
      mem_centralizer_mul_inv_of_mem_inv hUX (hFspec y)
    rw [(hGspec (F y)).2] at hmem
    exact conj_symm_mem_centralizer (Gc (F y)) hmem
  let toFun : ↥I → ↥S7 × ↥C := fun y => (F y, ⟨_, htoMem y⟩)
  let invFun : ↥S7 × ↥C → ↥I := fun p => ⟨_, hinvMem p⟩
  have hleft : ∀ y : ↥I, invFun (toFun y) = y := by
    intro y
    apply Subtype.ext
    show MulAut.conj (Gc (F y)) ((MulAut.conj (Gc (F y))).symm ((y : Y) * (U (F y))⁻¹)) *
      U (F y) = (y : Y)
    rw [MulEquiv.apply_symm_apply]
    group
  have hright : ∀ p : ↥S7 × ↥C, toFun (invFun p) = p := by
    intro p
    have hF : F (invFun p) = p.1 := (hFuniq (invFun p) p.1 (hinvMemInv p)).symm
    refine Prod.ext hF ?_
    apply Subtype.ext
    show (MulAut.conj (Gc (F (invFun p)))).symm
        ((MulAut.conj (Gc p.1) (p.2 : Y) * U p.1) * (U (F (invFun p)))⁻¹) = (p.2 : Y)
    rw [hF]
    have h1 : (MulAut.conj (Gc p.1) (p.2 : Y) * U p.1) * (U p.1)⁻¹ =
        MulAut.conj (Gc p.1) (p.2 : Y) := by group
    rw [h1, MulEquiv.symm_apply_apply]
  let e : ↥I ≃ ↥S7 × ↥C := ⟨toFun, invFun, hleft, hright⟩
  have hcard : Nat.card ↥I = Nat.card ↥S7 * Nat.card (centralizer (X : Set Y)) := by
    rw [Nat.card_congr e, Nat.card_prod]
  have hdvd : Nat.card (centralizer (X : Set Y)) ∣ Nat.card ↥I := by
    rw [hcard]
    exact dvd_mul_left _ _
  rwa [Nat.card_coe_set_eq] at hdvd

theorem exists_conj_inverts_of_ti (h : TICountHyp S) {X : Subgroup Y} (hX7 : Nat.card X = 7)
    (hXN : X ≤ normalizer ((S : Subgroup Y) : Set Y))
    (hCXo : Odd (Nat.card (centralizer (X : Set Y)))) {y : Y} (hy2 : orderOf y = 2)
    (hyN : y ∉ normalizer ((S : Subgroup Y) : Set Y)) :
    ∃ g ∈ normalizer ((S : Subgroup Y) : Set Y),
      ∀ x ∈ X, (g⁻¹ * y * g) * x * (g⁻¹ * y * g)⁻¹ = x⁻¹ := by
  obtain ⟨Xy, hXy7, hXyN, hinv, -⟩ := exists_unique_inv_of_mem h hX7 hXN hCXo hy2 hyN
  obtain ⟨g, hgN, hg⟩ := exists_conj_eq_of_card_seven h.card_normalizer hXN hXyN hX7 hXy7
  refine ⟨g, hgN, fun x hx => ?_⟩
  have hgx : g * x * g⁻¹ ∈ Xy := by
    rw [hg]
    exact ⟨x, hx, rfl⟩
  have h1 := hinv _ hgx
  calc (g⁻¹ * y * g) * x * (g⁻¹ * y * g)⁻¹ = g⁻¹ * (y * (g * x * g⁻¹) * y⁻¹) * g := by group
    _ = g⁻¹ * (g * x * g⁻¹)⁻¹ * g := by rw [h1]
    _ = x⁻¹ := by group

end

theorem card_centralizer_dvd_of_ti {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y}
    (h : TICountHyp S) {X : Subgroup Y} (hX7 : Nat.card X = 7)
    (hXN : X ≤ normalizer ((S : Subgroup Y) : Set Y))
    (hCXo : Odd (Nat.card (centralizer (X : Set Y))))
    (hu : ∃ u : Y, orderOf u = 2 ∧ ∀ c ∈ centralizer (X : Set Y), u * c * u⁻¹ = c⁻¹) :
    Nat.card (centralizer (X : Set Y)) ∣ 168 := by
  have hci := dvd_count h hX7 hXN hCXo hu
  have hY : Nat.card Y =
      (Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} + 7) * 24 :=
    h.card_inv_outside.symm
  have hcY : Nat.card (centralizer (X : Set Y)) ∣ Nat.card Y :=
    Subgroup.card_subgroup_dvd_card (centralizer (X : Set Y))
  rw [hY] at hcY
  have harith : (Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} + 7) * 24
      = Set.ncard {y : Y | orderOf y = 2 ∧ y ∉ normalizer ((S : Subgroup Y) : Set Y)} * 24 + 168 := by
    ring
  rw [harith] at hcY
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hci 24)).mp hcY

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
