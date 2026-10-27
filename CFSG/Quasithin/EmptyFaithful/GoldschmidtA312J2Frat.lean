module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.Quasithin.A312J2

open CFSG.GroupTheory CFSG.OrderReductions.FrattiniAutomorphisms

theorem le_center_of_normal_card_two {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases h1 : n = 1
  · rw [h1]; simp
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
    have hgn : g * n * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance n hn g
    have h2 : (⟨n, hn⟩ : N) = y := huniq _ (fun h => h1 (congrArg Subtype.val h))
    have h3 : (⟨g * n * g⁻¹, hgn⟩ : N) = y := by
      apply huniq
      intro h
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      apply h1
      have h4 : n = g⁻¹ * 1 * g := by rw [← this]; group
      simpa using h4
    have h5 : g * n * g⁻¹ = n := congrArg Subtype.val (h3.trans h2.symm)
    calc g * n = (g * n * g⁻¹) * g := by group
      _ = n * g := by rw [h5]

theorem card_center_eq_two {Y : Type} [Group Y] [Finite Y] (Q : Subgroup Y) [Q.Normal]
    (hQ : Nat.card Q = 32) (hC : Nat.card (Subgroup.centralizer (Q : Set Y)) = 2) :
    Nat.card (Subgroup.center Q) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 5) (by rw [hQ]; norm_num)
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  have := hQ2.center_nontrivial
  let ι : Subgroup.center Q →* Subgroup.centralizer (Q : Set Y) :=
    { toFun := fun z => ⟨((z : Q) : Y), by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b h
    have h' := congrArg (fun z : Subgroup.centralizer (Q : Set Y) => (z : Y)) h
    exact Subtype.ext (Subtype.ext h')
  have hle : Nat.card (Subgroup.center Q) ≤ 2 := hC ▸ Nat.card_le_card_of_injective ι hι
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQ2.to_subgroup (Subgroup.center Q))
  have hgt : 1 < Nat.card (Subgroup.center Q) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  rw [hn] at hle hgt ⊢
  rcases n with _ | _ | n
  · simp at hgt
  · rfl
  · have : 2 ^ 2 ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem sixteen_le_card_quotient_frattini {Y : Type} [Group Y] [Finite Y] (Q : Subgroup Y)
    [Q.Normal] (hQ : Nat.card Q = 32) (hC : Nat.card (Subgroup.centralizer (Q : Set Y)) = 2)
    {x : Y} (hx : orderOf x = 5) : 16 ≤ Nat.card (Q ⧸ frattini Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 5) (by rw [hQ]; norm_num)
  obtain ⟨hchar, -, -, -, d, hd, -⟩ := frattini_elementary_quotient hQ2
  have hker := (frattini_automorphism_kernel hQ2).2
  by_contra hlt
  rw [not_le, hd] at hlt
  have hd3 : d ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (not_le.mp h)
    omega
  let σ : MulAut Q := MulAut.conjNormal x
  have hσ5 : σ ^ 5 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  let τ : MulAut (Q ⧸ frattini Q) := quotientAutomorphism (frattini Q) σ
  have hτ5 : τ ^ 5 = 1 := by rw [← map_pow, hσ5, map_one]
  let F : Subgroup (Q ⧸ frattini Q) :=
    { carrier := {w | τ w = w}
      mul_mem' := fun {a b} ha hb => by
        change τ a = a at ha
        change τ b = b at hb
        change τ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by
        change τ 1 = 1
        exact map_one τ
      inv_mem' := fun {a} ha => by
        change τ a = a at ha
        change τ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hcount : Nat.card (Q ⧸ frattini Q) ≡ Nat.card F [MOD 5] := by
    let _ : Fintype (Q ⧸ frattini Q) := Fintype.ofFinite _
    let π : Equiv.Perm (Q ⧸ frattini Q) := MulAut.toPerm _ τ
    have hπ5 : π ^ 5 ^ 1 = 1 := by
      rw [pow_one, show π = MulAut.toPerm _ τ from rfl, ← map_pow, hτ5, map_one]
    have h := Equiv.Perm.card_compl_support_modEq hπ5
    have e : ↥F ≃ ↥((Equiv.Perm.support π)ᶜ : Finset (Q ⧸ frattini Q)) :=
      Equiv.subtypeEquivRight fun w => by
        rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
        exact Iff.rfl
    have hcard : Nat.card F = ((Equiv.Perm.support π)ᶜ).card := by
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [Nat.card_eq_fintype_card (α := Q ⧸ frattini Q), hcard]
    exact h.symm
  have hFd : Nat.card F ∣ 2 ^ d := hd ▸ Subgroup.card_subgroup_dvd_card F
  obtain ⟨e, he, hFe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFd
  rw [hd, hFe] at hcount
  have hed : e = d := by
    interval_cases d <;> interval_cases e <;> first | rfl | (exfalso; revert hcount; decide)
  have hF : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hFe, hed, hd])
  have hτ1 : τ = 1 := by
    ext w
    have : w ∈ F := by rw [hF]; trivial
    exact this
  have hmem : σ ∈ (quotientAutomorphism (frattini Q)).ker := by
    rw [MonoidHom.mem_ker]
    exact hτ1
  obtain ⟨k, hk⟩ := hker ⟨σ, hmem⟩
  have hk' : σ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
    have h2 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  have hxC : x ∈ Subgroup.centralizer (Q : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := congrArg Subtype.val (DFunLike.congr_fun hσ1 ⟨q, hq⟩)
    have h' : x * q * x⁻¹ = q := h
    calc q * x = (x * q * x⁻¹) * x := by rw [h']
      _ = x * q := by group
  have := Subgroup.orderOf_dvd_natCard _ hxC
  rw [hC, hx] at this
  omega

theorem isExtraspecial_of_card_thirtyTwo {Y : Type} [Group Y] [Finite Y] (Q : Subgroup Y)
    [Q.Normal] (hQ : Nat.card Q = 32) (hC : Nat.card (Subgroup.centralizer (Q : Set Y)) = 2)
    {x : Y} (hx : orderOf x = 5) : CFSG.IsExtraspecial 2 Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 5) (by rw [hQ]; norm_num)
  have hZ := card_center_eq_two Q hQ hC
  have h16 := sixteen_le_card_quotient_frattini Q hQ hC hx
  obtain ⟨hchar, hcomm, hsq, -, d, hd, -⟩ := frattini_elementary_quotient hQ2
  have hΦ : frattini Q ≤ Subgroup.center Q := by
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Q)
    rw [hQ, hd] at hprod
    rw [hd] at h16
    have hpos : 0 < Nat.card (frattini Q) := Nat.card_pos
    have hle : Nat.card (frattini Q) ≤ 2 := by
      by_contra h
      have := Nat.mul_le_mul h16 (not_le.mp h)
      omega
    rcases Nat.lt_or_ge (Nat.card (frattini Q)) 2 with h1 | h2
    · have : Nat.card (frattini Q) = 1 := by omega
      rw [Subgroup.eq_bot_of_card_eq _ this]
      exact bot_le
    · exact le_center_of_normal_card_two (frattini Q) (by omega)
  have hcomm' : commutator Q ≤ Subgroup.center Q :=
    ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini Q)).mp hcomm).trans hΦ
  have hcomm'' : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := Subgroup.center Q)).mpr hcomm'
  refine
    { center_order_p := hZ
      quotient_elementary_abelian :=
        { toIsMulCommutative := hcomm''
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
            induction g using QuotientGroup.induction_on with | H g => ?_
            rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
            apply hΦ
            have hg2 : ((g ^ 2 : Q) : Q ⧸ frattini Q) = 1 := by
              rw [QuotientGroup.mk_pow]
              exact hsq _
            exact (QuotientGroup.eq_one_iff (g ^ 2)).mp hg2 }
      quotient_nontrivial := ?_ }
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)
  rw [hQ, hZ] at h
  exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

end CFSG.Quasithin.A312J2
