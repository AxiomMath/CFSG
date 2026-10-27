module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56R
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Quasithin.H13.MatNCert Matrix
open Sp6Over (GL6 M6 V7)

variable {G : Type} [Group G] [Finite G]

namespace S56

theorem eq_one_of_mem_op_two {s₀ x : G} (hx : x ∈ Op 2 (Cen s₀)) {n : ℕ} (hn : Nat.Coprime 2 n)
    (hxn : x ^ n = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := op_two_isPGroup s₀ ⟨x, hx⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Nat.Coprime (orderOf x) 2 :=
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxn) hn).symm
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd) (orderOf_dvd_of_pow_eq_one h1))

theorem exists_lift {H K : Type*} [Group H] [Group K] (ψ : H →* K) {n : ℕ}
    (hN : Nat.card ψ.ker = 2 ^ n) {f x : K} (hf : f ∈ ψ.range) (hx : x ∈ ψ.range)
    (hfo : orderOf f = 5) (hxo : orderOf x = 3) (hfx : f * x = x * f) :
    ∃ f₂ x₂ : H, orderOf f₂ = 5 ∧ x₂ ^ 3 = 1 ∧ x ∈ Subgroup.zpowers (ψ x₂) ∧ f₂ * x₂ = x₂ * f₂ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨d₀, hd₀⟩ := ψ.range.mul_mem hf hx
  have hf5 : f ^ 5 = 1 := by rw [← hfo]; exact pow_orderOf_eq_one f
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hc : Commute f x := hfx
  set N := 2 ^ n with hNdef
  set M := N * N with hM
  have hψ : ∀ m : ℕ, ψ (d₀ ^ m) = f ^ m * x ^ m := fun m => by rw [map_pow, hd₀, hc.mul_pow]
  have hker : d₀ ^ (15 * N) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, show 15 * N = 5 * (3 * N) by ring, pow_mul, hf5, one_pow, one_mul,
      show 5 * (3 * N) = 3 * (5 * N) by ring, pow_mul, hx3, one_pow]
  have h15 : (d₀ ^ M) ^ 15 = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, hker⟩ : ψ.ker)))
    rw [hN] at this
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
    rw [← pow_mul, show M * 15 = 15 * N * N by rw [hM]; ring, pow_mul]
    exact this
  have hcop : ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.Coprime q M := fun q hq hq2 => by
    rw [hM, hNdef]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right n ((Nat.coprime_primes hq Nat.prime_two).2 hq2))
      (Nat.Coprime.pow_right n ((Nat.coprime_primes hq Nat.prime_two).2 hq2))
  refine ⟨(d₀ ^ M) ^ 3, (d₀ ^ M) ^ 5, orderOf_eq_prime ?_ ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, h15]
  · intro h1
    have h2 : ψ ((d₀ ^ M) ^ 3) = f ^ (M * 3) := by
      rw [← pow_mul, hψ, pow_mul x M 3, ← pow_mul, mul_comm M 3, pow_mul x 3 M, hx3, one_pow,
        mul_one, mul_comm]
    rw [h1, map_one] at h2
    have hd : 5 ∣ M * 3 := hfo ▸ orderOf_dvd_of_pow_eq_one h2.symm
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.mul_right (hcop 5 (by norm_num) (by norm_num))
      (by norm_num : Nat.Coprime 5 3)) hd
    omega
  · rw [← pow_mul, show 5 * 3 = 15 by rfl, h15]
  · have h2 : ψ ((d₀ ^ M) ^ 5) = x ^ (M * 5) := by
      rw [← pow_mul, hψ, mul_comm M 5, pow_mul f 5 M, hf5, one_pow, one_mul]
    rw [h2]
    have hcop3 : Nat.Coprime (M * 5) 3 :=
      Nat.Coprime.mul_right (hcop 3 Nat.prime_three (by norm_num)) (by norm_num) |>.symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop3 (by norm_num)
    refine Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast, ← pow_mul, ← pow_mod_orderOf, hxo, hm, pow_one]
  · exact (Commute.pow_pow_self (d₀ ^ M) 3 5).eq

section Ker

variable {s₀ : G} (hs : orderOf s₀ = 2)
  (κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7)
  (hκ : κ ⟨s₀, s₀_mem_center hs⟩ = Multiplicative.ofAdd (Pi.single 0 1))

include hκ in
theorem sq_mem_of_rhoBar_eq_one
    (hcen : CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) = Op 2 (Cen s₀)) {g : G}
    (hg : g ∈ Cen s₀) (h1 : rhoBar hs κ hκ ⟨g, hg⟩ = 1) : g ^ 2 ∈ Op 2 (Cen s₀) := by
  rw [← hcen, Subgroup.mem_centralizer_iff]
  intro z hz
  have hgs : g * s₀ * g⁻¹ = s₀ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hs2 : s₀ * s₀ = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hsq : g ^ 2 * z * (g ^ 2)⁻¹ = g * (g * z * g⁻¹) * g⁻¹ := by rw [sq]; group
  have key : g ^ 2 * z * (g ^ 2)⁻¹ = z := by
    rcases conj_of_rhoBar_eq_one hs κ hκ hg h1 hz with h | h
    · rw [hsq, h, h]
    · rw [hsq, h, show g * (z * s₀) * g⁻¹ = (g * z * g⁻¹) * (g * s₀ * g⁻¹) by group, h, hgs,
        mul_assoc, hs2, mul_one]
  calc z * g ^ 2 = g ^ 2 * z * (g ^ 2)⁻¹ * g ^ 2 := by rw [key]
    _ = g ^ 2 * z := by group

include hκ in
theorem mem_S_of_rhoBar_eq_one
    (hcen : CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) = Op 2 (Cen s₀)) {g : G}
    (hg : g ∈ Cen s₀) (h1 : rhoBar hs κ hκ ⟨g, hg⟩ = 1) : g ∈ Op 2 (Cen s₀) := by
  have hp : IsPGroup 2 (rhoBar hs κ hκ).ker := fun x => by
    have hx2 := sq_mem_of_rhoBar_eq_one hs κ hκ hcen (x : Cen s₀).2 x.2
    obtain ⟨k, hk⟩ := op_two_isPGroup s₀ ⟨_, hx2⟩
    refine ⟨k + 1, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul]
    exact this
  have hle : (rhoBar hs κ hκ).ker ≤ CFSG.pCore 2 ↥(Cen s₀) := le_sSup ⟨inferInstance, hp⟩
  exact ⟨⟨g, hg⟩, hle h1, rfl⟩

end Ker

end S56

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section NoFive

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.u_mem_A₁ : b₂ * b₃ ∈ A₁sub b b₁ b₂ b₃ := h5.εA_u₃ ▸ h5.coordA.mem _

theorem FF81Sec5.orderOf_u : orderOf (b₂ * b₃) = 3 := by
  rw [← h5.εA_u₃]; exact h5.coordA.orderOf (by decide)

theorem FF81Sec5.A₁_le_D : A₁sub b b₁ b₂ b₃ ≤ Cen s₀ ⊓ Cen (b₂ * b₃) := fun a ha =>
  Subgroup.mem_inf.mpr ⟨h5.A₁_le_cen_s₀ ha,
    Subgroup.mem_centralizer_singleton_iff.mpr (h5.A₁_comm ha h5.u_mem_A₁)⟩

variable (hKC : KF_Sp6ShortRootCen)
include hKC

theorem FF81Sec5.no_five (c2 : FF81Conc5_2 b b₁ b₂ b₃ s₀)
    (hsyl : Nat.Coprime 3 ((A₁sub b b₁ b₂ b₃).relIndex (Cen s₀ ⊓ Cen (b₂ * b₃))))
    {f x : G} (hf : f ∈ Cen s₀ ⊓ Cen (b₂ * b₃)) (hx : x ∈ Cen s₀ ⊓ Cen (b₂ * b₃))
    (hfo : orderOf f = 5) (hx3 : x ^ 3 = 1) (hxu : x ∉ Subgroup.zpowers (b₂ * b₃))
    (hfx : f * x = x * f) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, hhyp⟩ := c2
  have hB := h5.basis
  have hC := hKC G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab s₀ h5.hs₀L h5.hs₀ h5.s₀_b₁ h5.s₀_u₃ h5.hs₀b
  have huD : b₂ * b₃ ∈ Cen s₀ ⊓ Cen (b₂ * b₃) := h5.A₁_le_D h5.u_mem_A₁
  have hu3 : (b₂ * b₃) ^ 3 = 1 := by rw [← h5.orderOf_u]; exact pow_orderOf_eq_one _
  have hxu' : x * (b₂ * b₃) = b₂ * b₃ * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have hQ : CFSG.Open.IsElemAbelian 3 (Subgroup.closure {b₂ * b₃, x}) :=
    CFSG.Open.IsElemAbelian.closure_of_commute
      (by
        rintro a (rfl | rfl) c (rfl | rfl)
        exacts [rfl, hxu'.symm, hxu', rfl])
      (by rintro a (rfl | rfl); exacts [hu3, hx3])
  have hQD : Subgroup.closure {b₂ * b₃, x} ≤ Cen s₀ ⊓ Cen (b₂ * b₃) :=
    (Subgroup.closure_le _).mpr (by rintro a (rfl | rfl); exacts [huD, hx])
  have hQp : IsPGroup 3 (Subgroup.closure {b₂ * b₃, x}) := fun y =>
    ⟨1, Subtype.ext (by simpa using hQ.2 y y.2)⟩
  have hA₁p : IsPGroup 3 (A₁sub b b₁ b₂ b₃) :=
    IsPGroup.of_card (n := 3) (by rw [h5.coordA.card]; norm_num)
  obtain ⟨k, hkD, hk⟩ :=
    L41.exists_conj_le_sylowOf_p ⟨h5.A₁_le_D, hA₁p, hsyl⟩ hQD hQp
  have hku : k * (b₂ * b₃) = b₂ * b₃ * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hkD).2
  set x₃ := k * x * k⁻¹ with hx₃
  set f₃ := k * f * k⁻¹ with hf₃
  have hx₃A : x₃ ∈ A₁sub b b₁ b₂ b₃ := hk x (Subgroup.subset_closure (by simp))
  have hx₃u : x₃ ∉ Subgroup.zpowers (b₂ * b₃) := fun h => hxu (by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have hc : k * (b₂ * b₃) ^ i = (b₂ * b₃) ^ i * k := ((Commute.zpow_right hku i)).eq
    calc (b₂ * b₃) ^ i = k⁻¹ * ((b₂ * b₃) ^ i * k) := by rw [← hc]; group
      _ = k⁻¹ * (k * x * k⁻¹ * k) := by rw [hi]
      _ = x := by group)
  have hx₃3 : x₃ ^ 3 = 1 := by rw [hx₃, conj_pow, hx3, mul_one, mul_inv_cancel]
  have hx₃o : orderOf x₃ = 3 :=
    orderOf_eq_prime hx₃3 fun h => hx₃u (h ▸ Subgroup.one_mem _)
  set W := Subgroup.zpowers (b₂ * b₃) ⊔ Subgroup.zpowers x₃ with hW
  have hWcl : W = Subgroup.closure {b₂ * b₃, x₃} := by
    rw [hW, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hux₃ : x₃ * (b₂ * b₃) = b₂ * b₃ * x₃ := h5.A₁_comm hx₃A h5.u_mem_A₁
  have hWe : CFSG.Open.IsElemAbelian 3 W := by
    rw [hWcl]
    exact CFSG.Open.IsElemAbelian.closure_of_commute
      (by
        rintro a (rfl | rfl) c (rfl | rfl)
        exacts [rfl, hux₃.symm, hux₃, rfl])
      (by rintro a (rfl | rfl); exacts [hu3, hx₃3])
  have hcW : Nat.card W = 9 := by
    have hcomm : ∀ a ∈ Subgroup.zpowers (b₂ * b₃), ∀ c ∈ Subgroup.zpowers x₃, a * c = c * a :=
      fun a ha c hc => hWe.comm (le_sup_left (a := Subgroup.zpowers (b₂ * b₃)) ha)
        (le_sup_right (b := Subgroup.zpowers x₃) hc)
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
    rw [Nat.card_zpowers, Nat.card_zpowers, h5.orderOf_u, hx₃o] at h
    have hi : Nat.card ↥(Subgroup.zpowers (b₂ * b₃) ⊓ Subgroup.zpowers x₃) = 1 := by
      have hd : Nat.card ↥(Subgroup.zpowers (b₂ * b₃) ⊓ Subgroup.zpowers x₃) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_right (a := Subgroup.zpowers (b₂ * b₃))
          (b := Subgroup.zpowers x₃))
        rwa [Nat.card_zpowers, hx₃o] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
      · exact h1
      · exfalso
        have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right (a := Subgroup.zpowers (b₂ * b₃))
          (b := Subgroup.zpowers x₃)) (by rw [h3, Nat.card_zpowers, hx₃o])
        have : x₃ ∈ Subgroup.zpowers (b₂ * b₃) ⊓ Subgroup.zpowers x₃ := by
          rw [heq]; exact Subgroup.mem_zpowers x₃
        exact hx₃u (Subgroup.mem_inf.mp this).1
    rw [hi] at h
    change Nat.card W * 1 = 3 * 3 at h
    omega
  have hWA : W ≤ A₁sub b b₁ b₂ b₃ :=
    sup_le (Subgroup.zpowers_le.mpr h5.u_mem_A₁) (Subgroup.zpowers_le.mpr hx₃A)
  have hWel : IsElemAb 3 2 W :=
    ⟨CFSG.IsElementaryAbelian.of_forall (fun a ha c hc => hWe.comm ha hc) hWe.2, hcW⟩
  obtain ⟨h, hhH, hhb⟩ := hhyp W hWA hWel
  have hhs : h ∈ Cen s₀ := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hhH).1 s₀
      (Subgroup.subset_closure (by simp))).symm
  have hf₃D : f₃ ∈ Cen s₀ ⊓ Cen (b₂ * b₃) :=
    (Cen s₀ ⊓ Cen (b₂ * b₃)).mul_mem ((Cen s₀ ⊓ Cen (b₂ * b₃)).mul_mem hkD hf)
      ((Cen s₀ ⊓ Cen (b₂ * b₃)).inv_mem hkD)
  have hWf : W ≤ Cen f₃ := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hf₃D).2).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc x₃ * f₃ = k * (x * f) * k⁻¹ := by rw [hx₃, hf₃]; group
        _ = k * (f * x) * k⁻¹ := by rw [hfx]
        _ = f₃ * x₃ := by rw [hx₃, hf₃]; group
  have hbf : h * b * h⁻¹ * f₃ = f₃ * (h * b * h⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hWf hhb)
  set g₅ := (h⁻¹ * k) * f * (h⁻¹ * k)⁻¹ with hg₅
  have hg₅f : g₅ = h⁻¹ * f₃ * h := by rw [hg₅, hf₃]; group
  have hg₅b : g₅ ∈ Cen b := by
    rw [Subgroup.mem_centralizer_singleton_iff, hg₅f]
    calc h⁻¹ * f₃ * h * b = h⁻¹ * (f₃ * (h * b * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * b * h⁻¹ * f₃) * h := by rw [hbf]
      _ = b * (h⁻¹ * f₃ * h) := by group
  have hg₅s : g₅ ∈ Cen s₀ := by
    rw [hg₅f]
    exact (Cen s₀).mul_mem ((Cen s₀).mul_mem ((Cen s₀).inv_mem hhs)
      (Subgroup.mem_inf.mp hf₃D).1) hhs
  have hg₅o : orderOf g₅ = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hg₅, conj_pow, ← hfo, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    · intro h1
      rw [hg₅, conj_eq_one_iff] at h1
      rw [h1, orderOf_one] at hfo
      omega
  have hg₅L : g₅ ∈ L := h5.mem_L_of_coprime hg₅b (by rw [hg₅o]; norm_num)
  have hd : 5 ∣ Nat.card ↥(L ⊓ Cen s₀) := by
    have := orderOf_dvd_natCard (⟨g₅, Subgroup.mem_inf.mpr ⟨hg₅L, hg₅s⟩⟩ : ↥(L ⊓ Cen s₀))
    rwa [Subgroup.orderOf_mk, hg₅o] at this
  exact hC.2.2 hd

end NoFive

section Rho

variable {s₀ : G} (hs : orderOf s₀ = 2)
  (κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7)
  (hκ : κ ⟨s₀, S56.s₀_mem_center hs⟩ = Multiplicative.ofAdd (Pi.single 0 1))

noncomputable def S56.rhoD (u : G) : ↥(Cen s₀ ⊓ Cen u) →* GL6 :=
  (S56.rhoBar hs κ hκ).comp (Subgroup.inclusion inf_le_left)

noncomputable def S56.rhoJ {u : G} {J : Subgroup G} (hJD : J ≤ Cen s₀ ⊓ Cen u)
    (e : ↥J ≃* Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 6) →* GL6 :=
  (S56.rhoD hs κ hκ u).comp ((Subgroup.inclusion hJD).comp e.symm.toMonoidHom)

end Rho

section Coord

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.u_mem_D : b₂ * b₃ ∈ Cen s₀ ⊓ Cen (b₂ * b₃) := h5.A₁_le_D h5.u_mem_A₁

omit h5 in
theorem FF81Sec5.J_le_D (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀) :
    OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀ ⊓ Cen (b₂ * b₃) := fun j hj => by
  have hj' : j ∈ CenS (Subgroup.closure {b₂, b₃}) := Subgroup.map_subtype_le _ hj
  rw [Subgroup.mem_centralizer_iff] at hj'
  have h2 := hj' b₂ (Subgroup.subset_closure (by simp))
  have h3 := hj' b₃ (Subgroup.subset_closure (by simp))
  refine Subgroup.mem_inf.mpr ⟨hJs hj, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc j * (b₂ * b₃) = (j * b₂) * b₃ := (mul_assoc _ _ _).symm
    _ = (b₂ * j) * b₃ := by rw [h2]
    _ = b₂ * (j * b₃) := mul_assoc _ _ _
    _ = b₂ * (b₃ * j) := by rw [h3]
    _ = b₂ * b₃ * j := (mul_assoc _ _ _).symm

theorem FF81Sec5.exists_coord (hbig : h5.Big) :
    ∃ κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7,
      κ ⟨s₀, S56.s₀_mem_center h5.hs₀⟩ = Multiplicative.ofAdd (Pi.single 0 1) := by
  have hZe : CFSG.Open.IsElemAbelian 2 (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) := by
    rw [hbig.center_eq]
    exact ⟨⟨⟨fun a c => Subtype.ext (hbig.Zcomm _ a.2 _ c.2)⟩⟩,
      fun x hx => by rw [pow_two]; exact hbig.Zsq x hx⟩
  have hZc : Nat.card ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) = 2 ^ 7 := by
    rw [hbig.center_eq]; exact hbig.cardZ
  have hs1 : s₀ ≠ 1 := fun h => by
    have := h5.hs₀
    rw [h, orderOf_one] at this
    omega
  exact S56.exists_coord hZe hZc (S56.s₀_mem_center h5.hs₀) hs1

end Coord

section ClaimC

variable (hKF : KF_Sp6Levi) (hKC : KF_Sp6ShortRootCen)
  (hGL : KF_Sp4CenGL6) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (hbig : h5.Big)
  (c2 : FF81Conc5_2 b b₁ b₂ b₃ s₀)
  (e : ↥(OUp 3 (CenS (Subgroup.closure {b₂, b₃}))) ≃* Equiv.Perm (Fin 6))
  (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀)
  (κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7)
  (hκ : κ ⟨s₀, S56.s₀_mem_center h5.hs₀⟩ = Multiplicative.ofAdd (Pi.single 0 1))
include hKF hKC hGL h5 hbig c2

theorem FF81Sec5.rhoD_facts :
    orderOf (S56.rhoD h5.hs₀ κ hκ (b₂ * b₃) ⟨b₂ * b₃, h5.u_mem_D⟩) = 3 ∧
    16 ≤ Nat.card {v : Fin 6 → ZMod 2 //
      ((S56.rhoD h5.hs₀ κ hκ (b₂ * b₃) ⟨b₂ * b₃, h5.u_mem_D⟩ : GL6) : M6) *ᵥ v = v} ∧
    S56.rhoJ h5.hs₀ κ hκ (FF81Sec5.J_le_D hJs) e (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 ∧
    (S56.rhoD h5.hs₀ κ hκ (b₂ * b₃)).range =
      (S56.rhoJ h5.hs₀ κ hκ (FF81Sec5.J_le_D hJs) e).range ⊔
        Subgroup.zpowers (S56.rhoD h5.hs₀ κ hκ (b₂ * b₃) ⟨b₂ * b₃, h5.u_mem_D⟩) := by
  have hcen := h5.cenS_center hKF hKC hbig c2
  obtain ⟨hcu, hcuE⟩ := h5.cen_u₃ hKF hbig
  have hu3 : (b₂ * b₃) ^ 3 = 1 := by rw [← h5.orderOf_u]; exact pow_orderOf_eq_one _
  have hker : ∀ {g : G} (hg : g ∈ Cen s₀), S56.rhoBar h5.hs₀ κ hκ ⟨g, hg⟩ = 1 →
      g ∈ Op 2 (Cen s₀) := fun hg h1 => S56.mem_S_of_rhoBar_eq_one h5.hs₀ κ hκ hcen hg h1
  have hDs : Cen s₀ ⊓ Cen (b₂ * b₃) ≤ Cen s₀ := inf_le_left
  set ψ := S56.rhoD h5.hs₀ κ hκ (b₂ * b₃) with hψ
  have huD := h5.u_mem_D
  have hJD := FF81Sec5.J_le_D hJs
  set φ := S56.rhoJ h5.hs₀ κ hκ hJD e with hφ
  set u' := ψ ⟨b₂ * b₃, huD⟩ with hu'
  have hS3 : ∀ {y : G}, y ∈ Op 2 (Cen s₀) → y ^ 3 = 1 → y = 1 := fun hy h =>
    S56.eq_one_of_mem_op_two hy (by norm_num) h
  have hu'3 : orderOf u' = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · have : (⟨b₂ * b₃, huD⟩ : ↥(Cen s₀ ⊓ Cen (b₂ * b₃))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hu3)
      rw [hu', ← map_pow, this, map_one]
    · intro h1
      have := hS3 (hker (hDs huD) h1) hu3
      have ho := h5.orderOf_u
      rw [this, orderOf_one] at ho
      omega
  have h16 : 16 ≤ Nat.card {v : Fin 6 → ZMod 2 // (u' : M6) *ᵥ v = v} := by
    have hle := S56.card_cen_le h5.hs₀ κ hκ (hDs huD)
    have heq : (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ⊓ Cen (b₂ * b₃) =
        Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃) := by
      refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf ?_ inf_le_right)
      rw [hcu]
      exact sup_le (h5.W_le_center hbig (by simp)) (h5.W_le_center hbig (by simp))
    rw [heq, hcuE.2] at hle
    change 2 ^ 5 ≤ 2 * Nat.card {v : Fin 6 → ZMod 2 // (u' : M6) *ᵥ v = v} at hle
    omega
  have hu'Y : u' ∈ ψ.range := ⟨_, rfl⟩
  have hYc : ψ.range ≤ Subgroup.centralizer {u'} := by
    rintro _ ⟨d, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hu', ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d.2).2))
  have hφY : ∀ σ, φ σ ∈ ψ.range := fun σ => ⟨_, rfl⟩
  have hφ1 : φ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 := by
    intro h1
    set j := e.symm (Equiv.swap 0 1 * Equiv.swap 1 2) with hj
    have hj3 : (j : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hj, ← map_pow,
        show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1 by decide, map_one,
        Subgroup.coe_one]
    have hj1 : (j : G) = 1 := hS3 (hker (hDs (hJD j.2)) h1) hj3
    have : j = 1 := Subtype.ext hj1
    rw [hj, map_eq_one_iff _ e.symm.injective] at this
    exact absurd this (by decide)
  refine ⟨hu'3, h16, hφ1, ?_⟩
  rcases hGL ψ.range u' φ hu'3 h16 hu'Y hYc hφY hφ1 with hY | ⟨hYcard, f, hfY, x, hxY, hfo, hxo,
    hxu', hfx⟩
  · exact hY
  ·
    exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hkp : IsPGroup 2 ψ.ker := fun k => by
      have hkS : ((k : ↥(Cen s₀ ⊓ Cen (b₂ * b₃))) : G) ∈ Op 2 (Cen s₀) :=
        hker (hDs (k : ↥(Cen s₀ ⊓ Cen (b₂ * b₃))).2) k.2
      obtain ⟨n, hn⟩ := op_two_isPGroup s₀ ⟨_, hkS⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
      simpa using this
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkp
    have hDc : Nat.card ↥(Cen s₀ ⊓ Cen (b₂ * b₃)) = 2 ^ n * 60480 := by
      rw [← Subgroup.card_ker_mul_card_range ψ, hn, hYcard]
    have hsyl : Nat.Coprime 3 ((A₁sub b b₁ b₂ b₃).relIndex (Cen s₀ ⊓ Cen (b₂ * b₃))) := by
      have hr := Subgroup.relIndex_mul_card (H := A₁sub b b₁ b₂ b₃) (K := Cen s₀ ⊓ Cen (b₂ * b₃))
      rw [inf_of_le_left h5.A₁_le_D, h5.coordA.card, hDc] at hr
      generalize hP : 2 ^ n = P at hr
      have hr' : (A₁sub b b₁ b₂ b₃).relIndex (Cen s₀ ⊓ Cen (b₂ * b₃)) = P * 2240 := by omega
      rw [hr', ← hP]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right n (by norm_num)) (by norm_num)
    obtain ⟨f₂, x₂, hf₂, hx₂, hxx₂, hfx₂⟩ := S56.exists_lift ψ hn hfY hxY hfo hxo hfx
    refine h5.no_five hKC c2 hsyl f₂.2 x₂.2 (by rw [Subgroup.orderOf_coe, hf₂])
      (by simpa using congrArg Subtype.val hx₂) (fun hx₂u => hxu' ?_)
      (congrArg Subtype.val hfx₂)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx₂u
    have : x₂ = (⟨b₂ * b₃, huD⟩ : ↥(Cen s₀ ⊓ Cen (b₂ * b₃))) ^ i :=
      Subtype.ext (by simpa using hi.symm)
    have hx₂z : ψ x₂ ∈ Subgroup.zpowers u' := by
      rw [this, map_zpow]; exact Subgroup.zpow_mem_zpowers _ _
    exact Subgroup.zpowers_le.mpr hx₂z hxx₂

omit c2 in
theorem FF81Sec5.cen_s₀_u₃ (c2 : FF81Conc5_2 b b₁ b₂ b₃ s₀) (c4 : FF81Conc5_4 b b₁ b₂ b₃ s₀) :
    Cen s₀ ⊓ Cen (b₂ * b₃) = (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) ⊔
      OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔ Subgroup.zpowers (b₂ * b₃) := by
  obtain ⟨⟨e⟩, hJs, -, -⟩ := c4
  have hcen := h5.cenS_center hKF hKC hbig c2
  obtain ⟨κ, hκ⟩ := h5.exists_coord hbig
  have hker : ∀ {g : G} (hg : g ∈ Cen s₀), S56.rhoBar h5.hs₀ κ hκ ⟨g, hg⟩ = 1 →
      g ∈ Op 2 (Cen s₀) := fun hg h1 => S56.mem_S_of_rhoBar_eq_one h5.hs₀ κ hκ hcen hg h1
  have hDs : Cen s₀ ⊓ Cen (b₂ * b₃) ≤ Cen s₀ := inf_le_left
  have hY := (h5.rhoD_facts hKF hKC hGL hbig c2 e hJs κ hκ).2.2.2
  set ψ := S56.rhoD h5.hs₀ κ hκ (b₂ * b₃) with hψ
  have huD := h5.u_mem_D
  have hJD := FF81Sec5.J_le_D hJs
  set φ := S56.rhoJ h5.hs₀ κ hκ hJD e with hφ
  set u' := ψ ⟨b₂ * b₃, huD⟩ with hu'
  refine le_antisymm (fun d hd => ?_) (sup_le (sup_le (inf_le_inf_right _ (op_two_le s₀)) hJD)
    (Subgroup.zpowers_le.mpr huD))
  set M := (OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔ Subgroup.zpowers (b₂ * b₃)).subgroupOf
    (Cen s₀ ⊓ Cen (b₂ * b₃)) with hM
  have hle : φ.range ⊔ Subgroup.zpowers u' ≤ M.map ψ := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ⟨⟨b₂ * b₃, huD⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)), rfl⟩)
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (e.symm σ).2), rfl⟩
  obtain ⟨m, hm, hmd⟩ := hle (by rw [← hY]; exact ⟨⟨d, hd⟩, rfl⟩)
  have h1 : ψ (m⁻¹ * ⟨d, hd⟩) = 1 := by rw [map_mul, map_inv, hmd, inv_mul_cancel]
  have hmS : (m : G)⁻¹ * d ∈ Op 2 (Cen s₀) := hker (hDs (m⁻¹ * ⟨d, hd⟩).2) h1
  have hmu : (m : G)⁻¹ * d ∈ Cen (b₂ * b₃) := (Subgroup.mem_inf.mp (m⁻¹ * ⟨d, hd⟩).2).2
  have hJZ : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔ Subgroup.zpowers (b₂ * b₃) ≤
      (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) ⊔ OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔
        Subgroup.zpowers (b₂ * b₃) :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have := Subgroup.mul_mem _ (hJZ (Subgroup.mem_subgroupOf.mp hm))
    ((le_sup_left.trans le_sup_left : Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃) ≤ _)
      (Subgroup.mem_inf.mpr ⟨hmS, hmu⟩))
  rwa [mul_inv_cancel_left] at this

end ClaimC

theorem ff81_5_6 (hKF : KF_Sp6Levi) (hKS : KF_Sp6ShortRoot)
    (hKC : KF_Sp6ShortRootCen) (hGL : KF_Sp4CenGL6) : FF81_5_6 := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 _ _ c2 c4 _
  have hbig := h5.big hKF hKS
  exact ⟨h5.cenS_center hKF hKC hbig c2, (h5.cen_u₃ hKF hbig).2,
    h5.cen_s₀_u₃ hKF hKC hGL hbig c2 c4⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
