module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.Assembly.Defs
public import CFSG.Dihedral.Glauberman.DicksonMaxList

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open scoped MatrixGroups

theorem sq_eq_one_of_comm_sr {n : ℕ} (x : DihedralGroup n)
    (h : x * DihedralGroup.sr 0 = DihedralGroup.sr 0 * x) : x ^ 2 = 1 := by
  rcases x with i | i
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq, zero_sub,
      zero_add] at h
    have h2 : i + i = 0 := by
      rw [← neg_add_cancel i, h]
    rw [sq, DihedralGroup.r_mul_r, h2, DihedralGroup.r_zero]
  · rw [sq, DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]

theorem perm_four_eq_one : ∀ x : Equiv.Perm (Fin 4),
    x * Equiv.swap 0 1 = Equiv.swap 0 1 * x →
    x * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) =
      (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) * x → x = 1 := by
  decide

theorem mem_center_of_mulEquiv {H Q : Type*} [Group H] [Group Q] (f : H ≃* Q) {x : H}
    (hx : ∀ h : H, h * x = x * h) : f x ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨h, rfl⟩ := f.surjective q
  rw [← map_mul, ← map_mul, hx h]

theorem isCyclic_centralizer {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (e : A ≃* PSL(2, ZMod p)) {g : A} (hg3 : 3 ≤ orderOf g)
    (hgp : ¬ p ∣ orderOf g) : IsCyclic (Subgroup.centralizer ({g} : Set A)) := by
  set H := Subgroup.centralizer ({g} : Set A) with hH
  set H' : Subgroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup (ZMod p)) := H.map e.toMonoidHom
    with hH'
  let eH : ↥H ≃* ↥H' := Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
  have hgH : g ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set x : ↥H' := eH ⟨g, hgH⟩ with hx
  have hxc : ∀ h : ↥H', h * x = x * h := by
    intro h
    obtain ⟨h0, rfl⟩ := eH.surjective h
    rw [hx, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp h0.2)
  have hox : orderOf x = orderOf g := by
    rw [hx, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  have hx2 : ¬ x ^ 2 = 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    omega
  have hx1 : x ≠ 1 := by
    intro h
    apply hx2
    rw [h, one_pow]
  have hxp : ¬ x ^ p = 1 := by
    intro h
    rcases (Nat.dvd_prime hp.out).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h1
    · exact hx1 (orderOf_eq_one_iff.mp h1)
    · exact hgp ⟨1, by rw [← hox, h1, mul_one]⟩
  suffices IsCyclic ↥H' from isCyclic_of_surjective eH.symm.toMonoidHom eH.symm.surjective
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list (F := ZMod p) hF H' with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨eD⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ |
      ⟨-, ⟨eA5⟩⟩ | ⟨m, t, -, -, -, -, E, C, hEn, hEel, -, -, -, -, hEC, hfaith, -⟩ |
      ⟨m, hm, ⟨eL⟩⟩ | ⟨m, hm, -⟩
  ·
    exact (hxp (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p ↥H') x)).elim
  · exact hcyc
  ·
    exfalso
    apply hx2
    have h := sq_eq_one_of_comm_sr (eD x)
      (Subgroup.mem_center_iff.mp (mem_center_of_mulEquiv eD hxc) _).symm
    exact eD.injective (by rw [map_pow, h, map_one])
  ·
    exfalso
    apply hx1
    have h := mem_center_of_mulEquiv eA hxc
    rw [alternatingGroup.center_eq_bot (le_of_eq (Nat.card_fin 4).symm), Subgroup.mem_bot] at h
    exact eA.injective (by rw [h, map_one])
  ·
    exfalso
    apply hx1
    have h := Subgroup.mem_center_iff.mp (mem_center_of_mulEquiv eS hxc)
    have h1 := perm_four_eq_one (eS x) (h _).symm (h _).symm
    exact eS.injective (by rw [h1, map_one])
  ·
    exfalso
    apply hx1
    have h := mem_center_of_mulEquiv eA5 hxc
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot] at h
    exact eA5.injective (by rw [h, map_one])
  ·
    exfalso
    have : E.Normal := hEn
    have hxEC : x ∈ ((E ⊔ C : Subgroup ↥H') : Set ↥H') := by rw [hEC]; exact Subgroup.mem_top x
    rw [Subgroup.normal_mul] at hxEC
    obtain ⟨e₀, he₀, c₀, hc₀, hec⟩ := Set.mem_mul.mp hxEC
    have hcomm := isMulCommutative_iff.mp hEel.toIsMulCommutative
    have hc₁ : c₀ = 1 := by
      refine hfaith c₀ hc₀ fun e' he' => ?_
      have hc' : c₀ = e₀⁻¹ * x := by rw [← hec]; group
      have h1 : e₀⁻¹ * e' = e' * e₀⁻¹ :=
        congrArg Subtype.val (hcomm ⟨e₀⁻¹, E.inv_mem he₀⟩ ⟨e', he'⟩)
      rw [hc', mul_assoc, ← hxc e', ← mul_assoc, h1, mul_assoc]
    rw [hc₁, mul_one] at hec
    rw [← hec] at hxp
    exact hxp (CFSG.elemPow_eq_one_of_isElementaryAbelian e₀ he₀)
  ·
    exfalso
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hm
    subst hm1
    apply hx1
    have h := mem_center_of_mulEquiv eL hxc
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p 1), Subgroup.mem_bot] at h
    exact eL.injective (by rw [h, map_one])
  ·
    exfalso
    have := Nat.eq_one_of_dvd_one hm
    omega

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
