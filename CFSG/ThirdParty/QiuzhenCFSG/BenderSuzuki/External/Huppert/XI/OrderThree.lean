module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.External

universe u v w

/--
Huppert XI.2.2 (Tits), in a transport-friendly form. In a sharply triply
transitive action with no nonidentity element fixing three points, any group
embedded in the pointwise stabilizer of two points has at most one subgroup of
order three.
-/
public theorem huppert_XI_2_2_subgroup_order_three_unique
    {G : Type u} {Omega : Type v} {A : Type w}
    [Group G] [MulAction G Omega] [Group A] [Finite A]
    (ι : A →* G) (hι : Function.Injective ι)
    (a b x : Omega) (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x)
    (hfixa : ∀ d : A, ι d • a = a)
    (hfixb : ∀ d : A, ι d • b = b)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c)) :
    ∀ U V : Subgroup A, Nat.card U = 3 → Nat.card V = 3 → U = V := by
  classical
  have hthree_ext :
      ∀ r s : G, ∀ p q z : Omega,
        p ≠ q → p ≠ z → q ≠ z →
        r • p = s • p → r • q = s • q → r • z = s • z → r = s := by
    intro r s p q z hpq hpz hqz hp hq hz
    have hfixp : (s⁻¹ * r) • p = p := by
      rw [mul_smul, hp, inv_smul_smul]
    have hfixq : (s⁻¹ * r) • q = q := by
      rw [mul_smul, hq, inv_smul_smul]
    have hfixz : (s⁻¹ * r) • z = z := by
      rw [mul_smul, hz, inv_smul_smul]
    have hone : s⁻¹ * r = 1 := by
      by_contra hne
      exact hat_most_two_fixed_points (s⁻¹ * r) hne p q z hpq hpz hqz
        ⟨hfixp, hfixq, hfixz⟩
    exact (inv_mul_eq_one.mp hone).symm
  have hi_ne_one :
      ∀ d : A, d ≠ 1 → ι d ≠ 1 := by
    intro d hd hid
    apply hd
    apply hι
    simpa using hid
  have hfixed_mem :
      ∀ d : A, d ≠ 1 → ∀ z : Omega, ι d • z = z → z = a ∨ z = b := by
    intro d hd z hz
    by_cases hza : z = a
    · exact Or.inl hza
    by_cases hzb : z = b
    · exact Or.inr hzb
    exfalso
    exact hat_most_two_fixed_points (ι d) (hi_ne_one d hd)
      a b z hab (fun h => hza h.symm) (fun h => hzb h.symm) ⟨hfixa d, hfixb d, hz⟩
  have hgenerator :
      ∀ W : Subgroup A, Nat.card W = 3 →
        ∃ d : A, orderOf d = 3 ∧ Subgroup.zpowers d = W := by
    intro W hW
    have hWnontrivial : Nontrivial W :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial W := hWnontrivial
    obtain ⟨d, hdne⟩ := exists_ne (1 : W)
    have hdorderW : orderOf d = 3 := by
      have hdvd : orderOf d ∣ 3 := by
        simpa [hW] using orderOf_dvd_natCard d
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with hone | hthree
      · exact False.elim (hdne (orderOf_eq_one_iff.mp hone))
      · exact hthree
    have hdorderA : orderOf (d : A) = 3 := by
      simpa only [Subgroup.orderOf_coe] using hdorderW
    refine ⟨(d : A), hdorderA, ?_⟩
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).2 d.property
    · rw [Nat.card_zpowers, hdorderA, hW]
  intro U V hU hV
  by_cases hUV : U = V
  · exact hUV
  obtain ⟨u, huorder, hzu⟩ := hgenerator U hU
  obtain ⟨v, hvorder, hzv⟩ := hgenerator V hV
  let ug : G := ι u
  let vg : G := ι v
  have hugorder : orderOf ug = 3 := by
    simpa [ug] using (orderOf_injective ι hι u).trans huorder
  have hvgorder : orderOf vg = 3 := by
    simpa [vg] using (orderOf_injective ι hι v).trans hvorder
  have hu_ne : u ≠ 1 := by
    intro hu
    rw [hu, orderOf_one] at huorder
    omega
  have hv_ne : v ≠ 1 := by
    intro hv
    rw [hv, orderOf_one] at hvorder
    omega
  have hu_sq_ne : u ^ 2 ≠ 1 := by
    intro hu2
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    rw [huorder] at hdvd
    omega
  have hug_ne : ug ≠ 1 := hi_ne_one u hu_ne
  have hvg_ne : vg ≠ 1 := hi_ne_one v hv_ne
  have hug_cube : ug ^ 3 = 1 := by
    rw [← hugorder]
    exact pow_orderOf_eq_one ug
  have hvg_cube : vg ^ 3 = 1 := by
    rw [← hvgorder]
    exact pow_orderOf_eq_one vg
  let y : Omega := ug • x
  let z : Omega := (ug ^ 2) • x
  let y' : Omega := vg • x
  let z' : Omega := (vg ^ 2) • x
  have hxy : x ≠ y := by
    intro h
    exact hat_most_two_fixed_points ug hug_ne a b x hab hax hbx
      ⟨hfixa u, hfixb u, by simpa [y] using h.symm⟩
  have hxz : x ≠ z := by
    intro h
    have hfix : ι (u ^ 2) • x = x := by
      simpa [z] using h.symm
    exact hat_most_two_fixed_points (ι (u ^ 2))
      (hi_ne_one (u ^ 2) hu_sq_ne) a b x hab hax hbx
      ⟨hfixa (u ^ 2), hfixb (u ^ 2), hfix⟩
  have hyz : y ≠ z := by
    intro h
    apply hxy
    apply (MulAction.toPermHom G Omega ug).injective
    simpa [y, z, pow_two, mul_smul] using h
  have hxy' : x ≠ y' := by
    intro h
    exact hat_most_two_fixed_points vg hvg_ne a b x hab hax hbx
      ⟨hfixa v, hfixb v, by simpa [y'] using h.symm⟩
  have hv_sq_ne : v ^ 2 ≠ 1 := by
    intro hv2
    have hdvd : orderOf v ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hv2
    rw [hvorder] at hdvd
    omega
  have hxz' : x ≠ z' := by
    intro h
    have hfix : ι (v ^ 2) • x = x := by
      simpa [z'] using h.symm
    exact hat_most_two_fixed_points (ι (v ^ 2))
      (hi_ne_one (v ^ 2) hv_sq_ne) a b x hab hax hbx
      ⟨hfixa (v ^ 2), hfixb (v ^ 2), hfix⟩
  have hyz' : y' ≠ z' := by
    intro h
    apply hxy'
    apply (MulAction.toPermHom G Omega vg).injective
    simpa [y', z', pow_two, mul_smul] using h
  have hug_x : ug • x = y := rfl
  have hug_y : ug • y = z := by
    simp [y, z, pow_two, mul_smul]
  have hug_z : ug • z = x := by
    calc
      ug • z = (ug ^ 3) • x := by simp [z, pow_succ', mul_smul]
      _ = x := by rw [hug_cube]; simp
  have hvg_x : vg • x = y' := rfl
  have hvg_y : vg • y' = z' := by
    simp [y', z', pow_two, mul_smul]
  have hvg_z : vg • z' = x := by
    calc
      vg • z' = (vg ^ 3) • x := by simp [z', pow_succ', mul_smul]
      _ = x := by rw [hvg_cube]; simp
  obtain ⟨g, hg, _hguniq⟩ :=
    hsharp x y z x z y hxy hxz hyz hxz hxy hyz.symm
  obtain ⟨g', hg', _hg'uniq⟩ :=
    hsharp x y z x y' z' hxy hxz hyz hxy' hxz' hyz'
  have hg_inv_x : g⁻¹ • x = x := by
    calc
      g⁻¹ • x = g⁻¹ • (g • x) := congrArg (fun q => g⁻¹ • q) hg.1.symm
      _ = x := inv_smul_smul g x
  have hg_inv_y : g⁻¹ • y = z := by
    rw [← hg.2.2]
    exact inv_smul_smul g z
  have hg_inv_z : g⁻¹ • z = y := by
    rw [← hg.2.1]
    exact inv_smul_smul g y
  have hg'_inv_x : g'⁻¹ • x = x := by
    calc
      g'⁻¹ • x = g'⁻¹ • (g' • x) :=
        congrArg (fun q => g'⁻¹ • q) hg'.1.symm
      _ = x := inv_smul_smul g' x
  have hg'_inv_y' : g'⁻¹ • y' = y := by
    rw [← hg'.2.1]
    exact inv_smul_smul g' y
  have hg'_inv_z' : g'⁻¹ • z' = z := by
    rw [← hg'.2.2]
    exact inv_smul_smul g' z
  have hug_sq_x : (ug ^ 2) • x = z := rfl
  have hug_sq_y : (ug ^ 2) • y = x := by
    calc
      (ug ^ 2) • y = (ug ^ 3) • x := by
        simp [y, pow_succ', mul_smul]
      _ = x := by rw [hug_cube]; simp
  have hug_four : ug ^ 4 = ug := by
    calc
      ug ^ 4 = ug ^ 3 * ug := by group
      _ = ug := by rw [hug_cube]; simp
  have hug_sq_z : (ug ^ 2) • z = y := by
    calc
      (ug ^ 2) • z = (ug ^ 4) • x := by
        change (ug ^ 2) • ((ug ^ 2) • x) = (ug ^ 4) • x
        rw [← mul_smul]
        congr 1
        group
      _ = y := by
        simpa [y] using congrArg (fun q : G => q • x) hug_four
  have hconj_g : g * ug * g⁻¹ = ug ^ 2 := by
    apply hthree_ext (g * ug * g⁻¹) (ug ^ 2) x y z hxy hxz hyz
    · simp [mul_smul, hg_inv_x, hug_x, hg.2.1, hug_sq_x]
    · simp [mul_smul, hg_inv_y, hug_z, hg.1, hug_sq_y]
    · simp [mul_smul, hg_inv_z, hug_y, hg.2.2, hug_sq_z]
  have hconj_g' : g' * ug * g'⁻¹ = vg := by
    apply hthree_ext (g' * ug * g'⁻¹) vg x y' z' hxy' hxz' hyz'
    · simp [mul_smul, hg'_inv_x, hug_x, hg'.2.1, hvg_x]
    · simp [mul_smul, hg'_inv_y', hug_y, hg'.2.2, hvg_y]
    · simp [mul_smul, hg'_inv_z', hug_z, hg'.1, hvg_z]
  have hg_ne : g ≠ 1 := by
    intro hg1
    apply hyz
    calc
      y = (1 : G) • y := by simp
      _ = g • y := by rw [hg1]
      _ = z := hg.2.1
  have hg'_ne : g' ≠ 1 := by
    intro hg1
    have huvG : ug = vg := by
      calc
        ug = (1 : G) * ug * (1 : G)⁻¹ := by simp
        _ = g' * ug * g'⁻¹ := by rw [hg1]
        _ = vg := hconj_g'
    have huv : u = v := hι (by simpa [ug, vg] using huvG)
    apply hUV
    rw [← hzu, ← hzv, huv]
  have hg_a_fixed : ι (u ^ 2) • (g • a) = g • a := by
    calc
      ι (u ^ 2) • (g • a) = (ug ^ 2) • (g • a) := by simp [ug]
      _ = (g * ug * g⁻¹) • (g • a) := by rw [hconj_g]
      _ = g • (ug • a) := by simp [mul_smul]
      _ = g • a := by rw [show ug • a = a by simpa [ug] using hfixa u]
  have hg_b_fixed : ι (u ^ 2) • (g • b) = g • b := by
    calc
      ι (u ^ 2) • (g • b) = (ug ^ 2) • (g • b) := by simp [ug]
      _ = (g * ug * g⁻¹) • (g • b) := by rw [hconj_g]
      _ = g • (ug • b) := by simp [mul_smul]
      _ = g • b := by rw [show ug • b = b by simpa [ug] using hfixb u]
  have hg'_a_fixed : ι v • (g' • a) = g' • a := by
    calc
      ι v • (g' • a) = vg • (g' • a) := rfl
      _ = (g' * ug * g'⁻¹) • (g' • a) := by rw [hconj_g']
      _ = g' • (ug • a) := by simp [mul_smul]
      _ = g' • a := by rw [show ug • a = a by simpa [ug] using hfixa u]
  have hg'_b_fixed : ι v • (g' • b) = g' • b := by
    calc
      ι v • (g' • b) = vg • (g' • b) := rfl
      _ = (g' * ug * g'⁻¹) • (g' • b) := by rw [hconj_g']
      _ = g' • (ug • b) := by simp [mul_smul]
      _ = g' • b := by rw [show ug • b = b by simpa [ug] using hfixb u]
  have hg_a_mem : g • a = a ∨ g • a = b :=
    hfixed_mem (u ^ 2) hu_sq_ne (g • a) hg_a_fixed
  have hg_b_mem : g • b = a ∨ g • b = b :=
    hfixed_mem (u ^ 2) hu_sq_ne (g • b) hg_b_fixed
  have hg'_a_mem : g' • a = a ∨ g' • a = b :=
    hfixed_mem v hv_ne (g' • a) hg'_a_fixed
  have hg'_b_mem : g' • b = a ∨ g' • b = b :=
    hfixed_mem v hv_ne (g' • b) hg'_b_fixed
  have hswap :
      ∀ r : G, r ≠ 1 → r • x = x →
        (r • a = a ∨ r • a = b) →
        (r • b = a ∨ r • b = b) →
        r • a = b ∧ r • b = a := by
    intro r hrne hrx hram hrbm
    rcases hram with hra | hra <;> rcases hrbm with hrb | hrb
    · exfalso
      apply hab
      exact (MulAction.toPermHom G Omega r).injective
        (hra.trans hrb.symm)
    · exfalso
      exact hat_most_two_fixed_points r hrne a b x hab hax hbx
        ⟨hra, hrb, hrx⟩
    · exact ⟨hra, hrb⟩
    · exfalso
      apply hab
      exact (MulAction.toPermHom G Omega r).injective
        (hra.trans hrb.symm)
  have hgswap : g • a = b ∧ g • b = a :=
    hswap g hg_ne hg.1 hg_a_mem hg_b_mem
  have hg'swap : g' • a = b ∧ g' • b = a :=
    hswap g' hg'_ne hg'.1 hg'_a_mem hg'_b_mem
  have hgg' : g = g' :=
    hthree_ext g g' a b x hab hax hbx
      (hgswap.1.trans hg'swap.1.symm)
      (hgswap.2.trans hg'swap.2.symm)
      (hg.1.trans hg'.1.symm)
  have huvG : vg = ug ^ 2 := by
    calc
      vg = g' * ug * g'⁻¹ := hconj_g'.symm
      _ = g * ug * g⁻¹ := by rw [hgg']
      _ = ug ^ 2 := hconj_g
  have huv : v = u ^ 2 := by
    apply hι
    simpa [vg, ug] using huvG
  have hVleU : V ≤ U := by
    rw [← hzv]
    apply (Subgroup.zpowers_le).2
    rw [huv]
    exact U.pow_mem (by
      rw [← hzu]
      exact Subgroup.mem_zpowers u) 2
  exact (Subgroup.eq_of_le_of_card_ge hVleU (by rw [hU, hV])).symm

end CFSG.BenderSuzuki.External
