module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem E6QTwo.y_ne_one_of_notMem_closure {Bs K' : Subgroup G} {y : G} (hyB : y ∈ Bs)
    (hyC : (⟨y, hyB⟩ : ↥Bs) ∉
      Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) :
    y ≠ 1 := by
  intro hy1
  apply hyC
  have h1 : (⟨y, hyB⟩ : ↥Bs) = 1 := Subtype.ext hy1
  rw [h1]
  exact (Subgroup.closure _).one_mem

theorem E6QTwo.closure_map_subtype_le_of_le_normalizer {Bs K' : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (K' : Set G)) :
    (Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}).map
      Bs.subtype ≤ K' := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr ?_
  rintro b ⟨φ, hφ, c, rfl⟩
  change ((φ c * c⁻¹ : ↥Bs) : G) ∈ K'
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  have hval : ((φ c * c⁻¹ : ↥Bs) : G) = g * (c : G) * g⁻¹ * (c : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hg c]
  rw [hval]
  have hc : (c : G) * g⁻¹ * (c : G)⁻¹ ∈ K' :=
    (Subgroup.mem_normalizer_iff.mp (hBsN c.2) g⁻¹).mp (K'.inv_mem hgK)
  rw [show g * (c : G) * g⁻¹ * (c : G)⁻¹ = g * ((c : G) * g⁻¹ * (c : G)⁻¹) by group]
  exact K'.mul_mem hgK hc

private theorem E6QTwo.mem_zpowers_of_mem_inf_centralizer {Bs K' : Subgroup G} {y : G}
    (hyB : y ∈ Bs)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K' Bs, φ b = b) →
      b ∈ Subgroup.zpowers ⟨y, hyB⟩)
    {b : ↥Bs} (hbK : (b : G) ∈ Subgroup.centralizer (K' : Set G)) :
    b ∈ Subgroup.zpowers ⟨y, hyB⟩ := by
  refine hfix b ?_
  intro φ hφ
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  apply Subtype.ext
  rw [hg b]
  show g * (b : G) * g⁻¹ = (b : G)
  rw [Subgroup.mem_centralizer_iff.mp hbK g hgK, mul_inv_cancel_right]

private theorem E6QTwo.aut_eq_one_or_isTransvection {Bs : Subgroup G} {y : G}
    (hyBs : y ∈ Bs) (hy1 : y ≠ 1) (hBs : IsElemAbelian 3 Bs) {ψ : MulAut ↥Bs}
    (hψy : ψ ⟨y, hyBs⟩ = ⟨y, hyBs⟩)
    (hψ : ∀ b : ↥Bs, ((b⁻¹ * ψ b : ↥Bs) : G) ∈ Subgroup.zpowers y) :
    ψ = 1 ∨ GGIsTransvection 3 ψ := by
  classical
  haveI : IsMulCommutative ↥Bs := hBs.1
  let c : ↥Bs := ⟨y, hyBs⟩
  have hψc : ψ c = c := by simpa only [c] using hψy
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (y : G) ^ 3 = 1
    exact hBs.2 y hyBs
  have hc1 : c ≠ 1 := by
    intro h
    exact hy1 (by simpa [c] using congrArg Subtype.val h)
  have hc_ord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  let D : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * ψ b
      map_one' := by simp
      map_mul' := by
        intro a b
        show (a * b)⁻¹ * ψ (a * b) = (a⁻¹ * ψ a) * (b⁻¹ * ψ b)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hD_apply : ∀ b : ↥Bs, D b = b⁻¹ * ψ b := fun b => rfl
  have hfix : ∀ b : ↥Bs, ψ (b⁻¹ * ψ b) = b⁻¹ * ψ b := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    have hck : c ^ k = b⁻¹ * ψ b := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
      exact hk
    calc ψ (b⁻¹ * ψ b) = ψ (c ^ k) := by rw [hck]
      _ = (ψ c) ^ k := map_zpow ψ c k
      _ = c ^ k := by rw [hψc]
      _ = b⁻¹ * ψ b := hck
  have hD_ker : Nat.card {b : ↥Bs // ψ b = b} = Nat.card D.ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun b => ?_)
    show ψ b = b ↔ b ∈ D.ker
    rw [MonoidHom.mem_ker, hD_apply]
    exact eq_comm.trans inv_mul_eq_one.symm
  have hD_range_le : D.range ≤ Subgroup.zpowers c := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
    exact hk
  have hcard_zp : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, hc_ord]
  have hcardD : Nat.card D.ker * Nat.card D.range = Nat.card ↥Bs :=
    Subgroup.card_ker_mul_card_range D
  have hdvd : Nat.card D.range ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hD_range_le
    rwa [hcard_zp] at h
  by_cases hψ1 : ψ = 1
  · exact Or.inl hψ1
  · right
    refine ⟨?_, hfix⟩
    rw [hD_ker]
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (Nat.card D.range) hdvd with h1 | h3
    · exfalso
      have hbot : D.range = ⊥ := Subgroup.eq_bot_of_card_eq D.range h1
      have hD1 : D = 1 := by
        ext b
        have hmem : D b ∈ D.range := MonoidHom.mem_range.mpr ⟨b, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      apply hψ1
      ext b
      have hb : D b = 1 := by rw [hD1]; rfl
      have hb' : b⁻¹ * ψ b = 1 := by rw [← hD_apply]; exact hb
      exact congrArg Subtype.val (inv_mul_eq_one.mp hb').symm
    · rw [h3] at hcardD
      exact hcardD

theorem E6QTwo.centralizes_of_mem_center_inf_normalizer {Bs K' : Subgroup G} {y : G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs) (hyB : y ∈ Bs) (hy1 : y ≠ 1)
    (hK'y : K' ≤ Subgroup.centralizer ({y} : Set G)) (hBsN : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K' Bs, φ b = b) →
      b ∈ Subgroup.zpowers ⟨y, hyB⟩)
    {z : G} (hzN : z ∈ Subgroup.normalizer (Bs : Set G))
    (hzK : z ∈ (Subgroup.center ↥K').map K'.subtype) :
    z ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  obtain ⟨zK, hzKc, hzKval⟩ := Subgroup.mem_map.mp hzK
  have hzK' : z ∈ K' := hzKval ▸ zK.2
  have hzKeq : zK = (⟨z, hzK'⟩ : ↥K') := Subtype.ext hzKval
  have hzy : z * y = y * z := Subgroup.mem_centralizer_singleton_iff.mp (hK'y hzK')
  have hcentral : ∀ b : ↥Bs, ((b⁻¹ * ggConjAut Bs hzN b : ↥Bs) : G) ∈
      Subgroup.centralizer (K' : Set G) := by
    intro b
    have hbN : (b : G) ∈ Subgroup.normalizer (K' : Set G) := hBsN b.2
    have hmem : (b : G)⁻¹ * z * (b : G) ∈ K' := by
      have hbNinv : (b : G)⁻¹ ∈ Subgroup.normalizer (K' : Set G) := Subgroup.inv_mem _ hbN
      simpa using (Subgroup.mem_normalizer_iff.mp hbNinv z).mp hzK'
    have hcent : (⟨(b : G)⁻¹ * z * (b : G), hmem⟩ : ↥K') ∈ Subgroup.center ↥K' := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hk' : (b : G) * (k : G) * (b : G)⁻¹ ∈ K' :=
        (Subgroup.mem_normalizer_iff.mp hbN k).mp k.2
      have hzk1 : ((b : G) * (k : G) * (b : G)⁻¹) * z =
          z * ((b : G) * (k : G) * (b : G)⁻¹) := by
        have h := congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hzKc (⟨(b : G) * (k : G) * (b : G)⁻¹, hk'⟩ : ↥K'))
        rw [hzKeq] at h
        simpa using h
      calc (k : G) * ((b : G)⁻¹ * z * (b : G))
          = (b : G)⁻¹ * (((b : G) * (k : G) * (b : G)⁻¹) * z) * (b : G) := by group
        _ = (b : G)⁻¹ * (z * ((b : G) * (k : G) * (b : G)⁻¹)) * (b : G) := by rw [hzk1]
        _ = ((b : G)⁻¹ * z * (b : G)) * (k : G) := by group
    have hzKinv : z⁻¹ ∈ K' := K'.inv_mem hzK'
    have hzKinv_center : (⟨z⁻¹, hzKinv⟩ : ↥K') ∈ Subgroup.center ↥K' := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hzk := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzKc k)
      rw [hzKeq] at hzk
      exact (show Commute (k : G) z from hzk).inv_right.eq
    have hmZ : (b : G)⁻¹ * z * (b : G) * z⁻¹ ∈
        (Subgroup.center ↥K').map K'.subtype := by
      have := Subgroup.mem_map_of_mem K'.subtype (Subgroup.mul_mem _ hcent hzKinv_center)
      simpa [mul_assoc] using this
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hmval : ((b⁻¹ * ggConjAut Bs hzN b : ↥Bs) : G) =
        (b : G)⁻¹ * z * (b : G) * z⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ggConjAut_apply]
      group
    rw [hmval]
    obtain ⟨w, hwc, hwval⟩ := Subgroup.mem_map.mp hmZ
    have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc (⟨k, hk⟩ : ↥K'))
    rw [← hwval]
    exact hcomm
  have hψ : ∀ b : ↥Bs, ((b⁻¹ * ggConjAut Bs hzN b : ↥Bs) : G) ∈ Subgroup.zpowers y := by
    intro b
    have hb := E6QTwo.mem_zpowers_of_mem_inf_centralizer (K' := K') hyB hfix (hcentral b)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at hk'
    exact hk'
  have hψy : ggConjAut Bs hzN ⟨y, hyB⟩ = ⟨y, hyB⟩ := by
    apply Subtype.ext
    show z * y * z⁻¹ = y
    rw [hzy, mul_inv_cancel_right]
  have hsplit := E6QTwo.aut_eq_one_or_isTransvection hyB hy1 hBs hψy hψ
  rcases hsplit with h1 | htv
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : ggConjAut Bs hzN ⟨b, hb⟩ = ⟨b, hb⟩ := by rw [h1]; rfl
    have hval := congrArg (fun x : ↥Bs => (x : G)) hb'
    rw [ggConjAut_apply] at hval
    have hval' : z * (b : G) * z⁻¹ = (b : G) := hval
    have hzb : z * (b : G) = (b : G) * z := by
      calc z * (b : G) = (z * (b : G) * z⁻¹) * z := by group
        _ = (b : G) * z := by rw [hval']
    exact hzb.symm
  · exact absurd htv (hNT _ (ggConjAut_mem_ggInduced (Subgroup.mem_top z) hzN))

theorem E6QTwo.closure_map_subtype_inf_center_eq_bot {Bs K' : Subgroup G} {y : G}
    (hBs : IsElemAbelian 3 Bs) (hyB : y ∈ Bs)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K' Bs, φ b = b) →
      b ∈ Subgroup.zpowers ⟨y, hyB⟩)
    (hyC : (⟨y, hyB⟩ : ↥Bs) ∉
      Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) :
    (Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}).map
        Bs.subtype ⊓ (Subgroup.center ↥K').map K'.subtype = ⊥ := by
  classical
  set Cb : Subgroup ↥Bs :=
    Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}
    with hCbdef
  have hy1 : y ≠ 1 := E6QTwo.y_ne_one_of_notMem_closure hyB hyC
  have hy3 : (⟨y, hyB⟩ : ↥Bs) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 y hyB
  have hyord : Nat.card (Subgroup.zpowers (⟨y, hyB⟩ : ↥Bs)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 (fun h => hy1 (congrArg Subtype.val h))]
  have hCy : ∀ b : ↥Bs, b ∈ Cb → b ∈ Subgroup.zpowers ⟨y, hyB⟩ → b = 1 := by
    intro b hbC hbz
    by_contra hb1
    have hb3 : b ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBs.2 b.val b.2
    have hbord : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
    have hle : Subgroup.zpowers b ≤ Subgroup.zpowers (⟨y, hyB⟩ : ↥Bs) :=
      Subgroup.zpowers_le.mpr hbz
    have heq : Subgroup.zpowers b = Subgroup.zpowers (⟨y, hyB⟩ : ↥Bs) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hbord, hyord])
    have hy_mem : (⟨y, hyB⟩ : ↥Bs) ∈ Subgroup.zpowers b := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    exact hyC (Subgroup.zpowers_le.mpr hbC hy_mem)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxC, hxZ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨b, hbC, hbval⟩ := Subgroup.mem_map.mp hxC
  obtain ⟨zK, hzKc, hzKval⟩ := Subgroup.mem_map.mp hxZ
  have hxcent : x ∈ Subgroup.centralizer (K' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hzKc (⟨k, hk⟩ : ↥K'))
    have hc2 : (k : G) * (zK : G) = (zK : G) * (k : G) := by
      simpa only [Subgroup.coe_mul] using hc
    rw [show (zK : G) = x from hzKval] at hc2
    exact hc2
  have hbx : (b : G) ∈ Subgroup.centralizer (K' : Set G) := by
    rw [show (b : G) = x from hbval]
    exact hxcent
  have hmemZ : b ∈ Subgroup.zpowers ⟨y, hyB⟩ := by
    refine hfix b ?_
    intro φ hφ
    obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hg b]
    have hgx : g * (b : G) = (b : G) * g :=
      Subgroup.mem_centralizer_iff.mp hbx g hgK
    rw [hgx, mul_inv_cancel_right]
  have hb1 : b = 1 := hCy b hbC hmemZ
  rw [← hbval, hb1]
  rfl

end CFSG.StandardType

end
