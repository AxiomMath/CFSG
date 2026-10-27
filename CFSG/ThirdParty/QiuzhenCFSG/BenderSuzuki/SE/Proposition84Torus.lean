module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.BenderSuzuki

open scoped IsMulCommutative

open PFAppendixIII PFchapter1section1

universe u v

public theorem invertedTorus_lift_of_central_odd_kernel
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) [Z.Normal]
    (hZcenter : Z ≤ Subgroup.center G)
    (hZodd : Odd (Nat.card Z))
    (t : G)
    (T : Subgroup (G ⧸ Z))
    (hTcyclic : IsCyclic T)
    (hTinverted : ∀ x : G ⧸ Z, x ∈ T →
      rightConjugateElem x (QuotientGroup.mk' Z t) = x⁻¹) :
    ∃ J : Subgroup G,
      (J : Set G) =
          {x : G | QuotientGroup.mk' Z x ∈ T ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic J ∧ Nat.card J = Nat.card T := by
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  let P : Subgroup G := T.comap q
  let f : P →* T :=
    { toFun := fun x ↦ ⟨q (x : G), x.property⟩
      map_one' := by ext; exact map_one q
      map_mul' := by
        intro x y
        ext
        exact map_mul q (x : G) (y : G) }
  letI : IsCyclic T := hTcyclic
  have hfker : f.ker ≤ Subgroup.center P := by
    intro x hx
    have hxq : q (x : G) = 1 := by
      exact congrArg Subtype.val (show f x = 1 from hx)
    have hxZ : (x : G) ∈ Z := (QuotientGroup.eq_one_iff (x : G)).mp hxq
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hZcenter hxZ) y
  letI : IsMulCommutative P :=
    ⟨Std.Commutative.mk (commutative_of_cyclic_center_quotient f hfker)⟩
  letI : CommGroup P := IsMulCommutative.instCommGroup
  let J : Subgroup G :=
    { carrier := {x : G | q x ∈ T ∧ rightConjugateElem x t = x⁻¹}
      one_mem' := by simp [rightConjugateElem]
      mul_mem' := by
        intro x y hx hy
        constructor
        · simpa only [map_mul] using T.mul_mem hx.1 hy.1
        · let xp : P := ⟨x, hx.1⟩
          let yp : P := ⟨y, hy.1⟩
          have hcomm : x * y = y * x := by
            exact congrArg Subtype.val (mul_comm xp yp)
          have hcommInv : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
            exact congrArg Subtype.val (mul_comm xp⁻¹ yp⁻¹)
          have hxanti : t⁻¹ * x * t = x⁻¹ := by
            exact hx.2
          have hyanti : t⁻¹ * y * t = y⁻¹ := by
            exact hy.2
          change t⁻¹ * (x * y) * t = (x * y)⁻¹
          calc
            t⁻¹ * (x * y) * t =
                (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
            _ = x⁻¹ * y⁻¹ := by rw [hxanti, hyanti]
            _ = y⁻¹ * x⁻¹ := hcommInv
            _ = (x * y)⁻¹ := (mul_inv_rev x y).symm
      inv_mem' := by
        intro x hx
        constructor
        · simpa only [map_inv] using T.inv_mem hx.1
        · change t⁻¹ * x⁻¹ * t = (x⁻¹)⁻¹
          calc
            t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
            _ = (x⁻¹)⁻¹ := congrArg Inv.inv hx.2 }
  let fJ : J →* T :=
    { toFun := fun x ↦ ⟨q (x : G), x.property.1⟩
      map_one' := by ext; exact map_one q
      map_mul' := by
        intro x y
        ext
        exact map_mul q (x : G) (y : G) }
  have hfJ_bijective : Function.Bijective fJ := by
    constructor
    · intro a b hab
      have habq : q (a : G) = q (b : G) :=
        congrArg Subtype.val hab
      let kG : G := (a : G)⁻¹ * (b : G)
      have hkq : q kG = 1 := by
        dsimp [kG]
        rw [map_mul, map_inv, habq]
        simp
      have hkZ : kG ∈ Z :=
        (QuotientGroup.eq_one_iff kG).mp hkq
      let k : Z := ⟨kG, hkZ⟩
      have hkcenter : kG ∈ Subgroup.center G := hZcenter hkZ
      have hkt : t⁻¹ * kG * t = kG := by
        have hcomm : kG * t = t * kG :=
          (Subgroup.mem_center_iff.mp hkcenter t).symm
        calc
          t⁻¹ * kG * t = t⁻¹ * (kG * t) := by rw [mul_assoc]
          _ = t⁻¹ * (t * kG) := by rw [hcomm]
          _ = kG := by simp
      have habval : (b : G) = (a : G) * kG := by
        dsimp [kG]
        group
      have haanti : t⁻¹ * (a : G) * t = (a : G)⁻¹ :=
        a.property.2
      have hbanti : t⁻¹ * (b : G) * t = (b : G)⁻¹ :=
        b.property.2
      have heq : (a : G)⁻¹ * kG = kG⁻¹ * (a : G)⁻¹ := by
        calc
          (a : G)⁻¹ * kG =
              (t⁻¹ * (a : G) * t) * (t⁻¹ * kG * t) := by
                rw [haanti, hkt]
          _ = t⁻¹ * ((a : G) * kG) * t := by group
          _ = t⁻¹ * (b : G) * t := by rw [← habval]
          _ = (b : G)⁻¹ := hbanti
          _ = ((a : G) * kG)⁻¹ := by rw [← habval]
          _ = kG⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
      have hkInvCenter : kG⁻¹ ∈ Subgroup.center G :=
        (Subgroup.center G).inv_mem hkcenter
      have hcommInv : kG⁻¹ * (a : G) = (a : G) * kG⁻¹ :=
        (Subgroup.mem_center_iff.mp hkInvCenter (a : G)).symm
      have hk_eq_inv : kG = kG⁻¹ := by
        calc
          kG = (a : G) * ((a : G)⁻¹ * kG) := by simp
          _ = (a : G) * (kG⁻¹ * (a : G)⁻¹) := by rw [heq]
          _ = ((a : G) * kG⁻¹) * (a : G)⁻¹ := by rw [mul_assoc]
          _ = (kG⁻¹ * (a : G)) * (a : G)⁻¹ := by rw [← hcommInv]
          _ = kG⁻¹ := by simp
      have hksq : k ^ 2 = 1 := by
        apply Subtype.ext
        change kG ^ 2 = 1
        rw [pow_two]
        nth_rw 1 [hk_eq_inv]
        simp
      have hkone : k = 1 := by
        apply hZodd.coprime_two_right.pow_left_bijective.injective
        simpa using hksq
      apply Subtype.ext
      rw [habval]
      have hkGone : kG = 1 := congrArg Subtype.val hkone
      rw [hkGone, mul_one]
    · intro y
      obtain ⟨x, hxq⟩ :=
        QuotientGroup.mk'_surjective Z (y : G ⧸ Z)
      have hxT : q x ∈ T := by
        rw [hxq]
        exact y.property
      let cG : G := rightConjugateElem x t * x
      have hcq : q cG = 1 := by
        have hyanti := hTinverted (y : G ⧸ Z) y.property
        dsimp [cG]
        rw [map_mul]
        have hconjmap :
            q (rightConjugateElem x t) =
              rightConjugateElem (q x) (q t) := by
          simp [rightConjugateElem]
        rw [hconjmap, hxq, hyanti]
        simp
      have hcZ : cG ∈ Z :=
        (QuotientGroup.eq_one_iff cG).mp hcq
      let c : Z := ⟨cG, hcZ⟩
      obtain ⟨k, hk⟩ :=
        hZodd.coprime_two_right.pow_left_bijective.surjective c⁻¹
      let kG : G := (k : G)
      have hkcenter : kG ∈ Subgroup.center G :=
        hZcenter k.property
      have hkt : t⁻¹ * kG * t = kG := by
        have hcomm : kG * t = t * kG :=
          (Subgroup.mem_center_iff.mp hkcenter t).symm
        calc
          t⁻¹ * kG * t = t⁻¹ * (kG * t) := by rw [mul_assoc]
          _ = t⁻¹ * (t * kG) := by rw [hcomm]
          _ = kG := by simp
      have hkval : kG ^ 2 = cG⁻¹ := by
        exact congrArg Subtype.val hk
      have hc_eq : cG = (kG ^ 2)⁻¹ := by
        have h := congrArg Inv.inv hkval
        simpa using h.symm
      have hck : cG * kG = kG⁻¹ := by
        rw [hc_eq]
        group
      have hconjx : t⁻¹ * x * t = cG * x⁻¹ := by
        calc
          t⁻¹ * x * t = (t⁻¹ * x * t * x) * x⁻¹ := by group
          _ = cG * x⁻¹ := by rfl
      have hcommInv : kG * x⁻¹ = x⁻¹ * kG :=
        (Subgroup.mem_center_iff.mp hkcenter x⁻¹).symm
      have hxkq : q (x * kG) = (y : G ⧸ Z) := by
        rw [map_mul, hxq]
        have hkqone : q kG = 1 :=
          (QuotientGroup.eq_one_iff kG).mpr k.property
        rw [hkqone, mul_one]
      have hxkanti :
          rightConjugateElem (x * kG) t = (x * kG)⁻¹ := by
        change t⁻¹ * (x * kG) * t = (x * kG)⁻¹
        calc
          t⁻¹ * (x * kG) * t =
              (t⁻¹ * x * t) * (t⁻¹ * kG * t) := by group
          _ = (cG * x⁻¹) * kG := by rw [hconjx, hkt]
          _ = cG * (x⁻¹ * kG) := by rw [mul_assoc]
          _ = cG * (kG * x⁻¹) := by rw [hcommInv]
          _ = (cG * kG) * x⁻¹ := (mul_assoc cG kG x⁻¹).symm
          _ = kG⁻¹ * x⁻¹ := by rw [hck]
          _ = (x * kG)⁻¹ := (mul_inv_rev _ _).symm
      let j : J := ⟨x * kG, ⟨by simpa [hxkq] using y.property, hxkanti⟩⟩
      refine ⟨j, ?_⟩
      apply Subtype.ext
      exact hxkq
  let e : J ≃* T := MulEquiv.ofBijective fJ hfJ_bijective
  refine ⟨J, rfl, e.isCyclic.mpr hTcyclic, ?_⟩
  exact Nat.card_congr e.toEquiv

public theorem invertedTorus_of_standard_pair
    {G : Type u} {Omega : Type*}
    [Group G] [Finite G] [MulAction G Omega]
    (B : Subgroup G) (t : G)
    (ht : IsInvolution t) (htB : t ∉ B)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hBpoint : ∃ alpha : Omega, B = MulAction.stabilizer G alpha)
    (alpha0 beta0 : Omega) (halpha0beta0 : alpha0 ≠ beta0)
    (w : G) (hwalpha : w • alpha0 = beta0)
    (hwbeta : w • beta0 = alpha0)
    (H0 T0 : Subgroup G)
    (hH0set : (H0 : Set G) =
      {x : G | x • alpha0 = alpha0 ∧ x • beta0 = beta0})
    (hH0comm : IsMulCommutative H0)
    (hT0set : (T0 : Set G) =
      {x : G | x ∈ H0 ∧ rightConjugateElem x w = x⁻¹})
    (hT0cyclic : IsCyclic T0) :
    ∃ T : Subgroup G,
      (T : Set G) =
          {x : G | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = Nat.card T0 := by
  have hmemH0 (x : G) :
      x ∈ H0 ↔ x • alpha0 = alpha0 ∧ x • beta0 = beta0 :=
    Set.ext_iff.mp hH0set x
  have hmemT0 (x : G) :
      x ∈ T0 ↔ x ∈ H0 ∧ rightConjugateElem x w = x⁻¹ :=
    Set.ext_iff.mp hT0set x
  rcases hBpoint with ⟨alpha, rfl⟩
  let beta : Omega := t • alpha
  have hbeta : beta ≠ alpha := by
    intro h
    apply htB
    rw [MulAction.mem_stabilizer_iff]
    exact h
  rw [MulAction.is_two_pretransitive_iff] at htwo
  obtain ⟨g, hgalpha, hgbeta⟩ :=
    htwo hbeta.symm halpha0beta0
  let c : MulAut G := MulAut.conj g
  let t0 : G := c t
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have ht0alpha : t0 • alpha0 = beta0 := by
    rw [← hgalpha, ← hgbeta]
    simp [t0, c, beta, MulAut.conj_apply, smul_smul, mul_assoc]
  have ht0beta : t0 • beta0 = alpha0 := by
    rw [← hgbeta, ← hgalpha]
    simp [t0, c, beta, MulAut.conj_apply, smul_smul, mul_assoc, htt]
  have hwInvAlpha : w⁻¹ • alpha0 = beta0 := by
    calc
      w⁻¹ • alpha0 = w⁻¹ • (w • beta0) := by rw [hwbeta]
      _ = beta0 := inv_smul_smul w beta0
  have hwInvBeta : w⁻¹ • beta0 = alpha0 := by
    calc
      w⁻¹ • beta0 = w⁻¹ • (w • alpha0) := by rw [hwalpha]
      _ = alpha0 := inv_smul_smul w alpha0
  let d : G := t0 * w⁻¹
  have hdH0 : d ∈ H0 := by
    rw [hmemH0]
    constructor
    · change (t0 * w⁻¹) • alpha0 = alpha0
      rw [mul_smul, hwInvAlpha, ht0beta]
    · change (t0 * w⁻¹) • beta0 = beta0
      rw [mul_smul, hwInvBeta, ht0alpha]
  letI : IsMulCommutative H0 := hH0comm
  have ht0_eq : t0 = d * w := by
    dsimp [d]
    group
  have hconjCompare : ∀ x : G, x ∈ H0 →
      rightConjugateElem x t0 = rightConjugateElem x w := by
    intro x hx
    have hdInvH0 : d⁻¹ ∈ H0 := H0.inv_mem hdH0
    have hcomm : d⁻¹ * x = x * d⁻¹ :=
      Subgroup.mul_comm_of_mem_isMulCommutative (H := H0) hdInvH0 hx
    change t0⁻¹ * x * t0 = w⁻¹ * x * w
    rw [ht0_eq]
    calc
      (d * w)⁻¹ * x * (d * w) =
          w⁻¹ * (d⁻¹ * x) * d * w := by group
      _ = w⁻¹ * (x * d⁻¹) * d * w := by rw [hcomm]
      _ = w⁻¹ * x * w := by group
  have hfixConj (x : G) (z : Omega) :
      (c x) • (g • z) = g • (x • z) := by
    simp [c, MulAut.conj_apply, smul_smul, mul_assoc]
  have hcH0iff (x : G) :
      c x ∈ H0 ↔
        x ∈ MulAction.stabilizer G alpha ∧
          x ∈ MulAction.stabilizer G beta := by
    rw [hmemH0]
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro hx
      constructor
      · have h := hx.1
        rw [← hgalpha] at h
        simpa [hfixConj] using h
      · have h := hx.2
        rw [← hgbeta] at h
        simpa [hfixConj] using h
    · rintro ⟨hxalpha, hxbeta⟩
      constructor
      · rw [← hgalpha, hfixConj, hxalpha]
      · rw [← hgbeta, hfixConj, hxbeta]
  have hantiTransport (x : G) :
      rightConjugateElem (c x) (c t) = (c x)⁻¹ ↔
        rightConjugateElem x t = x⁻¹ := by
    constructor
    · intro h
      apply c.injective
      calc
        c (rightConjugateElem x t) =
            rightConjugateElem (c x) (c t) := by
              simp [rightConjugateElem]
        _ = (c x)⁻¹ := h
        _ = c x⁻¹ := (map_inv c x).symm
    · intro h
      calc
        rightConjugateElem (c x) (c t) =
            c (rightConjugateElem x t) := by
              simp [rightConjugateElem]
        _ = c x⁻¹ := by rw [h]
        _ = (c x)⁻¹ := map_inv c x
  let T : Subgroup G := T0.map c.symm.toMonoidHom
  have hmemT (x : G) : x ∈ T ↔ c x ∈ T0 := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hycx : y = c x := by
        have h := congrArg c hyx
        simpa using h
      simpa [hycx] using hy
    · intro hx
      refine ⟨c x, hx, ?_⟩
      simp
  let e : T ≃* T0 :=
    { toFun := fun x ↦ ⟨c x, (hmemT (x : G)).mp x.property⟩
      invFun := fun y ↦ ⟨c.symm y, (hmemT (c.symm y)).mpr (by simpa)⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simpa using c.map_mul (x : G) (y : G) }
  refine ⟨T, ?_, e.isCyclic.mpr hT0cyclic, Nat.card_congr e.toEquiv⟩
  ext x
  change x ∈ T ↔
    x ∈ MulAction.stabilizer G alpha ∧
      x ∈ rightConjugate (MulAction.stabilizer G alpha) t ∧
        rightConjugateElem x t = x⁻¹
  rw [hmemT, hmemT0]
  have hanti_compare_of_H0 (x : G) (hxH0 : c x ∈ H0) :
      rightConjugateElem (c x) w = (c x)⁻¹ ↔
        rightConjugateElem x t = x⁻¹ := by
    rw [← hconjCompare (c x) hxH0]
    exact hantiTransport x
  rw [hcH0iff]
  rw [rightConjugate_stabilizer alpha t, ht.inv_eq_self]
  constructor
  · rintro ⟨hxstabs, hantiW⟩
    have hxH0 : c x ∈ H0 := (hcH0iff x).mpr hxstabs
    exact ⟨hxstabs.1, hxstabs.2,
      (hanti_compare_of_H0 x hxH0).mp hantiW⟩
  · rintro ⟨hxalpha, hxbeta, hantiT⟩
    have hxH0 : c x ∈ H0 :=
      (hcH0iff x).mpr ⟨hxalpha, hxbeta⟩
    exact ⟨⟨hxalpha, hxbeta⟩,
      (hanti_compare_of_H0 x hxH0).mpr hantiT⟩

/-- Transport a nontrivial element of the standard two-point stabilizer that
centralizes the standard Weyl involution to an arbitrary Borel and an outside
involution. -/
public theorem centralizer_borel_inter_rightConjugate_of_standard_pair
    {G : Type u} {Omega : Type*}
    [Group G] [Finite G] [MulAction G Omega]
    (B : Subgroup G) (t : G)
    (ht : IsInvolution t) (htB : t ∉ B)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hBpoint : ∃ alpha : Omega, B = MulAction.stabilizer G alpha)
    (alpha0 beta0 : Omega) (halpha0beta0 : alpha0 ≠ beta0)
    (w : G) (hwalpha : w • alpha0 = beta0)
    (hwbeta : w • beta0 = alpha0)
    (H0 : Subgroup G)
    (hH0set : (H0 : Set G) =
      {x : G | x • alpha0 = alpha0 ∧ x • beta0 = beta0})
    (hH0comm : IsMulCommutative H0)
    (z0 : G) (hz0H : z0 ∈ H0) (hz0ne : z0 ≠ 1)
    (hz0w : z0 * w = w * z0) :
    ∃ z : G, z ≠ 1 ∧ z ∈ B ∧ z ∈ rightConjugate B t ∧
      z ∈ Subgroup.centralizer ({t} : Set G) := by
  have hmemH0 (x : G) :
      x ∈ H0 ↔ x • alpha0 = alpha0 ∧ x • beta0 = beta0 :=
    Set.ext_iff.mp hH0set x
  rcases hBpoint with ⟨alpha, rfl⟩
  let beta : Omega := t • alpha
  have hbeta : beta ≠ alpha := by
    intro h
    apply htB
    rw [MulAction.mem_stabilizer_iff]
    exact h
  rw [MulAction.is_two_pretransitive_iff] at htwo
  obtain ⟨g, hgalpha, hgbeta⟩ :=
    htwo hbeta.symm halpha0beta0
  let c : MulAut G := MulAut.conj g
  let t0 : G := c t
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have ht0alpha : t0 • alpha0 = beta0 := by
    rw [← hgalpha, ← hgbeta]
    simp [t0, c, beta, MulAut.conj_apply, smul_smul, mul_assoc]
  have ht0beta : t0 • beta0 = alpha0 := by
    rw [← hgbeta, ← hgalpha]
    simp [t0, c, beta, MulAut.conj_apply, smul_smul, mul_assoc, htt]
  have hwInvAlpha : w⁻¹ • alpha0 = beta0 := by
    calc
      w⁻¹ • alpha0 = w⁻¹ • (w • beta0) := by rw [hwbeta]
      _ = beta0 := inv_smul_smul w beta0
  have hwInvBeta : w⁻¹ • beta0 = alpha0 := by
    calc
      w⁻¹ • beta0 = w⁻¹ • (w • alpha0) := by rw [hwalpha]
      _ = alpha0 := inv_smul_smul w alpha0
  let d : G := t0 * w⁻¹
  have hdH0 : d ∈ H0 := by
    rw [hmemH0]
    constructor
    · change (t0 * w⁻¹) • alpha0 = alpha0
      rw [mul_smul, hwInvAlpha, ht0beta]
    · change (t0 * w⁻¹) • beta0 = beta0
      rw [mul_smul, hwInvBeta, ht0alpha]
  letI : IsMulCommutative H0 := hH0comm
  have ht0_eq : t0 = d * w := by
    dsimp [d]
    group
  have hz0d : z0 * d = d * z0 :=
    Subgroup.mul_comm_of_mem_isMulCommutative H0 hz0H hdH0
  have hz0t0 : z0 * t0 = t0 * z0 := by
    rw [ht0_eq]
    calc
      z0 * (d * w) = (z0 * d) * w := (mul_assoc z0 d w).symm
      _ = (d * z0) * w := by rw [hz0d]
      _ = d * (z0 * w) := mul_assoc d z0 w
      _ = d * (w * z0) := by rw [hz0w]
      _ = (d * w) * z0 := (mul_assoc d w z0).symm
  have hfixConj (x : G) (z : Omega) :
      (c x) • (g • z) = g • (x • z) := by
    simp [c, MulAut.conj_apply, smul_smul, mul_assoc]
  have hcH0iff (x : G) :
      c x ∈ H0 ↔
        x ∈ MulAction.stabilizer G alpha ∧
          x ∈ MulAction.stabilizer G beta := by
    rw [hmemH0]
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro hx
      constructor
      · have h := hx.1
        rw [← hgalpha] at h
        simpa [hfixConj] using h
      · have h := hx.2
        rw [← hgbeta] at h
        simpa [hfixConj] using h
    · rintro ⟨hxalpha, hxbeta⟩
      constructor
      · rw [← hgalpha, hfixConj, hxalpha]
      · rw [← hgbeta, hfixConj, hxbeta]
  let z : G := c.symm z0
  have hcz : c z = z0 := by simp [z]
  have hzstabs : z ∈ MulAction.stabilizer G alpha ∧
      z ∈ MulAction.stabilizer G beta := by
    apply (hcH0iff z).mp
    simpa [hcz] using hz0H
  have hzne : z ≠ 1 := by
    intro hz
    apply hz0ne
    calc
      z0 = c z := hcz.symm
      _ = c 1 := by rw [hz]
      _ = 1 := map_one c
  have hzconj : z ∈ rightConjugate (MulAction.stabilizer G alpha) t := by
    rw [rightConjugate_stabilizer alpha t, ht.inv_eq_self]
    exact hzstabs.2
  have hzcomm : z * t = t * z := by
    apply c.injective
    simpa [hcz, t0] using hz0t0
  exact ⟨z, hzne, hzstabs.1, hzconj,
    Subgroup.mem_centralizer_singleton_iff.mpr hzcomm⟩

public theorem invertedTorus_pullback_mulEquiv
    {G : Type u} {Q : Type v}
    [Group G] [Finite G] [Group Q] [Finite Q]
    (e : G ≃* Q) (B : Subgroup G) (t : G)
    (TQ : Subgroup Q)
    (hTQset : (TQ : Set Q) =
      {x : Q | x ∈ B.map e.toMonoidHom ∧
        x ∈ rightConjugate (B.map e.toMonoidHom) (e t) ∧
        rightConjugateElem x (e t) = x⁻¹})
    (hTQcyclic : IsCyclic TQ) :
    ∃ T : Subgroup G,
      (T : Set G) =
          {x : G | x ∈ B ∧ x ∈ rightConjugate B t ∧
            rightConjugateElem x t = x⁻¹} ∧
        IsCyclic T ∧ Nat.card T = Nat.card TQ := by
  let T : Subgroup G := TQ.map e.symm.toMonoidHom
  have hmemT (x : G) : x ∈ T ↔ e x ∈ TQ := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hye : y = e x := by
        have h := congrArg e hyx
        simpa using h
      simpa [hye] using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  let eT : T ≃* TQ :=
    { toFun := fun x ↦ ⟨e x, (hmemT (x : G)).mp x.property⟩
      invFun := fun y ↦ ⟨e.symm y, (hmemT (e.symm y)).mpr (by simp)⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact e.map_mul (x : G) (y : G) }
  refine ⟨T, ?_, eT.isCyclic.mpr hTQcyclic, Nat.card_congr eT.toEquiv⟩
  ext x
  change x ∈ T ↔
    x ∈ B ∧ x ∈ rightConjugate B t ∧
      rightConjugateElem x t = x⁻¹
  rw [hmemT]
  rw [show e x ∈ TQ ↔
      e x ∈ B.map e.toMonoidHom ∧
        e x ∈ rightConjugate (B.map e.toMonoidHom) (e t) ∧
          rightConjugateElem (e x) (e t) = (e x)⁻¹ from
    Set.ext_iff.mp hTQset (e x)]
  have hright :
      e x ∈ rightConjugate (B.map e.toMonoidHom) (e t) ↔
        x ∈ rightConjugate B t := by
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, ha⟩
      refine ⟨b, hb, ?_⟩
      apply e.injective
      simpa using ha
    · rintro ⟨b, hb, hbtx⟩
      refine ⟨e b, Subgroup.mem_map_of_mem e.toMonoidHom hb, ?_⟩
      simpa using congrArg e hbtx
  have hanti :
      rightConjugateElem (e x) (e t) = (e x)⁻¹ ↔
        rightConjugateElem x t = x⁻¹ := by
    constructor
    · intro h
      apply e.injective
      simpa [rightConjugateElem] using h
    · intro h
      simpa [rightConjugateElem] using congrArg e h
  rw [hright, hanti]
  simp

end CFSG.BenderSuzuki
