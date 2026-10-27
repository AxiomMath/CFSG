module

public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.GroupTheory.InternalSemidirectEquiv
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.WordPresentation
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIsoBase
public import CFSG.GroupTheory.SuzukiTwoGroupsQuadratic

public section

namespace CFSG.Quasithin.St84

open Subgroup Module
open scoped commutatorElement BigOperators

variable {G : Type*} [Group G]

theorem exists_centralizer_complement [Finite G] {P Q : Subgroup G} {k : G}
    (hQP : Q ≤ P) (hQn : P ≤ Subgroup.normalizer (Q : Set G))
    (hQ2 : IsPGroup 2 Q) (hkP : k ∈ P) (hk3 : orderOf k = 3)
    (hcomm : ∀ x ∈ P, k * x * k⁻¹ * x⁻¹ ∈ Q) :
    ∀ x ∈ P, ∃ q ∈ Q, ∃ a ∈ P ⊓ Subgroup.centralizer ({k} : Set G), x = q * a := by
  classical
  let K : Subgroup G := Subgroup.zpowers k
  have hKP : K ≤ P := Subgroup.zpowers_le.mpr hkP
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := hKP.trans hQn
  have hKPn : K ≤ Subgroup.normalizer (P : Set G) := hKP.trans (Subgroup.le_normalizer)
  have hKcard : Nat.card ↥K = 3 := by
    rw [show Nat.card ↥K = orderOf k from Nat.card_zpowers k, hk3]
  have hKp : IsPGroup 3 ↥K := IsPGroup.of_card (n := 1) (by simpa using hKcard)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  let ρ : ↥K →* MulAut ↥P := CFSG.GroupTheory.conjHom P K hKPn
  let R : Subgroup ↥P := Q.subgroupOf P
  have hRn : R.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQn
  have hRcard : Nat.card R = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
  have hp : ¬ 3 ∣ Nat.card R := by
    rw [hRcard]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hQ2 Nat.prime_three (by norm_num)
  have hR : ∀ b : ↥K, ∀ r ∈ R, ρ b r ∈ R := by
    intro b r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    have hbP : (b : G) ∈ P := hKP b.2
    have h := (Subgroup.mem_normalizer_iff.mp (hQn hbP) (r : G)).mp hr
    rw [CFSG.GroupTheory.conjHom_apply]
    exact h
  intro x hxP
  let xP : ↥P := ⟨x, hxP⟩
  have hxcos : ∀ b : ↥K, ρ b xP * xP⁻¹ ∈ R := by
    intro b
    let S : Subgroup ↥K :=
      { carrier := {b : ↥K | ρ b xP * xP⁻¹ ∈ R}
        one_mem' := by
          show ρ 1 xP * xP⁻¹ ∈ R
          rw [show ρ 1 xP = xP by simp, mul_inv_cancel]
          exact R.one_mem
        mul_mem' := by
          intro b c hb hc
          change ρ (b * c) xP * xP⁻¹ ∈ R
          have hbc : ρ (b * c) xP * xP⁻¹ = ρ b (ρ c xP * xP⁻¹) * (ρ b xP * xP⁻¹) := by
            simp [map_mul, map_inv, MulAut.mul_apply, mul_inv_rev]
          rw [hbc]
          exact R.mul_mem (hR b _ hc) hb
        inv_mem' := by
          intro b hb
          change ρ b⁻¹ xP * xP⁻¹ ∈ R
          have h2 : ρ b (ρ b⁻¹ xP * xP⁻¹) ∈ R := by
            have h1 : ρ b (ρ b⁻¹ xP * xP⁻¹) = (ρ b xP * xP⁻¹)⁻¹ := by
              simp [map_mul, map_inv, MulAut.mul_apply, mul_inv_rev]
            rw [h1]
            exact R.inv_mem hb
          have h3 : ρ b⁻¹ (ρ b (ρ b⁻¹ xP * xP⁻¹)) = ρ b⁻¹ xP * xP⁻¹ := by simp
          rw [← h3]
          exact hR b⁻¹ _ h2 }
    have hkS : (⟨k, Subgroup.mem_zpowers k⟩ : ↥K) ∈ S := by
      show ρ ⟨k, Subgroup.mem_zpowers k⟩ xP * xP⁻¹ ∈ R
      rw [Subgroup.mem_subgroupOf]
      have hv : ((ρ ⟨k, Subgroup.mem_zpowers k⟩ xP * xP⁻¹ : ↥P) : G) =
          k * x * k⁻¹ * x⁻¹ := by
        rw [Subgroup.coe_mul, CFSG.GroupTheory.conjHom_apply]
        rfl
      rw [hv]
      exact hcomm x hxP
    have htop : S = ⊤ := by
      apply eq_top_iff.mpr
      intro b _
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp b.2
      have hb : b = (⟨k, Subgroup.mem_zpowers k⟩ : ↥K) ^ z := by
        apply Subtype.ext
        exact hz.symm
      rw [hb]
      exact Subgroup.zpow_mem _ hkS z
    have hbS : b ∈ S := by
      rw [htop]
      exact Subgroup.mem_top b
    simpa [S] using hbS
  obtain ⟨yP, hyx, hyfix⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset.exists_fixed
      (p := 3) hKp ρ R hRn hR hp xP hxcos
  refine ⟨((yP * xP⁻¹ : ↥P) : G)⁻¹, Q.inv_mem (Subgroup.mem_subgroupOf.mp hyx),
    ⟨(yP : G), ⟨yP.2, ?_⟩, ?_⟩⟩
  · show (yP : G) ∈ Subgroup.centralizer ({k} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hyfix ⟨k, Subgroup.mem_zpowers k⟩
    have hv : ((ρ ⟨k, Subgroup.mem_zpowers k⟩ yP : ↥P) : G) = k * (yP : G) * k⁻¹ := by
      rw [CFSG.GroupTheory.conjHom_apply]
    have h' : k * (yP : G) * k⁻¹ = (yP : G) := by
      rw [← hv, h]
    calc (yP : G) * k = (k * (yP : G) * k⁻¹) * k := by rw [h']
      _ = k * (yP : G) := by group
  · have hz : ((yP * xP⁻¹ : ↥P) : G) = (yP : G) * x⁻¹ := rfl
    rw [hz]
    group

theorem centralizer_eq_bot_of_fpf {Q Z : Subgroup G} {k : G}
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    (hZ : ∀ z ∈ Z, k * z * k⁻¹ = z → z = 1)
    (hQZ : ∀ x ∈ Q, k * x * k⁻¹ * x⁻¹ ∈ Z → x ∈ Z) :
    Q ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxQ, hxC⟩ := hx
  have hfix : k * x * k⁻¹ = x := by
    have hcomm : x * k = k * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    calc k * x * k⁻¹ = (x * k) * k⁻¹ := by rw [hcomm]
      _ = x := by group
  have hxZ : x ∈ Z := hQZ x hxQ (by rw [hfix, mul_inv_cancel]; exact Z.one_mem)
  have hx1 : x = 1 := hZ x hxZ hfix
  rw [Subgroup.mem_bot]
  exact hx1

theorem exists_mul_mem_centralizer_of_acts_trivially [Finite G] {Q Z : Subgroup G} {k : G}
    (hZQ : Z ≤ Q) (hQ2 : IsPGroup 2 Q) (hk3 : orderOf k = 3)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    (hkZ : k ∈ Subgroup.normalizer (Z : Set G))
    (hZn : ∀ q ∈ Q, ∀ z ∈ Z, q * z * q⁻¹ ∈ Z)
    (htriv : ∀ x ∈ Q, k * x * k⁻¹ * x⁻¹ ∈ Z) :
    ∀ x ∈ Q, ∃ z ∈ Z, ∃ a ∈ Q ⊓ Subgroup.centralizer ({k} : Set G), x = z * a := by
  classical
  let K : Subgroup G := Subgroup.zpowers k
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hkQ
  have hKcard : Nat.card ↥K = 3 := by
    rw [show Nat.card ↥K = orderOf k from Nat.card_zpowers k, hk3]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have hKp : IsPGroup 3 ↥K := IsPGroup.of_card (n := 1) (by simpa using hKcard)
  let Q' := ↥Q
  let R : Subgroup Q' := Z.subgroupOf Q
  have hRn : R.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hZn g g.2 n hn
  let ρ : ↥K →* MulAut Q' := CFSG.GroupTheory.conjHom Q K hKQ
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) := Subgroup.zpowers_le.mpr hkZ
  have hRinv : ∀ b : ↥K, ∀ r ∈ R, ρ b r ∈ R := by
    intro b r hr
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    have hb : (b : G) ∈ Subgroup.normalizer (Z : Set G) := hKZ b.2
    have h := (Subgroup.mem_normalizer_iff.mp hb (r : G)).mp hr
    rw [CFSG.GroupTheory.conjHom_apply]
    exact h
  have hRstable : ∀ b : ↥K, ∀ y : Q', ρ b y * y⁻¹ ∈ R := by
    intro b y
    let S : Subgroup ↥K :=
      { carrier := {b : ↥K | ρ b y * y⁻¹ ∈ R}
        one_mem' := by
          show ρ 1 y * y⁻¹ ∈ R
          rw [show ρ 1 y = y by simp, mul_inv_cancel]
          exact R.one_mem
        mul_mem' := by
          intro b c hb hc
          change ρ (b * c) y * y⁻¹ ∈ R
          have hbc : ρ (b * c) y * y⁻¹ =
              ρ b (ρ c y * y⁻¹) * (ρ b y * y⁻¹) := by
            rw [map_mul, MulAut.mul_apply, map_mul, map_inv (ρ b) y]
            group
          rw [hbc]
          exact R.mul_mem (hRinv b _ hc) hb
        inv_mem' := by
          intro b hb
          change ρ b⁻¹ y * y⁻¹ ∈ R
          have h2 : ρ b (ρ b⁻¹ y * y⁻¹) ∈ R := by
            have h1 : ρ b (ρ b⁻¹ y * y⁻¹) = (ρ b y * y⁻¹)⁻¹ := by
              have hρ : (ρ b) * (ρ b)⁻¹ = 1 := mul_inv_cancel (ρ b)
              have hb' : ρ b⁻¹ = (ρ b)⁻¹ := map_inv ρ b
              have hy : (ρ b) (y⁻¹) = ((ρ b) y)⁻¹ := map_inv (ρ b) y
              rw [map_mul, hy, hb', ← MulAut.mul_apply, hρ, MulAut.one_apply]
              rw [mul_inv_rev, inv_inv]
            rw [h1]
            exact R.inv_mem hb
          have h3 : ρ b⁻¹ (ρ b (ρ b⁻¹ y * y⁻¹)) = ρ b⁻¹ y * y⁻¹ := by simp
          rw [← h3]
          exact hRinv b⁻¹ _ h2 }
    have hkS : (⟨k, Subgroup.mem_zpowers k⟩ : ↥K) ∈ S := by
      show ρ ⟨k, Subgroup.mem_zpowers k⟩ y * y⁻¹ ∈ R
      rw [Subgroup.mem_subgroupOf]
      have hv : ((ρ ⟨k, Subgroup.mem_zpowers k⟩ y * y⁻¹ : Q') : G) =
          k * (y : G) * k⁻¹ * (y : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, CFSG.GroupTheory.conjHom_apply]
      rw [hv]
      exact htriv y y.2
    have htop : S = ⊤ := by
      apply eq_top_iff.mpr
      intro c _
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp c.2
      have hc : c = (⟨k, Subgroup.mem_zpowers k⟩ : ↥K) ^ z := by
        apply Subtype.ext
        exact hz.symm
      rw [hc]
      exact Subgroup.zpow_mem _ hkS z
    have hbS : b ∈ S := by
      rw [htop]
      exact Subgroup.mem_top b
    simpa [S] using hbS
  intro x hxQ
  let x' : Q' := ⟨x, hxQ⟩
  have heq : ∀ b : ↥K, ∀ y : Q', QuotientGroup.mk' R (ρ b y) = QuotientGroup.mk' R y := by
    intro b y
    exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hRstable b y)
  have hcop : ¬ 3 ∣ Nat.card Q' :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hQ2 Nat.prime_three (by norm_num)
  obtain ⟨y, hyquot, hyfix⟩ :=
    CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_coprime
      (prime := 3) hKp ρ (1 : ↥K →* MulAut (Q' ⧸ R)) (QuotientGroup.mk' R)
      (QuotientGroup.mk'_surjective R) hcop (fun b y => by simpa using heq b y)
      (QuotientGroup.mk' R x') (fun b => rfl)
  have hzR : y * x'⁻¹ ∈ R := by
    simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hyquot
  refine ⟨(((y * x'⁻¹ : Q') : G))⁻¹, Z.inv_mem (Subgroup.mem_subgroupOf.mp hzR),
    ⟨(y : G), ⟨y.2, ?_⟩, ?_⟩⟩
  · show (y : G) ∈ Subgroup.centralizer ({k} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hyfix ⟨k, Subgroup.mem_zpowers k⟩
    have hv : ((ρ ⟨k, Subgroup.mem_zpowers k⟩ y : Q') : G) = k * (y : G) * k⁻¹ := by
      rw [CFSG.GroupTheory.conjHom_apply]
    have h' : k * (y : G) * k⁻¹ = (y : G) := by
      rw [← hv, h]
    calc (y : G) * k = (k * (y : G) * k⁻¹) * k := by rw [h']
      _ = k * (y : G) := by group
  · have hz : ((y * x'⁻¹ : Q') : G) = (y : G) * x⁻¹ := rfl
    rw [hz]
    group

theorem sq_mul_of_central {Z : Subgroup G} {x y : G}
    (hZ : ∀ z ∈ Z, ∀ g : G, g * z = z * g)
    (hx : x ^ 2 ∈ Z) (hy : y ^ 2 ∈ Z) (hc : ⁅y, x⁆ ∈ Z) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅y, x⁆ := by
  have hcomm : Commute x ⁅y, x⁆ := hZ _ hc x
  have hx' : Commute (⁅y, x⁆) (x ^ 2) := (hZ _ hc (x ^ 2)).symm
  have hy' : Commute (⁅y, x⁆) (y ^ 2) := (hZ _ hc (y ^ 2)).symm
  rw [CFSG.GroupTheory.SuzukiTwoGroup.mul_sq_of_commute hcomm]
  calc ⁅y, x⁆ * x ^ 2 * y ^ 2 = x ^ 2 * ⁅y, x⁆ * y ^ 2 := by rw [hx']
    _ = x ^ 2 * y ^ 2 * ⁅y, x⁆ := by rw [mul_assoc, hy', ← mul_assoc]

section Squaring

variable {Q : Type*} [Group Q] (Z : Subgroup Q)

@[expose] noncomputable def squaringMap (hZc : Z ≤ Subgroup.center Q) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hsq : ∀ x : Q, x ^ 2 ∈ Z) : Q ⧸ Z → Z :=
  fun v =>
    Quotient.liftOn' v (fun x => (⟨x ^ 2, hsq x⟩ : Z)) fun a b h => by
      have h' : a⁻¹ * b ∈ Z := QuotientGroup.leftRel_apply.mp h
      apply Subtype.ext
      change a ^ 2 = b ^ 2
      have hz : a⁻¹ * b ∈ Subgroup.center Q := hZc h'
      have hz2 : (a⁻¹ * b) ^ 2 = 1 := hZ2 _ h'
      have hcomm : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.mp hz a
      have hb : b = a * (a⁻¹ * b) := by group
      rw [hb, hcomm.mul_pow, hz2, mul_one]

@[simp] theorem squaringMap_mk (hZc : Z ≤ Subgroup.center Q) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hsq : ∀ x : Q, x ^ 2 ∈ Z) (x : Q) :
    squaringMap Z hZc hZ2 hsq (x : Q ⧸ Z) = ⟨x ^ 2, hsq x⟩ := by
  rw [squaringMap, Quotient.liftOn'_mk]

end Squaring

variable {ι κ : Type*} {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]

variable [Fintype ι] [DecidableEq ι]

noncomputable def pcIso {m n : ℕ} {ws : List (List (Fin m × Bool))} {Q : Type*} [Group Q]
    (h : Finite (CFSG.CosetTable.PG m ws) ∧ Nat.card (CFSG.CosetTable.PG m ws) ≤ n) (f : Fin m → Q)
    (hf : ∀ w ∈ ws, CFSG.Certificates.signedProd f w = 1)
    (hgen : Subgroup.closure (Set.range f) = ⊤) (hcard : Nat.card Q = n) :
    CFSG.CosetTable.PG m ws ≃* Q :=
  Classical.choose
    (CFSG.Quasithin.Fan86.exists_mulEquiv_presented
      (rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) (N := n) (g := f)
      (by
        intro r hr
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        rw [CFSG.Certificates.lift_mk_eq_signedProd]
        exact hf w hw)
      hgen h.1 h.2 hcard)

theorem pcIso_of {m n : ℕ} {ws : List (List (Fin m × Bool))} {Q : Type*} [Group Q]
    (h : Finite (CFSG.CosetTable.PG m ws) ∧ Nat.card (CFSG.CosetTable.PG m ws) ≤ n) (f : Fin m → Q)
    (hf : ∀ w ∈ ws, CFSG.Certificates.signedProd f w = 1)
    (hgen : Subgroup.closure (Set.range f) = ⊤) (hcard : Nat.card Q = n) (j : Fin m) :
    pcIso h f hf hgen hcard (PresentedGroup.of j) = f j := by
  unfold pcIso
  exact (Classical.choose_spec
    (CFSG.Quasithin.Fan86.exists_mulEquiv_presented
      (rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) (N := n) (g := f)
      (by
        intro r hr
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
        rw [CFSG.Certificates.lift_mk_eq_signedProd]
        exact hf w hw)
      hgen h.1 h.2 hcard)) j

theorem equivariant_of_gens {A A' V V' : Type*} [Group A] [Group A'] [Group V] [Group V']
    (φ : A →* MulAut V) (φ' : A' →* MulAut V') (β : V →* V') (α : A →* A')
    {sA : Set A} (hA : Subgroup.closure sA = ⊤) {sV : Set V}
    (hV : Subgroup.closure sV = ⊤)
    (h : ∀ a ∈ sA, ∀ v ∈ sV, β (φ a v) = φ' (α a) (β v)) :
    ∀ a v, β (φ a v) = φ' (α a) (β v) := by
  let Good : Subgroup A :=
    { carrier := {a | ∀ v, β (φ a v) = φ' (α a) (β v)}
      one_mem' := by
        intro v
        simp
      mul_mem' := by
        intro a b ha hb v
        rw [map_mul φ a b, map_mul α a b, map_mul φ' (α a) (α b)]
        simp only [MulAut.mul_apply]
        rw [ha (φ b v), hb v]
      inv_mem' := by
        intro a ha v
        have h1 := ha ((φ a)⁻¹ v)
        simp only [MulAut.inv_apply, inv_mul_cancel, MulAut.one_apply] at h1
        have h2 : β ((φ a)⁻¹ v) = (φ' (α a))⁻¹ (β v) := by
          have := congrArg (fun w => (φ' (α a))⁻¹ w) h1
          simpa using this.symm
        rw [map_inv φ a, map_inv α a, map_inv φ' (α a)]
        exact h2 }
  have hsA : sA ⊆ Good := by
    intro a ha
    let f : V →* V' :=
      { toFun := fun v => β (φ a v)
        map_one' := by simp
        map_mul' := by
          intro v w
          simp only [map_mul, MulAut.mul_apply] }
    let g : V →* V' :=
      { toFun := fun v => φ' (α a) (β v)
        map_one' := by simp
        map_mul' := by
          intro v w
          simp only [map_mul, MulAut.mul_apply] }
    have hfg : f = g := MonoidHom.eq_of_eqOn_dense hV fun v hv => h a ha v hv
    intro v
    exact congrArg (fun f : V →* V' => f v) hfg
  have htop : Good = ⊤ := by
    rw [eq_top_iff, ← hA]
    exact (Subgroup.closure_le Good).mpr hsA
  intro a v
  have ha : a ∈ Good := by
    rw [htop]
    exact Subgroup.mem_top a
  exact ha v

end CFSG.Quasithin.St84
