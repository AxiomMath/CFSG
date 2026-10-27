module

public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T M L : Subgroup G}

open scoped Classical in
@[expose] noncomputable def commIndicator (x : G) : ZMod 2 := if x = 1 then 0 else 1

theorem commIndicator_one : commIndicator (1 : G) = 0 := by simp [commIndicator]

theorem commIndicator_eq_zero_iff {x : G} : commIndicator x = 0 ↔ x = 1 := by
  by_cases hx : x = 1
  · simp [commIndicator, hx]
  · simp [commIndicator, hx]

structure HatModel (T M : Subgroup G) where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod 2) V]
  [finite : Finite V]
  π : G → V
  B : LinearMap.BilinForm (ZMod 2) V
  π_mul : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, π (a * b) = π a + π b
  π_surj : ∀ v : V, ∃ u ∈ uOfL22 T M, π u = v
  π_eq_iff : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M,
    π a = π b ↔ a⁻¹ * b ∈ centerOf (uOfL22 T M)
  B_spec : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, B (π a) (π b) = 0 ↔ a * b * a⁻¹ * b⁻¹ = 1

attribute [instance] HatModel.addCommGroup HatModel.module HatModel.finite

namespace HatModel

variable (D : HatModel T M)

theorem π_one : D.π 1 = 0 := by
  have := D.π_mul 1 (uOfL22 T M).one_mem 1 (uOfL22 T M).one_mem
  simpa using this

theorem π_eq_zero_iff {a : G} (ha : a ∈ uOfL22 T M) : D.π a = 0 ↔ a ∈ centerOf (uOfL22 T M) := by
  rw [← D.π_one, D.π_eq_iff a ha 1 (uOfL22 T M).one_mem]
  simp

theorem B_isAlt (v : D.V) : D.B v v = 0 := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  exact (D.B_spec u hu u hu).mpr (by group)

theorem B_symm (v w : D.V) : D.B v w = D.B w v := by
  obtain ⟨a, ha, rfl⟩ := D.π_surj v
  obtain ⟨b, hb, rfl⟩ := D.π_surj w
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 ↔ b * a * b⁻¹ * a⁻¹ = 1 := by
    constructor
    · intro he
      have : a * b = b * a := by
        calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
          _ = b * a := by rw [he]; group
      calc b * a * b⁻¹ * a⁻¹ = (a * b) * b⁻¹ * a⁻¹ := by rw [this]
        _ = 1 := by group
    · intro he
      have : b * a = a * b := by
        calc b * a = (b * a * b⁻¹ * a⁻¹) * a * b := by group
          _ = a * b := by rw [he]; group
      calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [this]
        _ = 1 := by group
  have h2 : D.B (D.π a) (D.π b) = 0 ↔ D.B (D.π b) (D.π a) = 0 := by
    rw [D.B_spec a ha b hb, D.B_spec b hb a ha]
    exact h1
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases (D.B (D.π a) (D.π b)) with h3 | h3
  · rw [h3]
    exact (h2.mp h3).symm
  · rcases hcases (D.B (D.π b) (D.π a)) with h4 | h4
    · exact absurd (h2.mpr h4) (by rw [h3]; decide)
    · rw [h3, h4]

theorem B_nondegenerate (v : D.V) (hv : ∀ w, D.B v w = 0) : v = 0 := by
  obtain ⟨a, ha, rfl⟩ := D.π_surj v
  rw [D.π_eq_zero_iff ha]
  refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have h1 := (D.B_spec a ha u hu).mp (hv (D.π u))
  have h2 : a * u = u * a := by
    calc a * u = (a * u * a⁻¹ * u⁻¹) * u * a := by group
      _ = u * a := by rw [h1]; group
  exact h2.symm

def hat (A : Subgroup G) : Submodule (ZMod 2) D.V where
  carrier := {v | ∃ a ∈ A, a ∈ uOfL22 T M ∧ D.π a = v}
  add_mem' := by
    rintro _ _ ⟨a, haA, haU, rfl⟩ ⟨b, hbA, hbU, rfl⟩
    exact ⟨a * b, A.mul_mem haA hbA, (uOfL22 T M).mul_mem haU hbU, D.π_mul a haU b hbU⟩
  zero_mem' := ⟨1, A.one_mem, (uOfL22 T M).one_mem, D.π_one⟩
  smul_mem' := by
    intro c v hv
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]
      exact ⟨1, A.one_mem, (uOfL22 T M).one_mem, D.π_one⟩
    · rw [one_smul]
      exact hv

theorem mem_hat {A : Subgroup G} {v : D.V} :
    v ∈ D.hat A ↔ ∃ a ∈ A, a ∈ uOfL22 T M ∧ D.π a = v := Iff.rfl

theorem π_mem_hat {A : Subgroup G} {a : G} (haA : a ∈ A) (haU : a ∈ uOfL22 T M) :
    D.π a ∈ D.hat A := ⟨a, haA, haU, rfl⟩

theorem hat_mono {A A' : Subgroup G} (hAA' : A ≤ A') : D.hat A ≤ D.hat A' :=
  fun _ ⟨a, ha, haU, hv⟩ => ⟨a, hAA' ha, haU, hv⟩

end HatModel

private theorem hat_commutator_mul_mul {a b z z' : G}
    (hzb : z * b = b * z) (hz'a : z' * a = a * z') (hzz' : z * z' = z' * z) :
    ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have e1 : z * (b * z') * z⁻¹ = b * z' := by
    have : z * (b * z') = (b * z') * z := by
      rw [← mul_assoc, hzb, mul_assoc, hzz', ← mul_assoc]
    rw [this]
    group
  have e2 : z' * a⁻¹ * z'⁻¹ = a⁻¹ := by
    have : z' * a⁻¹ = a⁻¹ * z' := by
      have h1 : a * z' = z' * a := hz'a.symm
      calc z' * a⁻¹ = a⁻¹ * (a * z') * a⁻¹ := by group
        _ = a⁻¹ * (z' * a) * a⁻¹ := by rw [h1]
        _ = a⁻¹ * z' := by group
    rw [this]
    group
  calc ⁅a * z, b * z'⁆ = a * (z * (b * z') * z⁻¹) * a⁻¹ * z'⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = a * (b * z') * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [e1]
    _ = a * b * (z' * a⁻¹ * z'⁻¹) * b⁻¹ := by group
    _ = ⁅a, b⁆ := by
        rw [e2]
        simp only [commutatorElement_def]

namespace Hyp1281Two

variable [Finite G]

theorem exists_hatModel (h : Hyp1281Two G T M L) : Nonempty (HatModel T M) := by
  classical
  have hZuU : centerOf (uOfL22 T M) ≤ uOfL22 T M := inf_le_left
  have hV₁Zu : quasithinOmegaOneCenter T ≤ centerOf (uOfL22 T M) :=
    h.omegaOneCenter_le_centerOf_uOfL22
  have hZc : ∀ z ∈ centerOf (uOfL22 T M), ∀ u ∈ uOfL22 T M, u * z = z * u := fun z hz u hu =>
    Subgroup.mem_centralizer_iff.mp hz.2 u hu
  have hQS : QuotSetting (uOfL22 T M) (uOfL22 T M) (centerOf (uOfL22 T M)) :=
    { S₂_le := hZuU
      Sx_le := le_rfl
      nS := fun _ hx _ hy =>
        (uOfL22 T M).mul_mem ((uOfL22 T M).mul_mem hx hy) ((uOfL22 T M).inv_mem hx)
      nS₂ := fun _ hx y hy => (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hx)) y).mp hy
      abel := fun _ ha _ hb => hV₁Zu (h.commutator_mem_omegaOneCenter ha hb)
      sq := fun _ ha => hV₁Zu (by
        have := h.sq_mem_omegaOneCenter ha
        rwa [pow_two] at this) }
  have hN : ((centerOf (uOfL22 T M)).subgroupOf (uOfL22 T M)).Normal := hQS.normal
  let _ : CommGroup (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M))) := hQS.quotCommGroup
  let _ : Module (ZMod 2) (Additive (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M)))) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show (2 : ℕ) • x = 0
      rw [two_nsmul]
      exact Additive.toMul.injective (by simpa using hQS.quot_sq (Additive.toMul x)))
  have hmulL : ∀ a ∈ uOfL22 T M, ∀ a' ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M,
      ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
    intro a ha a' ha' b hb
    have e : ⁅a * a', b⁆ = (a * ⁅a', b⁆ * a⁻¹) * ⁅a, b⁆ := by
      simp only [commutatorElement_def]
      group
    have hc : ⁅a', b⁆ ∈ centerOf (uOfL22 T M) :=
      hV₁Zu (h.commutator_mem_omegaOneCenter ha' hb)
    have h2 : a * ⁅a', b⁆ * a⁻¹ = ⁅a', b⁆ := by
      have := hZc _ hc a ha
      calc a * ⁅a', b⁆ * a⁻¹ = (⁅a', b⁆ * a) * a⁻¹ := by rw [this]
        _ = ⁅a', b⁆ := by group
    rw [e, h2]
  have hmulR : ∀ a ∈ uOfL22 T M, ∀ b ∈ uOfL22 T M, ∀ b' ∈ uOfL22 T M,
      ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
    intro a ha b hb b' hb'
    have e : ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hc : ⁅a, b'⁆ ∈ centerOf (uOfL22 T M) :=
      hV₁Zu (h.commutator_mem_omegaOneCenter ha hb')
    have h2 : b * ⁅a, b'⁆ * b⁻¹ = ⁅a, b'⁆ := by
      have := hZc _ hc b hb
      calc b * ⁅a, b'⁆ * b⁻¹ = (⁅a, b'⁆ * b) * b⁻¹ := by rw [this]
        _ = ⁅a, b'⁆ := by group
    rw [e, h2]
  have hind : ∀ x ∈ quasithinOmegaOneCenter T, ∀ y ∈ quasithinOmegaOneCenter T,
      commIndicator (x * y) = commIndicator x + commIndicator y := by
    intro x hx y hy
    obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
    have hzz : z * z = 1 := by
      simpa [sq] using h.almostSpecialHyp_g1.sq_eq_one_of_mem_V (omegaOneCenter_le_VZ T M hzZ)
    have hz : commIndicator z = 1 := by simp [commIndicator, hz1]
    rcases hall x hx with hx1 | hx1 <;> rcases hall y hy with hy1 | hy1
    · rw [hx1, hy1]
      simp [commIndicator]
    · rw [hx1, hy1]
      simp [commIndicator]
    · rw [hx1, hy1]
      simp [commIndicator]
    · rw [hx1, hy1, hzz, hz, commIndicator_one]
      decide
  let rep : SecQuot (uOfL22 T M) (centerOf (uOfL22 T M)) → ↥(uOfL22 T M) :=
    Function.surjInv (secMk_surjective (A := uOfL22 T M) (B := centerOf (uOfL22 T M)))
  have hrep : ∀ q : SecQuot (uOfL22 T M) (centerOf (uOfL22 T M)),
      secMk (uOfL22 T M) (centerOf (uOfL22 T M)) (rep q) = q :=
    Function.surjInv_eq (secMk_surjective (A := uOfL22 T M) (B := centerOf (uOfL22 T M)))
  let f : Additive (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M))) →
      Additive (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M))) → ZMod 2 := fun x y =>
    commIndicator ⁅((rep (Additive.toMul x) : ↥(uOfL22 T M)) : G),
      ((rep (Additive.toMul y) : ↥(uOfL22 T M)) : G)⁆
  have key : ∀ (a' b' a b : ↥(uOfL22 T M)),
      secMk (uOfL22 T M) (centerOf (uOfL22 T M)) a' = secMk _ _ a →
      secMk (uOfL22 T M) (centerOf (uOfL22 T M)) b' = secMk _ _ b →
        ⁅(a' : G), (b' : G)⁆ = ⁅(a : G), (b : G)⁆ := by
    intro a' b' a b ha hb
    have ha1 := secMk_eq_secMk_iff.mp ha
    have hb1 := secMk_eq_secMk_iff.mp hb
    have := hat_commutator_mul_mul (a := (a' : G)) (b := (b' : G))
      (z := (a' : G)⁻¹ * a) (z' := (b' : G)⁻¹ * b)
      (hZc _ ha1 b' b'.2).symm (hZc _ hb1 a' a'.2).symm (hZc _ ha1 _ (hZuU hb1)).symm
    simpa using this.symm
  have hf : ∀ a b : ↥(uOfL22 T M),
      f (Additive.ofMul (secMk _ _ a)) (Additive.ofMul (secMk _ _ b)) =
        commIndicator ⁅(a : G), (b : G)⁆ := fun a b =>
    congrArg commIndicator (key _ _ a b (hrep _) (hrep _))
  have hsurj : ∀ x : Additive (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M))),
      ∃ a : ↥(uOfL22 T M), x = Additive.ofMul (secMk _ _ a) := fun x => by
    obtain ⟨a, ha⟩ := secMk_surjective (A := uOfL22 T M) (B := centerOf (uOfL22 T M))
      (Additive.toMul x)
    exact ⟨a, (congrArg Additive.ofMul ha).symm⟩
  have hadd : ∀ a a' : ↥(uOfL22 T M),
      Additive.ofMul (secMk (uOfL22 T M) (centerOf (uOfL22 T M)) a) +
        Additive.ofMul (secMk (uOfL22 T M) (centerOf (uOfL22 T M)) a') =
      Additive.ofMul (secMk (uOfL22 T M) (centerOf (uOfL22 T M)) (a * a')) := by
    intro a a'
    rw [map_mul, ofMul_mul]
  have hzero : (0 : Additive (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M)))) =
      Additive.ofMul (secMk (uOfL22 T M) (centerOf (uOfL22 T M)) 1) := by
    rw [map_one, ofMul_one]
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have H1 : ∀ x x' y, f (x + x') y = f x y + f x' y := by
    intro x x' y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨a', rfl⟩ := hsurj x'
    obtain ⟨b, rfl⟩ := hsurj y
    rw [hadd, hf, hf, hf]
    have e := hmulL a a.2 a' a'.2 b b.2
    have hm1 : ⁅(a' : G), (b : G)⁆ ∈ quasithinOmegaOneCenter T :=
      h.commutator_mem_omegaOneCenter a'.2 b.2
    have hm2 : ⁅(a : G), (b : G)⁆ ∈ quasithinOmegaOneCenter T :=
      h.commutator_mem_omegaOneCenter a.2 b.2
    show commIndicator ⁅((a : G) * a'), (b : G)⁆ = _
    rw [e, hind _ hm1 _ hm2, add_comm]
  have H3 : ∀ x y y', f x (y + y') = f x y + f x y' := by
    intro x y y'
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨b', rfl⟩ := hsurj y'
    rw [hadd, hf, hf, hf]
    have e := hmulR a a.2 b b.2 b' b'.2
    have hm1 : ⁅(a : G), (b : G)⁆ ∈ quasithinOmegaOneCenter T :=
      h.commutator_mem_omegaOneCenter a.2 b.2
    have hm2 : ⁅(a : G), (b' : G)⁆ ∈ quasithinOmegaOneCenter T :=
      h.commutator_mem_omegaOneCenter a.2 b'.2
    show commIndicator ⁅(a : G), ((b : G) * b')⁆ = _
    rw [e, hind _ hm1 _ hm2]
  have H2 : ∀ (c : ZMod 2) x y, f (c • x) y = c • f x y := by
    intro c x y
    rcases hc01 c with rfl | rfl
    · obtain ⟨b, rfl⟩ := hsurj y
      rw [zero_smul, zero_smul, hzero, hf]
      simp [commIndicator_one]
    · rw [one_smul, one_smul]
  have H4 : ∀ (c : ZMod 2) x y, f x (c • y) = c • f x y := by
    intro c x y
    rcases hc01 c with rfl | rfl
    · obtain ⟨a, rfl⟩ := hsurj x
      rw [zero_smul, zero_smul, hzero, hf]
      simp [commIndicator_one]
    · rw [one_smul, one_smul]
  refine ⟨{ V := Additive (SecQuot (uOfL22 T M) (centerOf (uOfL22 T M)))
            addCommGroup := inferInstance
            module := inferInstance
            finite := inferInstance
            π := fun x => if hx : x ∈ uOfL22 T M then Additive.ofMul (secMk _ _ ⟨x, hx⟩) else 0
            B := LinearMap.mk₂ (ZMod 2) f H1 H2 H3 H4
            π_mul := ?_
            π_surj := ?_
            π_eq_iff := ?_
            B_spec := ?_ }⟩
  · intro a ha b hb
    have hab := (uOfL22 T M).mul_mem ha hb
    simp only [ha, hb, hab, ↓reduceDIte]
    exact (hadd ⟨a, ha⟩ ⟨b, hb⟩).symm
  · intro v
    obtain ⟨u, rfl⟩ := hsurj v
    exact ⟨u, u.2, by simp only [u.2, ↓reduceDIte]⟩
  · intro a ha b hb
    simp only [ha, hb, ↓reduceDIte]
    rw [Equiv.apply_eq_iff_eq, secMk_eq_secMk_iff]
  · intro a ha b hb
    simp only [ha, hb, ↓reduceDIte]
    rw [LinearMap.mk₂_apply, hf, commIndicator_eq_zero_iff]
    simp only [commutatorElement_def]

end Hyp1281Two

end CFSG.Quasithin
