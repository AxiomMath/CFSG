module

public import CFSG.LocalAnalysis.StandardType.GGL45TGSetting

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open GGL45TA (scalar_mem_center map_scalar scalar_injective semi semi_apply semi_semi
  semi_one_one semi_scalar ggL45TA_comm_mul_center_left ggL45TA_comm_mul_center_right
  ggL45TA_comm_mul_left ggL45TA_comm_mul_right)

variable {d : ℕ} {k : Type} [Field k] {K : Type} [Group K] {D : GData d k} {π : D.H →* K}

theorem SemilinImpl.mul {γ₁ γ₂ : MulAut K} {g₁ g₂ : GL (Fin d) k} {σ₁ σ₂ : k ≃+* k}
    (h₁ : SemilinImpl π γ₁ g₁ σ₁) (hg₂ : g₂ ∈ D.A) (h₂ : SemilinImpl π γ₂ g₂ σ₂) :
    SemilinImpl π (γ₁ * γ₂) (g₁ * Matrix.GeneralLinearGroup.map σ₁.toRingHom g₂) (σ₁ * σ₂) := by
  intro h h' hh'
  let m : D.H := ⟨semi g₂ σ₂ h, D.conj_mem g₂ hg₂ _ (D.map_mem σ₂ h h.2)⟩
  rw [MulAut.mul_apply, h₂ h m rfl]
  apply h₁ m h'
  change (h' : GL (Fin d) k) = semi g₁ σ₁ (semi g₂ σ₂ h)
  rw [semi_semi, hh']
  rfl

theorem SemilinImpl.inv {γ : MulAut K} {g : GL (Fin d) k} {σ : k ≃+* k}
    (hγ : SemilinImpl π γ g σ) :
    SemilinImpl π γ⁻¹ (Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom g⁻¹) σ⁻¹ := by
  intro h h' hh'
  have h1 : γ (π h') = π h := hγ h' h (by
    change (h : GL (Fin d) k) = semi g σ h'
    have hh'' : (h' : GL (Fin d) k) =
        semi (Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom g⁻¹) σ⁻¹ h := hh'
    rw [hh'', semi_semi, ← YS09Field.glMap_mul, mul_inv_cancel, YS09Field.glMap_one,
      mul_inv_cancel, semi_one_one])
  rw [← h1, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem SemilinImpl.implements {γ : MulAut K} {g : GL (Fin d) k}
    (hγ : SemilinImpl π γ g 1) : Implements π γ g := by
  intro h h' hh'
  apply hγ h h'
  rw [hh', YS09Field.glMap_one]

namespace GSetting

variable {p q₀ : ℕ} [Finite k] {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem dvd_card_sub_one (S : GSetting p q₀ d k D K ψ E) : p ∣ Nat.card k - 1 := by
  have h := S.card_units
  rw [Nat.card_units] at h
  have h3 : ((q₀ : ℤ) - 1) ∣ (q₀ : ℤ) ^ p - 1 := by
    simpa using sub_dvd_pow_sub_pow (q₀ : ℤ) 1 p
  exact Int.natCast_dvd_natCast.mp (h ▸ S.dvd_q₀.trans h3)

theorem tau_pow (S : GSetting p q₀ d k D K ψ E) : S.τ ^ p = 1 := by
  classical
  haveI := Fintype.ofFinite k
  have hiter : ∀ (j : ℕ) (a : k), (S.τ ^ j) a = a ^ q₀ ^ j := by
    intro j
    induction j with
    | zero => intro a; simp
    | succ j ih =>
      intro a
      rw [pow_succ', RingAut.mul_apply, ih, map_pow, S.τ_apply, ← pow_mul, ← pow_succ']
  ext a
  rw [hiter, ← S.card_k, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rfl

theorem units_map_eq (S : GSetting p q₀ d k D K ψ E) {σ : k ≃+* k} {m : ℕ} (hσ : σ ^ p ^ m = 1)
    {c : kˣ} (hc : c ^ p = 1) : Units.map σ.toRingHom.toMonoidHom c = c := by
  obtain ⟨ω, hω⟩ := TypeA.exists_isPrimitiveRoot S.hp S.dvd_card_sub_one
  apply Units.ext
  change σ (c : k) = c
  exact LinModel.fieldAut_fixes_root S.hp hω hσ (by rw [← Units.val_pow_eq_pow_val, hc,
    Units.val_one])

theorem inv_pow_eq_one {σ : k ≃+* k} {n : ℕ} (hσ : σ ^ n = 1) : σ⁻¹ ^ n = 1 := by
  rw [inv_pow, hσ, inv_one]

theorem semi_mem (g : GL (Fin d) k) (hg : g ∈ D.A) (σ : k ≃+* k) {y : GL (Fin d) k}
    (hy : y ∈ D.A) : semi g σ y ∈ D.A :=
  D.A.mul_mem (D.A.mul_mem hg (D.map_memA σ y hy)) (D.A.inv_mem hg)

theorem exists_semi_eq (S : GSetting p q₀ d k D K ψ E) {γ : MulAut K} {g : GL (Fin d) k}
    (hgA : g ∈ D.A) {σ : k ≃+* k} (hγ : SemilinImpl S.π γ g σ) {e' : MulAut K}
    (he' : γ * e' * γ⁻¹ = e') {y : GL (Fin d) k} (hyA : y ∈ D.A) (hy : y ^ p = 1)
    (hye : Implements S.π e' y) :
    ∃ c : kˣ, c ^ p = 1 ∧ semi g σ y = Matrix.GeneralLinearGroup.scalar (Fin d) c * y := by
  have h1 := hγ.conj hgA hyA hye
  rw [he'] at h1
  obtain ⟨c, hc⟩ := implements_unique S.ker_le (semi_mem g hgA σ hyA) hyA h1 hye
  have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩)
  have heq : semi g σ y = Matrix.GeneralLinearGroup.scalar (Fin d) c * y := by
    rw [semi_apply, ← hcen y, hc, mul_inv_cancel_left, semi_apply]
  refine ⟨c, ?_, heq⟩
  have hd1 : 1 ≤ d := le_trans (by norm_num) S.three_le
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) c) y := (hcen y).symm
  apply scalar_injective (k := k) hd1
  have h2 : (semi g σ y) ^ p = 1 := by rw [← map_pow, hy, map_one]
  rw [heq, hcomm.mul_pow, hy, mul_one] at h2
  rw [map_pow, h2, map_one]

theorem commute_of_mem_P (S : GSetting p q₀ d k D K ψ E) {γ : MulAut K} (hγp : GGL45IsPElt p γ)
    (hγE : ∀ e' ∈ E, γ * e' = e' * γ) {x : GL (Fin d) k} (hxA : x ∈ D.A)
    (hx : Implements S.π (γ * ψ⁻¹ * γ⁻¹ * ψ) x) {y : GL (Fin d) k} (hy : S.IsLift y) :
    x * y = y * x := by
  obtain ⟨hyA, hyp, e', he', hye⟩ := hy
  obtain ⟨g, hgA, σ, m, hσm, hγ⟩ := S.semilin γ hγp
  have hd1 : 1 ≤ d := le_trans (by norm_num) S.three_le
  set τ := S.τ
  have hψ : SemilinImpl S.π ψ 1 τ := S.ψ_impl
  have hg'A : Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom g⁻¹ ∈ D.A :=
    D.map_memA _ _ (D.A.inv_mem hgA)
  have h1A : Matrix.GeneralLinearGroup.map τ⁻¹.toRingHom 1⁻¹ ∈ D.A := by
    rw [inv_one, map_one]; exact D.A.one_mem
  have hcomp := ((hγ.mul h1A hψ.inv).mul hg'A hγ.inv).mul D.A.one_mem hψ
  have hsig : σ * τ⁻¹ * σ⁻¹ * τ = 1 := by
    rw [ringEquiv_mul_comm_of_finite σ τ⁻¹, mul_assoc τ⁻¹, mul_inv_cancel, mul_one,
      inv_mul_cancel]
  set W := g * Matrix.GeneralLinearGroup.map σ.toRingHom
      (Matrix.GeneralLinearGroup.map τ⁻¹.toRingHom 1⁻¹) *
      Matrix.GeneralLinearGroup.map (σ * τ⁻¹).toRingHom
        (Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom g⁻¹) *
      Matrix.GeneralLinearGroup.map (σ * τ⁻¹ * σ⁻¹).toRingHom 1 with hW
  have hWA : W ∈ D.A := by
    rw [hW]
    refine D.A.mul_mem (D.A.mul_mem (D.A.mul_mem hgA (D.map_memA _ _ h1A))
      (D.map_memA _ _ hg'A)) ?_
    rw [map_one]; exact D.A.one_mem
  have hfun : ∀ z, semi W (σ * τ⁻¹ * σ⁻¹ * τ) z = semi g σ
      (semi (Matrix.GeneralLinearGroup.map τ⁻¹.toRingHom 1⁻¹) τ⁻¹
        (semi (Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom g⁻¹) σ⁻¹ (semi 1 τ z))) := by
    intro z
    rw [hW, ← semi_semi, ← semi_semi, ← semi_semi]
  rw [hsig] at hcomp hfun
  have hWimpl : Implements S.π (γ * ψ⁻¹ * γ⁻¹ * ψ) W := hcomp.implements
  obtain ⟨s, hs⟩ := implements_unique S.ker_le hxA hWA hx hWimpl
  have hxW : x = W * Matrix.GeneralLinearGroup.scalar (Fin d) s := by
    rw [hs, mul_inv_cancel_left]
  have hconj : ∀ α : MulAut K, (∀ e ∈ E, α * e = e * α) → α * e' * α⁻¹ = e' := fun α hα => by
    rw [hα e' he', mul_inv_cancel_right]
  have hγinv : ∀ e ∈ E, γ⁻¹ * e = e * γ⁻¹ := fun e he => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hγE e he, mul_inv_cancel_right]
  have hψE : ∀ e ∈ E, ψ * e = e * ψ := fun e he => (S.comm e he).symm
  have hψinv : ∀ e ∈ E, ψ⁻¹ * e = e * ψ⁻¹ := fun e he => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hψE e he, mul_inv_cancel_right]
  obtain ⟨c₁, hc₁p, hc₁⟩ := S.exists_semi_eq D.A.one_mem hψ (hconj ψ hψE) hyA hyp hye
  obtain ⟨c₂, hc₂p, hc₂⟩ := S.exists_semi_eq hg'A hγ.inv (by
    have := hconj γ⁻¹ hγinv
    simpa using this) hyA hyp hye
  obtain ⟨c₃, hc₃p, hc₃⟩ := S.exists_semi_eq h1A hψ.inv (by
    have := hconj ψ⁻¹ hψinv
    simpa using this) hyA hyp hye
  obtain ⟨c₄, hc₄p, hc₄⟩ := S.exists_semi_eq hgA hγ (hconj γ hγE) hyA hyp hye
  have hτp : τ ^ p ^ 1 = 1 := by rw [pow_one]; exact S.tau_pow
  have hfix : ∀ (ρ : k ≃+* k) (n : ℕ), ρ ^ p ^ n = 1 → ∀ c : kˣ, c ^ p = 1 →
      Units.map ρ.toRingHom.toMonoidHom c = c := fun ρ n hρ c hc => S.units_map_eq hρ hc
  have hsemi_mul : ∀ (g' : GL (Fin d) k) (ρ : k ≃+* k) (n : ℕ), ρ ^ p ^ n = 1 → ∀ c : kˣ,
      c ^ p = 1 → ∀ z : GL (Fin d) k, semi g' ρ (Matrix.GeneralLinearGroup.scalar (Fin d) c * z) =
        Matrix.GeneralLinearGroup.scalar (Fin d) c * semi g' ρ z := by
    intro g' ρ n hρ c hc z
    rw [map_mul, semi_scalar, hfix ρ n hρ c hc]
  set sc := Matrix.GeneralLinearGroup.scalar (Fin d) (R := k)
  have hsc_comm : ∀ (c : kˣ) (z : GL (Fin d) k), sc c * z = z * sc c := fun c z =>
    (Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩) z).symm
  have h13 : c₁ * c₃ = 1 := by
    have h := semi_semi (Matrix.GeneralLinearGroup.map τ⁻¹.toRingHom 1⁻¹) 1 τ⁻¹ τ y
    rw [hc₁, hsemi_mul _ τ⁻¹ 1 (inv_pow_eq_one hτp) c₁ hc₁p, hc₃, inv_one, map_one, one_mul,
      inv_mul_cancel, semi_one_one, ← mul_assoc, ← map_mul] at h
    apply scalar_injective (k := k) hd1
    rw [map_one]
    calc sc (c₁ * c₃) = sc (c₁ * c₃) * y * y⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  have h24 : c₂ * c₄ = 1 := by
    have h := semi_semi g (Matrix.GeneralLinearGroup.map σ⁻¹.toRingHom g⁻¹) σ σ⁻¹ y
    rw [hc₂, hsemi_mul g σ m hσm c₂ hc₂p, hc₄, ← mul_assoc, ← map_mul, ← YS09Field.glMap_mul,
      mul_inv_cancel, YS09Field.glMap_one, mul_inv_cancel, semi_one_one] at h
    apply scalar_injective (k := k) hd1
    rw [map_one]
    calc sc (c₂ * c₄) = sc (c₂ * c₄) * y * y⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  have hWy : semi W 1 y = y := by
    rw [hfun, hc₁, hsemi_mul _ σ⁻¹ m (inv_pow_eq_one hσm) c₁ hc₁p,
      hc₂, ← mul_assoc, ← map_mul, hsemi_mul _ τ⁻¹ 1 (inv_pow_eq_one hτp) _
        (by rw [mul_pow, hc₁p, hc₂p, one_mul]),
      hc₃, ← mul_assoc, ← map_mul, hsemi_mul g σ m hσm _
        (by rw [mul_pow, mul_pow, hc₁p, hc₂p, hc₃p, one_mul, one_mul]),
      hc₄, ← mul_assoc, ← map_mul]
    have h1234 : c₁ * c₂ * c₃ * c₄ = 1 := by
      calc c₁ * c₂ * c₃ * c₄ = (c₁ * c₃) * (c₂ * c₄) := by
            rw [mul_assoc, mul_assoc, mul_assoc, mul_left_comm c₂, ← mul_assoc]
        _ = 1 := by rw [h13, h24, one_mul]
    rw [h1234, map_one, one_mul]
  have hWy' : W * y = y * W := by
    have h := hWy
    rw [semi_apply, YS09Field.glMap_one] at h
    calc W * y = W * y * W⁻¹ * W := by group
      _ = y * W := by rw [h]
  rw [hxW, mul_assoc, hsc_comm s y, ← mul_assoc, hWy', mul_assoc]

theorem mul_comm_of_mem (S : GSetting p q₀ d k D K ψ E) {e f : MulAut K} (he : e ∈ E)
    (hf : f ∈ E) : e * f = f * e := by
  haveI := S.elem.1
  exact congrArg Subtype.val (mul_comm' (⟨e, he⟩ : E) ⟨f, hf⟩)

theorem comm_mem_scalars (S : GSetting p q₀ d k D K ψ E) {e f : MulAut K} (he : e ∈ E)
    (hf : f ∈ E) {x y : GL (Fin d) k} (hxA : x ∈ D.A) (hyA : y ∈ D.A) (hx : Implements S.π e x)
    (hy : Implements S.π f y) : x * y * x⁻¹ * y⁻¹ ∈ LargeEvenScalars (Fin d) k := by
  have h := ((hx.mul hyA hy).mul (D.A.inv_mem hxA) hx.inv).mul (D.A.inv_mem hyA) hy.inv
  rw [S.mul_comm_of_mem he hf, mul_inv_cancel_right, mul_inv_cancel] at h
  exact mem_scalars_of_implements_one S.ker_le
    (D.A.mul_mem (D.A.mul_mem (D.A.mul_mem hxA hyA) (D.A.inv_mem hxA)) (D.A.inv_mem hyA)) h

theorem isLift_comm (S : GSetting p q₀ d k D K ψ E) {x y : GL (Fin d) k} (hx : S.IsLift x)
    (hy : S.IsLift y) : x * y = y * x := by
  classical
  have hL : ∀ e : E, ∃ x : GL (Fin d) k, x ∈ D.A ∧ x ^ p = 1 ∧ Implements S.π e x :=
    fun e => S.exists_lift e.2
  choose L hLA hLp hLi using hL
  have hLlift : ∀ e : E, S.IsLift (L e) := fun e => ⟨hLA e, hLp e, e, e.2, hLi e⟩
  letI : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (S.mul_comm_of_mem a.2 b.2) }
  let c : E → E → GL (Fin d) k := fun e f => L e * L f * (L e)⁻¹ * (L f)⁻¹
  have hcen : ∀ e f, c e f ∈ Subgroup.center (GL (Fin d) k) := fun e f =>
    scalar_mem_center (S.comm_mem_scalars e.2 f.2 (hLA e) (hLA f) (hLi e) (hLi f))
  have hprod : ∀ e e' : E, ∃ s ∈ Subgroup.center (GL (Fin d) k), L (e * e') = L e * L e' * s := by
    intro e e'
    have h := implements_unique S.ker_le (hLA (e * e')) (D.A.mul_mem (hLA e) (hLA e'))
      (hLi (e * e')) ((hLi e).mul (hLA e') (hLi e'))
    exact ⟨_, scalar_mem_center h, by rw [mul_inv_cancel_left]⟩
  have hl : ∀ a a' b, c (a * a') b = c a b * c a' b := by
    intro a a' b
    obtain ⟨s, hs, hseq⟩ := hprod a a'
    simp only [c]
    rw [hseq, ggL45TA_comm_mul_center_left hs, ggL45TA_comm_mul_left (hcen a' b)]
  have hr : ∀ a b b', c a (b * b') = c a b * c a b' := by
    intro a b b'
    obtain ⟨s, hs, hseq⟩ := hprod b b'
    simp only [c]
    rw [hseq, ggL45TA_comm_mul_center_right hs, ggL45TA_comm_mul_right (hcen a b')]
  have halt : ∀ a, c a a = 1 := fun a => by simp only [c]; group
  obtain ⟨P, hPE, hPcard, hPγ⟩ := S.pik
  have hP : ∀ a ∈ P.subgroupOf E, ∀ b, c a b = 1 := by
    intro a ha b
    obtain ⟨γ, hγp, hγE, hγe⟩ := hPγ a (Subgroup.mem_subgroupOf.mp ha)
    have hcomm := S.commute_of_mem_P hγp hγE (hLA a) (hγe ▸ hLi a) (hLlift b)
    simp only [c]
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel]
  have hEfin : Finite E := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have := S.card_E
    rw [Nat.card_eq_zero_of_infinite] at this
    exact absurd this (Nat.not_le.mpr (pow_pos S.hp.pos 2))
  have hidx : (P.subgroupOf E).index ∣ p := by
    haveI : Fact p.Prime := ⟨S.hp⟩
    have hpE : IsPGroup p E := fun g => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact S.elem.2 g g.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpE
    have hdvd : (P.subgroupOf E).index ∣ p ^ m := hm ▸ Subgroup.index_dvd_card _
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow S.hp).mp hdvd
    haveI : Finite P := Finite.of_injective (Subgroup.inclusion hPE)
      (Subgroup.inclusion_injective hPE)
    have hcardP : Nat.card (P.subgroupOf E) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv
    have hmul := Subgroup.card_mul_index (P.subgroupOf E)
    rw [hcardP] at hmul
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have hle : (P.subgroupOf E).index ≤ p := by
      have h1 : Nat.card P * (P.subgroupOf E).index ≤ Nat.card P * p := by
        rw [hmul, mul_comm (Nat.card P)]; exact hPcard
      exact Nat.le_of_mul_le_mul_left h1 hPpos
    rw [hjeq] at hle ⊢
    rcases j with _ | _ | j
    · simp
    · simp
    · exfalso
      have h2 : p ^ 2 ≤ p ^ (j + 2) := Nat.pow_le_pow_right S.hp.pos (by omega)
      have h3 := S.hp.two_le
      nlinarith
  have hall := ggL45TA_pairing_eq_one S.hp c hl hr halt (P.subgroupOf E) hP hidx
  obtain ⟨hxA, -, e, he, hxe⟩ := hx
  obtain ⟨hyA, -, f, hf, hyf⟩ := hy
  obtain ⟨s, hs⟩ := implements_unique S.ker_le hxA (hLA ⟨e, he⟩) hxe (hLi ⟨e, he⟩)
  obtain ⟨s', hs'⟩ := implements_unique S.ker_le hyA (hLA ⟨f, hf⟩) hyf (hLi ⟨f, hf⟩)
  have hxeq : x = L ⟨e, he⟩ * Matrix.GeneralLinearGroup.scalar (Fin d) s := by
    rw [hs, mul_inv_cancel_left]
  have hyeq : y = L ⟨f, hf⟩ * Matrix.GeneralLinearGroup.scalar (Fin d) s' := by
    rw [hs', mul_inv_cancel_left]
  have hc : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [hxeq, hyeq, ggL45TA_comm_mul_center_left (scalar_mem_center ⟨s, rfl⟩),
      ggL45TA_comm_mul_center_right (scalar_mem_center ⟨s', rfl⟩)]
    exact hall ⟨e, he⟩ ⟨f, hf⟩
  calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
    _ = y * x := by rw [hc, one_mul]

end GSetting

end CFSG.StandardType.GGL45TG
