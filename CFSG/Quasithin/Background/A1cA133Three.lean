module

public import CFSG.Quasithin.Background.A1cA133Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LinearGroups
open scoped MatrixGroups commutatorElement

namespace A1c

section Prelim

theorem transvection_pow_three_eq_one {i j : Fin 2} (hij : i ≠ j) (c : ZMod 3) :
    (Matrix.SpecialLinearGroup.transvection hij c : SL(2, ZMod 3)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, pow_succ, pow_one]
  simp only [coe_transvection]
  rw [(elementary_matrix_identities hij).2.1, (elementary_matrix_identities hij).2.1]
  have : c + c + c = 0 := by revert c; decide
  rw [this, Matrix.single_zero, add_zero]
  rfl

theorem hom_eq_one_of_sl2_three {L A : Type*} [Group L] [Group A] (π : L →* SL(2, ZMod 3))
    (hπ : Function.Surjective π) (hA : ∀ a : A, a * a = 1) (f : L →* A) (hf : π.ker ≤ f.ker) :
    f = 1 := by
  have hgen : ∀ T ∈ elementarySet 2 (ZMod 3), T ∈ (f.ker).map π := by
    rintro T ⟨i, j, hij, c, rfl⟩
    obtain ⟨g, hg⟩ := hπ (Matrix.SpecialLinearGroup.transvection hij c)
    refine ⟨g, MonoidHom.mem_ker.2 ?_, hg⟩
    have hg3 : g ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hg]
      exact transvection_pow_three_eq_one hij c
    have h1 : f g ^ 3 = 1 := by rw [← map_pow]; exact hf hg3
    have h2 := hA (f g)
    calc f g = f g ^ 3 * (f g * f g)⁻¹ := by group
      _ = 1 := by rw [h1, h2]; simp
  have htop : (f.ker).map π = ⊤ := by
    rw [eq_top_iff, ← special_linear_elementary_generation (n := 2) (K := ZMod 3)]
    exact (Subgroup.closure_le _).2 hgen
  ext g
  have hmem : π g ∈ (f.ker).map π := by rw [htop]; trivial
  obtain ⟨k, hk, hkg⟩ := hmem
  have h1 : k⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  have h2 := MonoidHom.mem_ker.1 (hf h1)
  rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk, inv_one, one_mul] at h2
  simpa using h2

theorem matrix_eq_one_or_neg_one_of_sq_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M = 1) (hdet : M.det = 1) : M = 1 ∨ M = -1 := by
  by_contra hcon
  push Not at hcon
  have h3 := det_eq_neg_one_of_sq_eq_one hM hcon.1 hcon.2
  rw [hdet] at h3
  apply h2
  linear_combination h3

theorem sl2_eq_negOne_of_sq_eq_one_three {g : SL(2, ZMod 3)} (hg : g * g = 1) (hg1 : g ≠ 1) :
    g = sl2NegOne 3 := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hM : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g = 1 := by
    simpa using congrArg Subtype.val hg
  rcases matrix_eq_one_or_neg_one_of_sq_eq_one h2 hM g.2 with h | h
  · exact absurd (Subtype.ext h) hg1
  · apply Subtype.ext
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2NegOne]

theorem neg_one_ne_one_GL_three : (-1 : GL (Fin 2) (ZMod 3)) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) (ZMod 3) => ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0)) h
  simp at this
  revert this
  decide

end Prelim

section ActGL

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [Group L] [Finite L]

theorem exists_actGL {P : Subgroup L} [P.Normal] (hP : IsPOnePlusTwo p ↥P) :
    ∃ Θ : L →* GL (Fin 2) (ZMod p),
      (∀ g, Θ g = 1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ centerOf P) ∧
      (∀ g, Θ g = -1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y ∈ centerOf P) := by
  classical
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hVel : CFSG.IsElementaryAbelian p (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p ↥P
  have hVcomm : ∀ a b : ↥P ⧸ Subgroup.center ↥P, a * b = b * a := fun a b => mul_comm' a b
  have hVpow : ∀ a : ↥P ⧸ Subgroup.center ↥P, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p _) a
  have hVcard : Nat.card (↥P ⧸ Subgroup.center ↥P) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
    rw [hPcard, CFSG.IsExtraspecial.center_order_p p ↥P] at h1
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    exact (Nat.eq_of_mul_eq_mul_right hp.out.pos (h3.symm.trans h1)).symm
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p) hVcomm hVpow hVcard
  let ε := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  refine ⟨ε.toMonoidHom.comp (actV P), fun g => ?_, fun g => ?_⟩
  · rw [← actV_eq_one_iff]
    show ε (actV P g) = 1 ↔ _
    rw [← map_one ε]
    exact ε.injective.eq_iff
  · rw [← actV_eq_inv_iff]
    exact CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e (actV P g)

omit [Finite L] in
theorem comm_eq_one_of_inverting {P : Subgroup L} (hp2 : p ≠ 2) (hPp : ∀ y ∈ P, y ^ p = 1)
    {t x y : L} (hyP : y ∈ P) (hZt : ∀ z ∈ centerOf P, t * z = z * t)
    (hZx : ∀ z ∈ centerOf P, x * z = z * x) (hxt : t * x = x * t)
    (hty : t * y * t⁻¹ * y ∈ centerOf P) (hxy : x * y * x⁻¹ * y⁻¹ ∈ centerOf P) :
    x * y * x⁻¹ * y⁻¹ = 1 := by
  set z' := x * y * x⁻¹ * y⁻¹ with hz'
  set z₁ := t * y * t⁻¹ * y with hz₁
  have hZP : centerOf P ≤ P := inf_le_left
  have hZc : ∀ z ∈ centerOf P, ∀ y ∈ P, y * z = z * y := fun z hz y hy =>
    (mem_centerOf_iff.1 hz).2 y hy
  have hyz' : x * y * x⁻¹ = z' * y := by rw [hz']; group
  have htyz : t * y * t⁻¹ = z₁ * y⁻¹ := by rw [hz₁]; group
  have hyP' : y⁻¹ ∈ P := P.inv_mem hyP
  have hxt' : x * t = t * x := hxt.symm
  have hA : x * (t * y * t⁻¹) * x⁻¹ = z' * (z₁ * y⁻¹) := by
    calc x * (t * y * t⁻¹) * x⁻¹ = (x * t) * y * (x * t)⁻¹ := by group
      _ = (t * x) * y * (t * x)⁻¹ := by rw [hxt']
      _ = t * (x * y * x⁻¹) * t⁻¹ := by group
      _ = t * (z' * y) * t⁻¹ := by rw [hyz']
      _ = (t * z' * t⁻¹) * (t * y * t⁻¹) := by group
      _ = z' * (z₁ * y⁻¹) := by rw [htyz, mul_inv_eq_iff_eq_mul.2 (hZt z' hxy)]
  have hB : x * (t * y * t⁻¹) * x⁻¹ = z₁ * (y⁻¹ * z'⁻¹) := by
    calc x * (t * y * t⁻¹) * x⁻¹ = x * (z₁ * y⁻¹) * x⁻¹ := by rw [htyz]
      _ = (x * z₁ * x⁻¹) * (x * y * x⁻¹)⁻¹ := by group
      _ = z₁ * (y⁻¹ * z'⁻¹) := by rw [mul_inv_eq_iff_eq_mul.2 (hZx z₁ hty), hyz', mul_inv_rev]
  have hz'c : Commute z' y⁻¹ := (hZc z' hxy y⁻¹ hyP').symm
  have hz₁c : Commute z₁ z' := (hZc z₁ hty z' (hZP hxy)).symm
  have h1 : z' * z₁ * y⁻¹ = z₁ * z'⁻¹ * y⁻¹ := by
    calc z' * z₁ * y⁻¹ = z' * (z₁ * y⁻¹) := by group
      _ = z₁ * (y⁻¹ * z'⁻¹) := by rw [← hA, ← hB]
      _ = z₁ * (z'⁻¹ * y⁻¹) := by rw [(hz'c.inv_left).eq]
      _ = z₁ * z'⁻¹ * y⁻¹ := by group
  have h2 : z' * z₁ = z₁ * z'⁻¹ := mul_right_cancel h1
  have h3 : z' = z'⁻¹ := by
    rw [← hz₁c.eq] at h2
    exact mul_left_cancel h2
  have hsq : z' * z' = 1 := mul_eq_one_iff_eq_inv.2 h3
  have h2d : orderOf z' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hpd : orderOf z' ∣ p := orderOf_dvd_of_pow_eq_one (hPp z' (hZP hxy))
  have hg : orderOf z' ∣ Nat.gcd 2 p := Nat.dvd_gcd h2d hpd
  have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)
  rw [hcop] at hg
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)

end ActGL

end A1c

open A1c

section Main3

variable {L : Type*} [Group L] [Finite L]

theorem two_lt_pRank_of_quotient_sl2_three (P : Subgroup L) [P.Normal]
    (hP : IsPOnePlusTwo 3 ↥P) (hL : Nonempty (L ⧸ P ≃* SL(2, ZMod 3))) {t : L}
    (ht2 : orderOf t = 2) (htP : ∃ y ∈ P, t * y * t⁻¹ ≠ y) {X : Subgroup L}
    (hXcard : Nat.card X = 3) (hXt : X ≤ Subgroup.centralizer ({t} : Set L))
    (hXZ : X ≠ Subgroup.center L) : 2 < pRank 3 (⊤ : Subgroup L) := by
  classical
  obtain ⟨e⟩ := hL
  let π : L →* SL(2, ZMod 3) := e.toMonoidHom.comp (QuotientGroup.mk' P)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective P)
  have hker : π.ker = P := by
    ext g
    rw [MonoidHom.mem_ker]
    show e (g : L ⧸ P) = 1 ↔ g ∈ P
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hP' := hP
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hPp : ∀ y ∈ P, y ^ 3 = 1 := fun y hy => by
    simpa using congrArg Subtype.val (hPexp ⟨y, hy⟩)
  set Z := centerOf P with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZcard : Nat.card Z = 3 := card_centerOf hext
  have hZexp : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => hPp z (hZP hz)
  have hπP : ∀ y ∈ P, π y = 1 := fun y hy => by
    rw [← MonoidHom.mem_ker, hker]; exact hy
  have hπmem : ∀ y, π y = 1 → y ∈ P := fun y hy => by
    rw [← hker]; exact hy
  have hZcen : ∀ g : L, ∀ z ∈ Z, g * z = z * g := by
    have := centerOf_normal (P := P)
    have hcyc : IsCyclic ↥Z := isCyclic_of_prime_card hZcard
    let ψ : L →* MulAut ↥Z := MulAut.conjNormal
    have hMA : ∀ a : MulAut ↥Z, a * a = 1 := by
      intro a
      have h1 : Nat.card (MulAut ↥Z) = 2 := by
        rw [IsCyclic.card_mulAut, hZcard, Nat.totient_prime Nat.prime_three]
      have : Finite (MulAut ↥Z) := Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
      have h2 := pow_card_eq_one' (G := MulAut ↥Z) (x := a)
      rw [h1, sq] at h2
      exact h2
    have hψ : ψ = 1 := hom_eq_one_of_sl2_three π hπ hMA ψ (by
      intro k hk
      rw [hker] at hk
      rw [MonoidHom.mem_ker]
      ext w
      have h1 := (mem_centerOf_iff.1 w.2).2 k hk
      have h2 : (((MulAut.conjNormal k : MulAut ↥Z) w : ↥Z) : L) = k * w * k⁻¹ :=
        MulAut.conjNormal_apply k w
      show (((MulAut.conjNormal k : MulAut ↥Z) w : ↥Z) : L) = (w : L)
      rw [h2, mul_inv_eq_iff_eq_mul]
      exact h1)
    intro g z hz
    have hψg : ψ g = 1 := by rw [hψ]; rfl
    have h3 := congrArg (fun φ : MulAut ↥Z => ((φ ⟨z, hz⟩ : ↥Z) : L)) hψg
    have h2 : (((MulAut.conjNormal g : MulAut ↥Z) ⟨z, hz⟩ : ↥Z) : L) = g * z * g⁻¹ :=
      MulAut.conjNormal_apply g ⟨z, hz⟩
    have h4 : g * z * g⁻¹ = z := by
      have h5 : (((MulAut.conjNormal g : MulAut ↥Z) ⟨z, hz⟩ : ↥Z) : L) = z := h3
      rw [← h2]; exact h5
    rw [mul_inv_eq_iff_eq_mul] at h4
    exact h4
  obtain ⟨Θ, hΘ1, hΘneg⟩ := exists_actGL (p := 3) hP'
  have hPK : ∀ y ∈ P, Θ y = 1 := fun y hy =>
    (hΘ1 y).2 fun y' hy' => commutator_mem_centerOf hext hy hy'
  have hdet : ∀ g : L, ((Θ g : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    have hf : (Matrix.GeneralLinearGroup.det.comp Θ) = 1 :=
      hom_eq_one_of_sl2_three π hπ (fun a => by revert a; decide) _ (by
        intro k hk
        rw [hker] at hk
        rw [MonoidHom.mem_ker]
        simp [hPK k hk])
    intro g
    have := congrArg (fun f : L →* (ZMod 3)ˣ => ((f g : (ZMod 3)ˣ) : ZMod 3)) hf
    simpa using this
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have htt : t * t = 1 := by rw [← sq]; exact ht2 ▸ pow_orderOf_eq_one t
  have hΘt1 : Θ t ≠ 1 := by
    intro h
    obtain ⟨y, hyP, hy⟩ := htP
    apply hy
    have hall := (hΘ1 t).1 h y hyP
    set z := t * y * t⁻¹ * y⁻¹ with hz
    have hzy : t * y * t⁻¹ = z * y := by rw [hz]; group
    have h1 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [htt]; group
    have h3 : t * (t * y * t⁻¹) * t⁻¹ = z * (z * y) := by
      rw [hzy]
      calc t * (z * y) * t⁻¹ = (t * z * t⁻¹) * (t * y * t⁻¹) := by group
        _ = z * (z * y) := by rw [mul_inv_eq_iff_eq_mul.2 (hZcen t z hall), hzy]
    have h4 : z * z = 1 := by
      have h5 : z * z * y = 1 * y := by
        calc z * z * y = z * (z * y) := by group
          _ = y := by rw [← h3, h1]
          _ = 1 * y := (one_mul y).symm
      exact mul_right_cancel h5
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [hZexp z hall, h4]; simp
    rw [hz1, one_mul] at hzy
    exact hzy
  have hΘt : Θ t = -1 := by
    rcases GL2_eq_one_or_neg_one_of_sq_eq_one h2 (by rw [← map_mul, htt, map_one]) (hdet t) with h | h
    · exact absurd h hΘt1
    · exact h
  have ht : ∀ y ∈ P, t * y * t⁻¹ * y ∈ Z := (hΘneg t).1 hΘt
  have hπt : π t = sl2NegOne 3 := by
    apply sl2_eq_negOne_of_sq_eq_one_three (by rw [← map_mul, htt, map_one])
    intro h1
    have htP' : t ∈ P := hπmem t h1
    have h3 : t ^ 3 = 1 := hPp t htP'
    have h4 : t = 1 := by
      calc t = t ^ 3 * (t * t)⁻¹ := by group
        _ = 1 := by rw [h3, htt]; simp
    rw [h4, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hcenterL : Subgroup.center L ≤ Z := by
    intro z hz
    have hzc : ∀ g : L, g * z = z * g := Subgroup.mem_center_iff.1 hz
    have hπzc : π z ∈ Subgroup.center (SL(2, ZMod 3)) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨g, rfl⟩ := hπ s
      rw [← map_mul, ← map_mul, hzc g]
    rcases eq_one_or_eq_sl2NegOne_of_mem_center hπzc with h | h
    · exact ⟨hπmem z h, Subgroup.mem_centralizer_iff.2 fun y hy => hzc y⟩
    · exfalso
      have hztP : z * t⁻¹ ∈ P := by
        apply hπmem
        rw [map_mul, map_inv, h, hπt, mul_inv_cancel]
      have hΘz : Θ z = 1 := (hΘ1 z).2 fun y hy => by
        have : z * y * z⁻¹ * y⁻¹ = 1 := by rw [← hzc y]; group
        rw [this]; exact (centerOf P).one_mem
      have hΘz' : Θ z = -1 := by
        have : z = (z * t⁻¹) * t := by group
        rw [this, map_mul, hPK _ hztP, one_mul, hΘt]
      exact neg_one_ne_one_GL_three (hΘz'.symm.trans hΘz)
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hXcard])
  set x : L := (x' : L) with hxdef
  have hxX : x ∈ X := x'.2
  have hxp : orderOf x = 3 := by rw [hxdef, Subgroup.orderOf_coe, hx']
  have hxcent : x ∈ Subgroup.centralizer ({t} : Set L) := hXt hxX
  have hxt : t * x = x * t := Subgroup.mem_centralizer_iff.1 hxcent t (Set.mem_singleton t)
  by_cases hΘx : Θ x = 1
  ·
    have hxall := (hΘ1 x).1 hΘx
    have hxc : ∀ y ∈ P, x * y = y * x := fun y hy => by
      have h1 := comm_eq_one_of_inverting hp2 hPp hy (fun z hz => hZcen t z hz)
        (fun z hz => hZcen x z hz) hxt (ht y hy) (hxall y hy)
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hxP : x ∉ P := by
      intro hxPm
      have hxZ : x ∈ Z := (mem_centerOf_iff).2 ⟨hxPm, fun y hy => (hxc y hy).symm⟩
      have h1 : Subgroup.zpowers x = X :=
        Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hxX)
          (by rw [Nat.card_zpowers, hxp, hXcard])
      have h2 : Subgroup.zpowers x = Z := zpowers_eq_of_card_eq_prime hZcard hxZ hxp
      apply hXZ
      rw [← h1, h2]
      exact le_antisymm hcenterL (fun z hz => Subgroup.mem_center_iff.2 fun g => hZcen g z hz)
        |>.symm
    exact two_lt_pRank_of_centralizing_element hP' hxp hxc hxP
  ·
    have hxV : ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ Z := by
      by_contra hcon
      push Not at hcon
      exact hΘx ((hΘ1 x).2 hcon)
    exact two_lt_pRank_of_inverting_element hp2 hP' ht hxcent hxp hxV

end Main3

end CFSG.Quasithin
