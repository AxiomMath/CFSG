module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkCore
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmRank

public section

namespace CFSG.StandardType

namespace WitOmBlk

open Matrix Module QuadraticMap SUTB NoOffOm OrdPNsGen OrdPNsOm
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Abstract

theorem exists_conj_mem_zpowers {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hrank : ∀ x z : H, x ^ p = 1 → z ^ p = 1 → x * z = z * x → z ≠ 1 →
      x ∈ Subgroup.zpowers z)
    {b c : H} (hbp : b ^ p = 1) (hb1 : b ≠ 1) (hcp : c ^ p = 1) :
    ∃ h : H, h * c * h⁻¹ ∈ Subgroup.zpowers b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hc1 : c = 1
  · exact ⟨1, by rw [hc1]; simp⟩
  have hbo : orderOf b = p := orderOf_eq_prime hbp hb1
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hbP : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have hcP : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco, pow_one])
  obtain ⟨P, hbPle⟩ := hbP.exists_le_sylow
  obtain ⟨P', hcPle⟩ := hcP.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P' P
  have hcP' : c ∈ (P' : Subgroup H) := hcPle (Subgroup.mem_zpowers c)
  have hhc : h * c * h⁻¹ ∈ (P : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul c (MulAut.conj h) _ hcP'
  have hbmem : b ∈ (P : Subgroup H) := hbPle (Subgroup.mem_zpowers b)
  have hPnt : Nontrivial (P : Subgroup H) :=
    ⟨⟨⟨b, hbmem⟩, 1, fun h' => hb1 (congrArg Subtype.val h')⟩⟩
  have hZ := P.isPGroup'.center_nontrivial
  have hZP : IsPGroup p (Subgroup.center (P : Subgroup H)) := P.isPGroup'.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZP
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hn
  have hdvd : p ∣ Nat.card (Subgroup.center (P : Subgroup H)) := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set z : H := ((z₀ : (P : Subgroup H)) : H) with hz
  have hzo : orderOf z = p := by
    rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hzp : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have hzc : ∀ w ∈ (P : Subgroup H), w * z = z * w := by
    intro w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z₀.2 ⟨w, hw⟩)
  have hbz := hrank b z hbp hzp (hzc b hbmem) hz1
  have hcz := hrank _ z (by rw [conj_pow, hcp, mul_one, mul_inv_cancel]) hzp (hzc _ hhc) hz1
  have heq : Subgroup.zpowers b = Subgroup.zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hbz) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hbo, hzo]
  exact ⟨h, heq ▸ hcz⟩

end Abstract

section Supp

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem map_mem_of_fix_orth' [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {f : Module.End K V} (hf : ∀ u v, polar Q (f u) (f v) = polar Q u v) {X : Submodule K V}
    (hfix : ∀ y ∈ X.orthogonalBilin (polarBilin Q), f y = y) {x : V} (hx : x ∈ X) : f x ∈ X := by
  rw [← orthogonalBilin_orthogonalBilin hQ X, mem_orth_iff]
  intro y hy
  rw [← hfix y hy, hf, polar_comm]
  exact mem_orth_iff.mp hy x hx

theorem map_mem_orth_of_fix' {f : Module.End K V} (hf : ∀ u v, polar Q (f u) (f v) = polar Q u v)
    {X : Submodule K V} (hfix : ∀ x ∈ X, f x = x) {y : V}
    (hy : y ∈ X.orthogonalBilin (polarBilin Q)) : f y ∈ X.orthogonalBilin (polarBilin Q) := by
  rw [mem_orth_iff] at hy ⊢
  intro x hx
  rw [← hfix x hx, hf]
  exact hy x hx

theorem commute_end_of_fix [FiniteDimensional K V] {X : Submodule K V}
    (hX : NondegOn (polarBilin Q) X) {f₁ f₂ : Module.End K V}
    (h₁ : ∀ y ∈ X.orthogonalBilin (polarBilin Q), f₁ y = y) (h₁X : ∀ x ∈ X, f₁ x ∈ X)
    (h₂ : ∀ x ∈ X, f₂ x = x)
    (h₂Y : ∀ y ∈ X.orthogonalBilin (polarBilin Q), f₂ y ∈ X.orthogonalBilin (polarBilin Q)) :
    f₁ * f₂ = f₂ * f₁ := by
  ext v
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_add_orth hX v
  simp only [Module.End.mul_apply, map_add, h₂ x hx, h₁ y hy, h₁ _ (h₂Y y hy), h₂ _ (h₁X x hx)]

theorem eq_one_of_fix_fix [FiniteDimensional K V] {X : Submodule K V}
    (hX : NondegOn (polarBilin Q) X) {f : Module.End K V} (h₁ : ∀ x ∈ X, f x = x)
    (h₂ : ∀ y ∈ X.orthogonalBilin (polarBilin Q), f y = y) : f = 1 := by
  ext v
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_add_orth hX v
  simp only [map_add, h₁ x hx, h₂ y hy, Module.End.one_apply]

end Supp

section Piece

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ}

omit [CharP K 2] in
theorem exists_genMax_ge (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) {E₀ : Subgroup (GL (Fin d) K)} (hE₀ : E₀ ≤ matrixDerived Q)
    (hpow : ∀ a ∈ E₀, a ^ p = 1) (hcomm : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a) :
    ∃ E : Subgroup (GL (Fin d) K), GenMax (polB Q) (matrixDerived Q) p E ∧ E₀ ≤ E := by
  classical
  set Γ := matrixDerived Q with hΓ
  set P : Subgroup (GL (Fin d) K) → Prop := fun E =>
    E ≤ Γ ∧ E₀ ≤ E ∧ (∀ a ∈ E, a ^ p = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hP
  set R : ℕ → Prop := fun k => ∃ E, P E ∧ Nat.card E = k with hR
  have hP0 : P E₀ := ⟨hE₀, le_rfl, hpow, hcomm⟩
  have hbound : ∀ k, R k → k ≤ Nat.card (GL (Fin d) K) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hR0 : R (Nat.card E₀) := ⟨_, hP0, rfl⟩
  set N := Nat.findGreatest R (Nat.card (GL (Fin d) K)) with hN
  obtain ⟨E, hE, hEN⟩ : R N := Nat.findGreatest_spec (hbound _ hR0) hR0
  refine ⟨E, ⟨polB_isSymm, hnd.1, hp, hp2, hE.1, hE.2.2.1, hE.2.2.2, fun g hg hgp hgE => ?_,
    fun g hg v w => polB_glin_of_mem_isometries (matrixDerived_le_isometries Q (hE.1 hg)) v w,
    fun c hc W hW hWA => ?_⟩, hE.2.1⟩
  · set E' := Subgroup.closure ((E : Set (GL (Fin d) K)) ∪ {g}) with hE'
    have h1 := closure_comm_pow (S := (E : Set (GL (Fin d) K)) ∪ {g}) (p := p)
      (by
        rintro x (hx | hx) y (hy | hy)
        · exact hE.2.2.2 x hx y hy
        · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
        · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
        · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
      (by
        rintro x (hx | hx)
        · exact hE.2.2.1 x hx
        · rw [Set.mem_singleton_iff.mp hx]; exact hgp)
    have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hE'Γ : E' ≤ Γ := by
      rw [hE', Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hE.1 hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg
    have hP' : P E' := ⟨hE'Γ, hE.2.1.trans hEE', h1.2, h1.1⟩
    have hcard : Nat.card E' ≤ Nat.card E := by
      rw [hEN]
      exact Nat.le_findGreatest (hbound _ ⟨E', hP', rfl⟩) ⟨E', hP', rfl⟩
    have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
    rw [heq]
    exact Subgroup.subset_closure (Or.inr rfl)
  · exact exists_restrict_mem_omega hnd hT hp hp2 (hE.1 hc) (hE.2.2.1 c hc) hW (hWA c hc)

omit [Finite K] [CharP K 2] in
theorem glin_pow_of_eqOn {y b : GL (Fin d) K}
    (hUy : ∀ u ∈ grng y, glin y u ∈ grng y) (hbon : ∀ w ∈ grng y, glin b w = glin y w) :
    ∀ (k : ℕ), ∀ u ∈ grng y, glin (b ^ k) u = glin (y ^ k) u := by
  intro k
  induction k with
  | zero => intro u _; rw [pow_zero, pow_zero]
  | succ k ih =>
    intro u hu
    have hyk : glin (y ^ k) u ∈ grng y := pow_mem_of_inv hUy k u hu
    rw [pow_succ', glin_mul, Module.End.mul_apply, ih u hu, hbon _ hyk, ← Module.End.mul_apply,
      ← glin_mul, ← pow_succ']

theorem mem_zpowers_of_piece (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {A : Subgroup (GL (Fin d) K)} (hA : GenMax (polB Q) (matrixDerived Q) p A)
    {y : GL (Fin d) K} (hy : y ∈ A)
    (hcyc : ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ grng y, glin c u = glin (y ^ k) u)
    {b : GL (Fin d) K} (hbA : b ∈ A) (hbon : ∀ w ∈ grng y, glin b w = glin y w)
    {x z : GL (Fin d) K} (hx : x ∈ matrixDerived Q) (hz : z ∈ matrixDerived Q)
    (hxoff : ∀ v ∈ (grng y).orthogonalBilin (polB Q), glin x v = v)
    (hzoff : ∀ v ∈ (grng y).orthogonalBilin (polB Q), glin z v = v)
    (hxp : x ^ p = 1) (hzp : z ^ p = 1) (hxz : x * z = z * x) (hz1 : z ≠ 1) :
    x ∈ Subgroup.zpowers z := by
  classical
  by_contra hxz'
  have : Fact p.Prime := ⟨hA.prime⟩
  have hp1 := hA.prime.one_lt
  have hUnd : NondegOn (polB Q) (grng y) := nondegOn_grng hA hy
  have hUy : ∀ u ∈ grng y, glin y u ∈ grng y := grng_inv hA hy hy
  have hiso : ∀ g ∈ matrixDerived Q, ∀ u v, polar Q (glin g u) (glin g v) = polar Q u v :=
    fun g hg u v => polB_glin_of_mem_isometries (matrixDerived_le_isometries Q hg) u v
  set A₀ : Subgroup (GL (Fin d) K) := A ⊓ genFixOn d K (grng y : Set (Fin d → K)) with hA₀
  set X₀ : Subgroup (GL (Fin d) K) := Subgroup.zpowers x ⊔ Subgroup.zpowers z with hX₀
  have hX₀fix : X₀ ≤ genFixOn d K ((grng y).orthogonalBilin (polB Q) : Set (Fin d → K)) :=
    sup_le ((Subgroup.zpowers_le).mpr hxoff) ((Subgroup.zpowers_le).mpr hzoff)
  have hX₀Ω : X₀ ≤ matrixDerived Q :=
    sup_le ((Subgroup.zpowers_le).mpr hx) ((Subgroup.zpowers_le).mpr hz)
  have hcommA₀ : ∀ a ∈ A₀, ∀ w ∈ X₀, a * w = w * a := by
    intro a ha w hw
    apply glin_injective
    rw [glin_mul, glin_mul]
    exact (commute_end_of_fix hUnd (fun v hv => hX₀fix hw v hv)
      (fun u hu => map_mem_of_fix_orth' hnd (hiso w (hX₀Ω hw)) (fun v hv => hX₀fix hw v hv) hu)
      (fun u hu => ha.2 u hu)
      (fun v hv => map_mem_orth_of_fix' (fun u v => hA.iso a ha.1 u v) (fun u hu => ha.2 u hu)
        hv)).symm
  set S : Set (GL (Fin d) K) := (A₀ : Set (GL (Fin d) K)) ∪ {x, z} with hSdef
  have hxX : x ∈ X₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hzX : z ∈ X₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hSc : ∀ a ∈ S, ∀ c ∈ S, a * c = c * a := by
    rintro a (ha | ha | ha) c (hc | hc | hc)
    · exact hA.comm a ha.1 c hc.1
    · rw [hc]; exact hcommA₀ a ha x hxX
    · rw [Set.mem_singleton_iff.mp hc]; exact hcommA₀ a ha z hzX
    · rw [ha]; exact (hcommA₀ c hc x hxX).symm
    · rw [ha, hc]
    · rw [ha, Set.mem_singleton_iff.mp hc]; exact hxz
    · rw [Set.mem_singleton_iff.mp ha]; exact (hcommA₀ c hc z hzX).symm
    · rw [Set.mem_singleton_iff.mp ha, hc]; exact hxz.symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hc]
  have hSp : ∀ a ∈ S, a ^ p = 1 := by
    rintro a (ha | ha | ha)
    · exact hA.pow a ha.1
    · rw [ha]; exact hxp
    · rw [Set.mem_singleton_iff.mp ha]; exact hzp
  obtain ⟨hE₀c, hE₀p⟩ := closure_comm_pow hSc hSp
  have hE₀Ω : Subgroup.closure S ≤ matrixDerived Q := by
    rw [Subgroup.closure_le]
    rintro a (ha | ha | ha)
    · exact hA.le ha.1
    · rw [ha]; exact hx
    · rw [Set.mem_singleton_iff.mp ha]; exact hz
  obtain ⟨E, hE, hE₀E⟩ := exists_genMax_ge hnd hT hA.prime hA.ne_two hE₀Ω hE₀p hE₀c
  have hcardE := card_le_card_of_genMax hnd hT hE hA
  have hcardE₀ := Subgroup.card_le_of_le hE₀E
  have hAle : Nat.card A ≤ Nat.card A₀ * p := by
    have hbpow := glin_pow_of_eqOn hUy hbon
    have hzb : Subgroup.zpowers b ≤ A := (Subgroup.zpowers_le).mpr hbA
    let φ : A₀ × Subgroup.zpowers b → A := fun q =>
      ⟨q.1.1 * q.2.1, A.mul_mem q.1.2.1 (hzb q.2.2)⟩
    have hφ : Function.Surjective φ := by
      rintro ⟨c, hc⟩
      obtain ⟨k, hk⟩ := hcyc c hc
      have hpk : k + (p - 1) * k = p * k := by
        have : p - 1 + 1 = p := Nat.sub_add_cancel hA.prime.one_lt.le
        nlinarith
      have ha : c * b ^ ((p - 1) * k) ∈ A₀ := by
        refine ⟨A.mul_mem hc (A.pow_mem hbA _), fun u hu => ?_⟩
        rw [glin_mul, Module.End.mul_apply, hbpow _ u hu, hk _ (pow_mem_of_inv hUy _ u hu),
          ← Module.End.mul_apply, ← glin_mul, ← pow_add, hpk, pow_mul, hA.pow y hy, one_pow,
          glin_one]
        rfl
      refine ⟨(⟨_, ha⟩, ⟨b ^ k, Subgroup.npow_mem_zpowers b k⟩), Subtype.ext ?_⟩
      change c * b ^ ((p - 1) * k) * b ^ k = c
      rw [mul_assoc, ← pow_add, add_comm, hpk, pow_mul, hA.pow b hbA, one_pow, mul_one]
    calc Nat.card A ≤ Nat.card (A₀ × Subgroup.zpowers b) := Nat.card_le_card_of_surjective φ hφ
      _ = Nat.card A₀ * orderOf b := by rw [Nat.card_prod, Nat.card_zpowers]
      _ ≤ Nat.card A₀ * p :=
        Nat.mul_le_mul_left _ (orderOf_le_of_pow_eq_one hA.prime.pos (hA.pow b hbA))
  have hX₀E : X₀ ≤ Subgroup.closure S :=
    sup_le ((Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Or.inr (Or.inl rfl))))
      ((Subgroup.zpowers_le).mpr (Subgroup.subset_closure (Or.inr (Or.inr rfl))))
  have hE₀ge : Nat.card A₀ * Nat.card X₀ ≤ Nat.card (Subgroup.closure S) := by
    let ψ : A₀ × X₀ → Subgroup.closure S := fun q =>
      ⟨q.1.1 * q.2.1, (Subgroup.closure S).mul_mem (Subgroup.subset_closure (Or.inl q.1.2))
        (hX₀E q.2.2)⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨a, w⟩ ⟨a', w'⟩ h
      have h1 : a.1 * w.1 = a'.1 * w'.1 := congrArg Subtype.val h
      have htA : a'.1⁻¹ * a.1 ∈ A₀ := A₀.mul_mem (A₀.inv_mem a'.2) a.2
      have htX : a'.1⁻¹ * a.1 ∈ X₀ := by
        have e : a'.1⁻¹ * a.1 = w'.1 * w.1⁻¹ := by
          calc a'.1⁻¹ * a.1 = a'.1⁻¹ * (a.1 * w.1) * w.1⁻¹ := by group
            _ = w'.1 * w.1⁻¹ := by rw [h1]; group
        rw [e]
        exact X₀.mul_mem w'.2 (X₀.inv_mem w.2)
      have ht1 : a'.1⁻¹ * a.1 = 1 := by
        apply glin_injective
        rw [glin_one]
        exact eq_one_of_fix_fix hUnd (fun u hu => htA.2 u hu) (fun v hv => hX₀fix htX v hv)
      have haa : a = a' := Subtype.ext (inv_mul_eq_one.mp ht1).symm
      have hww : w = w' := Subtype.ext (by rw [haa] at h1; exact mul_left_cancel h1)
      rw [haa, hww]
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective ψ hψ
  have hX₀ge : p * p ≤ Nat.card X₀ := by
    have hXP : IsPGroup p X₀ := fun w =>
      ⟨1, Subtype.ext (by rw [pow_one]; exact hE₀p _ (hX₀E w.2))⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXP
    have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
    have hzle : Subgroup.zpowers z ≤ X₀ := le_sup_right
    by_contra hlt
    push Not at hlt
    have hn1 : n ≤ 1 := by
      by_contra hn2
      push Not at hn2
      have h2 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hA.prime.pos hn2
      rw [hn] at hlt
      nlinarith
    have hcard : Nat.card X₀ ≤ Nat.card (Subgroup.zpowers z) := by
      rw [Nat.card_zpowers, hzo, hn]
      calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right hA.prime.pos hn1
        _ = p := pow_one p
    have heq := Subgroup.eq_of_le_of_card_ge hzle hcard
    exact hxz' (by rw [heq]; exact hxX)
  have hA₀pos : 0 < Nat.card A₀ := Nat.card_pos
  have h1 : Nat.card A₀ * (p * p) ≤ Nat.card A₀ * p :=
    calc Nat.card A₀ * (p * p) ≤ Nat.card A₀ * Nat.card X₀ := Nat.mul_le_mul_left _ hX₀ge
      _ ≤ Nat.card (Subgroup.closure S) := hE₀ge
      _ ≤ Nat.card E := hcardE₀
      _ ≤ Nat.card A := hcardE
      _ ≤ Nat.card A₀ * p := hAle
  have h2 : p * p ≤ p * 1 := by
    rw [mul_one]
    exact Nat.le_of_mul_le_mul_left h1 hA₀pos
  have := Nat.le_of_mul_le_mul_left h2 hA.prime.pos
  omega

theorem exists_conj_eq_pow_of_piece (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {A : Subgroup (GL (Fin d) K)} (hA : GenMax (polB Q) (matrixDerived Q) p A)
    {y : GL (Fin d) K} (hy : y ∈ A)
    (hcyc : ∀ c ∈ A, ∃ k : ℕ, ∀ u ∈ grng y, glin c u = glin (y ^ k) u)
    {b : GL (Fin d) K} (hbA : b ∈ A) (hbon : ∀ w ∈ grng y, glin b w = glin y w)
    (hboff : ∀ v ∈ (grng y).orthogonalBilin (polB Q), glin b v = v) (hb1 : b ≠ 1)
    {c : GL (Fin d) K} (hc : c ∈ matrixDerived Q) (hcp : c ^ p = 1)
    (hcoff : ∀ v ∈ (grng y).orthogonalBilin (polB Q), glin c v = v) :
    ∃ h ∈ matrixDerived Q, (∀ v ∈ (grng y).orthogonalBilin (polB Q), glin h v = v) ∧
      ∃ k : ℕ, h * c * h⁻¹ = b ^ k := by
  classical
  set H₀ : Subgroup (GL (Fin d) K) := matrixDerived Q ⊓
    genFixOn d K ((grng y).orthogonalBilin (polB Q) : Set (Fin d → K)) with hH₀
  have hrank : ∀ x z : H₀, x ^ p = 1 → z ^ p = 1 → x * z = z * x → z ≠ 1 →
      x ∈ Subgroup.zpowers z := by
    intro x z hxp hzp hxz hz1
    have h := mem_zpowers_of_piece hnd hT hA hy hcyc hbA hbon x.2.1 z.2.1
      (fun v hv => x.2.2 v hv) (fun v hv => z.2.2 v hv)
      (by rw [← Subgroup.coe_pow, hxp]; rfl) (by rw [← Subgroup.coe_pow, hzp]; rfl)
      (congrArg Subtype.val hxz) (fun h1 => hz1 (Subtype.ext h1))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  have hb : b ∈ H₀ := ⟨hA.le hbA, fun v hv => hboff v hv⟩
  have hcH : c ∈ H₀ := ⟨hc, fun v hv => hcoff v hv⟩
  obtain ⟨h, hh⟩ := exists_conj_mem_zpowers hA.prime hrank (b := ⟨b, hb⟩) (c := ⟨c, hcH⟩)
    (Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.pow b hbA))
    (fun h1 => hb1 (congrArg Subtype.val h1)) (Subtype.ext (by rw [Subgroup.coe_pow]; exact hcp))
  obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hh)
  refine ⟨h.1, h.2.1, fun v hv => h.2.2 v hv, k, ?_⟩
  have := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv] at this
  exact this.symm

end Piece

end WitOmBlk

end CFSG.StandardType
