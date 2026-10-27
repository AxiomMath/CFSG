module

public import CFSG.RankThree.OddKernel.CriticalFixedSpaces
public import CFSG.RankThree.PartTwo.Sec13.F135LastFixed
public import CFSG.RankThree.PartTwo.Sec13.K135SFFour

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

section SFLin

open CFSG.SectionRank.Ccomm

private theorem exists_mulEquiv_fin_three {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ x y : W, x * y = y * x) (hexp : ∀ x : W, x ^ 3 = 1) :
    ∃ n : ℕ, Nonempty (W ≃* Multiplicative (Fin n → ZMod 3)) := by
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let _ : Module (ZMod 3) (Additive W) := AddCommGroup.zmodModule (n := 3) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  have hF : Module.Finite (ZMod 3) (Additive W) := Module.Finite.of_finite
  exact ⟨Module.finrank (ZMod 3) (Additive W), ⟨AddEquiv.toMultiplicativeRight
    (Module.finBasis (ZMod 3) (Additive W)).equivFun.toAddEquiv⟩⟩

theorem exists_linear_model {W : Type*} [Group W] [Finite W] (hcomm : ∀ x y : W, x * y = y * x)
    (hexp : ∀ x : W, x ^ 3 = 1) {Γ : Type*} [Group Γ] (α : Γ →* MulAut W) :
    ∃ (n : ℕ) (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)),
      (α ≠ 1 → ρ ≠ 1) ∧ ∀ g : Γ,
        Nat.card {v : Fin n → ZMod 3 //
          Matrix.mulVec ((ρ g : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
            Matrix (Fin n) (Fin n) (ZMod 3)) v = v} = Nat.card {w : W // α g w = w} := by
  obtain ⟨n, ⟨e⟩⟩ := exists_mulEquiv_fin_three hcomm hexp
  refine ⟨n, (elemAutEquivGL e).toMonoidHom.comp α, ?_, fun g => ?_⟩
  · intro hα hρ
    apply hα
    refine MonoidHom.ext fun g => ?_
    have hg : elemAutEquivGL e (α g) = 1 :=
      congrArg (fun f : Γ →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3) => f g) hρ
    rw [MonoidHom.one_apply]
    apply (elemAutEquivGL e).injective
    rw [hg, map_one]
  · have key : ∀ (v : Fin n → ZMod 3) (w : W), Multiplicative.toAdd (e w) = v →
        (Matrix.mulVec ((((elemAutEquivGL e).toMonoidHom.comp α) g :
            Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) v = v ↔
          α g w = w) := by
      intro v w hv
      subst hv
      have h1 : Matrix.mulVec ((((elemAutEquivGL e).toMonoidHom.comp α) g :
            Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3))
          (Multiplicative.toAdd (e w)) = Multiplicative.toAdd (e (α g w)) :=
        elemAutEquivGL_mulVec e (α g) w
      rw [h1]
      constructor
      · intro h
        exact e.injective (Multiplicative.toAdd.injective h)
      · intro h
        rw [h]
    let E : (Fin n → ZMod 3) ≃ W := Equiv.trans Multiplicative.ofAdd e.symm.toEquiv
    refine Nat.card_congr (Equiv.subtypeEquiv E ?_)
    intro v
    exact key v (E v) (by simp [E])

end SFLin

section SFFixed

open CFSG Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven
open scoped commutatorElement

private theorem comm_mem_centralizer_D {Y : Type*} [Group Y] {P : Subgroup Y} (D : Subgroup P)
    (hDcl : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set P)) (x y g : D) :
    g * ⁅x, y⁆ = ⁅x, y⁆ * g := by
  apply Subtype.ext
  have hc : ⁅(x : P), (y : P)⁆ ∈ ⁅D, (⊤ : Subgroup P)⁆ :=
    Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
  have hcen := (Subgroup.mem_inf.1 (hDcl hc)).2
  rw [Subgroup.mem_centralizer_iff] at hcen
  exact hcen _ g.2

theorem card_fixed_frattini_quotient_le_three {Y : Type*} [Group Y] [Finite Y] {P : Subgroup Y}
    [P.Normal] (hP : IsPGroup 3 P) (D : Subgroup P) [D.Characteristic]
    (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hDcl : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set P))
    {t : Y} (ht : orderOf t = 2)
    (hrank : CFSG.Open.pRank 3 (D.map P.subtype ⊓ Subgroup.centralizer {t}) ≤ 3) :
    Nat.card {w : D ⧸ frattini D //
      (frattiniAction D).comp (MulAut.conjNormal (H := P)) t w = w} ≤ 3 ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set α : Y →* MulAut (D ⧸ frattini D) := (frattiniAction D).comp (MulAut.conjNormal (H := P))
    with hα
  set g : D →* Y := P.subtype.comp D.subtype with hg
  have hginj : Function.Injective g := P.subtype_injective.comp D.subtype_injective
  set C' : Subgroup D := (centralizer {t}).comap g with hC'
  have hDp : IsPGroup 3 D := hP.to_subgroup D
  obtain ⟨-, hWcomm, -⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hDp
  have hC'rank : CFSG.Open.pRank 3 (⊤ : Subgroup C') ≤ 3 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt
      ((C'.equivMapOfInjective g hginj).trans
        (MulEquiv.subgroupCongr (CFSG.RankThree.OddKernel.map_comap_centralizer D t))),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrank
  have hC'pRank : CFSG.pRank 3 ↥C' ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥C']
    exact hC'rank
  have hC'p : IsPGroup 3 C' := hDp.to_subgroup C'
  have hC'exp : ∀ x : C', x ^ 3 = 1 := fun x =>
    Subtype.ext (Subtype.ext (by simpa using hDexp _ x.1.2))
  have hC'class : commutator ↥C' ≤ Subgroup.center ↥C' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact comm_mem_centralizer_D D hDcl x.1 y.1 k.1
  have hquot : Nat.card (↥C' ⧸ commutator ↥C') ≤ 3 ^ 4 :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.l9_card_quot_le hC'p hC'exp hC'class hC'pRank
  set f : C' →* D ⧸ frattini D := (QuotientGroup.mk' (frattini D)).comp C'.subtype with hf
  have hfW : ∀ a b : f.range, a * b = b * a := fun a b => Subtype.ext (hWcomm a.1 b.1)
  have hle : Nat.card f.range ≤ Nat.card (↥C' ⧸ commutator ↥C') :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.l9_card_le_of_surj hfW f.rangeRestrict
      (MonoidHom.rangeRestrict_surjective f)
  set A := zpowers t with hA
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  set β : A →* MulAut D := (MulAut.characteristic D).comp
    ((MulAut.conjNormal (H := P)).comp A.subtype) with hβ
  have hΦinv : ∀ a : A, ∀ n ∈ frattini D, β a n ∈ frattini D := fun a n hn =>
    characteristic_iff_le_comap.mp inferInstance (β a) hn
  have hcop : ¬ 2 ∣ Nat.card (frattini D) := by
    obtain ⟨k, hk⟩ := (hDp.to_subgroup (frattini D)).exists_card_eq
    rw [hk]
    intro h
    have h23 : (2 : ℕ) ∣ 3 := Nat.prime_two.dvd_of_dvd_pow h
    exact absurd h23 (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hA2 β (frattini D)
    hΦinv hcop
  have hqa : ∀ a : A, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction β
      (frattini D) hΦinv a = α a := fun a => rfl
  have hset : ∀ w : D ⧸ frattini D, α t w = w ↔ w ∈ f.range := by
    intro w
    constructor
    · intro hw
      have hstab : A ≤ (MulAction.stabilizer (MulAut (D ⧸ frattini D)) w).comap α := by
        rw [hA, zpowers_le, mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hw
      have hmem : w ∈ {q : D ⧸ frattini D | ∀ a : A,
          CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction β (frattini D) hΦinv a q
            = q} := by
        intro a
        rw [hqa]
        have := hstab a.2
        rwa [mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
      rw [hlift] at hmem
      obtain ⟨c, hc, rfl⟩ := hmem
      refine ⟨⟨c, ?_⟩, rfl⟩
      have h1 := congrArg (fun x : D => ((x : P) : Y)) (hc ⟨t, mem_zpowers t⟩)
      simp only [hβ, MonoidHom.comp_apply, MulAut.characteristic_apply_apply_coe,
        coe_subtype, MulAut.conjNormal_apply] at h1
      rw [hC', mem_comap, mem_centralizer_singleton_iff]
      change ((c : P) : Y) * t = t * ((c : P) : Y)
      calc ((c : P) : Y) * t = t * ((c : P) : Y) * t⁻¹ * t := by rw [h1]
        _ = t * ((c : P) : Y) := by group
    · rintro ⟨c, rfl⟩
      have hc : g c * t = t * g c := mem_centralizer_singleton_iff.1 c.2
      change frattiniAction D (MulAut.conjNormal t) ((c : D) : D ⧸ frattini D) =
        ((c : D) : D ⧸ frattini D)
      rw [frattiniAction_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      change t * ((c : D) : P) * t⁻¹ = (((c : D) : P) : Y)
      change ((c : D) : P) * t = t * ((c : D) : P) at hc
      rw [← hc, mul_inv_cancel_right]
  have hcard : Nat.card {w : D ⧸ frattini D // α t w = w} = Nat.card f.range :=
    Nat.card_congr (Equiv.subtypeEquivRight hset)
  rw [hcard]
  exact hle.trans hquot

end SFFixed

section SFCrit

open CFSG Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven
open scoped commutatorElement

theorem exists_critical_action {Y : Type*} [Group Y] [Finite Y] (Q : Subgroup Y) [Q.Normal]
    (hQ : IsPGroup 3 Q) (Xb : Subgroup Y) [Group.IsPerfect Xb]
    (hact : ¬ Xb ≤ Subgroup.centralizer (Q : Set Y)) :
    ∃ (D : Subgroup Q) (_ : D.Characteristic), D ≠ ⊥ ∧ (∀ x ∈ D, x ^ 3 = 1) ∧
      ⁅D, (⊤ : Subgroup Q)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set Q) ∧
      (frattiniAction D).comp ((MulAut.conjNormal (H := Q)).comp Xb.subtype) ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ1 : Q ≠ ⊥ := by
    intro h0
    apply hact
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [h0, SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  haveI : Nontrivial Q := (nontrivial_iff_ne_bot Q).2 hQ1
  obtain ⟨D, hDc, hD1, hDexp, hDZ, -, hker⟩ :=
    supercritical_witness (p := 3) (by norm_num) hQ
  refine ⟨D, hDc, hD1, hDexp, hDZ, ?_⟩
  intro hα
  set c : Xb →* MulAut Q := (MulAut.conjNormal (H := Q)).comp Xb.subtype with hc
  have hle : c.range ≤ (frattiniAction D).ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    have h1 : (frattiniAction D).comp c x = 1 := by
      rw [hα, MonoidHom.one_apply]
    exact h1
  have : Finite (MulAut Q) := inferInstance
  have hpg : IsPGroup 3 c.range := hker.to_le hle
  have : Group.IsPerfect c.range := Group.IsPerfect.range c
  have hc1 : c.range = ⊥ := by
    by_contra hne
    have : Nontrivial c.range := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent c.range hpg.isNilpotent
  apply hact
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hy : c ⟨x, hx⟩ = 1 := by
    have : c ⟨x, hx⟩ ∈ c.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hc1, Subgroup.mem_bot] at this
    exact this
  have hy' : (MulAut.conjNormal (H := Q) x : MulAut Q) = 1 := hy
  have h2 := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : Y)) hy'
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

end SFCrit

section SFCore

open CFSG Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm CFSG.Assembly.RankThreeEven
open scoped commutatorElement


theorem sf2_core {Y : Type*} [Group Y] [Finite Y] (Q : Subgroup Y) [Q.Normal] (hQ : IsPGroup 3 Q)
    (Xb : Subgroup Y) [Group.IsPerfect Xb] (hact : ¬ Xb ≤ Subgroup.centralizer (Q : Set Y))
    (hrank : ∀ t ∈ Xb, orderOf t = 2 → CFSG.Open.pRank 3 (Q ⊓ Subgroup.centralizer {t}) ≤ 3)
    (a b : Y) (ha : a ∈ Xb) (hb : b ∈ Xb) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) :
    ∃ (n : ℕ) (ρ : Xb →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)), n ≤ 12 ∧ ρ ≠ 1 ∧
      ∀ t : Xb, orderOf t = 2 → Nat.card {v : Fin n → ZMod 3 //
        Matrix.mulVec ((ρ t : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
          Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hDchar, hD1, hDexp, hDcl, hα⟩ := exists_critical_action Q hQ Xb hact
  haveI := hDchar
  set α : Xb →* MulAut (D ⧸ frattini D) :=
    (frattiniAction D).comp ((MulAut.conjNormal (H := Q)).comp Xb.subtype) with hαdef
  have hDp : IsPGroup 3 D := hQ.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  obtain ⟨n, ρ, hρ1, hρfix⟩ := exists_linear_model hWcomm hWpow α
  have hfix : ∀ t : Xb, orderOf t = 2 → Nat.card {w : D ⧸ frattini D // α t w = w} ≤ 3 ^ 4 := by
    intro t ht
    have ht' : orderOf (t : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have hr : CFSG.Open.pRank 3 (D.map Q.subtype ⊓ Subgroup.centralizer {(t : Y)}) ≤ 3 :=
      (CFSG.SectionRank.pRank_mono (by norm_num)
        (inf_le_inf_right _ (Subgroup.map_subtype_le D))).trans (hrank t t.2 ht')
    exact card_fixed_frattini_quotient_le_three hQ D hDexp hDcl ht' hr
  have hfixρ : ∀ t : Xb, orderOf t = 2 → Nat.card {v : Fin n → ZMod 3 //
      Matrix.mulVec ((ρ t : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
        Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ 4 := fun t ht => by
    rw [hρfix t]
    exact hfix t ht
  have hab' : (⟨a, ha⟩ : Xb) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := Subtype.ext hab
  have ha1 : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have hb1 : b ^ 2 = 1 := by rw [← hb2]; exact pow_orderOf_eq_one b
  have hna : (⟨a, ha⟩ : Xb) * ⟨a, ha⟩ = 1 := Subtype.ext (by simpa [sq] using ha1)
  have hnb : (⟨b, hb⟩ : Xb) * ⟨b, hb⟩ = 1 := Subtype.ext (by simpa [sq] using hb1)
  have hab2 : orderOf ((⟨a, ha⟩ : Xb) * ⟨b, hb⟩) = 2 := by
    have hxy : Commute (⟨a, ha⟩ : Xb) ⟨b, hb⟩ := hab'
    have hx2 : (⟨a, ha⟩ : Xb) ^ 2 = 1 := by rw [sq]; exact hna
    have hy2 : (⟨b, hb⟩ : Xb) ^ 2 = 1 := by rw [sq]; exact hnb
    refine orderOf_eq_prime ?_ ?_
    · rw [hxy.mul_pow, hx2, hy2, one_mul]
    · intro h
      apply hne
      have h1 : (⟨a, ha⟩ : Xb) = ⟨b, hb⟩ := by
        calc (⟨a, ha⟩ : Xb) = ⟨a, ha⟩ * (⟨b, hb⟩ * ⟨b, hb⟩) := by rw [hnb, mul_one]
          _ = (⟨a, ha⟩ * ⟨b, hb⟩) * ⟨b, hb⟩ := by rw [mul_assoc]
          _ = ⟨b, hb⟩ := by rw [h, one_mul]
      exact congrArg Subtype.val h1
  have hoa : orderOf (⟨a, ha⟩ : Xb) = 2 := by rw [← Subgroup.orderOf_coe]; exact ha2
  have hob : orderOf (⟨b, hb⟩ : Xb) = 2 := by rw [← Subgroup.orderOf_coe]; exact hb2
  have hn : n ≤ 3 * 4 := by
    refine le_of_four_group_fixed (ρ ⟨a, ha⟩) (ρ ⟨b, hb⟩) ?_ ?_ ?_
      (hfixρ _ hoa) (hfixρ _ hob) ?_
    · rw [← map_mul, hna, map_one]
    · rw [← map_mul, hnb, map_one]
    · rw [← map_mul, ← map_mul, hab']
    · rw [← map_mul]
      exact hfixρ _ hab2
  exact ⟨n, ρ, by omega, hρ1 hα, hfixρ⟩

end SFCore

end CFSG.RankThree.PartTwo.Sec13.K135SF
