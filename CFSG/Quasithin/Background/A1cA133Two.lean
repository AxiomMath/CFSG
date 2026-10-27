module

public import CFSG.Quasithin.Background.A1cA133Lemmas
public import CFSG.Quasithin.Background.A1cKlein
public import CFSG.Quasithin.Background.A1cRankLemmas
public import CFSG.Quasithin.Background.A1cSL2Facts

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped MatrixGroups commutatorElement

namespace A1c

section Prelim

variable {L : Type*} [Group L]

theorem GL2_eq_one_or_neg_one_of_sq_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {g : GL (Fin 2) F} (hg : g * g = 1) (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1) :
    g = 1 ∨ g = -1 := by
  by_contra hcon
  push Not at hcon
  have hM : (g : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
    simpa using congrArg Units.val hg
  have h1 : (g : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h => hcon.1 (Units.ext h)
  have hn : (g : Matrix (Fin 2) (Fin 2) F) ≠ -1 := fun h => hcon.2 (Units.ext (by simpa using h))
  have h3 := det_eq_neg_one_of_sq_eq_one hM h1 hn
  rw [hdet] at h3
  apply h2
  linear_combination h3

variable {p : ℕ} [Fact p.Prime]

theorem exists_mem_not_mem_centerOf {P : Subgroup L} [Finite L] (hP : IsPOnePlusTwo p ↥P) :
    ∃ y ∈ P, y ∉ centerOf P := by
  by_contra hcon
  push Not at hcon
  have hle : P ≤ centerOf P := hcon
  have h1 := Subgroup.card_le_of_le hle
  rw [card_centerOf hP.1, hP.2.1] at h1
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h2 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
  omega

theorem mem_centerOf_of_sq_mem {P : Subgroup L} (hp2 : p ≠ 2) (hPp : ∀ y ∈ P, y ^ p = 1) {y : L}
    (hy : y ∈ P) (hsq : y * y ∈ centerOf P) : y ∈ centerOf P := by
  obtain ⟨j, hj⟩ : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h1 : y = (y * y) ^ (j + 1) := by
    have h2 : y ^ p = 1 := hPp y hy
    rw [hj] at h2
    calc y = y ^ (2 * j + 1) * y := by rw [h2, one_mul]
      _ = (y * y) ^ (j + 1) := by rw [← sq, ← pow_mul, ← pow_succ]; congr 1
  rw [h1]
  exact (centerOf P).pow_mem hsq _

theorem two_lt_pRank_of_centralizing_element [Finite L] {P : Subgroup L}
    (hP : IsPOnePlusTwo p ↥P) {x : L} (hxp : orderOf x = p) (hxc : ∀ y ∈ P, x * y = y * x)
    (hxP : x ∉ P) : 2 < pRank p (⊤ : Subgroup L) := by
  classical
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hPp : ∀ y ∈ P, y ^ p = 1 := fun y hy => by
    simpa using congrArg Subtype.val (hPexp ⟨y, hy⟩)
  set Z : Subgroup L := centerOf P with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZcard : Nat.card Z = p := card_centerOf hext
  have hZc : ∀ z ∈ Z, ∀ y ∈ P, y * z = z * y := fun z hz y hy => (mem_centerOf_iff.1 hz).2 y hy
  obtain ⟨y, hyP, hyZ⟩ := exists_mem_not_mem_centerOf ⟨hext, hPcard, hPexp⟩
  have hyo : orderOf y = p := orderOf_eq_prime (hPp y hyP) (fun h => hyZ (h ▸ Z.one_mem))
  have hZel : IsElemAbelian p Z :=
    ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZP b.2)).symm⟩⟩, fun z hz => hPp z (hZP hz)⟩
  obtain ⟨hE1, hE1card⟩ := exists_elemAbelian_sup_zpowers hZel hyo
    (fun e he => (hZc e he y hyP).symm) hyZ
  have hE1P : Z ⊔ Subgroup.zpowers y ≤ P := sup_le hZP (Subgroup.zpowers_le.2 hyP)
  have hxE : x ∉ Z ⊔ Subgroup.zpowers y := fun h => hxP (hE1P h)
  obtain ⟨hE2, hE2card⟩ := exists_elemAbelian_sup_zpowers hE1 hxp
    (fun e he => (hxc e (hE1P he)).symm) hxE
  have h3 := le_pRank (Fact.out : p.Prime)
    (le_top : (Z ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers x ≤ ⊤) hE2 (k := 3)
    (by rw [hE2card, hE1card, hZcard]; ring)
  omega

theorem exists_mul_mem_centralizer_of_trivial_action {S : Type*} [Group S] (π : L →* S)
    (hπ : Function.Surjective π) (hS : Group.IsPerfect S) {P : Subgroup L} (hker : π.ker = P)
    (hZcen : ∀ g : L, ∀ z ∈ centerOf P, g * z = z * g)
    (hall : ∀ g : L, ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ centerOf P) (g : L) :
    ∃ y ∈ P, y⁻¹ * g ∈ Subgroup.centralizer (P : Set L) := by
  classical
  set Z := centerOf P with hZ
  have hZP : Z ≤ P := inf_le_left
  have hZP' : ∀ z ∈ Z, ∀ y ∈ P, y * z = z * y := fun z hz y hy => (mem_centerOf_iff.1 hz).2 y hy
  let _ : CommGroup ↥Z := { (inferInstance : Group ↥Z) with
    mul_comm := fun a b => Subtype.ext (hZP' a a.2 b (hZP b.2)).symm }
  have key2 : ∀ (g a b : L), a ∈ P → b ∈ P →
      g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by
    intro g a b ha hb
    have hz' := hall g b hb
    have h1 : a * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * a := hZP' _ hz' a ha
    calc g * (a * b) * g⁻¹ * (a * b)⁻¹
        = (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
      _ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by rw [h1]; group
  have key1 : ∀ (g g' a : L), a ∈ P →
      (g * g') * a * (g * g')⁻¹ * a⁻¹ = (g * a * g⁻¹ * a⁻¹) * (g' * a * g'⁻¹ * a⁻¹) := by
    intro g g' a ha
    have hz1 := hall g' a ha
    have hgz1 : g * (g' * a * g'⁻¹ * a⁻¹) * g⁻¹ = g' * a * g'⁻¹ * a⁻¹ := by
      rw [hZcen g _ hz1]; group
    have hz2 := hall g a ha
    have hcz := hZP' _ hz1 _ (hZP hz2)
    calc (g * g') * a * (g * g')⁻¹ * a⁻¹
        = g * (g' * a * g'⁻¹ * a⁻¹) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) := by group
      _ = (g' * a * g'⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) := by rw [hgz1]
      _ = (g * a * g⁻¹ * a⁻¹) * (g' * a * g'⁻¹ * a⁻¹) := hcz.symm
  let ψ : L → (↥P →* ↥Z) := fun g =>
    { toFun := fun y => ⟨g * y * g⁻¹ * y⁻¹, hall g y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => Subtype.ext (by simpa using key2 g y y' y.2 y'.2) }
  let Φ : L →* (↥P →* ↥Z) :=
    { toFun := ψ
      map_one' := MonoidHom.ext fun y => Subtype.ext (by simp [ψ])
      map_mul' := fun g g' => MonoidHom.ext fun y => Subtype.ext (by
        simpa [ψ] using key1 g g' y y.2) }
  let R : Subgroup (↥P →* ↥Z) := (Φ.comp P.subtype).range
  let F : L →* ((↥P →* ↥Z) ⧸ R) := (QuotientGroup.mk' R).comp Φ
  have hF : π.ker ≤ F.ker := by
    intro k hk
    rw [hker] at hk
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).2 ⟨⟨k, hk⟩, rfl⟩
  have hF1 := hom_eq_one_of_perfect_quotient π hπ hS F hF
  have hg : Φ g ∈ R := by
    have h1 : F g = 1 := by rw [hF1]; rfl
    exact (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨⟨y, hyP⟩, hy⟩ := hg
  refine ⟨y, hyP, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
  have h1 : Φ (y⁻¹ * g) = 1 := by
    rw [map_mul, map_inv]
    have : Φ y = Φ g := hy
    rw [this, inv_mul_cancel]
  have h2 := congrArg (fun f : ↥P →* ↥Z => ((f ⟨h, hh⟩ : ↥Z) : L)) h1
  have h3 : (y⁻¹ * g) * h * (y⁻¹ * g)⁻¹ * h⁻¹ = 1 := h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

theorem mul_comm_mem_centerOf {P : Subgroup L} {u v : L} (hu : u ∈ P) (h : u * v ∈ centerOf P) :
    v * u ∈ centerOf P := by
  have h2 : u * (u * v) = (u * v) * u := (mem_centerOf_iff.1 h).2 u hu
  have h3 : v * u = u * v := by
    calc v * u = u⁻¹ * ((u * v) * u) := by group
      _ = u⁻¹ * (u * (u * v)) := by rw [h2]
      _ = u * v := by group
  rw [h3]
  exact h

theorem coe_mem_centerOf_iff {P : Subgroup L} (u : ↥P) :
    (u : L) ∈ centerOf P ↔ u ∈ Subgroup.center ↥P := by
  rw [mem_centerOf_iff, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, h⟩ g
    exact Subtype.ext (h g g.2)
  · intro h
    exact ⟨u.2, fun y hy => congrArg Subtype.val (h ⟨y, hy⟩)⟩

@[expose] def actV (P : Subgroup L) [P.Normal] : L →* MulAut (↥P ⧸ Subgroup.center ↥P) :=
  (CFSG.SectionRank.Ccomm.autQuotient (Subgroup.center ↥P)).comp MulAut.conjNormal

theorem actV_apply_mk {P : Subgroup L} [P.Normal] (g : L) (y : ↥P) :
    actV P g (y : ↥P ⧸ Subgroup.center ↥P) =
      ((MulAut.conjNormal g y : ↥P) : ↥P ⧸ Subgroup.center ↥P) := rfl

theorem mk_eq_mk_iff {P : Subgroup L} (a b : ↥P) :
    ((a : ↥P ⧸ Subgroup.center ↥P) = (b : ↥P ⧸ Subgroup.center ↥P)) ↔
      (a : L)⁻¹ * (b : L) ∈ centerOf P := by
  rw [QuotientGroup.eq, ← coe_mem_centerOf_iff]
  simp

theorem actV_eq_one_iff {P : Subgroup L} [P.Normal] (g : L) :
    actV P g = 1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ centerOf P := by
  constructor
  · intro h y hy
    have h2 : actV P g (⟨y, hy⟩ : ↥P) = (⟨y, hy⟩ : ↥P) := by rw [h]; rfl
    rw [actV_apply_mk, mk_eq_mk_iff, MulAut.conjNormal_apply] at h2
    have hu : g * y * g⁻¹ ∈ P := Subgroup.Normal.conj_mem ‹P.Normal› y hy g
    exact (inv_mul_mem_iff_mul_inv_mem hu hy).1 h2
  · intro h
    apply MulEquiv.ext
    intro w
    induction w using QuotientGroup.induction_on with
    | H y =>
      rw [actV_apply_mk]
      show _ = ((y : ↥P) : ↥P ⧸ Subgroup.center ↥P)
      rw [mk_eq_mk_iff, MulAut.conjNormal_apply]
      have hy := y.2
      have hu : g * (y : L) * g⁻¹ ∈ P := Subgroup.Normal.conj_mem ‹P.Normal› y hy g
      exact (inv_mul_mem_iff_mul_inv_mem hu hy).2 (h y hy)

theorem actV_eq_inv_iff {P : Subgroup L} [P.Normal] (g : L) :
    (∀ w : ↥P ⧸ Subgroup.center ↥P, actV P g w = w⁻¹) ↔
      ∀ y ∈ P, g * y * g⁻¹ * y ∈ centerOf P := by
  have key : ∀ (y : ↥P), actV P g (y : ↥P ⧸ Subgroup.center ↥P) =
      ((y : ↥P ⧸ Subgroup.center ↥P))⁻¹ ↔ (g * y * g⁻¹) * y ∈ centerOf P := by
    intro y
    have hy := y.2
    have hu : g * (y : L) * g⁻¹ ∈ P := Subgroup.Normal.conj_mem ‹P.Normal› y hy g
    rw [actV_apply_mk, ← QuotientGroup.mk_inv, mk_eq_mk_iff, MulAut.conjNormal_apply]
    show (g * (y : L) * g⁻¹)⁻¹ * (y : L)⁻¹ ∈ centerOf P ↔ _
    have : (g * (y : L) * g⁻¹)⁻¹ * (y : L)⁻¹ = (y * (g * y * g⁻¹))⁻¹ := by group
    rw [this, Subgroup.inv_mem_iff]
    exact ⟨fun h1 => mul_comm_mem_centerOf hy h1, fun h1 => mul_comm_mem_centerOf hu h1⟩
  constructor
  · intro h y hy
    exact (key ⟨y, hy⟩).1 (h _)
  · intro h w
    induction w using QuotientGroup.induction_on with
    | H y => exact (key y).2 (h y y.2)

end Prelim

section Main

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [Group L] [Finite L]

theorem two_lt_pRank_of_surjective_sl2 (hp5 : 5 ≤ p) {P : Subgroup L} [P.Normal]
    (hP : IsPOnePlusTwo p ↥P) (π : L →* SL(2, ZMod p)) (hπ : Function.Surjective π)
    (hker : π.ker = P) : 2 < pRank p (⊤ : Subgroup L) := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hP' := hP
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hperf := sl2_isPerfect hp5
  have hPg : IsPGroup p ↥P := CFSG.IsExtraspecial.isPGroup p ↥P
  have hPp : ∀ y ∈ P, y ^ p = 1 := fun y hy => by
    simpa using congrArg Subtype.val (hPexp ⟨y, hy⟩)
  set Z := centerOf P with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZcard : Nat.card Z = p := card_centerOf hext
  have hZcyc : IsCyclic ↥Z := isCyclic_of_prime_card hZcard
  have hZcen : ∀ g : L, ∀ z ∈ Z, g * z = z * g := fun g z hz =>
    centerOf_le_center π hπ hperf hker hZcyc g hz
  have hZexp : ∀ z ∈ Z, z ^ p = 1 := fun z hz => hPp z (hZP hz)
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
  let Θ : L →* GL (Fin 2) (ZMod p) := ε.toMonoidHom.comp (actV P)
  have hΘ1 : ∀ g : L, Θ g = 1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ Z := by
    intro g
    rw [← actV_eq_one_iff]
    show ε (actV P g) = 1 ↔ _
    rw [← map_one ε]
    exact ε.injective.eq_iff
  have hΘneg : ∀ g : L, Θ g = -1 ↔ ∀ y ∈ P, g * y * g⁻¹ * y ∈ Z := by
    intro g
    rw [← actV_eq_inv_iff]
    exact CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e (actV P g)
  have hPK : ∀ y ∈ P, Θ y = 1 := fun y hy =>
    (hΘ1 y).2 fun y' hy' => commutator_mem_centerOf hext hy hy'
  have hdet : ∀ g : L, ((Θ g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    have hf : (Matrix.GeneralLinearGroup.det.comp Θ) = 1 :=
      hom_eq_one_of_perfect_quotient π hπ hperf _ (by
        intro k hk
        rw [hker] at hk
        rw [MonoidHom.mem_ker]
        simp [hPK k hk])
    intro g
    have := congrArg (fun f : L →* (ZMod p)ˣ => ((f g : (ZMod p)ˣ) : ZMod p)) hf
    simpa using this
  have hinv : ∀ g : L, Θ g * Θ g = 1 → Θ g = 1 ∨ Θ g = -1 := fun g hg =>
    GL2_eq_one_or_neg_one_of_sq_eq_one h2 hg (hdet g)
  have : Fact (1 < p) := ⟨hp1⟩
  let K : Subgroup L := Θ.ker
  have hKn : K.Normal := MonoidHom.normal_ker Θ
  have hPK' : P ≤ K := fun y hy => hPK y hy
  have hpre : ∀ g : L, π g ∈ K.map π → g ∈ K := by
    rintro g ⟨k, hk, hkg⟩
    have h1 : k⁻¹ * g ∈ P := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    have h3 : g = k * (k⁻¹ * g) := by group
    rw [h3]
    exact K.mul_mem hk (hPK' h1)
  have hKπn : (K.map π).Normal := Subgroup.Normal.map hKn π hπ
  have hπP : ∀ y ∈ P, π y = 1 := fun y hy => by
    rw [← MonoidHom.mem_ker, hker]; exact hy
  have hπmem : ∀ y, π y = 1 → y ∈ P := fun y hy => by
    rw [← hker]; exact hy
  obtain ⟨c₀, hc₀⟩ := hπ (sl2U p)
  obtain ⟨w₀, hw₀⟩ := hπ (sl2W p)
  have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
  have h4 : (2 : ZMod p) = ((4 : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
    rw [show ((4 : ℕ) : ZMod p) = 2 * 2 by norm_num, mul_assoc, h2inv, mul_one]
  obtain ⟨d₀, hd₀⟩ := hπ (sl2Diag p 2 (2 : ZMod p)⁻¹ h2inv)
  have hdU : sl2Diag p 2 (2 : ZMod p)⁻¹ h2inv * sl2U p =
      sl2U p ^ 4 * sl2Diag p 2 (2 : ZMod p)⁻¹ h2inv :=
    sl2Diag_mul_sl2U 2 _ h2inv 4 h4
  have hdπ' : π d₀ * sl2U p = sl2U p ^ 4 * π d₀ := by rw [hd₀]; exact hdU
  rcases normal_le_center_or_eq_top hp5 (K.map π) with hcen | htop
  ·
    have hcenter : ∀ g ∈ K.map π, g = 1 ∨ g = sl2NegOne p := fun g hg =>
      eq_one_or_eq_sl2NegOne_of_mem_center (hcen hg)
    by_cases hneg : sl2NegOne p ∈ K.map π
    ·
      exfalso
      have hw₀sq : Θ w₀ * Θ w₀ = 1 := by
        have : w₀ * w₀ ∈ K := hpre _ (by rw [map_mul, hw₀, sl2W_mul_self]; exact hneg)
        rw [← map_mul]; exact this
      have hΘw : Θ w₀ = -1 := by
        rcases hinv w₀ hw₀sq with h | h
        · exfalso
          have h1 : sl2W p ∈ K.map π := ⟨w₀, h, hw₀⟩
          rcases hcenter _ h1 with h' | h'
          · exact sl2W_ne_one h'
          · exact sl2W_ne_negOne h'
        · exact h
      have hu₁ : c₀ * w₀ * c₀⁻¹ * w₀⁻¹ ∈ K := by
        show Θ (c₀ * w₀ * c₀⁻¹ * w₀⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hΘw]
        have hc : Θ c₀ * (-1) = (-1) * Θ c₀ := by simp
        rw [hc]
        simp
      have h3 := hcenter _ ⟨_, hu₁, rfl⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc₀, hw₀] at h3
      rcases h3 with h3 | h3
      · apply sl2U_mul_sl2W_ne (p := p)
        rw [mul_inv_eq_one] at h3
        exact (mul_inv_eq_iff_eq_mul.1 h3)
      · apply sl2U_mul_sl2W_ne' (p := p)
        have h5 := mul_inv_eq_iff_eq_mul.1 h3
        have h6 := mul_inv_eq_iff_eq_mul.1 h5
        rw [h6, mul_assoc]
    ·
      obtain ⟨t, ht2, htπ⟩ := exists_involution_lift hπ (by rw [hker]; exact hPg) hp2
        (orderOf_sl2NegOne hp2)
      have ht2' : t ^ 2 = 1 := ht2 ▸ pow_orderOf_eq_one t
      have htK : t ∉ K := fun h => hneg (by rw [← htπ]; exact ⟨t, h, rfl⟩)
      have hΘt : Θ t = -1 := by
        rcases hinv t (by rw [← map_mul, ← sq, ht2', map_one]) with h | h
        · exact absurd h htK
        · exact h
      have ht : ∀ y ∈ P, t * y * t⁻¹ * y ∈ Z := (hΘneg t).1 hΘt
      have hlift : ∀ g : L, ∃ c : L, c ∈ Subgroup.centralizer ({t} : Set L) ∧ π c = π g := by
        intro g
        have hg : g * t * g⁻¹ * t⁻¹ ∈ P := by
          apply hπmem
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, htπ, sl2NegOne_comm]
          group
        obtain ⟨y, hy, hc⟩ := exists_mul_mem_centralizer hp2 hPg ht2' hg
        refine ⟨y⁻¹ * g, hc, ?_⟩
        rw [map_mul, map_inv, hπP y hy, inv_one, one_mul]
      obtain ⟨c, hcC, hcπ⟩ := hlift c₀
      obtain ⟨d, hdC, hdπ⟩ := hlift d₀
      have hCZ : ∀ y ∈ Subgroup.centralizer ({t} : Set L), π y = 1 → y ∈ Z := by
        intro y hyC hy1
        have hyP := hπmem y hy1
        have hty : t * y = y * t := Subgroup.mem_centralizer_iff.1 hyC t (Set.mem_singleton t)
        have h1 := ht y hyP
        rw [mul_inv_eq_iff_eq_mul.2 hty] at h1
        exact mem_centerOf_of_sq_mem hp2 hPp hyP h1
      have hcp : c ^ p = 1 := pow_eq_one_of_lift hp5 π hZcen hZexp hCZ hcC hdC
        (hcπ.trans hc₀) (by rw [hdπ]; exact hdπ')
      have hc1 : c ≠ 1 := fun h => sl2U_ne_one (p := p) (by rw [← hc₀, ← hcπ, h, map_one])
      have hxp : orderOf c = p := orderOf_eq_prime hcp hc1
      have hxV : ∃ y ∈ P, c * y * c⁻¹ * y⁻¹ ∉ Z := by
        by_contra hcon
        push Not at hcon
        have hcK : c ∈ K := (hΘ1 c).2 hcon
        have h1 : sl2U p ∈ K.map π := ⟨c, hcK, hcπ.trans hc₀⟩
        rcases hcenter _ h1 with h' | h'
        · exact sl2U_ne_one h'
        · exact sl2U_ne_negOne h'
      exact two_lt_pRank_of_inverting_element hp2 hP' ht hcC hxp hxV
  ·
    have hall : ∀ g : L, ∀ y ∈ P, g * y * g⁻¹ * y⁻¹ ∈ Z := fun g y hy =>
      (hΘ1 g).1 (hpre g (by rw [htop]; trivial)) y hy
    have hlift : ∀ g : L, ∃ c : L, c ∈ Subgroup.centralizer (P : Set L) ∧ π c = π g := by
      intro g
      obtain ⟨y, hy, hc⟩ :=
        exists_mul_mem_centralizer_of_trivial_action π hπ hperf hker hZcen hall g
      refine ⟨y⁻¹ * g, hc, ?_⟩
      rw [map_mul, map_inv, hπP y hy, inv_one, one_mul]
    obtain ⟨c, hcC, hcπ⟩ := hlift c₀
    obtain ⟨d, hdC, hdπ⟩ := hlift d₀
    have hCZ : ∀ y ∈ Subgroup.centralizer (P : Set L), π y = 1 → y ∈ Z := fun y hyC hy1 =>
      ⟨hπmem y hy1, hyC⟩
    have hcp : c ^ p = 1 := pow_eq_one_of_lift hp5 π hZcen hZexp hCZ hcC hdC
      (hcπ.trans hc₀) (by rw [hdπ]; exact hdπ')
    have hc1 : c ≠ 1 := fun h => sl2U_ne_one (p := p) (by rw [← hc₀, ← hcπ, h, map_one])
    have hxp : orderOf c = p := orderOf_eq_prime hcp hc1
    have hxP : c ∉ P := fun h => sl2U_ne_one (p := p) (by rw [← hc₀, ← hcπ]; exact hπP c h)
    exact two_lt_pRank_of_centralizing_element hP' hxp
      (fun y hy => (Subgroup.mem_centralizer_iff.1 hcC y hy).symm) hxP

end Main

end A1c

section A133Two

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [Group L] [Finite L]

theorem two_lt_pRank_of_quotient_sl2 (hp4 : 3 < p) (P : Subgroup L) [P.Normal]
    (hP : IsPOnePlusTwo p ↥P) (hL : Nonempty (L ⧸ P ≃* SL(2, ZMod p))) :
    2 < pRank p (⊤ : Subgroup L) := by
  obtain ⟨e⟩ := hL
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp.out (by decide)
  refine A1c.two_lt_pRank_of_surjective_sl2 hp5 hP (e.toMonoidHom.comp (QuotientGroup.mk' P))
    (e.surjective.comp (QuotientGroup.mk'_surjective P)) ?_
  ext g
  rw [MonoidHom.mem_ker]
  show e (g : L ⧸ P) = 1 ↔ g ∈ P
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

end A133Two

end CFSG.Quasithin
