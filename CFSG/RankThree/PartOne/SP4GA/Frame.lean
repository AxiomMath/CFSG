module

public import CFSG.RankThree.PartOne.K1214.ZRows
public import CFSG.RankThree.PartOne.K1214.CycCtx
public import CFSG.RankThree.PartOne.SP4GA.Pointwise
import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne.SP4GA

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

variable {G : Type} [Group G]

theorem exists_generator_of_cyclic {H : Subgroup G} [IsCyclic ↥H] {n : ℕ} (hn : Nat.card ↥H = n) :
    ∃ x : G, Subgroup.zpowers x = H ∧ orderOf x = n := by
  obtain ⟨x₀, hx₀⟩ := IsCyclic.exists_generator (α := ↥H)
  refine ⟨(x₀ : G), ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      exact Subgroup.zpowers_le.2 x₀.2 hg
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hx₀ ⟨g, hg⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx₀, hn]

theorem dvd_of_pow_pow_eq_one {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {x : G}
    (hx : orderOf x = p ^ e) {i : ℤ} (h : (x ^ (p ^ (e - 1))) ^ i = 1) : (p : ℤ) ∣ i := by
  rw [← zpow_natCast x (p ^ (e - 1)), ← zpow_mul] at h
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h
  rw [hx] at h2
  have h3 : ((p ^ e : ℕ) : ℤ) = ((p ^ (e - 1) : ℕ) : ℤ) * (p : ℤ) := by
    rw [← Nat.cast_mul, ← pow_succ, Nat.sub_add_cancel he]
  rw [h3] at h2
  have h4 : ((p ^ (e - 1) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (pow_pos hp.pos _).ne'
  exact (mul_dvd_mul_iff_left h4).1 h2

theorem mem_zpowers_pow_of_pow_eq_one {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {x g : G}
    (hx : orderOf x = p ^ e) (hg : g ∈ Subgroup.zpowers x) (hgp : g ^ p = 1) :
    g ∈ Subgroup.zpowers (x ^ (p ^ (e - 1))) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h1 : x ^ (i * (p : ℤ)) = 1 := by rw [zpow_mul, zpow_natCast, hgp]
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hx] at h2
  have h3 : ((p ^ e : ℕ) : ℤ) = ((p ^ (e - 1) : ℕ) : ℤ) * (p : ℤ) := by
    rw [← Nat.cast_mul, ← pow_succ, Nat.sub_add_cancel he]
  rw [h3] at h2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨j, hj⟩ := (mul_dvd_mul_iff_right hp0).1 h2
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨j, ?_⟩
  rw [hj, zpow_mul, zpow_natCast]

structure Frame7 (p e : ℕ) (c : G) (E L P Q : Subgroup G) (x y : G) : Prop where
  two_le : 2 ≤ e
  setup : Setup p e P (E ⊓ L) c x y (x ^ (p ^ (e - 1))) (y ^ (p ^ (e - 1)))
  Q_eq : Q = Subgroup.zpowers y ⊔ Subgroup.zpowers x
  disj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥
  x_ord : orderOf x = p ^ e
  y_ord : orderOf y = p ^ e
  x_norm : ∀ u ∈ P, ∀ r ∈ Subgroup.zpowers x, u * r * u⁻¹ ∈ Subgroup.zpowers x
  y_norm : ∀ u ∈ P, ∀ z ∈ Subgroup.zpowers y, u * z * u⁻¹ ∈ Subgroup.zpowers y
  cx : c * x ≠ x * c
  cy : c * y ≠ y * c
  c_not_mem : c ∉ Q
  c_pow : c ^ p = 1
  P_pgroup : IsPGroup p ↥P
  Q_norm : ∀ u ∈ P, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q
  P_gen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f
  hr : ∃ r : ℤ, kap c x = (x ^ (p ^ (e - 1))) ^ r ∧ ¬ (p : ℤ) ∣ r
  hr' : ∃ r' : ℤ, kap c y = (y ^ (p ^ (e - 1))) ^ r'

section Exists

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {b : G}
  {K I X P Q : Subgroup G}

theorem exists_frame (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes)
    (hU5 : KF1214U5) (hZ : KF1214ZRow 7) (ctx : Fus12Ctx G p A c L E) (h7 : RowModel p L 7)
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) (hout : Out1214 p c L E I P Q)
    (hE3 : Nat.card E = p ^ 3) (hRc : ∃ r ∈ P ⊓ I, c * r ≠ r * c) :
    ∃ (e : ℕ) (x y : G), Frame7 p e c E L P Q x y := by
  classical
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hKR' := hKR G p A c L E ctx b K I X P Q hL hC hF
  obtain ⟨r, e, hr, he2, hEcard, ⟨φ⟩⟩ := R_equiv hRig h112 ctx hL hC hF hKR'
  have hr1 : r = 1 := by
    have h1 : p ^ (r + 2) = p ^ 3 := hEcard.symm.trans hE3
    have := Nat.pow_right_injective hp.two_le h1
    omega
  subst hr1
  obtain ⟨hZab, hZexp, hZY⟩ := hZ G p A c L E ctx h7 b K I X P Q hL hC hF hout.P_gen
  have hexp : Monoid.exponent ↥(P ⊓ I) = p ^ e := by
    rw [Monoid.exponent_eq_of_mulEquiv φ]
    exact exponent_pi_eq (by omega) le_rfl
  have hZcard := hZexp.trans hexp
  have hcd := cycData_of_ctx h112 ctx hL hC hF hout.P_gen hr he2 hEcard φ hZab hZcard hZY
  have hRcyc : IsCyclic ↥(P ⊓ I) := by
    have φ' : ↥(P ⊓ I) ≃* Multiplicative (ZMod (p ^ e)) := φ.trans (MulEquiv.piUnique _)
    exact isCyclic_of_surjective φ'.symm φ'.symm.surjective
  have hRcard : Nat.card ↥(P ⊓ I) = p ^ e := by
    rw [← IsCyclic.exponent_eq_card, hexp]
  obtain ⟨x, hxR, hxo⟩ := exists_generator_of_cyclic (H := P ⊓ I) hRcard
  have hZcyc : IsCyclic ↥(Subgroup.centralizer (I : Set G) ⊓ P) := hout.C_cyc
  obtain ⟨y, hyZ, hyo⟩ := exists_generator_of_cyclic (H := Subgroup.centralizer (I : Set G) ⊓ P)
    hZcard
  have hxmem : x ∈ P ⊓ I := hxR ▸ Subgroup.mem_zpowers x
  have hymem : y ∈ Subgroup.centralizer (I : Set G) ⊓ P := hyZ ▸ Subgroup.mem_zpowers y
  have he1 : 1 ≤ e := by omega
  have hcx : c * x ≠ x * c := by
    intro h
    obtain ⟨r₀, hr₀, hne⟩ := hRc
    rw [← hxR] at hr₀
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr₀
    exact hne ((Commute.zpow_right (show Commute c x from h) k).eq)
  have hcy : c * y ≠ y * c := by
    intro h
    have hZC : (Subgroup.centralizer (I : Set G) ⊓ P) ⊓ Subgroup.centralizer ({c} : Set G) =
        Subgroup.centralizer (I : Set G) ⊓ P := by
      apply le_antisymm inf_le_left
      intro z hz
      refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
      rw [← hyZ] at hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.zpow_left (show Commute y c from h.symm) k).eq
    rw [hZC] at hZY
    have hpos : 0 < Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) := Nat.card_pos
    have : 1 * Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) =
        p * Nat.card ↥(Subgroup.centralizer (I : Set G) ⊓ P) := by rw [one_mul]; exact hZY
    have := Nat.eq_of_mul_eq_mul_right hpos this
    exact hp.one_lt.ne this
  have hPE : P ≤ Subgroup.normalizer (E : Set G) := P_le_normalizer_of_omega hout.omega
  have hn12 : ¬ RowModel p L 12 := hU5 G p A c L E ctx
  have hnH := not_dvd_torusImage ctx hn12
  have hcE : c ∈ E := c_mem_E ctx
  have hEel := ctx.hyp.E_elem
  have hEpow : ∀ z ∈ E, z ^ p = 1 := fun z hz => Sec12Three.pow_eq_one_of_mem_E ctx.hyp hz
  have hQ : Q = Subgroup.zpowers y ⊔ Subgroup.zpowers x := by
    rw [hC.Q_eq, hyZ, hxR]
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [hxR, hyZ]
    exact hcd.ZR_bot
  have hxy : x * y = y * x := (hcd.ZR y hymem x hxmem).symm
  have hxn : ∀ u ∈ P, ∀ r ∈ Subgroup.zpowers x, u * r * u⁻¹ ∈ Subgroup.zpowers x := by
    rw [hxR]
    exact hcd.R_norm
  have hyn : ∀ u ∈ P, ∀ z ∈ Subgroup.zpowers y, u * z * u⁻¹ ∈ Subgroup.zpowers y := by
    rw [hyZ]
    exact hcd.Z_norm
  have hxP : x ∈ P := hxmem.1
  have hyP : y ∈ P := hymem.2
  have hβKp : (x ^ (p ^ (e - 1))) ^ p = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel he1, ← hxo]
    exact pow_orderOf_eq_one x
  have hβbp : (y ^ (p ^ (e - 1))) ^ p = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel he1, ← hyo]
    exact pow_orderOf_eq_one y
  have hxQ : ∀ k : ℤ, x ^ k ∈ Q := fun k => by
    rw [hQ]
    exact Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k)
  have hyQ : ∀ k : ℤ, y ^ k ∈ Q := fun k => by
    rw [hQ]
    exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k)
  have hβK_mem : x ^ (p ^ (e - 1)) ∈ E ⊓ L := by
    have h1 : x ^ (p ^ (e - 1)) ∈ Q := by
      have := hxQ (((p ^ (e - 1) : ℕ)) : ℤ)
      rwa [zpow_natCast] at this
    have h2 : x ^ (p ^ (e - 1)) ∈ E := by
      rw [← hout.omega]
      exact Subgroup.subset_closure ⟨pow_mem hxP _, hβKp⟩
    rw [← hout.QE]
    exact ⟨h1, h2⟩
  have hβb_mem : y ^ (p ^ (e - 1)) ∈ E ⊓ L := by
    have h1 : y ^ (p ^ (e - 1)) ∈ Q := by
      have := hyQ (((p ^ (e - 1) : ℕ)) : ℤ)
      rwa [zpow_natCast] at this
    have h2 : y ^ (p ^ (e - 1)) ∈ E := by
      rw [← hout.omega]
      exact Subgroup.subset_closure ⟨pow_mem hyP _, hβbp⟩
    rw [← hout.QE]
    exact ⟨h1, h2⟩
  have hindep : ∀ i j : ℤ, (x ^ (p ^ (e - 1))) ^ i * (y ^ (p ^ (e - 1))) ^ j = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j h
    have h1 : (x ^ (p ^ (e - 1))) ^ i = ((y ^ (p ^ (e - 1))) ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : (x ^ (p ^ (e - 1))) ^ i ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y :=
      ⟨Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) _, by
        rw [h1]
        exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.pow_mem _
          (Subgroup.mem_zpowers y) _) _)⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    have h3 : (y ^ (p ^ (e - 1))) ^ j = 1 := by
      rw [h2] at h1
      exact inv_eq_one.1 h1.symm
    exact ⟨dvd_of_pow_pow_eq_one hp he1 hxo h2, dvd_of_pow_pow_eq_one hp he1 hyo h3⟩
  have hkapB : ∀ u ∈ P, kap c u ∈ E ⊓ L := fun u hu => mod_B ctx hnH hC hPE hu hcE
  have hsetup : Setup p e P (E ⊓ L) c x y (x ^ (p ^ (e - 1))) (y ^ (p ^ (e - 1))) :=
    { hp := hp
      hp2 := hp2
      he := he1
      c_mem := hcd.c_P
      x_mem := hxP
      y_mem := hyP
      B_central := fun β hβ u hu => fix_B ctx hnH hC hPE hu hβ
      B_comm := fun β hβ β' hβ' => by
        have := hEel.is_comm.comm ⟨β, hβ.1⟩ ⟨β', hβ'.1⟩
        exact congrArg Subtype.val this
      kap_mem := hkapB
      xy := hxy
      βK_def := rfl
      βb_def := rfl
      βK_mem := hβK_mem
      βb_mem := hβb_mem
      βK_p := hβKp
      βb_p := hβbp
      indep := hindep }
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℤ, kap c x = (x ^ (p ^ (e - 1))) ^ r₁ := by
    have h1 : kap c x ∈ Subgroup.zpowers x := by
      have e1 : kap c x = x * (c * x⁻¹ * c⁻¹) := by unfold kap; group
      rw [e1]
      have h2 : c * x⁻¹ * c⁻¹ ∈ P ⊓ I := hcd.R_norm c hcd.c_P x⁻¹ ((P ⊓ I).inv_mem hxmem)
      rw [← hxR] at h2
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) h2
    have h2 : (kap c x) ^ p = 1 := hEpow _ (hkapB x hxP).1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      (mem_zpowers_pow_of_pow_eq_one hp he1 hxo h1 h2)
    exact ⟨k, hk.symm⟩
  have hr₁p : ¬ (p : ℤ) ∣ r₁ := by
    intro hdvd
    have h1 : (x ^ (p ^ (e - 1))) ^ r₁ = 1 := zpow_eq_one_of_dvd hβKp hdvd
    rw [h1] at hr₁
    apply hcx
    have h2 : x * c * x⁻¹ * c⁻¹ = 1 := hr₁
    have h3 : x * c * x⁻¹ = c := mul_inv_eq_one.1 h2
    have h4 : x * c = c * x := by
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
    exact h4.symm
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : ℤ, kap c y = (y ^ (p ^ (e - 1))) ^ r₂ := by
    have h1 : kap c y ∈ Subgroup.zpowers y := by
      have e1 : kap c y = y * (c * y⁻¹ * c⁻¹) := by unfold kap; group
      rw [e1]
      have h2 : c * y⁻¹ * c⁻¹ ∈ Subgroup.centralizer (I : Set G) ⊓ P :=
        hcd.Z_norm c hcd.c_P y⁻¹ ((Subgroup.centralizer (I : Set G) ⊓ P).inv_mem hymem)
      rw [← hyZ] at h2
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers y) h2
    have h2 : (kap c y) ^ p = 1 := hEpow _ (hkapB y hyP).1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
      (mem_zpowers_pow_of_pow_eq_one hp he1 hyo h1 h2)
    exact ⟨k, hk.symm⟩
  exact ⟨e, x, y,
    { two_le := he2
      setup := hsetup
      Q_eq := hQ
      disj := hdisj
      x_ord := hxo
      y_ord := hyo
      x_norm := hxn
      y_norm := hyn
      cx := hcx
      cy := hcy
      c_not_mem := hcd.c_Q
      c_pow := hcd.c_p
      P_pgroup := hcd.P_p
      Q_norm := hcd.Q_norm
      P_gen := hout.P_gen
      hr := ⟨r₁, hr₁, hr₁p⟩
      hr' := ⟨r₂, hr₂⟩ }⟩

end Exists

end CFSG.RankThree.PartOne.SP4GA
