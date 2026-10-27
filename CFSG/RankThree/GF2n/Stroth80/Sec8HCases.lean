module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HCount
public import CFSG.RankThree.GF2n.Stroth80.Sec8HFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec8HGen
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def sec8MoveSub (N I Y : Subgroup G) (hN : N ≤ Subgroup.normalizer (I : Set G)) :
    Subgroup G where
  carrier := {l | l ∈ N ∧ ∀ y ∈ Y, ⁅y, l⁆ ∈ I}
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨N.mul_mem haN hbN, fun y hy => ?_⟩
    have e : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact I.mul_mem (ha y hy) ((Subgroup.mem_normalizer_iff.mp (hN haN) _).mp (hb y hy))
  one_mem' := ⟨N.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨N.inv_mem haN, fun y hy => ?_⟩
    have e : ⁅y, a⁻¹⁆ = (a⁻¹ * ⁅y, a⁆ * a)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine I.inv_mem ?_
    have := (Subgroup.mem_normalizer_iff.mp (hN (N.inv_mem haN)) _).mp (ha y hy)
    simpa using this

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_caseB (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {m : ℕ}
    (hmSp : SpMNat hc t m) {g : G} (hgM : g ∈ M)
    (hgL : g ∈ Subgroup.normalizer (LB M Q B : Set G))
    (hVW : ∀ v ∈ Vt M (LB M Q B) B Z t, g * v * g⁻¹ ∈ Sec8W1 M Q Z B t r)
    (hcard : Nat.card Z ^ (m + 1) ≤
      Nat.card ↥(Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)))
    (hAc : ¬ ∀ x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t),
      x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) : False := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hgi : g⁻¹ ∈ M := M.inv_mem hgM
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hRV := hc.Rt_normalizes_Vt ht
  have hinvV₁ : ∀ l ∈ LB M Q B, ∀ x ∈ Sec8V1 M Q Z B t r,
      l * x * l⁻¹ ∈ Sec8V1 M Q Z B t r := by
    intro l hl x hx
    exact conj_mem_of_conjSubgroup_eq
      (sec8InvStatement_holds G M Q Z B hc n t hs r hr l (hLR hl)).1 hx
  have hinvV : ∀ l ∈ LB M Q B, ∀ x ∈ Vt M (LB M Q B) B Z t,
      l * x * l⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hRV (hLR hl)) x).mp hx
  have hgLmem : ∀ l ∈ LB M Q B, g * l * g⁻¹ ∈ LB M Q B :=
    fun l hl => (Subgroup.mem_normalizer_iff.mp hgL l).mp hl
  have hgLmem' : ∀ l ∈ LB M Q B, g⁻¹ * l * g ∈ LB M Q B := by
    intro l hl
    refine (Subgroup.mem_normalizer_iff.mp hgL (g⁻¹ * l * g)).mpr ?_
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group]
    exact hl
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, hhyp, hBiff, hψ, nn, γ, M₀, hglob, θ, hθ⟩ :=
    sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  obtain ⟨A, A₀, hAmem, hA₀mem, hA₀A, hdim⟩ :=
    sec8_exists_codim_one h310chi h53.1 hc hs hr hglob
  have hV₁K : ∀ (c : GaloisField 2 nn) (e : M₀.E), e ∈ M₀.img (Sec8V1 M Q Z B t r) →
      c • e ∈ M₀.img (Sec8V1 M Q Z B t r) :=
    fun c e he => (hAmem _).mp (A.smul_mem c ((hAmem e).mpr he))
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := sec8_Z_le_V1 hc t r
  have hV₁Q : Sec8V1 M Q Z B t r ≤ Q := sec8_V1_le_Q hc t r
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := by
    show Vt M (LB M Q B) B Z t ≤ ((Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t) ⊓
      ((Q ⊓ QB (conjSubgroup r B)) ⊔ Vt M (LB M Q B) B Z t)
    exact le_inf le_sup_right le_sup_right
  have hZg : conjSubgroup g⁻¹ Z = Z := hc.conj_Z_eq hgi
  set D₀ : Subgroup G := Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Sec8V1 M Q Z B t r) with hD₀
  have hZD₀ : Z ≤ D₀ := le_inf hZV (hZg.symm.le.trans (Subgroup.map_mono hZV₁))
  have hD₀V : D₀ ≤ Vt M (LB M Q B) B Z t := inf_le_left
  have hDK₀ : ∀ (c : K) (d : ↥(Vt M (LB M Q B) B Z t)), (d : G) ∈ D₀ →
      ∃ d' : ↥(Vt M (LB M Q B) B Z t), (d' : G) ∈ D₀ ∧ secVec ψ d' = c • secVec ψ d :=
    sec8_inter_smul_closed (hc := hc) hglob θ ψ hθ hZV₁ hV₁Q hV₁K hgi
  have hgBZ : conjSubgroup g B ⊔ Z = B ⊔ Z := by
    have h1 := (hc.mem_normalizer_LB_iff' hs5.width hs5.n_gt hs5.noA2 hgM).mp hgL
    have h2 : conjSubgroup g (B ⊔ Z : Subgroup G) = B ⊔ Z := conjSubgroup_eq_self_iff.mpr h1
    rwa [conjSubgroup_sup', hc.conj_Z_eq hgM] at h2
  have huD₀ : ∃ d : ↥(Vt M (LB M Q B) B Z t), (d : G) ∈ D₀ ∧ secVec ψ d = u := by
    obtain ⟨b, hbB, hbu⟩ := (hBiff u).mpr ⟨1, (one_smul K u).symm⟩
    refine ⟨b, Subgroup.mem_inf.mpr ⟨b.2, ?_⟩, hbu⟩
    rw [mem_conjSubgroup, inv_inv]
    have h1 : g * (b : G) * g⁻¹ ∈ conjSubgroup g B ⊔ Z := by
      refine Subgroup.mem_sup_left ?_
      rw [mem_conjSubgroup, show g⁻¹ * (g * (b : G) * g⁻¹) * g = (b : G) by group]
      exact hbB
    rw [hgBZ] at h1
    exact hVV₁ (sup_le (hc.B_le_Vt ht) hZV h1)
  have hDinv₀ : ∀ l ∈ LB M Q B, ∀ d ∈ D₀, l * d * l⁻¹ ∈ D₀ := by
    intro l hl d hd
    refine Subgroup.mem_inf.mpr ⟨hinvV l hl d (Subgroup.mem_inf.mp hd).1, ?_⟩
    have hd2 := (Subgroup.mem_inf.mp hd).2
    rw [mem_conjSubgroup, inv_inv] at hd2 ⊢
    have e : g * (l * d * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * d * g⁻¹) * (g * l * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact hinvV₁ _ (hgLmem l hl) _ hd2
  have hLN₀ : LB M Q B ≤ Subgroup.normalizer (D₀ : Set G) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun d hd => hDinv₀ l hl d hd
  have hdich := sec8_subspace_dichotomy hpts ψ hψ hZD₀ hD₀V hDK₀ huD₀ hDinv₀
  have hDu₀ : ∀ d : ↥(Vt M (LB M Q B) B Z t), (d : G) ∈ D₀ → spForm m K u (secVec ψ d) = 0 := by
    rcases hdich with h | h
    · exact h
    · exfalso
      apply hAc
      intro x hx
      have hx' : g⁻¹ * x * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hx
      have h1 := (Subgroup.mem_inf.mp (h hx')).2
      rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
      exact Subgroup.mem_sup_right h1
  set S₀ : Subgroup G := sec8MoveSub (LB M Q B) D₀ (Vt M (LB M Q B) B Z t) hLN₀ with hS₀def
  have hS₀L : S₀ ≤ LB M Q B := fun l hl => hl.1
  have hS₀ : ∀ l ∈ LB M Q B, l ∈ S₀ ↔ ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, l⁆ ∈ D₀ :=
    fun l hl => ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩
  set S : Subgroup G := conjSubgroup g S₀ with hSdef
  have hgLeq : conjSubgroup g (LB M Q B) = LB M Q B := conjSubgroup_eq_self_iff.mpr hgL
  have hSL : S ≤ LB M Q B := by
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hS₀L
    rw [← hgLeq]
    exact this
  have hS_iso : ∀ (l : G) (hl : l ∈ S) (y : Fin m ⊕ Fin m → K),
      spForm m K y ((φ ⟨l, le_Rt (M := M) (LB M Q B) ht (hSL hl)⟩ :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) = 0 := by
    intro l hl y
    by_contra hy
    have hna : SpNonA2 (φ ⟨l, le_Rt (M := M) (LB M Q B) ht (hSL hl)⟩) := ⟨y, hy⟩
    have hl' : g⁻¹ * l * g ∈ S₀ := by
      have := mem_conjSubgroup.mp hl
      simpa using this
    have hF := sec8_fixed_le_A1 h53 sec8InvStatement_holds hs hr hpts (hSL hl) hna
    apply hAc
    intro x hx
    have hx' : g⁻¹ * x * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hx
    have hxW : x ∈ Sec8W1 M Q Z B t r := by
      have := hVW _ hx'
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    have h1 := (hl'.2 _ hx')
    have h2 := (mem_conjSubgroup.mp (Subgroup.mem_inf.mp h1).2)
    rw [inv_inv, show g * ⁅g⁻¹ * x * g, g⁻¹ * l * g⁆ * g⁻¹ = ⁅x, l⁆ by
      simp only [commutatorElement_def]; group] at h2
    apply hF x hxW
    have e : ⁅l, x⁆ = ⁅x, l⁆⁻¹ := (commutatorElement_inv x l).symm
    rw [e]
    exact (Sec8V1 M Q Z B t r).inv_mem h2
  have h1 := sec8_card_LB hpts ht
  have h2 := sec8_card_isotropic_sub hpts ht hSL hS_iso
  have h4 := sec8_card_index hpts ht _ (sec8_isSecMod_psi hpts ψ hψ) hZD₀ hD₀V hDK₀ huD₀ hDu₀
    hS₀L hS₀
  have h3 : Nat.card ↥S₀ = Nat.card ↥S := (card_conjSubgroup g S₀).symm
  have h5 : Nat.card Z ^ (m + 1) ≤ Nat.card ↥D₀ := by
    have e1 : conjSubgroup g D₀ = conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
        Sec8V1 M Q Z B t r := by
      rw [hD₀, conjSubgroup_inf, ← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel,
        CFSG.RankThree.GF2n.conjSubgroup_one]
    have e2 : Nat.card ↥D₀ = Nat.card ↥(conjSubgroup g D₀) := (card_conjSubgroup g D₀).symm
    rw [e2, e1, inf_comm]
    exact hcard
  have hq : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have ha : 0 < Nat.card ↥(LB M Q B ⊓ hc.CN t) := Nat.card_pos
  rw [← h3] at h2
  exact sec8_caseB_arith hq ha h1 h2 h4 h5

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_caseA_large (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {m : ℕ}
    (hmSp : SpMNat hc t m) {g : G} (hgM : g ∈ M)
    (hgL : g ∈ Subgroup.normalizer (LB M Q B : Set G))
    (hAc : ∀ x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t),
      x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) :
    Nat.card Z ^ (m + 1) <
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hgi : g⁻¹ ∈ M := M.inv_mem hgM
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hRV := hc.Rt_normalizes_Vt ht
  have hinvV : ∀ l ∈ LB M Q B, ∀ x ∈ Vt M (LB M Q B) B Z t,
      l * x * l⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun l hl x hx => (Subgroup.mem_normalizer_iff.mp (hRV (hLR hl)) x).mp hx
  have hgLmem : ∀ l ∈ LB M Q B, g * l * g⁻¹ ∈ LB M Q B :=
    fun l hl => (Subgroup.mem_normalizer_iff.mp hgL l).mp hl
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, -⟩ := sec8_natdata h34 hRoot hs hr hmSp
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZg : conjSubgroup g⁻¹ Z = Z := hc.conj_Z_eq hgi
  have hcomm : ∀ l ∈ LB M Q B, ∀ v ∈ Vt M (LB M Q B) B Z t,
      ⁅v, l⁆ ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := by
    intro l hl v hv
    have hx : g * v * g⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * v * g⁻¹) * g = v by group]
      exact hv
    have hl₁ : g * l * g⁻¹ ∈ LB M Q B := hgLmem l hl
    have h1 : ⁅g * l * g⁻¹, g * v * g⁻¹⁆ ∈ Vt M (LB M Q B) B Z t :=
      sec8_comm_A1_le_V hs hl₁
        (sec8_comm_V1_LB h310chi h53.1 sec8InvStatement_holds hs hr hl₁) _ (hAc _ hx)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (Vt M (LB M Q B) B Z t).mul_mem hv
        (hinvV l hl _ ((Vt M (LB M Q B) B Z t).inv_mem hv))
    · rw [mem_conjSubgroup, inv_inv]
      have e : g * ⁅v, l⁆ * g⁻¹ = ⁅g * l * g⁻¹, g * v * g⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Vt M (LB M Q B) B Z t).inv_mem h1
  have hZD : Z ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) :=
    le_inf hZV (hZg.symm.le.trans (Subgroup.map_mono hZV))
  have hcard := sec8_card_comm hpts ht hZD inf_le_left hcomm
  have e1 : conjSubgroup g (Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) =
      conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Vt M (LB M Q B) B Z t := by
    rw [conjSubgroup_inf, ← CFSG.RankThree.GF2n.conjSubgroup_mul, mul_inv_cancel,
      CFSG.RankThree.GF2n.conjSubgroup_one]
  have e2 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
    rw [← card_conjSubgroup g, e1, inf_comm]
  rw [← e2]
  refine lt_of_lt_of_le ?_ hcard
  have hm := hpts.two_le
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  exact Nat.pow_lt_pow_right hq (by omega)

end

end CFSG.RankThree.GF2n.Stroth80
