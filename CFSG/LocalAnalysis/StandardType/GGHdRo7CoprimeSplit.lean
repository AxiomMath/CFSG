module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.GroupTheory.ElemAbelianClosure
import Mathlib.GroupTheory.Commutator.Basic
import TauCeti.GroupTheory.OrderOfElement.PPart
import TauCeti.GroupTheory.SpecificGroups.Cyclic.CoprimePart

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section CoprimeSplitAux

private lemma hdRo7CopSplitAux_mem_centralizer_of_conj_action {G : Type} [Group G]
    {X : Subgroup G} {b x : G}
    (hxX : x ∈ X) (h : ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  calc y * (x⁻¹ * b) = x⁻¹ * (x * y * x⁻¹) * b := by group
    _ = x⁻¹ * (b * y * b⁻¹) * b := by rw [← h y hy]
    _ = (x⁻¹ * b) * y := by group

private lemma hdRo7CopSplitAux_conj_action_of_decomp {G : Type} [Group G]
    {X : Subgroup G} {b t d : G}
    (hb : b = t * d) (hd : d ∈ Subgroup.centralizer (X : Set G)) {y : G} (hy : y ∈ X) :
    b * y * b⁻¹ = t * y * t⁻¹ := by
  have hdy : d * y = y * d := (Subgroup.mem_centralizer_iff.mp hd y hy).symm
  rw [hb]
  calc t * d * y * (t * d)⁻¹ = t * (d * y * d⁻¹) * t⁻¹ := by group
    _ = t * y * t⁻¹ := by rw [show d * y * d⁻¹ = y by rw [hdy]; group]

private lemma hdRo7CopSplitAux_g_pow_mem_centralizer {G : Type} [Group G] {p : ℕ}
    {X : Subgroup G} {b g : G}
    (hgX : g ∈ X) (hbp : b ^ p = 1)
    (hact : ∀ y ∈ X, b * y * b⁻¹ = g * y * g⁻¹) :
    g ^ p ∈ Subgroup.centralizer (X : Set G) := by
  have hcC : g⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
    hdRo7CopSplitAux_mem_centralizer_of_conj_action hgX hact
  have hcomm_gc : Commute g (g⁻¹ * b) := Subgroup.mem_centralizer_iff.mp hcC g hgX
  have hcp : (g⁻¹ * b) ^ p ∈ Subgroup.centralizer (X : Set G) :=
    (Subgroup.centralizer (X : Set G)).pow_mem hcC p
  have hmul : g ^ p * (g⁻¹ * b) ^ p = 1 := by
    rw [← Commute.mul_pow hcomm_gc p]
    rw [show g * (g⁻¹ * b) = b by group, hbp]
  rw [mul_eq_one_iff_eq_inv.mp hmul]
  exact (Subgroup.centralizer (X : Set G)).inv_mem hcp

private lemma hdRo7CopSplitAux_not_dvd_orderOf_pow {G : Type} [Group G] {p : ℕ}
    {X : Subgroup G} {g : G}
    (hp : p.Prime) (hgX : g ∈ X) (hgpc : g ^ p ∈ Subgroup.centralizer (X : Set G))
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center X))) :
    ¬ p ∣ orderOf (g ^ p) := by
  have hzX : g ^ p ∈ X := X.pow_mem hgX p
  have hzcenter : (⟨g ^ p, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hgpc (w : G) w.2
  have hdvd : orderOf (g ^ p) ∣ Nat.card (Subgroup.center X) := by
    have h1 : orderOf (⟨⟨g ^ p, hzX⟩, hzcenter⟩ : Subgroup.center X) ∣
        Nat.card (Subgroup.center X) := orderOf_dvd_natCard _
    have h2 : orderOf (g ^ p) =
        orderOf (⟨⟨g ^ p, hzX⟩, hzcenter⟩ : Subgroup.center X) :=
      orderOf_injective (X.subtype.comp (Subgroup.center X).subtype)
        ((Subgroup.subtype_injective X).comp (Subgroup.subtype_injective (Subgroup.center X)))
        ⟨⟨g ^ p, hzX⟩, hzcenter⟩
    rwa [← h2] at h1
  intro hdvd'
  have hpN : p ∣ Nat.card (Subgroup.center X) := dvd_trans hdvd' hdvd
  have hg : Nat.gcd p (Nat.card (Subgroup.center X)) = p := Nat.gcd_eq_left hpN
  have h1 : Nat.gcd p (Nat.card (Subgroup.center X)) = 1 := hcop.gcd_eq_one
  rw [hg] at h1
  exact Nat.Prime.ne_one hp h1

private lemma hdRo7CopSplitAux_factorization_le_one {p : ℕ} {n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : ¬ p ∣ n / Nat.gcd n p) : n.factorization p ≤ 1 := by
  by_contra hle
  have h2 : 2 ≤ n.factorization p := by omega
  have hpp : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr h2
  have hpdvd : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) hpp
  have hgcd : Nat.gcd n p = p := Nat.gcd_eq_right hpdvd
  have hpdvdiv : p ∣ n / p := (Nat.dvd_div_iff_mul_dvd hpdvd).mpr (by simpa [pow_two] using hpp)
  exact h (by rw [hgcd]; exact hpdvdiv)

private lemma hdRo7CopSplitAux_zpowers_pow_eq_of_not_dvd {G : Type} [Group G] [Finite G]
    {p : ℕ} {g : G}
    (hp : p.Prime) (hndvd : ¬ p ∣ orderOf g) :
    Subgroup.zpowers (g ^ p) = Subgroup.zpowers g := by
  apply Subgroup.eq_of_le_of_card_ge
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨(p : ℤ), by rw [zpow_natCast]⟩)
  · rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow' g hp.ne_zero]
    have hcop : Nat.gcd (orderOf g) p = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd))
    rw [hcop, Nat.div_one]

private lemma hdRo7CopSplitAux_pow_factorization_mem_centralizer {G : Type} [Group G]
    [Finite G] {p : ℕ} {X : Subgroup G} {g : G}
    (hp : p.Prime) (hgne : orderOf g ≠ 0)
    (hgpc : g ^ p ∈ Subgroup.centralizer (X : Set G)) :
    g ^ (p ^ (orderOf g).factorization p) ∈ Subgroup.centralizer (X : Set G) := by
  rcases Nat.eq_zero_or_pos ((orderOf g).factorization p) with he | he
  · have hndvdg : ¬ p ∣ orderOf g := by
      intro hpdvd
      have h1 : 1 ≤ (orderOf g).factorization p :=
        (hp.pow_dvd_iff_le_factorization hgne).mp (by simpa using hpdvd)
      omega
    have htop : Subgroup.zpowers (g ^ p) = Subgroup.zpowers g :=
      hdRo7CopSplitAux_zpowers_pow_eq_of_not_dvd hp hndvdg
    rw [he, pow_zero, pow_one]
    exact (Subgroup.zpowers_le.mpr hgpc) (by rw [htop]; exact Subgroup.mem_zpowers g)
  · have he1 : 1 ≤ (orderOf g).factorization p := he
    have hpow : g ^ (p ^ (orderOf g).factorization p) =
        (g ^ p) ^ (p ^ ((orderOf g).factorization p - 1)) := by
      have hexp : p ^ (orderOf g).factorization p =
          p * p ^ ((orderOf g).factorization p - 1) := by
        calc p ^ (orderOf g).factorization p
            = p ^ ((orderOf g).factorization p - 1 + 1) := by
              rw [Nat.sub_add_cancel he1]
          _ = p ^ ((orderOf g).factorization p - 1) * p := by rw [pow_succ]
          _ = p * p ^ ((orderOf g).factorization p - 1) := by rw [Nat.mul_comm]
      rw [hexp, pow_mul]
    rw [hpow]
    exact (Subgroup.centralizer (X : Set G)).pow_mem hgpc _

private lemma hdRo7CopSplitAux_pFreePart_mem_centralizer {G : Type} [Group G] [Finite G]
    {p : ℕ} {X : Subgroup G} {g : G}
    (hp : p.Prime) (hgne : orderOf g ≠ 0)
    (hgpc : g ^ p ∈ Subgroup.centralizer (X : Set G)) :
    TauCeti.pFreePart p g ∈ Subgroup.centralizer (X : Set G) := by
  have hmem : TauCeti.pFreePart p g ∈
      Subgroup.zpowers (g ^ (p ^ (orderOf g).factorization p)) := by
    rw [← TauCeti.zpowers_pFreePart_eq_zpowers_pow_ordProj hp hgne]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.zpowers_le.mpr
    (hdRo7CopSplitAux_pow_factorization_mem_centralizer hp hgne hgpc)) hmem

private lemma hdRo7CopSplitAux_pPart_pow_eq_one {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {g : G}
    (hndvd : ¬ p ∣ orderOf (g ^ p)) : TauCeti.pPart p g ^ p = 1 := by
  have hgne : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have he1 : (orderOf g).factorization p ≤ 1 :=
    hdRo7CopSplitAux_factorization_le_one hp hgne
      (by simpa [orderOf_pow' g hp.ne_zero] using hndvd)
  rw [← orderOf_dvd_iff_pow_eq_one]
  rw [TauCeti.orderOf_pPart hp hgne]
  have hdvd : p ^ (orderOf g).factorization p ∣ p ^ 1 :=
    (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr (by simpa using he1)
  rw [pow_one] at hdvd
  exact hdvd

private lemma hdRo7CopSplitAux_pow_mul_eq {G : Type} [Group G] {t t' : G}
    (hct : Commute (commutatorElement.bracket t t') t) (n : ℕ) :
    t ^ n * t' = (commutatorElement.bracket t t') ^ n * t' * t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : t * (commutatorElement.bracket t t') ^ n = (commutatorElement.bracket t t') ^ n * t :=
      (hct.pow_left n).eq.symm
    have htt' : t * t' = commutatorElement.bracket t t' * t' * t := by
      unfold commutatorElement
      group
    calc
      t ^ (n + 1) * t' = t * (t ^ n * t') := by rw [pow_succ']; group
      _ = t * ((commutatorElement.bracket t t') ^ n * t' * t ^ n) := by rw [ih]
      _ = (t * (commutatorElement.bracket t t') ^ n) * t' * t ^ n := by group
      _ = ((commutatorElement.bracket t t') ^ n * t) * t' * t ^ n := by rw [h1]
      _ = (commutatorElement.bracket t t') ^ n * (t * t') * t ^ n := by group
      _ = (commutatorElement.bracket t t') ^ n * (commutatorElement.bracket t t' * t' * t) * t ^ n := by
            rw [htt']
      _ = (commutatorElement.bracket t t') ^ (n + 1) * t' * t ^ (n + 1) := by
            rw [pow_succ, pow_succ']; group

end CoprimeSplitAux

theorem ggBstar_split_of_inner_coprime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs : Subgroup G} (hBs : GGBstar p B Bs) {X : Subgroup G}
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center X)))
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ∀ b ∈ Bs, ∃ x ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = x * c := by
  intro b hb
  obtain ⟨g, hgX, hgact⟩ := hinner b hb
  let t := TauCeti.pPart p g
  let z := TauCeti.pFreePart p g
  have hbp1 : b ^ p = 1 := hBs.2.1.2 b hb
  have hcC : g⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
    hdRo7CopSplitAux_mem_centralizer_of_conj_action hgX hgact
  have hgpc : g ^ p ∈ Subgroup.centralizer (X : Set G) :=
    hdRo7CopSplitAux_g_pow_mem_centralizer hgX hbp1 hgact
  have hgne : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hndvd : ¬ p ∣ orderOf (g ^ p) :=
    hdRo7CopSplitAux_not_dvd_orderOf_pow hp hgX hgpc hcop
  have htX : t ∈ X := by
    change TauCeti.pPart p g ∈ X
    exact Subgroup.zpowers_le_of_mem hgX (TauCeti.pPart_mem_zpowers p g)
  have htpow : t ^ p = 1 := by
    change TauCeti.pPart p g ^ p = 1
    exact hdRo7CopSplitAux_pPart_pow_eq_one hp hndvd
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    change TauCeti.pFreePart p g ∈ Subgroup.centralizer (X : Set G)
    exact hdRo7CopSplitAux_pFreePart_mem_centralizer hp hgne hgpc
  have hgdecomp : t * z = g := by
    change TauCeti.pPart p g * TauCeti.pFreePart p g = g
    exact TauCeti.pPart_mul_pFreePart p g
  have htCBs : t ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    obtain ⟨g', hg'X, hg'act⟩ := hinner b' hb'
    let t' := TauCeti.pPart p g'
    let z' := TauCeti.pFreePart p g'
    have hb'p1 : b' ^ p = 1 := hBs.2.1.2 b' hb'
    have hc'C : g'⁻¹ * b' ∈ Subgroup.centralizer (X : Set G) :=
      hdRo7CopSplitAux_mem_centralizer_of_conj_action hg'X hg'act
    have hg'pc : g' ^ p ∈ Subgroup.centralizer (X : Set G) :=
      hdRo7CopSplitAux_g_pow_mem_centralizer hg'X hb'p1 hg'act
    have hg'ne : orderOf g' ≠ 0 := ne_of_gt (orderOf_pos g')
    have hndvd' : ¬ p ∣ orderOf (g' ^ p) :=
      hdRo7CopSplitAux_not_dvd_orderOf_pow hp hg'X hg'pc hcop
    have ht'X : t' ∈ X := by
      change TauCeti.pPart p g' ∈ X
      exact Subgroup.zpowers_le_of_mem hg'X (TauCeti.pPart_mem_zpowers p g')
    have ht'pow : t' ^ p = 1 := by
      change TauCeti.pPart p g' ^ p = 1
      exact hdRo7CopSplitAux_pPart_pow_eq_one hp hndvd'
    have hz'C : z' ∈ Subgroup.centralizer (X : Set G) := by
      change TauCeti.pFreePart p g' ∈ Subgroup.centralizer (X : Set G)
      exact hdRo7CopSplitAux_pFreePart_mem_centralizer hp hg'ne hg'pc
    have hg'decomp : t' * z' = g' := by
      change TauCeti.pPart p g' * TauCeti.pFreePart p g' = g'
      exact TauCeti.pPart_mul_pFreePart p g'
    have hdC : z * (g⁻¹ * b) ∈ Subgroup.centralizer (X : Set G) :=
      (Subgroup.centralizer (X : Set G)).mul_mem hzC hcC
    have hd'C : z' * (g'⁻¹ * b') ∈ Subgroup.centralizer (X : Set G) :=
      (Subgroup.centralizer (X : Set G)).mul_mem hz'C hc'C
    have hb_eq : b = t * (z * (g⁻¹ * b)) := by
      calc b = g * (g⁻¹ * b) := by group
        _ = (t * z) * (g⁻¹ * b) := by rw [hgdecomp]
        _ = t * (z * (g⁻¹ * b)) := by group
    have hb'_eq : b' = t' * (z' * (g'⁻¹ * b')) := by
      calc b' = g' * (g'⁻¹ * b') := by group
        _ = (t' * z') * (g'⁻¹ * b') := by rw [hg'decomp]
        _ = t' * (z' * (g'⁻¹ * b')) := by group
    have hbb' : b * b' = b' * b := IsElemAbelian.comm hBs.2.1 hb hb'
    have hcomm_actions : ∀ y ∈ X,
        t' * (t * y * t⁻¹) * t'⁻¹ = t * (t' * y * t'⁻¹) * t⁻¹ := by
      intro y hy
      have hL : b' * (b * y * b⁻¹) * b'⁻¹ = t' * (t * y * t⁻¹) * t'⁻¹ := by
        rw [hdRo7CopSplitAux_conj_action_of_decomp hb_eq hdC hy]
        exact hdRo7CopSplitAux_conj_action_of_decomp hb'_eq hd'C
          (X.mul_mem (X.mul_mem htX hy) (X.inv_mem htX))
      have hR : b * (b' * y * b'⁻¹) * b⁻¹ = t * (t' * y * t'⁻¹) * t⁻¹ := by
        rw [hdRo7CopSplitAux_conj_action_of_decomp hb'_eq hd'C hy]
        exact hdRo7CopSplitAux_conj_action_of_decomp hb_eq hdC
          (X.mul_mem (X.mul_mem ht'X hy) (X.inv_mem ht'X))
      calc
        t' * (t * y * t⁻¹) * t'⁻¹ = b' * (b * y * b⁻¹) * b'⁻¹ := hL.symm
        _ = (b' * b) * y * (b' * b)⁻¹ := by group
        _ = (b * b') * y * (b * b')⁻¹ := by rw [hbb']
        _ = b * (b' * y * b'⁻¹) * b⁻¹ := by group
        _ = t * (t' * y * t'⁻¹) * t⁻¹ := hR
    have hφmul : MulAut.conj (⟨t, htX⟩ : X) * MulAut.conj (⟨t', ht'X⟩ : X) =
        MulAut.conj (⟨t', ht'X⟩ : X) * MulAut.conj (⟨t, htX⟩ : X) := by
      ext y
      simpa only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
        using (hcomm_actions y y.2).symm
    have hmem : commutatorElement.bracket t t' ∈ X := by
      unfold commutatorElement
      exact X.mul_mem (X.mul_mem (X.mul_mem htX ht'X) (X.inv_mem htX)) (X.inv_mem ht'X)
    have hXcomm : commutatorElement.bracket (⟨t, htX⟩ : X) (⟨t', ht'X⟩ : X) =
        (⟨commutatorElement.bracket t t', hmem⟩ : X) := by
      apply Subtype.ext
      rfl
    have hφ_commutator :
        (MulAut.conj : X →* MulAut X) (⟨commutatorElement.bracket t t', hmem⟩ : X) = 1 := by
      rw [← hXcomm, map_commutatorElement (MulAut.conj : X →* MulAut X),
        commutatorElement_eq_one_iff_mul_comm.mpr hφmul]
    have hcenter : (⟨commutatorElement.bracket t t', hmem⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := congrArg (fun f : MulAut X => f w) hφ_commutator
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      have h2 : w * (⟨commutatorElement.bracket t t', hmem⟩ : X) =
          (⟨commutatorElement.bracket t t', hmem⟩ : X) * w := by
        have hzw : (⟨commutatorElement.bracket t t', hmem⟩ : X) * w =
            w * (⟨commutatorElement.bracket t t', hmem⟩ : X) := by
          calc (⟨commutatorElement.bracket t t', hmem⟩ : X) * w
              = (⟨commutatorElement.bracket t t', hmem⟩ : X) * w *
                  (⟨commutatorElement.bracket t t', hmem⟩ : X)⁻¹ *
                  (⟨commutatorElement.bracket t t', hmem⟩ : X) := by group
            _ = w * (⟨commutatorElement.bracket t t', hmem⟩ : X) := by rw [h]
        exact hzw.symm
      exact h2
    have hcommc : Commute (commutatorElement.bracket t t') t := by
      have h := (Subgroup.mem_center_iff.mp hcenter) (⟨t, htX⟩ : X)
      exact (congrArg Subtype.val h).symm
    have hcpow : (commutatorElement.bracket t t') ^ p = 1 := by
      have h := hdRo7CopSplitAux_pow_mul_eq hcommc p
      rw [htpow, one_mul, mul_one] at h
      have h' : (commutatorElement.bracket t t') ^ p * t' = 1 * t' := by
        rw [one_mul]
        simpa using h.symm
      exact mul_right_cancel h'
    have hdvd' : orderOf (commutatorElement.bracket t t') ∣ p :=
      orderOf_dvd_of_pow_eq_one hcpow
    have hdvd : orderOf (commutatorElement.bracket t t') ∣ Nat.card (Subgroup.center X) := by
      have h1 : orderOf (⟨⟨commutatorElement.bracket t t', hmem⟩, hcenter⟩ : Subgroup.center X) ∣
          Nat.card (Subgroup.center X) := orderOf_dvd_natCard _
      have h2 : orderOf (commutatorElement.bracket t t') =
          orderOf (⟨⟨commutatorElement.bracket t t', hmem⟩, hcenter⟩ : Subgroup.center X) :=
        orderOf_injective (X.subtype.comp (Subgroup.center X).subtype)
          ((Subgroup.subtype_injective X).comp (Subgroup.subtype_injective (Subgroup.center X)))
          ⟨⟨commutatorElement.bracket t t', hmem⟩, hcenter⟩
      rwa [← h2] at h1
    have hone : orderOf (commutatorElement.bracket t t') ∣ 1 := by
      have h := Nat.dvd_gcd hdvd' hdvd
      rwa [hcop.gcd_eq_one] at h
    have hct1 : commutatorElement.bracket t t' = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
    have htt' : t * t' = t' * t := commutatorElement_eq_one_iff_mul_comm.mp hct1
    have hdt : t * (z' * (g'⁻¹ * b')) = (z' * (g'⁻¹ * b')) * t :=
      Subgroup.mem_centralizer_iff.mp hd'C t htX
    have htb' : t * b' = b' * t := by
      rw [hb'_eq]
      calc
        t * (t' * (z' * (g'⁻¹ * b'))) = (t * t') * (z' * (g'⁻¹ * b')) := by group
        _ = (t' * t) * (z' * (g'⁻¹ * b')) := by rw [htt']
        _ = t' * (t * (z' * (g'⁻¹ * b'))) := by group
        _ = t' * ((z' * (g'⁻¹ * b')) * t) := by rw [hdt]
        _ = (t' * (z' * (g'⁻¹ * b'))) * t := by group
    exact htb'.symm
  have htBs : t ∈ Bs := hBs.2.2.2 t htCBs htpow
  refine ⟨t, ⟨htBs, htX⟩, t⁻¹ * b, ⟨?_, ?_⟩, ?_⟩
  · exact Bs.mul_mem (Bs.inv_mem htBs) hb
  · have hcz : t⁻¹ * b = z * (g⁻¹ * b) := by
      calc t⁻¹ * b = t⁻¹ * (g * (g⁻¹ * b)) := by group
        _ = t⁻¹ * ((t * z) * (g⁻¹ * b)) := by rw [hgdecomp]
        _ = z * (g⁻¹ * b) := by group
    rw [hcz]
    exact (Subgroup.centralizer (X : Set G)).mul_mem hzC hcC
  · group

theorem bstar_inf_le_conj_preimage_centralizes {G : Type} [Group G] {p : ℕ}
    {B Bs J : Subgroup G} (hBs : GGBstar p B Bs)
    (hBN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    let P : Subgroup ↥J :=
      (ggGamma J hBN).range.comap (MulAut.conj : ↥J →* MulAut ↥J)
    (Bs ⊓ J : Subgroup G) ≤ P.map J.subtype ∧
      ∀ q ∈ P, ∀ e ∈ (Bs ⊓ J : Subgroup G), (q : G) * e * (q : G)⁻¹ = e := by
  intro P
  letI : IsMulCommutative ↥Bs := hBs.2.1.1
  have hconj : ∀ (e : G) (heBs : e ∈ Bs) (heJ : e ∈ J),
      MulAut.conj (⟨e, heJ⟩ : ↥J) = ggGamma J hBN ⟨e, heBs⟩ := by
    intro e heBs heJ
    ext l
    rfl
  constructor
  · rintro e he
    obtain ⟨heBs, heJ⟩ := Subgroup.mem_inf.mp he
    refine ⟨⟨e, heJ⟩, ?_, rfl⟩
    change MulAut.conj (⟨e, heJ⟩ : ↥J) ∈ (ggGamma J hBN).range
    rw [hconj e heBs heJ]
    exact ⟨⟨e, heBs⟩, rfl⟩
  · intro q hq e he
    obtain ⟨heBs, heJ⟩ := Subgroup.mem_inf.mp he
    rw [Subgroup.mem_comap] at hq
    obtain ⟨b, hb⟩ := hq
    have h1 : (MulAut.conj q) (⟨e, heJ⟩ : ↥J) =
        (ggGamma J hBN b) (⟨e, heJ⟩ : ↥J) := by rw [hb]
    have h2 : (q : G) * e * (q : G)⁻¹ = (b : G) * e * (b : G)⁻¹ := by
      have hval := congrArg (fun x : ↥J => (x : G)) h1
      change (q : G) * e * (q : G)⁻¹ = (b : G) * e * (b : G)⁻¹ at hval
      exact hval
    have hbe : (b : G) * e = e * (b : G) :=
      congrArg Subtype.val (hBs.2.1.1.is_comm.comm b ⟨e, heBs⟩)
    rw [h2]
    calc (b : G) * e * (b : G)⁻¹ = (e * (b : G)) * (b : G)⁻¹ := by rw [hbe]
      _ = e := by group

end CFSG.StandardType

end
