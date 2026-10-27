module

public import Mathlib.GroupTheory.PGroup
import CFSG.Quasithin.Background.A1bPGroups
import CFSG.Assembly.OrderReductions.InvariantSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

theorem w162_exp_class_of_inverted {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : IsPGroup p N) (α : MulAut N) (hα : α * α = 1)
    (hgen : Subgroup.closure {y : N | ∃ x : N, y = x⁻¹ * α x} = ⊤)
    (hcomm : ∀ x ∈ commutator N, α x = x) (hpow : ∀ x : N, α (x ^ p) = x ^ p) :
    (∀ x : N, x ^ p = 1) ∧ ∀ x y z : N, ⁅⁅x, y⁆, z⁆ = 1 := by
  have hα_apply : ∀ x : N, α (α x) = x := by
    intro x
    have h := congrArg (fun f : MulAut N => f x) hα
    simpa using h
  have hinv : ∀ x : N, α (x⁻¹ * α x) = (x⁻¹ * α x)⁻¹ := by
    intro x
    simp only [map_mul, map_inv, hα_apply, mul_inv_rev, inv_inv]
  have hS : ∀ y ∈ {y : N | ∃ x : N, y = x⁻¹ * α x}, y ^ p = 1 := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hcoe : α ((x⁻¹ * α x) ^ p) = ((x⁻¹ * α x) ^ p)⁻¹ := by
      rw [map_pow, hinv, inv_pow]
    have hself : ((x⁻¹ * α x) ^ p) = ((x⁻¹ * α x) ^ p)⁻¹ := by
      calc ((x⁻¹ * α x) ^ p) = α ((x⁻¹ * α x) ^ p) := (hpow ((x⁻¹ * α x))).symm
        _ = ((x⁻¹ * α x) ^ p)⁻¹ := hcoe
    have htwo : ((x⁻¹ * α x) ^ p) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hself]
      exact mul_inv_cancel _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hN) ((x⁻¹ * α x) ^ p)
    have hdvd : orderOf ((x⁻¹ * α x) ^ p) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr htwo
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have hpdvd : p ∣ 2 := dvd_trans (dvd_pow_self p hk0) hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd with h1 | h2
      · exact (Fact.out : p.Prime).ne_one h1
      · exact hp2 h2
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hcenter : commutator N ≤ Subgroup.center N := by
    intro a ha
    have hcommS :
        a ∈ Subgroup.centralizer ({y : N | ∃ x : N, y = x⁻¹ * α x} : Set N) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      have ha' : α a = a := hcomm a ha
      have hc : ⁅a, x⁆ ∈ commutator N :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top x)
      have hc' : α ⁅a, x⁆ = ⁅a, x⁆ := hcomm ⁅a, x⁆ hc
      have hαx : α x = x * (x⁻¹ * α x) := by group
      have hexp : α ⁅a, x⁆ = ((⁅a, x⁆ * x) * ⁅a, x⁻¹ * α x⁆) * x⁻¹ := by
        conv_lhs => rw [map_commutatorElement, ha', hαx]
        rw [commutatorElement_mul_right_eq_mul_conj]
      have hone : ⁅a, x⁻¹ * α x⁆ = 1 := by
        have hEq0 : ⁅a, x⁆ = ((⁅a, x⁆ * x) * ⁅a, x⁻¹ * α x⁆) * x⁻¹ :=
          hc'.symm.trans hexp
        have hEq1 : ⁅a, x⁆ * x = (⁅a, x⁆ * x) * ⁅a, x⁻¹ * α x⁆ := by
          calc ⁅a, x⁆ * x = (((⁅a, x⁆ * x) * ⁅a, x⁻¹ * α x⁆) * x⁻¹) * x := by
                rw [← hEq0]
            _ = (⁅a, x⁆ * x) * ⁅a, x⁻¹ * α x⁆ := by group
        exact mul_left_cancel (hEq1.symm.trans (mul_one (⁅a, x⁆ * x)).symm)
      exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
    rw [Subgroup.mem_center_iff]
    intro x
    have hEq : Subgroup.centralizer ({y : N | ∃ x : N, y = x⁻¹ * α x} : Set N) =
        Subgroup.centralizer (⊤ : Set N) := by
      rw [← Subgroup.centralizer_closure, hgen]
      rfl
    have htop : a ∈ Subgroup.centralizer (⊤ : Set N) := by
      rw [← hEq]
      exact hcommS
    exact htop x (Subgroup.mem_top x)
  have hcl : ∀ x y z : N, ⁅⁅x, y⁆, z⁆ = 1 := by
    intro x y z
    have hmem : ⁅x, y⁆ ∈ commutator N :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hz : ⁅x, y⁆ ∈ Subgroup.center N := hcenter hmem
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz z).symm
  have hgenpow : Subgroup.closure {x : N | x ^ p = 1} = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgen]
    exact Subgroup.closure_mono (fun y hy => hS y hy)
  have hclass : CFSG.Quasithin.ClassLeTwo (⊤ : Subgroup N) := by
    unfold CFSG.Quasithin.ClassLeTwo
    rw [eq_bot_iff]
    calc ⁅⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆, (⊤ : Subgroup N)⁆
        ≤ ⁅Subgroup.center N, (⊤ : Subgroup N)⁆ := Subgroup.commutator_mono hcenter le_rfl
      _ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
  exact ⟨CFSG.Quasithin.pow_eq_one_of_classLeTwo hp2 hclass hgenpow, hcl⟩


private lemma w162_grp_invariant_sylow_image {Γ : Type*} [Group Γ] [Finite Γ]
    {N P : Subgroup Γ} [N.Normal] (hodd : Odd (Nat.card N)) (hP : IsPGroup 2 P)
    (q : ℕ) (hq : q.Prime) :
    ∃ Y : Subgroup Γ, Y ≤ N ∧ P ≤ Subgroup.normalizer (Y : Set Γ) ∧
      Nat.card Y = q ^ (Nat.card N).factorization q ∧ (Y = N → IsPGroup q N) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨R, hR⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
    (actor := ↥P) (group := ↥N) 2 q hP hodd.not_two_dvd_nat
    ((MulAut.conjNormal (H := N)).comp P.subtype)
  refine ⟨(R : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmaps : N.subtype.comp (MulAut.conjNormal (H := N) g).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp N.subtype := by
      ext n
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    rw [Subgroup.map_map]
    rw [show ((↑(MulAut.conj g) : Γ →* Γ).comp N.subtype) =
      ((MulAut.conj g).toMonoidHom.comp N.subtype) from rfl]
    rw [← hmaps, ← Subgroup.map_map]
    have hg' := hR ⟨g, hg⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at hg'
    rw [hg']
  · rw [Subgroup.card_subtype]
    exact Sylow.card_eq_multiplicity R
  · intro hY
    have hq' : IsPGroup q ((R : Subgroup ↥N).map N.subtype) :=
      R.isPGroup'.map N.subtype
    rwa [hY] at hq'

private lemma w162_grp_zpowers_eq_one_or {Γ : Type*} [Group Γ] {t : Γ} (ht : t * t = 1)
    {s : Γ} (hs : s ∈ Subgroup.zpowers t) : s = 1 ∨ s = t := by
  rw [Subgroup.mem_zpowers_iff] at hs
  obtain ⟨m, rfl⟩ := hs
  have htwo : t ^ (2 : ℕ) = 1 := by rw [pow_two, ht]
  have hmeq : t ^ m = t ^ (m % 2) := zpow_eq_zpow_emod' m htwo
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · left; rw [hmeq, hm, zpow_zero]
  · right; rw [hmeq, hm, zpow_one]

private lemma w162_grp_pow_closure_ne_top {N : Type*} [Group N] [Finite N] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hN : IsPGroup p N) [Nontrivial N] :
    Subgroup.closure (Set.range (fun x : N => x ^ p)) ≠ ⊤ := by
  intro htop
  haveI : Group.IsNilpotent N := hN.isNilpotent
  have hcommlt : commutator N < (⊤ : Subgroup N) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial N
  have hAnontr : Nontrivial (Abelianization N) :=
    QuotientGroup.nontrivial_iff.mpr hcommlt.ne
  have hApg : IsPGroup p (Abelianization N) := hN.to_quotient (commutator N)
  have hπsurj : Function.Surjective (Abelianization.of (G := N)) := by
    intro a
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (commutator N) a
    exact ⟨x, by rw [← hx]; rfl⟩
  have hmap : Subgroup.map (Abelianization.of (G := N))
      (Subgroup.closure (Set.range (fun x : N => x ^ p))) = ⊤ := by
    rw [htop, Subgroup.map_top_of_surjective _ hπsurj]
  have hset : Abelianization.of (G := N) '' Set.range (fun x : N => x ^ p) =
      Set.range (fun a : Abelianization N => a ^ p) := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨Abelianization.of z, by rw [map_pow]⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨x, rfl⟩ := hπsurj b
      exact ⟨x ^ p, ⟨x, rfl⟩, by rw [map_pow]⟩
  have hpowtop : Subgroup.closure (Set.range (fun a : Abelianization N => a ^ p)) = ⊤ := by
    rw [MonoidHom.map_closure, hset] at hmap
    exact hmap
  let P : Subgroup (Abelianization N) :=
    { carrier := Set.range (fun a : Abelianization N => a ^ p)
      one_mem' := ⟨1, one_pow p⟩
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, mul_pow a b p⟩
      inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, inv_pow a p⟩ }
  have hPtop : P = ⊤ := by
    rw [← hpowtop]
    apply le_antisymm
    · exact Subgroup.subset_closure
    · rw [Subgroup.closure_le]; intro x hx; exact hx
  have hsurj : Function.Surjective (fun a : Abelianization N => a ^ p) := by
    intro a
    have : a ∈ P := by rw [hPtop]; exact Subgroup.mem_top a
    exact this
  have hinj : Function.Injective (fun a : Abelianization N => a ^ p) :=
    (Finite.injective_iff_surjective (α := Abelianization N)).mpr hsurj
  obtain ⟨n, hnpos, hncard⟩ := hApg.nontrivial_iff_card.mp hAnontr
  have hpdvd : p ∣ Nat.card (Abelianization N) := by
    rw [hncard]; exact dvd_pow_self p hnpos.ne'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Abelianization N) p hpdvd
  have hy1 : y ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy; exact (Fact.out : p.Prime).ne_one hy.symm
  have hyk : y ^ p = 1 := by
    rw [← hy]; exact pow_orderOf_eq_one y
  exact hy1 (hinj (by change y ^ p = 1 ^ p; rw [hyk, one_pow]))

private lemma w162_grp_power_closure_characteristic {N : Type*} [Group N] (p : ℕ) :
    (Subgroup.closure (Set.range (fun x : N => x ^ p))).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro x ⟨w, hw, rfl⟩
  rcases hw with ⟨z, rfl⟩
  rw [map_pow]
  exact Subgroup.subset_closure ⟨φ z, rfl⟩

theorem w162_exp_class_of_min {Γ : Type*} [Group Γ] [Finite Γ] {N P : Subgroup Γ} [N.Normal]
    (hodd : Odd (Nat.card N)) (hP : IsPGroup 2 P) {t : Γ} (ht : t * t = 1) (hne : N ≠ ⊥)
    (hgen : N ≤ ⁅N, Subgroup.zpowers t⁆)
    (hmin : ∀ Y : Subgroup Γ, Y ≤ N → Y ≠ N → P ≤ Subgroup.normalizer (Y : Set Γ) →
      ∀ y ∈ Y, t * y = y * t) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p N ∧ (∀ x ∈ N, x ^ p = 1) ∧
      ∀ x ∈ N, ∀ y ∈ N, ∀ z ∈ N, ⁅⁅x, y⁆, z⁆ = 1 := by
  have key : ∃ p : ℕ, p.Prime ∧ IsPGroup p N := by
    by_contra hno
    have hYexists : ∀ q (hq : q.Prime), ∃ Y : Subgroup Γ,
        Y ≤ N ∧ P ≤ Subgroup.normalizer (Y : Set Γ) ∧
        Nat.card Y = q ^ (Nat.card N).factorization q ∧ (Y = N → IsPGroup q N) :=
      fun q hq => w162_grp_invariant_sylow_image hodd hP q hq
    let Y : (q : ℕ) → q.Prime → Subgroup Γ := fun q hq => Classical.choose (hYexists q hq)
    have hYle : ∀ q hq, Y q hq ≤ N := fun q hq => (Classical.choose_spec (hYexists q hq)).1
    have hYnorm : ∀ q hq, P ≤ Subgroup.normalizer (Y q hq : Set Γ) :=
      fun q hq => (Classical.choose_spec (hYexists q hq)).2.1
    have hYcard : ∀ q hq, Nat.card (Y q hq) = q ^ (Nat.card N).factorization q :=
      fun q hq => (Classical.choose_spec (hYexists q hq)).2.2.1
    have hYproper : ∀ q hq, Y q hq ≠ N := by
      intro q hq hEq
      exact hno ⟨q, hq, (Classical.choose_spec (hYexists q hq)).2.2.2 hEq⟩
    let C : Subgroup Γ := N ⊓ Subgroup.centralizer ({t} : Set Γ)
    have hYC : ∀ q hq, Y q hq ≤ C := by
      intro q hq y hy
      refine ⟨hYle q hq hy, ?_⟩
      change y ∈ Subgroup.centralizer ({t} : Set Γ)
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hmin (Y q hq) (hYle q hq) (hYproper q hq) (hYnorm q hq) y hy
    have hcardC : Nat.card N ∣ Nat.card C := by
      apply (Nat.factorization_prime_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mp
      intro q hq
      have hdvd : q ^ (Nat.card N).factorization q ∣ Nat.card C := by
        rw [← hYcard q hq]
        exact Subgroup.card_dvd_of_le (hYC q hq)
      exact (Nat.Prime.pow_dvd_iff_le_factorization hq (Nat.card_pos.ne')).mp hdvd
    have hCN : C = N := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      exact Nat.le_of_dvd Nat.card_pos hcardC
    have htcent : ∀ n ∈ N, t * n = n * t := by
      intro n hn
      have hnC : n ∈ C := by rw [hCN]; exact hn
      have hnC' : n ∈ N ⊓ Subgroup.centralizer ({t} : Set Γ) := hnC
      exact (Subgroup.mem_centralizer_iff.mp hnC'.2) t (Set.mem_singleton t)
    have hcommbot : ⁅N, Subgroup.zpowers t⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      change s ∈ Subgroup.zpowers t at hs
      rw [Subgroup.mem_zpowers_iff] at hs
      obtain ⟨k, rfl⟩ := hs
      exact (Commute.zpow_left (show Commute t n from htcent n hn) k).eq
    have : N ≤ ⊥ := hcommbot ▸ hgen
    exact hne (le_bot_iff.mp this)
  obtain ⟨p, hpprime, hPN⟩ := key
  haveI : Fact p.Prime := ⟨hpprime⟩
  haveI hNnt : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  haveI hNnil : Group.IsNilpotent ↥N := hPN.isNilpotent
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPN
    have hcard1 : Nat.card N ≠ 1 := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne |>.ne'
    have hnpos : 0 < n := by
      by_contra h0
      have : n = 0 := by omega
      rw [this, pow_zero] at hn
      exact hcard1 hn
    exact hodd.not_two_dvd_nat (by rw [hn]; exact dvd_pow_self 2 hnpos.ne')
  let α : MulAut ↥N := MulAut.conjNormal (H := N) t
  have hα : α * α = 1 := by
    change MulAut.conjNormal (H := N) t * MulAut.conjNormal (H := N) t = 1
    rw [← map_mul, ht, map_one]
  have hmapTop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcommα : ∀ x ∈ commutator (↥N), α x = x := by
    intro x hx
    change MulAut.conjNormal (H := N) t x = x
    have hDle : (commutator (↥N)).map N.subtype ≤ N := Subgroup.map_subtype_le _
    have hDne : (commutator (↥N)).map N.subtype ≠ N := by
      intro hEq
      have hlt : commutator (↥N) < (⊤ : Subgroup ↥N) :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial ↥N
      have hlt' : (commutator (↥N)).map N.subtype < (⊤ : Subgroup ↥N).map N.subtype :=
        Subgroup.map_subtype_lt_map_subtype.mpr hlt
      rw [hEq, hmapTop] at hlt'
      exact lt_irrefl N hlt'
    have hDnorm : P ≤ Subgroup.normalizer
        (((commutator (↥N)).map N.subtype : Subgroup Γ) : Set Γ) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmaps : N.subtype.comp (MulAut.conjNormal (H := N) g).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp N.subtype := by
        ext n
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
      rw [Subgroup.map_map]
      rw [show ((↑(MulAut.conj g) : Γ →* Γ).comp N.subtype) =
        ((MulAut.conj g).toMonoidHom.comp N.subtype) from rfl]
      rw [← hmaps, ← Subgroup.map_map]
      rw [Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (commutator (↥N)).Characteristic) (MulAut.conjNormal (H := N) g)]
    have hxmem : ((x : Γ)) ∈ (commutator (↥N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hx
    have htx := hmin ((commutator (↥N)).map N.subtype) hDle hDne hDnorm x hxmem
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, inv_eq_of_mul_eq_one_right ht]
    calc t * ↑x * t = (↑x * t) * t := by rw [htx]
      _ = ↑x := by rw [mul_assoc, ht, mul_one]
  have hpowα : ∀ x : ↥N, α (x ^ p) = x ^ p := by
    intro x
    change MulAut.conjNormal (H := N) t (x ^ p) = x ^ p
    let V : Subgroup ↥N := Subgroup.closure (Set.range (fun y : ↥N => y ^ p))
    have hVle : V.map N.subtype ≤ N := Subgroup.map_subtype_le _
    have hVne : V.map N.subtype ≠ N := by
      intro hVN
      have hVtopne : V ≠ ⊤ := w162_grp_pow_closure_ne_top hp2 hPN
      have hVeq : V = ⊤ := by
        apply Subgroup.map_injective N.subtype_injective
        rw [hVN, hmapTop]
      exact hVtopne hVeq
    have hVnorm : P ≤ Subgroup.normalizer ((V.map N.subtype : Subgroup Γ) : Set Γ) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hmaps : N.subtype.comp (MulAut.conjNormal (H := N) g).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp N.subtype := by
        ext n
        simp [MulAut.conjNormal_apply, MulAut.conj_apply]
      rw [Subgroup.map_map]
      rw [show ((↑(MulAut.conj g) : Γ →* Γ).comp N.subtype) =
        ((MulAut.conj g).toMonoidHom.comp N.subtype) from rfl]
      rw [← hmaps, ← Subgroup.map_map]
      congr 1
      exact Subgroup.characteristic_iff_map_eq.mp
        (w162_grp_power_closure_characteristic (N := ↥N) p) (MulAut.conjNormal (H := N) g)
    have hxV : x ^ p ∈ V := Subgroup.subset_closure ⟨x, rfl⟩
    have hxmem : ((x ^ p : ↥N) : Γ) ∈ V.map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hxV
    have htx := hmin (V.map N.subtype) hVle hVne hVnorm (x ^ p) hxmem
    have htx' : t * (↑(x ^ p) : Γ) = (↑(x ^ p) : Γ) * t := by
      simpa only [Subgroup.coe_pow] using htx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, inv_eq_of_mul_eq_one_right ht]
    calc t * ↑(x ^ p) * t = (↑(x ^ p) * t) * t := by rw [htx']
      _ = ↑(x ^ p) := by rw [mul_assoc, ht, mul_one]
  have hgenα : Subgroup.closure {y : ↥N | ∃ x : ↥N, y = x⁻¹ * α x} = ⊤ := by
    let S : Set ↥N := {y : ↥N | ∃ x : ↥N, y = x⁻¹ * α x}
    let T : Subgroup Γ := (Subgroup.closure S).map N.subtype
    have hcommT : ⁅N, Subgroup.zpowers t⁆ ≤ T := by
      rw [Subgroup.commutator_le]
      intro n hn s hs
      rcases w162_grp_zpowers_eq_one_or ht hs with h1 | h1
      · rw [h1, commutatorElement_one_right]; exact T.one_mem
      · rw [h1]
        have hxS : (⟨n⁻¹, N.inv_mem hn⟩ : ↥N)⁻¹ * α ⟨n⁻¹, N.inv_mem hn⟩ ∈
            Subgroup.closure S :=
          Subgroup.subset_closure ⟨⟨n⁻¹, N.inv_mem hn⟩, rfl⟩
        have hmap := Subgroup.mem_map_of_mem N.subtype hxS
        have heq : N.subtype
            ((⟨n⁻¹, N.inv_mem hn⟩ : ↥N)⁻¹ * α ⟨n⁻¹, N.inv_mem hn⟩) = ⁅n, t⁆ := by
          rw [show N.subtype
              ((⟨n⁻¹, N.inv_mem hn⟩ : ↥N)⁻¹ * α ⟨n⁻¹, N.inv_mem hn⟩)
              = (((⟨n⁻¹, N.inv_mem hn⟩ : ↥N)⁻¹ * α ⟨n⁻¹, N.inv_mem hn⟩ : ↥N) : Γ)
              from rfl]
          rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
            commutatorElement_def]
          simp only [Subtype.coe_mk]
          group
        rwa [heq] at hmap
    have hNT : N ≤ T := hgen.trans hcommT
    have htopmap : (⊤ : Subgroup ↥N).map N.subtype ≤ (Subgroup.closure S).map N.subtype := by
      rw [hmapTop]
      exact hNT
    exact top_le_iff.mp ((Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp htopmap)
  have hmain := w162_exp_class_of_inverted hp2 hPN α hα hgenα hcommα hpowα
  refine ⟨p, hpprime, hp2, hPN, ?_, ?_⟩
  · intro x hx
    simpa using congrArg Subtype.val (hmain.1 ⟨x, hx⟩)
  · intro x hx y hy z hz
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      using congrArg Subtype.val (hmain.2 ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩)

end CFSG.LocalAnalysis.WeakClosure81
