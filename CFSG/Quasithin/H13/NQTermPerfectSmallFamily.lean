module

public import CFSG.Quasithin.H13.NQTermTerminalSupport
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup
open CFSG.Quasithin.SteinbergCC (coreQuotConj frattiniQuotConj)

theorem eq_top_of_index_le_four {L : Type*} [Group L] (hL : Group.IsPerfect L) (H : Subgroup L)
    (h0 : H.index ≠ 0) (h4 : H.index ≤ 4) : H = ⊤ := by
  have : H.FiniteIndex := ⟨h0⟩
  have : Finite (L ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have hcard : Nat.card (L ⧸ H) ≤ 4 := by rw [← Subgroup.index_eq_card]; exact h4
  have : Group.IsSolvable (Equiv.Perm (L ⧸ H)) := Equiv.Perm.isSolvable hcard
  have : Group.IsPerfect L := hL
  set φ := MulAction.toPermHom L (L ⧸ H) with hφ
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  refine eq_top_iff.mpr fun g _ => ?_
  have h1 : φ g = 1 := congrArg Subtype.val (Subsingleton.elim (⟨φ g, g, rfl⟩ : φ.range) 1)
  have h2 : g • ((1 : L) : L ⧸ H) = ((1 : L) : L ⧸ H) := by
    have h3 := congrArg (fun σ : Equiv.Perm (L ⧸ H) => σ ((1 : L) : L ⧸ H)) h1
    simpa [hφ, MulAction.toPermHom_apply] using h3
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h2
  exact inv_inv g ▸ H.inv_mem h2

theorem perfect_invariant_family_eq_empty {L : Type*} [Group L] [Finite L]
    (hL : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (A X : Subgroup L) [A.Normal] [X.Normal]
    (hAX : A ≤ X) (hA : ¬p ∣ Nat.card A) {d : ℕ}
    (hXe : CFSG.IsElementaryAbelian p (X.map (QuotientGroup.mk' A)))
    (hXcard : Nat.card (X.map (QuotientGroup.mk' A)) = p ^ d) (P : Subgroup L)
    (hP : ∃ S : Sylow p X, (S : Subgroup X).map X.subtype = P)
    (hirr : ∀ W : Subgroup (L ⧸ A), W ≤ X.map (QuotientGroup.mk' A) →
      (∀ g : L, ∀ w ∈ W, (g : L ⧸ A) * w * (g : L ⧸ A)⁻¹ ∈ W) →
      W = ⊥ ∨ W = X.map (QuotientGroup.mk' A))
    (T : Set (Subgroup L)) (hTf : T.Finite) (hT4 : T.ncard ≤ 4)
    (hTP : ∀ Q ∈ T, Q ≤ P ∧ Q ≠ ⊥ ∧ Q ≠ P)
    (hTn : ∀ n ∈ normalizer (P : Set L), ∀ Q ∈ T, Q.map (MulAut.conj n).toMonoidHom ∈ T) :
    T = ∅ := by
  classical
  obtain ⟨⟨hPA, hPX⟩, -, hconj, -, -⟩ :=
    SteinbergBT.coprime_abelian_quotient_Sylow_action_transport hp A X hAX hA hXe hXcard P hP
  have hPXle : P ≤ X := by
    obtain ⟨S, rfl⟩ := hP
    exact Subgroup.map_subtype_le _
  set π := QuotientGroup.mk' A with hπ
  have hmapmul : ∀ (W : Subgroup (L ⧸ A)) (a b : L ⧸ A),
      W.map (MulAut.conj (a * b)).toMonoidHom =
        (W.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro W a b
    rw [Subgroup.map_map, map_mul]
    rfl
  refine Set.eq_empty_iff_forall_notMem.mpr fun Q hQ => ?_
  obtain ⟨hQP, hQ1, hQP'⟩ := hTP Q hQ
  set Qb := Q.map π with hQb
  have hQbX : Qb ≤ X.map π := Subgroup.map_mono (hQP.trans hPXle)
  set S : Set (Subgroup (L ⧸ A)) := (fun R : Subgroup L => R.map π) '' T with hS
  have hconjS : ∀ g : L, Qb.map (MulAut.conj (π g)).toMonoidHom ∈ S := by
    intro g
    obtain ⟨n, hn, hgn⟩ := hconj g
    refine ⟨Q.map (MulAut.conj n).toMonoidHom, hTn n hn Q hQ, ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨π q, ⟨q, hq, rfl⟩, ?_⟩
      have h1 := hgn (π q) (hQbX ⟨q, hq, rfl⟩)
      change (g : L ⧸ A) * π q * (g : L ⧸ A)⁻¹ = π (n * q * n⁻¹)
      rw [h1, map_mul, map_mul, map_inv]
      rfl
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨n * q * n⁻¹, ⟨q, hq, rfl⟩, ?_⟩
      have h1 := hgn (π q) (hQbX ⟨q, hq, rfl⟩)
      change π (n * q * n⁻¹) = (g : L ⧸ A) * π q * (g : L ⧸ A)⁻¹
      rw [h1, map_mul, map_mul, map_inv]
      rfl
  set H := (normalizer (Qb : Set (L ⧸ A))).comap π with hH
  have hmemH : ∀ a b : L, a⁻¹ * b ∈ H ↔
      Qb.map (MulAut.conj (π a)).toMonoidHom = Qb.map (MulAut.conj (π b)).toMonoidHom := by
    intro a b
    have h1 : a⁻¹ * b ∈ H ↔ Qb.map (MulAut.conj (π (a⁻¹ * b))).toMonoidHom = Qb :=
      Subgroup.mem_normalizer_iff_map_conj_eq
    rw [h1]
    constructor
    · intro h
      rw [show π b = π a * π (a⁻¹ * b) by rw [← map_mul, mul_inv_cancel_left], hmapmul, h]
    · intro h
      rw [map_mul, hmapmul, ← h, ← hmapmul, map_inv, inv_mul_cancel, map_one]
      exact Subgroup.map_id Qb
  let ι : L ⧸ H → S := Quotient.lift (fun g : L => (⟨Qb.map (MulAut.conj (π g)).toMonoidHom,
      hconjS g⟩ : S)) fun a b hab =>
    Subtype.ext ((hmemH a b).mp (QuotientGroup.leftRel_apply.mp hab))
  have hι : Function.Injective ι := by
    intro u v huv
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.eq, hmemH]
    exact congrArg Subtype.val huv
  have hidx : H.index ≤ 4 := by
    rw [Subgroup.index_eq_card]
    calc Nat.card (L ⧸ H) ≤ Nat.card S := Nat.card_le_card_of_injective ι hι
      _ = S.ncard := Nat.card_coe_set_eq S
      _ ≤ T.ncard := Set.ncard_image_le hTf
      _ ≤ 4 := hT4
  have hHtop : H = ⊤ := eq_top_of_index_le_four hL H Subgroup.index_ne_zero_of_finite hidx
  have hinv : ∀ g : L, ∀ w ∈ Qb, (g : L ⧸ A) * w * (g : L ⧸ A)⁻¹ ∈ Qb := by
    intro g w hw
    have hg : g ∈ H := hHtop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  rcases hirr Qb hQbX hinv with h | h
  · apply hQ1
    refine eq_bot_iff.mpr fun q hq => ?_
    have hqA : q ∈ A := by
      have h1 : π q ∈ Qb := ⟨q, hq, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff q).mp h1
    have h2 : q ∈ P ⊓ A := ⟨hQP hq, hqA⟩
    rwa [hPA] at h2
  · apply hQP'
    refine le_antisymm hQP fun x hx => ?_
    have h1 : π x ∈ Qb := by
      rw [h, ← hPX]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have hy' : y ∈ Q := hy
    have h2 : y⁻¹ * x ∈ P ⊓ A :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hQP hy')) hx, QuotientGroup.eq.mp hyx⟩
    rw [hPA, Subgroup.mem_bot, inv_mul_eq_one] at h2
    rw [← h2]
    exact hy

theorem sylow_bijective_coreQuot {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (P₀ : Sylow p X) :
    Function.Bijective ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp (P₀ : Subgroup X).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint (P₀ : Subgroup X) (CFSG.pCore 2 X) :=
    IsPGroup.disjoint_of_ne p 2 hp2 _ _ P₀.isPGroup' CFSG.pCore_isPGroup
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : X) ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : X) ∈ (P₀ : Subgroup X) ⊓ CFSG.pCore 2 X := ⟨x.2, h1⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  · have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
      QuotientGroup.mk'_surjective _
    have htop : ((P₀.mapSurjective hsurj : Sylow p (X ⧸ CFSG.pCore 2 X)) :
        Subgroup (X ⧸ CFSG.pCore 2 X)) = ⊤ :=
      ((P₀.mapSurjective hsurj).is_maximal' (hP.to_subgroup ⊤) le_top).symm
    intro y
    have hy : y ∈ ((P₀.mapSurjective hsurj : Sylow p (X ⧸ CFSG.pCore 2 X)) :
        Subgroup (X ⧸ CFSG.pCore 2 X)) := htop ▸ Subgroup.mem_top y
    rw [Sylow.coe_mapSurjective] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩

theorem map_inf_centralizer_le_iff {L : Type*} [Group L] {X : Subgroup L} (B : Subgroup X)
    (a₀ : X) : B.map X.subtype ⊓ centralizer {(a₀ : L)} ≤ (center X).map X.subtype ↔
      B ⊓ centralizer {a₀} ≤ center X := by
  constructor
  · intro h w hw
    obtain ⟨hwB, hwc⟩ := Subgroup.mem_inf.mp hw
    have hwc' : w * a₀ = a₀ * w := Subgroup.mem_centralizer_singleton_iff.mp hwc
    have h1 : (w : L) ∈ B.map X.subtype ⊓ centralizer {(a₀ : L)} :=
      Subgroup.mem_inf.mpr ⟨⟨w, hwB, rfl⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hwc')⟩
    obtain ⟨z, hz, hzw⟩ := h h1
    rwa [← Subtype.ext hzw]
  · intro h y hy
    obtain ⟨hyB, hyc⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨w, hwB, rfl⟩ := hyB
    have hwc : (w : L) * a₀ = a₀ * w := Subgroup.mem_centralizer_singleton_iff.mp hyc
    refine ⟨w, h (Subgroup.mem_inf.mpr ⟨hwB, ?_⟩), rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hwc)

theorem false_of_small_centralizer_family {L : Type*} [Group L] [Finite L]
    (hL : Group.IsPerfect L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup L} [X.Normal]
    (hA1 : CFSG.pCore 2 X ≠ ⊥)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hP : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : L, ∀ u ∈ U, frattiniQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (P₀ : Sylow p X) (hPe : CFSG.IsElementaryAbelian p (P₀ : Subgroup X))
    (hPc : Nat.card (P₀ : Subgroup X) = p ^ 2)
    (R : Set (Subgroup X)) (hRf : R.Finite) (hR4 : R.ncard ≤ 4)
    (hR : ∀ a ∈ (P₀ : Subgroup X), a ≠ 1 →
      ¬ CFSG.pCore 2 X ⊓ centralizer {a} ≤ center X → zpowers a ∈ R) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A₀ := CFSG.pCore 2 X with hA₀
  have hA₀n : A₀.Normal := CFSG.pCore_normal
  have hA₀p : IsPGroup 2 A₀ := CFSG.pCore_isPGroup
  set P₁ : Subgroup X := (P₀ : Subgroup X) with hP₁
  have hbij := sylow_bijective_coreQuot hp2 hP P₀
  set e₀ : P₁ ≃* X ⧸ A₀ := MulEquiv.ofBijective _ hbij with he₀
  have he₀mk : ∀ u : P₁, e₀ u = ((u : X) : X ⧸ A₀) := fun _ => rfl
  have hPpow : ∀ u ∈ P₁, u ^ p = 1 := fun u hu => CFSG.elemPow_eq_one_of_isElementaryAbelian u hu
  have hXqc : Nat.card (X ⧸ A₀) = p ^ 2 := by rw [← Nat.card_congr e₀.toEquiv, hPc]
  have : IsMulCommutative (X ⧸ A₀) := ⟨⟨fun x y => e₀.symm.injective (by
    rw [map_mul, map_mul]
    exact hPe.toIsMulCommutative.is_comm.comm _ _)⟩⟩
  have hXqe : CFSG.IsElementaryAbelian p (X ⧸ A₀) := by
    refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_⟩
    obtain ⟨u, rfl⟩ := e₀.surjective x
    rw [← map_pow, show u ^ p = 1 from Subtype.ext (hPpow u u.2), map_one]
  have hΦ : frattini (X ⧸ A₀) = ⊥ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini (X ⧸ A₀))
    rw [hW, hXqc] at h
    have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
    have h1 : Nat.card (frattini (X ⧸ A₀)) = 1 := by
      have h2 : p ^ 2 * 1 = p ^ 2 * Nat.card (frattini (X ⧸ A₀)) := by rw [mul_one]; exact h
      exact (Nat.eq_of_mul_eq_mul_left hp0 h2).symm
    exact Subgroup.eq_bot_of_card_eq _ h1
  have hirr' : ∀ U : Subgroup (X ⧸ A₀), (∀ l : L, ∀ u ∈ U, coreQuotConj X l u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    set φ := QuotientGroup.mk' (frattini (X ⧸ A₀)) with hφ
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hΦ, Subgroup.mem_bot] at hx
      exact hx
    rcases hirr (U.map φ) (by
      rintro l _ ⟨u, hu, rfl⟩
      rw [hφ, QuotientGroup.mk'_apply, SteinbergCC.frattiniQuotConj_mk]
      exact ⟨_, hU l u hu, rfl⟩) with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective U hφinj).mp h)
    · refine Or.inr (eq_top_iff.mpr fun x _ => ?_)
      have hx : φ x ∈ U.map φ := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [← hφinj hyx]
  set A := A₀.map X.subtype with hAdef
  have hAn : A.Normal := normal_map_pCore 2 X
  obtain ⟨hXe', hXc', hirrL⟩ := map_mk_facts_of_coreQuot X A rfl hXqe hirr'
  set P := P₁.map X.subtype with hPdef
  have hpA : ¬ p ∣ Nat.card A := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (hA₀p.map X.subtype) : ∃ n, Nat.card A = 2 ^ n)
    rw [hn]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  set Zx := (center X).map X.subtype with hZx
  have hZxn : Zx.Normal := ConjAct.normal_of_characteristic_of_normal
  set T : Set (Subgroup L) := {Q | ∃ a ∈ P, a ≠ 1 ∧ Q = zpowers a ∧
    ¬ A ⊓ centralizer {a} ≤ Zx} with hT
  have hPpowL : ∀ a ∈ P, a ^ p = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hPpow u hu, Subgroup.coe_one]
  have hPcL : Nat.card P = p ^ 2 := by
    rw [hPdef, Subgroup.card_map_of_injective X.subtype_injective, hPc]
  have hTsub : T ⊆ (fun Q : Subgroup X => Q.map X.subtype) '' R := by
    rintro Q ⟨_, ⟨a₀, ha₀, rfl⟩, ha1, rfl, hac⟩
    have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [h, map_one])
    rw [Subgroup.coe_subtype, map_inf_centralizer_le_iff] at hac
    exact ⟨zpowers a₀, hR a₀ ha₀ ha₀1 hac, MonoidHom.map_zpowers _ _⟩
  have hTf : T.Finite := (hRf.image _).subset hTsub
  have hT4 : T.ncard ≤ 4 :=
    (Set.ncard_le_ncard hTsub (hRf.image _)).trans ((Set.ncard_image_le hRf).trans hR4)
  have hTP : ∀ Q ∈ T, Q ≤ P ∧ Q ≠ ⊥ ∧ Q ≠ P := by
    rintro Q ⟨a, ha, ha1, rfl, -⟩
    refine ⟨Subgroup.zpowers_le.mpr ha, fun h => ha1 ?_, fun h => ?_⟩
    · have h1 : a ∈ zpowers a := Subgroup.mem_zpowers a
      rw [h, Subgroup.mem_bot] at h1
      exact h1
    · have h1 : Nat.card (zpowers a) = p := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hPpowL a ha) ha1
      rw [h, hPcL] at h1
      have h2 : p ^ 1 = p ^ 2 := by rw [pow_one]; exact h1.symm
      have := Nat.pow_right_injective hp.two_le h2
      omega
  have hTn : ∀ n ∈ normalizer (P : Set L), ∀ Q ∈ T, Q.map (MulAut.conj n).toMonoidHom ∈ T := by
    rintro n hn Q ⟨a, ha, ha1, rfl, hac⟩
    refine ⟨n * a * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn a).mp ha, ?_, ?_, ?_⟩
    · intro h
      apply ha1
      have h1 : a = n⁻¹ * (n * a * n⁻¹) * n := by group
      rw [h1, h, mul_one, inv_mul_cancel]
    · rw [MonoidHom.map_zpowers]
      rfl
    · intro h
      apply hac
      intro w hw
      obtain ⟨hwA, hwc⟩ := Subgroup.mem_inf.mp hw
      have hwc' : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.mp hwc
      have h1 : n * w * n⁻¹ ∈ A ⊓ centralizer {n * a * n⁻¹} := by
        refine Subgroup.mem_inf.mpr ⟨hAn.conj_mem w hwA n,
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc n * w * n⁻¹ * (n * a * n⁻¹) = n * (w * a) * n⁻¹ := by group
          _ = n * (a * w) * n⁻¹ := by rw [hwc']
          _ = n * a * n⁻¹ * (n * w * n⁻¹) := by group
      have h2 := hZxn.conj_mem _ (h h1) n⁻¹
      have h3 : n⁻¹ * (n * w * n⁻¹) * n⁻¹⁻¹ = w := by group
      rwa [h3] at h2
  have hTe := perfect_invariant_family_eq_empty hL hp A X (Subgroup.map_subtype_le _) hpA hXe'
    (hXc'.trans hXqc) P ⟨P₀, rfl⟩ hirrL T hTf hT4 hTP hTn
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hp
    (A := P₁) (X := A₀) ⟨inferInstance, hPpow⟩ (by rw [hPc]) (by
      rw [Subgroup.normalizer_eq_top]
      exact le_top) (by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hA₀p : ∃ n, Nat.card A₀ = 2 ^ n)
      rw [hn]
      exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2 |>.pow_right n)
  by_cases hex : ∃ a₀ ∈ P₁, a₀ ≠ 1 ∧ ¬ A₀ ⊓ centralizer {a₀} ≤ center X
  · obtain ⟨a₀, ha₀, ha₀1, hac⟩ := hex
    have hmem : zpowers (a₀ : L) ∈ T := by
      refine ⟨a₀, ⟨a₀, ha₀, rfl⟩, fun h => ha₀1 (Subtype.ext h), rfl, ?_⟩
      rwa [map_inf_centralizer_le_iff]
    rw [hTe] at hmem
    exact hmem
  · push Not at hex
    have hAZ : A₀ ≤ center X := by
      rw [← hgen]
      exact iSup₂_le fun a ha => iSup_le fun ha1 => hex a ha ha1
    have hdecomp : ∀ x : X, ∃ u ∈ P₁, ∃ c ∈ A₀, x = u * c := by
      intro x
      obtain ⟨u, hu⟩ := hbij.2 (x : X ⧸ A₀)
      refine ⟨u, u.2, (u : X)⁻¹ * x, ?_, by group⟩
      rw [← QuotientGroup.eq]
      exact hu
    have hPn : P₁.Normal := by
      refine ⟨fun v hv x => ?_⟩
      obtain ⟨u, hu, c, hc, rfl⟩ := hdecomp x
      have hcz : c * v = v * c := (Subgroup.mem_center_iff.mp (hAZ hc) v).symm
      have h1 : u * c * v * (u * c)⁻¹ = u * v * u⁻¹ := by
        calc u * c * v * (u * c)⁻¹ = u * (c * v) * c⁻¹ * u⁻¹ := by group
          _ = u * (v * c) * c⁻¹ * u⁻¹ := by rw [hcz]
          _ = u * v * u⁻¹ := by group
      rw [h1]
      exact mul_mem (mul_mem hu hv) (inv_mem hu)
    have hP2 : IsPGroup 2 (X ⧸ P₁) := by
      refine IsPGroup.of_surjective hA₀p ((QuotientGroup.mk' P₁).comp A₀.subtype) ?_
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P₁ y
      obtain ⟨u, hu, c, hc, rfl⟩ := hdecomp x
      refine ⟨⟨c, hc⟩, ?_⟩
      change ((c : X) : X ⧸ P₁) = ((u * c : X) : X ⧸ P₁)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff u).mpr hu, one_mul]
    have htop : P₁ = ⊤ := hX2 P₁ hP2
    apply hA1
    have hdisj : Disjoint P₁ A₀ :=
      IsPGroup.disjoint_of_ne p 2 hp2 _ _ P₀.isPGroup' hA₀p
    refine eq_bot_iff.mpr fun c hc => ?_
    have h1 : c ∈ P₁ ⊓ A₀ := ⟨htop ▸ Subgroup.mem_top c, hc⟩
    rwa [disjoint_iff.mp hdisj] at h1

end CFSG.Quasithin.H13.NQTerm
