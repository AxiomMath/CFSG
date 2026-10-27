module

public import CFSG.GH74.Uniqueness.Bender.SuzukiAut
public import CFSG.GH74.Uniqueness.Bender.Sylow2Special
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.Background.RonanF13Defs
public import CFSG.GroupTheory.CoprimeQuotientNormalizer

public section

namespace CFSG.Quasithin.Stroth

open CFSG.GH74.Uniqueness.Bender
open Subgroup

private structure StatedSUActionData (X : Type) [Group X] [Finite X] (n : ℕ) (σ : MulAut X) where
  hZodd : Odd (Nat.card (Subgroup.center X))
  e' : ℕ
  hBquot : BenderType (X ⧸ Subgroup.center X) n 3 e'
  Tbar : Sylow 2 (X ⧸ Subgroup.center X)
  Hbar : Subgroup (X ⧸ Subgroup.center X)
  hHbar_le : Hbar ≤ Subgroup.normalizer
    ((Tbar : Subgroup (X ⧸ Subgroup.center X)) : Set (X ⧸ Subgroup.center X))
  hHbarodd : Odd (Nat.card Hbar)
  hTHbar : (Tbar : Subgroup (X ⧸ Subgroup.center X)) ⊔ Hbar =
    Subgroup.normalizer ((Tbar : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X))
  σbar : MulAut (X ⧸ Subgroup.center X)
  hσbar_mk : ∀ x : X, σbar (QuotientGroup.mk x) = QuotientGroup.mk (σ x)
  hσbar_pow : ∃ k : ℕ, σbar ^ (2 ^ k) = 1
  hσbarT : ∀ x ∈ (Tbar : Subgroup (X ⧸ Subgroup.center X)),
    σbar x ∈ (Tbar : Subgroup (X ⧸ Subgroup.center X))
  hσbarH : ∀ x ∈ Hbar, σbar x = x

private theorem eq_one_of_conj_of_odd {K : Type} [Group K] {D : Subgroup K} {d₀ : K}
    (hd₀ : d₀ ∈ D) (hDodd : Odd (Nat.card D)) (hcenter : Subgroup.center K = ⊥)
    (σ : MulAut K) (hconj : ∀ k, σ k = d₀ * k * d₀⁻¹)
    (hpow : ∃ m : ℕ, σ ^ (2 ^ m) = 1) : σ = 1 := by
  have hσ : σ = MulAut.conj d₀ := MulEquiv.ext hconj
  obtain ⟨m, hm⟩ := hpow
  have hd₀pow : d₀ ^ (2 ^ m) = 1 := by
    have h1 : (MulAut.conj d₀) ^ (2 ^ m) = 1 := by rw [← hσ]; exact hm
    rw [← map_pow] at h1
    have hcent : d₀ ^ (2 ^ m) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut K => f x) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * d₀ ^ (2 ^ m) = (d₀ ^ (2 ^ m) * x * (d₀ ^ (2 ^ m))⁻¹) * d₀ ^ (2 ^ m) := by
            rw [hx]
        _ = d₀ ^ (2 ^ m) * x := by group
    rw [hcenter, Subgroup.mem_bot] at hcent
    exact hcent
  have hordodd : Odd (orderOf d₀) :=
    Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hd₀)
  have hdvd : orderOf d₀ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hd₀pow
  have hcop : Nat.Coprime (orderOf d₀) (2 ^ m) :=
    (Nat.coprime_two_right.mpr hordodd).pow_right m
  have hone : orderOf d₀ = 1 := hcop.eq_one_of_dvd hdvd
  rw [hσ, orderOf_eq_one_iff.mp hone]
  exact map_one (MulAut.conj : K →* MulAut K)

private theorem exists_conj_cartan_of_complement {K : Type} [Group K] [Finite K]
    {q i e : ℕ} {P : Subgroup K} {t : K} (hc : BenderCore q i e P t)
    (hP2 : IsPGroup 2 P)
    {H : Subgroup K} (hH : H ≤ borel P) (hHodd : Odd (Nat.card H))
    (hTH : P ⊔ H = borel P) :
    ∃ g ∈ P, H = (cartan P t).map (MulAut.conj g).toMonoidHom := by
  classical
  let N : Subgroup K := borel P
  have hPle : P ≤ N := le_borel P
  have hHle : H ≤ N := hH
  letI : (P.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hPHinf : P ⊓ H = ⊥ := CFSG.Quasithin.RonanF13.inf_eq_bot_of_odd hP2 hHodd
  have hDle : cartan P t ≤ N := cartan_le_borel P t
  have hcompH : (P.subgroupOf N).IsComplement' (H.subgroupOf N) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext x
      constructor
      · rintro ⟨hxP, hxH⟩
        apply Subtype.ext
        have hx : (x : K) ∈ P ⊓ H := ⟨hxP, hxH⟩
        rwa [hPHinf, Subgroup.mem_bot] at hx
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact ⟨(P.subgroupOf N).one_mem, (H.subgroupOf N).one_mem⟩
    · have hsup : P.subgroupOf N ⊔ H.subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hPle hHle, hTH, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul (P.subgroupOf N) (H.subgroupOf N), hsup]
      rfl
  have hcompD : (P.subgroupOf N).IsComplement' ((cartan P t).subgroupOf N) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext x
      constructor
      · rintro ⟨hxP, hxD⟩
        apply Subtype.ext
        have hx : (x : K) ∈ P ⊓ cartan P t := ⟨hxP, hxD⟩
        rwa [hc.inf_eq, Subgroup.mem_bot] at hx
      · intro hx
        rw [Subgroup.mem_bot] at hx
        subst hx
        exact ⟨(P.subgroupOf N).one_mem, ((cartan P t).subgroupOf N).one_mem⟩
    · have hsup : P.subgroupOf N ⊔ (cartan P t).subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hPle hDle, hc.sup_eq, Subgroup.subgroupOf_self]
      rw [← Subgroup.normal_mul (P.subgroupOf N) ((cartan P t).subgroupOf N), hsup]
      rfl
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf N)) (P.subgroupOf N).index := by
    rw [hcompH.symm.index_eq_card]
    have hcardH : Nat.card (H.subgroupOf N) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
    rw [hcardH]
    have hcardP : Nat.card (P.subgroupOf N) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv
    obtain ⟨m, hm⟩ := hP2.exists_card_eq
    rw [hcardP, hm]
    exact (Nat.coprime_two_left.mpr hHodd).pow_left m
  obtain ⟨n, hn⟩ :=
    CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      (P.subgroupOf N) ((cartan P t).subgroupOf N) (H.subgroupOf N)
      (Subgroup.normal_in_normalizer) hcompD hcompH hcop
  refine ⟨((n : N) : K), n.2, ?_⟩
  have hnK := congrArg (fun X : Subgroup N => X.map N.subtype) hn
  rw [Subgroup.map_subgroupOf_eq_of_le hHle, Subgroup.map_map] at hnK
  have hcomp : (N.subtype.comp (MulAut.conj (n : N)).toMonoidHom) =
      ((MulAut.conj (((n : N) : K))).toMonoidHom.comp N.subtype) := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hDle] at hnK
  exact hnK

private theorem aut_eq_one_of_benderType_linear
    {K : Type} [Group K] [Finite K] {n : ℕ}
    (h : BenderType K n 1 1) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) : σ = 1 := by
  have hc := h.benderCore Q ht htQ
  obtain ⟨d₀, hd₀, hσd₀⟩ :=
    h.aut_eq_conj_cartan_linear (Q := Q) (t := t) (ht := ht) (htQ := htQ) (σ := σ)
      (hσQ := hσQ) (hσD := hσD)
  exact eq_one_of_conj_of_odd hd₀ hc.odd_card_cartan h.center_eq_bot σ hσd₀ hσ

private theorem aut_eq_one_of_benderType_suzuki
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 2 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) : σ = 1 := by
  cases h with
  | suzuki a ha e =>
    have hB : BenderType K (2 * a + 1) 2 1 := .suzuki a ha e
    have hc := hB.benderCore Q ht htQ
    obtain ⟨d₀, hd₀, hσd₀⟩ :=
      hB.aut_eq_conj_cartan_suzuki (Q := Q) (t := t) (ht := ht) (htQ := htQ) (σ := σ)
        (hσQ := hσQ) (hσD := hσD)
    exact eq_one_of_conj_of_odd hd₀ hc.odd_card_cartan hB.center_eq_bot σ hσd₀ hσ


private theorem unitary_fixes_rootCenter
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) :
    ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z := by
  classical
  have hc := h.benderCore Q ht htQ
  set Z : Subgroup K := rootCenter (Q : Subgroup K) with hZdef
  have hn2 : 2 ≤ n := h.two_le.2
  have hQmap_le : (Q : Subgroup K).map σ.toMonoidHom ≤ (Q : Subgroup K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hσQ x hx
  have hQmap : (Q : Subgroup K).map σ.toMonoidHom = (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hQmap_le (by rw [Subgroup.card_map_of_injective σ.injective])
  have hZmap : Z.map σ.toMonoidHom = Z := by
    rw [hZdef, ← rootCenter_map σ (Q : Subgroup K), hQmap]
  let eZ : Z ≃* Z.map σ.toMonoidHom :=
    Subgroup.equivMapOfInjective Z σ.toMonoidHom σ.injective
  let σZ : MulAut Z := eZ.trans (MulEquiv.subgroupCongr hZmap)
  have hσZapply : ∀ z : Z, ((σZ z : Z) : K) = σ (z : K) := fun z => rfl
  have hσZpow_apply : ∀ m : ℕ, ∀ z : Z, ((σZ ^ m) z : K) = (σ ^ m) (z : K) := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [pow_succ]
      change (((σZ ^ m) (σZ z) : Z) : K) = (σ ^ m * σ) (z : K)
      rw [ih, hσZapply]
      rfl
  have hσZpow : ∃ m : ℕ, σZ ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hσ
    refine ⟨m, ?_⟩
    ext z
    rw [hσZpow_apply, hm]
    rfl
  have hZact : IsPGroup 2 (Subgroup.zpowers σZ) := by
    obtain ⟨m, hm⟩ := hσZpow
    have hdvd : orderOf σZ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hZeven : 2 ∣ Nat.card Z := by
    rw [hZdef, hc.card_center]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z₀, hz₀fix, hz₀ne⟩ :=
    hZact.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := Z) hZeven
      (a := 1) (by rw [MulAction.mem_fixedPoints]; intro g; simp)
  have hz₀σ : σZ z₀ = z₀ := by
    have := hz₀fix ⟨σZ, Subgroup.mem_zpowers σZ⟩
    simpa using this
  have hz₀σK : σ (z₀ : K) = (z₀ : K) := by
    have := congrArg (fun z : Z => (z : K)) hz₀σ
    rwa [hσZapply] at this
  have hz₀neK : (z₀ : K) ≠ 1 := by
    intro h1
    exact hz₀ne (Subtype.ext h1).symm
  have hz₀Z : (z₀ : K) ∈ Z := z₀.2
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  · obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hz₀Z hz₀neK hz hz1
    have hσd : σ d = d := hσD d hd
    have hσdinv : σ d⁻¹ = d⁻¹ := by rw [map_inv, hσd]
    calc σ z = σ (d⁻¹ * (z₀ : K) * d) := by rw [hdz]
      _ = d⁻¹ * σ (z₀ : K) * σ d := by rw [map_mul, map_mul, hσdinv, hσd]
      _ = d⁻¹ * (z₀ : K) * d := by rw [hz₀σK, hσd]
      _ = z := by rw [hdz]

private theorem unitary_cocycle_mul
    {K : Type} [Group K] {Q Z : Subgroup K} {σ : MulAut K}
    (hσQ : ∀ x ∈ Q, σ x ∈ Q) (hZQ : Z ≤ Q)
    (hcentral : ∀ {z : K}, z ∈ Z → ∀ q ∈ Q, q * z = z * q)
    {x y : K} (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hxZ : x⁻¹ * σ x ∈ Z) (hyZ : y⁻¹ * σ y ∈ Z) :
    (x * y)⁻¹ * σ (x * y) = (x⁻¹ * σ x) * (y⁻¹ * σ y) := by
  have hxσy : (x⁻¹ * σ x) * σ y = σ y * (x⁻¹ * σ x) :=
    (hcentral hxZ (σ y) (hσQ y hyQ)).symm
  have hab : (x⁻¹ * σ x) * (y⁻¹ * σ y) = (y⁻¹ * σ y) * (x⁻¹ * σ x) :=
    (hcentral hxZ (y⁻¹ * σ y) (hZQ hyZ)).symm
  calc (x * y)⁻¹ * σ (x * y) = y⁻¹ * (x⁻¹ * σ x) * σ y := by
        rw [map_mul]
        group
    _ = y⁻¹ * ((x⁻¹ * σ x) * σ y) := by group
    _ = y⁻¹ * (σ y * (x⁻¹ * σ x)) := by rw [hxσy]
    _ = (y⁻¹ * σ y) * (x⁻¹ * σ x) := by group
    _ = (x⁻¹ * σ x) * (y⁻¹ * σ y) := hab.symm

private theorem quotient_congr_pow_eq_one
    {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (e : MulAut K) (he : N.map (e : K →* K) = N)
    (hpow : ∃ k : ℕ, e ^ (2 ^ k) = 1) :
    ∃ k : ℕ, (QuotientGroup.congr N N e he) ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hpow
  refine ⟨k, ?_⟩
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hiter : ∀ m : ℕ, ∀ y : K,
      ((QuotientGroup.congr N N e he) ^ m) (QuotientGroup.mk y) =
        QuotientGroup.mk ((e ^ m) y) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ]
      change ((QuotientGroup.congr N N e he) ^ m)
        ((QuotientGroup.congr N N e he) (QuotientGroup.mk y)) =
          QuotientGroup.mk ((e ^ (m + 1)) y)
      rw [QuotientGroup.congr_mk, ih (e y), pow_succ]
      rfl
  rw [hiter (2 ^ k) x, hk]
  rfl

private theorem unitary_fixed_cosets
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d)
    (hZfix : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z) :
    ∃ W : Subgroup K, (∀ x : K, x ∈ W ↔
        x ∈ (Q : Subgroup K) ∧ x⁻¹ * σ x ∈ rootCenter (Q : Subgroup K)) ∧
      rootCenter (Q : Subgroup K) ≤ W ∧
      W ≤ (Q : Subgroup K) ∧
      (∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ W, d * w * d⁻¹ ∈ W) := by
  classical
  set Z : Subgroup K := rootCenter (Q : Subgroup K) with hZdef
  set D : Subgroup K := cartan (Q : Subgroup K) t with hDdef
  have hZQ : Z ≤ (Q : Subgroup K) := rootCenter_le _
  have hcentral : ∀ {z : K}, z ∈ Z → ∀ q ∈ (Q : Subgroup K), q * z = z * q :=
    fun hz q hq => (mem_rootCenter_iff.mp (hZdef ▸ hz)).2 q hq
  let W : Subgroup K :=
    { carrier := {x | x ∈ (Q : Subgroup K) ∧ x⁻¹ * σ x ∈ Z}
      one_mem' := by simp
      mul_mem' := by
        rintro x y ⟨hxQ, hxZ⟩ ⟨hyQ, hyZ⟩
        exact ⟨(Q : Subgroup K).mul_mem hxQ hyQ,
          by rw [unitary_cocycle_mul hσQ hZQ hcentral hxQ hyQ hxZ hyZ]
             exact Z.mul_mem hxZ hyZ⟩
      inv_mem' := by
        rintro x ⟨hxQ, hxZ⟩
        refine ⟨(Q : Subgroup K).inv_mem hxQ, ?_⟩
        set a : K := x⁻¹ * σ x with ha
        have hσx : σ x = x * a := by rw [ha]; group
        have hxa : x * a = a * x := hcentral hxZ x hxQ
        have hxainv : a⁻¹ * x = x * a⁻¹ := by
          calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * x) * a⁻¹ := by rw [hxa]
            _ = x * a⁻¹ := by group
        rw [map_inv, hσx, mul_inv_rev, inv_inv]
        have heq : x * (a⁻¹ * x⁻¹) = a⁻¹ := by
          calc x * (a⁻¹ * x⁻¹) = (x * a⁻¹) * x⁻¹ := by group
            _ = (a⁻¹ * x) * x⁻¹ := by rw [← hxainv]
            _ = a⁻¹ := by group
        rw [heq]
        exact Z.inv_mem hxZ }
  refine ⟨W, fun x => Iff.rfl, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨rootCenter_le _ hz, ?_⟩
    rw [hZfix z hz]
    simpa using Z.one_mem
  · exact fun _ hx => hx.1
  · intro d hd w hw
    have hdN : d ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
      cartan_le_borel (Q : Subgroup K) t hd
    refine ⟨(Subgroup.mem_normalizer_iff.mp hdN w).mp hw.1, ?_⟩
    have hσd : σ d = d := hσD d hd
    have hσdinv : σ d⁻¹ = d⁻¹ := by rw [map_inv, hσd]
    have heq : (d * w * d⁻¹)⁻¹ * σ (d * w * d⁻¹) = d * (w⁻¹ * σ w) * d⁻¹ := by
      rw [map_mul, map_mul, hσd, hσdinv]
      group
    rw [heq]
    exact conj_mem_rootCenter hdN hw.2

private theorem unitary_sylow_quotient_aut
    {K : Type} [Group K] [Finite K] (Q : Subgroup K) {σ : MulAut K}
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ Q, σ x ∈ Q)
    (hZfix : ∀ z ∈ rootCenter Q, σ z = z) :
    ∃ σbar : MulAut (Q ⧸ (rootCenter Q).subgroupOf Q),
      (∀ x : Q, σbar (QuotientGroup.mk x) =
        QuotientGroup.mk (⟨σ (x : K), hσQ x x.2⟩ : Q)) ∧
      (∃ k : ℕ, σbar ^ (2 ^ k) = 1) := by
  classical
  set Z : Subgroup K := rootCenter Q with hZdef
  let Zsub : Subgroup Q := Z.subgroupOf Q
  let eQ : Q ≃* Q.map σ.toMonoidHom :=
    Subgroup.equivMapOfInjective Q σ.toMonoidHom σ.injective
  have hQmap : Q.map σ.toMonoidHom = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩; exact hσQ x hx
    · rw [Subgroup.card_map_of_injective σ.injective]
  let σQ : MulAut Q := eQ.trans (MulEquiv.subgroupCongr hQmap)
  have hσQapply : ∀ x : Q, ((σQ x : Q) : K) = σ (x : K) := fun x => rfl
  have hZsubmap : Zsub.map σQ = Zsub := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      change σ (z : K) ∈ Z
      rw [hZfix (z : K) hz]
      exact hz
    · intro hx
      refine ⟨x, hx, ?_⟩
      apply Subtype.ext
      change σ (x : K) = (x : K)
      rw [hZfix (x : K) hx]
  let σbar : MulAut (Q ⧸ Zsub) := QuotientGroup.congr Zsub Zsub σQ hZsubmap
  have hσbar_mk : ∀ x : Q, σbar (QuotientGroup.mk x) = QuotientGroup.mk (σQ x) :=
    fun x => QuotientGroup.congr_mk Zsub Zsub σQ hZsubmap x
  have hσbar_pow : ∃ m : ℕ, σbar ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := hσ
    refine ⟨m, ?_⟩
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hiter : ∀ j : ℕ, ∀ y : Q,
        (σbar ^ j) (QuotientGroup.mk y) = QuotientGroup.mk ((σQ ^ j) y) := by
      intro j
      induction j with
      | zero => intro y; simp
      | succ j ih =>
        intro y
        rw [pow_succ]
        change (σbar ^ j) (σbar (QuotientGroup.mk y)) =
          QuotientGroup.mk ((σQ ^ (j + 1)) y)
        rw [hσbar_mk, ih, pow_succ]
        rfl
    have hσQpow_apply : ∀ j : ℕ, ∀ y : Q,
        (((σQ ^ j) y : Q) : K) = (σ ^ j) (y : K) := by
      intro j
      induction j with
      | zero => intro y; simp
      | succ j ih =>
        intro y
        rw [pow_succ]
        change (((σQ ^ j) (σQ y) : Q) : K) = (σ ^ j * σ) (y : K)
        rw [ih, hσQapply]
        rfl
    rw [hiter]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    rw [hσQpow_apply, hm]
    rfl
  refine ⟨σbar, ?_, hσbar_pow⟩
  intro x
  rw [hσbar_mk]
  apply congrArg QuotientGroup.mk
  apply Subtype.ext
  exact hσQapply x

private theorem unitary_exists_fixed_coset
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hZfix : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z) :
    ∃ x : (Q : Subgroup K), (x : K) ∉ rootCenter (Q : Subgroup K) ∧
      (x : K)⁻¹ * σ (x : K) ∈ rootCenter (Q : Subgroup K) := by
  classical
  let Zsub : Subgroup (Q : Subgroup K) :=
    (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K)
  obtain ⟨σbar, hσbar_mk, hσbar_pow⟩ :=
    unitary_sylow_quotient_aut (Q : Subgroup K) hσ hσQ hZfix
  have hbaract : IsPGroup 2 (Subgroup.zpowers σbar) := by
    obtain ⟨m, hm⟩ := hσbar_pow
    have hdvd : orderOf σbar ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hquotcard : Nat.card ((Q : Subgroup K) ⧸ Zsub) = (2 ^ n) ^ 2 :=
    (h.lemma_3_5_a_unitary Q).2.2.2.2
  have hnpos : 0 < n := by have := h.two_le.2; omega
  have hquoten : 2 ∣ Nat.card ((Q : Subgroup K) ⧸ Zsub) := by
    rw [hquotcard]
    exact dvd_trans (dvd_pow_self 2 (Nat.ne_of_gt hnpos))
      (dvd_pow_self (2 ^ n) (by norm_num : 2 ≠ 0))
  obtain ⟨b, hbfix, hbne⟩ :=
    hbaract.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := (Q : Subgroup K) ⧸ Zsub) hquoten (a := 1)
      (by rw [MulAction.mem_fixedPoints]; intro g; simp)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
  have hσbar_fix : σbar (QuotientGroup.mk x) = QuotientGroup.mk x := by
    have := hbfix ⟨σbar, Subgroup.mem_zpowers σbar⟩
    simpa using this
  have hxWZ : (x : K)⁻¹ * σ (x : K) ∈ rootCenter (Q : Subgroup K) := by
    have heq : (QuotientGroup.mk (⟨σ (x : K), hσQ x x.2⟩ : (Q : Subgroup K)) :
        (Q : Subgroup K) ⧸ Zsub) = QuotientGroup.mk x := by
      rw [← hσbar_mk]
      exact hσbar_fix
    have hmem : (⟨σ (x : K), hσQ x x.2⟩ : (Q : Subgroup K))⁻¹ * x ∈ Zsub :=
      QuotientGroup.eq.mp heq
    have hmemK : (σ (x : K))⁻¹ * (x : K) ∈ rootCenter (Q : Subgroup K) := by
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    have hmem' := (rootCenter (Q : Subgroup K)).inv_mem hmemK
    simpa [mul_inv_rev] using hmem'
  have hxnotZ : (x : K) ∉ rootCenter (Q : Subgroup K) := by
    intro hxZ
    apply hbne
    exact ((QuotientGroup.eq_one_iff x).2 hxZ).symm
  exact ⟨x, hxnotZ, hxWZ⟩

private theorem unitary_fixed_cosets_ne_rootCenter
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hZfix : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z)
    {W : Subgroup K} (hWdef : ∀ x : K, x ∈ W ↔
      x ∈ (Q : Subgroup K) ∧ x⁻¹ * σ x ∈ rootCenter (Q : Subgroup K)) :
    W ≠ rootCenter (Q : Subgroup K) := by
  obtain ⟨x, hxnotZ, hxWZ⟩ := unitary_exists_fixed_coset h Q ht htQ σ hσ hσQ hZfix
  intro hWZ
  have hxW : (x : K) ∈ W := (hWdef (x : K)).mpr ⟨x.2, hxWZ⟩
  exact hxnotZ (hWZ ▸ hxW)

private theorem unitary_fixed_cosets_eq_top
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) {W : Subgroup K}
    (hZW : rootCenter (Q : Subgroup K) ≤ W) (hWQ : W ≤ (Q : Subgroup K))
    (hWinvar : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ W, d * w * d⁻¹ ∈ W)
    (hWne : W ≠ rootCenter (Q : Subgroup K)) : W = (Q : Subgroup K) := by
  rcases h.irreducible_unitary (Q := Q) (t := t) (ht := ht) (htQ := htQ) W
      hZW hWQ hWinvar with h1 | h1
  · exact absurd h1 hWne
  · exact h1

private theorem unitary_cocycle_hom_data
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d)
    (hZfix : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z)
    {W : Subgroup K} (hWdef : ∀ x : K, x ∈ W ↔
      x ∈ (Q : Subgroup K) ∧ x⁻¹ * σ x ∈ rootCenter (Q : Subgroup K))
    (hWQeq : W = (Q : Subgroup K)) :
    ∃ f : (Q : Subgroup K) →* rootCenter (Q : Subgroup K),
      (∀ x : (Q : Subgroup K),
        (((f x : rootCenter (Q : Subgroup K)) : K) = (x : K)⁻¹ * σ (x : K))) ∧
      ∃ Kfix : Subgroup K,
        Kfix = (f.ker).map (Q : Subgroup K).subtype ∧
          rootCenter (Q : Subgroup K) ≤ Kfix ∧
          Kfix ≤ (Q : Subgroup K) ∧
          (∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ Kfix, d * w * d⁻¹ ∈ Kfix) := by
  classical
  set Z : Subgroup K := rootCenter (Q : Subgroup K) with hZdef
  set D : Subgroup K := cartan (Q : Subgroup K) t with hDdef
  have hfixW : ∀ x : (Q : Subgroup K), (x : K)⁻¹ * σ (x : K) ∈ Z := by
    intro x
    have hx : (x : K) ∈ W := by rw [hWQeq]; exact x.2
    exact ((hWdef (x : K)).mp hx).2
  have hcentral : ∀ {z : K}, z ∈ Z → ∀ q ∈ (Q : Subgroup K), q * z = z * q :=
    fun hz q hq => (mem_rootCenter_iff.mp (hZdef ▸ hz)).2 q hq
  have hZQ : Z ≤ (Q : Subgroup K) := rootCenter_le _
  let f : (Q : Subgroup K) →* Z :=
    { toFun := fun x => ⟨(x : K)⁻¹ * σ (x : K), hfixW x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact unitary_cocycle_mul hσQ hZQ hcentral x.2 y.2 (hfixW x) (hfixW y) }
  have hkerZ : Z.subgroupOf (Q : Subgroup K) ≤ f.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change (z : K)⁻¹ * σ (z : K) = 1
    rw [hZfix (z : K) hz]
    group
  let Kfix : Subgroup K := (f.ker).map (Q : Subgroup K).subtype
  have hZKfix : Z ≤ Kfix := by
    intro z hz
    exact Subgroup.mem_map.mpr ⟨⟨z, rootCenter_le _ hz⟩, hkerZ hz, rfl⟩
  have hKfixQ : Kfix ≤ (Q : Subgroup K) := Subgroup.map_subtype_le _
  have hKfixInv : ∀ d ∈ D, ∀ w ∈ Kfix, d * w * d⁻¹ ∈ Kfix := by
    intro d hd w hw
    obtain ⟨q, hqker, rfl⟩ := Subgroup.mem_map.mp hw
    have hdN : d ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
      cartan_le_borel (Q : Subgroup K) t hd
    have hdqQ : d * (q : K) * d⁻¹ ∈ (Q : Subgroup K) :=
      (Subgroup.mem_normalizer_iff.mp hdN q).mp q.2
    refine Subgroup.mem_map.mpr ⟨⟨d * (q : K) * d⁻¹, hdqQ⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ((d * (q : K) * d⁻¹)⁻¹ * σ (d * (q : K) * d⁻¹) : K) = 1
    have hqeq : (q : K)⁻¹ * σ (q : K) = 1 := congrArg Subtype.val hqker
    have hqfix : σ (q : K) = q := by
      calc σ (q : K) = (q : K) * ((q : K)⁻¹ * σ (q : K)) := by group
        _ = (q : K) * 1 := by rw [hqeq]
        _ = q := by simp
    have hσd : σ d = d := hσD d hd
    have hσdinv : σ d⁻¹ = d⁻¹ := by rw [map_inv, hσd]
    rw [map_mul, map_mul, hσd, hσdinv, hqfix]
    group
  refine ⟨f, fun x => rfl, Kfix, rfl, hZKfix, hKfixQ, fun d hd => hKfixInv d hd⟩

private theorem unitary_fixes_sylow
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (φ : (Q : Subgroup K) →* rootCenter (Q : Subgroup K))
    (hφ_apply : ∀ x : (Q : Subgroup K),
      (((φ x : rootCenter (Q : Subgroup K)) : K) = (x : K)⁻¹ * σ (x : K)))
    (Kfix : Subgroup K)
    (hKfix_eq : Kfix = (φ.ker).map (Q : Subgroup K).subtype)
    (hZKfix : rootCenter (Q : Subgroup K) ≤ Kfix)
    (hKfixQ : Kfix ≤ (Q : Subgroup K))
    (hKfixInv : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ Kfix, d * w * d⁻¹ ∈ Kfix) :
    ∀ x ∈ (Q : Subgroup K), σ x = x := by
  classical
  have hc := h.benderCore Q ht htQ
  let Zsub : Subgroup (Q : Subgroup K) := (rootCenter (Q : Subgroup K)).subgroupOf (Q : Subgroup K)
  have hKfixCase : Kfix = rootCenter (Q : Subgroup K) ∨ Kfix = (Q : Subgroup K) := by
    rcases h.irreducible_unitary (Q := Q) (t := t) (ht := ht) (htQ := htQ) Kfix
        hZKfix hKfixQ hKfixInv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  rcases hKfixCase with hZ | hQ
  · have hker_eq : φ.ker = Zsub := by
      apply Subgroup.map_injective (Q : Subgroup K).subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (rootCenter_le (Q : Subgroup K))]
      exact hKfix_eq.symm.trans hZ
    have hquotcard : Nat.card ((Q : Subgroup K) ⧸ Zsub) = (2 ^ n) ^ 2 :=
      (h.lemma_3_5_a_unitary Q).2.2.2.2
    have hquotQ : Nat.card ((Q : Subgroup K) ⧸ φ.ker) = (2 ^ n) ^ 2 := by
      rw [hker_eq]
      exact hquotcard
    have hle : Nat.card ((Q : Subgroup K) ⧸ φ.ker) ≤ Nat.card (rootCenter (Q : Subgroup K)) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card φ.range)
    have hlt : Nat.card (rootCenter (Q : Subgroup K)) < Nat.card ((Q : Subgroup K) ⧸ φ.ker) := by
      rw [hquotQ, hc.card_center]
      have hnpos : 0 < n := by have := h.two_le.2; omega
      have h2n : 1 < 2 ^ n := by
        calc 1 = 2 ^ 0 := by simp
          _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hnpos
      calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
        _ < (2 ^ n) ^ 2 := Nat.pow_lt_pow_right h2n (by norm_num)
    exact absurd hle (not_le.mpr hlt)
  · intro x hx
    have hxK : (x : K) ∈ Kfix := hQ ▸ hx
    obtain ⟨q, hqker, hqx⟩ := Subgroup.mem_map.mp (hKfix_eq ▸ hxK)
    have hqx' : q = (⟨x, hx⟩ : (Q : Subgroup K)) := Subtype.ext hqx
    rw [MonoidHom.mem_ker] at hqker
    have h1 : φ ⟨x, hx⟩ = 1 := by
      rw [← hqx']
      exact hqker
    have h2 : (x : K)⁻¹ * σ (x : K) = 1 := by
      rw [← hφ_apply ⟨x, hx⟩]
      simpa using congrArg Subtype.val h1
    calc σ x = x * ((x : K)⁻¹ * σ (x : K)) := by group
      _ = x * 1 := by rw [h2]
      _ = x := by simp

private theorem unitary_eq_one
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d)
    (hσQpoint : ∀ x ∈ (Q : Subgroup K), σ x = x) : σ = 1 := by
  classical
  have hc := h.benderCore Q ht htQ
  set Z : Subgroup K := rootCenter (Q : Subgroup K) with hZdef
  set D : Subgroup K := cartan (Q : Subgroup K) t with hDdef
  obtain ⟨r, hrZ, hσr⟩ :=
    h.lemma_3_6_a (Q := Q) σ (fun x hx => hσQpoint x hx)
  have hr1 : r = 1 := by
    by_contra hrne
    have hcommD : ∀ d ∈ D, r * d = d * r := by
      intro d hd
      have h1 := hσD d hd
      rw [hσr d] at h1
      calc r * d = (r * d * r⁻¹) * r := by group
        _ = d * r := by rw [h1]
    have hsub : {z : K | z ∈ Z ∧ z ≠ 1} ⊆ {r} := by
      intro z hz
      obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hrZ hrne hz.1 hz.2
      have hrd : r * d = d * r := hcommD d hd
      rw [Set.mem_singleton_iff]
      calc z = d⁻¹ * r * d := hdz
        _ = d⁻¹ * (r * d) := by group
        _ = d⁻¹ * (d * r) := by rw [hrd]
        _ = r := by group
    have hle : {z : K | z ∈ Z ∧ z ≠ 1}.ncard ≤ 1 := by
      calc {z : K | z ∈ Z ∧ z ≠ 1}.ncard ≤ ({r} : Set K).ncard :=
            Set.ncard_le_ncard hsub
        _ = 1 := by simp
    have hge : 3 ≤ {z : K | z ∈ Z ∧ z ≠ 1}.ncard := by
      rw [hZdef, hc.ncard_rootCenter_ne_one]
      have h2n : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (h.two_le.2)
      omega
    omega
  ext k
  rw [hσr k, hr1]
  simp

private theorem aut_eq_one_of_benderType_unitary
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) : σ = 1 := by
  have hZfix := unitary_fixes_rootCenter h Q ht htQ σ hσ hσQ hσD
  obtain ⟨W, hWdef, hZW, hWQ, hWinvar⟩ :=
    unitary_fixed_cosets h Q ht htQ σ hσQ hσD hZfix
  have hWne := unitary_fixed_cosets_ne_rootCenter h Q ht htQ σ hσ hσQ hZfix hWdef
  have hWQeq := unitary_fixed_cosets_eq_top h Q ht htQ hZW hWQ hWinvar hWne
  obtain ⟨f, hf_apply, Kfix, hKfix_eq, hZKfix, hKfixQ, hKfixInv⟩ :=
    unitary_cocycle_hom_data h Q ht htQ σ hσQ hσD hZfix hWdef hWQeq
  exact unitary_eq_one h Q ht htQ σ hσD
    (unitary_fixes_sylow h Q ht htQ σ f hf_apply Kfix hKfix_eq hZKfix hKfixQ hKfixInv)

private theorem aut_eq_one_of_benderType
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (T : Sylow 2 K) {H : Subgroup K}
    (hH : H ≤ Subgroup.normalizer ((T : Subgroup K) : Set K))
    (hHodd : Odd (Nat.card H))
    (hTH : (T : Subgroup K) ⊔ H = Subgroup.normalizer ((T : Subgroup K) : Set K))
    (σ : MulAut K) (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσT : ∀ x ∈ (T : Subgroup K), σ x ∈ (T : Subgroup K))
    (hσH : ∀ x ∈ H, σ x = x) : σ = 1 := by
  classical
  obtain ⟨t, hc⟩ := h.exists_benderCore T
  obtain ⟨g, hgT, hHconj⟩ :=
    exists_conj_cartan_of_complement hc T.isPGroup' hH hHodd hTH
  let c : MulAut K := MulAut.conj g
  let σ' : MulAut K := c⁻¹ * σ * c
  have hσ'app : ∀ x : K, σ' x = g⁻¹ * σ (g * x * g⁻¹) * g := by
    intro x
    simp [σ', c, MulAut.conj_apply, mul_assoc]
  have hgN : g ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) :=
    Subgroup.le_normalizer hgT
  have hσ'T : ∀ x ∈ (T : Subgroup K), σ' x ∈ (T : Subgroup K) := by
    intro x hx
    rw [hσ'app]
    have hgx : g * x * g⁻¹ ∈ (T : Subgroup K) :=
      (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    have hσgx : σ (g * x * g⁻¹) ∈ (T : Subgroup K) := hσT _ hgx
    simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgN)
      (σ (g * x * g⁻¹))).mp hσgx
  have hσ'D : ∀ d ∈ cartan (T : Subgroup K) t, σ' d = d := by
    intro d hd
    rw [hσ'app]
    have hgdH : g * d * g⁻¹ ∈ H := by
      rw [hHconj]
      exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
    rw [hσH _ hgdH]
    group
  have hσ'pow : ∃ k : ℕ, σ' ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hσ
    refine ⟨k, ?_⟩
    have h1 : σ' ^ (2 ^ k) = c⁻¹ * σ ^ (2 ^ k) * c := by
      simpa [σ'] using (_root_.conj_pow (a := c⁻¹) (b := σ) (i := 2 ^ k))
    rw [h1, hk]
    simp
  have hσ'1 : σ' = 1 := by
    cases h with
    | linear n hn e =>
      exact aut_eq_one_of_benderType_linear (.linear n hn e) T hc.sq_eq_one hc.not_mem σ'
        hσ'pow hσ'T hσ'D
    | suzuki a ha e =>
      exact aut_eq_one_of_benderType_suzuki (.suzuki a ha e) T hc.sq_eq_one hc.not_mem σ'
        hσ'pow hσ'T hσ'D
    | unitary n hn e =>
      exact aut_eq_one_of_benderType_unitary (.unitary n hn e) T hc.sq_eq_one hc.not_mem σ'
        hσ'pow hσ'T hσ'D
  calc σ = c * σ' * c⁻¹ := by
        show σ = c * (c⁻¹ * σ * c) * c⁻¹
        group
    _ = 1 := by rw [hσ'1]; simp


private theorem statedSU_center_odd
    {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : X ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) :
    Odd (Nat.card (Subgroup.center X)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  let Y : Subgroup (GL (Fin 3) F) := CFSG.Open.StatedSU 3 (2 ^ n) F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * n) (by
      rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  have hYdata :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := n)
      hF (by norm_num) hnq
  have hYcenter : Subgroup.center ↥Y =
      (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf Y := hYdata.2
  have hYodd : Odd (Nat.card (Subgroup.center ↥Y)) := by
    by_contra hodd
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hodd
    have hzscalar : (z : ↥Y) ∈ (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf Y := by
      rw [← hYcenter]
      exact z.2
    have hz3 : (z : ↥Y) ^ 3 = 1 := statedSU_three_kernel (z : ↥Y) hzscalar
    have hdvd3 : orderOf (z : ↥Y) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hz0 : orderOf (z : ↥Y) = 2 := (Subgroup.orderOf_coe z).trans hz
    rw [hz0] at hdvd3
    norm_num at hdvd3
  have hcenter : Nat.card (Subgroup.center X) = Nat.card (Subgroup.center ↥Y) := by
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  rw [hcenter]
  exact hYodd

private theorem statedSU_quotient_bender
    {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : X ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) :
    ∃ e' : ℕ, BenderType (X ⧸ Subgroup.center X) n 3 e' := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  let Y : Subgroup (GL (Fin 3) F) := CFSG.Open.StatedSU 3 (2 ^ n) F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * n) (by
      rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  have hYdata :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := n)
      hF (by norm_num) hnq
  have hYcenter : Subgroup.center ↥Y =
      (CFSG.Open.StatedScalars (Fin 3) F).subgroupOf Y := hYdata.2
  let ZX : Subgroup X := Subgroup.center X
  let ZY : Subgroup ↥Y := Subgroup.center ↥Y
  let eZ : X ⧸ ZX ≃* (↥Y) ⧸ ZY :=
    QuotientGroup.congr ZX ZY e (Subgroup.map_center_eq e)
  let eP : X ⧸ ZX ≃* CFSG.Open.StatedProj Y :=
    eZ.trans (QuotientGroup.quotientMulEquivOfEq hYcenter)
  let b := CFSG.Quasithin.benderType_statedProj hn hF
  let e' := Classical.choose b
  have hBProj : BenderType (CFSG.Open.StatedProj Y) n 3 e' := Classical.choose_spec b
  exact ⟨e', hBProj.of_mulEquiv eP.symm⟩

private noncomputable def statedSU_quotient_action
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hZodd : Odd (Nat.card (Subgroup.center X))) (e' : ℕ)
    (hBquot : BenderType (X ⧸ Subgroup.center X) n 3 e')
    (T : Sylow 2 X) {H : Subgroup X}
    (hH : H ≤ Subgroup.normalizer ((T : Subgroup X) : Set X))
    (hHodd : Odd (Nat.card H))
    (hTH : (T : Subgroup X) ⊔ H = Subgroup.normalizer ((T : Subgroup X) : Set X))
    (σ : MulAut X) (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσT : ∀ x ∈ (T : Subgroup X), σ x ∈ (T : Subgroup X))
    (hσH : ∀ x ∈ H, σ x = x) :
    StatedSUActionData X n σ := by
  classical
  let ZX : Subgroup X := Subgroup.center X
  let π : X →* X ⧸ ZX := QuotientGroup.mk' ZX
  let Tbar : Sylow 2 (X ⧸ ZX) :=
    T.mapSurjective (f := π) (QuotientGroup.mk'_surjective ZX)
  let Hbar : Subgroup (X ⧸ ZX) := H.map π
  have hTbar : (Tbar : Subgroup (X ⧸ ZX)) = (T : Subgroup X).map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective ZX) T
  have hHbar_le : Hbar ≤ Subgroup.normalizer ((Tbar : Subgroup (X ⧸ ZX)) : Set (X ⧸ ZX)) := by
    calc Hbar ≤ (Subgroup.normalizer ((T : Subgroup X) : Set X)).map π :=
          Subgroup.map_mono hH
      _ ≤ Subgroup.normalizer (((T : Subgroup X).map π : Subgroup (X ⧸ ZX)) :
            Set (X ⧸ ZX)) := Subgroup.le_normalizer_map π
      _ = Subgroup.normalizer ((Tbar : Subgroup (X ⧸ ZX)) : Set (X ⧸ ZX)) := by rw [hTbar]
  have hHbarodd : Odd (Nat.card Hbar) :=
    Odd.of_dvd_nat hHodd (Subgroup.card_map_dvd (H := H) π)
  have hTHbar : (Tbar : Subgroup (X ⧸ ZX)) ⊔ Hbar =
      Subgroup.normalizer ((Tbar : Subgroup (X ⧸ ZX)) : Set (X ⧸ ZX)) := by
    have hsup : (Tbar : Subgroup (X ⧸ ZX)) ⊔ Hbar = ((T : Subgroup X) ⊔ H).map π := by
      rw [hTbar, ← Subgroup.map_sup]
    rw [hsup, hTH]
    exact CFSG.GroupTheory.normal_coprime_quotient_normalizer 2 ZX
      hZodd.not_two_dvd_nat (T : Subgroup X) T.isPGroup'
  let σbar : MulAut (X ⧸ ZX) :=
    QuotientGroup.congr ZX ZX σ (Subgroup.map_center_eq σ)
  have hσbar_mk : ∀ x : X, σbar (QuotientGroup.mk x) = QuotientGroup.mk (σ x) :=
    fun x => QuotientGroup.congr_mk ZX ZX σ (Subgroup.map_center_eq σ) x
  have hσbar_pow : ∃ k : ℕ, σbar ^ (2 ^ k) = 1 :=
    quotient_congr_pow_eq_one ZX σ (Subgroup.map_center_eq σ) hσ
  have hσbarT : ∀ x ∈ (Tbar : Subgroup (X ⧸ ZX)), σbar x ∈ (Tbar : Subgroup (X ⧸ ZX)) := by
    intro x hx
    rw [hTbar] at hx ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨σ t, hσT t ht, by
      change QuotientGroup.mk (σ t) = σbar (QuotientGroup.mk t)
      exact (hσbar_mk t).symm⟩
  have hσbarH : ∀ x ∈ Hbar, σbar x = x := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    change σbar (QuotientGroup.mk h) = QuotientGroup.mk h
    rw [hσbar_mk, hσH h hh]
  exact
    { hZodd := hZodd
      e' := e'
      hBquot := hBquot
      Tbar := Tbar
      Hbar := Hbar
      hHbar_le := hHbar_le
      hHbarodd := hHbarodd
      hTHbar := hTHbar
      σbar := σbar
      hσbar_mk := hσbar_mk
      hσbar_pow := hσbar_pow
      hσbarT := hσbarT
      hσbarH := hσbarH }

private theorem aut_eq_one_of_statedSU
    {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (e : X ≃* CFSG.Open.StatedSU 3 (2 ^ n) F)
    (T : Sylow 2 X) {H : Subgroup X}
    (hH : H ≤ Subgroup.normalizer ((T : Subgroup X) : Set X))
    (hHodd : Odd (Nat.card H))
    (hTH : (T : Subgroup X) ⊔ H = Subgroup.normalizer ((T : Subgroup X) : Set X))
    (σ : MulAut X) (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσT : ∀ x ∈ (T : Subgroup X), σ x ∈ (T : Subgroup X))
    (hσH : ∀ x ∈ H, σ x = x) : σ = 1 := by
  classical
  have hZodd := statedSU_center_odd hn hF e
  obtain ⟨e', hBquot⟩ := statedSU_quotient_bender hn hF e
  obtain ⟨-, -, -, Tbar, Hbar, hHbar_le, hHbarodd, hTHbar, σbar, hσbar_mk,
    hσbar_pow, hσbarT, hσbarH⟩ :=
    statedSU_quotient_action hZodd e' hBquot T hH hHodd hTH σ hσ hσT hσH
  have hσbar1 : σbar = 1 :=
    aut_eq_one_of_benderType hBquot Tbar hHbar_le hHbarodd hTHbar σbar hσbar_pow hσbarT hσbarH
  have hcentral : ∀ x : X, x⁻¹ * σ x ∈ Subgroup.center X := by
    intro x
    have heq : (QuotientGroup.mk (σ x) : X ⧸ Subgroup.center X) = QuotientGroup.mk x := by
      rw [← hσbar_mk]
      have := congrArg (fun f : MulAut (X ⧸ Subgroup.center X) =>
        f (QuotientGroup.mk x)) hσbar1
      simpa using this
    have hmem : (σ x)⁻¹ * x ∈ Subgroup.center X := QuotientGroup.eq.mp heq
    have hmem' := (Subgroup.center X).inv_mem hmem
    simpa [mul_inv_rev] using hmem'
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * n) (by
      rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have hnq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  have hYdata :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := 2) (f := n)
      hF (by norm_num) hnq
  have hperfX : Group.IsPerfect X := by
    haveI : Group.IsPerfect (CFSG.Open.StatedSU 3 (2 ^ n) F) := hYdata.1.1
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Group.IsPerfect X := hperfX
  have hσid : σ.toMonoidHom = MonoidHom.id X :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      σ.toMonoidHom hcentral
  ext x
  have := congrArg (fun f : X →* X => f x) hσid
  simpa using this

theorem mulAut_eq_one_of_fixes_borel_complement
    {X : Type} [Group X] [Finite X]
    (hX : (∃ a : ℕ, 1 ≤ a ∧ Nonempty (X ≃* CFSG.Open.Sz a)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
        (Nonempty (X ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
          Nonempty (X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)))) ∨
      (∃ n : ℕ, 2 ≤ n ∧ CFSG.Quasithin.IsL2Quot n X))
    (T : Sylow 2 X) {H : Subgroup X} (hH : H ≤ Subgroup.normalizer ((T : Subgroup X) : Set X))
    (hHodd : Odd (Nat.card H))
    (hTH : (T : Subgroup X) ⊔ H = Subgroup.normalizer ((T : Subgroup X) : Set X))
    (σ : MulAut X) (hσ : ∃ k : ℕ, σ ^ (2 ^ k) = 1)
    (hσT : ∀ x ∈ (T : Subgroup X), σ x ∈ (T : Subgroup X)) (hσH : ∀ h ∈ H, σ h = h) :
    σ = 1 := by
  rcases hX with hSz | hU | hL2
  · obtain ⟨a, ha, ⟨e⟩⟩ := hSz
    exact aut_eq_one_of_benderType
      (.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
      T hH hHodd hTH σ hσ hσT hσH
  · obtain ⟨n, hn, F, hField, hFinite, hF, hSU | hPSU⟩ := hU
    · letI : Field F := hField
      letI : Finite F := hFinite
      obtain ⟨e⟩ := hSU
      exact aut_eq_one_of_statedSU hn hF e T hH hHodd hTH σ hσ hσT hσH
    · letI : Field F := hField
      letI : Finite F := hFinite
      obtain ⟨e⟩ := hPSU
      obtain ⟨e', hB⟩ := CFSG.Quasithin.benderType_statedProj hn hF
      exact aut_eq_one_of_benderType (hB.of_mulEquiv e.symm) T hH hHodd hTH σ hσ hσT hσH
  · obtain ⟨n, hn, ⟨e⟩⟩ := hL2
    exact aut_eq_one_of_benderType (.linear n hn e) T hH hHodd hTH σ hσ hσT hσH
