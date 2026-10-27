module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofA6Fin
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

private theorem sba6s_check_comm : Core.pslLit.all (fun r =>
    Core.cmul r r != Core.cid || r == Core.cid || Core.pslLit.all (fun x =>
      Core.cmul (Core.cmul x x) x != Core.cid || x == Core.cid ||
        Core.cmul r x != Core.cmul x r)) = true := by
  decide +kernel

private theorem sba6s_check_exp9 : Core.pslLit.all (fun x =>
    Core.cpow x 9 != Core.cid || Core.cpow x 3 == Core.cid) = true := by
  decide +kernel

private theorem sba6s_check_cent : Core.p0Lit.all (fun b =>
    b == Core.cid || (Core.cpslList b).length % 9 != 0) = true := by
  decide +kernel

private theorem sba6s_noncomm {r x : P10} (hr : r ∈ A6Models.psl29) (hx : x ∈ A6Models.psl29)
    (hr2 : r * r = 1) (hr1 : r ≠ 1) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : r * x ≠ x * r := by
  intro hc
  have h := List.all_eq_true.mp sba6s_check_comm (code r) ((mem_psl29_iff r).mp hr)
  have e1 : (Core.cmul (code r) (code r) != Core.cid) = false := by
    rw [← code_mul, hr2, code_one]; simp
  have e2 : (code r == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, ← code_one]
    exact fun h' => hr1 (code_injective h')
  simp only [e1, e2, Bool.false_or] at h
  have h' := List.all_eq_true.mp h (code x) ((mem_psl29_iff x).mp hx)
  have e3 : (Core.cmul (Core.cmul (code x) (code x)) (code x) != Core.cid) = false := by
    rw [← code_mul, ← code_mul, show x * x * x = x ^ 3 by rw [pow_three, ← mul_assoc], hx3,
      code_one]
    simp
  have e4 : (code x == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, ← code_one]
    exact fun h'' => hx1 (code_injective h'')
  simp only [e3, e4, Bool.false_or] at h'
  rw [← code_mul, ← code_mul, hc] at h'
  simp at h'

private theorem sba6s_exp9 {x : P10} (hx : x ∈ A6Models.psl29) (h9 : x ^ 9 = 1) : x ^ 3 = 1 := by
  have h := List.all_eq_true.mp sba6s_check_exp9 (code x) ((mem_psl29_iff x).mp hx)
  have e1 : (Core.cpow (code x) 9 != Core.cid) = false := by
    rw [← code_pow, h9, code_one]; simp
  simp only [e1, Bool.false_or, beq_iff_eq] at h
  apply code_injective
  rw [code_pow, code_one]
  exact h

private theorem sba6s_exp3 {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 6)) {x : K}
    (h9 : x ^ 9 = 1) : x ^ 3 = 1 := by
  obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
  let φ : K ≃* A6Models.psl29 := e.trans ψ.symm
  have h := sba6s_exp9 (φ x).2 (by
    rw [← Subgroup.coe_pow, ← map_pow, h9, map_one]; rfl)
  apply φ.injective
  apply Subtype.ext
  rw [map_pow, Subgroup.coe_pow, h, map_one]
  rfl

private theorem sba6s_not_dvd {b : P10} (hb : b ∈ P0) (hb1 : b ≠ 1) :
    ¬ 9 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({b} : Set P10)) := by
  intro hd
  rw [card_psl29_centralizer] at hd
  have h := List.all_eq_true.mp sba6s_check_cent (code b) ((mem_P0_iff b).mp hb)
  have e1 : (code b == Core.cid) = false := by
    rw [beq_eq_false_iff_ne, ← code_one]
    exact fun h' => hb1 (code_injective h')
  have e2 : ((Core.cpslList (code b)).length % 9 != 0) = false := by
    simp [Nat.mod_eq_zero_of_dvd hd]
  simp [e1, e2] at h

private theorem sba6s_two_group_trivial {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 6)) {P R : Subgroup K} (hP9 : Nat.card P = 9)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hR : IsPGroup 2 R)
    (hPR : ∀ x ∈ P, ∀ r ∈ R, x * r * x⁻¹ ∈ R) : R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
  let φ : K ≃* A6Models.psl29 := e.trans ψ.symm
  by_contra hR1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hR
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hR1 ((Subgroup.card_eq_one).mp (by simpa using hn))
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hr'R : (r : K) ∈ R := r.2
  have hr2 : (r : K) * (r : K) = 1 := by
    have h2 : r ^ 2 = 1 := by rw [← hr]; exact pow_orderOf_eq_one r
    have := congrArg (fun y : R => (y : K)) h2
    simpa [pow_two] using this
  have hr1 : (r : K) ≠ 1 := by
    intro h1
    have : r = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hr
    omega
  let f : P → R := fun x => ⟨(x : K) * (r : K) * (x : K)⁻¹, hPR _ x.2 _ hr'R⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (x : K) * (r : K) * (x : K)⁻¹ = (y : K) * (r : K) * (y : K)⁻¹ :=
      congrArg Subtype.val hxy
    have hz : ((y : K)⁻¹ * (x : K)) * (r : K) = (r : K) * ((y : K)⁻¹ * (x : K)) := by
      calc ((y : K)⁻¹ * (x : K)) * (r : K)
          = (y : K)⁻¹ * ((x : K) * (r : K) * (x : K)⁻¹) * (x : K) := by group
        _ = (y : K)⁻¹ * ((y : K) * (r : K) * (y : K)⁻¹) * (x : K) := by rw [h1]
        _ = (r : K) * ((y : K)⁻¹ * (x : K)) := by group
    by_contra hne
    have hzP : (y : K)⁻¹ * (x : K) ∈ P := P.mul_mem (P.inv_mem y.2) x.2
    have hz1 : (y : K)⁻¹ * (x : K) ≠ 1 := by
      intro h1'
      apply hne
      apply Subtype.ext
      calc (x : K) = (y : K) * ((y : K)⁻¹ * (x : K)) := by group
        _ = y := by rw [h1', mul_one]
    have hz3 := hP3 _ hzP
    have hmul : ∀ a b : K, ((φ a : A6Models.psl29) : P10) * ((φ b : A6Models.psl29) : P10) =
        ((φ (a * b) : A6Models.psl29) : P10) := fun a b => by rw [map_mul]; rfl
    have hne1 : ∀ a : K, a ≠ 1 → ((φ a : A6Models.psl29) : P10) ≠ 1 := fun a ha h =>
      ha (φ.injective (Subtype.ext (by rw [h, map_one]; rfl)))
    refine sba6s_noncomm (φ (r : K)).2 (φ ((y : K)⁻¹ * (x : K))).2 ?_ (hne1 _ hr1) ?_
      (hne1 _ hz1) ?_
    · rw [hmul, hr2, map_one]; rfl
    · rw [← Subgroup.coe_pow, ← map_pow, hz3, map_one]; rfl
    · rw [hmul, hmul, hz]
  have hcardle : Nat.card P ≤ Nat.card R := Nat.card_le_card_of_injective f hf
  have hRdvd : Nat.card R ∣ 360 := by
    have h := Subgroup.card_subgroup_dvd_card R
    rwa [Nat.card_congr e.toEquiv, DoubleA3.card_alt6'] at h
  rw [hP9, hn] at hcardle
  rw [hn] at hRdvd
  have h8 : 2 ^ n ∣ 8 := by
    have hcop : Nat.Coprime (2 ^ n) 45 := Nat.Coprime.pow_left n (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (by simpa using hRdvd)
  have := Nat.le_of_dvd (by norm_num) h8
  omega

private theorem sba6s_aut_one {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 6)) {P : Subgroup K} (hP9 : Nat.card P = 9)
    (γ : MulAut K) (hγ : ∀ x ∈ P, γ x = x) {m : ℕ} (hm : γ ^ 2 ^ m = 1) : γ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
  let φ : K ≃* A6Models.psl29 := e.trans ψ.symm
  obtain ⟨b, hbA, hb⟩ := DoubleA3.exists_aut_model φ γ
  have hpow : ∀ (n : ℕ) (k : K), ((φ ((γ ^ n) k) : A6Models.psl29) : P10) =
      b ^ n * ((φ k : A6Models.psl29) : P10) * (b ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [pow_succ, MulAut.mul_apply, ih, hb, pow_succ]
      group
  have hbpow : b ^ 2 ^ m = 1 := by
    refine centralizer_psl29 (pow_mem hbA _) (fun x hx => ?_)
    obtain ⟨k, hk⟩ := φ.surjective ⟨x, hx⟩
    have h1 := hpow (2 ^ m) k
    rw [hm, MulAut.one_apply, hk] at h1
    simp only at h1
    calc b ^ 2 ^ m * x = (b ^ 2 ^ m * x * (b ^ 2 ^ m)⁻¹) * b ^ 2 ^ m := by group
      _ = x * b ^ 2 ^ m := by rw [← h1]
  by_contra hγ1
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hγ1
    refine MulEquiv.ext fun k => ?_
    apply φ.injective
    apply Subtype.ext
    have := hb k
    simpa using this
  have hQ2 : IsPGroup 2 (Subgroup.zpowers b) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hbpow)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨g, hg, hgQ⟩ := Push153B.A6.exists_conj_le_P0 (Q := Subgroup.zpowers b)
    (Subgroup.zpowers_le.mpr hbA) hQ2
  have hb'P0 : g * b * g⁻¹ ∈ P0 := hgQ ⟨b, Subgroup.mem_zpowers b, rfl⟩
  have hb'1 : g * b * g⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  let Pm : Subgroup P10 := ((P.map φ.toMonoidHom).map A6Models.psl29.subtype).map
    (MulAut.conj g).toMonoidHom
  have hPm9 : Nat.card Pm = 9 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      Subgroup.card_map_of_injective A6Models.psl29.subtype_injective,
      Subgroup.card_map_of_injective φ.injective, hP9]
  have hPmC : Pm ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({g * b * g⁻¹} : Set P10) := by
    rintro _ ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨psl29_normal g hg _ (φ k).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : b * ((φ k : A6Models.psl29) : P10) = ((φ k : A6Models.psl29) : P10) * b := by
      have h1 := hb k
      rw [hγ k hk] at h1
      calc b * ((φ k : A6Models.psl29) : P10)
          = (b * ((φ k : A6Models.psl29) : P10) * b⁻¹) * b := by group
        _ = ((φ k : A6Models.psl29) : P10) * b := by rw [← h1]
    show g * ((φ k : A6Models.psl29) : P10) * g⁻¹ * (g * b * g⁻¹) =
      g * b * g⁻¹ * (g * ((φ k : A6Models.psl29) : P10) * g⁻¹)
    calc g * ((φ k : A6Models.psl29) : P10) * g⁻¹ * (g * b * g⁻¹)
        = g * (((φ k : A6Models.psl29) : P10) * b) * g⁻¹ := by group
      _ = g * (b * ((φ k : A6Models.psl29) : P10)) * g⁻¹ := by rw [hc]
      _ = g * b * g⁻¹ * (g * ((φ k : A6Models.psl29) : P10) * g⁻¹) := by group
  exact sba6s_not_dvd hb'P0 hb'1 (hPm9 ▸ Subgroup.card_dvd_of_le hPmC)

private theorem sba6s_normal_oResidual (Y : Type*) [Group Y] : (oResidual 2 Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oResidual at hn ⊢
  have key : Subgroup.map (MulAut.conj g).toMonoidHom
      (Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2}) ≤
      Subgroup.closure {x : Y | Nat.Coprime (orderOf x) 2} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨x, hx, rfl⟩
    show Nat.Coprime (orderOf (MulAut.conj g x)) 2
    rwa [MulEquiv.orderOf_eq]
  exact key ⟨n, hn, rfl⟩

private theorem sba6s_exists_pow_mem_oResidual {Y : Type*} [Group Y] [Finite Y] (x : Y) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oResidual 2 Y := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, Subgroup.subset_closure ?_⟩
  show Nat.Coprime (orderOf (x ^ 2 ^ k)) 2
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm.coprime_two_right

private theorem sba6s_eq_one_of_pow {Y : Type*} [Group Y] {x : Y} {j c : ℕ}
    (h2 : x ^ 2 ^ j = 1) (hc : x ^ c = 1) (hodd : Odd c) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ j) c := Nat.Coprime.pow_left j hodd.coprime_two_right.symm
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hc)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h
  exact orderOf_eq_one_iff.mp h

private theorem sba6s_hO2 (N : Subgroup (X ⧸ CFSG.pCore 2 X))
    (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 X)).ker := by
    rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hK2 : IsPGroup 2 (N.comap (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
    IsPGroup.comap_of_ker_isPGroup h2 _ hker
  have hKn : (N.comap (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal := hN.comap _
  have hle : N.comap (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ CFSG.pCore 2 X :=
    le_sSup ⟨hKn, hK2⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 X) x
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff y).mpr (hle hx))

private theorem sba6s_two_element_trivial {G : Type} [Group G] [Finite G]
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) {Y : Subgroup G} (hYn : Y.Normal)
    (hY2 : ∀ g : G, ∃ k : ℕ, g ^ 2 ^ k ∈ Y) {t : G} (ht : ∃ k : ℕ, t ^ 2 ^ k = 1)
    (htY : ∀ y ∈ Y, y * t = t * y) : t = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.centralizer (Y : Set G) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_centralizer_iff] at hn ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Y := by simpa using hYn.conj_mem y hy g⁻¹
    have h1 := hn _ hy'
    calc y * (g * n * g⁻¹) = g * ((g⁻¹ * y * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * n * g⁻¹ * y := by group
  have hGY : IsPGroup 2 (G ⧸ Y) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := hY2 g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  haveI : Group.IsNilpotent (G ⧸ Y) := hGY.isNilpotent
  haveI hNnil : Group.IsNilpotent ↥N := by
    refine Subgroup.isNilpotent_of_ker_le_center ((QuotientGroup.mk' Y).comp N.subtype) ?_
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro m
    have hnY : (n : G) ∈ Y := (QuotientGroup.eq_one_iff (n : G)).mp (MonoidHom.mem_ker.mp hn)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp m.2 _ hnY).symm
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥N) := inferInstance
  haveI hPn : (P : Subgroup ↥N).Normal := inferInstance
  haveI := Sylow.unique_of_normal P hPn
  have key : ∀ n : ↥N, (∃ k : ℕ, n ^ 2 ^ k = 1) → n ∈ P := by
    rintro n ⟨k, hk⟩
    have hQ2 : IsPGroup 2 (Subgroup.zpowers n) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨Q, hQ⟩ := hQ2.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    exact hQP ▸ hQ (Subgroup.mem_zpowers n)
  have hH2 : IsPGroup 2 (P.map N.subtype) := P.isPGroup'.map N.subtype
  have htN : t ∈ N := Subgroup.mem_centralizer_iff.mpr htY
  have hWH : Subgroup.normalClosure {t} ≤ P.map N.subtype := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨k, hk⟩ := ht
    have hxN : c * a * c⁻¹ ∈ N := hNn.conj_mem a htN c
    have hx2 : (⟨c * a * c⁻¹, hxN⟩ : ↥N) ∈ P := by
      refine key _ ⟨k, Subtype.ext ?_⟩
      show (c * a * c⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    exact ⟨_, hx2, rfl⟩
  have hW0 : Subgroup.normalClosure {t} = ⊥ :=
    hO2 _ inferInstance (hH2.to_le hWH)
  have htW : t ∈ Subgroup.normalClosure {t} := Subgroup.subset_normalClosure (Set.mem_singleton t)
  rw [hW0] at htW
  exact Subgroup.mem_bot.mp htW

private theorem sba6s_decomp {G : Type} [Group G] [Finite G]
    (hT : Sec4.IsTripleCover ↥(oResidual 2 G) (alternatingGroup (Fin 6)))
    (hnq : ¬ CFSG.IsQuasisimple ↥(oResidual 2 G)) :
    ∃ Zg D : Subgroup G, Zg ≤ oResidual 2 G ∧ D ≤ oResidual 2 G ∧ Zg.Normal ∧ D.Normal ∧
      (∀ z ∈ Zg, ∀ y ∈ oResidual 2 G, z * y = y * z) ∧ Nat.card Zg = 3 ∧ Zg ⊓ D = ⊥ ∧
      oResidual 2 G ≤ Zg ⊔ D ∧ Nonempty (↥D ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hcard, ⟨e⟩⟩ := hT
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYn : (oResidual 2 G).Normal := sba6s_normal_oResidual G
  set Y : Subgroup G := oResidual 2 G with hY
  have hS6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hnc6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hcomm : IsMulCommutative (alternatingGroup (Fin 6)) := ⟨⟨fun a b => hc a b⟩⟩
    have h3 := (alternatingGroup.isMulCommutative_iff_card_le_three).mp hcomm
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    omega
  have hperf6 : commutator (alternatingGroup (Fin 6)) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (commutator (alternatingGroup (Fin 6))) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc6
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact h
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.isPerfect_def.mpr hperf6
  haveI : Group.IsPerfect (↥Y ⧸ Subgroup.center ↥Y) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQperf : commutator (↥Y ⧸ Subgroup.center ↥Y) = ⊤ := Group.isPerfect_def.mp inferInstance
  have hDZ : commutator ↥Y ⊔ Subgroup.center ↥Y = ⊤ := by
    have h1 : (commutator ↥Y).map (QuotientGroup.mk' (Subgroup.center ↥Y)) = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
      exact hQperf
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥Y), ← Subgroup.comap_map_eq, h1,
      Subgroup.comap_top]
  have hDZbot : commutator ↥Y ⊓ Subgroup.center ↥Y = ⊥ := by
    by_contra hne
    haveI : Fact (Nat.card (Subgroup.center ↥Y)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
    have hsub : ((commutator ↥Y ⊓ Subgroup.center ↥Y).subgroupOf (Subgroup.center ↥Y)) = ⊤ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        ((commutator ↥Y ⊓ Subgroup.center ↥Y).subgroupOf (Subgroup.center ↥Y)) with h | h
      · exfalso
        apply hne
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        have hxm : (⟨x, hx.2⟩ : Subgroup.center ↥Y) ∈
            (commutator ↥Y ⊓ Subgroup.center ↥Y).subgroupOf (Subgroup.center ↥Y) :=
          Subgroup.mem_subgroupOf.mpr hx
        rw [h, Subgroup.mem_bot] at hxm
        exact congrArg Subtype.val hxm
      · exact h
    have hZle : Subgroup.center ↥Y ≤ commutator ↥Y := by
      intro z hz
      have hzm : (⟨z, hz⟩ : Subgroup.center ↥Y) ∈
          (commutator ↥Y ⊓ Subgroup.center ↥Y).subgroupOf (Subgroup.center ↥Y) := by
        rw [hsub]; trivial
      exact (Subgroup.mem_subgroupOf.mp hzm).1
    have hDtop : commutator ↥Y = ⊤ := by
      rw [← hDZ]; exact (sup_eq_left.mpr hZle).symm
    refine hnq ⟨Group.isPerfect_def.mpr hDtop, ?_, ?_⟩
    · exact e.isSimpleGroup
    · obtain ⟨a, b, hab⟩ := hnc6
      exact ⟨e.symm a, e.symm b, fun h =>
        hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  let ι : ↥(commutator ↥Y) →* ↥Y ⧸ Subgroup.center ↥Y :=
    (QuotientGroup.mk' (Subgroup.center ↥Y)).comp (commutator ↥Y).subtype
  have hι : Function.Bijective ι := by
    constructor
    · intro a b hab
      have h1 : (a : ↥Y)⁻¹ * (b : ↥Y) ∈ Subgroup.center ↥Y := by
        have hab' : (QuotientGroup.mk (a : ↥Y) : ↥Y ⧸ Subgroup.center ↥Y) =
            QuotientGroup.mk (b : ↥Y) := hab
        exact QuotientGroup.eq.mp hab'
      have h2 : (a : ↥Y)⁻¹ * (b : ↥Y) ∈ commutator ↥Y :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2
      have h3 : (a : ↥Y)⁻¹ * (b : ↥Y) ∈ commutator ↥Y ⊓ Subgroup.center ↥Y := ⟨h2, h1⟩
      rw [hDZbot, Subgroup.mem_bot] at h3
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    · intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        have hy : y ∈ ((Subgroup.center ↥Y ⊔ commutator ↥Y : Subgroup ↥Y) : Set ↥Y) := by
          rw [sup_comm, hDZ]; trivial
        rw [Subgroup.normal_mul] at hy
        obtain ⟨z, hz, d, hd, hzd⟩ := hy
        refine ⟨⟨d, hd⟩, ?_⟩
        show (QuotientGroup.mk d : ↥Y ⧸ Subgroup.center ↥Y) = QuotientGroup.mk y
        rw [← hzd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, one_mul]
  have hinj : Function.Injective (Y.subtype) := Y.subtype_injective
  refine ⟨(Subgroup.center ↥Y).map Y.subtype, (commutator ↥Y).map Y.subtype,
    Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hn
    have hgz : g * (z : G) * g⁻¹ ∈ Y := hYn.conj_mem _ z.2 g
    refine ⟨⟨g * z * g⁻¹, hgz⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    apply Subtype.ext
    have hy' : g⁻¹ * (y : G) * g ∈ Y := by simpa using hYn.conj_mem y y.2 g⁻¹
    have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g⁻¹ * y * g, hy'⟩)
    show (y : G) * (g * (z : G) * g⁻¹) = g * (z : G) * g⁻¹ * (y : G)
    calc (y : G) * (g * (z : G) * g⁻¹) = g * ((g⁻¹ * (y : G) * g) * (z : G)) * g⁻¹ := by group
      _ = g * ((z : G) * (g⁻¹ * (y : G) * g)) * g⁻¹ := by rw [show (g⁻¹ * (y : G) * g) * (z : G) =
            (z : G) * (g⁻¹ * (y : G) * g) from hc]
      _ = g * (z : G) * g⁻¹ * (y : G) := by group
  ·
    have hD : (commutator ↥Y).map Y.subtype = ⁅Y, Y⁆ := Subgroup.map_subtype_commutator Y
    rw [hD]
    haveI := hYn
    infer_instance
  ·
    rintro _ ⟨z, hz, rfl⟩ y hy
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
  · rw [Subgroup.card_map_of_injective hinj]; exact hcard
  · rw [← Subgroup.map_inf _ _ _ hinj, inf_comm, hDZbot, Subgroup.map_bot]
  · have h1 : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine le_of_eq ?_
    calc Y = (⊤ : Subgroup ↥Y).map Y.subtype := h1.symm
      _ = (commutator ↥Y ⊔ Subgroup.center ↥Y).map Y.subtype := by rw [hDZ]
      _ = (commutator ↥Y).map Y.subtype ⊔ (Subgroup.center ↥Y).map Y.subtype :=
        Subgroup.map_sup _ _ _
      _ = (Subgroup.center ↥Y).map Y.subtype ⊔ (commutator ↥Y).map Y.subtype := sup_comm _ _
  · exact ⟨((Subgroup.equivMapOfInjective _ Y.subtype hinj).symm.trans
      (MulEquiv.ofBijective ι hι)).trans e⟩

private theorem sba6s_main {G : Type} [Group G] [Finite G]
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hT : Sec4.IsTripleCover ↥(oResidual 2 G) (alternatingGroup (Fin 6)))
    (hnq : ¬ CFSG.IsQuasisimple ↥(oResidual 2 G))
    {B T : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hBmax : ∀ B' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B' → B ≤ B' → B' = B)
    (hT2 : IsPGroup 2 T) (hTB : B ≤ Subgroup.normalizer (T : Set G)) : T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Zg, D, hZY, hDY, hZn, hDn, hZc, hZ3, hZD, hYZD, ⟨eD⟩⟩ := sba6s_decomp hT hnq
  have hYn : (oResidual 2 G).Normal := sba6s_normal_oResidual G
  haveI := hZn
  haveI := hDn
  set Y : Subgroup G := oResidual 2 G with hY
  have hBY : B ≤ Y := by
    intro b hb
    refine Subgroup.subset_closure ?_
    show Nat.Coprime (orderOf b) 2
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hB.2 b hb))
      (by norm_num : Nat.Coprime 3 2)
  have hZ3' : ∀ z ∈ Zg, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Zg))
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hZe : CFSG.Assembly.IsElemAbelian 3 Zg :=
    ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZY b.2))⟩⟩, hZ3'⟩
  have hZB : Zg ≤ B := by
    have hsup : CFSG.Assembly.IsElemAbelian 3 (Zg ⊔ B) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hZe hB (fun a ha b hb => hZc a ha b (hBY hb))
    exact le_sup_left.trans (hBmax _ hsup le_sup_right).le
  have hD360 : Nat.card D = 360 := by
    rw [Nat.card_congr eD.toEquiv, DoubleA3.card_alt6']
  have hBD9 : Nat.card ↥(B ⊓ D) ∣ 3 ^ 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hB.mono (inf_le_left : B ⊓ D ≤ B)).isPGroup
    have hdvd : Nat.card ↥(B ⊓ D) ∣ 360 := hD360 ▸ Subgroup.card_dvd_of_le inf_le_right
    rw [hn] at hdvd ⊢
    have hcop : Nat.Coprime (3 ^ n) 40 := Nat.Coprime.pow_left n (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
  obtain ⟨K, hK9, hBDK, hKD⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := G)
    Nat.prime_three (H := B ⊓ D) (L := D) hBD9 (by rw [hD360]; norm_num) inf_le_right
  have hK9' : Nat.card K = 9 := by rw [hK9]; norm_num
  have hKel : CFSG.Assembly.IsElemAbelian 3 K := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hK9, fun x hx => ?_⟩
    have hx9 : x ^ 9 = 1 := by
      have h := pow_card_eq_one' (x := (⟨x, hx⟩ : K))
      rw [hK9'] at h
      simpa using congrArg Subtype.val h
    have h9 : (⟨x, hKD hx⟩ : ↥D) ^ 9 = 1 := by
      apply Subtype.ext
      simpa using hx9
    exact congrArg Subtype.val (sba6s_exp3 eD h9)
  have hsupZK : CFSG.Assembly.IsElemAbelian 3 (Zg ⊔ K) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hZe hKel
      (fun a ha b hb => hZc a ha b (hDY (hKD hb)))
  have hBle : B ≤ Zg ⊔ K := by
    intro b hb
    have hbY : b ∈ ((Zg ⊔ D : Subgroup G) : Set G) := hYZD (hBY hb)
    rw [Subgroup.normal_mul] at hbY
    obtain ⟨z, hz, d, hd, rfl⟩ := hbY
    have hdB : d ∈ B := by
      have := B.mul_mem (B.inv_mem (hZB hz)) hb
      simpa using this
    exact Subgroup.mul_mem_sup hz (hBDK ⟨hdB, hd⟩)
  have hKB : K ≤ B := by
    have := hBmax _ hsupZK hBle
    rw [← this]
    exact le_sup_right
  have hK9D : Nat.card (K.subgroupOf D) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv]
    exact hK9'
  have hTD : T ⊓ D = ⊥ := by
    have hR := sba6s_two_group_trivial eD (P := K.subgroupOf D) (R := (T ⊓ D).subgroupOf D) hK9D
      (fun x hx => Subtype.ext (hKel.2 _ hx))
      ((hT2.to_le inf_le_left).comap_subtype)
      (fun x hx r hr => by
        have hxT : (x : G) * (r : G) * (x : G)⁻¹ ∈ T :=
          (Subgroup.mem_normalizer_iff.mp (hTB (hKB hx)) r).mp (Subgroup.mem_inf.mp hr).1
        exact Subgroup.mem_inf.mpr ⟨hxT, D.mul_mem (D.mul_mem x.2 r.2) (D.inv_mem x.2)⟩)
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hmem : (⟨y, hy.2⟩ : ↥D) ∈ (T ⊓ D).subgroupOf D := hy
    rw [hR, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hTY : T ⊓ Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    obtain ⟨hT', hY'⟩ := ht
    have hty : t ∈ ((Zg ⊔ D : Subgroup G) : Set G) := hYZD hY'
    rw [Subgroup.normal_mul] at hty
    obtain ⟨z, hz, d, hd, rfl⟩ := hty
    obtain ⟨k, hk⟩ := hT2 ⟨z * d, hT'⟩
    have hk' : (z * d) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hzd : Commute z d := hZc z hz d (hDY hd)
    rw [hzd.mul_pow] at hk'
    have hzpow : z ^ 2 ^ k ∈ Zg ⊓ D := by
      refine ⟨Subgroup.pow_mem _ hz _, ?_⟩
      have : z ^ 2 ^ k = (d ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk'
      rw [this]
      exact D.inv_mem (D.pow_mem hd _)
    rw [hZD, Subgroup.mem_bot] at hzpow
    have hz1 : z = 1 := sba6s_eq_one_of_pow hzpow (hZ3' z hz) (by decide)
    subst hz1
    have hdT : d ∈ T ⊓ D := ⟨by simpa using hT', hd⟩
    rw [hTD, Subgroup.mem_bot] at hdT
    simp [hdT]
  have hcomm : ∀ t ∈ T, ∀ b ∈ B, t * b = b * t := by
    intro t ht b hb
    have hbN : b * t⁻¹ * b⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hTB hb) t⁻¹).mp (T.inv_mem ht)
    have hc2 : t * (b * t⁻¹ * b⁻¹) ∈ Y := by
      have h1 : t * b * t⁻¹ ∈ Y := hYn.conj_mem b (hBY hb) t
      have h2 : (t * b * t⁻¹) * b⁻¹ ∈ Y := Y.mul_mem h1 (Y.inv_mem (hBY hb))
      simpa [mul_assoc] using h2
    have h0 : t * (b * t⁻¹ * b⁻¹) ∈ T ⊓ Y := ⟨T.mul_mem ht hbN, hc2⟩
    rw [hTY, Subgroup.mem_bot] at h0
    calc t * b = (t * (b * t⁻¹ * b⁻¹)) * (b * t) := by group
      _ = b * t := by rw [h0, one_mul]
  have hDc : ∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ = d := by
    intro t ht
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hγ : MulAut.conjNormal (H := D) t = 1 := by
      refine sba6s_aut_one eD (P := K.subgroupOf D) hK9D (MulAut.conjNormal t) ?_ (m := k) ?_
      · intro x hx
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have h1 := hcomm t ht x (hKB hx)
        calc t * (x : G) * t⁻¹ = (x : G) * t * t⁻¹ := by rw [h1]
          _ = x := by group
      · rw [← map_pow, hk', map_one]
    intro d hd
    have := congrArg (fun γ : MulAut ↥D => ((γ ⟨d, hd⟩ : ↥D) : G)) hγ
    simpa [MulAut.conjNormal_apply] using this
  have hYc : ∀ t ∈ T, ∀ y ∈ Y, y * t = t * y := by
    intro t ht y hy
    have hy' : y ∈ ((Zg ⊔ D : Subgroup G) : Set G) := hYZD hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨z, hz, d, hd, rfl⟩ := hy'
    have h1 : t * z = z * t := hcomm t ht z (hZB hz)
    have h2 : t * d = d * t := by
      have := hDc t ht d hd
      calc t * d = (t * d * t⁻¹) * t := by group
        _ = d * t := by rw [this]
    calc z * d * t = z * (d * t) := by rw [mul_assoc]
      _ = z * (t * d) := by rw [h2]
      _ = (z * t) * d := by rw [mul_assoc]
      _ = (t * z) * d := by rw [h1]
      _ = t * (z * d) := by rw [mul_assoc]
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  exact sba6s_two_element_trivial hO2 hYn (fun g => sba6s_exists_pow_mem_oResidual g)
    ⟨k, congrArg Subtype.val hk⟩ (hYc t ht)

private theorem sba6s_max_map {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    {B' : Subgroup (X ⧸ CFSG.pCore 2 X)} (hB' : CFSG.Assembly.IsElemAbelian 3 B')
    (hAB' : A.map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤ B') :
    B' ≤ A.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup X := CFSG.pCore 2 X with hQ
  set π : X →* X ⧸ Q := QuotientGroup.mk' Q with hπ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hinj : ∀ (E : Subgroup X) (c : ℕ), Odd c → (∀ x ∈ E, x ^ c = 1) →
      ∀ a ∈ E, ∀ b ∈ E, π a = π b → a = b := by
    intro E c hc hE a ha b hb hab
    have hab' : (QuotientGroup.mk a : X ⧸ Q) = QuotientGroup.mk b := hab
    have h1 : a⁻¹ * b ∈ Q := QuotientGroup.eq.mp hab'
    obtain ⟨j, hj⟩ := hQ2 ⟨a⁻¹ * b, h1⟩
    have hj' : (a⁻¹ * b) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have h2 : (a⁻¹ * b) ^ c = 1 := hE _ (E.mul_mem (E.inv_mem ha) hb)
    exact inv_mul_eq_one.mp (sba6s_eq_one_of_pow hj' h2 hc)
  have hinjA : ∀ a ∈ A, ∀ b ∈ A, π a = π b → a = b := hinj A 3 (by decide) hA.2
  set L : Subgroup X := B'.comap π with hL
  have hAL : A ≤ L := fun a ha => hAB' ⟨a, ha, rfl⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hB'.isPGroup
  have hL3 : 3 ^ n ∣ Nat.card L := by
    have h := Subgroup.card_dvd_of_surjective
      (MonoidHom.subgroupComap_surjective π B' (QuotientGroup.mk'_surjective Q))
    rw [hn] at h
    exact h
  have hAdvd : Nat.card A ∣ 3 ^ n := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hA.isPGroup
    have hle : Nat.card A ≤ Nat.card B' := by
      refine Nat.card_le_card_of_injective
        (fun a : A => (⟨π a, hAB' ⟨a, a.2, rfl⟩⟩ : B')) ?_
      intro a b hab
      exact Subtype.ext (hinjA a a.2 b b.2 (congrArg Subtype.val hab))
    rw [hm, hn] at hle
    rw [hm]
    exact pow_dvd_pow 3 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)
  obtain ⟨K, hKcard, hAK, hKL⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := X)
    Nat.prime_three (H := A) (L := L) hAdvd hL3 hAL
  have hKinj : ∀ a ∈ K, ∀ b ∈ K, π a = π b → a = b := by
    refine hinj K (3 ^ n) (Odd.pow (by decide)) (fun x hx => ?_)
    have h := pow_card_eq_one' (x := (⟨x, hx⟩ : K))
    rw [hKcard] at h
    simpa using congrArg Subtype.val h
  have hKB' : ∀ x ∈ K, π x ∈ B' := fun x hx => hKL hx
  have hKel : CFSG.Assembly.IsElemAbelian 3 K := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hKinj _ (K.mul_mem a.2 b.2) _ (K.mul_mem b.2 a.2)
      rw [map_mul, map_mul]
      exact CFSG.Open.IsElemAbelian.comm hB' (hKB' a a.2) (hKB' b b.2)
    · apply hKinj _ (K.pow_mem hx 3) _ K.one_mem
      rw [map_pow, map_one]
      exact hB'.2 _ (hKB' x hx)
  have hKA : K = A := hAmax K hKel hAK
  have hmapK : K.map π = B' := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hKB' x hx
    · have hbij : Function.Bijective (fun x : K => (⟨π x, x, x.2, rfl⟩ : K.map π)) := by
        constructor
        · intro a b hab
          exact Subtype.ext (hKinj a a.2 b b.2 (congrArg Subtype.val hab))
        · rintro ⟨_, x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
      rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hKcard, hn]
  calc B' = K.map π := hmapK.symm
    _ ≤ A.map π := by rw [hKA]

theorem le_pCore_of_isTripleCover_not_quasisimple
    {A S : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hS : S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2))
    (hT : Sec4.IsTripleCover ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) (alternatingGroup (Fin 6)))
    (hnq : ¬ CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) :
    S ≤ CFSG.pCore 2 X := by
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hSA : A ≤ Subgroup.normalizer (S : Set X) := hS.prop.2.2
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hbot : S.map π = ⊥ :=
    sba6s_main (fun N hN h2 => sba6s_hO2 N hN h2) hT hnq
      (CFSG.Open.IsElemAbelian.map hA π)
      (fun B' hB' hle => le_antisymm (sba6s_max_map hA hAmax hB' hle) hle)
      (hS2.map π) ((Subgroup.map_mono hSA).trans (Subgroup.le_normalizer_map π))
  intro s hs
  have hmem : π s ∈ S.map π := ⟨s, hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff s).mp hmem

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
