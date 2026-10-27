module

public import CFSG.Quasithin.SteinbergCDConjugateElementaryPairCubic
public import CFSG.Quasithin.H13.A7SharedSolvableOvergroup
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin.SteinbergCF

open Subgroup

theorem isElementaryAbelian_subgroupOf {p : ℕ} {G : Type*} [Group G] {K : Subgroup G}
    (N : Subgroup G) [hK : IsElementaryAbelian p K] : IsElementaryAbelian p (K.subgroupOf N) :=
  { toIsMulCommutative := ⟨⟨fun a b => by
      have h := hK.toIsMulCommutative.is_comm.comm ⟨((a : N) : G), a.2⟩ ⟨((b : N) : G), b.2⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hK.exponent_dvd_p
        ⟨((a : N) : G), a.2⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h }

theorem eq_one_of_mem_zpowers_of_pow {G : Type*} [Group G] {x n : G} (hxodd : Odd (orderOf x))
    (hn : n ∈ zpowers x) {k : ℕ} (hk : n ^ 2 ^ k = 1) : n = 1 := by
  have h1 : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf n ∣ orderOf x := orderOf_dvd_of_mem_zpowers hn
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hxodd)
  have h3 : orderOf n = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp h3

theorem exists_index_two_centralizes_inverts {G : Type*} [Group G] {P E : Subgroup G}
    [Finite P] [Finite E] (hPodd : ¬ 2 ∣ Nat.card P) (hEP : E ≤ normalizer (P : Set G))
    [hE : IsElementaryAbelian 2 E] (hact : ∃ e ∈ E, ∃ y ∈ P, e * y * e⁻¹ ≠ y) :
    ∃ x ∈ P, x ≠ 1 ∧ ∃ B : Subgroup G, B ≤ E ∧ B.relIndex E = 2 ∧
      (∀ b ∈ B, b * x = x * b) ∧ ∀ e ∈ E, e ∉ B → e * x * e⁻¹ = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥E →* MulAut ↥P := (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hEP)
  let _ : MulDistribMulAction ↥E ↥P := MulDistribMulAction.compHom ↥P φ
  have hsmul : ∀ (e : E) (y : P), ((e • y : P) : G) = (e : G) * y * (e : G)⁻¹ := fun e y => rfl
  obtain ⟨e₀, he₀, y₀, hy₀, hne⟩ := hact
  have : Nontrivial ↥E := ⟨⟨⟨e₀, he₀⟩, 1, fun h => hne (by
    have h' : e₀ = 1 := congrArg Subtype.val h
    rw [h', one_mul, inv_one, mul_one])⟩⟩
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := ↥E) (H := ↥P) hPodd
  have hex : ∃ B : Subgroup ↥E, B.index = 2 ∧ ∃ y ∈ CFSG.fixedPointSubgroup ↥B ↥P,
      ∃ e : ↥E, e • y ≠ y := by
    by_contra hno
    have hall : ∀ B : Subgroup ↥E, B.index = 2 → ∀ y ∈ CFSG.fixedPointSubgroup ↥B ↥P,
        ∀ e : ↥E, e • y = y := fun B hB y hy e => by
      by_contra h
      exact hno ⟨B, hB, y, hy, e, h⟩
    have hle : (⊤ : Subgroup ↥P) ≤ CFSG.fixedPointSubgroup ↥E ↥P := by
      rw [← hgen]
      refine iSup₂_le fun B hB y hy => ?_
      exact (FixedPoints.mem_subgroup _ _ _).mpr fun e => hall B hB y hy e
    have h1 := (FixedPoints.mem_subgroup _ _ _).mp (hle (Subgroup.mem_top ⟨y₀, hy₀⟩)) ⟨e₀, he₀⟩
    exact hne (congrArg Subtype.val h1)
  obtain ⟨B, hB, y, hy, e, hey⟩ := hex
  have hyB : ∀ b : ↥B, (b : ↥E) • y = y := fun b =>
    (FixedPoints.mem_subgroup _ _ _).mp hy b
  have heB : e ∉ B := fun h => hey (hyB ⟨e, h⟩)
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hE.toIsMulCommutative.is_comm.comm a b
  have hE2 : ∀ a : ↥E, a * a = 1 := fun a => by
    rw [← pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hE.exponent_dvd_p a
  set x : ↥P := y⁻¹ * (e • y) with hx
  have hx1 : x ≠ 1 := by
    intro h
    apply hey
    rw [hx, inv_mul_eq_one] at h
    exact h.symm
  have hBx : ∀ b : ↥B, (b : ↥E) • x = x := by
    intro b
    rw [hx, smul_mul', smul_inv', hyB b, smul_smul, hEc, ← smul_smul, hyB b]
  have hex' : e • x = x⁻¹ := by
    rw [hx, smul_mul', smul_inv', smul_smul, hE2, one_smul, mul_inv_rev, inv_inv]
  refine ⟨(x : G), x.2, fun h => hx1 (Subtype.ext h), B.map E.subtype, map_subtype_le B, ?_, ?_, ?_⟩
  · show (Subgroup.comap E.subtype (B.map E.subtype)).index = 2
    rw [comap_map_eq_self_of_injective E.subtype_injective]
    exact hB
  · rintro _ ⟨b, hb, rfl⟩
    have h := congrArg Subtype.val (hBx ⟨b, hb⟩)
    rw [hsmul] at h
    simp only [Subgroup.coe_subtype]
    calc (b : G) * x = (b : G) * x * (b : G)⁻¹ * b := by group
      _ = x * b := by rw [h]
  · intro e' he' he'B
    have he'B' : (⟨e', he'⟩ : ↥E) ∉ B := fun h => he'B ⟨_, h, rfl⟩
    have hmem : e⁻¹ * ⟨e', he'⟩ ∈ B := by
      rw [Subgroup.mul_mem_iff_of_index_two hB, inv_mem_iff]
      exact iff_of_false heB he'B'
    have hdec : (⟨e', he'⟩ : ↥E) = e * (e⁻¹ * ⟨e', he'⟩) := by group
    have h := congrArg Subtype.val (show (⟨e', he'⟩ : ↥E) • x = x⁻¹ by
      rw [hdec, ← smul_smul, hBx ⟨_, hmem⟩, hex'])
    rw [hsmul] at h
    exact h

theorem mem_conjugate_iff {G : Type*} [Group G] {H : Subgroup G} {g z : G} :
    z ∈ conjugate H g ↔ g * z * g⁻¹ ∈ H := by
  rw [conjugate, mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem map_conjugate {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G)
    (g : G) : (conjugate H g).map f = conjugate (H.map f) (f g) := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem index_two_inverting_join {G : Type*} [Group G] [Finite G] {x : G} (hx1 : x ≠ 1)
    (hxodd : Odd (orderOf x)) {E B : Subgroup G} (hBE : B ≤ E) (hB2 : B.relIndex E = 2)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1)
    (hBx : ∀ b ∈ B, b * x = x * b) (hEx : ∀ e ∈ E, e ∉ B → e * x * e⁻¹ = x⁻¹) :
    x ∈ E ⊔ conjugate E x ∧ ¬ 2 ∣ E.relIndex (E ⊔ conjugate E x) ∧
      E ⊔ conjugate E x ≤ normalizer (B : Set G) ∧
      ∀ N : Subgroup G, N ≤ E ⊔ conjugate E x → E ⊔ conjugate E x ≤ normalizer (N : Set G) →
        IsPGroup 2 N → N ≤ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := E ⊔ conjugate E x with hI
  have hEconj : ∀ e ∈ E, e * x * e⁻¹ ∈ zpowers x := by
    intro e he
    by_cases heB : e ∈ B
    · rw [hBx e heB, mul_inv_cancel_right]
      exact mem_zpowers x
    · rw [hEx e he heB]
      exact inv_mem (mem_zpowers x)
  have hfwd : ∀ e ∈ E, ∀ h ∈ zpowers x, e * h * e⁻¹ ∈ zpowers x := by
    intro e he h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact zpow_mem (hEconj e he) k
  have hEN : E ≤ normalizer (zpowers x : Set G) := by
    intro e he
    rw [mem_normalizer_iff]
    intro h
    refine ⟨hfwd e he h, fun hh => ?_⟩
    have h1 := hfwd e he _ hh
    have hee : e * e = 1 := by rw [← pow_two]; exact hE2 e he
    have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    rwa [hinv, show e * (e * h * e) * e = (e * e) * h * (e * e) by group, hee, one_mul,
      mul_one] at h1
  have hK₀N : zpowers x ⊔ E ≤ normalizer (zpowers x : Set G) := sup_le le_normalizer hEN
  have hK₀mem : ∀ k ∈ zpowers x ⊔ E, ∃ y ∈ zpowers x, ∃ e ∈ E, k = y * e := by
    intro k hk
    have hk' : k ∈ ((zpowers x ⊔ E : Subgroup G) : Set G) := hk
    rw [coe_mul_of_right_le_normalizer_left (zpowers x) E hEN] at hk'
    obtain ⟨y, hy, e, he, rfl⟩ := hk'
    exact ⟨y, hy, e, he, rfl⟩
  have hIK : I ≤ zpowers x ⊔ E := by
    refine sup_le le_sup_right ?_
    intro z hz
    rw [mem_conjugate_iff] at hz
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (mem_sup_left (mem_zpowers x))) (mem_sup_right hz))
      (mem_sup_left (mem_zpowers x))
  obtain ⟨u, huE, huB⟩ : ∃ u ∈ E, u ∉ B := by
    by_contra h
    have hle : E ≤ B := fun u hu => by_contra fun hu' => h ⟨u, hu, hu'⟩
    rw [relIndex_eq_one.mpr hle] at hB2
    exact absurd hB2 (by norm_num)
  have hxI : x ∈ I := by
    have h1 : x⁻¹ * u * x ∈ conjugate E x := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using huE
    have h2 : x⁻¹ * u * x * u⁻¹ ∈ I := mul_mem (mem_sup_right h1) (inv_mem (mem_sup_left huE))
    have h3 : x⁻¹ * u * x * u⁻¹ = x⁻¹ * x⁻¹ := by
      calc x⁻¹ * u * x * u⁻¹ = x⁻¹ * (u * x * u⁻¹) := by group
        _ = x⁻¹ * x⁻¹ := by rw [hEx u huE huB]
    rw [h3] at h2
    have h4 : x * x ∈ I := by
      have := inv_mem h2
      rwa [mul_inv_rev, inv_inv] at this
    obtain ⟨t, ht⟩ := hxodd
    have h5 : (x * x) ^ (t + 1) = x := by
      rw [← pow_two, ← pow_mul, show 2 * (t + 1) = orderOf x + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [← h5]
    exact pow_mem h4 _
  have hE2grp : IsPGroup 2 E := fun a => ⟨1, Subtype.ext (by simpa using hE2 a a.2)⟩
  have hmax : ∀ S : Subgroup G, IsPGroup 2 S → E ≤ S → S ≤ zpowers x ⊔ E → S ≤ E := by
    intro S hS hES hSK s hs
    obtain ⟨y, hy, e, he, rfl⟩ := hK₀mem s (hSK hs)
    have hyS : y ∈ S := by
      have := mul_mem hs (inv_mem (hES he))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨k, hk⟩ := hS ⟨y, hyS⟩
    have hy1 : y = 1 := eq_one_of_mem_zpowers_of_pow hxodd hy (k := k)
      (by simpa using congrArg Subtype.val hk)
    rw [hy1, one_mul]
    exact he
  have hEI : E ≤ I := le_sup_left
  have hodd : ¬ 2 ∣ E.relIndex I := by
    have hEsub : IsPGroup 2 (E.subgroupOf I) :=
      hE2grp.comap_of_injective I.subtype I.subtype_injective
    obtain ⟨S, hS⟩ := hEsub.exists_le_sylow
    have hSE : (S : Subgroup ↥I) ≤ E.subgroupOf I := by
      have h1 := hmax ((S : Subgroup ↥I).map I.subtype) (S.isPGroup'.map _)
        (fun e he => ⟨⟨e, hEI he⟩, hS (show (⟨e, hEI he⟩ : ↥I) ∈ E.subgroupOf I from he), rfl⟩)
        ((map_subtype_le _).trans hIK)
      intro s hs
      exact h1 ⟨s, hs, rfl⟩
    have heq : (S : Subgroup ↥I) = E.subgroupOf I := le_antisymm hSE hS
    have := S.not_dvd_index
    rw [heq] at this
    exact this
  have hBcent : zpowers x ⊔ E ≤ centralizer (B : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro b hb
      exact hBx b hb
    · intro e he
      rw [mem_centralizer_iff]
      intro b hb
      exact hEc b (hBE hb) e he
  have hBn : I ≤ normalizer (B : Set G) := by
    intro g hg
    have hgc := mem_centralizer_iff.mp (hBcent (hIK hg))
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : g * h * g⁻¹ = h := by rw [← hgc h hh, mul_inv_cancel_right]
      rwa [h1]
    · intro hh
      have h1 := hgc _ hh
      have h2 : g * h * g⁻¹ = h := by
        have h3 : g * h = g * (g * h * g⁻¹) := by
          calc g * h = g * h * g⁻¹ * g := by group
            _ = g * (g * h * g⁻¹) := h1
        exact (mul_left_cancel h3).symm
      rwa [h2] at hh
  refine ⟨hxI, hodd, hBn, fun N hNI hIN hN2 n hn => ?_⟩
  obtain ⟨y, hy, e, he, rfl⟩ := hK₀mem _ (hIK (hNI hn))
  have hc1 : (y * e) * x * (y * e)⁻¹ * x⁻¹ ∈ N := by
    have : x * (y * e)⁻¹ * x⁻¹ ∈ N := (mem_normalizer_iff.mp (hIN hxI) _).mp (inv_mem hn)
    have h2 := mul_mem hn this
    simpa [mul_assoc] using h2
  have hc2 : (y * e) * x * (y * e)⁻¹ * x⁻¹ ∈ zpowers x := by
    have : (y * e) * x * (y * e)⁻¹ ∈ zpowers x :=
      (mem_normalizer_iff.mp (hK₀N (hIK (hNI hn))) x).mp (mem_zpowers x)
    exact mul_mem this (inv_mem (mem_zpowers x))
  obtain ⟨k, hk⟩ := hN2 ⟨_, hc1⟩
  have hc : (y * e) * x * (y * e)⁻¹ * x⁻¹ = 1 :=
    eq_one_of_mem_zpowers_of_pow hxodd hc2 (k := k) (by simpa using congrArg Subtype.val hk)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hy
  have hyx : Commute y x := by
    rw [← hj]
    exact (Commute.refl x).zpow_left j
  have hex : e * x = x * e := by
    have h1 : (y * e) * x = x * (y * e) := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
      exact hc
    have h2 : y * (e * x) = y * (x * e) := by
      calc y * (e * x) = (y * e) * x := by group
        _ = x * (y * e) := h1
        _ = (x * y) * e := by group
        _ = (y * x) * e := by rw [hyx.eq]
        _ = y * (x * e) := by group
    exact mul_left_cancel h2
  have heB : e ∈ B := by
    by_contra heB
    have h1 := hEx e he heB
    rw [hex, mul_inv_cancel_right] at h1
    have h2 : x ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h1]
      exact inv_mul_cancel x
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at hxodd
        exact (Nat.not_odd_iff_even.mpr even_two) hxodd
    exact hx1 (orderOf_eq_one_iff.mp h4)
  have hcy : Commute e y := by
    rw [← hj]
    exact (show Commute e x from hex).zpow_right j
  have hey : Commute (y * e) e⁻¹ := (hcy.symm.mul_left (Commute.refl e)).inv_right
  obtain ⟨m, hm⟩ := hN2 ⟨y * e, hn⟩
  have hm' : (y * e) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hy1 : y = 1 := by
    apply eq_one_of_mem_zpowers_of_pow hxodd hy (k := m + 1)
    have h1 : y = (y * e) * e⁻¹ := by group
    have h2 : (y * e) ^ 2 ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, hm', one_pow]
    have h3 : e⁻¹ ^ 2 ^ (m + 1) = 1 := by
      rw [pow_succ', pow_mul, inv_pow, hE2 e he, inv_one, one_pow]
    rw [h1, hey.mul_pow, h2, h3, one_mul]
  rw [hy1, one_mul]
  exact heB

theorem map_conj_eq_of_mem_normalizer' {G : Type*} [Group G] {B : Subgroup G} {a : G}
    (ha : a ∈ normalizer (B : Set G)) : B.map (MulAut.conj a).toMonoidHom = B := by
  ext h
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  have := (mem_normalizer_iff.mp (inv_mem ha) h).symm
  rwa [inv_inv] at this

theorem le_normalizer_sup_of_le {G : Type*} [Group G] {A B C : Subgroup G}
    (hB : A ≤ normalizer (B : Set G)) (hC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  intro a ha
  have hX : (B ⊔ C).map (MulAut.conj a).toMonoidHom = B ⊔ C := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer' (hB ha),
      map_conj_eq_of_mem_normalizer' (hC ha)]
  rw [mem_normalizer_iff]
  intro h
  have h1 : a * h * a⁻¹ ∈ B ⊔ C ↔ h ∈ B ⊔ C := by
    conv_lhs => rw [← hX]
    rw [mem_map_equiv, MulAut.conj_symm_apply]
    simp [mul_assoc]
  exact h1.symm

theorem centralizer_eq_comap_subtype {G : Type*} [Group G] {I : Subgroup G} (K : Subgroup ↥I) :
    centralizer (K : Set ↥I) =
      (centralizer ((K.map I.subtype : Subgroup G) : Set G)).comap I.subtype := by
  ext z
  simp only [mem_comap, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (h k hk)
  · intro h k hk
    exact Subtype.ext (h _ ⟨k, hk, rfl⟩)

open CFSG.QuasithinUnique in
theorem sylow_inf_and_relIndex_pCoreOf {G G' : Type*} [Group G] [Finite G] [Group G']
    (π : G →* G') {Q T V I : Subgroup G} (hker : π.ker = Q) (hQ2 : IsPGroup 2 Q)
    (hT2 : IsPGroup 2 T) (hQT : Q ≤ T) (hVT : V ≤ T) (hVI : V ≤ I) {B : Subgroup G'}
    (hBV : B ≤ V.map π) (hB2 : B.relIndex (V.map π) = 2)
    (hodd : ¬ 2 ∣ (V.map π).relIndex (I.map π)) (hBn : I.map π ≤ normalizer (B : Set G'))
    (hcore : ∀ N : Subgroup G', N ≤ I.map π → I.map π ≤ normalizer (N : Set G') →
      IsPGroup 2 N → N ≤ B) :
    IsSylowTwoOf (T ⊓ I) I ∧ (CFSG.Open.pCoreOf 2 I).relIndex V = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set πI : ↥I →* G' := π.comp I.subtype with hπI
  have hrange : πI.range = I.map π := by
    rw [hπI, MonoidHom.range_comp, Subgroup.range_subtype]
  have hVmap : (V.subgroupOf I).map πI = V.map π := by
    rw [hπI, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVI]
  refine ⟨⟨inf_le_right, hT2.to_le inf_le_left, ?_⟩, ?_⟩
  · have hle : (V.map π).comap πI ≤ (T ⊓ I).subgroupOf I := by
      intro i hi
      obtain ⟨v, hv, hvi⟩ := hi
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, i.2⟩
      have hq : v⁻¹ * (i : G) ∈ Q := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hvi]
        simp [hπI]
      have : (i : G) = v * (v⁻¹ * i) := by group
      rw [this]
      exact mul_mem (hVT hv) (hQT hq)
    intro h2
    apply hodd
    rw [← hrange, ← Subgroup.index_comap]
    exact h2.trans (Subgroup.index_dvd_of_le hle)
  · have hpc : CFSG.Open.pCoreOf 2 I = (CFSG.pCore 2 ↥I).map I.subtype := by
      rw [CFSG.Open.pCoreOf]
    have hB2grp : IsPGroup 2 B := ((hT2.to_le hVT).map π).to_le hBV
    have hRO : B.comap πI = CFSG.pCore 2 ↥I := by
      apply le_antisymm
      · have hRn : (B.comap πI).Normal := ⟨fun r hr i => by
          show πI (i * r * i⁻¹) ∈ B
          rw [map_mul, map_mul, map_inv]
          exact (mem_normalizer_iff.mp (hBn (hrange ▸ ⟨i, rfl⟩)) _).mp hr⟩
        have hR2 : IsPGroup 2 (B.comap πI) := by
          intro r
          obtain ⟨a, ha⟩ := hB2grp ⟨πI r, r.2⟩
          have ha' : πI ((r : ↥I) ^ 2 ^ a) = 1 := by
            rw [map_pow]
            simpa using congrArg Subtype.val ha
          have hq : (((r : ↥I) : G) ^ 2 ^ a) ∈ Q := by
            rw [← hker, MonoidHom.mem_ker]
            simpa [hπI] using ha'
          obtain ⟨b, hb⟩ := hQ2 ⟨_, hq⟩
          have hb' : (((r : ↥I) : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
            simpa using congrArg Subtype.val hb
          refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
          simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
          rw [pow_add, pow_mul, hb']
        exact le_sSup ⟨hRn, hR2⟩
      · rw [← Subgroup.map_le_iff_le_comap]
        refine hcore _ ?_ ?_ (CFSG.pCore_isPGroup.map πI)
        · rw [← hrange]
          exact Subgroup.map_le_range _ _
        · have h1 := Subgroup.le_normalizer_map (H := CFSG.pCore 2 ↥I) πI
          rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
            hrange] at h1
          exact h1
    have h1 := Subgroup.relIndex_comap ((CFSG.pCore 2 ↥I).map I.subtype) I.subtype
      (V.subgroupOf I)
    rw [comap_map_eq_self_of_injective I.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hVI] at h1
    rw [hpc, ← h1, ← hRO, Subgroup.relIndex_comap, hVmap, hB2]

open CFSG.QuasithinUnique in
theorem isCharacteristicP_of_pCore_le_normalizer {G : Type*} [Group G] [Finite G]
    (hG : IsCharacteristicP 2 G) {I : Subgroup G}
    (hI : CFSG.pCore 2 G ≤ normalizer (I : Set G)) : IsCharacteristicP 2 ↥I := by
  have hQK : CFSG.pCore 2 G ≤ CFSG.Open.pCoreOf 2 (CFSG.pCore 2 G ⊔ I) :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer le_sup_left
      (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
      CFSG.pCore_isPGroup
  have hK : CharTwo (CFSG.pCore 2 G ⊔ I) := by
    intro k hk
    have hkC : k ∈ centralizer (CFSG.pCore 2 G : Set G) := centralizer_le hQK hk.2
    exact hQK (hG hkC)
  have hIK : I ≤ CFSG.pCore 2 G ⊔ I := le_sup_right
  have hn : (I.subgroupOf (CFSG.pCore 2 G ⊔ I)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hIK).mpr (sup_le hI le_normalizer)
  have hI2 := CharTwo.of_normal hK hIK hn
  rw [charTwo_iff_internal] at hI2
  unfold IsCharacteristicP
  exact hI2

open CFSG.QuasithinUnique in
theorem cubic_witness_of_conjugate_pair {G : Type*} [Group G] [Finite G] {T V : Subgroup G}
    {g : G} (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G)) [hVe : IsElementaryAbelian 2 V]
    (hgI : g ∈ V ⊔ conjugate V g) (hchar : IsCharacteristicP 2 ↥(V ⊔ conjugate V g))
    (hsyl : IsSylowTwoOf (T ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g))
    (hidx : (CFSG.Open.pCoreOf 2 (V ⊔ conjugate V g)).relIndex V = 2) :
    let A := conjugate V g ⊓ CFSG.Open.pCoreOf 2 (V ⊔ conjugate V g)
    A ≤ T ∧ A ≤ normalizer (V : Set G) ∧ autOn A V ≤ autOn T V ∧ autOn A V ≠ ⊥ ∧
      IsElementaryAbelian 2 (autOn A V) ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
      ∃ d r : ℕ, (centralizer (A : Set G)).relIndex V = 2 ^ d ∧
        Nat.card (autOn A V) = 2 ^ r ∧ d ≤ 2 * r := by
  intro A
  set I := V ⊔ conjugate V g with hI
  have hVI : V ≤ I := le_sup_left
  have hV'map : (V.subgroupOf I).map I.subtype = V := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVI]
  have hconj' : (conjugate (V.subgroupOf I) ⟨g, hgI⟩).map I.subtype = conjugate V g := by
    rw [map_conjugate, hV'map]
    rfl
  have hQ'map : (CFSG.pCore 2 ↥I).map I.subtype = CFSG.Open.pCoreOf 2 I := by
    rw [CFSG.Open.pCoreOf]
  have hgen : V.subgroupOf I ⊔ conjugate (V.subgroupOf I) ⟨g, hgI⟩ = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, hV'map, hconj', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hS2 : IsPGroup 2 (T.subgroupOf I) := by
    have h := hsyl.2.1.comap_of_injective I.subtype I.subtype_injective
    rwa [show (T ⊓ I).comap I.subtype = T.subgroupOf I from
      Subgroup.inf_subgroupOf_right T I] at h
  have hSodd : ¬ 2 ∣ (T.subgroupOf I).index := by
    have := hsyl.2.2
    rwa [Subgroup.inf_subgroupOf_right] at this
  have hVS : V.subgroupOf I ≤ T.subgroupOf I := fun v hv => hVT hv
  have hSV : T.subgroupOf I ≤ normalizer (V.subgroupOf I : Set ↥I) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro h
    exact mem_normalizer_iff.mp (hTV hs) h
  have : IsElementaryAbelian 2 (V.subgroupOf I) := isElementaryAbelian_subgroupOf I
  have hVQ' : (CFSG.pCore 2 ↥I).relIndex (V.subgroupOf I) = 2 := by
    have h1 := Subgroup.relIndex_comap ((CFSG.pCore 2 ↥I).map I.subtype) I.subtype
      (V.subgroupOf I)
    rw [comap_map_eq_self_of_injective I.subtype_injective, hV'map, hQ'map] at h1
    rw [h1, hidx]
  obtain ⟨-, -, -, -, ⟨hAQ, hQS, -⟩, -, hVA, hVAAA, hAe, d, r, hd, hr, -, hdr⟩ :=
    CFSG.Quasithin.conjugate_elementary_pair_order_two_core_image_cubic_bound hchar rfl hS2
      hSodd hVS hSV hgen hVQ' rfl rfl rfl rfl
  set AX := conjugate (V.subgroupOf I) ⟨g, hgI⟩ ⊓ CFSG.pCore 2 ↥I with hAX
  have hAmap : AX.map I.subtype = A := by
    rw [hAX, Subgroup.map_inf_eq _ _ _ I.subtype_injective, hconj', hQ'map]
  have hAT : A ≤ T := by
    rw [← hAmap]
    refine (Subgroup.map_mono (hAQ.trans hQS)).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hTV
  have hVAG : ⁅V, A⁆ ≠ ⊥ := by
    intro h
    apply hVA
    rw [← Subgroup.map_eq_bot_iff_of_injective _ I.subtype_injective, Subgroup.map_commutator,
      hV'map, hAmap, h]
  have hAnc : ¬ A ≤ centralizer (V : Set G) := by
    intro h
    apply hVAG
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    exact h
  have hAeG : IsElementaryAbelian 2 A := by
    have := Setup.Layer.isElementaryAbelian_map (p := 2) I.subtype AX
    rwa [hAmap] at this
  have hautE : IsElementaryAbelian 2 (autOn A V) := by
    have : IsElementaryAbelian 2 (A.subgroupOf (normalizer (V : Set G))) :=
      isElementaryAbelian_subgroupOf _
    exact Setup.Layer.isElementaryAbelian_map (p := 2) (conjAct V)
      (A.subgroupOf (normalizer (V : Set G)))
  refine ⟨hAT, hAN, Subgroup.map_mono (Subgroup.comap_mono hAT),
    autOn_ne_bot_of_not_le_centralizer hAN hAnc, hautE, ?_, d, r, ?_, ?_, hdr⟩
  · have h := congrArg (Subgroup.map I.subtype) hVAAA
    rwa [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_commutator, hV'map,
      hAmap, Subgroup.map_bot] at h
  · rw [centralizer_eq_comap_subtype, hAmap, Subgroup.relIndex_comap, hV'map] at hd
    exact hd
  · rw [card_autOn_eq_relIndex hAN, Subgroup.inf_relIndex_left]
    rw [centralizer_eq_comap_subtype, hV'map, Subgroup.relIndex_comap, hAmap] at hr
    exact hr

open CFSG.QuasithinUnique in
theorem solvable_minimal_parabolic_outside_core_seed_cubic_witness {H : Type*} [Group H]
    [Finite H] (hsolv : Group.IsSolvable H) (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hM : IsCoatom M)
    (hTM : (T : Subgroup H) ≤ M)
    (huniq : ∀ Y : Subgroup H, IsCoatom Y → (T : Subgroup H) ≤ Y → Y = M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVQ : ¬ V ≤ CFSG.pCore 2 H) :
    ∃ g : H, let I := V ⊔ conjugate V g
      g ∈ I ∧ IsSylowTwoOf ((T : Subgroup H) ⊓ I) I ∧ IsCharacteristicP 2 I ∧
        (CFSG.Open.pCoreOf 2 I).relIndex V = 2 ∧
        let A := conjugate V g ⊓ CFSG.Open.pCoreOf 2 I
        A ≤ T ∧ A ≤ normalizer (V : Set H) ∧ autOn A V ≤ autOn T V ∧ autOn A V ≠ ⊥ ∧
          IsElementaryAbelian 2 (autOn A V) ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
          ∃ d r : ℕ, (centralizer (A : Set H)).relIndex V = 2 ^ d ∧
            Nat.card (autOn A V) = 2 ^ r ∧ d ≤ 2 * r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 H with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hQT : Q ≤ T := hQ2.le_sylow_of_normal T
  have hker : (QuotientGroup.mk' Q).ker = Q := QuotientGroup.ker_mk' Q
  obtain ⟨p, hp, hp2, P, -, hPn, hPp, -, -, -, hfaith, -, -, -⟩ :=
    CFSG.Quasithin.H13.A7.A7_solvable_unique_Sylow_overgroup_structure hsolv T hTn hM hTM huniq
  set π := QuotientGroup.mk' Q with hπ
  have hVe : IsElementaryAbelian 2 (V.map π) := Setup.Layer.isElementaryAbelian_map π V
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hPodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  obtain ⟨v, hv, hvQ⟩ : ∃ v ∈ V, v ∉ Q := by
    by_contra h
    exact hVQ fun v hv => by_contra fun h' => h ⟨v, hv, h'⟩
  have hact : ∃ e ∈ V.map π, ∃ y ∈ P, e * y * e⁻¹ ≠ y := by
    refine ⟨π v, ⟨v, hv, rfl⟩, ?_⟩
    by_contra hall
    have h1 := hfaith (π v) ⟨v, hVT hv, rfl⟩ fun y hy => by
      have : π v * y * (π v)⁻¹ = y := by_contra fun h => hall ⟨y, hy, h⟩
      rw [this, mul_inv_cancel]
      exact one_mem _
    exact hvQ (hker ▸ (MonoidHom.mem_ker.mpr h1))
  have hEP : V.map π ≤ normalizer (P : Set (H ⧸ Q)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact le_top
  obtain ⟨x, hxP, hx1, B, hBV, hB2, hBx, hEx⟩ :=
    exists_index_two_centralizes_inverts hPodd hEP hact
  have hxodd : Odd (orderOf x) :=
    (Nat.not_even_iff_odd.mp fun h => hPodd (even_iff_two_dvd.mp h)).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard P hxP)
  have hEc : ∀ a ∈ V.map π, ∀ b ∈ V.map π, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : ∀ a ∈ V.map π, a ^ 2 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (A := V.map π) a ha
  obtain ⟨hxI, hodd, hBn, hcore⟩ :=
    index_two_inverting_join hx1 hxodd hBV hB2 hEc hE2 hBx hEx
  have himage : ∀ g : H, π g = x →
      (V ⊔ conjugate V g).map π = V.map π ⊔ conjugate (V.map π) x := by
    intro g hg
    rw [Subgroup.map_sup, map_conjugate, hg]
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective Q x
  have hex : ∃ n, ∃ g : H, π g = x ∧ Nat.card ↥(V ⊔ conjugate V g) = n := ⟨_, g₀, hg₀, rfl⟩
  obtain ⟨g₁, hg₁π, hg₁card⟩ := Nat.find_spec hex
  have hmin : ∀ g : H, π g = x →
      Nat.card ↥(V ⊔ conjugate V g₁) ≤ Nat.card ↥(V ⊔ conjugate V g) :=
    fun g hg => hg₁card ▸ Nat.find_min' hex ⟨g, hg, rfl⟩
  obtain ⟨g, hgI₁, hgπ⟩ : ∃ g ∈ V ⊔ conjugate V g₁, π g = x := by
    have h : x ∈ (V ⊔ conjugate V g₁).map π := by
      rw [himage g₁ hg₁π]
      exact hxI
    obtain ⟨g, hg, hgx⟩ := h
    exact ⟨g, hg, hgx⟩
  have hle : V ⊔ conjugate V g ≤ V ⊔ conjugate V g₁ := by
    refine sup_le le_sup_left ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ V ⊔ conjugate V g₁ := (le_sup_left : V ≤ V ⊔ conjugate V g₁) hw
    change g⁻¹ * w * g⁻¹⁻¹ ∈ V ⊔ conjugate V g₁
    exact mul_mem (mul_mem (inv_mem hgI₁) hw') (inv_mem (inv_mem hgI₁))
  have heqI : V ⊔ conjugate V g = V ⊔ conjugate V g₁ :=
    Subgroup.eq_of_le_of_card_ge hle (hmin g hgπ)
  have hgI : g ∈ V ⊔ conjugate V g := heqI ▸ hgI₁
  refine ⟨g, ?_⟩
  intro I
  have hIimg : I.map π = V.map π ⊔ conjugate (V.map π) x := himage g hgπ
  obtain ⟨hsyl, hidx⟩ := sylow_inf_and_relIndex_pCoreOf π hker hQ2 T.isPGroup' hQT hVT
    le_sup_left hBV hB2 (by rw [hIimg]; exact hodd) (by rw [hIimg]; exact hBn)
    (by rw [hIimg]; exact hcore)
  have hQV : Q ≤ normalizer (V : Set H) := hQT.trans hTV
  have hQc : Q ≤ normalizer (conjugate V g : Set H) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro h
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have hq' : g * q * g⁻¹ ∈ Q := (CFSG.pCore_normal (p := 2) (G := H)).conj_mem q hq g
    have h1 := mem_normalizer_iff.mp (hQV hq') (g * h * g⁻¹)
    rw [show g * q * g⁻¹ * (g * h * g⁻¹) * (g * q * g⁻¹)⁻¹ = g * (q * h * q⁻¹) * g⁻¹ by
      group] at h1
    exact h1
  have hchI : IsCharacteristicP 2 ↥I :=
    isCharacteristicP_of_pCore_le_normalizer hchar (le_normalizer_sup_of_le hQV hQc)
  exact ⟨hgI, hsyl, hchI, hidx, cubic_witness_of_conjugate_pair hVT hTV hgI hchI hsyl hidx⟩

end CFSG.Quasithin.SteinbergCF
