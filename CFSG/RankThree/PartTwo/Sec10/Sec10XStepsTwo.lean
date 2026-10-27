module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsU
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTwelve
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace Sec10XSteps

section General

variable {G : Type} [Group G]

theorem mem_normalizer_commutator_of_mem {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hX, Subgroup.mem_normalizer_iff_map_conj_eq.mp hY]

theorem mem_normalizer_sup_of_mem {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hX, Subgroup.mem_normalizer_iff_map_conj_eq.mp hY]

theorem conj_pow_eq_mul_pow {w c d : G} (hwc : w * c * w⁻¹ = c * d) (hwd : w * d * w⁻¹ = d)
    (k : ℕ) : w ^ k * c * (w ^ k)⁻¹ = c * d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hwdk : w * d ^ k * w⁻¹ = d ^ k := by rw [← conj_pow, hwd]
    calc w ^ (k + 1) * c * (w ^ (k + 1))⁻¹ = w * (w ^ k * c * (w ^ k)⁻¹) * w⁻¹ := by group
      _ = w * c * w⁻¹ * (w * d ^ k * w⁻¹) := by rw [ih]; group
      _ = c * d ^ (k + 1) := by rw [hwc, hwdk, pow_succ']; group

variable [Finite G]

theorem normalizer_le_normalizer_centralizer_of {D : Subgroup G} :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    change m * y * m⁻¹ ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : m⁻¹ * u * m ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) u).mp hu
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp hy) _ hu'
    calc u * (m * y * m⁻¹) = m * ((m⁻¹ * u * m) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * u * m)) * m⁻¹ := by rw [h1]
      _ = m * y * m⁻¹ * u := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]

theorem even_of_le_theta {A X B : Subgroup G} {a : G} (hX2 : IsPGroup 2 X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (haA : a ∈ A)
    (hXa : ¬ X ≤ Subgroup.centralizer ({a} : Set G))
    (hXθ : X ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G))) :
    Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer (B : Set G)), A⁆ : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxX, hxa⟩ : ∃ x ∈ X, x ∉ Subgroup.centralizer ({a} : Set G) := by
    by_contra hall
    push Not at hall
    exact hXa hall
  have hxa' : ⁅x, a⁆ ≠ 1 := by
    intro h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact hxa (Subgroup.mem_centralizer_singleton_iff.mpr h1)
  have hXA2 : IsPGroup 2 (⁅X, A⁆ : Subgroup G) :=
    hX2.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hAX)
  have hXA1 : (⁅X, A⁆ : Subgroup G) ≠ ⊥ := fun hb => hxa' (by
    have := Subgroup.commutator_mem_commutator hxX haA
    rwa [hb, Subgroup.mem_bot] at this)
  have h2 : 2 ∣ Nat.card (⁅X, A⁆ : Subgroup G) := by
    obtain ⟨m, hm⟩ := hXA2.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact hXA1 (Subgroup.eq_bot_of_card_eq _ hm)
    rw [hm]
    exact dvd_pow_self 2 hm0
  exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le
    (Subgroup.commutator_mono hXθ le_rfl)))

theorem le_of_inf_centralizer_mul_pow_le {c d : G} (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcd : c * d = d * c) (hE : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c, d} : Set G)))
    (hE9 : 9 ≤ Nat.card (Subgroup.closure ({c, d} : Set G))) {S M : Subgroup G}
    (hS2 : IsPGroup 2 S) (hES : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.normalizer (S : Set G))
    (hck : ∀ k : ℕ, S ⊓ Subgroup.centralizer ({c * d ^ k} : Set G) ≤ M)
    (hd : S ⊓ Subgroup.centralizer ({d} : Set G) ≤ M) : S ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hE (by simpa using hE9) hES hcop ?_
  intro v hv hv1 x hx
  obtain ⟨hxS, hxv'⟩ := hx
  have hxv : x * v = v * x := Subgroup.mem_centralizer_singleton_iff.mp hxv'
  obtain ⟨i, j, rfl⟩ := Sec10XProof.mem_closure_pair_of_commute hcd hv
  have hcd' : Commute c d := hcd
  by_cases hi : i % 3 = 0
  ·
    have hci : c ^ i = 1 := by
      rw [Sec10XProof.zpow_eq_zpow_emod_three hc3 i, hi, zpow_zero]
    rw [hci, one_mul] at hxv hv1
    have hj : j % 3 = 1 ∨ j % 3 = 2 := by
      have : j % 3 ≠ 0 := fun h0 => hv1 (by
        rw [Sec10XProof.zpow_eq_zpow_emod_three hd3 j, h0, zpow_zero])
      omega
    have hjj : (j * j) % 3 = 1 := by
      rcases hj with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
    have hxd : x * d = d * x := by
      have h1 : Commute x (d ^ j) := hxv
      have h2 := h1.zpow_right j
      rw [← zpow_mul, Sec10XProof.zpow_eq_zpow_emod_three hd3, hjj, zpow_one] at h2
      exact h2
    exact hd ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr hxd⟩
  ·
    have hii : (i * i) % 3 = 1 := by
      have : i % 3 = 1 ∨ i % 3 = 2 := by omega
      rcases this with h1 | h1 <;> rw [Int.mul_emod, h1] <;> norm_num
    set k : ℕ := ((i * j) % 3).toNat with hk
    have hkz : ((k : ℕ) : ℤ) = (i * j) % 3 := by
      rw [hk, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have hvi : (c ^ i * d ^ j) ^ i = c * d ^ k := by
      rw [(hcd'.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul,
        Sec10XProof.zpow_eq_zpow_emod_three hc3 (i * i), hii, zpow_one,
        Sec10XProof.zpow_eq_zpow_emod_three hd3 (j * i), mul_comm j i, ← hkz, zpow_natCast]
    have hxk : x * (c * d ^ k) = (c * d ^ k) * x := by
      have h1 : Commute x (c ^ i * d ^ j) := hxv
      have h2 := h1.zpow_right i
      rw [hvi] at h2
      exact h2
    exact hck k ⟨hxS, Subgroup.mem_centralizer_singleton_iff.mpr hxk⟩

omit [Finite G] in
theorem exists_conj_mem_inf_centralizer {c d : G} {X : Subgroup G} {w : G}
    (hwX : w ∈ Subgroup.normalizer (X : Set G)) (hwc : w * c * w⁻¹ = c * d)
    (hwd : w * d * w⁻¹ = d) (k : ℕ) {x : G}
    (hx : x ∈ X ⊓ Subgroup.centralizer ({c * d ^ k} : Set G)) :
    (w ^ k)⁻¹ * x * w ^ k ∈ X ⊓ Subgroup.centralizer ({c} : Set G) := by
  obtain ⟨hxS, hxc'⟩ := hx
  have hxc : x * (c * d ^ k) = c * d ^ k * x := Subgroup.mem_centralizer_singleton_iff.mp hxc'
  have hwkS : (w ^ k)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ hwX k)
  have hyS : (w ^ k)⁻¹ * x * ((w ^ k)⁻¹)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hwkS x).mp hxS
  rw [inv_inv] at hyS
  have hconj := conj_pow_eq_mul_pow hwc hwd k
  refine ⟨hyS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  set e := c * d ^ k with he
  have hc' : c = (w ^ k)⁻¹ * e * w ^ k := by
    calc c = (w ^ k)⁻¹ * (w ^ k * c * (w ^ k)⁻¹) * w ^ k := by group
      _ = (w ^ k)⁻¹ * e * w ^ k := by rw [hconj]
  have hxe : x * e = e * x := hxc
  rw [hc']
  calc ((w ^ k)⁻¹ * x * w ^ k) * ((w ^ k)⁻¹ * e * w ^ k) =
      (w ^ k)⁻¹ * (x * e) * w ^ k := by group
    _ = (w ^ k)⁻¹ * (e * x) * w ^ k := by rw [hxe]
    _ = ((w ^ k)⁻¹ * e * w ^ k) * ((w ^ k)⁻¹ * x * w ^ k) := by group

theorem le_of_inf_centralizer_le {c d : G} (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcd : c * d = d * c) (hE : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c, d} : Set G)))
    (hE9 : 9 ≤ Nat.card (Subgroup.closure ({c, d} : Set G))) {S M : Subgroup G}
    (hS2 : IsPGroup 2 S) (hES : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.normalizer (S : Set G))
    {w : G} (hwS : w ∈ Subgroup.normalizer (S : Set G)) (hwc : w * c * w⁻¹ = c * d)
    (hwd : w * d * w⁻¹ = d) (hwM : ∀ x ∈ M, w * x * w⁻¹ ∈ M)
    (hc : S ⊓ Subgroup.centralizer ({c} : Set G) ≤ M)
    (hd : S ⊓ Subgroup.centralizer ({d} : Set G) ≤ M) : S ≤ M := by
  have hwkM : ∀ k : ℕ, ∀ x ∈ M, w ^ k * x * (w ^ k)⁻¹ ∈ M := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      have h1 := hwM _ (ih x hx)
      have h2 : w * (w ^ k * x * (w ^ k)⁻¹) * w⁻¹ = w ^ (k + 1) * x * (w ^ (k + 1))⁻¹ := by
        group
      rwa [h2] at h1
  refine le_of_inf_centralizer_mul_pow_le hc3 hd3 hcd hE hE9 hS2 hES (fun k x hx => ?_) hd
  have h1 := hwkM k _ (hc (exists_conj_mem_inf_centralizer hwS hwc hwd k hx))
  have h2 : w ^ k * ((w ^ k)⁻¹ * x * w ^ k) * (w ^ k)⁻¹ = x := by group
  rwa [h2] at h1

end General

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem card_closure_c_d (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hd3 : orderOf d = 3) : Nat.card (Subgroup.closure ({c, d} : Set G)) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdA := h.d_mem_A hdL
  have hdL' : d ∈ L := (hdL ▸ Subgroup.mem_zpowers d : d ∈ A ⊓ L).2
  have hd3' : d ^ 3 = 1 := h.pow_three hdA
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  have hcl : Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hN : Subgroup.zpowers d ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) :
      Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (h.comm h.mem_A hdA) k).eq
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hd
    have h1 := disjoint_zpowers_of_pow_three (h.pow_three h.mem_A) h.c_not_mem_L
    exact hd1 ((Subgroup.disjoint_def.mp h1) hdL' hd)
  rw [hcl, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
    (disjoint_zpowers_of_pow_three hd3' hdc), Nat.card_zpowers, Nat.card_zpowers,
    h.orderOf_c, hd3]

theorem eq_bot_of_le_theta_inf_centralizer (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R)
    (hnot : ¬ sec10U L a ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTθ : T ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) (hTA : A ≤ Subgroup.normalizer (T : Set G)) :
    T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d₀, hd₀A, hd₀L, hd₀o⟩ := exists_mem_inf_orderOf h45 h
  have hd₀3 : d₀ ^ 3 = 1 := by rw [← hd₀o]; exact pow_orderOf_eq_one d₀
  have hd₀1 : d₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd₀o
    norm_num at hd₀o
  set Y := L ⊓ Subgroup.centralizer ({a} : Set G) with hY
  set U := sec10U L a with hUdef
  obtain ⟨hYcard, hU4, -, -⟩ := sec10U_facts h
  have hTH := hTc.trans (centralizer_le_normalizer_zpowers c)
  have hTL : T ≤ L := le_of_isPGroup_two h45 h hTH hT2 hd₀L hd₀3 hd₀1 (hTA hd₀A)
  have hTY : T ≤ Y := le_inf hTL (hTθ.trans (Subgroup.map_subtype_le _))
  have hUY : U ≤ Y := SteinbergBY.inSubgroup_pCore_le 2 Y
  have hYU : Y ≤ Subgroup.normalizer (U : Set G) := SteinbergBY.le_normalizer_inSubgroup_pCore 2 Y
  have hTU : T ≤ U := by
    have hU2 : IsPGroup 2 U := SteinbergBY.isPGroup_inSubgroup_pCore 2 Y
    have hTU2 : IsPGroup 2 (T ⊔ U : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hT2 hU2 (hTY.trans hYU)
    obtain ⟨m, hm⟩ := hTU2.exists_card_eq
    have hdvd : 2 ^ m ∣ 12 := by
      rw [← hm, ← hYcard]
      exact Subgroup.card_dvd_of_le (sup_le hTY hUY)
    have hm2 : m ≤ 2 := by
      by_contra hm2
      have : 2 ^ 3 ∣ 12 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    have heq : U = T ⊔ U := Subgroup.eq_of_le_of_card_ge le_sup_right (by
      rw [hm, hU4]
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num)
    rw [heq]
    exact le_sup_left
  have hd₀Y : d₀ ∈ Y := ⟨hd₀L, Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hd₀A h.a_mem)⟩
  have hUd := inf_centralizer_eq_bot h hd₀Y hd₀3 hd₀1
  have hP : IsPGroup 3 (Subgroup.zpowers d₀) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hd₀o, pow_one])
  have hmod := Sec6.card_inf_centralizer_modEq hP (Subgroup.zpowers_le.mpr (hTA hd₀A))
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hmod
  have hCT : T ⊓ Subgroup.centralizer ({d₀} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hUd]
    exact inf_le_inf_right _ hTU
  rw [hCT, Subgroup.card_bot] at hmod
  have hdvd : Nat.card T ∣ 4 := hU4 ▸ Subgroup.card_dvd_of_le hTU
  have hcases : Nat.card T = 1 ∨ Nat.card T = 4 := by
    obtain ⟨n, hn⟩ : ∃ n, Nat.card T = n := ⟨_, rfl⟩
    rw [hn] at hmod hdvd ⊢
    have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · exact absurd hdvd (by decide)
    · exact Or.inl rfl
    · exact absurd hmod (by decide)
    · exact absurd hdvd (by decide)
    · exact Or.inr rfl
  rcases hcases with h1 | h4
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : T = U := Subgroup.eq_of_le_of_card_ge hTU (by rw [h4, hU4])
    exact hnot (heq ▸ hTθ)

theorem exists_S_w (h107 : Item107) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hVθ : V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (hVA : A ≤ Subgroup.normalizer (V : Set G)) :
    ∃ S ∈ maxInvariantPiSubgroups
        (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
      V ≤ S ∧ ∃ w ∈ Subgroup.normalizer (A : Set G),
        w ∈ Subgroup.normalizer (S : Set G) ∧ w * a * w⁻¹ = a ∧ w * d * w⁻¹ = d ∧
          w * c * w⁻¹ = c * d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hAcl : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  obtain ⟨τ, hτT, hτa, hτc⟩ := Sec10XProof.exists_transvection h hdL hd3 hAcl
  obtain ⟨w₀, hw₀N, -, hw₀τ⟩ := Sec4.mem_autIn_iff.mp (h107 G A c L a R h d hdA hdL hτT)
  have hw₀ : ∀ x : A, w₀ * x * w₀⁻¹ = (τ x : G) := fun x => by
    rw [← hw₀τ, Sec4.normalizerMonoidHom_apply_coe]
  have hw₀a : w₀ * a * w₀⁻¹ = a := (hw₀ ⟨a, h.a_mem⟩).trans hτa
  have hw₀c : w₀ * c * w₀⁻¹ = c * d := (hw₀ ⟨c, h.mem_A⟩).trans hτc
  have hw₀d : w₀ * d * w₀⁻¹ = d := (hw₀ ⟨d, hdA⟩).trans (congrArg Subtype.val hτT.1)
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Θ := inSubgroup (aschbacherSolvableCore 3) Ca with hΘ
  have hAC : A ≤ Ca := Sec10XProof.le_centralizer_of_mem h h.a_mem
  have hAN : A ≤ Subgroup.normalizer (Θ : Set G) := hAC.trans (Sec6.le_normalizer_theta Ca)
  have hw₀C : w₀ ∈ Ca := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w₀ * a = w₀ * a * w₀⁻¹ * w₀ := by group
      _ = a * w₀ := by rw [hw₀a]
  have hw₀Θ : w₀ ∈ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta Ca hw₀C
  set ρ : A →* MulAut Θ := Θ.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρ
  have hρapp : ∀ (x : A) (y : Θ), ((ρ x y : Θ) : G) = (x : G) * y * (x : G)⁻¹ := fun x y =>
    Sec4.normalizerMonoidHom_apply_coe (hAN x.2) y
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    rw [hΘ, inSubgroup, Subgroup.card_map_of_injective Ca.subtype_injective]
    exact not_three_dvd_card_theta Ca
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Θ) := by
    rw [h.card_eq, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hΘ3)
  have hΘs : Group.IsSolvable Θ := by
    have : Group.IsSolvable (aschbacherSolvableCore 3 Ca) :=
      (solvable_prime_complement_core_characterization (H := Ca) Nat.prime_three).1
    exact Group.isSolvable_of_surjective
      (f := ((aschbacherSolvableCore 3 Ca).equivMapOfInjective Ca.subtype
        Ca.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hAs : Group.IsSolvable A := Group.isSolvable_of_comm fun x y => Subtype.ext (h.comm x.2 y.2)
  set V' := V.subgroupOf Θ with hV'
  have hV'2 : IsPGroup 2 V' := hV2.comap_subtype (K := Θ)
  have hV'inv : ∀ x : A, ∀ u ∈ V', ρ x u ∈ V' := fun x u hu => by
    rw [Subgroup.mem_subgroupOf, hρapp]
    exact (Subgroup.mem_normalizer_iff.mp (hVA x.2) u).mp (Subgroup.mem_subgroupOf.mp hu)
  obtain ⟨Q, hVQ, hQinv⟩ :=
    (PGroups.solvable_coprime_invariant_sylow_containment hcop ρ Nat.prime_two).1 V' hV'2 hV'inv
  have hQinv' : ∀ x : A, ∀ y ∈ (Q : Subgroup Θ), ρ x y ∈ (Q : Subgroup Θ) := fun x y hy => by
    rw [← hQinv x]
    exact ⟨y, hy, rfl⟩
  set S := (Q : Subgroup Θ).map Θ.subtype with hS
  have hSΘ : S ≤ Θ := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := Q.isPGroup'.map _
  have hSA : A ≤ Subgroup.normalizer (S : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨ρ ⟨x, hx⟩ s, hQinv' ⟨x, hx⟩ s hs, hρapp ⟨x, hx⟩ s⟩
    · rintro ⟨s, hs, hsz⟩
      refine ⟨ρ ⟨x, hx⟩⁻¹ s, hQinv' _ s hs, ?_⟩
      have h1 := hρapp ⟨x, hx⟩⁻¹ s
      simp only [Subgroup.coe_subtype] at hsz ⊢
      rw [h1, hsz]
      simp only [Subgroup.coe_inv, inv_inv]
      group
  have hSmax : S ∈ maxInvariantPiSubgroups Θ A (piOf 2) := by
    rw [mem_maxInvariantPiSubgroups_iff]
    refine ⟨⟨hSΘ, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2, hSA⟩, fun Y hY hSY => ?_⟩
    obtain ⟨hYΘ, hY2, -⟩ := hY
    have hY2' : IsPGroup 2 Y := (isPiSubgroup_piOf_iff Nat.prime_two Y).mp hY2
    have hQY : (Q : Subgroup Θ) ≤ Y.subgroupOf Θ := fun z hz =>
      Subgroup.mem_subgroupOf.mpr (hSY ⟨z, hz, rfl⟩)
    have heq := Q.is_maximal' (hY2'.comap_subtype (K := Θ)) hQY
    refine le_antisymm (fun z hz => ?_) hSY
    have hzQ : (⟨z, hYΘ hz⟩ : Θ) ∈ (Q : Subgroup Θ) := heq ▸ Subgroup.mem_subgroupOf.mpr hz
    exact ⟨_, hzQ, rfl⟩
  have hVS : V ≤ S := fun u hu => ⟨⟨u, hVθ hu⟩, hVQ (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  set ρw : MulAut Θ := Θ.normalizerMonoidHom ⟨w₀, hw₀Θ⟩ with hρw
  have hρwapp : ∀ z : Θ, ((ρw z : Θ) : G) = w₀ * z * w₀⁻¹ := fun z =>
    Sec4.normalizerMonoidHom_apply_coe hw₀Θ z
  have hρwinv : ∀ z : Θ, ((ρw⁻¹ z : Θ) : G) = w₀⁻¹ * z * w₀ := fun z => by
    have h1 : ρw⁻¹ = Θ.normalizerMonoidHom ⟨w₀⁻¹, Subgroup.inv_mem _ hw₀Θ⟩ := by
      rw [hρw, ← map_inv]
      rfl
    rw [h1, Sec4.normalizerMonoidHom_apply_coe, inv_inv]
  set Q' : Sylow 2 Θ := ρw • Q with hQ'
  have hQ'mem : ∀ z : Θ, z ∈ (Q' : Subgroup Θ) ↔ ρw⁻¹ z ∈ (Q : Subgroup Θ) := fun z => by
    rw [hQ', Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hQ'inv : ∀ x : A, ∀ z ∈ (Q' : Subgroup Θ), ρ x z ∈ (Q' : Subgroup Θ) := by
    intro x z hz
    rw [hQ'mem] at hz ⊢
    have hx' : w₀⁻¹ * x * w₀ ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw₀N) x).mp x.2
      simpa using this
    have hmem := hQinv' ⟨_, hx'⟩ _ hz
    convert hmem using 1
    apply Subtype.ext
    rw [hρwinv, hρapp, hρapp, hρwinv]
    group
  obtain ⟨y, hyfix, hyQ⟩ :=
    GroupTheory.SteinbergBK.solvable_coprime_invariant_sylow_conjugacy hΘs hcop ρ Q' Q hQ'inv
      hQinv'
  have hyC : (y : G) ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      have h1 := congrArg Subtype.val (hyfix ⟨x, hx⟩)
      rw [hρapp] at h1
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h1]
  have hcomm : ∀ x ∈ A, (y : G)⁻¹ * x * y = x := fun x hx => by
    have h1 := Subgroup.mem_centralizer_iff.mp hyC x hx
    calc (y : G)⁻¹ * x * y = (y : G)⁻¹ * (x * y) := by group
      _ = (y : G)⁻¹ * (y * x) := by rw [h1]
      _ = x := by group
  set w := (y : G)⁻¹ * w₀ with hw
  have hwconj : ∀ g : G, w * g * w⁻¹ = (y : G)⁻¹ * (w₀ * g * w₀⁻¹) * y := fun g => by
    rw [hw]
    group
  refine ⟨S, hSmax, hVS, w, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hyC)) hw₀N
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      have hsQ' : ρw s ∈ (Q' : Subgroup Θ) := by
        rw [hQ'mem, MulAut.inv_apply_self]
        exact hs
      have hmem : (MulAut.conj y⁻¹) (ρw s) ∈ (Q : Subgroup Θ) := by
        rw [← hyQ]
        exact ⟨_, hsQ', rfl⟩
      refine ⟨_, hmem, ?_⟩
      change ((MulAut.conj y⁻¹ (ρw s) : Θ) : G) = w * (s : G) * w⁻¹
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv,
        hρwapp, hwconj]
    · exact (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge
  · rw [hwconj, hw₀a, hcomm a h.a_mem]
  · rw [hwconj, hw₀d, hcomm d hdA]
  · rw [hwconj, hw₀c, hcomm (c * d) (A.mul_mem h.mem_A hdA)]

section Never


theorem false_of_even_commutator (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h463 : Item463Inv)
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {B : Subgroup G}
    (hBA : B ≤ A) (hdB : d ∈ B) (hB9 : Nat.card B = 9)
    (heven : Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer (B : Set G)), A⁆ : Subgroup G))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  have hdA := h.d_mem_A hdL
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hAC : A ≤ C := Sec10XProof.le_centralizer_of_mem h hdA
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsec4 : SectionFourHyp C := h.toTheoremFourHyp.sectionFourHyp
    (Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hd1)
  set A' := A.subgroupOf C with hA'
  have hA'map : A'.map C.subtype = A := by
    rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAC]
  have hA'el : CFSG.Assembly.IsElemAbelian 3 A' :=
    Sec10XProof.isElemAbelian_subgroupOf C h.mem_partTwoF.1
  have hA'max : Maximal (fun B : Subgroup C => CFSG.Assembly.IsElemAbelian 3 B) A' := by
    refine ⟨hA'el, fun B hB hAB => ?_⟩
    have hBG := Sec4.isElemAbelian_map C.subtype hB
    have hAB' : A ≤ B.map C.subtype := hA'map ▸ Subgroup.map_mono hAB
    have heq := h.mem_partTwoF.2.1 _ hBG hAB'
    intro y hy
    have hy' : (y : G) ∈ B.map C.subtype := ⟨y, hy, rfl⟩
    rw [heq] at hy'
    exact Subgroup.mem_subgroupOf.mpr hy'
  have hA'card : Nat.card A' = 27 := (Sec10XProof.card_subgroupOf_of_le hAC).trans h.card_eq
  set d' : C := ⟨d, hdC⟩ with hd'
  have hd'A : d' ∈ A' := Subgroup.mem_subgroupOf.mpr hdA
  have hd'Z : d' ∈ Subgroup.center C := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hd'1 : d' ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hBC : B ≤ C := hBA.trans hAC
  set B' := B.subgroupOf C with hB'
  have hB'A' : B' ≤ A' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hBA (Subgroup.mem_subgroupOf.mp hx))
  have hB'card : Nat.card B' = 9 := (Sec10XProof.card_subgroupOf_of_le hBC).trans hB9
  have hCB : Subgroup.centralizer (B : Set G) ≤ C :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB)
  have hθmap : (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B' : Set C))).map
      C.subtype = inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) := by
    rw [hB', Sec10XProof.centralizer_subgroupOf hBC, Sec6.map_inSubgroup_theta_of_injective
      C.subtype C.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hCB]
  have heven' : Even (Nat.card (⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer (B' : Set C)), A'⁆ : Subgroup C)) := by
    have hmap : (⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B' : Set C)),
        A'⁆ : Subgroup C).map C.subtype =
        ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)), A⁆ := by
      rw [Subgroup.map_commutator, hθmap, hA'map]
    rw [← Subgroup.card_map_of_injective C.subtype_injective, hmap]
    exact heven
  obtain ⟨L', hL', hlist, V', hV', hV'1⟩ := h463 C hsec4 A' hA'max hA'card d' hd'A hd'Z hd'1
    (Sec10XProof.odd_card_theta_centralizer h hdL) B' hB'A' hB'card heven'
  set X := L'.map C.subtype with hX
  have hXd : X ∈ thetaComponentsAt 3 d := ⟨L', hL', rfl⟩
  obtain ⟨hV'L', hV'2, hV'A⟩ := hV'
  have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (h.comm h.mem_A hdA)
  have hVinv : V'.map C.subtype ∈ invariantPiSubgroups X (Subgroup.zpowers c) (piOf 2) := by
    refine ⟨Subgroup.map_mono hV'L', fun r hr => hV'2 r ?_, ?_⟩
    · rwa [Subgroup.card_map_of_injective C.subtype_injective] at hr
    · rw [Subgroup.zpowers_le]
      exact Sec10XProof.mem_normalizer_map_subtype (x := ⟨c, hcC⟩)
        (hV'A (Subgroup.mem_subgroupOf.mpr h.mem_A))
  have hV1 : V'.map C.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXd
  obtain ⟨hθs, -, hθp, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθQ := (solvable_prime_complement_core_quotient_centralizers Nat.prime_three
    (aschbacherSolvableCore 3 X) hθs hθp).2.2.1
  set eQ : X ⧸ aschbacherSolvableCore 3 X ≃* L' ⧸ aschbacherSolvableCore 3 L' :=
    Sec4.thetaQuotCongr (L'.equivMapOfInjective C.subtype C.subtype_injective).symm with heQ
  have hc : (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)).map
      (eQ : X ⧸ aschbacherSolvableCore 3 X →* L' ⧸ aschbacherSolvableCore 3 L') =
      Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L') := Subgroup.map_center_eq eQ
  have : (solvableRadical L').Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨eR⟩ := Sec10XProof.nonempty_quotient_center_mulEquiv (Y := L') hL'.2.2
  rcases Sec10XProof.sec10XList hQ hθQ ((QuotientGroup.congr _ _ eQ hc).trans eR) hlist
      (fun hLF => Item1015Proof.false_of_listFacts h45 h97 h hdL hXd hLF hVinv hV1) with
    hlist' | h27
  · exact Item1015Proof.false_of_listFacts h45 h97 h hdL hXd
      (Item1015Proof.listFacts_of_list hlist') hVinv hV1
  · exact Sec10X.not_nonempty_mulEquiv_of_mem_thetaComponentsAt h45 h97 h hdL hXd h27

end Never

end Std

end Sec10XSteps

section Main

open Sec10XSteps


theorem step1011Two_of (h107 : Item107) (h463 : Item463Inv) : Step1011Two := by
  intro h45 h97 G _ _ A c L a R h d hdL _hmax hcomm hnot Y _hY _hUY _hiso hbound
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := sec10U L a with hUdef
  set Θ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) with hΘ
  set P := inSubgroup (CFSG.pCore 2)
    (Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({a} : Set G)) with hP
  set V := ⁅P, Subgroup.zpowers c⁆ with hV
  have hdA := h.d_mem_A hdL
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd3' : d ^ 3 = 1 := h.pow_three hdA
  obtain ⟨⟨hUf, -⟩, -, -⟩ := step1010U_holds h45 G A c L a R h
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := (mem_fourGroups_iff.mp hUf).1
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx h.a_mem)
  have hAK : A ≤ Subgroup.normalizer ((Subgroup.centralizer (U : Set G) ⊓
      Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := fun x hx =>
    SteinbergBY.mem_normalizer_inf (normalizer_le_normalizer_centralizer_of (hAU hx))
      (Subgroup.le_normalizer (hAa hx))
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hAK.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _)
  have hcK : c ∈ Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨Sec10XProof.closure_a_c_le_centralizer_U h (Subgroup.subset_closure (by simp)),
      Subgroup.mem_centralizer_singleton_iff.mpr (h.comm h.mem_A h.a_mem)⟩
  have hcP : c ∈ Subgroup.normalizer (P : Set G) :=
    SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hcK
  have hVP : V ≤ P :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcP)
  have hV2 : IsPGroup 2 V := (SteinbergBY.isPGroup_inSubgroup_pCore 2 _).to_le hVP
  have hVθ : V ≤ Θ := (Subgroup.commutator_mono le_rfl
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))).trans hbound
  have hcA : ∀ x ∈ A, x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (h.comm h.mem_A hx) k).eq)
  have hVA : A ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    mem_normalizer_commutator_of_mem (hAP hx) (hcA x hx)
  obtain ⟨S, hS, hVS, w, -, hwS, -, hwd, hwc⟩ := exists_S_w h107 h97 h hdL hV2 hVθ hVA
  obtain ⟨hSθ, hS2, hSA⟩ := hS.prop
  have hS2' : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS2
  have hSc : S ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    eq_bot_of_le_theta_inf_centralizer h45 h hnot (hS2'.to_le inf_le_left)
      (inf_le_left.trans hSθ) inf_le_right fun x hx =>
        SteinbergBY.mem_normalizer_inf (hSA hx) (Subgroup.le_normalizer
          (Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hx h.mem_A)))
  have hcdA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact h.mem_A
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := by
    refine le_of_inf_centralizer_le (h.pow_three h.mem_A) hd3' (h.comm h.mem_A hdA)
      (Sec10XProof.isElemAbelian_of_le h hcdA) (card_closure_c_d h hdL hd3).ge hS2'
      (hcdA.trans hSA) hwS hwc hwd (fun x hx => ?_) (by rw [hSc]; exact bot_le) inf_le_right
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc w * x * w⁻¹ * d = w * x * w⁻¹ * (w * d * w⁻¹) := by rw [hwd]
      _ = w * (x * d) * w⁻¹ := by group
      _ = w * (d * x) * w⁻¹ := by rw [hx]
      _ = (w * d * w⁻¹) * (w * x * w⁻¹) := by group
      _ = d * (w * x * w⁻¹) := by rw [hwd]
  set B := Subgroup.closure ({a, d} : Set G) with hB
  have hSB : S ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) :=
    (le_inf hSθ hSd).trans (Sec10XProof.theta_inf_centralizer_le a d)
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact h.a_mem
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hdA
  have hS1 : S ≠ ⊥ := fun hb => hcomm (le_bot_iff.mp (hb ▸ hVS))
  obtain ⟨s, hsS, hs1⟩ : ∃ s ∈ S, s ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hS1 ((Subgroup.eq_bot_iff_forall S).mpr hall)
  have hsc : ⁅s, c⁆ ≠ 1 := by
    intro h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    have hmem : s ∈ S ⊓ Subgroup.centralizer ({c} : Set G) :=
      ⟨hsS, Subgroup.mem_centralizer_singleton_iff.mpr h1⟩
    rw [hSc, Subgroup.mem_bot] at hmem
    exact hs1 hmem
  have hSA2 : IsPGroup 2 (⁅S, A⁆ : Subgroup G) :=
    hS2'.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hSA)
  have hSA1 : (⁅S, A⁆ : Subgroup G) ≠ ⊥ := fun hb => hsc (by
    have := Subgroup.commutator_mem_commutator hsS h.mem_A
    rwa [hb, Subgroup.mem_bot] at this)
  have h2 : 2 ∣ Nat.card (⁅S, A⁆ : Subgroup G) := by
    obtain ⟨m, hm⟩ := hSA2.exists_card_eq
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm
      exact hSA1 (Subgroup.eq_bot_of_card_eq _ hm)
    rw [hm]
    exact dvd_pow_self 2 hm0
  refine false_of_even_commutator h45 h97 h463 h hdL hBA
    (Subgroup.subset_closure (by simp)) (Sec10XProof.card_closure_a_d h hdL hd3) ?_
  exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le
    (Subgroup.commutator_mono hSB le_rfl)))

end Main

end CFSG.RankThree.PartTwo.Sec10
