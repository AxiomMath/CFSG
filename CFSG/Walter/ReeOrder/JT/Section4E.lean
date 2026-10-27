module

public import CFSG.Walter.ReeOrder.JT.Section4D
public import CFSG.Walter.ReeOrder.JT.Section4B

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

section IndexTwo

variable {X : Type*} [Group X] {N M : Subgroup X}

theorem mul_mem_iff_of_relIndex_two (hMi : (M.subgroupOf N).index = 2) {a b : X} (ha : a ∈ N)
    (hb : b ∈ N) : a * b ∈ M ↔ (a ∈ M ↔ b ∈ M) := by
  have := Subgroup.mul_mem_iff_of_index_two hMi (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem mem_of_relIndex_two_of_odd [Finite X] (hMi : (M.subgroupOf N).index = 2) {x : X}
    (hxN : x ∈ N) (hx : Odd (orderOf x)) : x ∈ M := by
  have hsq : x * x ∈ M := by
    have := Subgroup.mul_self_mem_of_index_two hMi ⟨x, hxN⟩
    simpa [Subgroup.mem_subgroupOf] using this
  obtain ⟨k, hk⟩ := hx
  have : x = (x * x) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [this]
  exact M.pow_mem hsq _

theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (V : Set X)) {y : X}
    (hy : y ∈ Subgroup.centralizer (V : Set X)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer (V : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro z hz
  have hz' : g⁻¹ * z * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z).mp hz
    simpa using this
  have := hy _ hz'
  calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [this]
    _ = g * y * g⁻¹ * z := by group

end IndexTwo

namespace Config

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (c : Config h)

theorem S_le_normalizer_R
    (hp : h.p ≠ 2) {R : Subgroup G} (hRQ : R ≤ c.Q) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) :=
  c.toSetup.S_le_centralizer_T.trans
    (c.toSetup.centralizer_T_le_normalizer_T.trans (c.normalizer_T_le_normalizer_R hp hRQ))

end Config

structure IndexTwo {X : Type*} [Group X] (N : Subgroup X) where
  M : Subgroup X
  le : M ≤ N
  normal : (M.subgroupOf N).Normal
  index : (M.subgroupOf N).index = 2

namespace IndexTwo

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} {c : Config h} {R : Subgroup G}
  (d : IndexTwo (Subgroup.normalizer (R : Set G)))

theorem Q_le
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) : c.Q ≤ d.M := fun _ hx =>
  mem_of_relIndex_two_of_odd d.index ((c.normalizer_T_le_normalizer_R hp hRQ)
    (c.toSetup.centralizer_T_le_normalizer_T (c.toSetup.Q_le_centralizer_T hx)))
    ((c.toSetup.mem_Q_iff hp).mp hx).2

theorem μ_mem
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) : c.μ ∈ d.M :=
  mem_of_relIndex_two_of_odd d.index (c.normalizer_T_le_normalizer_R hp hRQ c.μ_mem_NT)
    (by rw [c.orderOf_μ]; decide)

omit [Finite G] in
theorem conj_mem {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ d.M) :
    g * x * g⁻¹ ∈ d.M := by
  have := d.normal.conj_mem ⟨x, d.le hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

theorem S_not_le
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) : ¬ (c.S : Subgroup G) ≤ d.M := by
  intro hSM
  have h1 : (d.M.subgroupOf (Subgroup.normalizer (R : Set G))).index ∣
      ((c.S : Subgroup G).subgroupOf (Subgroup.normalizer (R : Set G))).index :=
    Subgroup.index_dvd_of_le (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢; exact hSM hx)
  have h2 : ((c.S : Subgroup G).subgroupOf (Subgroup.normalizer (R : Set G))).index ∣
      (c.S : Subgroup G).index :=
    Subgroup.relIndex_dvd_index_of_le (c.S_le_normalizer_R hp hRQ)
  rw [d.index] at h1
  exact c.S.not_dvd_index (h1.trans h2)

theorem card_S_inf
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) :
    Nat.card ((c.S : Subgroup G) ⊓ d.M : Subgroup G) = 4 := by
  have hSN := c.S_le_normalizer_R hp hRQ
  obtain ⟨s₀, hs₀S, hs₀M⟩ : ∃ s₀ ∈ (c.S : Subgroup G), s₀ ∉ d.M := by
    by_contra hcon
    push Not at hcon
    exact d.S_not_le hp hRQ hcon
  have h2 := card_eq_two_mul_of_xor (H := (c.S : Subgroup G) ⊓ d.M) (K := c.S) inf_le_left
    hs₀S fun b hb => by
      have := mul_mem_iff_of_relIndex_two d.index (hSN hb) (hSN hs₀S)
      constructor
      · intro hbs hbM
        exact hs₀M (this.mp hbs.2 |>.mp hbM.2)
      · intro hbM
        refine ⟨(c.S : Subgroup G).mul_mem hb hs₀S, this.mpr ⟨fun h1 => absurd ⟨hb, h1⟩ hbM,
          fun h1 => absurd h1 hs₀M⟩⟩
  rw [h.card_sylow hp c.S c.t_mem_S] at h2
  omega

theorem isKleinFour_S_inf
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) :
    IsKleinFour ((c.S : Subgroup G) ⊓ d.M : Subgroup G) := by
  refine ⟨d.card_S_inf hp hRQ, ?_⟩
  have hdvd : Monoid.exponent ((c.S : Subgroup G) ⊓ d.M : Subgroup G) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact h.mul_self_of_mem_sylow hp c.S c.t_mem_S x.2.1)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have : Subsingleton ((c.S : Subgroup G) ⊓ d.M : Subgroup G) := Monoid.exp_eq_one_iff.mp h1
    have := Nat.card_unique (α := ((c.S : Subgroup G) ⊓ d.M : Subgroup G))
    have := d.card_S_inf hp hRQ
    omega
  · exact h1

theorem card_eq
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) : ∃ k, Odd k ∧ Nat.card d.M = 4 * k := by
  have hSN := c.S_le_normalizer_R hp hRQ
  have h1 := Subgroup.relIndex_mul_card (c.S : Subgroup G) (Subgroup.normalizer (R : Set G))
  rw [inf_eq_left.mpr hSN, h.card_sylow hp c.S c.t_mem_S] at h1
  have hodd : Odd ((c.S : Subgroup G).relIndex (Subgroup.normalizer (R : Set G))) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2 => c.S.not_dvd_index (h2.trans (Subgroup.relIndex_dvd_index_of_le hSN))
  have h2 := (d.M.subgroupOf (Subgroup.normalizer (R : Set G))).card_mul_index
  rw [d.index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.le).toEquiv] at h2
  refine ⟨_, hodd, ?_⟩
  omega

@[expose] noncomputable def sylow
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) : Sylow 2 d.M :=
  Sylow.ofCard (((c.S : Subgroup G) ⊓ d.M).subgroupOf d.M) (by
    obtain ⟨k, hk, hMk⟩ := d.card_eq hp hRQ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, d.card_S_inf hp hRQ,
      hMk, show 4 = 2 ^ 2 by norm_num, Nat.factorization_mul (by norm_num) (by
        rintro rfl; exact absurd hk (by decide)), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hk)
        (even_iff_two_dvd.mpr h2))]
    simp)

theorem coe_sylow
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) :
    ((d.sylow hp hRQ : Sylow 2 d.M) : Subgroup d.M) =
      ((c.S : Subgroup G) ⊓ d.M).subgroupOf d.M := rfl

theorem exists_mem_normalizer_not_centralizer
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) :
    ∃ m ∈ d.M, m ∈ Subgroup.normalizer ((((c.S : Subgroup G) ⊓ d.M : Subgroup G)) : Set G) ∧
      m ∉ Subgroup.centralizer ((((c.S : Subgroup G) ⊓ d.M : Subgroup G)) : Set G) := by
  classical
  by_contra hcon
  push Not at hcon
  set V := ((c.S : Subgroup G) ⊓ d.M : Subgroup G)
  set V' := d.sylow hp hRQ
  have hV'V : ∀ y : d.M, y ∈ (V' : Subgroup d.M) ↔ (y : G) ∈ V := fun y => by
    rw [d.coe_sylow hp hRQ, Subgroup.mem_subgroupOf]
  have hNC : Subgroup.normalizer ((V' : Subgroup d.M) : Set d.M) ≤
      Subgroup.centralizer ((V' : Subgroup d.M) : Set d.M) := by
    intro n hn
    have hnN : (n : G) ∈ Subgroup.normalizer (V : Set G) := by
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      have := (Subgroup.mem_normalizer_iff.mp hn ⟨v, hv.2⟩).mp ((hV'V _).mpr hv)
      rw [hV'V] at this
      exact this
    have hnC := hcon n n.2 hnN
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hnC) y ((hV'V y).mp hy)
  have hcomp := MonoidHom.ker_transferSylow_isComplement' V' hNC
  have hKn : (MonoidHom.transferSylow V' hNC).ker.Normal := MonoidHom.normal_ker _
  generalize (MonoidHom.transferSylow V' hNC).ker = K at hcomp hKn
  obtain ⟨k, hk, hMk⟩ := d.card_eq hp hRQ
  have hKcard : Nat.card K = k := by
    have := hcomp.card_mul_card
    rw [d.coe_sylow hp hRQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      d.card_S_inf hp hRQ, hMk] at this
    omega
  have hKall : ∀ x : d.M, Odd (orderOf x) → x ∈ K := by
    intro x hx
    have hidx : K.index = 4 := by
      have := K.card_mul_index
      rw [hKcard, hMk] at this
      have hk0 : 0 < k := hk.pos
      exact Nat.eq_of_mul_eq_mul_left hk0 (by rw [this]; ring)
    have h1 : orderOf (QuotientGroup.mk x : d.M ⧸ K) ∣ 4 := by
      rw [← hidx, Subgroup.index]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk x : d.M ⧸ K) ∣ orderOf x :=
      orderOf_map_dvd (QuotientGroup.mk' K) x
    have h3 : orderOf (QuotientGroup.mk x : d.M ⧸ K) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hx))) h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hKodd : ∀ x ∈ K, Odd (orderOf x) := fun x hx => Odd.of_dvd_nat (hKcard ▸ hk)
    (Subgroup.orderOf_dvd_natCard K hx)
  have hSN := c.S_le_normalizer_R hp hRQ
  have hμM := d.μ_mem hp hRQ
  have hμT : ∀ x ∈ c.T, c.μ * x * c.μ⁻¹ = x := by
    intro x hxT
    have hxN : x ∈ Subgroup.normalizer (R : Set G) := hSN (c.le_S hxT)
    set z := x * c.μ * x⁻¹ * c.μ⁻¹
    have hzM : x * c.μ * x⁻¹ ∈ d.M := d.conj_mem hxN hμM
    have hzK : (⟨z, d.M.mul_mem hzM (d.M.inv_mem hμM)⟩ : d.M) ∈ K := by
      have h1 : (⟨x * c.μ * x⁻¹, hzM⟩ : d.M) ∈ K := hKall _ (by
        rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, c.orderOf_μ]; decide)
      have h2 : (⟨c.μ, hμM⟩ : d.M) ∈ K := hKall _ (by
        rw [Subgroup.orderOf_mk, c.orderOf_μ]; decide)
      have heq : (⟨z, d.M.mul_mem hzM (d.M.inv_mem hμM)⟩ : d.M) =
          ⟨x * c.μ * x⁻¹, hzM⟩ * (⟨c.μ, hμM⟩ : d.M)⁻¹ := Subtype.ext rfl
      rw [heq]
      exact K.mul_mem h1 (K.inv_mem h2)
    have hzT : z ∈ c.T := by
      have : c.μ * x⁻¹ * c.μ⁻¹ ∈ c.T :=
        (Subgroup.mem_normalizer_iff.mp c.μ_mem_NT _).mp (c.T.inv_mem hxT)
      have h3 : z = x * (c.μ * x⁻¹ * c.μ⁻¹) := by simp only [z]; group
      rw [h3]
      exact c.T.mul_mem hxT this
    have hz1 : z = 1 := by
      have ho := hKodd _ hzK
      rw [Subgroup.orderOf_mk] at ho
      have h4 : orderOf z ∣ 4 := c.four.card_four ▸ Subgroup.orderOf_dvd_natCard c.T hzT
      have : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h4 (by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr ho))) (dvd_refl _)
      exact orderOf_eq_one_iff.mp this
    have : x * c.μ * x⁻¹ = c.μ := by
      have := mul_inv_eq_one.mp hz1
      exact this
    have hxμ : x * c.μ = c.μ * x := by
      calc x * c.μ = (x * c.μ * x⁻¹) * x := by group
        _ = c.μ * x := by rw [this]
    calc c.μ * x * c.μ⁻¹ = x * c.μ * c.μ⁻¹ := by rw [hxμ]
      _ = x := by group
  have : Nontrivial c.T := by
    rw [← Finite.one_lt_card_iff_nontrivial, c.four.card_four]; norm_num
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : c.T)
  exact hx1 (Subtype.ext (c.μ_fpf x hx (hμT x hx)))

theorem pow_three_mem_centralizer
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) {m : G} (hmM : m ∈ d.M)
    (hmN : m ∈ Subgroup.normalizer ((((c.S : Subgroup G) ⊓ d.M : Subgroup G)) : Set G))
    (hmC : m ∉ Subgroup.centralizer ((((c.S : Subgroup G) ⊓ d.M : Subgroup G)) : Set G)) :
    m ^ 3 ∈ Subgroup.centralizer ((((c.S : Subgroup G) ⊓ d.M : Subgroup G)) : Set G) := by
  set V := ((c.S : Subgroup G) ⊓ d.M : Subgroup G)
  have hV := d.isKleinFour_S_inf hp hRQ
  set A := d.M ⊓ Subgroup.centralizer (V : Set G)
  set B := d.M ⊓ Subgroup.normalizer (V : Set G)
  have hAB : A ≤ B := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hVA : V ≤ A := le_inf inf_le_right fun x hx => Subgroup.mem_centralizer_iff.mpr
    fun y hy => congrArg Subtype.val (hV.isMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hVB : V ≤ B := hVA.trans hAB
  have h6 : A.relIndex B ∣ 6 := relIndex_inf_centralizer_dvd_six hV d.M
  have hodd : ¬ 2 ∣ A.relIndex B := by
    intro h2
    obtain ⟨k, hk, hMk⟩ := d.card_eq hp hRQ
    have h1 := Subgroup.relIndex_dvd_of_le_left B hVA
    have h3 := Subgroup.relIndex_mul_card V B
    rw [inf_eq_left.mpr hVB, hV.card_four] at h3
    have h4 : Nat.card B ∣ 4 * k := hMk ▸ Subgroup.card_dvd_of_le inf_le_left
    have h5 : V.relIndex B ∣ k := by
      rw [← h3, mul_comm 4 k] at h4
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 4) h4
    exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr ((h2.trans h1).trans h5))
  have hne1 : A.relIndex B ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun hle => hmC (hle ⟨hmM, hmN⟩).2
  have h3 : A.relIndex B = 3 := by
    have hle := Nat.le_of_dvd (by norm_num) h6
    interval_cases hk : A.relIndex B <;> simp_all
  have hnorm : (A.subgroupOf B).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨d.M.mul_mem (d.M.mul_mem g.2.1 hx.1) (d.M.inv_mem g.2.1),
      conj_mem_centralizer_of_mem_normalizer g.2.2 hx.2⟩
  have := Subgroup.pow_index_mem (A.subgroupOf B) (⟨m, hmM, hmN⟩ : B)
  rw [← Subgroup.relIndex, h3, Subgroup.mem_subgroupOf] at this
  exact this.2

theorem exists_conj_mem_S_inf
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) {x : G} (hxM : x ∈ d.M)
    (hx2 : orderOf x = 2) : ∃ g ∈ d.M, g * x * g⁻¹ ∈ (c.S : Subgroup G) ⊓ d.M := by
  have hx2' : IsPGroup 2 (Subgroup.zpowers (⟨x, hxM⟩ : d.M)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx2, pow_one])
  obtain ⟨P, hP⟩ := hx2'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq d.M P (d.sylow hp hRQ)
  refine ⟨g, g.2, ?_⟩
  have hmem : g * ⟨x, hxM⟩ * g⁻¹ ∈ ((d.sylow hp hRQ : Sylow 2 d.M) : Subgroup d.M) := by
    rw [← hg]
    change g * ⟨x, hxM⟩ * g⁻¹ ∈ MulAut.conj g • (P : Subgroup d.M)
    exact ⟨⟨x, hxM⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  rw [d.coe_sylow hp hRQ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem exists_conj_of_orderOf_eq_two
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) {x y : G}
    (hxM : x ∈ d.M) (hyM : y ∈ d.M) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∃ g ∈ d.M, g * x * g⁻¹ = y := by
  set V := ((c.S : Subgroup G) ⊓ d.M : Subgroup G)
  have hV := d.isKleinFour_S_inf hp hRQ
  obtain ⟨g₁, hg₁M, hg₁⟩ := d.exists_conj_mem_S_inf hp hRQ hxM hx2
  obtain ⟨g₂, hg₂M, hg₂⟩ := d.exists_conj_mem_S_inf hp hRQ hyM hy2
  obtain ⟨m, hmM, hmN, hmC⟩ := d.exists_mem_normalizer_not_centralizer hp hRQ
  have hm3 := d.pow_three_mem_centralizer hp hRQ hmM hmN hmC
  have hne : ∀ z : G, orderOf z = 2 → ∀ g : G, g * z * g⁻¹ ≠ 1 := by
    intro z hz g h1
    have : z = 1 := by
      have := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hz
    omega
  obtain ⟨k, hk⟩ := exists_pow_conj_of_pow_three_mem hV hmN hm3 hmC hg₁ (hne x hx2 g₁) hg₂
    (hne y hy2 g₂)
  refine ⟨g₂⁻¹ * m ^ k * g₁, d.M.mul_mem (d.M.mul_mem (d.M.inv_mem hg₂M) (d.M.pow_mem hmM k))
    hg₁M, ?_⟩
  have := congrArg (fun w => g₂⁻¹ * w * g₂) hk
  rw [show g₂⁻¹ * m ^ k * g₁ * x * (g₂⁻¹ * m ^ k * g₁)⁻¹ =
    g₂⁻¹ * (m ^ k * (g₁ * x * g₁⁻¹) * (m ^ k)⁻¹) * g₂ by group, this]
  group

theorem S_inf_eq_T
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) (hR : R ≠ ⊥) :
    (c.S : Subgroup G) ⊓ d.M = c.T := by
  classical
  set V := ((c.S : Subgroup G) ⊓ d.M : Subgroup G)
  have hV := d.isKleinFour_S_inf hp hRQ
  have hab := h.abelian_sylow c.S
  obtain ⟨u, ⟨huV, huT⟩, hu1⟩ : ∃ u ∈ V ⊓ c.T, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    let φ : V × c.T → (c.S : Subgroup G) := fun p =>
      ⟨(p.1 : G) * p.2, (c.S : Subgroup G).mul_mem p.1.2.1 (c.le_S p.2.2)⟩
    have hφ : Function.Injective φ := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab'
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab'
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a = 1 := hcon _ ⟨V.mul_mem (V.inv_mem a'.2) a.2,
        h2 ▸ c.T.mul_mem b'.2 (c.T.inv_mem b.2)⟩
      have ha : (a : G) = a' := by
        calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
          _ = a' := by rw [h3, mul_one]
      have hb : (b : G) = b' := by
        calc (b : G) = (a : G)⁻¹ * (a * b) := by group
          _ = (a : G)⁻¹ * (a' * b') := by rw [h1]
          _ = b' := by rw [ha]; group
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    have := Nat.card_le_card_of_injective φ hφ
    rw [Nat.card_prod, hV.card_four, c.four.card_four, h.card_sylow hp c.S c.t_mem_S] at this
    omega
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (by rw [pow_two]; exact mul_self_of_isKleinFour' hV huV) hu1
  have hVR : V ≤ (c.S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G) := by
    intro v hv
    refine ⟨hv.1, ?_⟩
    show v ∈ Subgroup.centralizer (R : Set G)
    by_cases hv1 : v = 1
    · rw [hv1]; exact Subgroup.one_mem _
    have hv2 : orderOf v = 2 := orderOf_eq_prime
      (by rw [pow_two]; exact mul_self_of_isKleinFour' hV hv) hv1
    obtain ⟨g, hgM, hg⟩ := d.exists_conj_of_orderOf_eq_two hp hRQ huV.2 hv.2 hu2 hv2
    rw [← hg, Subgroup.mem_centralizer_iff]
    intro x hx
    have hgN := d.le hgM
    have hx' : g⁻¹ * x * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx
      simpa using this
    have huR : u ∈ Subgroup.centralizer (R : Set G) :=
      Subgroup.centralizer_le hRQ (c.toSetup.T_le_centralizer_Q huT)
    have := (Subgroup.mem_centralizer_iff.mp huR) _ hx'
    calc x * (g * u * g⁻¹) = g * ((g⁻¹ * x * g) * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * u * g⁻¹ * x := by group
  rw [c.S_inf_centralizer_R hp hRQ hR] at hVR
  exact Subgroup.eq_of_le_of_card_ge hVR (by rw [hV.card_four, c.four.card_four])

theorem centralizer_t_inf_normalizer_R
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) (hR : R ≠ ⊥) :
    Subgroup.centralizer ({h.t} : Set G) ⊓ Subgroup.normalizer (R : Set G) =
      Subgroup.centralizer (c.T : Set G) := by
  set dd := c.toSetup.data hp
  have hRv : R ≤ Subgroup.centralizer ({dd.v} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q dd.v_mem_T)) x
        (hRQ hx))
  have hRodd : Odd (Nat.card R) :=
    Odd.of_dvd_nat (c.toSetup.odd_card_Q hp) (Subgroup.card_dvd_of_le hRQ)
  have hN := (h.facts hp).inf_normalizer_eq dd.v_mem_F dd.orderOf_v
    (hRQ.trans (c.toSetup.Q_le_F hp)) hRv hR hRodd
  apply le_antisymm
  · rintro x ⟨hxt, hxR⟩
    rw [dd.centralizer_T]
    refine ⟨hxt, ?_⟩
    show x ∈ Subgroup.centralizer ({dd.v} : Set G)
    have htR : h.t ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hRQ
        (c.toSetup.T_le_centralizer_Q c.t_mem_T))
    have htv := (h.commute_of_mem_F dd.v_mem_F)
    rcases h.mem_centralizer_t.mp hxt with hxF | hxF
    · have : x ∈ h.F ⊓ Subgroup.normalizer (R : Set G) := ⟨hxF, hxR⟩
      rw [hN] at this
      exact this.2
    · have : h.t * x ∈ h.F ⊓ Subgroup.normalizer (R : Set G) :=
        ⟨hxF, Subgroup.mul_mem _ htR hxR⟩
      rw [hN] at this
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp this.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : x = h.t * (h.t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [this, mul_assoc, h1, ← mul_assoc, ← htv, mul_assoc]
  · intro x hx
    refine ⟨?_, (c.normalizer_T_le_normalizer_R hp hRQ)
      (c.toSetup.centralizer_T_le_normalizer_T hx)⟩
    rw [dd.centralizer_T] at hx
    exact hx.1

theorem centralizer_t_inf_M
    (hp : h.p ≠ 2) (hRQ : R ≤ c.Q) (hR : R ≠ ⊥) :
    Subgroup.centralizer ({h.t} : Set G) ⊓ d.M = c.T ⊔ c.Q := by
  have hTM : c.T ≤ d.M := by
    rw [← d.S_inf_eq_T hp hRQ hR]; exact inf_le_right
  have hQM := d.Q_le hp hRQ
  have hSQ : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.S_le_centralizer_T.trans (c.toSetup.centralizer_T_le_normalizer_T.trans
      (c.toSetup.normalizer_T_le_normalizer_Q hp))
  apply le_antisymm
  · rintro x ⟨hxt, hxM⟩
    have hxC : x ∈ Subgroup.centralizer (c.T : Set G) := by
      rw [← centralizer_t_inf_normalizer_R (c := c) hp hRQ hR]
      exact ⟨hxt, d.le hxM⟩
    rw [c.toSetup.centralizer_T_eq hp, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSQ] at hxC
    obtain ⟨a, ha, b, hb, rfl⟩ := hxC
    have haM : a ∈ d.M := by
      have : a = (a * b) * b⁻¹ := by group
      rw [this]
      exact d.M.mul_mem hxM (d.M.inv_mem (hQM hb))
    have haT : a ∈ c.T := by
      rw [← d.S_inf_eq_T hp hRQ hR]
      exact ⟨ha, haM⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haT) (Subgroup.mem_sup_right hb)
  · refine sup_le (le_inf ?_ hTM) (le_inf ((c.toSetup.Q_le_F hp).trans h.le_centralizer) hQM)
    exact (c.le_S).trans (h.sylow_le_centralizer c.S c.t_mem_S)

theorem T_sup_Q_le_centralizer
    (hp : h.p ≠ 2) {x y : G} (hx : x ∈ c.T ⊔ c.Q)
    (hy : y ∈ c.T ⊔ c.Q) : x * y = y * x := by
  have hTab := c.four.isMulCommutative
  have hQab : IsMulCommutative c.Q := by
    have := c.toSetup.isCyclic_Q hp
    exact ⟨⟨fun a b => (IsCyclic.commGroup (α := c.Q)).mul_comm a b⟩⟩
  have hTC : c.T ≤ Subgroup.centralizer (c.T : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hTab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hQC : c.Q ≤ Subgroup.centralizer (c.Q : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hQab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have h1 : c.T ⊔ c.Q ≤ Subgroup.centralizer (c.T : Set G) ⊓
      Subgroup.centralizer (c.Q : Set G) :=
    sup_le (le_inf hTC c.toSetup.T_le_centralizer_Q)
      (le_inf c.toSetup.Q_le_centralizer_T hQC)
  have hx' := h1 hx
  have h2 : c.T ⊔ c.Q ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx'.1) z hz))
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hx'.2) z hz))
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hy)).symm

end IndexTwo

end CFSG.Walter.JT
