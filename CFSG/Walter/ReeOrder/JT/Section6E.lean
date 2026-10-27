module

public import CFSG.Walter.ReeOrder.JT.Section6D

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem commutator_mem_of_fpf {P R : Subgroup X} (hRP : R ≤ P)
    (hRn : ∀ x ∈ P, x ∈ Subgroup.normalizer (R : Set X)) (hRodd : Odd (Nat.card R)) {u : X}
    (hu : u * u = 1) (huP : u ∈ Subgroup.normalizer (P : Set X))
    (huR : u ∈ Subgroup.normalizer (R : Set X)) (hfix : ∀ x ∈ P, x * u = u * x → x ∈ R) :
    ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ R := by
  classical
  set R' := R.subgroupOf P with hR'def
  have hR'n : R'.Normal := ⟨fun n hn g => by
    rw [hR'def, Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hRn g g.2) n).mp hn
    simpa using this⟩
  let φ : P →* P :=
    { toFun := fun x => ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huP x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφR : R' ≤ R'.comap φ := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [hR'def, Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp huR x).mp hx
  set φ' := QuotientGroup.map R' R' φ hφR with hφ'def
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hfpf : MonoidHom.FixedPointFree φ' := by
    intro a ha
    induction a using QuotientGroup.induction_on with
    | H x =>
    rw [hφ'def, QuotientGroup.map_mk] at ha
    have h1 : (φ x)⁻¹ * x ∈ R' := QuotientGroup.eq.mp ha
    rw [hR'def, Subgroup.mem_subgroupOf] at h1
    have h2 : (x : X)⁻¹ * u * x * u⁻¹ ∈ R := by
      have := R.inv_mem h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev] at this
      have hφx : ((φ x : P) : X) = u * x * u⁻¹ := rfl
      rw [hφx] at this
      simpa [mul_assoc] using this
    obtain ⟨n, hnR, hn⟩ := exists_mem_centralizer_coset hRodd hu huR h2
    have hxn : (x : X) * n⁻¹ ∈ R := hfix _ (P.mul_mem x.2 (P.inv_mem (hRP hnR))) hn
    have hx : (x : X) ∈ R := by
      have := R.mul_mem hxn hnR
      simpa using this
    rw [QuotientGroup.eq_one_iff, hR'def, Subgroup.mem_subgroupOf]
    exact hx
  have hinvol : Function.Involutive φ' := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
    rw [hφ'def, QuotientGroup.map_mk, QuotientGroup.map_mk]
    congr 1
    apply Subtype.ext
    change u * (u * (x : X) * u⁻¹) * u⁻¹ = x
    rw [huinv]
    calc u * (u * (x : X) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu]; group
  have hcomm := MonoidHom.FixedPointFree.commute_all_of_involutive hfpf hinvol
  intro x hx y hy
  have h1 := (hcomm (QuotientGroup.mk ⟨y⁻¹, P.inv_mem hy⟩)
    (QuotientGroup.mk ⟨x⁻¹, P.inv_mem hx⟩)).eq
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hR'def,
    Subgroup.mem_subgroupOf] at h1
  simpa [mul_assoc] using h1

omit [Finite X] in
theorem mem_normalizer_sup {A B : Subgroup X} {u : X}
    (hA : u ∈ Subgroup.normalizer (A : Set X)) (hB : u ∈ Subgroup.normalizer (B : Set X)) :
    u ∈ Subgroup.normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

end General

namespace BorelData

variable {h : JTHyp G} (b : BorelData h)

theorem comm_of_mem {u v : G} (hu : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ)
    (hv : v = h.t ∨ v = b.τ ∨ v = h.t * b.τ) : u * v = v * u := by
  have hc : Commute h.t b.τ := b.τ_comm_t.symm
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · rfl
  · exact hc.eq
  · exact ((Commute.refl h.t).mul_right hc).eq
  · exact hc.symm.eq
  · rfl
  · exact (hc.symm.mul_right (Commute.refl b.τ)).eq
  · exact ((Commute.refl h.t).mul_left hc.symm).eq
  · exact (hc.mul_left (Commute.refl b.τ)).eq
  · rfl

structure M1Data where
  P : Subgroup G
  R_le : b.R ≤ P
  le_normalizer : P ≤ Subgroup.normalizer (b.R : Set G)
  isPGroup : IsPGroup h.p P
  normal : ∀ g ∈ Subgroup.normalizer (b.R : Set G), g ∈ Subgroup.normalizer (P : Set G)
  mem : ∀ y ∈ Subgroup.normalizer (b.R : Set G), ∀ n : ℕ, y ^ h.p ^ n = 1 → y ∈ P
  card : Nat.card P = h.q ^ 3

theorem t_mem_normalizer_R : h.t ∈ Subgroup.normalizer (b.R : Set G) :=
  Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun _ hx => (b.R_comm_t hx))

theorem τ_mem_normalizer_R : b.τ ∈ Subgroup.normalizer (b.R : Set G) :=
  mem_normalizer_of_conj_mem fun x hx => by rw [b.τ_inv x hx]; exact Subgroup.inv_mem _ hx

theorem isPGroup_R : IsPGroup h.p b.R := IsPGroup.of_card (by rw [b.card_R, JTHyp.q_eq])

theorem nonempty_m1Data
    (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) (hp3 : h.p ≠ 3)
    (h51 : h.q ^ 3 ∣ Nat.card G) : Nonempty b.M1Data := by
  obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := b.exists_M₁ hp hq5 hp3 h51
  exact ⟨⟨P, h1, h2, h3, h4, h5, h6⟩⟩

namespace M1Data

variable {b} (d : b.M1Data)

theorem t_mem : h.t ∈ Subgroup.normalizer (d.P : Set G) := d.normal _ b.t_mem_normalizer_R

theorem τ_mem : b.τ ∈ Subgroup.normalizer (d.P : Set G) := d.normal _ b.τ_mem_normalizer_R

theorem C_le : b.C ≤ Subgroup.normalizer (d.P : Set G) := fun _ hx =>
  d.normal _ (b.C_le_normalizer hx)

theorem mem_normalizer_inf {u v : G} (hu : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ)
    (hv : v = h.t ∨ v = b.τ ∨ v = h.t * b.τ) :
    u ∈ Subgroup.normalizer ((d.P ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) :
      Set G) := by
  have huP : u ∈ Subgroup.normalizer (d.P : Set G) := by
    rcases hu with rfl | rfl | rfl
    · exact d.t_mem
    · exact d.τ_mem
    · exact Subgroup.mul_mem _ d.t_mem d.τ_mem
  exact BorelData.mem_normalizer_inf huP (b.comm_of_mem hu hv)

variable (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) (hp3 : h.p ≠ 3)
include hp hq5 hp3

theorem card_inf
    {u : G} (hu : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ) :
    Nat.card (d.P ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = h.q := by
  have hprod := b.card_eq_prod hp hq5 d.isPGroup d.t_mem d.τ_mem
  rw [d.card] at hprod
  have hq2 : 2 ≤ h.q := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  have hle : ∀ {v : G}, (v = h.t ∨ v = b.τ ∨ v = h.t * b.τ) →
      Nat.card (d.P ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) = 1 ∨
        Nat.card (d.P ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) = h.q :=
    fun hv => b.card_inf_eq hp hq5 hp3 d.isPGroup d.C_le hv
  have hq3 : h.q ^ 3 = h.q * h.q * h.q := by ring
  rcases hle (Or.inl rfl) with h1 | h1 <;> rcases hle (Or.inr (Or.inl rfl)) with h2 | h2 <;>
    rcases hle (Or.inr (Or.inr rfl)) with h3 | h3 <;> rw [h1, h2, h3, hq3] at hprod <;>
    rcases hu with rfl | rfl | rfl <;> first | assumption | (exfalso; nlinarith)

theorem inf_t :
    d.P ⊓ Subgroup.centralizer ({h.t} : Set G) = b.R := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ⟨d.R_le hx,
    Subgroup.mem_centralizer_singleton_iff.mpr (b.R_comm_t hx)⟩) ?_
  rw [d.card_inf hp hq5 hp3 (Or.inl rfl), b.card_R]

omit hp3 in
theorem inf_T
    {x : G} (hx : x ∈ d.P) (h1 : x * h.t = h.t * x) (h2 : x * b.τ = b.τ * x) :
    x = 1 := by
  obtain ⟨n, hn⟩ := d.isPGroup ⟨x, hx⟩
  have hxn : x ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxC : x ∈ b.C := b.mem_C_of_commute hp hq5 h1 h2
    (Odd.of_dvd_nat ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow (orderOf_dvd_of_pow_eq_one hxn))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left n b.coprime_card_C.symm) (orderOf_dvd_of_pow_eq_one hxn)
    (Subgroup.orderOf_dvd_natCard _ hxC))

theorem commute_R
    {u : G} (hu : u = b.τ ∨ u = h.t * b.τ) :
    ∀ x ∈ b.R, ∀ y ∈ d.P ⊓ Subgroup.centralizer ({u} : Set G), x * y = y * x := by
  have hu' : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ := Or.inr hu
  set Ru := d.P ⊓ Subgroup.centralizer ({u} : Set G) with hRudef
  have hRuR : Ru ≤ Subgroup.normalizer (b.R : Set G) := inf_le_left.trans d.le_normalizer
  have hRup : IsPGroup h.p Ru := d.isPGroup.to_le inf_le_left
  have hdisj : Disjoint Ru b.R := by
    rw [Subgroup.disjoint_def]
    intro x hxu hxR
    refine d.inf_T hp hq5 (d.R_le hxR) (b.R_comm_t hxR) ?_
    have hxu' := Subgroup.mem_centralizer_singleton_iff.mp hxu.2
    rcases hu with rfl | rfl
    · exact hxu'
    · have hxt := b.R_comm_t hxR
      have e : b.τ = h.t⁻¹ * (h.t * b.τ) := by group
      rw [e]
      exact ((Commute.inv_right (hxt : Commute x h.t)).mul_right
        (hxu' : Commute x (h.t * b.τ))).eq
  set W := Ru ⊔ b.R with hWdef
  have hWcard : Nat.card W = h.q * h.q := by
    rw [hWdef, card_sup_eq_mul_of_disjoint hRuR hdisj, d.card_inf hp hq5 hp3 hu', b.card_R]
  have hWp : IsPGroup h.p W := hRup.to_sup_of_normal_right' b.isPGroup_R hRuR
  have hWP : W ≤ d.P := sup_le inf_le_left d.R_le
  have hTW : ∀ {v : G}, (v = h.t ∨ v = b.τ ∨ v = h.t * b.τ) →
      v ∈ Subgroup.normalizer (W : Set G) := by
    intro v hv
    have h1 : v ∈ Subgroup.normalizer (Ru : Set G) := d.mem_normalizer_inf hv hu'
    have h2 : v ∈ Subgroup.normalizer (b.R : Set G) := by
      rcases hv with rfl | rfl | rfl
      · exact b.t_mem_normalizer_R
      · exact b.τ_mem_normalizer_R
      · exact Subgroup.mul_mem _ b.t_mem_normalizer_R b.τ_mem_normalizer_R
    exact mem_normalizer_sup h1 h2
  have hWt : W ⊓ Subgroup.centralizer ({h.t} : Set G) = b.R := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ⟨Subgroup.mem_sup_right hx,
      Subgroup.mem_centralizer_singleton_iff.mpr (b.R_comm_t hx)⟩)
    rw [← d.inf_t hp hq5 hp3]
    exact ⟨hWP hx.1, hx.2⟩
  have hWu : W ⊓ Subgroup.centralizer ({u} : Set G) = Ru :=
    le_antisymm (fun x hx => ⟨hWP hx.1, hx.2⟩) (fun x hx => ⟨Subgroup.mem_sup_left hx, hx.2⟩)
  have hprod := b.card_eq_prod hp hq5 hWp (hTW (Or.inl rfl)) (hTW (Or.inr (Or.inl rfl)))
  rw [hWcard, hWt, b.card_R] at hprod
  have hq0 : 0 < h.q := by rw [JTHyp.q_eq]; exact pow_pos (Fact.out : h.p.Prime).pos _
  obtain ⟨w, hw, hw1⟩ : ∃ w : G, (w = b.τ ∨ w = h.t * b.τ) ∧
      W ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
    rcases hu with rfl | rfl
    · rw [hWu, d.card_inf hp hq5 hp3 hu'] at hprod
      refine ⟨h.t * b.τ, Or.inr rfl, ?_⟩
      rw [← Subgroup.card_eq_one]
      have : h.q * h.q * 1 = h.q * h.q * Nat.card (W ⊓ Subgroup.centralizer
          ({h.t * b.τ} : Set G) : Subgroup G) := by rw [mul_one]; exact hprod
      exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq0 hq0) this).symm
    · rw [hWu, d.card_inf hp hq5 hp3 hu'] at hprod
      refine ⟨b.τ, Or.inl rfl, ?_⟩
      rw [← Subgroup.card_eq_one]
      have : h.q * h.q * 1 = h.q * h.q * Nat.card (W ⊓ Subgroup.centralizer
          ({b.τ} : Set G) : Subgroup G) := by
        calc h.q * h.q * 1 = h.q * h.q := mul_one _
          _ = h.q * Nat.card (W ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) * h.q :=
            hprod
          _ = h.q * h.q * Nat.card (W ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) := by
            ring
      exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq0 hq0) this).symm
  have hww : w * w = 1 := by
    have := b.orderOf_eq_two (Or.inr hw)
    rw [← pow_two, ← this, pow_orderOf_eq_one]
  have hfix : ∀ x ∈ W, w * x * w⁻¹ = x → x = 1 := by
    intro x hx hwx
    have hxw : x ∈ W ⊓ Subgroup.centralizer ({w} : Set G) := ⟨hx,
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc x * w = w * x * w⁻¹ * w := by rw [hwx]
          _ = w * x := by group)⟩
    rw [hw1] at hxw
    exact Subgroup.mem_bot.mp hxw
  have hWc := commute_of_fpf_involution hww (hTW (Or.inr hw)) hfix
  intro x hx y hy
  exact hWc x (Subgroup.mem_sup_right hx) y (Subgroup.mem_sup_left hy)

theorem eq_of_le
    {W : Subgroup G} (hWP : W ≤ d.P) (htW : h.t ∈ Subgroup.normalizer (W : Set G))
    (hτW : b.τ ∈ Subgroup.normalizer (W : Set G)) (hRW : b.R ≤ W)
    (h2 : d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) ≤ W)
    (h3 : d.P ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) ≤ W) : W = d.P := by
  have hWp : IsPGroup h.p W := d.isPGroup.to_le hWP
  have hprod := b.card_eq_prod hp hq5 hWp htW hτW
  refine Subgroup.eq_of_le_of_card_ge hWP ?_
  have k1 : Nat.card b.R ≤ Nat.card (W ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le fun x hx => ⟨hRW hx,
      Subgroup.mem_centralizer_singleton_iff.mpr (b.R_comm_t hx)⟩
  have k2 : Nat.card (d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ Subgroup.centralizer ({b.τ} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le fun x hx => ⟨h2 hx, hx.2⟩
  have k3 : Nat.card (d.P ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) ≤
      Nat.card (W ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le fun x hx => ⟨h3 hx, hx.2⟩
  rw [b.card_R] at k1
  rw [d.card_inf hp hq5 hp3 (Or.inr (Or.inl rfl))] at k2
  rw [d.card_inf hp hq5 hp3 (Or.inr (Or.inr rfl))] at k3
  rw [hprod, d.card, pow_three, ← mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul k1 k2) k3

theorem R_le_center
    {x : G} (hx : x ∈ b.R) {y : G} (hy : y ∈ d.P) :
    x * y = y * x := by
  have hRc : ∀ a ∈ b.R, ∀ c ∈ b.R, a * c = c * a := by
    have := (psl2UnipotentFacts h.F h.iso hp h.f_pos).abelian b.R b.R_le_F
      (by rw [b.card_R, JTHyp.q_eq])
    intro a ha c hc
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  set W := Subgroup.centralizer ({x} : Set G) ⊓ d.P with hWdef
  have hRW : b.R ≤ W := fun z hz => ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (hRc z hz x hx), d.R_le hz⟩
  have hW2 : d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) ≤ W := fun z hz =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (d.commute_R hp hq5 hp3 (Or.inl rfl) x hx z
      hz).symm, hz.1⟩
  have hW3 : d.P ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) ≤ W := fun z hz =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (d.commute_R hp hq5 hp3 (Or.inr rfl) x hx z
      hz).symm, hz.1⟩
  have hxt := b.R_comm_t hx
  have hcN : ∀ {g : G}, g ∈ Subgroup.normalizer (d.P : Set G) → g * x = x * g ∨ g * x * g⁻¹ = x⁻¹ →
      g ∈ Subgroup.normalizer (W : Set G) := by
    intro g hgP hgx
    refine mem_normalizer_of_conj_mem fun z hz => Subgroup.mem_inf.mpr ⟨?_,
      (Subgroup.mem_normalizer_iff.mp hgP z).mp hz.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzx := Subgroup.mem_centralizer_singleton_iff.mp hz.1
    rcases hgx with hgx | hgx
    · have h1 : Commute x g := hgx.symm
      have h2 : Commute x z := hzx.symm
      exact ((h1.mul_right h2).mul_right h1.inv_right).symm.eq
    ·
      have hinv : g * z * g⁻¹ * x⁻¹ = x⁻¹ * (g * z * g⁻¹) := by
        rw [← hgx]
        calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
          _ = g * (x * z) * g⁻¹ := by rw [hzx]
          _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
      have := (Commute.inv_right (hinv : Commute (g * z * g⁻¹) x⁻¹)).eq
      rwa [inv_inv] at this
  have htW : h.t ∈ Subgroup.normalizer (W : Set G) := hcN d.t_mem (Or.inl hxt.symm)
  have hτW : b.τ ∈ Subgroup.normalizer (W : Set G) := hcN d.τ_mem (Or.inr (b.τ_inv x hx))
  have hWP := d.eq_of_le hp hq5 hp3 inf_le_right htW hτW hRW hW2 hW3
  have hyW : y ∈ W := by rw [hWdef, hWP]; exact hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyW.1).symm

theorem commutator_mem
    {x : G} (hx : x ∈ d.P) {y : G} (hy : y ∈ d.P) :
    x * y * x⁻¹ * y⁻¹ ∈ b.R := by
  refine commutator_mem_of_fpf d.R_le (fun z hz => d.le_normalizer hz) ?_ h.t_mul_t d.t_mem
    b.t_mem_normalizer_R (fun z hz hzt => ?_) x hx y hy
  · rw [b.card_R]
    exact h.odd_q hp
  · rw [← d.inf_t hp hq5 hp3]
    exact ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr hzt⟩

theorem commute
    {x : G} (hx : x ∈ d.P) {y : G} (hy : y ∈ d.P) : x * y = y * x := by
  classical
  have hq1 : h.q ≠ 1 := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  have key : ∀ {u : G}, (u = b.τ ∨ u = h.t * b.τ) →
      ∀ z ∈ d.P ⊓ Subgroup.centralizer ({u} : Set G), ∀ w ∈ d.P, z * w = w * z := by
    intro u hu
    have hu' : u = h.t ∨ u = b.τ ∨ u = h.t * b.τ := Or.inr hu
    set Ru := d.P ⊓ Subgroup.centralizer ({u} : Set G) with hRudef
    have hRucard : Nat.card Ru = h.q := d.card_inf hp hq5 hp3 hu'
    obtain ⟨g, hg⟩ := h.exists_conj_of_card_eq hp b.R_le_F b.card_R (b.orderOf_eq_two hu')
      (inf_le_right : Ru ≤ _) hRucard
    have hgR : ∀ {a : G}, a ∈ Ru ↔ g * a * g⁻¹ ∈ b.R := by
      intro a
      constructor
      · intro ha
        rw [← hg]
        exact ⟨a, ha, rfl⟩
      · intro ha
        rw [← hg] at ha
        obtain ⟨a', ha', ha'e⟩ := ha
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ha'e
        have : a' = a := by
          have := congrArg (fun z => g⁻¹ * z * g) ha'e
          simpa [mul_assoc] using this
        rw [← this]
        exact ha'
    set P' := d.P.map (MulAut.conj g⁻¹).toMonoidHom with hP'def
    have hP'mem : ∀ {a : G}, a ∈ P' ↔ g * a * g⁻¹ ∈ d.P := by
      intro a
      constructor
      · rintro ⟨a', ha', rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        simpa [mul_assoc] using ha'
      · intro ha
        refine ⟨g * a * g⁻¹, ha, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
    have hP'card : Nat.card P' = h.q ^ 3 := by
      rw [hP'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, d.card]
    have hP'p : IsPGroup h.p P' := d.isPGroup.map _
    have hNRu : ∀ {a : G}, a ∈ Subgroup.normalizer (Ru : Set G) →
        g * a * g⁻¹ ∈ Subgroup.normalizer (b.R : Set G) := by
      intro a ha
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      have hz' : g⁻¹ * z * g ∈ Ru := hgR.mpr (by simpa [mul_assoc] using hz)
      have h1 := (Subgroup.mem_normalizer_iff.mp ha _).mp hz'
      have h2 := hgR.mp h1
      have : g * (a * (g⁻¹ * z * g) * a⁻¹) * g⁻¹ = g * a * g⁻¹ * z * (g * a * g⁻¹)⁻¹ := by group
      rwa [this] at h2
    have hRP' : b.R ≤ P' := by
      intro z hz
      have hzN : z ∈ Subgroup.normalizer (Ru : Set G) := by
        refine mem_normalizer_of_conj_mem fun a ha => ?_
        rw [show z * a * z⁻¹ = a by
          rw [d.commute_R hp hq5 hp3 hu z hz a ha, mul_inv_cancel_right]]
        exact ha
      obtain ⟨n, hn⟩ := b.isPGroup_R ⟨z, hz⟩
      have hzn : z ^ h.p ^ n = 1 := by simpa using congrArg Subtype.val hn
      refine hP'mem.mpr (d.mem _ (hNRu hzN) n ?_)
      rw [conj_pow, hzn, mul_one, mul_inv_cancel]
    have hRuP' : Ru ≤ P' := fun z hz => hP'mem.mpr (d.R_le (hgR.mp hz))
    set X := b.R ⊔ Ru with hXdef
    have hRuR : Ru ≤ Subgroup.normalizer (b.R : Set G) := inf_le_left.trans d.le_normalizer
    have hXmem : ∀ {a : G}, a ∈ X ↔ ∃ r ∈ b.R, ∃ v ∈ Ru, r * v = a := by
      intro a
      have hle : b.R ≤ Subgroup.normalizer (Ru : Set G) := fun r hr =>
        mem_normalizer_of_conj_mem fun v hv => by
          rw [d.commute_R hp hq5 hp3 hu r hr v hv, mul_inv_cancel_right]
          exact hv
      rw [← SetLike.mem_coe, hXdef, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
      exact Iff.rfl
    have hXP : X ≤ d.P := sup_le d.R_le inf_le_left
    have hXP' : X ≤ P' := sup_le hRP' hRuP'
    have hPX : ∀ a ∈ d.P, a ∈ Subgroup.normalizer (X : Set G) := by
      intro a ha
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      have hc := d.commutator_mem hp hq5 hp3 ha (hXP hz)
      have : a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z := by group
      rw [this]
      exact X.mul_mem (Subgroup.mem_sup_left hc) hz
    have hP'X : ∀ a ∈ P', a ∈ Subgroup.normalizer (X : Set G) := by
      intro a ha
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      have hc : a * z * a⁻¹ * z⁻¹ ∈ Ru := by
        refine hgR.mpr ?_
        have := d.commutator_mem hp hq5 hp3 (hP'mem.mp ha) (hP'mem.mp (hXP' hz))
        have e : g * a * g⁻¹ * (g * z * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * z * g⁻¹)⁻¹ =
            g * (a * z * a⁻¹ * z⁻¹) * g⁻¹ := by group
        rwa [e] at this
      have : a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z := by group
      rw [this]
      exact X.mul_mem (Subgroup.mem_sup_right hc) hz
    have hXp : IsPGroup h.p X := hXP.trans le_rfl |> fun hle => d.isPGroup.to_le hle
    have hX1 : X ≠ ⊥ := fun h0 => by
      have := Subgroup.card_le_of_le (le_sup_left : b.R ≤ X)
      rw [hXdef] at h0
      rw [h0, Subgroup.card_bot, b.card_R] at this
      have h5 := h.five_lt
      rw [← JTHyp.q_eq] at h5
      omega
    have hTX : ∀ {v : G}, (v = h.t ∨ v = b.τ ∨ v = h.t * b.τ) →
        v ∈ Subgroup.normalizer (X : Set G) := by
      intro v hv
      have h2 : v ∈ Subgroup.normalizer (b.R : Set G) := by
        rcases hv with rfl | rfl | rfl
        · exact b.t_mem_normalizer_R
        · exact b.τ_mem_normalizer_R
        · exact Subgroup.mul_mem _ b.t_mem_normalizer_R b.τ_mem_normalizer_R
      exact mem_normalizer_sup h2 (d.mem_normalizer_inf hv hu')
    have hCX : b.C ≤ Subgroup.normalizer (X : Set G) := by
      intro c hc
      have hcR := b.C_le_normalizer hc
      have hcRu : c ∈ Subgroup.normalizer (Ru : Set G) :=
        BorelData.mem_normalizer_inf (d.C_le hc)
          (Subgroup.mem_centralizer_singleton_iff.mp (b.C_le_centralizer hu' hc))
      exact mem_normalizer_sup hcR hcRu
    have hXt : X ⊓ Subgroup.centralizer ({h.t} : Set G) = b.R := by
      refine le_antisymm (fun z hz => ?_) (fun z hz => ⟨Subgroup.mem_sup_left hz,
        Subgroup.mem_centralizer_singleton_iff.mpr (b.R_comm_t hz)⟩)
      rw [← d.inf_t hp hq5 hp3]
      exact ⟨hXP hz.1, hz.2⟩
    have hdisj : Disjoint Ru b.R := by
      rw [Subgroup.disjoint_def]
      intro z hzu hzR
      refine d.inf_T hp hq5 (d.R_le hzR) (b.R_comm_t hzR) ?_
      have hzu' := Subgroup.mem_centralizer_singleton_iff.mp hzu.2
      rcases hu with rfl | rfl
      · exact hzu'
      · have hzt := b.R_comm_t hzR
        have e : b.τ = h.t⁻¹ * (h.t * b.τ) := by group
        rw [e]
        exact ((Commute.inv_right (hzt : Commute z h.t)).mul_right
          (hzu' : Commute z (h.t * b.τ))).eq
    have hXcard : Nat.card X = h.q * h.q := by
      rw [hXdef, sup_comm, card_sup_eq_mul_of_disjoint hRuR hdisj, hRucard, b.card_R]
    have hXu : X ⊓ Subgroup.centralizer ({u} : Set G) = Ru :=
      le_antisymm (fun z hz => ⟨hXP hz.1, hz.2⟩) (fun z hz => ⟨Subgroup.mem_sup_right hz, hz.2⟩)
    have hprodX := b.card_eq_prod hp hq5 hXp (hTX (Or.inl rfl)) (hTX (Or.inr (Or.inl rfl)))
    rw [hXcard, hXt, b.card_R] at hprodX
    have hq0 : 0 < h.q := by rw [JTHyp.q_eq]; exact pow_pos (Fact.out : h.p.Prime).pos _
    obtain ⟨w, hwT, hw1, hXw⟩ : ∃ w : G, w ∈ b.T ∧ w ≠ 1 ∧
        Nat.card (X ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 1 := by
      rcases hu with rfl | rfl
      · rw [hXu, hRucard] at hprodX
        refine ⟨h.t * b.τ, b.mem_T_iff.mpr (Or.inl rfl), ?_, ?_⟩
        · have := b.orderOf_eq_two (Or.inr (Or.inr rfl))
          intro h0
          rw [h0, orderOf_one] at this
          omega
        · have : h.q * h.q * 1 = h.q * h.q * Nat.card (X ⊓ Subgroup.centralizer
              ({h.t * b.τ} : Set G) : Subgroup G) := by rw [mul_one]; exact hprodX
          exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq0 hq0) this).symm
      · rw [hXu, hRucard] at hprodX
        refine ⟨b.τ, b.τ_mem_T, b.τ_ne_one, ?_⟩
        have : h.q * h.q * 1 = h.q * h.q * Nat.card (X ⊓ Subgroup.centralizer
            ({b.τ} : Set G) : Subgroup G) := by
          rw [mul_one]
          calc h.q * h.q = h.q * Nat.card (X ⊓ Subgroup.centralizer ({b.τ} : Set G) :
                Subgroup G) * h.q := hprodX
            _ = h.q * h.q * Nat.card (X ⊓ Subgroup.centralizer ({b.τ} : Set G) :
                Subgroup G) := by ring
        exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hq0 hq0) this).symm
    obtain ⟨P₂, -, -, hP₂p, -, hP₂mem, k, hk, hP₂card⟩ := b.exists_P hp hq5 hp3 hXp hX1
      (hTX (Or.inl rfl)) (hTX (Or.inr (Or.inl rfl))) hCX b.t_mem_T hwT h.t_ne_one hw1
      (by rw [hXt, hXw, b.card_R]; exact hq1)
    have hPP₂ : d.P ≤ P₂ := fun a ha => by
      obtain ⟨n, hn⟩ := d.isPGroup ⟨a, ha⟩
      exact hP₂mem a (hPX a ha) n (by simpa using congrArg Subtype.val hn)
    have hP'P₂ : P' ≤ P₂ := fun a ha => by
      obtain ⟨n, hn⟩ := hP'p ⟨a, ha⟩
      exact hP₂mem a (hP'X a ha) n (by simpa using congrArg Subtype.val hn)
    have hq2 : 2 ≤ h.q := by
      have h5 := h.five_lt
      rw [← JTHyp.q_eq] at h5
      omega
    have hk3 : k = 3 := by
      have := Subgroup.card_le_of_le hPP₂
      rw [d.card, hP₂card] at this
      have := (Nat.pow_le_pow_iff_right hq2).mp this
      omega
    have hPeq : d.P = P₂ := Subgroup.eq_of_le_of_card_ge hPP₂ (by rw [hP₂card, d.card, hk3])
    have hP'eq : P' = P₂ := Subgroup.eq_of_le_of_card_ge hP'P₂ (by rw [hP₂card, hP'card, hk3])
    intro z hz a ha
    have haP' : a ∈ P' := hP'eq ▸ hPeq ▸ ha
    have h1 := d.R_le_center hp hq5 hp3 (hgR.mp hz) (hP'mem.mp haP')
    have : g * (z * a) * g⁻¹ = g * (a * z) * g⁻¹ := by
      calc g * (z * a) * g⁻¹ = (g * z * g⁻¹) * (g * a * g⁻¹) := by group
        _ = (g * a * g⁻¹) * (g * z * g⁻¹) := h1
        _ = g * (a * z) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  set Z := d.P ⊓ Subgroup.centralizer (d.P : Set G) with hZdef
  have hZN : ∀ {g : G}, g ∈ Subgroup.normalizer (d.P : Set G) →
      g ∈ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem fun z hz => ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1,
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ d.P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) w).mp hw
      simpa using this
    have hzw := (Subgroup.mem_centralizer_iff.mp hz.2) _ hw'
    calc w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hzw]
      _ = g * z * g⁻¹ * w := by group
  have hRZ : b.R ≤ Z := fun z hz => ⟨d.R_le hz, Subgroup.mem_centralizer_iff.mpr fun w hw =>
    (d.R_le_center hp hq5 hp3 hz hw).symm⟩
  have hZ2 : d.P ⊓ Subgroup.centralizer ({b.τ} : Set G) ≤ Z := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun w hw => (key (Or.inl rfl) z hz w hw).symm⟩
  have hZ3 : d.P ⊓ Subgroup.centralizer ({h.t * b.τ} : Set G) ≤ Z := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun w hw => (key (Or.inr rfl) z hz w hw).symm⟩
  have hZP := d.eq_of_le hp hq5 hp3 inf_le_left (hZN d.t_mem) (hZN d.τ_mem) hRZ hZ2 hZ3
  have hxZ : x ∈ Z := by rw [hZdef, hZP]; exact hx
  exact ((Subgroup.mem_centralizer_iff.mp hxZ.2) y hy).symm

end M1Data

end BorelData

end CFSG.Walter.JT
