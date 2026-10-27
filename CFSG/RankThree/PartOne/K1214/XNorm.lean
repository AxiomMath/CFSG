module

public import CFSG.RankThree.PartOne.K1214.PGroupCyclic
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.K1214.CycMain
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem omegaOne_conj_mem {p : ℕ} {K : Subgroup G} {m : G} (hm : ∀ t ∈ K, m * t * m⁻¹ ∈ K) {x : G}
    (hx : x ∈ omegaOne p K) : m * x * m⁻¹ ∈ omegaOne p K := by
  have : omegaOne p K ≤ (omegaOne p K).comap (MulAut.conj m).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyK, hyp⟩
    show m * y * m⁻¹ ∈ omegaOne p K
    refine Subgroup.subset_closure ⟨hm y hyK, ?_⟩
    rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  exact this hx

theorem commutator_conj_mem {H : Subgroup G} {m : G} (hm : ∀ t ∈ H, m * t * m⁻¹ ∈ H) {x : G}
    (hx : x ∈ ⁅H, H⁆) : m * x * m⁻¹ ∈ ⁅H, H⁆ := by
  have : ⁅H, H⁆ ≤ (⁅H, H⁆).comap (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    show m * ⁅g₁, g₂⁆ * m⁻¹ ∈ ⁅H, H⁆
    have e : m * ⁅g₁, g₂⁆ * m⁻¹ = ⁅m * g₁ * m⁻¹, m * g₂ * m⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hm g₁ hg₁) (hm g₂ hg₂)
  exact this hx

theorem centerIn_conj_mem {T : Subgroup G} {m : G} (hm : m ∈ Subgroup.normalizer (T : Set G))
    {y : G} (hy : y ∈ Subgroup.centralizer (T : Set G) ⊓ T) :
    m * y * m⁻¹ ∈ Subgroup.centralizer (T : Set G) ⊓ T := by
  refine ⟨Subgroup.mem_centralizer_iff.2 ?_, (Subgroup.mem_normalizer_iff.1 hm y).1 hy.2⟩
  intro t ht
  have ht' : m⁻¹ * t * m ∈ T := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm) t).1 ht
    simpa using this
  have h1 : (m⁻¹ * t * m) * y = y * (m⁻¹ * t * m) := Subgroup.mem_centralizer_iff.1 hy.1 _ ht'
  calc t * (m * y * m⁻¹) = m * ((m⁻¹ * t * m) * y) * m⁻¹ := by group
    _ = m * (y * (m⁻¹ * t * m)) * m⁻¹ := by rw [h1]
    _ = (m * y * m⁻¹) * t := by group

namespace CycBase

variable {p : ℕ} {c b : G} {E P Q R Z : Subgroup G} (h : CycBase p c b E P Q R Z)

include h

theorem p_ne_two : p ≠ 2 := by
  have := h.p5
  omega

theorem mem_normalizer_Z {x : G} (hx : x ∈ P) : x ∈ Subgroup.normalizer (Z : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => h.Z_norm x hx z hz, fun hz => ?_⟩
  have := h.Z_norm x⁻¹ (P.inv_mem hx) _ hz
  simpa [mul_assoc] using this

theorem commute_c_Rp {y : G} (hy : y ∈ h.Rp) : c * y = y * c := by
  have := h.actR.2 y hy.1 hy.2
  calc c * y = (c * y * c⁻¹) * c := by group
    _ = y * c := by rw [this]

theorem commutator_sup_le :
    ⁅Z ⊔ (Subgroup.zpowers c ⊔ h.Rp), Z ⊔ (Subgroup.zpowers c ⊔ h.Rp)⁆ ≤ Z := by
  classical
  have hcRp : ∀ k ∈ Subgroup.zpowers c, ∀ y ∈ h.Rp, k * y = y * k := by
    intro k hk y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hcy : Commute c y := h.commute_c_Rp hy
    exact (hcy.zpow_left i).eq
  have hMcomm : ∀ m ∈ Subgroup.zpowers c ⊔ h.Rp, ∀ m' ∈ Subgroup.zpowers c ⊔ h.Rp,
      m * m' = m' * m := by
    intro m hm m' hm'
    obtain ⟨k, hk, y, hy, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcRp hm
    obtain ⟨k', hk', y', hy', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcRp hm'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.1 hk'
    have h1 : Commute (c ^ i) (c ^ i') := Commute.zpow_zpow_self c i i'
    have h2 : Commute y y' := h.R_ab y hy.1 y' hy'.1
    have h3 : Commute (c ^ i) y' := hcRp _ hk y' hy'
    have h4 : Commute (c ^ i') y := hcRp _ hk' y hy
    exact (Commute.mul_left (Commute.mul_right h1 h3) (Commute.mul_right h4.symm h2)).eq
  have hMN : Subgroup.zpowers c ⊔ h.Rp ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (Subgroup.zpowers_le.2 (h.mem_normalizer_Z h.c_P))
      fun y hy => h.mem_normalizer_Z (h.R_le (h.Rp_le_R hy))
  have hV : (↑(Z ⊔ (Subgroup.zpowers c ⊔ h.Rp)) : Set G) =
      (Z : Set G) * ((Subgroup.zpowers c ⊔ h.Rp : Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z _ hMN
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁' : g₁ ∈ (Z : Set G) * ((Subgroup.zpowers c ⊔ h.Rp : Subgroup G) : Set G) := hV ▸ hg₁
  have hg₂' : g₂ ∈ (Z : Set G) * ((Subgroup.zpowers c ⊔ h.Rp : Subgroup G) : Set G) := hV ▸ hg₂
  obtain ⟨z₁, hz₁, m₁, hm₁, rfl⟩ := Set.mem_mul.1 hg₁'
  obtain ⟨z₂, hz₂, m₂, hm₂, rfl⟩ := Set.mem_mul.1 hg₂'
  have hconj : m₁ * m₂ * m₁⁻¹ = m₂ := by
    rw [hMcomm m₁ hm₁ m₂ hm₂]
    group
  have e : ⁅z₁ * m₁, z₂ * m₂⁆ =
      z₁ * (m₁ * z₂ * m₁⁻¹) * (m₂ * z₁⁻¹ * m₂⁻¹) * z₂⁻¹ := by
    calc ⁅z₁ * m₁, z₂ * m₂⁆
        = z₁ * (m₁ * z₂ * m₁⁻¹) * (m₁ * m₂ * m₁⁻¹) * z₁⁻¹ * m₂⁻¹ * z₂⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = z₁ * (m₁ * z₂ * m₁⁻¹) * m₂ * z₁⁻¹ * m₂⁻¹ * z₂⁻¹ := by rw [hconj]
      _ = z₁ * (m₁ * z₂ * m₁⁻¹) * (m₂ * z₁⁻¹ * m₂⁻¹) * z₂⁻¹ := by group
  rw [e]
  have h1 : m₁ * z₂ * m₁⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 (hMN hm₁) z₂).1 hz₂
  have h2 : m₂ * z₁⁻¹ * m₂⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 (hMN hm₂) _).1 (Z.inv_mem hz₁)
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem hz₁ h1) h2) (Z.inv_mem hz₂)

section Fin

variable [Finite G]

theorem R_conj_mem {r e : ℕ} (he : 1 ≤ e) (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e))))
    (hEcard : Nat.card E = p ^ (r + 2)) : ∀ x ∈ R, ∀ y ∈ E, x * y * x⁻¹ ∈ E := by
  intro x hx
  have hEeq := h.E_eq he φ hEcard
  have hle : E ≤ E.comap (MulAut.conj x).toMonoidHom := by
    refine le_trans hEeq.le ?_
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Subgroup.zpowers_le.2 ?_
      have hd : c * x * c⁻¹ * x⁻¹ ∈ h.Rp :=
        ⟨R.mul_mem (h.R_norm c h.c_P x hx) (R.inv_mem hx), h.actR.1 x hx⟩
      show x * c * x⁻¹ ∈ E
      have : x * c * x⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ * c := by group
      rw [this]
      exact E.mul_mem (E.inv_mem (h.Rp_le_E hd)) h.c_E
    · intro y hy
      show x * y * x⁻¹ ∈ E
      have hy1 : x * y = y * x := h.R_ab x hx y hy.1
      have : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [hy1]
          _ = y := by group
      rw [this]
      exact h.Rp_le_E hy
    · refine Subgroup.zpowers_le.2 ?_
      show x * b * x⁻¹ ∈ E
      have hb1 : b * x = x * b := h.ZR b h.b_Z x hx
      have : x * b * x⁻¹ = b := by
        calc x * b * x⁻¹ = (b * x) * x⁻¹ := by rw [hb1]
          _ = b := by group
      rw [this]
      exact h.b_E
  intro y hy
  exact hle hy

theorem R_le_normalizer {r e : ℕ} (he : 1 ≤ e)
    (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) (hEcard : Nat.card E = p ^ (r + 2)) :
    R ≤ Subgroup.normalizer (E : Set G) :=
  Torsion37.le_normalizer_of_forall (R := R) (Y := E) (h.R_conj_mem he φ hEcard)

theorem comm_c_mem_b {r e : ℕ} (he : 1 ≤ e)
    (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) (hEcard : Nat.card E = p ^ (r + 2))
    {z : G} (hzZ : z ∈ Z) (hzN : z ∈ Subgroup.normalizer (E : Set G)) :
    c * z * c⁻¹ * z⁻¹ ∈ Subgroup.zpowers b := by
  have h1 : c * z * c⁻¹ * z⁻¹ ∈ E := by
    have : c * z * c⁻¹ * z⁻¹ = c * (z * c⁻¹ * z⁻¹) := by group
    rw [this]
    exact E.mul_mem h.c_E ((Subgroup.mem_normalizer_iff.1 hzN _).1 (E.inv_mem h.c_E))
  have h2 : c * z * c⁻¹ * z⁻¹ ∈ Z := Z.mul_mem (h.Z_norm c h.c_P z hzZ) (Z.inv_mem hzZ)
  exact h.E_inf_Z he φ hEcard h1 h2

omit [Finite G] in
theorem Eb_props {y : G} (hy : y ∈ Subgroup.zpowers b ⊔ h.Rp) :
    c * y = y * c ∧ y ^ p = 1 ∧ ∀ q ∈ Q, y * q = q * y := by
  have hcomm : ∀ k ∈ Subgroup.zpowers b, ∀ l ∈ h.Rp, k * l = l * k := by
    intro k hk l hl
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hbl : b * l = l * b := h.ZR b h.b_Z l hl.1
    exact (Commute.zpow_left (show Commute b l from hbl) i).eq
  obtain ⟨k, hk, l, hl, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcomm hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hcb : Commute c b := h.b_cent c h.c_P
  have hcl : Commute c l := by
    have := h.actR.2 l hl.1 hl.2
    show c * l = l * c
    calc c * l = (c * l * c⁻¹) * c := by group
      _ = l * c := by rw [this]
  have hlq : ∀ q ∈ Q, l * q = q * l := by
    intro q hq
    rw [h.Q_eq] at hq
    obtain ⟨z, hz, r', hr, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute h.ZR hq
    have h1 : l * z = z * l := (h.ZR z hz l hl.1).symm
    have h2 : l * r' = r' * l := h.R_ab l hl.1 r' hr
    exact (Commute.mul_right (show Commute l z from h1) (show Commute l r' from h2)).eq
  have hbq : ∀ q ∈ Q, b ^ i * q = q * b ^ i := by
    intro q hq
    have : Commute q b := h.b_cent q (h.Q_le hq)
    exact (this.symm.zpow_left i).eq
  refine ⟨(Commute.mul_right (hcb.zpow_right i) hcl).eq, ?_, fun q hq => ?_⟩
  · have hbl : Commute (b ^ i) l := by
      have : Commute b l := h.ZR b h.b_Z l hl.1
      exact this.zpow_left i
    rw [hbl.mul_pow, hl.2, mul_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      h.b_p, one_zpow]
  · exact (Commute.mul_left (show Commute (b ^ i) q from hbq q hq)
      (show Commute l q from hlq q hq)).eq

theorem pElement_decomp {r e : ℕ} (he : 1 ≤ e)
    (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) (hEcard : Nat.card E = p ^ (r + 2))
    {x : G} (hxP : x ∈ P) (hxN : x ∈ Subgroup.normalizer (E : Set G)) (hxp : x ^ p = 1) :
    ∃ j : ℕ, ∃ z ∈ Z, ∃ ρ ∈ h.Rp, x = c ^ j * z * ρ ∧ z ^ p = 1 ∧
      z ∈ Subgroup.normalizer (E : Set G) := by
  classical
  obtain ⟨f, hfP, hPf⟩ := h.P_gen
  obtain ⟨j, q, hq, hxq⟩ :=
    exists_c_pow_mul h.prime h.Q_le h.Q_normal' hfP hPf h.c_P h.c_Q h.c_p hxP hxp
  have hq' := hq
  rw [h.Q_eq] at hq'
  obtain ⟨z, hz, r', hr, hqzr⟩ := Torsion37.exists_mul_of_mem_sup_of_commute h.ZR hq'
  subst hqzr
  subst hxq
  have hcN : c ∈ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer h.c_E
  have hr'N : r' ∈ Subgroup.normalizer (E : Set G) := h.R_le_normalizer he φ hEcard hr
  have hzN : z ∈ Subgroup.normalizer (E : Set G) := by
    have : z = (c ^ j)⁻¹ * (c ^ j * (z * r')) * r'⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hcN j)) hxN)
      (Subgroup.inv_mem _ hr'N)
  have hdz : c * z * c⁻¹ * z⁻¹ ∈ Subgroup.zpowers b := h.comm_c_mem_b he φ hEcard hz hzN
  have hdr : c * r' * c⁻¹ * r'⁻¹ ∈ h.Rp :=
    ⟨R.mul_mem (h.R_norm c h.c_P r' hr) (R.inv_mem hr), h.actR.1 r' hr⟩
  have hzdr : z * (c * r' * c⁻¹ * r'⁻¹) = (c * r' * c⁻¹ * r'⁻¹) * z := h.ZR z hz _ hdr.1
  have hd : c * (z * r') * c⁻¹ * (z * r')⁻¹ = (c * z * c⁻¹ * z⁻¹) * (c * r' * c⁻¹ * r'⁻¹) := by
    calc c * (z * r') * c⁻¹ * (z * r')⁻¹
        = (c * z * c⁻¹ * z⁻¹) * (z * (c * r' * c⁻¹ * r'⁻¹) * z⁻¹) := by group
      _ = (c * z * c⁻¹ * z⁻¹) * (c * r' * c⁻¹ * r'⁻¹) := by rw [hzdr]; group
  have hdEb : (c * z * c⁻¹ * z⁻¹) * (c * r' * c⁻¹ * r'⁻¹) ∈ Subgroup.zpowers b ⊔ h.Rp :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hdz) (Subgroup.mem_sup_right hdr)
  obtain ⟨hcd, hdp, hdq⟩ := h.Eb_props hdEb
  have hzrQ : z * r' ∈ Q := by
    rw [h.Q_eq]
    exact Subgroup.mul_mem_sup hz hr
  have hpow : (c ^ j * (z * r')) ^ p = (z * r') ^ p :=
    pow_c_pow_mul h.prime h.p_ne_two hd hcd hdp (hdq _ hzrQ) h.c_p j
  have h1 : z ^ p * r' ^ p = 1 := by
    rw [← (Commute.mul_pow (show Commute z r' from h.ZR z hz r' hr)), ← hpow]
    exact hxp
  have hzp : z ^ p = 1 := by
    have h2 : z ^ p = (r' ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : z ^ p ∈ R ⊓ Z := ⟨by rw [h2]; exact R.inv_mem (R.pow_mem hr p), Z.pow_mem hz p⟩
    rw [h.ZR_bot, Subgroup.mem_bot] at h3
    exact h3
  have hr'p : r' ^ p = 1 := by simpa [hzp] using h1
  exact ⟨j, z, hz, r', ⟨hr, hr'p⟩, (mul_assoc _ _ _).symm, hzp, hzN⟩

theorem mem_zpowers_of_pow_eq_one
    (hF : ∀ U : Subgroup G, U ≤ Q ⊓ E →
      (∀ m ∈ Subgroup.normalizer ((P ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G),
        ∀ u ∈ U, m * u * m⁻¹ ∈ U) → U = ⊥ ∨ U = Q ⊓ E)
    {u : G} (huZ : u ∈ Z) (huN : u ∈ Subgroup.normalizer (E : Set G)) (hup : u ^ p = 1) :
    u ∈ Subgroup.zpowers b := by
  classical
  obtain ⟨r, e, hr, he2, ⟨φ⟩, hEcard⟩ := h.shape
  have he : 1 ≤ e := by omega
  by_contra hub
  set T : Subgroup G := P ⊓ Subgroup.normalizer (E : Set G) with hT
  have hTP : T ≤ P := inf_le_left
  have hcN : c ∈ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer h.c_E
  have hcT : c ∈ T := ⟨h.c_P, hcN⟩
  have huT : u ∈ T := ⟨h.Z_le huZ, huN⟩
  have hET : E ≤ T := fun y hy => ⟨h.E_le hy, Subgroup.le_normalizer hy⟩
  set W : Subgroup G := omegaOne p T with hW
  set ZT : Subgroup G := Subgroup.centralizer (T : Set G) ⊓ T with hZT
  set Om : Subgroup G := omegaOne p ZT with hOm
  set U : Subgroup G := ⁅W, W⁆ ⊓ Om with hU
  have hWV : W ≤ Z ⊔ (Subgroup.zpowers c ⊔ h.Rp) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxT, hxp⟩
    obtain ⟨j, z, hz, ρ, hρ, rfl, -, -⟩ := h.pElement_decomp he φ hEcard hxT.1 hxT.2 hxp
    have h1 : c ^ j * z * (c ^ j)⁻¹ ∈ Z := h.Z_norm (c ^ j) (P.pow_mem h.c_P j) z hz
    have h2 : c ^ j * ρ ∈ Subgroup.zpowers c ⊔ h.Rp :=
      Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) j))
        (Subgroup.mem_sup_right hρ)
    have : c ^ j * z * ρ = (c ^ j * z * (c ^ j)⁻¹) * (c ^ j * ρ) := by group
    rw [this]
    exact Subgroup.mul_mem_sup h1 h2
  have hWZ : ⁅W, W⁆ ≤ Z := (Subgroup.commutator_mono hWV hWV).trans h.commutator_sup_le
  have hZTE : ∀ y ∈ ZT, y ^ p = 1 → y ∈ E := by
    intro y hy hyp
    have hcent : Subgroup.zpowers y ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro e' he'
      exact Subgroup.mem_centralizer_iff.1 hy.1 e' (hET he')
    have hE := h.E_elem
    have hy' := IsElementaryAbelian.zpowers_of_pow_eq_one hyp
    have hF' : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers y) :=
      IsElementaryAbelian.sup_of_le_centralizer hcent
    have := h.E_max _ hF' le_sup_left
    have h1 : Subgroup.zpowers y ≤ E ⊔ Subgroup.zpowers y := le_sup_right
    rw [this] at h1
    exact h1 (Subgroup.mem_zpowers y)
  have hOmE : Om ≤ E := (Subgroup.closure_le _).2 (fun y hy => hZTE y hy.1 hy.2)
  have hUQE : U ≤ Q ⊓ E := fun x hx =>
    ⟨by rw [h.Q_eq]; exact Subgroup.mem_sup_left (hWZ hx.1), hOmE hx.2⟩
  have hUinv : ∀ m ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ U, m * x * m⁻¹ ∈ U := by
    intro m hm x hx
    have hmT : ∀ t ∈ T, m * t * m⁻¹ ∈ T := fun t ht => (Subgroup.mem_normalizer_iff.1 hm t).1 ht
    have hmW : ∀ t ∈ W, m * t * m⁻¹ ∈ W := fun t ht => omegaOne_conj_mem hmT ht
    have hmZT : ∀ t ∈ ZT, m * t * m⁻¹ ∈ ZT := fun t ht => centerIn_conj_mem hm ht
    exact ⟨commutator_conj_mem hmW hx.1, omegaOne_conj_mem hmZT hx.2⟩
  have hw_b : c * u * c⁻¹ * u⁻¹ ∈ Subgroup.zpowers b := h.comm_c_mem_b he φ hEcard huZ huN
  have hw_ne : c * u * c⁻¹ * u⁻¹ ≠ 1 := by
    intro h1
    apply hub
    exact h.Y_torsion he φ hEcard huZ (mul_inv_eq_one.1 h1) hup
  have hwW : c * u * c⁻¹ * u⁻¹ ∈ ⁅W, W⁆ := by
    have hcW : c ∈ W := Subgroup.subset_closure ⟨hcT, h.c_p⟩
    have huW : u ∈ W := Subgroup.subset_closure ⟨huT, hup⟩
    have := Subgroup.commutator_mem_commutator hcW huW
    rwa [commutatorElement_def] at this
  have hwOm : c * u * c⁻¹ * u⁻¹ ∈ Om := by
    have hbZT : b ∈ ZT :=
      ⟨Subgroup.mem_centralizer_iff.2 fun t ht => h.b_cent t (hTP ht), hET h.b_E⟩
    have hwZT : c * u * c⁻¹ * u⁻¹ ∈ ZT := (Subgroup.zpowers_le.2 hbZT) hw_b
    have hwp : (c * u * c⁻¹ * u⁻¹) ^ p = 1 := by
      have := orderOf_dvd_of_mem_zpowers hw_b
      rw [h.orderOf_b] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    exact Subgroup.subset_closure ⟨hwZT, hwp⟩
  have hwU : c * u * c⁻¹ * u⁻¹ ∈ U := ⟨hwW, hwOm⟩
  rcases hF U hUQE hUinv with hU0 | hUB
  · rw [hU0, Subgroup.mem_bot] at hwU
    exact hw_ne hwU
  · have hRpU : h.Rp ≤ U := by
      rw [hUB]
      exact le_inf h.Rp_le_Q h.Rp_le_E
    have hRpZ : h.Rp ≤ R ⊓ Z :=
      le_inf h.Rp_le_R ((hRpU.trans (inf_le_left : U ≤ ⁅W, W⁆)).trans hWZ)
    rw [h.ZR_bot] at hRpZ
    have hcard1 : Nat.card h.Rp = 1 := by
      have : h.Rp = ⊥ := le_bot_iff.1 hRpZ
      rw [this]
      simp
    have hpow := h.card_Rp he φ
    have h1 : 1 < p ^ r := Nat.one_lt_pow (by omega) h.prime.one_lt
    omega

theorem omegaOne_eq
    (hF : ∀ U : Subgroup G, U ≤ Q ⊓ E →
      (∀ m ∈ Subgroup.normalizer ((P ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G),
        ∀ u ∈ U, m * u * m⁻¹ ∈ U) → U = ⊥ ∨ U = Q ⊓ E) :
    omegaOne p (P ⊓ Subgroup.normalizer (E : Set G)) = E := by
  obtain ⟨r, e, hr, he2, ⟨φ⟩, hEcard⟩ := h.shape
  have he : 1 ≤ e := by omega
  have hE := h.E_elem
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxT, hxp⟩
    obtain ⟨j, z, hz, ρ, hρ, rfl, hzp, hzN⟩ := h.pElement_decomp he φ hEcard hxT.1 hxT.2 hxp
    have hzb := h.mem_zpowers_of_pow_eq_one hF hz hzN hzp
    exact E.mul_mem (E.mul_mem (E.pow_mem h.c_E j) (Subgroup.zpowers_le.2 h.b_E hzb))
      (h.Rp_le_E hρ)
  · intro y hy
    exact Subgroup.subset_closure
      ⟨⟨h.E_le hy, Subgroup.le_normalizer hy⟩,
        elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) y hy⟩

theorem le_normalizer
    (hF : ∀ U : Subgroup G, U ≤ Q ⊓ E →
      (∀ m ∈ Subgroup.normalizer ((P ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G),
        ∀ u ∈ U, m * u * m⁻¹ ∈ U) → U = ⊥ ∨ U = Q ⊓ E) :
    P ≤ Subgroup.normalizer (E : Set G) := by
  classical
  have hp : Fact p.Prime := ⟨h.prime⟩
  set T : Subgroup G := P ⊓ Subgroup.normalizer (E : Set G) with hT
  have hω := h.omegaOne_eq hF
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (E : Set G) := by
    refine Torsion37.le_normalizer_of_forall (R := Subgroup.normalizer (T : Set G)) (Y := E) ?_
    intro m hm y hy
    have hmT : ∀ t ∈ T, m * t * m⁻¹ ∈ T := fun t ht => (Subgroup.mem_normalizer_iff.1 hm t).1 ht
    have hy' : y ∈ omegaOne p T := by
      rw [hω]
      exact hy
    have := omegaOne_conj_mem (p := p) hmT hy'
    rwa [hω] at this
  by_contra hne
  have hTlt : T.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ T.subgroupOf P := by rw [htop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.1 this).2
  have : Group.IsNilpotent ↥P := h.P_p.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent (T.subgroupOf P) hTlt
  obtain ⟨y', hy'N, hy'T⟩ := IsConcreteLE.exists_of_lt hlt
  have hyP : (y' : G) ∈ P := y'.2
  have hyT : (y' : G) ∉ T := fun hyT' => hy'T (Subgroup.mem_subgroupOf.2 hyT')
  have hyN : (y' : G) ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hcoe : ∀ t' : ↥P, ((y' * t' * y'⁻¹ : ↥P) : G) = (y' : G) * (t' : G) * (y' : G)⁻¹ := by
      intro t'
      simp
    constructor
    · intro ht
      have htP : t ∈ P := ht.1
      have h1 : (⟨t, htP⟩ : ↥P) ∈ T.subgroupOf P := ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hy'N ⟨t, htP⟩).1 h1
      have h3 := Subgroup.mem_subgroupOf.1 h2
      rwa [hcoe] at h3
    · intro ht
      have htP' : (y' : G) * t * (y' : G)⁻¹ ∈ P := ht.1
      have htP : t ∈ P := by
        have h4 := P.mul_mem (P.mul_mem (P.inv_mem hyP) htP') hyP
        have e : (y' : G)⁻¹ * ((y' : G) * t * (y' : G)⁻¹) * (y' : G) = t := by group
        rwa [e] at h4
      have h1 : (y' * ⟨t, htP⟩ * y'⁻¹ : ↥P) ∈ T.subgroupOf P := by
        rw [Subgroup.mem_subgroupOf, hcoe]
        exact ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hy'N ⟨t, htP⟩).2 h1
      exact Subgroup.mem_subgroupOf.1 h2
  exact hyT ⟨hyP, hNT hyN⟩

theorem isCyclic_Z
    (hF : ∀ U : Subgroup G, U ≤ Q ⊓ E →
      (∀ m ∈ Subgroup.normalizer ((P ⊓ Subgroup.normalizer (E : Set G) : Subgroup G) : Set G),
        ∀ u ∈ U, m * u * m⁻¹ ∈ U) → U = ⊥ ∨ U = Q ⊓ E) :
    IsCyclic ↥Z := by
  have hPN := h.le_normalizer hF
  exact isCyclic_subgroup_of_pow_eq_one_subset h.prime h.p_ne_two (h.P_p.to_le h.Z_le) h.b_Z
    h.orderOf_b fun z hz hzp => h.mem_zpowers_of_pow_eq_one hF hz (hPN (h.Z_le hz)) hzp

end Fin

end CycBase

end CFSG.RankThree.PartOne.K1214
