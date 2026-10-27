module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119KT
public import CFSG.RankThree.PartTwo.Sec21.Hering2119KN
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK
import all CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix
open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem matrix_eq_of_mulVec {A B : M4} (h : ∀ v, A.mulVec v = B.mulVec v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem omega4_add_right (a u w : V4) : omega4 a (u + w) = omega4 a u + omega4 a w := by
  simp [omega4]; ring

theorem omega4_smul_right (a : V4) (c : F3) (u : V4) : omega4 a (c • u) = c * omega4 a u := by
  simp [omega4]; ring

theorem mem_normalizer_zpowers_of_mem {g d : G} (h : g * d * g⁻¹ ∈ Subgroup.zpowers d) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ h k

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem inA_Phi {b : G} (hb : b ∈ A) : inA (Phi d a₀ a₁ f₀ f₁ b) := by
  have hC := h.hC
  refine ⟨?_, ?_⟩
  · simp [Phi, hC.om_zero_of_comm (h.hAc _ h.ha₀ _ hb)]
  · simp [Phi, hC.om_zero_of_comm (h.hAc _ h.ha₁ _ hb)]

theorem exists_A_of_inA {v : V4} (hv : inA v) : ∃ b ∈ A, Phi d a₀ a₁ f₀ f₁ b = v := by
  obtain ⟨h2, h3⟩ := hv
  refine ⟨a₀ ^ (v 0).val * a₁ ^ (v 1).val, A.mul_mem (A.pow_mem h.ha₀ _) (A.pow_mem h.ha₁ _), ?_⟩
  have e := h.Phi_rep v
  unfold rep at e
  have e2 : (v 2).val = 0 := by rw [h2]; rfl
  have e3 : (v 3).val = 0 := by rw [h3]; rfl
  rw [e2, e3] at e
  simpa using e

end SympBasis

structure LineSetup (A Q D M Y : Subgroup G) (d a₀ a₁ f₀ f₁ e t₀ t x : G) : Prop where
  hS : SympBasis A Q d a₀ a₁ f₀ f₁
  hT : TData A Q D M Y d e t₀
  hxD : x ∈ D
  hxQ : x ∉ Q
  htN : t ∈ Subgroup.normalizer (Q : Set G)
  hte : t * e = e * t
  htD : ∀ y ∈ D, t * y * t⁻¹ = y⁻¹
  htriv : ∀ b ∈ Q, b⁻¹ * t * b * t⁻¹ ∈ D
  hMQ : M ≤ Q
  hfus : ∀ m ∈ M, ∃ w : G, w * e * w⁻¹ = e ∧ w * m * w⁻¹ ∈ Subgroup.zpowers d
  h81 : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ R : Subgroup G, IsPGroup 3 R →
    R ≤ Subgroup.centralizer ({b} : Set G) → Nat.card R ≤ 81

namespace LineSetup

variable {A Q D M Y : Subgroup G} {d a₀ a₁ f₀ f₁ e t₀ t x : G}
  (h : LineSetup A Q D M Y d a₀ a₁ f₀ f₁ e t₀ t x)

include h

theorem hxN : x ∈ Subgroup.normalizer (Q : Set G) := h.hT.hP'N (Subgroup.mem_sup_right h.hxD)

theorem hxd : x * d * x⁻¹ = d := by
  have := h.hT.hDc x h.hxD d h.hT.hdD
  rw [this]; group

theorem hxNQ : x ∈ NQ Q d := by
  refine ⟨h.hxN, mem_normalizer_zpowers_of_mem ?_⟩
  rw [h.hxd]; exact Subgroup.mem_zpowers d

theorem htd : t * d * t⁻¹ = d⁻¹ := h.htD d h.hT.hdD

theorem htNQ : t ∈ NQ Q d := by
  refine ⟨h.htN, mem_normalizer_zpowers_of_mem ?_⟩
  rw [h.htd]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers d)

theorem hx3 : x ^ 3 = 1 := h.hT.hDe.2 x h.hxD

theorem heQ : e ∈ Q := h.hT.hAQ h.hT.heA

theorem xi_ne_one : Mg d a₀ a₁ f₀ f₁ x ≠ 1 := fun hM =>
  h.hxQ (h.hS.mem_Q_of_Mg_one h.hxNQ hM (n := 1) (by simpa using h.hx3))

theorem xi_cube : Mg d a₀ a₁ f₀ f₁ x * Mg d a₀ a₁ f₀ f₁ x * Mg d a₀ a₁ f₀ f₁ x = 1 := by
  have e : (h.hS.MgHom (⟨x, h.hxNQ⟩ : NQ Q d)) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, h.hxNQ⟩ : NQ Q d) ^ 3 = 1 := Subtype.ext (by simpa using h.hx3)
    rw [this, map_one]
  rw [← pow_three']
  exact e

theorem xi_symp (u v : V4) :
    omega4 ((Mg d a₀ a₁ f₀ f₁ x).mulVec u) ((Mg d a₀ a₁ f₀ f₁ x).mulVec v) = omega4 u v :=
  h.hS.Mg_symp h.hxN h.hxd u v

theorem xi_noFix : ∀ v, inA v → v ≠ 0 → (Mg d a₀ a₁ f₀ f₁ x).mulVec v ≠ v := by
  intro v hv hne hfix
  obtain ⟨b, hbA, rfl⟩ := h.hS.exists_A_of_inA hv
  have hbd : b ∉ Subgroup.zpowers d := fun hb => hne (h.hS.Phi_z0 hb)
  have := h.hS.no_fix3 (h.hS.hAQ hbA) hbd (h.h81 b hbA hbd) h.hxNQ ⟨1, by simpa using h.hx3⟩ hfix
  exact h.hxQ this

theorem xi_Phi {b : G} (hb : b ∈ Q) :
    Phi d a₀ a₁ f₀ f₁ (x * b * x⁻¹) = (Mg d a₀ a₁ f₀ f₁ x).mulVec (Phi d a₀ a₁ f₀ f₁ b) :=
  h.hS.Mg_apply h.hxN (NQ_conj_d h.hxNQ) hb

theorem T_Phi {b : G} (hb : b ∈ Q) :
    Phi d a₀ a₁ f₀ f₁ (t * b * t⁻¹) = (Mg d a₀ a₁ f₀ f₁ t).mulVec (Phi d a₀ a₁ f₀ f₁ b) :=
  h.hS.Mg_apply h.htN (NQ_conj_d h.htNQ) hb

theorem mem_DQ_of_fix {b : G} (hb : b ∈ Q)
    (hfix : (Mg d a₀ a₁ f₀ f₁ x).mulVec (Phi d a₀ a₁ f₀ f₁ b) = Phi d a₀ a₁ f₀ f₁ b) :
    b ∈ D ⊓ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := h.hS
  let C : Subgroup G :=
    { carrier := {y | y ∈ Q ∧ Phi d a₀ a₁ f₀ f₁ (x * y * x⁻¹) = Phi d a₀ a₁ f₀ f₁ y}
      mul_mem' := by
        rintro y y' ⟨hy, hy1⟩ ⟨hy', hy1'⟩
        refine ⟨Q.mul_mem hy hy', ?_⟩
        have e : x * (y * y') * x⁻¹ = (x * y * x⁻¹) * (x * y' * x⁻¹) := by group
        rw [e, hS.Phi_mul (hS.conj_mem h.hxN hy) (hS.conj_mem h.hxN hy'), hS.Phi_mul hy hy', hy1,
          hy1']
      one_mem' := ⟨Q.one_mem, by simp [hS.Phi_one]⟩
      inv_mem' := by
        rintro y ⟨hy, hy1⟩
        refine ⟨Q.inv_mem hy, ?_⟩
        have e : x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
        rw [e, hS.Phi_inv (hS.conj_mem h.hxN hy), hS.Phi_inv hy, hy1] }
  have hCQ : C ≤ Q := fun y hy => hy.1
  have hCN : C ≤ Subgroup.normalizer (A : Set G) := hCQ.trans hS.hQS.le
  have hDQC : D ⊓ Q ≤ C := by
    rintro y ⟨hyD, hyQ⟩
    refine ⟨hyQ, ?_⟩
    have : x * y * x⁻¹ = y := by rw [h.hT.hDc x h.hxD y hyD]; group
    rw [this]
  have hCA : A ⊓ C ≤ Subgroup.zpowers d := by
    rintro y ⟨hyA, hyQ, hyx⟩
    refine hS.Phi_ker hyQ ?_
    by_contra hne
    exact h.xi_noFix _ (hS.inA_Phi hyA) hne (by rw [← h.xi_Phi hyQ]; exact hyx)
  have hm := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := A) (B := C) hCN
  have h1 : Nat.card (A ⊔ C : Subgroup G) ≤ 243 := by
    rw [← h.hT.hQ243]
    exact Subgroup.card_le_of_le (sup_le hS.hAQ hCQ)
  have h2 : Nat.card (A ⊓ C : Subgroup G) ≤ 3 := by
    have := Subgroup.card_le_of_le hCA
    rwa [Nat.card_zpowers, orderOf_eq_prime hS.hd3 hS.hd1] at this
  rw [h.hT.hA27] at hm
  have h3 : 27 * Nat.card C ≤ 243 * 3 := by
    rw [← hm]; exact Nat.mul_le_mul h1 h2
  have h4 : Nat.card C ≤ Nat.card (D ⊓ Q : Subgroup G) := by
    rw [h.hT.card_QD.2]; omega
  have hCeq : D ⊓ Q = C := Subgroup.eq_of_le_of_card_ge hDQC h4
  have hbC : b ∈ C := ⟨hb, by rw [h.xi_Phi hb, hfix]⟩
  rw [hCeq]; exact hbC

theorem fix_iff (v : V4) :
    (Mg d a₀ a₁ f₀ f₁ x).mulVec v = v ↔ ∃ b ∈ D ⊓ Q, Phi d a₀ a₁ f₀ f₁ b = v := by
  constructor
  · intro hv
    have hb := h.hS.rep_mem v
    have hr := h.hS.Phi_rep v
    refine ⟨_, h.mem_DQ_of_fix hb (by rw [hr]; exact hv), hr⟩
  · rintro ⟨b, ⟨hbD, hbQ⟩, rfl⟩
    rw [← h.xi_Phi hbQ]
    have : x * b * x⁻¹ = b := by rw [h.hT.hDc x h.hxD b hbD]; group
    rw [this]

theorem presF (v : V4) (hv : InF (Phi d a₀ a₁ f₀ f₁ e) (Mg d a₀ a₁ f₀ f₁ x) v) :
    InF (Phi d a₀ a₁ f₀ f₁ e) (Mg d a₀ a₁ f₀ f₁ x) ((Mg d a₀ a₁ f₀ f₁ x).mulVec v) := by
  have hS := h.hS
  have hC := hS.hC
  obtain ⟨c, hh, hhfix, hhom, rfl⟩ := hv
  obtain ⟨m₀, hm₀M, hxe⟩ := h.hT.hLA.hcent x (h.hT.hDY h.hxD)
  have hm₀Q : m₀ ∈ Q := h.hMQ hm₀M
  have hm₀D : m₀ ∈ D := h.hT.hLA.hMD hm₀M
  have h1 : (Mg d a₀ a₁ f₀ f₁ x).mulVec (Phi d a₀ a₁ f₀ f₁ e) =
      Phi d a₀ a₁ f₀ f₁ e + Phi d a₀ a₁ f₀ f₁ m₀ := by
    rw [← h.xi_Phi h.heQ, hxe, hS.Phi_mul h.heQ hm₀Q]
  have h2 : (Mg d a₀ a₁ f₀ f₁ x).mulVec (Phi d a₀ a₁ f₀ f₁ m₀) = Phi d a₀ a₁ f₀ f₁ m₀ :=
    (h.fix_iff _).mpr ⟨m₀, ⟨hm₀D, hm₀Q⟩, rfl⟩
  have h3 : omega4 (Phi d a₀ a₁ f₀ f₁ e) (Phi d a₀ a₁ f₀ f₁ m₀) = 0 := by
    rw [hS.omega4_Phi h.heQ hm₀Q]
    apply hC.om_zero_of_comm
    have := h.hT.hLA.hMc m₀ hm₀M
    calc e * m₀ = e * m₀ * e⁻¹ * e := by group
      _ = m₀ * e := by rw [this]
  refine ⟨c, c • Phi d a₀ a₁ f₀ f₁ m₀ + hh, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2, hhfix]
  · rw [omega4_add_right, omega4_smul_right, h3, hhom]; simp
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, h1, hhfix, smul_add]; abel

theorem t_sq_conj {b : G} (hb : b ∈ Q) : t * (t * b * t⁻¹) * t⁻¹ = b := by
  have hδ := h.htriv b hb
  set δ := b⁻¹ * t * b * t⁻¹ with hδdef
  have e1 : t * b * t⁻¹ = b * δ := by rw [hδdef]; group
  calc t * (t * b * t⁻¹) * t⁻¹ = t * (b * δ) * t⁻¹ := by rw [e1]
    _ = (t * b * t⁻¹) * (t * δ * t⁻¹) := by group
    _ = (b * δ) * δ⁻¹ := by rw [e1, h.htD δ hδ]
    _ = b := by group

theorem T_sq : Mg d a₀ a₁ f₀ f₁ t * Mg d a₀ a₁ f₀ f₁ t = 1 := by
  apply matrix_eq_of_mulVec
  intro v
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ Q, Phi d a₀ a₁ f₀ f₁ b = v := ⟨_, h.hS.rep_mem v, h.hS.Phi_rep v⟩
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ← h.T_Phi hb,
    ← h.T_Phi (h.hS.conj_mem h.htN hb), h.t_sq_conj hb]

theorem T_fixa : (Mg d a₀ a₁ f₀ f₁ t).mulVec (Phi d a₀ a₁ f₀ f₁ e) = Phi d a₀ a₁ f₀ f₁ e := by
  rw [← h.T_Phi h.heQ]
  have : t * e * t⁻¹ = e := by rw [h.hte]; group
  rw [this]

theorem T_neg (v : V4) (hv : (Mg d a₀ a₁ f₀ f₁ x).mulVec v = v) :
    (Mg d a₀ a₁ f₀ f₁ t).mulVec v = -v := by
  obtain ⟨b, ⟨hbD, hbQ⟩, rfl⟩ := (h.fix_iff v).mp hv
  rw [← h.T_Phi hbQ, h.htD b hbD, h.hS.Phi_inv hbQ]

theorem isItem :
    IsItem (Phi d a₀ a₁ f₀ f₁ e) (Mg d a₀ a₁ f₀ f₁ x) (Mg d a₀ a₁ f₀ f₁ t) :=
  ⟨h.xi_symp, h.xi_ne_one, h.xi_cube, h.xi_noFix, h.presF, h.T_sq,
    h.hS.Mg_mult h.htN h.htd, h.T_fixa, h.T_neg⟩

theorem badVec_good {v : V4}
    (hv : BadVec (Phi d a₀ a₁ f₀ f₁ e) (Mg d a₀ a₁ f₀ f₁ x) v) :
    ∃ f ∈ Q, f ∉ Subgroup.zpowers d ∧ Phi d a₀ a₁ f₀ f₁ f = v ∧
      ∀ R : Subgroup G, IsPGroup 3 R → R ≤ Subgroup.centralizer ({f} : Set G) →
        Nat.card R ≤ 81 := by
  have hS := h.hS
  have hC := hS.hC
  rcases hv with ⟨hinA, hne⟩ | ⟨hF, hnH⟩
  · obtain ⟨b, hbA, hbv⟩ := hS.exists_A_of_inA hinA
    have hbd : b ∉ Subgroup.zpowers d := fun hb => hne (by rw [← hbv]; exact hS.Phi_z0 hb)
    exact ⟨b, hS.hAQ hbA, hbd, hbv, h.h81 b hbA hbd⟩
  · obtain ⟨c, hh, hhfix, hhom, rfl⟩ := hF
    obtain ⟨m, ⟨hmD, hmQ⟩, rfl⟩ := (h.fix_iff hh).mp hhfix
    have hem : e * m = m * e := hC.comm_of_om_zero h.heQ hmQ (by
      rw [← hS.omega4_Phi h.heQ hmQ]; exact hhom)
    have hmM : m ∈ M := h.hT.hLA.hkerM m hmD (by
      calc e * m * e⁻¹ * m⁻¹ = (m * e) * e⁻¹ * m⁻¹ := by rw [hem]
        _ = 1 := by group)
    have hc0 : c ≠ 0 := by
      intro hc
      apply hnH
      rw [hc, zero_smul, zero_add]
      exact ⟨(h.fix_iff _).mpr ⟨m, ⟨hmD, hmQ⟩, rfl⟩, hhom⟩
    have hvne : c • Phi d a₀ a₁ f₀ f₁ e + Phi d a₀ a₁ f₀ f₁ m ≠ 0 := fun h0 =>
      hnH (by rw [h0]; exact ⟨Matrix.mulVec_zero _, by simp [omega4]⟩)
    have hk : c.val = 1 ∨ c.val = 2 := by
      have h1 := ZMod.val_lt c
      have h2 : c.val ≠ 0 := fun h0 => hc0 ((ZMod.val_eq_zero c).mp h0)
      omega
    have heA := h.hT.heA
    have he3 : e ^ 3 = 1 := h.hT.hAe.2 e heA
    have hfQ : e ^ c.val * m ∈ Q := Q.mul_mem (Q.pow_mem h.heQ _) hmQ
    have hPhif : Phi d a₀ a₁ f₀ f₁ (e ^ c.val * m) =
        c • Phi d a₀ a₁ f₀ f₁ e + Phi d a₀ a₁ f₀ f₁ m := by
      rw [hS.Phi_mul (Q.pow_mem h.heQ _) hmQ, hS.Phi_pow h.heQ,
        ← Nat.cast_smul_eq_nsmul F3, ZMod.natCast_zmod_val]
    have hfd : e ^ c.val * m ∉ Subgroup.zpowers d := fun hf =>
      hvne (by rw [← hPhif]; exact hS.Phi_z0 hf)
    obtain ⟨w, hwe, hwm⟩ := h.hfus m hmM
    have hwf : w * (e ^ c.val * m) * w⁻¹ = e ^ c.val * (w * m * w⁻¹) := by
      have : w * (e ^ c.val * m) * w⁻¹ = (w * e * w⁻¹) ^ c.val * (w * m * w⁻¹) := by
        rw [conj_pow]; group
      rw [this, hwe]
    have hbA : w * (e ^ c.val * m) * w⁻¹ ∈ A := by
      rw [hwf]
      exact A.mul_mem (A.pow_mem heA _) (Subgroup.zpowers_le.mpr h.hT.hdA hwm)
    have hbd : w * (e ^ c.val * m) * w⁻¹ ∉ Subgroup.zpowers d := by
      intro hb
      rw [hwf] at hb
      have hek : e ^ c.val ∈ Subgroup.zpowers d := by
        have h1 := Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hwm)
        rwa [mul_inv_cancel_right] at h1
      apply h.hT.hed
      rcases hk with hk | hk
      · rw [hk, pow_one] at hek; exact hek
      · rw [hk] at hek
        have : e = (e ^ 2) ^ 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, he3, one_mul]
        rw [this]; exact Subgroup.pow_mem _ hek 2
    refine ⟨e ^ c.val * m, hfQ, hfd, hPhif, ?_⟩
    intro R hR3 hRC
    have hR' : R.map (MulAut.conj w).toMonoidHom ≤
        Subgroup.centralizer ({w * (e ^ c.val * m) * w⁻¹} : Set G) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hrf := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc w * r * w⁻¹ * (w * (e ^ c.val * m) * w⁻¹) = w * (r * (e ^ c.val * m)) * w⁻¹ := by
            group
        _ = w * ((e ^ c.val * m) * r) * w⁻¹ := by rw [hrf]
        _ = w * (e ^ c.val * m) * w⁻¹ * (w * r * w⁻¹) := by group
    have := h.h81 _ hbA hbd _ (hR3.map _) hR'
    rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at this

end LineSetup

theorem compat_of_lines {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G}
    (hS : SympBasis A Q d a₀ a₁ f₀ f₁) {D M Y : Fin 4 → Subgroup G} {e t₀ t x : Fin 4 → G}
    (hL : ∀ i, LineSetup A Q (D i) (M i) (Y i) d a₀ a₁ f₀ f₁ (e i) (t₀ i) (t i) (x i))
    (hlv : ∀ i, Phi d a₀ a₁ f₀ f₁ (e i) = lineVec i) :
    Compat (fun i => Mg d a₀ a₁ f₀ f₁ (x i)) (fun i => Mg d a₀ a₁ f₀ f₁ (t i)) := by
  intro g hg hg1 hg3 i v hv hfix
  have hlift : ∃ ĝ ∈ NQ Q d, Mg d a₀ a₁ f₀ f₁ ĝ = g := by
    refine Submonoid.closure_induction
      (motive := fun g _ => ∃ ĝ ∈ NQ Q d, Mg d a₀ a₁ f₀ f₁ ĝ = g) ?_ ?_ ?_ hg
    · rintro g (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨x j, (hL j).hxNQ, rfl⟩
      · exact ⟨t j, (hL j).htNQ, rfl⟩
    · exact ⟨1, (NQ Q d).one_mem, hS.Mg_one⟩
    · rintro g g' _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a * b, (NQ Q d).mul_mem ha hb, hS.Mg_mul ha.1 (NQ_conj_d ha) hb.1⟩
  obtain ⟨ĝ, hĝ, rfl⟩ := hlift
  have h3 : (Mg d a₀ a₁ f₀ f₁ ĝ) ^ 3 = 1 := by rw [pow_three']; exact hg3
  obtain ⟨g', hg', ⟨n, hn⟩, hMg'⟩ := hS.exists_three_elt hĝ h3
  have hv' : BadVec (Phi d a₀ a₁ f₀ f₁ (e i)) (Mg d a₀ a₁ f₀ f₁ (x i)) v := by
    rw [hlv i]; exact hv
  obtain ⟨f, hfQ, hfd, hPhif, hbound⟩ := (hL i).badVec_good hv'
  have hgQ := hS.no_fix3 hfQ hfd hbound hg' ⟨n, hn⟩ (by rw [hMg', hPhif]; exact hfix)
  exact hg1 (by rw [← hMg']; exact hS.Mg_Q hgQ)

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
