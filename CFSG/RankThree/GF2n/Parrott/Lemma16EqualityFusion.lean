module

public import CFSG.RankThree.GF2n.Parrott.Section2CJSigmaQ8
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer
public import CFSG.RankThree.GF2n.Parrott.Lemma16FusionSubgroup
public import CFSG.RankThree.GF2n.Parrott.WMultiplicity

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem conj_commutator_eq_inv_of_mul_self_eq_one {x k : G} (hxx : x * x = 1) :
    x * (x * k * x⁻¹ * k⁻¹) * x⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ := by
  have hxx' : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hxx, inv_one]
  rw [eq_inv_iff_mul_eq_one]
  calc x * (x * k * x⁻¹ * k⁻¹) * x⁻¹ * (x * k * x⁻¹ * k⁻¹)
      = (x * x) * k * (x⁻¹ * x⁻¹) * k⁻¹ := by group
    _ = 1 := by rw [hxx, hxx']; group

omit [Finite G] in
theorem conj_commutator_mul_self_eq_inv {x k : G} (hk2 : x * (k * k) * x⁻¹ = k * k)
    (hc : (k * (x * k * x⁻¹ * k⁻¹) * k⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹) * (x * k * x⁻¹ * k⁻¹) =
      (x * k * x⁻¹ * k⁻¹) * (k * (x * k * x⁻¹ * k⁻¹) * k⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹)) :
    (x * k * x⁻¹ * k⁻¹) * (x * k * x⁻¹ * k⁻¹) =
      (k * (x * k * x⁻¹ * k⁻¹) * k⁻¹ * (x * k * x⁻¹ * k⁻¹)⁻¹)⁻¹ := by
  obtain ⟨j, hj⟩ : ∃ j, x * k * x⁻¹ * k⁻¹ = j := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, k * j * k⁻¹ * j⁻¹ = c := ⟨_, rfl⟩
  rw [hj, hc'] at hc ⊢
  have hxk : x * k * x⁻¹ = j * k := by rw [← hj]; group
  have e1 : x * (k * k) * x⁻¹ = c * (j * j) * (k * k) := by
    calc x * (k * k) * x⁻¹ = (x * k * x⁻¹) * (x * k * x⁻¹) := by group
      _ = j * (k * j * k⁻¹) * (k * k) := by rw [hxk]; group
      _ = j * (c * j) * (k * k) := by rw [← hc']; group
      _ = (j * c) * j * (k * k) := by group
      _ = (c * j) * j * (k * k) := by rw [hc]
      _ = c * (j * j) * (k * k) := by group
  rw [hk2] at e1
  have e2 : c * (j * j) = 1 := by
    calc c * (j * j) = c * (j * j) * (k * k) * (k * k)⁻¹ := by group
      _ = (k * k) * (k * k)⁻¹ := by rw [← e1]
      _ = 1 := mul_inv_cancel _
  calc j * j = c⁻¹ * (c * (j * j)) := by group
    _ = c⁻¹ := by rw [e2, mul_one]

omit [Finite G] in
theorem mul_mem_of_mem_or_mul_mem {A B : Subgroup G} {w : G} (hwA : ∀ a ∈ A, a * w = w * a)
    (hww : w * w = 1) (hAB : ∀ a ∈ A, a ∈ B ∨ a * w ∈ B) :
    ∀ a ∈ A, ∀ a' ∈ A, a ∉ B → a' ∉ B → a * a' ∈ B := by
  intro a ha a' ha' haB ha'B
  have h1 : a * w ∈ B := (hAB a ha).resolve_left haB
  have h2 : a' * w ∈ B := (hAB a' ha').resolve_left ha'B
  have e : a * a' = (a * w) * (a' * w) := by
    calc a * a' = a * a' * (w * w) := by rw [hww, mul_one]
      _ = a * (a' * w) * w := by group
      _ = a * (w * a') * w := by rw [hwA a' ha']
      _ = (a * w) * (a' * w) := by group
  rw [e]
  exact B.mul_mem h1 h2

theorem mul_ne_mul_of_card_eq_four_mul {N T : Subgroup G} (hNT : N ≤ T)
    (hcard : Nat.card T = 4 * Nat.card N) (hNc : ∀ n ∈ N, ∀ r ∈ T, n * r = r * n)
    (hT : ∃ r₁ ∈ T, ∃ r₂ ∈ T, r₁ * r₂ ≠ r₂ * r₁) {a b : G} (ha : a ∈ T) (hb : b ∈ T)
    (haN : a ∉ N) (hbN : b ∉ N) (habN : a⁻¹ * b ∉ N) : a * b ≠ b * a := by
  intro hab
  obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hT
  have hC1 : T ⊓ Subgroup.centralizer ({a} : Set G) = T := by
    refine eq_of_le_of_card_eq_four_mul (fun n hn => ⟨hNT hn, ?_⟩) inf_le_left hcard
      (a := a) (b := b) ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr hab.symm⟩ haN hbN habN
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hNc n hn a ha)
  have hC2 : T ⊓ Subgroup.centralizer ({b} : Set G) = T := by
    refine eq_of_le_of_card_eq_four_mul (fun n hn => ⟨hNT hn, ?_⟩) inf_le_left hcard
      (a := a) (b := b) ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr hab⟩
      ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ haN hbN habN
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hNc n hn b hb)
  have hC3 : T ⊓ Subgroup.centralizer (T : Set G) = T := by
    refine eq_of_le_of_card_eq_four_mul
      (fun n hn => ⟨hNT hn, Subgroup.mem_centralizer_iff.mpr fun r hr => (hNc n hn r hr).symm⟩)
      inf_le_left hcard (a := a) (b := b) ⟨ha, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      ⟨hb, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩ haN hbN habN
    · have : r ∈ T ⊓ Subgroup.centralizer ({a} : Set G) := by rw [hC1]; exact hr
      exact Subgroup.mem_centralizer_singleton_iff.mp this.2
    · have : r ∈ T ⊓ Subgroup.centralizer ({b} : Set G) := by rw [hC2]; exact hr
      exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  have : r₂ ∈ T ⊓ Subgroup.centralizer (T : Set G) := by rw [hC3]; exact hr₂
  exact hne (Subgroup.mem_centralizer_iff.mp this.2 r₁ hr₁)

theorem mem_or_inv_mul_mem_of_conj_mul_inv_mem {N T : Subgroup G} (hNT : N ≤ T)
    (hcard : Nat.card T = 4 * Nat.card N) (hTN : ∀ r ∈ T, ∀ n ∈ N, r * n = n * r) {x : G}
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) {k : G} (hk : k ∈ T) (hkx : x * k * x⁻¹ * k⁻¹ ∉ N)
    {j : G} (hj : j ∈ T) (hjN : j ∉ N) (hjx : x * j * x⁻¹ * j⁻¹ ∈ N) {q : G} (hq : q ∈ T)
    (hqx : x * q * x⁻¹ * q⁻¹ ∈ N) : q ∈ N ∨ j⁻¹ * q ∈ N := by
  by_contra hne
  push Not at hne
  let S : Subgroup G :=
    { carrier := {r | r ∈ T ∧ x * r * x⁻¹ * r⁻¹ ∈ N}
      mul_mem' := by
        rintro r₁ r₂ ⟨hr₁, hd₁⟩ ⟨hr₂, hd₂⟩
        refine ⟨T.mul_mem hr₁ hr₂, ?_⟩
        have e : x * (r₁ * r₂) * x⁻¹ * (r₁ * r₂)⁻¹ =
            (x * r₁ * x⁻¹ * r₁⁻¹) * (r₁ * (x * r₂ * x⁻¹ * r₂⁻¹) * r₁⁻¹) := by group
        rw [e, hTN r₁ hr₁ _ hd₂, mul_inv_cancel_right]
        exact N.mul_mem hd₁ hd₂
      one_mem' := ⟨T.one_mem, by simp⟩
      inv_mem' := by
        rintro r ⟨hr, hd⟩
        refine ⟨T.inv_mem hr, ?_⟩
        have e : x * r⁻¹ * x⁻¹ * r⁻¹⁻¹ = r⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * r := by group
        rw [e, hTN r⁻¹ (T.inv_mem hr) _ (N.inv_mem hd), inv_mul_cancel_right]
        exact N.inv_mem hd }
  have hNS : N ≤ S := fun n hn => ⟨hNT hn, N.mul_mem (hxN n hn) (N.inv_mem hn)⟩
  have hST : S ≤ T := fun r hr => hr.1
  have hS := eq_of_le_of_card_eq_four_mul hNS hST hcard (a := j) (b := q) ⟨hj, hjx⟩ ⟨hq, hqx⟩
    hjN hne.1 hne.2
  have hkS : k ∈ S := by rw [hS]; exact hk
  exact hkx hkS.2

omit [Finite G] in
theorem forall_exists_conj_of_mem_closure {A P : Subgroup G} {x : G} {s : Set G}
    (hsA : s ⊆ A) (hs : ∀ b ∈ s, ∀ a ∈ A, ∃ y ∈ P, y * (x * a) * y⁻¹ = x * (a * b)) :
    ∀ b ∈ Subgroup.closure s, ∀ a ∈ A, ∃ y ∈ P, y * (x * a) * y⁻¹ = x * (a * b) := by
  have hcl : Subgroup.closure s ≤ A := (Subgroup.closure_le A).mpr hsA
  intro b hb
  induction hb using Subgroup.closure_induction with
  | mem b hbs => exact hs b hbs
  | one => exact fun a _ => ⟨1, P.one_mem, by group⟩
  | mul b₁ b₂ hb₁ hb₂ ih₁ ih₂ =>
    intro a ha
    obtain ⟨y₁, hy₁, e₁⟩ := ih₁ a ha
    obtain ⟨y₂, hy₂, e₂⟩ := ih₂ (a * b₁) (A.mul_mem ha (hcl hb₁))
    refine ⟨y₂ * y₁, P.mul_mem hy₂ hy₁, ?_⟩
    calc y₂ * y₁ * (x * a) * (y₂ * y₁)⁻¹ = y₂ * (y₁ * (x * a) * y₁⁻¹) * y₂⁻¹ := by group
      _ = x * (a * (b₁ * b₂)) := by rw [e₁, e₂]; group
  | inv b hb ih =>
    intro a ha
    obtain ⟨y, hy, e⟩ := ih (a * b⁻¹) (A.mul_mem ha (A.inv_mem (hcl hb)))
    refine ⟨y⁻¹, P.inv_mem hy, ?_⟩
    have e' : x * a = y * (x * (a * b⁻¹)) * y⁻¹ := by
      rw [e]; group
    rw [e']; group

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem uvt_inverts_sigma1_mul_sigma2 :
    u * v * t * (sigma1 * sigma2) * (u * v * t)⁻¹ = (sigma1 * sigma2)⁻¹ := by
  have ht : t * (sigma1 * sigma2) * t⁻¹ = sigma1 * sigma2 := by
    calc t * (sigma1 * sigma2) * t⁻¹ = (t * sigma1) * sigma2 * t⁻¹ := by group
      _ = sigma1 * (t * sigma2) * t⁻¹ := by rw [t_commute_sigma1]; group
      _ = sigma1 * (sigma2 * t) * t⁻¹ := by rw [t_commute_sigma2]
      _ = sigma1 * sigma2 := by group
  have hv : v * (sigma1 * sigma2) * v⁻¹ = sigma1⁻¹ * sigma2⁻¹ := by
    calc v * (sigma1 * sigma2) * v⁻¹ = (v * sigma1 * v⁻¹) * (v * sigma2 * v⁻¹) := by group
      _ = sigma1⁻¹ * sigma2⁻¹ := by rw [sigma1_conj_v, sigma2_conj_v]
  have hu2 : u * sigma2 * u⁻¹ = sigma1 := by
    have h := sigma1_mul_u
    calc u * sigma2 * u⁻¹ = sigma1 * u * u⁻¹ := by rw [h]
      _ = sigma1 := by group
  have hu : u * (sigma1⁻¹ * sigma2⁻¹) * u⁻¹ = sigma2⁻¹ * sigma1⁻¹ := by
    calc u * (sigma1⁻¹ * sigma2⁻¹) * u⁻¹ = (u * sigma1 * u⁻¹)⁻¹ * (u * sigma2 * u⁻¹)⁻¹ := by
          group
      _ = sigma2⁻¹ * sigma1⁻¹ := by rw [sigma1_conj_u, hu2]
  calc u * v * t * (sigma1 * sigma2) * (u * v * t)⁻¹
      = u * (v * (t * (sigma1 * sigma2) * t⁻¹) * v⁻¹) * u⁻¹ := by group
    _ = sigma2⁻¹ * sigma1⁻¹ := by rw [ht, hv, hu]
    _ = (sigma1 * sigma2)⁻¹ := by rw [mul_inv_rev]

theorem conj_mul_sigma2_mul_mem_J {σ₂ : ↥(H z)}
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    {x : G} (hxH : x ∈ H z)
    (hqx : qH D ⟨x, hxH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) :
    x * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * x⁻¹ *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) ∈ J z := by
  let y : ↥(H z) := ⟨x, hxH⟩ * (sigma1Nine (z := z) D * σ₂) * ⟨x, hxH⟩⁻¹ *
    (sigma1Nine (z := z) D * σ₂)
  have hy : qH D y = 1 := by
    simp only [y, map_mul, map_inv, hqx, qH_sigma1Nine, hq₂]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [uvt_inverts_sigma1_mul_sigma2, inv_mul_cancel]
  have hyJ : y ∈ (J z).subgroupOf (H z) := (J_mem_iff D y).mpr hy
  exact Subgroup.mem_subgroupOf.mp hyJ

theorem conj_mem_CJ_mul_inv_inf_commutator (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {x : G} (hxH : x ∈ H z)
    (hxσ : x ∈ Subgroup.centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    {q : G} (hq : q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    x * q * x⁻¹ ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  obtain ⟨hqs, hqJ⟩ := mem_CJ.mp hq.1
  refine ⟨mem_CJ.mpr ⟨?_, (Subgroup.mem_normalizer_iff.mp (hHN hxH) q).mp hqJ⟩,
    commutator_sigma1Nine_conj_mem (z := z) (D := D) h hEq hσ₂ hq₂ hcomm.eq.symm ⟨x, hxH⟩ q hq.2⟩
  have hx' : x * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hxσ
  have hq' : q * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * q :=
    Subgroup.mem_centralizer_singleton_iff.mp hqs
  have hxi : x⁻¹ * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x⁻¹ := by
    calc x⁻¹ * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        = x⁻¹ * (((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) * x⁻¹ := by rw [hx']
      _ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * q * x⁻¹ * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
      = x * q * (x⁻¹ * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) := by group
    _ = x * (q * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) * x⁻¹ := by rw [hxi]; group
    _ = x * (((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * q) * x⁻¹ := by rw [hq']
    _ = (x * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) * q * x⁻¹ := by group
    _ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * (x * q * x⁻¹) := by rw [hx']; group

omit [Finite G]
  in
theorem conj_mul_conj_inv_eq_of_conj_eq {x ω q ε c c' d : G}
    (hxω : x * ω * x⁻¹ = ε * ω⁻¹) (hxq : x * q * x⁻¹ = c * q)
    (hxr : x * (ω * q * ω⁻¹) * x⁻¹ = c' * (ω * q * ω⁻¹))
    (hd : ε * (ω⁻¹ * q * ω) * ε⁻¹ = d * (ω⁻¹ * q * ω))
    (hcω : ω * c = c * ω) (hcε : ε * c = c * ε) :
    c' * (ω * q * ω⁻¹) = c * d * (ω⁻¹ * q * ω) := by
  have hcω' : ω⁻¹ * c = c * ω⁻¹ := (Commute.inv_left hcω).eq
  calc c' * (ω * q * ω⁻¹) = x * (ω * q * ω⁻¹) * x⁻¹ := hxr.symm
    _ = (x * ω * x⁻¹) * (x * q * x⁻¹) * (x * ω * x⁻¹)⁻¹ := by group
    _ = ε * (ω⁻¹ * c) * q * ω * ε⁻¹ := by rw [hxω, hxq]; group
    _ = (ε * c) * (ω⁻¹ * q * ω) * ε⁻¹ := by rw [hcω']; group
    _ = c * (ε * (ω⁻¹ * q * ω) * ε⁻¹) := by rw [hcε]; group
    _ = c * d * (ω⁻¹ * q * ω) := by rw [hd]; group

omit [Finite G]
  in
theorem conj_mul_inv_eq_mul_self_of_mul_mul_eq_one {ω q m : G} (hω3 : ω * ω * ω = 1)
    (hmω : ω * m = m * ω) (hm : ω * q * ω⁻¹ * (ω⁻¹ * q * ω)⁻¹ = m) :
    ω * q * ω⁻¹ * q⁻¹ = m * m := by
  have hm' : ω * m * ω⁻¹ = m := by rw [hmω]; group
  calc ω * q * ω⁻¹ * q⁻¹ = ω * q * (ω * ω * ω)⁻¹ * ω⁻¹ * q⁻¹ := by rw [hω3]; group
    _ = ω * q * ω⁻¹ * ω⁻¹ * q⁻¹ * 1 * q * ω⁻¹ * ω⁻¹ * q⁻¹ := by group
    _ = ω * q * ω⁻¹ * ω⁻¹ * q⁻¹ * (ω * ω * ω) * q * ω⁻¹ * ω⁻¹ * q⁻¹ := by rw [hω3]
    _ = m * (ω * m * ω⁻¹) := by rw [← hm]; group
    _ = m * m := by rw [hm']

theorem exists_conj_mul_inv_not_mem_zpowers (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {x : G} (hxH : x ∈ H z)
    (hqx : qH D ⟨x, hxH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) :
    ∃ k ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      x * k * x⁻¹ * k⁻¹ ∉ Subgroup.zpowers z := by
  by_contra hall
  push Not at hall
  set Q : Subgroup G := CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQ
  have hω3 : ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]; exact pow_orderOf_eq_one _
    have h2 : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one _
    have : (sigma1Nine (z := z) D * σ₂) ^ 3 = 1 := by rw [hcomm.mul_pow, h1, h2, one_mul]
    rw [← pow_three']
    exact congrArg Subtype.val this
  set ω : G := ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) with hω
  have hωH : ω ∈ H z := (sigma1Nine (z := z) D * σ₂).2
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hcomJ : ∀ r₁ ∈ J z, ∀ r₂ ∈ J z, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers z := by
    intro r₁ hr₁ r₂ hr₂
    rw [← h.2.2.1]
    have := Subgroup.commutator_mem_commutator hr₁ hr₂
    rwa [commutatorElement_def] at this
  have hQJ : ∀ r ∈ Q, r ∈ J z := fun r hr => (mem_CJ.mp hr.1).2
  have hωσ : ω ∈ Subgroup.centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : Commute (sigma1Nine (z := z) D * σ₂) (sigma1Nine (z := z) D * σ₂⁻¹) :=
      Commute.mul_left ((Commute.refl _).mul_right hcomm.inv_right)
        (hcomm.symm.mul_right (Commute.refl _).inv_right)
    exact congrArg Subtype.val hc.eq
  have hωQ : ∀ r ∈ Q, ω * r * ω⁻¹ ∈ Q := fun r hr =>
    conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq hωH hωσ hr
  have hωiQ : ∀ r ∈ Q, ω⁻¹ * r * ω ∈ Q := by
    intro r hr
    have := conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq
      (inv_mem hωH) (Subgroup.inv_mem _ hωσ) hr
    rwa [inv_inv] at this
  have hεJ : x * ω * x⁻¹ * ω ∈ J z := conj_mul_sigma2_mul_mem_J (z := z) D hq₂ hxH hqx
  have hle : Q ≤ Subgroup.zpowers z := by
    intro q hq
    apply mem_zpowers_of_conj_mul_inv_mem_zpowers (z := z) D h hcomm hq.1 hq.2
    have hrQ : ω * q * ω⁻¹ ∈ Q := hωQ q hq
    have hq'Q : ω⁻¹ * q * ω ∈ Q := hωiQ q hq
    obtain ⟨c, hc_eq⟩ : ∃ c, x * q * x⁻¹ * q⁻¹ = c := ⟨_, rfl⟩
    obtain ⟨c', hc'_eq⟩ : ∃ c', x * (ω * q * ω⁻¹) * x⁻¹ * (ω * q * ω⁻¹)⁻¹ = c' := ⟨_, rfl⟩
    obtain ⟨ε, hε_eq⟩ : ∃ ε, x * ω * x⁻¹ * ω = ε := ⟨_, rfl⟩
    obtain ⟨d, hd_eq⟩ : ∃ d, ε * (ω⁻¹ * q * ω) * ε⁻¹ * (ω⁻¹ * q * ω)⁻¹ = d := ⟨_, rfl⟩
    have hc : c ∈ Subgroup.zpowers z := hc_eq ▸ hall q hq
    have hc' : c' ∈ Subgroup.zpowers z := hc'_eq ▸ hall _ hrQ
    have hεJ' : ε ∈ J z := hε_eq ▸ hεJ
    have hd : d ∈ Subgroup.zpowers z := hd_eq ▸ hcomJ _ hεJ' _ (hQJ _ hq'Q)
    have key := conj_mul_conj_inv_eq_of_conj_eq (x := x) (ω := ω) (q := q) (ε := ε) (c := c)
      (c' := c') (d := d) (by rw [← hε_eq]; group) (by rw [← hc_eq]; group)
      (by rw [← hc'_eq]; group) (by rw [← hd_eq]; group) (hcent c hc ω hωH)
      (hcent c hc ε (J_le_H hεJ'))
    have hm' : ω * q * ω⁻¹ * (ω⁻¹ * q * ω)⁻¹ = c'⁻¹ * c * d := by
      calc ω * q * ω⁻¹ * (ω⁻¹ * q * ω)⁻¹
          = c'⁻¹ * (c' * (ω * q * ω⁻¹)) * (ω⁻¹ * q * ω)⁻¹ := by group
        _ = c'⁻¹ * (c * d * (ω⁻¹ * q * ω)) * (ω⁻¹ * q * ω)⁻¹ := by rw [key]
        _ = c'⁻¹ * c * d := by group
    have hm : c'⁻¹ * c * d ∈ Subgroup.zpowers z := mul_mem (mul_mem (inv_mem hc') hc) hd
    rw [conj_mul_inv_eq_mul_self_of_mul_mul_eq_one hω3 (hcent _ hm ω hωH) hm']
    exact mul_mem hm hm
  have h8 := card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq
  have h2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, h.1]
  have := Subgroup.card_le_of_le hle
  rw [← hQ] at h8
  omega

theorem conj_mem_CJ_sigma1Nine (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {x : G} (hxH : x ∈ H z)
    {e : G} (he : e ∈ CJ z (sigma1Nine (z := z) D : G)) :
    x * e * x⁻¹ ∈ CJ z (sigma1Nine (z := z) D : G) := by
  have hN0 := J0sub_normal (z := z) (D := D) h hEq hσ₂ hq₂
  obtain ⟨hes, heJ⟩ := mem_CJ.mp he
  have hmem : (⟨e, J_le_H heJ⟩ : ↥(H z)) ∈ J0sub (z := z) D := by
    rw [mem_J0sub_iff' D]
    exact ⟨heJ, Subgroup.mem_centralizer_singleton_iff.mp hes⟩
  have hc := hN0.conj_mem _ hmem ⟨x, hxH⟩
  rw [mem_J0sub_iff' D] at hc
  obtain ⟨hcJ, hcc⟩ := hc
  refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · simpa using hcc
  · simpa using hcJ

theorem centerIn_le_CJ_sigma1Nine (h : Tim79a.ParrottHyp z) :
    centerIn (J z) ≤ CJ z (sigma1Nine (z := z) D : G) := fun _ hζ =>
  mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (sigma_commute_of_mem_centerIn_of (z := z) (conjZ_sigma1Nine h D) hζ).eq.symm, hζ.1⟩

omit
  hN in
theorem exists_mem_centerIn_mem_or_mul_mem (h : Tim79a.ParrottHyp z) :
    ∃ z₁ : G, z₁ ∈ centerIn (J z) ∧ z₁ ∉ Subgroup.zpowers z ∧ z₁ * z₁ = 1 ∧
      ∀ ζ ∈ centerIn (J z), ζ ∈ Subgroup.zpowers z ∨ ζ * z₁ ∈ Subgroup.zpowers z := by
  obtain ⟨z₁, hZ, hz₁, hord⟩ := exists_z1 h
  have hz₁Z : z₁ ∈ centerIn (J z) := by
    rw [hZ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  have hz₁H : z₁ ∈ H z := J_le_H hz₁Z.1
  have hz₁1 : z₁ * z₁ = 1 := by rw [← sq, ← hord]; exact pow_orderOf_eq_one z₁
  refine ⟨z₁, hz₁Z, hz₁, hz₁1, fun ζ hζ => ?_⟩
  rw [hZ] at hζ
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers z₁, Commute a b := by
    intro a ha b hb
    have hbH : b ∈ H z := Subgroup.zpowers_le_of_mem hz₁H hb
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.zpowers_le_of_mem (z_centralizes_H h) ha) b hbH).symm
  obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hζ
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord).mp hb with rfl | rfl
  · left; rwa [mul_one]
  · right; rwa [mul_assoc, hz₁1, mul_one]

omit
  hN in
theorem mul_self_eq_one_of_mem_centerIn (h : Tim79a.ParrottHyp z) {ζ : G}
    (hζ : ζ ∈ centerIn (J z)) : ζ * ζ = 1 := by
  obtain ⟨z₁, hz₁Z, -, hz₁1, hdec⟩ := exists_mem_centerIn_mem_or_mul_mem h
  rcases hdec ζ hζ with hm | hm
  · exact sq_eq_one_of_mem_zpowers h hm
  · have hc : z₁ * (ζ * z₁) = (ζ * z₁) * z₁ :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hm) z₁ (J_le_H hz₁Z.1)
    calc ζ * ζ = (ζ * z₁) * (z₁ * (ζ * z₁)) * z₁ := by
          rw [show (ζ * z₁) * (z₁ * (ζ * z₁)) * z₁ = ζ * (z₁ * z₁) * ζ * (z₁ * z₁) by group,
            hz₁1]; group
      _ = (ζ * z₁) * (ζ * z₁) * (z₁ * z₁) := by rw [hc]; group
      _ = 1 := by rw [sq_eq_one_of_mem_zpowers h hm, hz₁1, one_mul]

omit
  hN in
theorem conj_mem_centerIn_J {g : G} (hg : g ∈ H z) {ζ : G} (hζ : ζ ∈ centerIn (J z)) :
    g * ζ * g⁻¹ ∈ centerIn (J z) := by
  have := (conjZ z ⟨g, hg⟩ ⟨ζ, hζ⟩).2
  rwa [conjZ_apply_coe] at this

omit
  hN in
theorem conj_eq_self_of_mem_centerIn (h : Tim79a.ParrottHyp z) {P : Subgroup G} {x j : G}
    (hxH : x ∈ H z) (hjP : j ∈ P) (hjJ : j ∈ J z) (hjx : x * j * x⁻¹ = j * z) (hjj : j * j = z)
    (hZP : centerIn (J z) ≤ P)
    (hAE : IsElemAbelian 2 (P ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∀ ζ ∈ centerIn (J z), x * ζ * x⁻¹ = ζ := by
  obtain ⟨z₁, hz₁Z, hz₁, -, hdec⟩ := exists_mem_centerIn_mem_or_mul_mem h
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hz2 : orderOf z = 2 := h.1
  have hz1 : z ≠ 1 := by
    intro hz; rw [hz, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  intro ζ hζ
  have hxζ : x * ζ * x⁻¹ ∈ centerIn (J z) := conj_mem_centerIn_J hxH hζ
  have hm : x * ζ * x⁻¹ * ζ⁻¹ ∈ Subgroup.zpowers z := by
    rcases hdec ζ hζ with h1 | h1
    · rw [hcent ζ h1 x hxH, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · rcases hdec _ hxζ with h2 | h2
      · exfalso
        apply hz₁
        have hζz : ζ ∈ Subgroup.zpowers z := by
          have : ζ = x⁻¹ * (x * ζ * x⁻¹) * x := by group
          rw [this, hcent _ h2 x⁻¹ (inv_mem hxH), inv_mul_cancel_right]
          exact h2
        have : z₁ = ζ⁻¹ * (ζ * z₁) := by group
        rw [this]
        exact mul_mem (inv_mem hζz) h1
      · have : x * ζ * x⁻¹ * ζ⁻¹ = (x * ζ * x⁻¹ * z₁) * (ζ * z₁)⁻¹ := by group
        rw [this]
        exact mul_mem h2 (inv_mem h1)
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hm with h1 | h1
  · calc x * ζ * x⁻¹ = x * ζ * x⁻¹ * ζ⁻¹ * ζ := by group
      _ = ζ := by rw [h1, one_mul]
  · exfalso
    have hxζ' : x * ζ * x⁻¹ = z * ζ := by
      calc x * ζ * x⁻¹ = x * ζ * x⁻¹ * ζ⁻¹ * ζ := by group
        _ = z * ζ := by rw [h1]
    have hzz : z * z = 1 := sq_eq_one_of_mem_zpowers h (Subgroup.mem_zpowers z)
    have hjζ : j * ζ ∈ P ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine ⟨P.mul_mem hjP (hZP hζ), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have e : x * (j * ζ) * x⁻¹ = j * ζ := by
        calc x * (j * ζ) * x⁻¹ = (x * j * x⁻¹) * (x * ζ * x⁻¹) := by group
          _ = j * (z * z) * ζ := by rw [hjx, hxζ']; group
          _ = j * ζ := by rw [hzz, mul_one]
      calc j * ζ * x = x * (j * ζ) * x⁻¹ * x := by rw [e]
        _ = x * (j * ζ) := by group
    have hsq := hAE.2 _ hjζ
    have hζj : ζ * j = j * ζ := (Subgroup.mem_centralizer_iff.mp hζ.2 j hjJ).symm
    apply hz1
    calc z = j * j * (ζ * ζ) := by rw [hjj, mul_self_eq_one_of_mem_centerIn h hζ, mul_one]
      _ = j * (ζ * j) * ζ := by rw [hζj]; group
      _ = (j * ζ) ^ 2 := by rw [sq]; group
      _ = 1 := hsq

theorem conj_eq_self_of_mem_centerIn_of_mem_H (h : Tim79a.ParrottHyp z) {x : G}
    (hxH : x ∈ H z)
    (hxQ : qH D ⟨x, hxH⟩ ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    (hxZ : ∀ ζ ∈ centerIn (J z), x * ζ * x⁻¹ = ζ) {g : G} (hg : g ∈ H z) :
    ∀ ζ ∈ centerIn (J z), g * ζ * g⁻¹ = ζ := by
  have key : ∀ g' : ↥(H z), qH D g' ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup →
      ∀ ζ ∈ centerIn (J z), (g' : G) * ζ * (g' : G)⁻¹ = ζ := by
    intro g' hg' ζ hζ
    have h1 := conjZ_eq_one_of_mem_Q (z := z) D h g' hg'
    have h2 := conjZ_apply_coe g' ⟨ζ, hζ⟩
    rw [h1] at h2
    exact h2.symm
  intro ζ hζ
  by_cases hgQ : qH D ⟨g, hg⟩ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
  · exact key ⟨g, hg⟩ hgQ ζ hζ
  · have hgx : qH D (⟨g, hg⟩ * ⟨x, hxH⟩) ∈
        QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two index_QP45]
      exact iff_of_false hgQ hxQ
    have := key _ hgx ζ hζ
    simp only [Subgroup.coe_mul] at this
    calc g * ζ * g⁻¹ = g * (x * ζ * x⁻¹) * g⁻¹ := by rw [hxZ ζ hζ]
      _ = g * x * ζ * (g * x)⁻¹ := by group
      _ = ζ := this

theorem conj_mul_inv_mem_centerIn_of_mem_CJ_sigma1Nine (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : G} (hgH : g ∈ H z)
    (hgQ : qH D ⟨g, hgH⟩ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {e : G} (he : e ∈ CJ z (sigma1Nine (z := z) D : G)) :
    g * e * g⁻¹ * e⁻¹ ∈ centerIn (J z) := by
  have hJ0 := J0sub_normal (z := z) (D := D) h hEq hσ₂ hq₂
  have hcomm := QP45_subgroupOf_le_commutator_QA45 hgQ
  have hmap : (_root_.commutator ↥(H z)).map (qH D) =
      _root_.commutator ↥QA45.originalSubgroup := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (qH_surjective D)]
  rw [← hmap] at hcomm
  obtain ⟨h'', hh'', hq⟩ := Subgroup.mem_map.mp hcomm
  have hh'G : (h'' : G) ∈ ⁅H z, H z⁆ := by
    have := Subgroup.mem_map_of_mem (H z).subtype hh''
    rwa [Subgroup.map_subtype_commutator] at this
  obtain ⟨j, hj⟩ : ∃ j, ((h''⁻¹ * ⟨g, hgH⟩ : ↥(H z)) : G) = j := ⟨_, rfl⟩
  have hjJ : j ∈ J z := by
    have : h''⁻¹ * ⟨g, hgH⟩ ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul, map_inv, hq, inv_mul_cancel]
    rw [← hj]
    exact Subgroup.mem_subgroupOf.mp this
  have hg : g = (h'' : G) * j := by
    rw [← hj]; simp
  have heJ : e ∈ J z := (mem_CJ.mp he).2
  have h1 : (h'' : G) * e * (h'' : G)⁻¹ * e⁻¹ ∈ centerIn (J z) := by
    have := derived_commutator_CJ_le_center (z := z) (D := D) h hJ0
      (Subgroup.commutator_mem_commutator hh'G he)
    rwa [commutatorElement_def] at this
  have h2 : j * e * j⁻¹ * e⁻¹ ∈ Subgroup.zpowers z := by
    rw [← h.2.2.1]
    have := Subgroup.commutator_mem_commutator hjJ heJ
    rwa [commutatorElement_def] at this
  have hzZ : Subgroup.zpowers z ≤ centerIn (J z) :=
    Subgroup.zpowers_le_of_mem ⟨z_mem_J h, z_centralizes_J h⟩
  have hc : (h'' : G) * (j * e * j⁻¹ * e⁻¹) = (j * e * j⁻¹ * e⁻¹) * (h'' : G) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) h2) _ h''.2
  have e1 : g * e * g⁻¹ * e⁻¹ =
      (j * e * j⁻¹ * e⁻¹) * ((h'' : G) * e * (h'' : G)⁻¹ * e⁻¹) := by
    rw [hg]
    calc (h'' : G) * j * e * ((h'' : G) * j)⁻¹ * e⁻¹
        = (h'' : G) * (j * e * j⁻¹ * e⁻¹) * e * (h'' : G)⁻¹ * e⁻¹ := by group
      _ = (j * e * j⁻¹ * e⁻¹) * ((h'' : G) * e * (h'' : G)⁻¹ * e⁻¹) := by rw [hc]; group
  rw [e1]
  exact (centerIn (J z)).mul_mem (hzZ h2) h1

theorem conj_mul_inv_mem_zpowers_of_conj_mem_CJ_mul_inv_inf_commutator
    (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : G} (hgH : g ∈ H z)
    (hgQ : ∀ q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆,
      g * q * g⁻¹ ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆)
    (hgg : g * g ∈ J z)
    (hgω : g * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * g⁻¹ *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹ ∈ J z)
    {q : G} (hq : q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    g * q * g⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  by_contra hq0
  set Q : Subgroup G := CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQ
  set ω : G := ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) with hω
  have hωH : ω ∈ H z := (sigma1Nine (z := z) D * σ₂).2
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hcomJ : ∀ r₁ ∈ J z, ∀ r₂ ∈ J z, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers z := by
    intro r₁ hr₁ r₂ hr₂
    rw [← h.2.2.1]
    have := Subgroup.commutator_mem_commutator hr₁ hr₂
    rwa [commutatorElement_def] at this
  have hQJ : ∀ r ∈ Q, r ∈ J z := fun r hr => (mem_CJ.mp hr.1).2
  have hzQ : z ∈ Q := by
    have hzA : z ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      rw [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
      exact Subgroup.mem_zpowers z
    refine ⟨mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, z_mem_J h⟩, hzA.2⟩
    exact (hcent z (Subgroup.mem_zpowers z) _ (sigma1Nine (z := z) D * σ₂⁻¹).2).symm
  have hQcard : Nat.card Q = 4 * Nat.card (Subgroup.zpowers z) := by
    rw [hQ, card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq, Nat.card_zpowers,
      h.1]
  have hωσ : ω ∈ Subgroup.centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : Commute (sigma1Nine (z := z) D * σ₂) (sigma1Nine (z := z) D * σ₂⁻¹) :=
      Commute.mul_left ((Commute.refl _).mul_right hcomm.inv_right)
        (hcomm.symm.mul_right (Commute.refl _).inv_right)
    exact congrArg Subtype.val hc.eq
  have hωQ : ∀ r ∈ Q, ω * r * ω⁻¹ ∈ Q := fun r hr =>
    conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq hωH hωσ hr
  obtain ⟨r₀, hr₀_eq⟩ : ∃ r, g * q * g⁻¹ * q⁻¹ = r := ⟨_, rfl⟩
  have hr₀z : r₀ ∉ Subgroup.zpowers z := hr₀_eq ▸ hq0
  have hr₀Q : r₀ ∈ Q := hr₀_eq ▸ Q.mul_mem (hgQ q hq) (Q.inv_mem hq)
  have hr₀x : g * r₀ * g⁻¹ * r₀⁻¹ ∈ Subgroup.zpowers z := by
    have e : g * r₀ * g⁻¹ * r₀⁻¹ = ((g * g) * q * (g * g)⁻¹ * q⁻¹) *
        ((q * (g * q * g⁻¹)⁻¹) * (q * (g * q * g⁻¹)⁻¹)) := by rw [← hr₀_eq]; group
    rw [e]
    exact mul_mem (hcomJ _ hgg _ (hQJ q hq))
      (sq_mem_zpowers_z h (mul_mem (hQJ q hq) (inv_mem (hQJ _ (hgQ q hq)))))
  obtain ⟨r₁, hr₁_eq⟩ : ∃ r, ω * r₀ * ω⁻¹ = r := ⟨_, rfl⟩
  have hr₁Q : r₁ ∈ Q := hr₁_eq ▸ hωQ r₀ hr₀Q
  have hr₁x : g * r₁ * g⁻¹ * r₁⁻¹ ∈ Subgroup.zpowers z := by
    obtain ⟨ε, hε_eq⟩ : ∃ ε, g * ω * g⁻¹ * ω⁻¹ = ε := ⟨_, rfl⟩
    obtain ⟨ζ₀, hζ₀_eq⟩ : ∃ ζ, g * r₀ * g⁻¹ * r₀⁻¹ = ζ := ⟨_, rfl⟩
    obtain ⟨d, hd_eq⟩ : ∃ d, ε * r₁ * ε⁻¹ * r₁⁻¹ = d := ⟨_, rfl⟩
    have hεJ : ε ∈ J z := hε_eq ▸ hgω
    have hζ₀ : ζ₀ ∈ Subgroup.zpowers z := hζ₀_eq ▸ hr₀x
    have hd : d ∈ Subgroup.zpowers z := hd_eq ▸ hcomJ ε hεJ r₁ (hQJ r₁ hr₁Q)
    have hεω : ε * ω ∈ H z := mul_mem (J_le_H hεJ) hωH
    have e1 : g * ω * g⁻¹ = ε * ω := by rw [← hε_eq]; group
    have e2 : g * r₀ * g⁻¹ = ζ₀ * r₀ := by rw [← hζ₀_eq]; group
    have e : g * r₁ * g⁻¹ * r₁⁻¹ = ζ₀ * d := by
      calc g * r₁ * g⁻¹ * r₁⁻¹
          = (g * ω * g⁻¹) * (g * r₀ * g⁻¹) * (g * ω * g⁻¹)⁻¹ * r₁⁻¹ := by
            rw [← hr₁_eq]; group
        _ = ((ε * ω) * ζ₀) * r₀ * (ε * ω)⁻¹ * r₁⁻¹ := by rw [e1, e2]; group
        _ = (ζ₀ * (ε * ω)) * r₀ * (ε * ω)⁻¹ * r₁⁻¹ := by rw [hcent ζ₀ hζ₀ _ hεω]
        _ = ζ₀ * (ε * (ω * r₀ * ω⁻¹) * ε⁻¹ * r₁⁻¹) := by group
        _ = ζ₀ * d := by rw [hr₁_eq, hd_eq]
    rw [e]; exact mul_mem hζ₀ hd
  have hr₁z : r₁ ∉ Subgroup.zpowers z := by
    intro hr₁z
    apply hr₀z
    have : r₀ = ω⁻¹ * r₁ * ω := by rw [← hr₁_eq]; group
    rw [this, hcent r₁ hr₁z _ (inv_mem hωH), mul_assoc, inv_mul_cancel, mul_one]
    exact hr₁z
  have hr₀r₁ : r₀⁻¹ * r₁ ∉ Subgroup.zpowers z := by
    intro hm
    apply hr₀z
    apply mem_zpowers_of_conj_mul_inv_mem_zpowers (z := z) D h hcomm hr₀Q.1 hr₀Q.2
    rw [← hω, hr₁_eq]
    have e : r₁ * r₀⁻¹ = r₀ * (r₀⁻¹ * r₁) * r₀⁻¹ := by group
    rw [e, hcent _ hm r₀ (J_le_H (hQJ r₀ hr₀Q)), mul_inv_cancel_right]
    exact hm
  have hzpQ : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le_of_mem hzQ
  have hTN : ∀ r ∈ Q, ∀ n ∈ Subgroup.zpowers z, r * n = n * r := fun r hr n hn =>
    hcent n hn r (J_le_H (hQJ r hr))
  have hxN : ∀ n ∈ Subgroup.zpowers z, g * n * g⁻¹ ∈ Subgroup.zpowers z := fun n hn => by
    rw [hcent n hn g hgH, mul_inv_cancel_right]; exact hn
  rcases mem_or_inv_mul_mem_of_conj_mul_inv_mem hzpQ hQcard hTN hxN hq hq0 hr₀Q hr₀z hr₀x
    hr₁Q hr₁x with h1 | h1
  · exact hr₁z h1
  · exact hr₀r₁ h1

omit [Finite G]
  hN in
theorem conj_commutator_eq_of_conj_mul_inv_mem_centerIn {g x k : G} (hgx : g * x = x * g)
    (hk : g * k * g⁻¹ * k⁻¹ ∈ centerIn (J z))
    (hxZ : ∀ ζ ∈ centerIn (J z), x * ζ * x⁻¹ = ζ) (hδJ : x * k * x⁻¹ * k⁻¹ ∈ J z) :
    g * (x * k * x⁻¹ * k⁻¹) * g⁻¹ = x * k * x⁻¹ * k⁻¹ := by
  obtain ⟨ζ, hζ_eq⟩ : ∃ ζ, g * k * g⁻¹ * k⁻¹ = ζ := ⟨_, rfl⟩
  rw [hζ_eq] at hk
  have hgk : g * k * g⁻¹ = ζ * k := by rw [← hζ_eq]; group
  have hgxg : g * x * g⁻¹ = x := by rw [hgx]; group
  have hζδ : ζ * (x * k * x⁻¹ * k⁻¹) = (x * k * x⁻¹ * k⁻¹) * ζ :=
    (Subgroup.mem_centralizer_iff.mp hk.2 _ hδJ).symm
  calc g * (x * k * x⁻¹ * k⁻¹) * g⁻¹
      = (g * x * g⁻¹) * (g * k * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * k * g⁻¹)⁻¹ := by group
    _ = (x * ζ * x⁻¹) * (x * k * x⁻¹ * k⁻¹) * ζ⁻¹ := by rw [hgxg, hgk]; group
    _ = ζ * (x * k * x⁻¹ * k⁻¹) * ζ⁻¹ := by rw [hxZ ζ hk]
    _ = x * k * x⁻¹ * k⁻¹ := by rw [hζδ]; group

section Model

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

theorem mul_self_eq_one_of_mem_centralizer_uvt_of_mem_QP45 {a : A45}
    (ha : a ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
      Subgroup.centralizer ({uA * vA * tA} : Set A45))
    (hQ : a ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) {n : ℕ}
    (hn : a ^ 2 ^ n = 1) : a * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have huvt : (uA * vA * tA) * (uA * vA * tA) = 1 := by
    have h1 : (uA * vA) * (uA * vA) = 1 := by
      rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
    have h2 : Commute (uA * vA) tA := (hut.mul_right hvt).symm
    rw [Commute.mul_mul_mul_comm h2.symm (uA * vA) tA, h1, htt, one_mul]
  have huvtQ : uA * vA * tA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    uvtA_not_mem_QP45
  have huvtC : uA * vA * tA ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext uvt_mul_sigma1_mul_sigma2_inv)
  have haw := ha.2
  obtain ⟨w, hw⟩ : ∃ w, uA * vA * tA = w := ⟨_, rfl⟩
  rw [hw] at huvt huvtQ huvtC haw
  have huvt1 : w ≠ 1 := by
    intro h1
    apply huvtQ
    rw [h1]
    exact Subgroup.one_mem _
  have hord2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact huvt) huvt1
  have hcomm : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers w, Commute p q := by
    intro p hp q hq
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord2).mp hq with rfl | rfl
    · exact Commute.one_right p
    · exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le_of_mem haw hp)
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord2).mp hy2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd (Subgroup.zpowers_le_of_mem hQ hy1) huvtQ
  have hcard := CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj
  rw [Nat.card_zpowers, Nat.card_zpowers, hord, hord2] at hcard
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers w ≤
      Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) :=
    sup_le (Subgroup.zpowers_le_of_mem ha.1) (Subgroup.zpowers_le_of_mem huvtC)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  have h108 : Nat.card (Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45)) = 108 :=
    card_centralizer_sigma1_mul_sigma2_inv_QA45
  rw [h108] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have h8 : 2 ^ 2 * 2 ∣ 2 ^ k * 2 :=
      Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) 2
    have := Nat.dvd_trans h8 hdvd
    norm_num at this
  have h2 : orderOf a ∣ 2 := by
    rw [hord]
    exact (Nat.pow_dvd_pow 2 hk1).trans (by norm_num)
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem exists_conj_eq_one_or_eq_t_of_mem_QP45 {a : A45}
    (ha : a ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
      Subgroup.centralizer ({uA * vA * tA} : Set A45))
    (hQ : a ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) {n : ℕ}
    (hn : a ^ 2 ^ n = 1) :
    ∃ d ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
        Subgroup.centralizer ({uA * vA * tA} : Set A45),
      d⁻¹ * a * d = 1 ∨ d⁻¹ * a * d = tA := by
  have h2 := mul_self_eq_one_of_mem_centralizer_uvt_of_mem_QP45 ha hQ hn
  obtain ⟨d, hd, hconj⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer_uvt ha h2
  refine ⟨d, hd, ?_⟩
  have hN : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  have hmQ : d⁻¹ * a * d ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    have := hN.conj_mem a hQ d⁻¹
    rwa [inv_inv] at this
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have htuv : Commute tA (uA * vA) := hut.mul_right hvt
  have huvsq : (uA * vA) * (uA * vA) = 1 := by
    rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
  have htQ : tA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    Subgroup.mem_subgroupOf.mpr t_mem_Q
  have ht1 : tA ≠ 1 := by
    intro h1
    have h1' : ((tA : A45) : Equiv.Perm (Fin 45)) = ((1 : A45) : Equiv.Perm (Fin 45)) :=
      congrArg Subtype.val h1
    exact t_ne_one h1'
  have huv1 : uA * vA ≠ 1 := by
    intro h1
    apply uvA_not_mem_QP45
    rw [h1]
    exact Subgroup.one_mem _
  have hord_t : orderOf tA = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hord_uv : orderOf (uA * vA) = 2 := orderOf_eq_prime (by rw [sq]; exact huvsq) huv1
  obtain ⟨m, k, hmk⟩ := (CFSG.GroupTheory.mem_closure_pair_iff_of_commute htuv).mp hconj
  rw [← hmk] at hmQ ⊢
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord_t).mp (Subgroup.zpow_mem_zpowers tA m)
    with h1 | h1 <;>
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hord_uv).mp
    (Subgroup.zpow_mem_zpowers (uA * vA) k) with h2 | h2 <;>
  rw [h1, h2] at hmQ ⊢
  · left; rw [mul_one]
  · exfalso; apply uvA_not_mem_QP45; rwa [one_mul] at hmQ
  · right; rw [mul_one]
  · exfalso
    apply uvA_not_mem_QP45
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ htQ) hmQ
    rwa [inv_mul_cancel_left] at this

end Model

theorem conj_mul_inv_mem_centerIn_of_mem_CJ_mul_inv (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) {g : G} (hgH : g ∈ H z)
    (hgσ : g ∈ Subgroup.centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hgx : qH D ⟨g, hgH⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
        ⟨t, t_mem_A⟩) =
      ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) * qH D ⟨g, hgH⟩)
    (hgQ : qH D ⟨g, hgH⟩ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {n : ℕ} (hgn : g ^ 2 ^ n = 1)
    {p : G} (hp : p ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) :
    g * p * g⁻¹ * p⁻¹ ∈ centerIn (J z) := by
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσdef
  have hqσ : qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
    rw [hσdef, map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hgσ' : (⟨g, hgH⟩ : ↥(H z)) * σ = σ * ⟨g, hgH⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgσ)
  have hgbσ : qH D ⟨g, hgH⟩ ∈ Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹} : Set QA45.originalSubgroup) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hqσ, ← map_mul, ← map_mul, hgσ']
  have hgbx : qH D ⟨g, hgH⟩ ∈ Subgroup.centralizer
      ({(⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩} :
        Set QA45.originalSubgroup) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgx
  have hgbn : qH D ⟨g, hgH⟩ ^ 2 ^ n = 1 := by
    have : (⟨g, hgH⟩ : ↥(H z)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hgn)
    rw [← map_pow, this, map_one]
  obtain ⟨d, hdC, hd⟩ := exists_conj_eq_one_or_eq_t_of_mem_QP45 ⟨hgbσ, hgbx⟩ hgQ hgbn
  have hσ3 : orderOf σ = 3 := orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hdσ : d * qH D σ = qH D σ * d := by
    rw [hqσ]; exact Subgroup.mem_centralizer_singleton_iff.mp hdC.1
  obtain ⟨dt, hdtq, hdtσ⟩ := exists_lift_centralizer D hσ3 hdσ
  set g' : ↥(H z) := dt⁻¹ * ⟨g, hgH⟩ * dt with hg'def
  have hg'q : qH D g' = 1 ∨ qH D g' = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) := by
    rw [hg'def, map_mul, map_mul, map_inv, hdtq]; exact hd
  have hg'σ' : g' * σ = σ * g' := by
    have hdtσ' : dt⁻¹ * σ = σ * dt⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hdtσ, mul_assoc, mul_inv_cancel, mul_one]
    calc g' * σ = dt⁻¹ * ⟨g, hgH⟩ * (dt * σ) := by rw [hg'def]; group
      _ = dt⁻¹ * (⟨g, hgH⟩ * σ) * dt := by rw [hdtσ]; group
      _ = (dt⁻¹ * σ) * ⟨g, hgH⟩ * dt := by rw [hgσ']; group
      _ = σ * g' := by rw [hdtσ', hg'def]; group
  have hg'σ : (g' : G) ∈ Subgroup.centralizer ({(σ : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg'σ')
  have htt : (⟨t, t_mem_A⟩ : QA45.originalSubgroup) * ⟨t, t_mem_A⟩ = 1 := Subtype.ext t_sq
  have hg'QP : qH D g' ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rcases hg'q with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_subgroupOf.mpr t_mem_Q
  have hg'g' : (g' : G) * g' ∈ J z := by
    have : g' * g' ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul]
      rcases hg'q with h1 | h1 <;> rw [h1]
      · exact mul_one 1
      · exact htt
    exact Subgroup.mem_subgroupOf.mp this
  have hg'ω : (g' : G) * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * (g' : G)⁻¹ *
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹ ∈ J z := by
    have : g' * (sigma1Nine (z := z) D * σ₂) * g'⁻¹ * (sigma1Nine (z := z) D * σ₂)⁻¹ ∈
        (J z).subgroupOf (H z) := by
      rw [J_mem_iff D]
      simp only [map_mul, map_inv, qH_sigma1Nine, hq₂]
      rcases hg'q with h1 | h1 <;> rw [h1]
      · group
      · have ht1 : Commute (⟨t, t_mem_A⟩ : QA45.originalSubgroup) ⟨sigma1, sigma1_mem_A⟩ :=
          Subtype.ext t_commute_sigma1
        have ht2 : Commute (⟨t, t_mem_A⟩ : QA45.originalSubgroup) ⟨sigma2, sigma2_mem_A⟩ :=
          Subtype.ext t_commute_sigma2
        rw [(ht1.mul_right ht2).eq]; group
    simpa using Subgroup.mem_subgroupOf.mp this
  have hg'Qn := fun q (hq : q ∈ CJ z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
      ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) =>
    conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq g'.2 hg'σ hq
  have hdtiσ : ((dt⁻¹ : ↥(H z)) : G) * (σ : G) = (σ : G) * ((dt⁻¹ : ↥(H z)) : G) := by
    have : dt⁻¹ * σ = σ * dt⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hdtσ, mul_assoc, mul_inv_cancel, mul_one]
    exact congrArg Subtype.val this
  have hp' : ((dt⁻¹ : ↥(H z)) : G) * p * ((dt⁻¹ : ↥(H z)) : G)⁻¹ ∈ CJ z (σ : G) :=
    conj_mem_CJ_of_commute (z := z) (dt⁻¹).2 hdtiσ hp
  obtain ⟨q, hq, e, he, hqe⟩ := exists_mul_eq_of_mem_CJ_mul_inv (z := z) D h hEq hp'
  have h1 := conj_mul_inv_mem_zpowers_of_conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂
    hcomm hEq g'.2 hg'Qn hg'g' hg'ω hq
  have h2 := conj_mul_inv_mem_centerIn_of_mem_CJ_sigma1Nine (z := z) D h hσ₂ hq₂ hEq g'.2
    hg'QP he
  have hzZ : Subgroup.zpowers z ≤ centerIn (J z) :=
    Subgroup.zpowers_le_of_mem ⟨z_mem_J h, z_centralizes_J h⟩
  have hqJ : q ∈ J z := (mem_CJ.mp hq.1).2
  have hqc : q * ((g' : G) * e * (g' : G)⁻¹ * e⁻¹) = ((g' : G) * e * (g' : G)⁻¹ * e⁻¹) * q :=
    Subgroup.mem_centralizer_iff.mp h2.2 q hqJ
  obtain ⟨p', hp'_eq⟩ : ∃ p', ((dt⁻¹ : ↥(H z)) : G) * p * ((dt⁻¹ : ↥(H z)) : G)⁻¹ = p' :=
    ⟨_, rfl⟩
  rw [hp'_eq] at hqe
  have hm : (g' : G) * p' * (g' : G)⁻¹ * p'⁻¹ ∈ centerIn (J z) := by
    rw [← hqe]
    have e1 : (g' : G) * (q * e) * (g' : G)⁻¹ * (q * e)⁻¹ =
        ((g' : G) * q * (g' : G)⁻¹ * q⁻¹) * (q * ((g' : G) * e * (g' : G)⁻¹ * e⁻¹) * q⁻¹) := by
      group
    rw [e1, hqc, mul_inv_cancel_right]
    exact (centerIn (J z)).mul_mem (hzZ h1) h2
  have hfin := conj_mem_centerIn_J (z := z) dt.2 hm
  have e2 : (dt : G) * ((g' : G) * p' * (g' : G)⁻¹ * p'⁻¹) * (dt : G)⁻¹ = g * p * g⁻¹ * p⁻¹ := by
    rw [← hp'_eq, hg'def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rwa [e2] at hfin

theorem exists_fusion_subgroup_CJ_of_qH_eq_uvt (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹)
    {x : G} (hxH : x ∈ H z)
    (hqx : qH D ⟨x, hxH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩)
    (hx2 : orderOf x = 2)
    (hxσ : x ∈ Subgroup.centralizer ({(σ : G)} : Set G))
    (hAE : IsElemAbelian 2 (CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∃ B : Subgroup G, B ≤ CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G) ∧ z ∈ B ∧
      Nat.card B = 4 ∧
      (∀ a ∈ CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G),
        ∀ a' ∈ CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G), a ∉ B → a' ∉ B → a * a' ∈ B) ∧
      (∀ a ∈ CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G), ∀ b ∈ B,
        ∃ y ∈ J z ⊓ Subgroup.centralizer ({(σ : G)} : Set G), y * (x * a) * y⁻¹ = x * (a * b)) ∧
      ∀ X : Subgroup G, IsSylowOf 2 X (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
        Subgroup.centralizer ({x} : Set G)) → ∀ y ∈ X, ∀ b ∈ B, y * b = b * y := by
  subst hσ
  set s : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) with hs
  set Q : Subgroup G := CJ z s ⊓
    ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ with hQ
  set J₀ : Subgroup G := CJ z (sigma1Nine (z := z) D : G) with hJ₀
  set Z : Subgroup G := centerIn (J z) with hZ
  set A : Subgroup G := CJ z s ⊓ Subgroup.centralizer ({x} : Set G) with hA
  have hz2 : orderOf z = 2 := h.1
  have hz1 : z ≠ 1 := by
    intro hz; rw [hz, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hzz : z * z = 1 := sq_eq_one_of_mem_zpowers h (Subgroup.mem_zpowers z)
  have hzJ : z ∈ J z := z_mem_J h
  have hzZ : z ∈ Z := ⟨hzJ, z_centralizes_J h⟩
  have hzpZ : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le_of_mem hzZ
  have hcent : ∀ w ∈ Subgroup.zpowers z, ∀ g ∈ H z, g * w = w * g := fun w hw g hg =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le_of_mem (z_centralizes_H h) hw) g hg
  have hcomJ : ∀ r₁ ∈ J z, ∀ r₂ ∈ J z, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers z := by
    intro r₁ hr₁ r₂ hr₂
    rw [← h.2.2.1]
    have := Subgroup.commutator_mem_commutator hr₁ hr₂
    rwa [commutatorElement_def] at this
  have hxx : x * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one x
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hZc : ∀ ζ ∈ Z, ∀ r ∈ J z, r * ζ = ζ * r := fun ζ hζ r hr =>
    Subgroup.mem_centralizer_iff.mp hζ.2 r hr
  have hPJ : ∀ p ∈ CJ z s, p ∈ J z := fun p hp => (mem_CJ.mp hp).2
  have hPσ : ∀ p ∈ CJ z s, p ∈ Subgroup.centralizer ({s} : Set G) := fun p hp => (mem_CJ.mp hp).1
  have hQP : ∀ q ∈ Q, q ∈ CJ z s := fun q hq => hq.1
  have hQJ : ∀ q ∈ Q, q ∈ J z := fun q hq => hPJ q hq.1
  have hJ₀P : J₀ ≤ CJ z s := by
    intro y hy
    obtain ⟨hy1, hyJ⟩ := mem_CJ.mp hy
    have h1 : Commute y (sigma1Nine (z := z) D : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy1
    have h2' : (⟨y, hyJ⟩ : ↥(J z)) ∈ centralizerJ σ₂ := by
      rw [← hEq]
      exact mem_centralizerJ_iff.mpr h1
    have h2 : Commute y (σ₂ : G) := mem_centralizerJ_iff.mp h2'
    refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hyJ⟩
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (h1.mul_right h2.inv_right).eq
  have hJ₀J : ∀ e ∈ J₀, e ∈ J z := fun e he => (mem_CJ.mp he).2
  have hZJ₀ : Z ≤ J₀ := centerIn_le_CJ_sigma1Nine (z := z) D h
  have hZP : Z ≤ CJ z s := hZJ₀.trans hJ₀P
  have hzQ : z ∈ Q := by
    have hzA : z ∈ (J z ⊓ Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G)) ⊓
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
      rw [centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
      exact Subgroup.mem_zpowers z
    exact ⟨hZP hzZ, hzA.2⟩
  have hzpQ : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le_of_mem hzQ
  have hQcard : Nat.card Q = 4 * Nat.card (Subgroup.zpowers z) := by
    rw [hQ, card_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq, Nat.card_zpowers, hz2]
  have hJ₀card : Nat.card J₀ = 4 * Nat.card Z := by
    rw [hJ₀, card_CJ_eq_card_centralizerJ, card_centralizerJ_sigma1Nine h D, hZ, card_centerIn_J h]
  have hQJ₀ : ∀ q ∈ Q, q ∈ J₀ → q ∈ Subgroup.zpowers z := fun q hq hqe => by
    rw [← centralizer_inf_commutator_eq_sigma1Nine (z := z) h D]
    exact ⟨⟨hQJ q hq, (mem_CJ.mp hqe).1⟩, hq.2⟩
  have hQJ₀c : ∀ q ∈ Q, ∀ e ∈ J₀, q * e = e * q := fun q hq e he =>
    (commute_of_mem_CJ_sigma1Nine_of_mem_commutator (z := z) D h he hq.2).symm
  have hPdec : ∀ p ∈ CJ z s, ∃ q ∈ Q, ∃ e ∈ J₀, q * e = p := fun p hp =>
    exists_mul_eq_of_mem_CJ_mul_inv (z := z) D h hEq hp
  have hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun q hq =>
    conj_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq hxH hxσ hq
  have hxJ₀ : ∀ e ∈ J₀, x * e * x⁻¹ ∈ J₀ := fun e he =>
    conj_mem_CJ_sigma1Nine (z := z) D h hσ₂ hq₂ hEq hxH he
  have hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    (commute_of_mem_of_isMulCommutative hAE.1 ha ha').eq
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAE.2 a ha
  have hAx : ∀ a ∈ A, x * a * x⁻¹ = a := fun a ha => by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp ha.2]; group
  have hAJ : ∀ a ∈ A, a ∈ J z := fun a ha => hPJ a ha.1
  have hδmul : ∀ a b : G, x * (a * b) * x⁻¹ * (a * b)⁻¹ =
      (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := fun a b => by group
  have hδz : ∀ w ∈ Subgroup.zpowers z, x * w * x⁻¹ * w⁻¹ = 1 := fun w hw => by
    rw [hcent w hw x hxH]; group
  have hmove : ∀ y a : G, y * (x * a) * y⁻¹ =
      x * (x * y * x⁻¹ * y⁻¹) * (y * a * y⁻¹ * a⁻¹) * a := fun y a => by
    calc y * (x * a) * y⁻¹ = y * (x⁻¹ * a) * y⁻¹ := by rw [hxi]
      _ = (x * x) * (y * (x⁻¹ * a) * y⁻¹) := by rw [hxx, one_mul]
      _ = x * (x * y * x⁻¹ * y⁻¹) * (y * a * y⁻¹ * a⁻¹) * a := by group
  have hxQP : qH D ⟨x, hxH⟩ ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rw [hqx]; exact uvtA_not_mem_QP45
  obtain ⟨kU, hkU, hkUz⟩ :=
    exists_conj_mul_inv_not_mem_zpowers (z := z) D h hσ₂ hq₂ hcomm hEq hxH hqx
  obtain ⟨jU, hjU_eq⟩ : ∃ j, x * kU * x⁻¹ * kU⁻¹ = j := ⟨_, rfl⟩
  have hjUz : jU ∉ Subgroup.zpowers z := hjU_eq ▸ hkUz
  have hjUQ : jU ∈ Q := hjU_eq ▸ Q.mul_mem (hxQ kU hkU) (Q.inv_mem hkU)
  have hjUJ : jU ∈ J z := hQJ jU hjUQ
  have hjUH : jU ∈ H z := J_le_H hjUJ
  have hjUsq : jU * jU = z :=
    mul_self_eq_of_mem_CJ_mul_inv_inf_commutator (z := z) D h hσ₂ hq₂ hcomm hEq hjUQ hjUz
  have hxjU : x * jU * x⁻¹ = jU * z := by
    have h1 : x * jU * x⁻¹ = jU⁻¹ := by
      rw [← hjU_eq]; exact conj_commutator_eq_inv_of_mul_self_eq_one hxx
    rw [h1]
    calc jU⁻¹ = jU⁻¹ * (z * z) := by rw [hzz, mul_one]
      _ = jU⁻¹ * (jU * jU) * z := by rw [hjUsq]; group
      _ = jU * z := by group
  have hδjU : x * jU * x⁻¹ * jU⁻¹ = z := by
    rw [hxjU, hcent z (Subgroup.mem_zpowers z) jU hjUH]; group
  have hxZ : ∀ ζ ∈ Z, x * ζ * x⁻¹ = ζ :=
    conj_eq_self_of_mem_centerIn h hxH (hQP jU hjUQ) hjUJ hxjU hjUsq hZP hAE
  have hZA : Z ≤ A := fun ζ hζ => ⟨hZP hζ, Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc ζ * x = x * ζ * x⁻¹ * x := by rw [hxZ ζ hζ]
      _ = x * ζ := by group)⟩
  have hTN : ∀ r ∈ Q, ∀ n ∈ Subgroup.zpowers z, r * n = n * r := fun r hr n hn =>
    hcent n hn r (J_le_H (hQJ r hr))
  have hxN : ∀ n ∈ Subgroup.zpowers z, x * n * x⁻¹ ∈ Subgroup.zpowers z := fun n hn => by
    rw [hcent n hn x hxH, mul_inv_cancel_right]; exact hn
  have hSQ : ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ Subgroup.zpowers z →
      q ∈ Subgroup.zpowers z ∨ jU⁻¹ * q ∈ Subgroup.zpowers z := fun q hq hqx =>
    mem_or_inv_mul_mem_of_conj_mul_inv_mem hzpQ hQcard hTN hxN hkU hkUz hjUQ hjUz
      (hδjU ▸ Subgroup.mem_zpowers z) hq hqx
  have hzjU : z ∈ Subgroup.zpowers jU :=
    Subgroup.mem_zpowers_iff.mpr ⟨2, by rw [zpow_two, hjUsq]⟩
  have hRdef : ∀ q, (q ∈ Subgroup.zpowers z ∨ jU⁻¹ * q ∈ Subgroup.zpowers z) →
      q ∈ Subgroup.zpowers jU := by
    rintro q (hq | hq)
    · exact Subgroup.zpowers_le_of_mem hzjU hq
    · have : q = jU * (jU⁻¹ * q) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_zpowers jU) (Subgroup.zpowers_le_of_mem hzjU hq)
  have hRc : ∀ q ∈ Subgroup.zpowers jU, ∀ q' ∈ Subgroup.zpowers jU, q * q' = q' * q := by
    rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
    exact (Commute.zpow_zpow_self jU i k).eq
  have hAdec : ∀ a ∈ A, ∃ q ∈ Q, ∃ e ∈ J₀, q * e = a ∧ q ∈ Subgroup.zpowers jU ∧
      ((q ∈ Subgroup.zpowers z ∧ x * e * x⁻¹ * e⁻¹ = 1) ∨
        (jU⁻¹ * q ∈ Subgroup.zpowers z ∧ x * e * x⁻¹ * e⁻¹ = z)) := by
    intro a ha
    obtain ⟨q, hq, e, he, rfl⟩ := hPdec a ha.1
    have hδa : x * (q * e) * x⁻¹ * (q * e)⁻¹ = 1 := by rw [hAx _ ha, mul_inv_cancel]
    obtain ⟨dq, hdq⟩ : ∃ d, x * q * x⁻¹ * q⁻¹ = d := ⟨_, rfl⟩
    obtain ⟨de, hde⟩ : ∃ d, x * e * x⁻¹ * e⁻¹ = d := ⟨_, rfl⟩
    have hdeJ₀ : de ∈ J₀ := hde ▸ J₀.mul_mem (hxJ₀ e he) (J₀.inv_mem he)
    have hdqQ : dq ∈ Q := hdq ▸ Q.mul_mem (hxQ q hq) (Q.inv_mem hq)
    have hprod : dq * de = 1 := by
      rw [hδmul q e, hdq, hde, hQJ₀c q hq de hdeJ₀, mul_inv_cancel_right] at hδa
      exact hδa
    have hdq' : dq = de⁻¹ := eq_inv_of_mul_eq_one_left hprod
    have hdqz : dq ∈ Subgroup.zpowers z := hQJ₀ dq hdqQ (hdq' ▸ J₀.inv_mem hdeJ₀)
    have hq' := hSQ q hq (hdq ▸ hdqz)
    refine ⟨q, hq, e, he, rfl, hRdef q hq', ?_⟩
    rcases hq' with hqz | hqz
    · left
      refine ⟨hqz, ?_⟩
      have h1 : dq = 1 := hdq ▸ hδz q hqz
      rw [hde]
      rw [h1, one_mul] at hprod
      exact hprod
    · right
      refine ⟨hqz, ?_⟩
      have h1 : dq = z := by
        rw [← hdq]
        have hqe : q = jU * (jU⁻¹ * q) := by group
        rw [hqe, hδmul, hδjU, hδz _ hqz, mul_one, mul_inv_cancel, mul_one]
      rw [hde]
      rw [h1] at hprod
      calc de = z⁻¹ * (z * de) := by group
        _ = z := by rw [hprod, mul_one, inv_eq_of_mul_eq_one_right hzz]
  have hjUA : ∀ a ∈ A, jU * a = a * jU := by
    intro a ha
    obtain ⟨q, hq, e, he, rfl, hqR, -⟩ := hAdec a ha
    have h1 : jU * q = q * jU := hRc jU (Subgroup.mem_zpowers jU) q hqR
    have h2 : jU * e = e * jU := hQJ₀c jU hjUQ e he
    calc jU * (q * e) = (jU * q) * e := by group
      _ = q * (jU * e) := by rw [h1]; group
      _ = q * e * jU := by rw [h2]; group
  have hjUP : jU ∈ J z ⊓ Subgroup.centralizer ({s} : Set G) := ⟨hjUJ, hPσ jU (hQP jU hjUQ)⟩
  have hzmove : ∀ a ∈ A, jU * (x * a) * jU⁻¹ = x * (a * z) := by
    intro a ha
    have hjUx : jU * x * jU⁻¹ = x * z := by
      have e1 : x⁻¹ * jU * x = jU * z := by
        rw [show x⁻¹ * jU * x = x * jU * x⁻¹ by rw [hxi]]; exact hxjU
      calc jU * x * jU⁻¹ = x * (x⁻¹ * jU * x) * jU⁻¹ := by group
        _ = x * (jU * z * jU⁻¹) := by rw [e1]; group
        _ = x * z := by rw [hcent z (Subgroup.mem_zpowers z) jU hjUH]; group
    have hjUa : jU * a * jU⁻¹ = a := by rw [hjUA a ha]; group
    calc jU * (x * a) * jU⁻¹ = (jU * x * jU⁻¹) * (jU * a * jU⁻¹) := by group
      _ = x * (z * a) := by rw [hjUx, hjUa]; group
      _ = x * (a * z) := by rw [← hcent z (Subgroup.mem_zpowers z) a (J_le_H (hAJ a ha))]
  have hNcJ₀ : ∀ n ∈ Z, ∀ r ∈ J₀, n * r = r * n := fun n hn r hr => (hZc n hn r (hJ₀J r hr)).symm
  have hJ₀nab := exists_not_commute_CJ_sigma1Nine (z := z) D h
  have hAZ : ∀ a ∈ A, ∀ a' ∈ A, a ∉ Z → a' ∉ Z → a⁻¹ * a' ∈ Z := by
    intro a ha a' ha' haZ ha'Z
    by_contra hZ'
    have hc := hAab _ ha _ ha'
    obtain ⟨q, hq, e, he, rfl, hqR, hqe⟩ := hAdec a ha
    obtain ⟨q', hq', e', he', rfl, hq'R, hq'e⟩ := hAdec a' ha'
    have heZ : e ∉ Z := by
      intro heZ
      rcases hqe with ⟨hqz, -⟩ | ⟨-, hez⟩
      · exact haZ (Z.mul_mem (hzpZ hqz) heZ)
      · rw [hxZ e heZ, mul_inv_cancel] at hez; exact hz1 hez.symm
    have he'Z : e' ∉ Z := by
      intro heZ
      rcases hq'e with ⟨hqz, -⟩ | ⟨-, hez⟩
      · exact ha'Z (Z.mul_mem (hzpZ hqz) heZ)
      · rw [hxZ e' heZ, mul_inv_cancel] at hez; exact hz1 hez.symm
    have hee'Z : e⁻¹ * e' ∉ Z := by
      intro hm
      have hδe' : x * e' * x⁻¹ * e'⁻¹ = x * e * x⁻¹ * e⁻¹ := by
        have : e' = e * (e⁻¹ * e') := by group
        rw [this, hδmul, hxZ _ hm]; group
      have hqq : q⁻¹ * q' ∈ Subgroup.zpowers z := by
        rcases hqe with ⟨hqz, hδe⟩ | ⟨hqz, hδe⟩ <;>
          rcases hq'e with ⟨hq'z, hδe2⟩ | ⟨hq'z, hδe2⟩
        · exact mul_mem (inv_mem hqz) hq'z
        · exfalso; rw [hδe', hδe] at hδe2; exact hz1 hδe2.symm
        · exfalso; rw [hδe', hδe] at hδe2; exact hz1 hδe2
        · have : q⁻¹ * q' = (jU⁻¹ * q)⁻¹ * (jU⁻¹ * q') := by group
          rw [this]; exact mul_mem (inv_mem hqz) hq'z
      apply hZ'
      have hc' := hcent _ hqq e⁻¹ (inv_mem (J_le_H (hJ₀J e he)))
      have : (q * e)⁻¹ * (q' * e') = (q⁻¹ * q') * (e⁻¹ * e') := by
        calc (q * e)⁻¹ * (q' * e') = e⁻¹ * (q⁻¹ * q') * e' := by group
          _ = (q⁻¹ * q') * (e⁻¹ * e') := by rw [hc']; group
      rw [this]
      exact Z.mul_mem (hzpZ hqq) hm
    apply mul_ne_mul_of_card_eq_four_mul hZJ₀ hJ₀card hNcJ₀ hJ₀nab he he' heZ he'Z hee'Z
    have h1 : q * q' = q' * q := hRc q hqR q' hq'R
    have h2 : e' * q = q * e' := (hQJ₀c q hq e' he').symm
    have h3 : e * q' = q' * e := (hQJ₀c q' hq' e he).symm
    have e1 : q * e * (q' * e') = q * q' * (e * e') := by
      calc q * e * (q' * e') = q * (e * q') * e' := by group
        _ = q * (q' * e) * e' := by rw [h3]
        _ = q * q' * (e * e') := by group
    have e2 : q' * e' * (q * e) = q * q' * (e' * e) := by
      calc q' * e' * (q * e) = q' * (e' * q) * e := by group
        _ = q' * (q * e') * e := by rw [h2]
        _ = (q' * q) * (e' * e) := by group
        _ = q * q' * (e' * e) := by rw [h1]
    have : q * q' * (e * e') = q * q' * (e' * e) := by rw [← e1, ← e2]; exact hc
    exact mul_left_cancel this
  obtain ⟨z₁, hz₁Z, -, hz₁1, hdec⟩ := exists_mem_centerIn_mem_or_mul_mem h
  have hzA : z ∈ A := hZA hzZ
  have hsJ : ∀ y ∈ CJ z s, y ∈ J z ⊓ Subgroup.centralizer ({s} : Set G) := fun y hy =>
    ⟨hPJ y hy, hPσ y hy⟩
  have hcmove : ∀ c ∈ A, ∀ y ∈ CJ z s, x * y * x⁻¹ * y⁻¹ = c → (∀ a ∈ A, a * c = c * a) →
      ∀ a ∈ A, ∃ y' ∈ J z ⊓ Subgroup.centralizer ({s} : Set G),
        y' * (x * a) * y'⁻¹ = x * (a * c) := by
    intro c hcA y hy hδy hcc a ha
    have hya := hcomJ y (hPJ y hy) a (hAJ a ha)
    have haH : a ∈ H z := J_le_H (hAJ a ha)
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hya with h1 | h1
    · refine ⟨y, hsJ y hy, ?_⟩
      rw [hmove y a, hδy, h1, mul_one, mul_assoc, ← hcc a ha]
    · have hacz : a * c * z ∈ A := A.mul_mem (A.mul_mem ha hcA) hzA
      have e1 : y * (x * a) * y⁻¹ = x * (a * c * z) := by
        rw [hmove y a, hδy, h1]
        calc x * c * z * a = x * (c * (z * a)) := by group
          _ = x * (c * (a * z)) := by rw [← hcent z (Subgroup.mem_zpowers z) a haH]
          _ = x * (a * c * z) := by rw [← mul_assoc c, ← hcc a ha]
      refine ⟨jU * y, (J z ⊓ Subgroup.centralizer ({s} : Set G)).mul_mem hjUP (hsJ y hy), ?_⟩
      calc jU * y * (x * a) * (jU * y)⁻¹ = jU * (y * (x * a) * y⁻¹) * jU⁻¹ := by group
        _ = jU * (x * (a * c * z)) * jU⁻¹ := by rw [e1]
        _ = x * (a * c * z * z) := hzmove _ hacz
        _ = x * (a * c) := by rw [mul_assoc (a * c), hzz, mul_one]
  have hBclos : ∀ c ∈ A, c * c = 1 → c ∉ Subgroup.zpowers z →
      Subgroup.closure ({z, c} : Set G) ≤ A ∧ z ∈ Subgroup.closure ({z, c} : Set G) ∧
        c ∈ Subgroup.closure ({z, c} : Set G) ∧
        Nat.card (Subgroup.closure ({z, c} : Set G)) = 4 := by
    intro c hcA hcc hcz
    have hc1 : c ≠ 1 := fun h1 => hcz (h1 ▸ one_mem _)
    have hcz' : c ≠ z := fun h1 => hcz (h1 ▸ Subgroup.mem_zpowers z)
    have hzc : z * c = c * z :=
      (hcent z (Subgroup.mem_zpowers z) c (J_le_H (hAJ c hcA))).symm
    refine ⟨?_, Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
      CFSG.GroupTheory.card_closure_pair_of_involutions hzz hcc hzc hz1 hc1 hcz'⟩
    rw [Subgroup.closure_le]
    intro b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact hzA
    · exact hcA
  by_cases hsign : ∃ kF ∈ J₀, x * kF * x⁻¹ * kF⁻¹ ∉ Z
  ·
    obtain ⟨kF, hkF, hkFZ⟩ := hsign
    obtain ⟨jF, hjF_eq⟩ : ∃ j, x * kF * x⁻¹ * kF⁻¹ = j := ⟨_, rfl⟩
    have hjFJ₀ : jF ∈ J₀ := hjF_eq ▸ J₀.mul_mem (hxJ₀ kF hkF) (J₀.inv_mem hkF)
    have hjFZ : jF ∉ Z := hjF_eq ▸ hkFZ
    have hkFJ : kF ∈ J z := hJ₀J kF hkF
    have hjFJ : jF ∈ J z := hJ₀J jF hjFJ₀
    have hkFnZ : kF ∉ Z := by
      intro hk; apply hkFZ; rw [hxZ kF hk, mul_inv_cancel]; exact Z.one_mem
    have hk2 : kF * kF ∈ Subgroup.zpowers z := sq_mem_zpowers_z h hkFJ
    have hkFjF : kF⁻¹ * jF ∉ Z := by
      intro hm
      apply hkFnZ
      have hxk : x * kF * x⁻¹ ∈ Z := by
        have e : x * kF * x⁻¹ = (kF⁻¹ * jF) * (kF * kF) := by
          calc x * kF * x⁻¹ = kF * (kF⁻¹ * jF) * kF := by rw [← hjF_eq]; group
            _ = (kF⁻¹ * jF) * kF * kF := by rw [hZc _ hm kF hkFJ]
            _ = (kF⁻¹ * jF) * (kF * kF) := by group
        rw [e]
        exact Z.mul_mem hm (hzpZ hk2)
      have := conj_mem_centerIn_J (z := z) (inv_mem hxH) hxk
      rwa [show x⁻¹ * (x * kF * x⁻¹) * x⁻¹⁻¹ = kF by group] at this
    have hne := mul_ne_mul_of_card_eq_four_mul hZJ₀ hJ₀card hNcJ₀ hJ₀nab hkF hjFJ₀ hkFnZ hjFZ
      hkFjF
    have hkj : kF * jF * kF⁻¹ * jF⁻¹ = z := by
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp (hcomJ kF hkFJ jF hjFJ)
        with h1 | h1
      · exfalso; apply hne
        calc kF * jF = kF * jF * kF⁻¹ * jF⁻¹ * (jF * kF) := by group
          _ = jF * kF := by rw [h1, one_mul]
      · exact h1
    have hjFsq : jF * jF = z := by
      have hk2' : x * (kF * kF) * x⁻¹ = kF * kF := by
        rw [hcent _ hk2 x hxH, mul_inv_cancel_right]
      have hc' : (kF * (x * kF * x⁻¹ * kF⁻¹) * kF⁻¹ * (x * kF * x⁻¹ * kF⁻¹)⁻¹) *
          (x * kF * x⁻¹ * kF⁻¹) = (x * kF * x⁻¹ * kF⁻¹) *
          (kF * (x * kF * x⁻¹ * kF⁻¹) * kF⁻¹ * (x * kF * x⁻¹ * kF⁻¹)⁻¹) := by
        rw [hjF_eq, hkj]
        exact (hcent z (Subgroup.mem_zpowers z) jF (J_le_H hjFJ)).symm
      have := conj_commutator_mul_self_eq_inv hk2' hc'
      rw [hjF_eq, hkj, inv_eq_of_mul_eq_one_right hzz] at this
      exact this
    have hxjF : x * jF * x⁻¹ = jF * z := by
      have h1 : x * jF * x⁻¹ = jF⁻¹ := by
        rw [← hjF_eq]; exact conj_commutator_eq_inv_of_mul_self_eq_one hxx
      rw [h1]
      calc jF⁻¹ = jF⁻¹ * (z * z) := by rw [hzz, mul_one]
        _ = jF⁻¹ * (jF * jF) * z := by rw [hjFsq]; group
        _ = jF * z := by group
    have hjFjU : jF * jU = jU * jF := (hQJ₀c jU hjUQ jF hjFJ₀).symm
    have hyP : kF * kU ∈ CJ z s := (CJ z s).mul_mem (hJ₀P hkF) (hQP kU hkU)
    have hδc : x * (kF * kU) * x⁻¹ * (kF * kU)⁻¹ = jF * jU := by
      rw [hδmul, hjF_eq, hjU_eq, (hQJ₀c jU hjUQ kF hkF).symm]; group
    have hcP : jF * jU ∈ CJ z s := (CJ z s).mul_mem (hJ₀P hjFJ₀) (hQP jU hjUQ)
    have hcA : jF * jU ∈ A := by
      refine ⟨hcP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have e : x * (jF * jU) * x⁻¹ = jF * jU := by
        calc x * (jF * jU) * x⁻¹ = (x * jF * x⁻¹) * (x * jU * x⁻¹) := by group
          _ = jF * z * (jU * z) := by rw [hxjF, hxjU]
          _ = jF * (z * jU) * z := by group
          _ = jF * (jU * z) * z := by rw [← hcent z (Subgroup.mem_zpowers z) jU hjUH]
          _ = jF * jU * (z * z) := by group
          _ = jF * jU := by rw [hzz, mul_one]
      calc jF * jU * x = x * (jF * jU) * x⁻¹ * x := by rw [e]
        _ = x * (jF * jU) := by group
    have hcc : (jF * jU) * (jF * jU) = 1 := by
      calc (jF * jU) * (jF * jU) = jF * (jU * jF) * jU := by group
        _ = jF * (jF * jU) * jU := by rw [hjFjU]
        _ = (jF * jF) * (jU * jU) := by group
        _ = 1 := by rw [hjFsq, hjUsq, hzz]
    have hcZ : jF * jU ∉ Z := by
      intro hm
      apply hjUz
      apply hQJ₀ jU hjUQ
      have : jU = jF⁻¹ * (jF * jU) := by group
      rw [this]
      exact J₀.mul_mem (J₀.inv_mem hjFJ₀) (hZJ₀ hm)
    have hcz : jF * jU ∉ Subgroup.zpowers z := fun hm => hcZ (hzpZ hm)
    obtain ⟨hBA, hzB, hcB, hB4⟩ := hBclos _ hcA hcc hcz
    have hzpB : Subgroup.zpowers z ≤ Subgroup.closure ({z, jF * jU} : Set G) :=
      Subgroup.zpowers_le_of_mem hzB
    refine ⟨Subgroup.closure {z, jF * jU}, hBA, hzB, hB4, ?_, ?_, ?_⟩
    ·
      refine mul_mem_of_mem_or_mul_mem (w := z₁) (fun a ha => hZc z₁ hz₁Z a (hAJ a ha)) hz₁1 ?_
      intro a ha
      by_cases haZ : a ∈ Z
      · rcases hdec a haZ with h1 | h1
        · left; exact hzpB h1
        · right; exact hzpB h1
      · have hca : (jF * jU)⁻¹ * a ∈ Z := hAZ _ hcA a ha hcZ haZ
        rcases hdec _ hca with h1 | h1
        · left
          have : a = (jF * jU) * ((jF * jU)⁻¹ * a) := by group
          rw [this]; exact mul_mem hcB (hzpB h1)
        · right
          have : a * z₁ = (jF * jU) * ((jF * jU)⁻¹ * a * z₁) := by group
          rw [this]; exact mul_mem hcB (hzpB h1)
    ·
      have hmv := forall_exists_conj_of_mem_closure (A := A)
        (P := J z ⊓ Subgroup.centralizer ({s} : Set G)) (x := x) (s := {z, jF * jU})
        (by
          intro b hb
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · exact hzA
          · exact hcA)
        (by
          intro b hb a ha
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · exact ⟨jU, hjUP, hzmove a ha⟩
          · exact hcmove _ hcA _ hyP hδc (fun a' ha' => hAab a' ha' _ hcA) a ha)
      exact fun a ha b hb => hmv b hb a ha
    ·
      intro X hX y hy b hb
      obtain ⟨⟨hyσ, hyH⟩, hyx⟩ := hX.le hy
      obtain ⟨n, hn⟩ := hX.isPGroup ⟨y, hy⟩
      have hyn : y ^ 2 ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      have hyx' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hyx
      have hqyx : qH D ⟨y, hyH⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
          ⟨t, t_mem_A⟩) = ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
          ⟨t, t_mem_A⟩) * qH D ⟨y, hyH⟩ := by
        rw [← hqx, ← map_mul, ← map_mul]
        exact congrArg (qH D) (Subtype.ext hyx')
      have hcy : y * (jF * jU) * y⁻¹ = jF * jU := by
        by_cases hyQ : qH D ⟨y, hyH⟩ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
        · have hgP := fun p (hp : p ∈ CJ z s) =>
            conj_mul_inv_mem_centerIn_of_mem_CJ_mul_inv (z := z) D h hσ₂ hq₂ hcomm hEq hyH hyσ
              hqyx hyQ hyn hp
          rw [← hδc]
          exact conj_commutator_eq_of_conj_mul_inv_mem_centerIn hyx' (hgP _ hyP) hxZ
            (hδc ▸ hPJ _ hcP)
        · have hyxH : y * x ∈ H z := mul_mem hyH hxH
          have hyxQ : qH D ⟨y * x, hyxH⟩ ∈
              QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
            have : (⟨y * x, hyxH⟩ : ↥(H z)) = ⟨y, hyH⟩ * ⟨x, hxH⟩ := rfl
            rw [this, map_mul, Subgroup.mul_mem_iff_of_index_two index_QP45]
            exact iff_of_false hyQ hxQP
          have hyxσ : y * x ∈ Subgroup.centralizer ({s} : Set G) := mul_mem hyσ hxσ
          have hyxx : qH D ⟨y * x, hyxH⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) *
              ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) = ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) *
              ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) * qH D ⟨y * x, hyxH⟩ := by
            have : (⟨y * x, hyxH⟩ : ↥(H z)) = ⟨y, hyH⟩ * ⟨x, hxH⟩ := rfl
            rw [this, map_mul, hqx]
            calc qH D ⟨y, hyH⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
                  ⟨t, t_mem_A⟩) * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
                  ⟨t, t_mem_A⟩)
                = (((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) *
                  qH D ⟨y, hyH⟩) * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
                  ⟨t, t_mem_A⟩) := by rw [hqyx]
              _ = ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩) *
                  (qH D ⟨y, hyH⟩ * ((⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ *
                  ⟨t, t_mem_A⟩)) := by rw [mul_assoc]
          have hyxn : (y * x) ^ 2 ^ (n + 1) = 1 := by
            have h1 : y ^ 2 ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hyn, one_pow]
            have h2 : x ^ 2 ^ (n + 1) = 1 := by rw [pow_succ', pow_mul, sq, hxx, one_pow]
            rw [Commute.mul_pow hyx', h1, h2, one_mul]
          have hgP := fun p (hp : p ∈ CJ z s) =>
            conj_mul_inv_mem_centerIn_of_mem_CJ_mul_inv (z := z) D h hσ₂ hq₂ hcomm hEq hyxH hyxσ
              hyxx hyxQ hyxn hp
          have hyxc : (y * x) * (jF * jU) * (y * x)⁻¹ = jF * jU := by
            rw [← hδc]
            have hyxx' : y * x * x = x * (y * x) := by
              calc y * x * x = y * (x * x) := mul_assoc _ _ _
                _ = (x * x) * y := by rw [hxx, mul_one, one_mul]
                _ = x * (x * y) := mul_assoc _ _ _
                _ = x * (y * x) := by rw [hyx']
            exact conj_commutator_eq_of_conj_mul_inv_mem_centerIn hyxx' (hgP _ hyP) hxZ
              (hδc ▸ hPJ _ hcP)
          calc y * (jF * jU) * y⁻¹ = (y * x) * (x⁻¹ * (jF * jU) * x) * (y * x)⁻¹ := by group
            _ = (y * x) * (jF * jU) * (y * x)⁻¹ := by
                rw [show x⁻¹ * (jF * jU) * x = x * (jF * jU) * x⁻¹ by rw [hxi], hAx _ hcA]
            _ = jF * jU := hyxc
      have hyc : y * (jF * jU) = (jF * jU) * y := by
        calc y * (jF * jU) = y * (jF * jU) * y⁻¹ * y := by group
          _ = (jF * jU) * y := by rw [hcy]
      have hyz : y * z = z * y := hcent z (Subgroup.mem_zpowers z) y hyH
      have hle : Subgroup.closure ({z, jF * jU} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
        rw [Subgroup.closure_le]
        intro b' hb'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
        rcases hb' with rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hyz.symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
  ·
    push Not at hsign
    have he₁ : ∃ e₁ ∈ J₀, x * e₁ * x⁻¹ * e₁⁻¹ ∉ Subgroup.zpowers z := by
      by_contra hall
      push Not at hall
      obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := hJ₀nab
      have hlift : ∀ r ∈ J₀, ∃ w ∈ Subgroup.zpowers jU, w * r ∈ A := by
        intro r hr
        have hrA : x * r * x⁻¹ * r⁻¹ = 1 → r ∈ A := fun h1 => ⟨hJ₀P hr,
          Subgroup.mem_centralizer_singleton_iff.mpr (by
            calc r * x = (x * r * x⁻¹ * r⁻¹)⁻¹ * (x * r) := by group
              _ = x * r := by rw [h1, inv_one, one_mul])⟩
        rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp (hall r hr) with h1 | h1
        · exact ⟨1, one_mem _, by rw [one_mul]; exact hrA h1⟩
        · refine ⟨jU, Subgroup.mem_zpowers jU, ⟨(CJ z s).mul_mem (hQP jU hjUQ) (hJ₀P hr),
            Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩⟩
          have hδ : x * (jU * r) * x⁻¹ * (jU * r)⁻¹ = 1 := by
            rw [hδmul, hδjU, h1, hcent z (Subgroup.mem_zpowers z) jU hjUH]
            calc z * (z * jU * jU⁻¹) = z * z := by group
              _ = 1 := hzz
          calc jU * r * x = (x * (jU * r) * x⁻¹ * (jU * r)⁻¹)⁻¹ * (x * (jU * r)) := by group
            _ = x * (jU * r) := by rw [hδ, inv_one, one_mul]
      obtain ⟨w₁, hw₁, hA₁⟩ := hlift r₁ hr₁
      obtain ⟨w₂, hw₂, hA₂⟩ := hlift r₂ hr₂
      apply hne
      have hc := hAab _ hA₁ _ hA₂
      have hw₁Q : w₁ ∈ Q := Subgroup.zpowers_le_of_mem hjUQ hw₁
      have hw₂Q : w₂ ∈ Q := Subgroup.zpowers_le_of_mem hjUQ hw₂
      have h1 : w₁ * w₂ = w₂ * w₁ := hRc w₁ hw₁ w₂ hw₂
      have h2 : r₂ * w₁ = w₁ * r₂ := (hQJ₀c w₁ hw₁Q r₂ hr₂).symm
      have h3 : r₁ * w₂ = w₂ * r₁ := (hQJ₀c w₂ hw₂Q r₁ hr₁).symm
      have e1 : w₁ * r₁ * (w₂ * r₂) = w₁ * w₂ * (r₁ * r₂) := by
        calc w₁ * r₁ * (w₂ * r₂) = w₁ * (r₁ * w₂) * r₂ := by group
          _ = w₁ * (w₂ * r₁) * r₂ := by rw [h3]
          _ = w₁ * w₂ * (r₁ * r₂) := by group
      have e2 : w₂ * r₂ * (w₁ * r₁) = w₁ * w₂ * (r₂ * r₁) := by
        calc w₂ * r₂ * (w₁ * r₁) = w₂ * (r₂ * w₁) * r₁ := by group
          _ = w₂ * (w₁ * r₂) * r₁ := by rw [h2]
          _ = (w₂ * w₁) * (r₂ * r₁) := by group
          _ = w₁ * w₂ * (r₂ * r₁) := by rw [h1]
      have : w₁ * w₂ * (r₁ * r₂) = w₁ * w₂ * (r₂ * r₁) := by rw [← e1, ← e2]; exact hc
      exact mul_left_cancel this
    obtain ⟨e₁, he₁J₀, he₁z⟩ := he₁
    obtain ⟨c, hc_eq⟩ : ∃ c, x * e₁ * x⁻¹ * e₁⁻¹ = c := ⟨_, rfl⟩
    have hcZ : c ∈ Z := hc_eq ▸ hsign e₁ he₁J₀
    have hcz : c ∉ Subgroup.zpowers z := hc_eq ▸ he₁z
    have hcA : c ∈ A := hZA hcZ
    have hcc : c * c = 1 := mul_self_eq_one_of_mem_centerIn h hcZ
    obtain ⟨hBA, hzB, hcB, hB4⟩ := hBclos c hcA hcc hcz
    have hBZ : Subgroup.closure ({z, c} : Set G) = Z := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hB4, hZ, card_centerIn_J h])
      rw [Subgroup.closure_le]
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl
      · exact hzZ
      · exact hcZ
    refine ⟨Subgroup.closure {z, c}, hBA, hzB, hB4, ?_, ?_, ?_⟩
    ·
      intro a ha a' ha' haB ha'B
      rw [hBZ] at haB ha'B ⊢
      have h1 := hAZ a ha a' ha' haB ha'B
      have e : a * a' = (a * a) * (a⁻¹ * a') := by group
      rw [e, hAsq a ha, one_mul]
      exact h1
    ·
      have hmv := forall_exists_conj_of_mem_closure (A := A)
        (P := J z ⊓ Subgroup.centralizer ({s} : Set G)) (x := x) (s := {z, c})
        (by
          intro b hb
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · exact hzA
          · exact hcA)
        (by
          intro b hb a ha
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
          rcases hb with rfl | rfl
          · exact ⟨jU, hjUP, hzmove a ha⟩
          · exact hcmove _ hcA _ (hJ₀P he₁J₀) hc_eq
              (fun a' ha' => hZc b hcZ a' (hAJ a' ha')) a ha)
      exact fun a ha b hb => hmv b hb a ha
    ·
      intro X hX y hy b hb
      obtain ⟨⟨-, hyH⟩, -⟩ := hX.le hy
      rw [hBZ] at hb
      have := conj_eq_self_of_mem_centerIn_of_mem_H (z := z) D h hxH hxQP hxZ hyH b hb
      calc y * b = y * b * y⁻¹ * y := by group
        _ = b * y := by rw [this]

theorem exists_fusion_subgroup_of_mem_uvtJ (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹)
    {x : G} (hxc : cosetJ (z := z) (uH D * vH D * tH D) x) (hx2 : orderOf x = 2)
    (hxσ : x ∈ Subgroup.centralizer ({(σ : G)} : Set G)) (hxE : IsElemAbelian 2 (CJ z x))
    {X K : Subgroup G}
    (hX : IsSylowOf 2 X (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
      Subgroup.centralizer ({x} : Set G)))
    (hK : ∀ k : G, k ∈ K ↔ k ∈ X ∧ (∀ y ∈ X, y * k = k * y) ∧ k * k = 1) :
    ∃ B : Subgroup G, B ≤ K ⊓ J z ∧ z ∈ B ∧ 2 < Nat.card B ∧
      (∀ a ∈ K ⊓ J z, ∀ a' ∈ K ⊓ J z, a ∉ B → a' ∉ B → a * a' ∈ B) ∧
      ∀ a ∈ K ⊓ J z, ∀ b ∈ B, IsConj (x * a) (x * (a * b)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hjJ, hxj⟩ := hxc
  have hxH : x ∈ H z := hxj ▸ mul_mem (uH D * vH D * tH D).2 (J_le_H hjJ)
  have hqx : qH D ⟨x, hxH⟩ =
      (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩ := by
    have e : (⟨x, hxH⟩ : ↥(H z)) = uH D * vH D * tH D * ⟨j, J_le_H hjJ⟩ := Subtype.ext hxj
    have hj1 : qH D ⟨j, J_le_H hjJ⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hjJ)
    rw [e, map_mul, hj1, mul_one, map_mul, map_mul, qH_uH, qH_vH, qH_tH]
  have hAle : CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ CJ z x := fun a ha =>
    mem_CJ.mpr ⟨ha.2, (mem_CJ.mp ha.1).2⟩
  have hAE : IsElemAbelian 2 (CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ⟨⟨⟨fun a b => Subtype.ext
      (commute_of_mem_of_isMulCommutative hxE.1 (hAle a.2) (hAle b.2)).eq⟩⟩,
      fun a ha => hxE.2 a (hAle ha)⟩
  obtain ⟨B, hBA, hzB, hB4, hidx, hmv, hBX⟩ :=
    exists_fusion_subgroup_CJ_of_qH_eq_uvt D h hσ₂ hq₂ hcomm hEq hσ hxH hqx hx2 hxσ hAE
  replace hBX := hBX X hX
  have hKJA : K ⊓ J z ≤ CJ z (σ : G) ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro k ⟨hkK, hkJ⟩
    obtain ⟨hkX, -, -⟩ := (hK k).mp hkK
    obtain ⟨⟨hkσ, -⟩, hkx⟩ := hX.le hkX
    exact ⟨mem_CJ.mpr ⟨hkσ, hkJ⟩, hkx⟩
  have hBX' : B ≤ X := by
    have hBp : IsPGroup 2 B := IsPGroup.of_card (n := 2) (by rw [hB4]; norm_num)
    have hXB : X ≤ Subgroup.normalizer (B : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        rw [hBX y hy b hb, mul_inv_cancel_right]
        exact hb
      · intro hb
        have h1 := hBX y hy _ hb
        have e : b = y * b * y⁻¹ := by
          calc b = y⁻¹ * ((y * b * y⁻¹) * y) := by group
            _ = y⁻¹ * (y * (y * b * y⁻¹)) := by rw [h1]
            _ = y * b * y⁻¹ := by group
        rw [e]
        exact hb
    have hsup := IsPGroup.to_sup_of_normal_right' hX.isPGroup hBp hXB
    have hle : X ⊔ B ≤ Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
        Subgroup.centralizer ({x} : Set G) := by
      refine sup_le hX.le fun b hb => ?_
      obtain ⟨hbP, hbx⟩ := hBA hb
      obtain ⟨hbσ, hbJ⟩ := mem_CJ.mp hbP
      exact ⟨⟨hbσ, J_le_H hbJ⟩, hbx⟩
    have heq := hX.eq_of_le le_sup_left hle hsup
    rw [← heq]
    exact le_sup_right
  refine ⟨B, fun b hb => ⟨(hK b).mpr ⟨hBX' hb, fun y hy => hBX y hy b hb, ?_⟩,
    (mem_CJ.mp (hBA hb).1).2⟩, hzB, by rw [hB4]; norm_num, ?_, ?_⟩
  · rw [← sq]; exact hAE.2 b (hBA hb)
  · intro a ha a' ha' haB ha'B
    exact hidx a (hKJA ha) a' (hKJA ha') haB ha'B
  · intro a ha b hb
    obtain ⟨y, -, hy⟩ := hmv a (hKJA ha) b hb
    exact isConj_iff.mpr ⟨y, hy⟩

end CFSG.RankThree.GF2n.Parrott
