module

public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrA
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {P : Type} [Group P]

structure WrCore [Finite P] (T₀ K₁ X₀ S : Subgroup P) (τ : P) : Prop where
  hO : ∀ C : Subgroup P, C.Normal → IsPGroup 2 C → C = ⊥
  hT : IsSylowTwoOf T₀ ⊤
  hA5 : Nonempty (↥K₁ ≃* AFive)
  hsub : ∀ s ∈ T₀, IsSubnormal (cjSub s K₁) ⊤
  hτ : τ ∈ T₀
  hne : cjSub τ K₁ ≠ K₁
  hcomm : ∀ s ∈ T₀, cjSub s K₁ = K₁ ∨ ⁅K₁, cjSub s K₁⁆ = ⊥
  hgen : K₁ ⊔ T₀ = ⊤
  h27 : ¬ 27 ∣ Nat.card X₀
  hS : IsSylowTwoOf S K₁
  hMX : K₁ ⊓ Subgroup.normalizer (S : Set P) ≤ X₀
  hX₀ : X₀ ≤ (K₁ ⊓ Subgroup.normalizer (S : Set P)) ⊔
    cjSub τ (K₁ ⊓ Subgroup.normalizer (S : Set P)) ⊔ T₀
  hTX : T₀ ≤ X₀
  hTK : T₀ ⊓ K₁ ≤ K₁ ⊓ Subgroup.normalizer (S : Set P)
  hd : ∃ d ∈ K₁ ⊓ Subgroup.normalizer (S : Set P), orderOf d = 3

namespace WrCore

noncomputable def cjEquiv (g : P) (K : Subgroup P) : ↥K ≃* ↥(cjSub g K) :=
  (MulAut.conj g).subgroupMap K

theorem eq_one_of_commute_of_equiv {K : Subgroup P} (e : ↥K ≃* AFive) {z : P} (hz : z ∈ K)
    (h : ∀ a ∈ K, z * a = a * z) : z = 1 := by
  have h1 : e ⟨z, hz⟩ = 1 := eq_one_of_forall_commute_aFive fun a => by
    have := h (e.symm a) (e.symm a).2
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact Subtype.ext this
  have := congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).mp h1)
  exact this

theorem inf_eq_bot_of_commute {K L : Subgroup P} (e : ↥K ≃* AFive)
    (hc : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a) : K ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute_of_equiv e hz.1 fun a ha => (hc a ha z hz.2).symm

theorem commute_of_commutator_eq_bot {K L : Subgroup P} (h : ⁅K, L⁆ = ⊥) :
    ∀ a ∈ K, ∀ b ∈ L, a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem card_eq_four_of_isSylowTwoOf [Finite P] {T H : Subgroup P} (hT : IsSylowTwoOf T H)
    (hH : Nat.card H = 60) : Nat.card T = 4 := by
  obtain ⟨b, hb⟩ := hT.2.1.exists_card_eq
  have h1 : Nat.card (T.subgroupOf H) * (T.subgroupOf H).index = Nat.card H :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  have hidx : ¬ 2 ∣ (T.subgroupOf H).index := hT.2.2
  rw [h2, hb, hH] at h1
  have hb6 : b < 6 := by
    by_contra h
    have h3 : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ b ≤ 60 := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
    omega
  rw [hb]
  interval_cases b <;> omega

theorem nonempty_cjSub_equiv {K : Subgroup P} (h : Nonempty (↥K ≃* AFive)) (g : P) :
    Nonempty (↥(cjSub g K) ≃* AFive) :=
  h.map fun e => (cjEquiv g K).symm.trans e

theorem conj_mem_cjSub {K : Subgroup P} {x : P} (hx : x ∈ K) (g : P) :
    g * x * g⁻¹ ∈ cjSub g K := by
  rw [mem_cjSub]
  simpa [mul_assoc] using hx

variable [Finite P] {T₀ K₁ X₀ S : Subgroup P} {τ : P}

theorem card_sup_of_commute {A B : Subgroup P} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hinf : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup P) = Nat.card A * Nat.card B := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).1
  rwa [hinf, Subgroup.card_bot, mul_one] at h

theorem commute₁₂ (c : WrCore T₀ K₁ X₀ S τ) : ∀ a ∈ K₁, ∀ b ∈ cjSub τ K₁, a * b = b * a :=
  commute_of_commutator_eq_bot ((c.hcomm τ c.hτ).resolve_left c.hne)

theorem orbit (c : WrCore T₀ K₁ X₀ S τ) :
    ∀ s ∈ T₀, cjSub s K₁ = K₁ ∨ cjSub s K₁ = cjSub τ K₁ := by
  intro s hs
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have c12 := c.commute₁₂
  have c13 : ∀ a ∈ K₁, ∀ b ∈ cjSub s K₁, a * b = b * a :=
    commute_of_commutator_eq_bot ((c.hcomm s hs).resolve_left h1)
  have c23 : ∀ a ∈ cjSub τ K₁, ∀ b ∈ cjSub s K₁, a * b = b * a := by
    have hs' : τ⁻¹ * s ∈ T₀ := T₀.mul_mem (T₀.inv_mem c.hτ) hs
    have hne' : cjSub (τ⁻¹ * s) K₁ ≠ K₁ := fun h => h2 (by
      rw [show s = τ * (τ⁻¹ * s) by group, B2F.cjSub_mul, h])
    have hc := commute_of_commutator_eq_bot ((c.hcomm _ hs').resolve_left hne')
    intro a ha b hb
    rw [mem_cjSub] at ha hb
    have hb' : τ⁻¹ * b * τ ∈ cjSub (τ⁻¹ * s) K₁ := by
      rw [mem_cjSub]
      simpa [mul_assoc] using hb
    have := hc _ ha _ hb'
    calc a * b = τ * ((τ⁻¹ * a * τ) * (τ⁻¹ * b * τ)) * τ⁻¹ := by group
      _ = τ * ((τ⁻¹ * b * τ) * (τ⁻¹ * a * τ)) * τ⁻¹ := by rw [this]
      _ = b * a := by group
  obtain ⟨e₁⟩ := c.hA5
  obtain ⟨e₂⟩ := nonempty_cjSub_equiv c.hA5 τ
  obtain ⟨e₃⟩ := nonempty_cjSub_equiv c.hA5 s
  obtain ⟨d, hdM, hd3⟩ := c.hd
  have hdX : d ∈ X₀ := c.hMX hdM
  have hτX := c.hTX c.hτ
  have hsX := c.hTX hs
  have ho : ∀ g : P, orderOf (g * d * g⁻¹) = 3 := fun g => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hd3]
  set Z₁ := Subgroup.zpowers d
  set Z₂ := Subgroup.zpowers (τ * d * τ⁻¹)
  set Z₃ := Subgroup.zpowers (s * d * s⁻¹)
  have hZ₁ : Z₁ ≤ K₁ := (Subgroup.zpowers_le).mpr hdM.1
  have hZ₂ : Z₂ ≤ cjSub τ K₁ := (Subgroup.zpowers_le).mpr (conj_mem_cjSub hdM.1 τ)
  have hZ₃ : Z₃ ≤ cjSub s K₁ := (Subgroup.zpowers_le).mpr (conj_mem_cjSub hdM.1 s)
  have hc12 : ∀ x ∈ Z₁, ∀ y ∈ Z₂, x * y = y * x := fun x hx y hy => c12 x (hZ₁ hx) y (hZ₂ hy)
  have hW : Nat.card (Z₁ ⊔ Z₂ : Subgroup P) = 9 := by
    rw [card_sup_of_commute hc12 (eq_bot_iff.mpr ((inf_le_inf hZ₁ hZ₂).trans
      (inf_eq_bot_of_commute e₁ c12).le)), Nat.card_zpowers, Nat.card_zpowers, hd3, ho]
  have hcent : K₁ ⊔ cjSub τ K₁ ≤ Subgroup.centralizer (cjSub s K₁ : Set P) := by
    refine sup_le (fun a ha => ?_) (fun a ha => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro b hb
    · exact (c13 a ha b hb).symm
    · exact (c23 a ha b hb).symm
  have hW₁₂ : Z₁ ⊔ Z₂ ≤ K₁ ⊔ cjSub τ K₁ := sup_le_sup hZ₁ hZ₂
  have hc3 : ∀ x ∈ (Z₁ ⊔ Z₂ : Subgroup P), ∀ y ∈ Z₃, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hcent (hW₁₂ hx))) y (hZ₃ hy)).symm
  have hinf3 : (Z₁ ⊔ Z₂) ⊓ Z₃ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine eq_one_of_commute_of_equiv e₃ (hZ₃ hz.2) fun a ha => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hcent (hW₁₂ hz.1))) a ha).symm
  have h27 : Nat.card ((Z₁ ⊔ Z₂) ⊔ Z₃ : Subgroup P) = 27 := by
    rw [card_sup_of_commute hc3 hinf3, hW, Nat.card_zpowers, ho]
  have hle : (Z₁ ⊔ Z₂) ⊔ Z₃ ≤ X₀ := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact hdX
    · exact X₀.mul_mem (X₀.mul_mem hτX hdX) (X₀.inv_mem hτX)
    · exact X₀.mul_mem (X₀.mul_mem hsX hdX) (X₀.inv_mem hsX)
  exact c.h27 (h27 ▸ Subgroup.card_dvd_of_le hle)

end WrCore

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
