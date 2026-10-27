module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommuteBasic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.S14110.Commute

open Subgroup

variable {Γ : Type*} [Group Γ]

structure BlockData (Q X W : Subgroup Γ) (c : Γ) : Prop where
  a4 : A4Data X W c
  le_Q : W ≤ Q
  central : ∀ q ∈ Q, ∀ w ∈ W, q * w = w * q
  comm_mem : ∀ q ∈ Q, q * c * q⁻¹ * c⁻¹ ∈ W

variable {Q X W : Subgroup Γ} {c : Γ}

theorem BlockData.conj (hb : BlockData Q X W c) {w₀ : Γ} (hw₀ : w₀ ∈ W) :
    BlockData Q X W (w₀ * c * w₀⁻¹) where
  a4 := a4Data_conj hb.a4 hw₀
  le_Q := hb.le_Q
  central := hb.central
  comm_mem := by
    intro q hq
    have hq0 : q * w₀ = w₀ * q := hb.central q hq w₀ hw₀
    have hq0' : w₀⁻¹ * q⁻¹ = q⁻¹ * w₀⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hq0]
    have e : q * (w₀ * c * w₀⁻¹) * q⁻¹ * (w₀ * c * w₀⁻¹)⁻¹ =
        w₀ * (q * c * q⁻¹ * c⁻¹) * w₀⁻¹ := by
      calc q * (w₀ * c * w₀⁻¹) * q⁻¹ * (w₀ * c * w₀⁻¹)⁻¹
          = (q * w₀) * c * (w₀⁻¹ * q⁻¹) * (w₀ * c⁻¹ * w₀⁻¹) := by group
        _ = (w₀ * q) * c * (q⁻¹ * w₀⁻¹) * (w₀ * c⁻¹ * w₀⁻¹) := by rw [hq0, hq0']
        _ = w₀ * (q * c * q⁻¹ * c⁻¹) * w₀⁻¹ := by group
    rw [e]
    exact W.mul_mem (W.mul_mem hw₀ (hb.comm_mem q hq)) (W.inv_mem hw₀)

theorem BlockData.pow_comm_mem [Q.Normal] (hb : BlockData Q X W c) (k : ℕ) :
    ∀ q ∈ Q, q⁻¹ * (c ^ k * q * (c ^ k)⁻¹) ∈ W := by
  induction k with
  | zero => intro q _; simp
  | succ k ih =>
    intro q hq
    have hq' : c ^ k * q * (c ^ k)⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance q hq _
    have h1 := ih q hq
    have h2 := hb.comm_mem q⁻¹ (Q.inv_mem hq)
    have h3 := hb.a4.conj_mem h1
    have e : q⁻¹ * (c ^ (k + 1) * q * (c ^ (k + 1))⁻¹) =
        (q⁻¹ * c * q * c⁻¹) * (c * (q⁻¹ * (c ^ k * q * (c ^ k)⁻¹)) * c⁻¹) := by
      rw [pow_succ']; group
    rw [e]
    refine W.mul_mem ?_ h3
    simpa using h2

theorem conj_mem_W_of_comm_mem (hX : A4Data X W c) (hWQ : W ≤ Q)
    (hcm : ∀ q ∈ Q, q * c * q⁻¹ * c⁻¹ ∈ W) {q : Γ} (hq : q ∈ Q) {w : Γ} (hw : w ∈ W) :
    q * w * q⁻¹ ∈ W := by
  obtain ⟨w₀, hw₀, rfl⟩ := hX.exists_mul_conj_inv_eq hw
  have h1 := hcm (q * w₀) (Q.mul_mem hq (hWQ hw₀))
  have h2 := hcm q hq
  have e : q * (w₀ * (c * w₀⁻¹ * c⁻¹)) * q⁻¹ =
      (q * w₀ * c * (q * w₀)⁻¹ * c⁻¹) * (q * c * q⁻¹ * c⁻¹)⁻¹ := by group
  rw [e]
  exact W.mul_mem h1 (W.inv_mem h2)

theorem BlockData.of_comm_mem (hX : A4Data X W c) (hWQ : W ≤ Q)
    (hQ2 : ∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) (hcm : ∀ q ∈ Q, q * c * q⁻¹ * c⁻¹ ∈ W) :
    BlockData Q X W c where
  a4 := hX
  le_Q := hWQ
  central := by
    intro q hq w hw
    have := centralizes_of_two_power hX (fun w hw => conj_mem_W_of_comm_mem hX hWQ hcm hq hw)
      (hcm q hq) (hQ2 q hq) w hw
    calc q * w = (q * w * q⁻¹) * q := by group
      _ = w * q := by rw [this]
  comm_mem := hcm

theorem card_mulAut_dvd (E : Type*) [Group E] [Finite E] (hcomm : ∀ a b : E, a * b = b * a)
    (h2 : ∀ a : E, a ^ 2 = 1) (hcard : Nat.card E ≤ 16) : Nat.card (MulAut E) ∣ 20160 := by
  have hP : IsPGroup 2 E := fun a => ⟨1, by simpa using h2 a⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := E)).1 hP
  have hn4 : n ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm h2 hn
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases n <;> simp [Fin.prod_univ_succ]

theorem comm_of_isPGroup_three {A : Type*} [Group A] [Finite A] (hA : IsPGroup 3 A)
    (hdvd : Nat.card A ∣ 20160) : ∀ a b : A, a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have h1 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 hlt
    rw [← hn] at h1
    have := h1.trans hdvd
    omega
  interval_cases n
  · intro a b
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
    exact Subsingleton.elim _ _
  · intro a b
    have hcyc : IsCyclic A := isCyclic_of_prime_card (p := 3) (by simpa using hn)
    exact mul_comm' a b
  · intro a b
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
    exact mul_comm' a b

theorem mem_normalizer_of_pow_three {F : Subgroup Γ} {g : Γ} (hg3 : g ^ 3 = 1)
    (h : ∀ f ∈ F, g * f * g⁻¹ ∈ F) : g ∈ normalizer (F : Set Γ) := by
  rw [mem_normalizer_iff]
  intro f
  refine ⟨h f, fun hf => ?_⟩
  have h2 := h _ (h _ hf)
  have hggg : g * g * g = 1 := by rw [← pow_three']; exact hg3
  have : g * (g * (g * f * g⁻¹) * g⁻¹) * g⁻¹ = f := by
    calc g * (g * (g * f * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * f * (g * g * g)⁻¹ := by group
      _ = f := by rw [hggg]; simp
  rwa [this] at h2

theorem sq_mul_comm {F : Subgroup Γ} {z q : Γ} (hzF : ∀ f ∈ F, z * f * z⁻¹ = f)
    (hF2 : ∀ f ∈ F, f ^ 2 = 1) (hq : q⁻¹ * (z * q * z⁻¹) ∈ F) : z ^ 2 * q = q * z ^ 2 := by
  have hzf := hzF _ hq
  have hf2 := hF2 _ hq
  have e : z * q * z⁻¹ = q * (q⁻¹ * (z * q * z⁻¹)) := by group
  have h1 : z * (z * q * z⁻¹) * z⁻¹ = q := by
    calc z * (z * q * z⁻¹) * z⁻¹ = z * (q * (q⁻¹ * (z * q * z⁻¹))) * z⁻¹ := by rw [← e]
      _ = (z * q * z⁻¹) * (z * (q⁻¹ * (z * q * z⁻¹)) * z⁻¹) := by group
      _ = (q * (q⁻¹ * (z * q * z⁻¹))) * (q⁻¹ * (z * q * z⁻¹)) := by rw [← e, hzf]
      _ = q * (q⁻¹ * (z * q * z⁻¹)) ^ 2 := by rw [pow_two]; group
      _ = q := by rw [hf2]; simp
  calc z ^ 2 * q = (z * (z * q * z⁻¹) * z⁻¹) * z ^ 2 := by rw [pow_two]; group
    _ = q * z ^ 2 := by rw [h1]

theorem commutator_mem [Finite Γ] [Q.Normal]
    (hQc : ∀ g : Γ, (∀ q ∈ Q, g * q = q * g) → g ∈ Q)
    {Y W' : Subgroup Γ} {c' : Γ}
    (hX : BlockData Q X W c) (hY : BlockData Q Y W' c')
    {R : Subgroup Γ} (hcR : c ∈ R) (hc'R : c' ∈ R) (hR : ∀ g ∈ R, ∃ k : ℕ, g ^ 3 ^ k ∈ Q) :
    c * c' * c⁻¹ * c'⁻¹ ∈ Q := by
  classical
  have hWfin : Finite W := hX.a4.finite_W
  have hW'fin : Finite W' := hY.a4.finite_W
  have hWW' : ∀ w ∈ W, ∀ w' ∈ W', w' * w = w * w' := fun w hw w' hw' =>
    hX.central w' (hY.le_Q hw') w hw
  have hcentr : ∀ v ∈ W', ∀ w ∈ W, v * w * v⁻¹ = w := fun v hv w hw => by
    rw [hWW' w hw v hv]; group
  have hWnorm : W' ≤ normalizer (W : Set Γ) := by
    intro w' hw'
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw; rw [hcentr w' hw' w hw]; exact hw
    · intro hw
      have h1 := hcentr w'⁻¹ (W'.inv_mem hw') (w' * w * w'⁻¹) hw
      have h2 : w = w' * w * w'⁻¹ := by
        calc w = w'⁻¹ * (w' * w * w'⁻¹) * w'⁻¹⁻¹ := by group
          _ = w' * w * w'⁻¹ := h1
      rw [h2]; exact hw
  obtain ⟨F, hF⟩ : ∃ F : Subgroup Γ, F = W ⊔ W' := ⟨_, rfl⟩
  have hFmem : ∀ f, f ∈ F ↔ ∃ w ∈ W, ∃ w' ∈ W', w * w' = f := by
    intro f
    rw [hF, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left W W' hWnorm]
    exact Set.mem_mul
  have hWF : W ≤ F := hF ▸ le_sup_left
  have hW'F : W' ≤ F := hF ▸ le_sup_right
  have hFQ : F ≤ Q := hF ▸ sup_le hX.le_Q hY.le_Q
  have hFcent : ∀ q ∈ Q, ∀ f ∈ F, q * f = f * q := by
    intro q hq f hf
    obtain ⟨w, hw, w', hw', rfl⟩ := (hFmem f).1 hf
    calc q * (w * w') = (q * w) * w' := by group
      _ = (w * q) * w' := by rw [hX.central q hq w hw]
      _ = w * (q * w') := by group
      _ = w * (w' * q) := by rw [hY.central q hq w' hw']
      _ = (w * w') * q := by group
  have hF2 : ∀ f ∈ F, f ^ 2 = 1 := by
    intro f hf
    obtain ⟨w, hw, w', hw', rfl⟩ := (hFmem f).1 hf
    calc (w * w') ^ 2 = w * (w' * w) * w' := by rw [pow_two]; group
      _ = w * (w * w') * w' := by rw [hWW' w hw w' hw']
      _ = w ^ 2 * w' ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hX.a4.sq_eq_one w hw, hY.a4.sq_eq_one w' hw']; simp
  have hFcomm : ∀ a b : F, a * b = b * a := fun a b => Subtype.ext (hFcent a (hFQ a.2) b b.2)
  have hFcard : Nat.card F ≤ 16 := by
    have hsurj : Function.Surjective (fun p : W × W' =>
        (⟨(p.1 : Γ) * p.2, (hFmem _).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : F)) := by
      rintro ⟨f, hf⟩
      obtain ⟨w, hw, w', hw', rfl⟩ := (hFmem f).1 hf
      exact ⟨(⟨w, hw⟩, ⟨w', hw'⟩), rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, hX.a4.card_W, hY.a4.card_W] at this
    omega
  have hAut : Nat.card (MulAut F) ∣ 20160 :=
    card_mulAut_dvd F hFcomm (fun a => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hF2 a a.2)) hFcard
  have hcF : ∀ f ∈ F, c * f * c⁻¹ ∈ F := by
    intro f hf
    obtain ⟨w, hw, w', hw', rfl⟩ := (hFmem f).1 hf
    have h1 : c * w * c⁻¹ ∈ F := hWF (hX.a4.conj_mem hw)
    have h2 : c * w' * c⁻¹ ∈ F := by
      have h3 := hX.comm_mem w' (hY.le_Q hw')
      have : c * w' * c⁻¹ = (w' * c * w'⁻¹ * c⁻¹)⁻¹ * w' := by group
      rw [this]
      exact F.mul_mem (F.inv_mem (hWF h3)) (hW'F hw')
    have : c * (w * w') * c⁻¹ = (c * w * c⁻¹) * (c * w' * c⁻¹) := by group
    rw [this]; exact F.mul_mem h1 h2
  have hc'F : ∀ f ∈ F, c' * f * c'⁻¹ ∈ F := by
    intro f hf
    obtain ⟨w, hw, w', hw', rfl⟩ := (hFmem f).1 hf
    have h1 : c' * w' * c'⁻¹ ∈ F := hW'F (hY.a4.conj_mem hw')
    have h2 : c' * w * c'⁻¹ ∈ F := by
      have h3 := hY.comm_mem w (hX.le_Q hw)
      have : c' * w * c'⁻¹ = (w * c' * w⁻¹ * c'⁻¹)⁻¹ * w := by group
      rw [this]
      exact F.mul_mem (F.inv_mem (hW'F h3)) (hWF hw)
    have : c' * (w * w') * c'⁻¹ = (c' * w * c'⁻¹) * (c' * w' * c'⁻¹) := by group
    rw [this]; exact F.mul_mem h2 h1
  have hcN : c ∈ normalizer (F : Set Γ) := mem_normalizer_of_pow_three hX.a4.c_pow_three hcF
  have hc'N : c' ∈ normalizer (F : Set Γ) := mem_normalizer_of_pow_three hY.a4.c_pow_three hc'F
  let N : Subgroup Γ := normalizer (F : Set Γ)
  let ρ : N →* MulAut F := F.normalizerMonoidHom
  have hρ : ∀ (x : N) (a : F), ((ρ x a : F) : Γ) = x * a * (x : Γ)⁻¹ := fun x a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe F x a
  let Pstar : Subgroup (MulAut F) := (R.subgroupOf N).map ρ
  have hP3 : IsPGroup 3 Pstar := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := hR (x : Γ) (Subgroup.mem_subgroupOf.1 hx)
    refine ⟨k, Subtype.ext ?_⟩
    show (ρ x) ^ 3 ^ k = 1
    rw [← map_pow]
    have hxq : ((x ^ 3 ^ k : N) : Γ) ∈ Q := by rw [Subgroup.coe_pow]; exact hk
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hρ]
    have := hFcent _ hxq a a.2
    show ((x ^ 3 ^ k : N) : Γ) * a * ((x ^ 3 ^ k : N) : Γ)⁻¹ = a
    rw [this]; group
  have hdvd : Nat.card Pstar ∣ 20160 := (Subgroup.card_subgroup_dvd_card Pstar).trans hAut
  have hcomm := comm_of_isPGroup_three hP3 hdvd
  have hmemP : ∀ g : N, (g : Γ) ∈ R → ρ g ∈ Pstar := fun g hg =>
    Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have key : ρ ⟨c, hcN⟩ * ρ ⟨c', hc'N⟩ = ρ ⟨c', hc'N⟩ * ρ ⟨c, hcN⟩ :=
    congrArg Subtype.val (hcomm ⟨ρ ⟨c, hcN⟩, hmemP _ hcR⟩ ⟨ρ ⟨c', hc'N⟩, hmemP _ hc'R⟩)
  have hzN : c * c' * c⁻¹ * c'⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem hcN hc'N) (N.inv_mem hcN)) (N.inv_mem hc'N)
  have hzρ : ρ ⟨c * c' * c⁻¹ * c'⁻¹, hzN⟩ = 1 := by
    have e : (⟨c * c' * c⁻¹ * c'⁻¹, hzN⟩ : N) =
        ⟨c, hcN⟩ * ⟨c', hc'N⟩ * ⟨c, hcN⟩⁻¹ * ⟨c', hc'N⟩⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, key]
    group
  have hzF : ∀ f ∈ F, (c * c' * c⁻¹ * c'⁻¹) * f * (c * c' * c⁻¹ * c'⁻¹)⁻¹ = f := by
    intro f hf
    have := congrArg (fun φ : MulAut F => ((φ ⟨f, hf⟩ : F) : Γ)) hzρ
    simpa [hρ] using this
  let K : Subgroup Γ :=
    { carrier := {g | g ∈ N ∧ ∀ q ∈ Q, q⁻¹ * (g * q * g⁻¹) ∈ F}
      mul_mem' := by
        rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
        refine ⟨N.mul_mem hgN hhN, fun q hq => ?_⟩
        have h1 := hh q hq
        have h2 := hg q hq
        have h3 : g * (q⁻¹ * (h * q * h⁻¹)) * g⁻¹ ∈ F := (mem_normalizer_iff.1 hgN _).1 h1
        have e : q⁻¹ * (g * h * q * (g * h)⁻¹) =
            (q⁻¹ * (g * q * g⁻¹)) * (g * (q⁻¹ * (h * q * h⁻¹)) * g⁻¹) := by group
        rw [e]; exact F.mul_mem h2 h3
      one_mem' := ⟨N.one_mem, fun q hq => by simp⟩
      inv_mem' := by
        rintro g ⟨hgN, hg⟩
        refine ⟨N.inv_mem hgN, fun q hq => ?_⟩
        have hq' : g⁻¹ * q * g ∈ Q := by
          simpa using Subgroup.Normal.conj_mem inferInstance q hq g⁻¹
        have h1 := hg _ hq'
        have e : q⁻¹ * (g⁻¹ * q * g⁻¹⁻¹) =
            ((g⁻¹ * q * g)⁻¹ * (g * (g⁻¹ * q * g) * g⁻¹))⁻¹ := by group
        rw [e]; exact F.inv_mem h1 }
  have hcK : c ∈ K := ⟨hcN, fun q hq => by
    have := hX.comm_mem q⁻¹ (Q.inv_mem hq)
    have e : q⁻¹ * (c * q * c⁻¹) = q⁻¹ * c * q⁻¹⁻¹ * c⁻¹ := by group
    rw [e]; exact hWF this⟩
  have hc'K : c' ∈ K := ⟨hc'N, fun q hq => by
    have := hY.comm_mem q⁻¹ (Q.inv_mem hq)
    have e : q⁻¹ * (c' * q * c'⁻¹) = q⁻¹ * c' * q⁻¹⁻¹ * c'⁻¹ := by group
    rw [e]; exact hW'F this⟩
  have hzK : c * c' * c⁻¹ * c'⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hcK hc'K) (K.inv_mem hcK)) (K.inv_mem hc'K)
  have hzR : c * c' * c⁻¹ * c'⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hcR hc'R) (R.inv_mem hcR)) (R.inv_mem hc'R)
  generalize hz : c * c' * c⁻¹ * c'⁻¹ = z at hzF hzK hzR
  have hz2 : z ^ 2 ∈ Q := by
    apply hQc
    intro q hq
    exact sq_mul_comm hzF hF2 (hzK.2 q hq)
  obtain ⟨k, hk⟩ := hR z hzR
  exact mem_of_sq_mem_of_pow_mem (Odd.pow (by decide)) hz2 hk

theorem exists_conj_commute [Finite Γ] [Q.Normal]
    (hQ2 : ∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1) {Y W' : Subgroup Γ} {c' : Γ}
    (hX : BlockData Q X W c) (hY : BlockData Q Y W' c')
    (hcc : c * c' * c⁻¹ * c'⁻¹ ∈ Q) :
    ∃ w₀ ∈ W, c' * (w₀ * c * w₀⁻¹) = (w₀ * c * w₀⁻¹) * c' := by
  classical
  have hWfin : Finite W := hX.a4.finite_W
  have hc3 : c ^ 3 = 1 := hX.a4.c_pow_three
  have hccc : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have hc'3 : c' ^ 3 = 1 := hY.a4.c_pow_three
  obtain ⟨y, hy⟩ : ∃ y : Γ, y = c' * c * c'⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have hyQ : y ∈ Q := by
    have : y = (c * c' * c⁻¹ * c'⁻¹)⁻¹ := by rw [hy]; group
    rw [this]; exact Q.inv_mem hcc
  have hyc : y * c = c' * c * c'⁻¹ := by rw [hy]; group
  have hyW : y ∈ W := by
    have h1 : (y * c) ^ 3 = 1 := by
      rw [hyc, pow_three']
      calc c' * c * c'⁻¹ * (c' * c * c'⁻¹) * (c' * c * c'⁻¹) = c' * (c * c * c) * c'⁻¹ := by group
        _ = 1 := by rw [hccc]; group
    have hz₁ : y⁻¹ * c * y * c⁻¹ ∈ W := by
      have := hX.comm_mem y⁻¹ (Q.inv_mem hyQ); simpa using this
    obtain ⟨z₁, hz₁W, hz₁eq⟩ : ∃ z₁ ∈ W, c * y * c⁻¹ = y * z₁ :=
      ⟨y⁻¹ * c * y * c⁻¹, hz₁, by group⟩
    have hz₂W : c * z₁ * c⁻¹ ∈ W := hX.a4.conj_mem hz₁W
    have e2 : c * (c * y * c⁻¹) * c⁻¹ = y * z₁ * (c * z₁ * c⁻¹) := by
      rw [hz₁eq]
      calc c * (y * z₁) * c⁻¹ = (c * y * c⁻¹) * (c * z₁ * c⁻¹) := by group
        _ = y * z₁ * (c * z₁ * c⁻¹) := by rw [hz₁eq]
    have e3 : (y * c) ^ 3 = y * (c * y * c⁻¹) * (c * (c * y * c⁻¹) * c⁻¹) * (c * c * c) := by
      rw [pow_three']; group
    have hyz : y * z₁ = z₁ * y := hX.central y hyQ z₁ hz₁W
    have e4 : y * (y * z₁) * (y * z₁ * (c * z₁ * c⁻¹)) =
        y ^ 3 * (z₁ * z₁ * (c * z₁ * c⁻¹)) := by
      calc y * (y * z₁) * (y * z₁ * (c * z₁ * c⁻¹)) = y * y * (z₁ * y) * z₁ * (c * z₁ * c⁻¹) := by
            group
        _ = y * y * (y * z₁) * z₁ * (c * z₁ * c⁻¹) := by rw [hyz]
        _ = y ^ 3 * (z₁ * z₁ * (c * z₁ * c⁻¹)) := by rw [pow_three']; group
    rw [e3, e2, hz₁eq, hccc, mul_one, e4] at h1
    have hy3 : y ^ 3 ∈ W := by
      have : y ^ 3 = (z₁ * z₁ * (c * z₁ * c⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact W.inv_mem (W.mul_mem (W.mul_mem hz₁W hz₁W) hz₂W)
    exact mem_of_pow_three_mem hy3 (hQ2 y hyQ)
  let S : Set Γ := (fun w => w * c) '' (W : Set Γ)
  have hS : S.ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective c), ← Nat.card_coe_set_eq]
    exact hX.a4.card_W
  have hconj : ∀ w ∈ W, ∃ w₀ ∈ W, w * c = w₀ * c * w₀⁻¹ := by
    intro w hw
    obtain ⟨w₀, hw₀, hw₀eq⟩ := hX.a4.exists_mul_conj_inv_eq hw
    exact ⟨w₀, hw₀, by rw [← hw₀eq]; group⟩
  have hmap : ∀ s ∈ S, c' * s * c'⁻¹ ∈ S := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨w₀, hw₀, hwc⟩ := hconj w hw
    have hx'Q : c' * w₀ * c'⁻¹ ∈ Q :=
      Subgroup.Normal.conj_mem inferInstance w₀ (hX.le_Q hw₀) c'
    have hxy : (c' * w₀ * c'⁻¹) * y = y * (c' * w₀ * c'⁻¹) := hX.central _ hx'Q y hyW
    have e : c' * (w * c) * c'⁻¹ =
        (y * ((c' * w₀ * c'⁻¹) * c * (c' * w₀ * c'⁻¹)⁻¹ * c⁻¹)) * c := by
      show c' * (w * c) * c'⁻¹ = _
      rw [hwc]
      calc c' * (w₀ * c * w₀⁻¹) * c'⁻¹
          = (c' * w₀ * c'⁻¹) * (c' * c * c'⁻¹) * (c' * w₀ * c'⁻¹)⁻¹ := by group
        _ = (c' * w₀ * c'⁻¹) * (y * c) * (c' * w₀ * c'⁻¹)⁻¹ := by rw [hyc]
        _ = ((c' * w₀ * c'⁻¹) * y) * c * (c' * w₀ * c'⁻¹)⁻¹ := by group
        _ = (y * (c' * w₀ * c'⁻¹)) * c * (c' * w₀ * c'⁻¹)⁻¹ := by rw [hxy]
        _ = (y * ((c' * w₀ * c'⁻¹) * c * (c' * w₀ * c'⁻¹)⁻¹ * c⁻¹)) * c := by group
    refine ⟨y * ((c' * w₀ * c'⁻¹) * c * (c' * w₀ * c'⁻¹)⁻¹ * c⁻¹), ?_, e.symm⟩
    exact W.mul_mem hyW (hX.comm_mem _ hx'Q)
  obtain ⟨s, ⟨w, hw, rfl⟩, hs⟩ := exists_fixed_conj hS hc'3 hmap
  obtain ⟨w₀, hw₀, hwc⟩ := hconj w hw
  refine ⟨w₀, hw₀, ?_⟩
  have hs' : c' * (w * c) * c'⁻¹ = w * c := hs
  rw [hwc] at hs'
  calc c' * (w₀ * c * w₀⁻¹) = (c' * (w₀ * c * w₀⁻¹) * c'⁻¹) * c' := by group
    _ = (w₀ * c * w₀⁻¹) * c' := by rw [hs']

theorem normalizes_of_commute [Q.Normal] {c' : Γ} (hX : BlockData Q X W c) (hcc : c * c' = c' * c) :
    ∀ w ∈ W, c' * w * c'⁻¹ ∈ W := by
  intro w hw
  obtain ⟨w₀, hw₀, rfl⟩ := hX.a4.exists_mul_conj_inv_eq hw
  have hyQ : c' * w₀ * c'⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance w₀ (hX.le_Q hw₀) c'
  have hcc' : c' * c * c'⁻¹ = c := by
    calc c' * c * c'⁻¹ = c * c' * c'⁻¹ := by rw [hcc]
      _ = c := by group
  have hcc'' : c' * c⁻¹ * c'⁻¹ = c⁻¹ := by
    calc c' * c⁻¹ * c'⁻¹ = (c' * c * c'⁻¹)⁻¹ := by group
      _ = c⁻¹ := by rw [hcc']
  have e : c' * (w₀ * (c * w₀⁻¹ * c⁻¹)) * c'⁻¹ =
      (c' * w₀ * c'⁻¹) * c * (c' * w₀ * c'⁻¹)⁻¹ * c⁻¹ := by
    calc c' * (w₀ * (c * w₀⁻¹ * c⁻¹)) * c'⁻¹
        = (c' * w₀ * c'⁻¹) * (c' * c * c'⁻¹) * (c' * w₀⁻¹ * c'⁻¹) * (c' * c⁻¹ * c'⁻¹) := by group
      _ = (c' * w₀ * c'⁻¹) * c * (c' * w₀ * c'⁻¹)⁻¹ * c⁻¹ := by rw [hcc', hcc'']; group
  rw [e]
  exact hX.comm_mem _ hyQ

theorem le_of_not_centralizes [Q.Normal] {Y W' : Subgroup Γ} {c' : Γ} (hX : BlockData Q X W c)
    (hY : BlockData Q Y W' c') (hcc : c * c' = c' * c)
    (hne : ¬ ∀ w ∈ W, c' * w * c'⁻¹ = w) : W ≤ W' := by
  have hnorm := normalizes_of_commute hX hcc
  have hfpf : ∀ w ∈ W, w ≠ 1 → c' * w * c'⁻¹ ≠ w := by
    intro u hu hu1 hfix
    exact hne (centralizes_of_fixes hX.a4 (CommutesOn.of_commute hcc.symm) hu hu1 hfix)
  intro w hw
  obtain ⟨w₀, hw₀, hw₀eq⟩ := exists_mul_conj_inv_eq_of_fpf hX.a4 hnorm hfpf hw
  have h1 := hY.comm_mem w₀ (hX.le_Q hw₀)
  have e : w₀ * (c' * w₀⁻¹ * c'⁻¹) = w₀ * c' * w₀⁻¹ * c'⁻¹ := by group
  rw [← hw₀eq, e]
  exact h1

theorem eq_of_W_eq [Finite Γ] [Q.Normal] (hQ2 : ∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1)
    (hQc : ∀ g : Γ, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) {Y : Subgroup Γ} {c' : Γ}
    (hX : BlockData Q X W c) (hY : BlockData Q Y W c') (hcc : c * c' = c' * c) : Y = X := by
  have hnorm := normalizes_of_commute hX hcc
  obtain ⟨j, hj⟩ := exists_pow_conj_eq hX.a4 (CommutesOn.of_commute hcc.symm) hnorm
  have hc3 : c ^ 3 = 1 := hX.a4.c_pow_three
  have hc'3 : c' ^ 3 = 1 := hY.a4.c_pow_three
  obtain ⟨a, ha⟩ : ∃ a : Γ, a = c ^ (2 * j) := ⟨_, rfl⟩
  have hab : a * c ^ j = 1 := by
    rw [ha, ← pow_add, show 2 * j + j = 3 * j by ring, pow_mul, hc3, one_pow]
  have hac' : Commute a c' := ha ▸ (show Commute c c' from hcc).pow_left (2 * j)
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← pow_mul, show 2 * j * 3 = 3 * (2 * j) by ring, pow_mul, hc3, one_pow]
  have haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W := fun w hw => by
    have := (mem_normalizer_iff.1 (pow_mem hX.a4.mem_normalizer (2 * j)) w).1 hw
    rwa [← ha] at this
  have hgW : ∀ w ∈ W, (a * c') * w * (a * c')⁻¹ = w := by
    intro w hw
    calc (a * c') * w * (a * c')⁻¹ = a * (c' * w * c'⁻¹) * a⁻¹ := by group
      _ = a * (c ^ j * w * (c ^ j)⁻¹) * a⁻¹ := by rw [hj w hw]
      _ = (a * c ^ j) * w * (a * c ^ j)⁻¹ := by group
      _ = w := by rw [hab]; simp
  have hgq : ∀ q ∈ Q, q⁻¹ * ((a * c') * q * (a * c')⁻¹) ∈ W := by
    intro q hq
    have h1 : q⁻¹ * c' * q * c'⁻¹ ∈ W := by simpa using hY.comm_mem q⁻¹ (Q.inv_mem hq)
    have h2 : q⁻¹ * (a * q * a⁻¹) ∈ W := by
      have := hX.pow_comm_mem (2 * j) q hq
      rwa [← ha] at this
    have h3 : a * (q⁻¹ * c' * q * c'⁻¹) * a⁻¹ ∈ W := haW _ h1
    have e : q⁻¹ * ((a * c') * q * (a * c')⁻¹) =
        (q⁻¹ * (a * q * a⁻¹)) * (a * (q⁻¹ * c' * q * c'⁻¹) * a⁻¹) := by group
    rw [e]; exact W.mul_mem h2 h3
  have hg2 : (a * c') ^ 2 ∈ Q := by
    apply hQc
    intro q hq
    exact sq_mul_comm (F := W) hgW hX.a4.sq_eq_one (hgq q hq)
  have hg3 : (a * c') ^ 3 = 1 := by
    rw [hac'.mul_pow, ha3, hc'3, one_mul]
  have hg2' : (a * c') ^ 2 = 1 := by
    have h1 : ((a * c') ^ 2) ^ 3 ∈ (⊥ : Subgroup Γ) := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hg3, one_pow]
      exact Subgroup.one_mem _
    exact Subgroup.mem_bot.1 (mem_of_pow_three_mem h1 (hQ2 _ hg2))
  have hg1 : a * c' = 1 := by
    calc a * c' = (a * c') ^ 3 * ((a * c') ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg3, hg2']; simp
  have hc'X : c' ∈ X := by
    have : c' = a⁻¹ := eq_inv_of_mul_eq_one_right hg1
    rw [this, ha]
    exact X.inv_mem (X.pow_mem hX.a4.mem_X _)
  have hYX : Y ≤ X := by
    rw [hY.a4.eq_sup]
    exact sup_le hX.a4.le (zpowers_le.2 hc'X)
  have hXfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hX.a4.card_X]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hYX (by rw [hX.a4.card_X, hY.a4.card_X])

theorem commute_or_eq_of_commute [Finite Γ] [Q.Normal] (hQ2 : ∀ q ∈ Q, ∃ m : ℕ, q ^ 2 ^ m = 1)
    (hQc : ∀ g : Γ, (∀ q ∈ Q, g * q = q * g) → g ∈ Q) {Y W' : Subgroup Γ} {c' : Γ}
    (hX : BlockData Q X W c) (hY : BlockData Q Y W' c') (hcc : c * c' = c' * c) :
    X = Y ∨ ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  have hWW'eq : (¬ ∀ w ∈ W, c' * w * c'⁻¹ = w) ∨ (¬ ∀ w' ∈ W', c * w' * c⁻¹ = w') → W = W' := by
    rintro (h | h)
    · exact Subgroup.eq_of_le_of_card_ge (le_of_not_centralizes hX hY hcc h)
        (by rw [hX.a4.card_W, hY.a4.card_W])
    · exact (Subgroup.eq_of_le_of_card_ge (le_of_not_centralizes hY hX hcc.symm h)
        (by rw [hX.a4.card_W, hY.a4.card_W])).symm
  by_cases h1 : ∀ w ∈ W, c' * w * c'⁻¹ = w
  · by_cases h2 : ∀ w' ∈ W', c * w' * c⁻¹ = w'
    · right
      intro x hx y hy
      obtain ⟨w, hw, k, rfl⟩ := hX.a4.mem_decomp hx
      obtain ⟨w', hw', l, rfl⟩ := hY.a4.mem_decomp hy
      have f1 : w * w' = w' * w := hY.central w (hX.le_Q hw) w' hw'
      have hcw' : Commute c w' := by
        show c * w' = w' * c
        calc c * w' = (c * w' * c⁻¹) * c := by group
          _ = w' * c := by rw [h2 w' hw']
      have hc'w : Commute c' w := by
        show c' * w = w * c'
        calc c' * w = (c' * w * c'⁻¹) * c' := by group
          _ = w * c' := by rw [h1 w hw]
      have f2 : Commute (c ^ k) w' := hcw'.zpow_left k
      have f3 : Commute (c' ^ l) w := hc'w.zpow_left l
      have f4 : Commute (c ^ k) (c' ^ l) := (show Commute c c' from hcc).zpow_zpow k l
      calc w * c ^ k * (w' * c' ^ l) = w * (c ^ k * w') * c' ^ l := by group
        _ = w * (w' * c ^ k) * c' ^ l := by rw [f2.eq]
        _ = (w * w') * (c ^ k * c' ^ l) := by group
        _ = (w' * w) * (c' ^ l * c ^ k) := by rw [f1, f4.eq]
        _ = w' * (w * c' ^ l) * c ^ k := by group
        _ = w' * (c' ^ l * w) * c ^ k := by rw [f3.eq]
        _ = w' * c' ^ l * (w * c ^ k) := by group
    · left
      obtain rfl := hWW'eq (Or.inr h2)
      exact (eq_of_W_eq hQ2 hQc hX hY hcc).symm
  · left
    obtain rfl := hWW'eq (Or.inl h1)
    exact (eq_of_W_eq hQ2 hQc hX hY hcc).symm

end CFSG.Quasithin.S14110.Commute
