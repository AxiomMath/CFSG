module

public import CFSG.Quasithin.Vol2.Ch10SecQ34LG
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A129Native
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_conj_mul (A : Subgroup G) (a b : G) :
    A.map (MulAut.conj (a * b)).toMonoidHom =
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext x
  simp

theorem open_pCore_eq (p : ℕ) (Q : Type*) [Group Q] : CFSG.Open.pCore p Q = CFSG.pCore p Q :=
  CFSG.Open.pCore_eq_pCore p Q

theorem mem_pCoreOf_iff {K : Subgroup G} {x : G} (hx : x ∈ K) :
    x ∈ pCoreOf 2 K ↔ (⟨x, hx⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨_, h, rfl⟩

structure PairCtx (H K₁ K₂ : Subgroup G)
    (φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)) : Prop where
  mem₁ : K₁ ∈ cComp H
  mem₂ : K₂ ∈ cComp H
  ne : K₁ ≠ K₂
  comm : ∀ L₁ L₂ : Subgroup G, L₁ ∈ cComp H → L₂ ∈ cComp H → L₁ ≠ L₂ →
    ⁅L₁, L₂⁆ ≤ pCoreOf 2 L₁ ⊓ pCoreOf 2 L₂
  normal : H ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)
  surj : Function.Surjective φ
  ker : φ.ker = (pCoreOf 2 (K₁ ⊔ K₂)).subgroupOf (K₁ ⊔ K₂)
  app₁ : ∀ (k : G) (hk : k ∈ K₁), φ ⟨k, Subgroup.mem_sup_left hk⟩ =
    (((⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁), 1)
  app₂ : ∀ (k : G) (hk : k ∈ K₂), φ ⟨k, Subgroup.mem_sup_right hk⟩ =
    (1, ((⟨k, hk⟩ : ↥K₂) : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂))
  center₁ : Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = ⊥
  center₂ : Subgroup.center (↥K₂ ⧸ CFSG.pCore 2 ↥K₂) = ⊥

namespace PairCtx

variable {H K₁ K₂ : Subgroup G}
  {φ : ↥(K₁ ⊔ K₂) →* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) × (↥K₂ ⧸ CFSG.pCore 2 ↥K₂)}

theorem le_normalizer₁₂ (hc : PairCtx H K₁ K₂ φ) : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_right.mpr
    (((hc.comm K₁ K₂ hc.mem₁ hc.mem₂ hc.ne).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K₂))

theorem exists_mul (hc : PairCtx H K₁ K₂ φ) {z : G} (hz : z ∈ K₁ ⊔ K₂) :
    ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, k₁ * k₂ = z := by
  have h : z ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ hc.le_normalizer₁₂] at h
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := Set.mem_mul.mp h
  exact ⟨k₁, hk₁, k₂, hk₂, hk⟩

theorem app_mul (hc : PairCtx H K₁ K₂ φ) {k₁ k₂ : G} (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (hk : k₁ * k₂ ∈ K₁ ⊔ K₂) :
    φ ⟨k₁ * k₂, hk⟩ = (((⟨k₁, hk₁⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁),
      ((⟨k₂, hk₂⟩ : ↥K₂) : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂)) := by
  have e : (⟨k₁ * k₂, hk⟩ : ↥(K₁ ⊔ K₂)) =
      ⟨k₁, Subgroup.mem_sup_left hk₁⟩ * ⟨k₂, Subgroup.mem_sup_right hk₂⟩ := rfl
  rw [e, map_mul, hc.app₁ k₁ hk₁, hc.app₂ k₂ hk₂, Prod.mk_mul_mk, mul_one, one_mul]

theorem app_mul' (hc : PairCtx H K₁ K₂ φ) {k₁ k₂ : G} (hk₁ : k₁ ∈ K₁) (hk₂ : k₂ ∈ K₂)
    (hk : k₂ * k₁ ∈ K₁ ⊔ K₂) :
    φ ⟨k₂ * k₁, hk⟩ = (((⟨k₁, hk₁⟩ : ↥K₁) : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁),
      ((⟨k₂, hk₂⟩ : ↥K₂) : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂)) := by
  have e : (⟨k₂ * k₁, hk⟩ : ↥(K₁ ⊔ K₂)) =
      ⟨k₂, Subgroup.mem_sup_right hk₂⟩ * ⟨k₁, Subgroup.mem_sup_left hk₁⟩ := rfl
  rw [e, map_mul, hc.app₁ k₁ hk₁, hc.app₂ k₂ hk₂, Prod.mk_mul_mk, mul_one, one_mul]

theorem app_eq_one_of_mem₁ (hc : PairCtx H K₁ K₂ φ) {x : G} (hx : x ∈ pCoreOf 2 K₁)
    (hxK : x ∈ K₁ ⊔ K₂) : φ ⟨x, hxK⟩ = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  change φ ⟨(y : G), Subgroup.mem_sup_left y.2⟩ = 1
  rw [hc.app₁ y y.2]
  exact Prod.ext ((QuotientGroup.eq_one_iff y).mpr hy) rfl

theorem app_eq_one_of_mem₂ (hc : PairCtx H K₁ K₂ φ) {x : G} (hx : x ∈ pCoreOf 2 K₂)
    (hxK : x ∈ K₁ ⊔ K₂) : φ ⟨x, hxK⟩ = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  change φ ⟨(y : G), Subgroup.mem_sup_right y.2⟩ = 1
  rw [hc.app₂ y y.2]
  exact Prod.ext rfl ((QuotientGroup.eq_one_iff y).mpr hy)

theorem map_conj_eq [Finite G] (hc : PairCtx H K₁ K₂ φ) {g : G} (hg : g ∈ H) {L : Subgroup G}
    (hL : L = K₁ ∨ L = K₂) :
    L.map (MulAut.conj g).toMonoidHom = K₁ ∨ L.map (MulAut.conj g).toMonoidHom = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hLH : L ∈ cComp H := by
    rcases hL with rfl | rfl
    exacts [hc.mem₁, hc.mem₂]
  have hL'H : L' ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj g) hLH
    rwa [A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hg)] at h1
  have hLK : L ≤ K₁ ⊔ K₂ := by
    rcases hL with rfl | rfl
    exacts [le_sup_left, le_sup_right]
  have hL'K : L' ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hc.normal hg) l).mp (hLK hl)
  by_contra hne
  push Not at hne
  obtain ⟨hne₁, hne₂⟩ := hne
  have h₁ := hc.comm L' K₁ hL'H hc.mem₁ hne₁
  have h₂ := hc.comm L' K₂ hL'H hc.mem₂ hne₂
  have hφ : ∀ l (hl : l ∈ L'), φ ⟨l, hL'K hl⟩ = 1 := by
    intro l hl
    have hcomm : ∀ (k : G) (hk : k ∈ K₁ ⊔ K₂), k ∈ K₁ ∨ k ∈ K₂ →
        φ ⟨l, hL'K hl⟩ * φ ⟨k, hk⟩ = φ ⟨k, hk⟩ * φ ⟨l, hL'K hl⟩ := by
      intro k hk hk'
      have hcK : ⁅l, k⁆ ∈ K₁ ⊔ K₂ :=
        (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).mul_mem (hL'K hl) hk)
          ((K₁ ⊔ K₂).inv_mem (hL'K hl))) ((K₁ ⊔ K₂).inv_mem hk)
      have h1 : φ ⟨⁅l, k⁆, hcK⟩ = 1 := by
        rcases hk' with hk' | hk'
        · exact hc.app_eq_one_of_mem₁ (h₁ (Subgroup.commutator_mem_commutator hl hk')).2 hcK
        · exact hc.app_eq_one_of_mem₂ (h₂ (Subgroup.commutator_mem_commutator hl hk')).2 hcK
      have e : (⟨⁅l, k⁆, hcK⟩ : ↥(K₁ ⊔ K₂)) = ⁅(⟨l, hL'K hl⟩ : ↥(K₁ ⊔ K₂)), ⟨k, hk⟩⁆ := rfl
      rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hz₁ : (φ ⟨l, hL'K hl⟩).1 ∈ Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have := congrArg Prod.fst (hcomm k (Subgroup.mem_sup_left hk) (Or.inl hk))
      rw [Prod.fst_mul, Prod.fst_mul, hc.app₁ k hk] at this
      exact this.symm
    have hz₂ : (φ ⟨l, hL'K hl⟩).2 ∈ Subgroup.center (↥K₂ ⧸ CFSG.pCore 2 ↥K₂) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have := congrArg Prod.snd (hcomm k (Subgroup.mem_sup_right hk) (Or.inr hk))
      rw [Prod.snd_mul, Prod.snd_mul, hc.app₂ k hk] at this
      exact this.symm
    rw [hc.center₁, Subgroup.mem_bot] at hz₁
    rw [hc.center₂, Subgroup.mem_bot] at hz₂
    exact Prod.ext hz₁ hz₂
  have hO : L' ≤ pCoreOf 2 (K₁ ⊔ K₂) := fun l hl => by
    have h := hφ l hl
    rw [← MonoidHom.mem_ker, hc.ker, Subgroup.mem_subgroupOf] at h
    exact h
  exact ne_bot_of_mem_cComp hL'H (Vol2Native.eq_bot_of_perfect_of_isPGroup L'
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hO) (perfect_of_mem_cComp hL'H))

theorem fix_or_swap [Finite G] (hc : PairCtx H K₁ K₂ φ) {g : G} (hg : g ∈ H) :
    (K₁.map (MulAut.conj g).toMonoidHom = K₁ ∧ K₂.map (MulAut.conj g).toMonoidHom = K₂) ∨
      (K₁.map (MulAut.conj g).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj g).toMonoidHom = K₁) := by
  have hinj : ∀ B₁ B₂ : Subgroup G, B₁.map (MulAut.conj g).toMonoidHom =
      B₂.map (MulAut.conj g).toMonoidHom → B₁ = B₂ :=
    fun B₁ B₂ h => Subgroup.map_injective (MulAut.conj g).injective h
  rcases hc.map_conj_eq hg (Or.inl rfl) with h1 | h1 <;>
    rcases hc.map_conj_eq hg (Or.inr rfl) with h2 | h2
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hc.ne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj _ _ (h1.trans h2.symm)) hc.ne

theorem fix_of_odd [Finite G] (hc : PairCtx H K₁ K₂ φ) {g : G} (hg : g ∈ H)
    (hodd : Odd (orderOf g)) :
    K₁.map (MulAut.conj g).toMonoidHom = K₁ ∧ K₂.map (MulAut.conj g).toMonoidHom = K₂ := by
  rcases hc.fix_or_swap hg with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hsq : K₁.map (MulAut.conj (g * g)).toMonoidHom = K₁ := by
      rw [map_conj_mul, h1, h2]
    have heven : ∀ i : ℕ, K₁.map (MulAut.conj (g ^ (2 * i))).toMonoidHom = K₁ := by
      intro i
      induction i with
      | zero => rw [mul_zero, pow_zero, map_conj_one]
      | succ i ih =>
        rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, sq, map_conj_mul, hsq, ih]
    obtain ⟨i, hi⟩ := hodd
    have h3 : K₁.map (MulAut.conj (g ^ (2 * i + 1))).toMonoidHom = K₂ := by
      rw [pow_succ', map_conj_mul, heven, h1]
    rw [← hi, pow_orderOf_eq_one, map_conj_one] at h3
    exact hc.ne h3

theorem app_conj_fix (hc : PairCtx H K₁ K₂ φ) {n : G}
    (h₁ : K₁.map (MulAut.conj n).toMonoidHom = K₁) (h₂ : K₂.map (MulAut.conj n).toMonoidHom = K₂)
    {z : G} (hz : z ∈ K₁ ⊔ K₂) (hz' : n * z * n⁻¹ ∈ K₁ ⊔ K₂) :
    φ ⟨n * z * n⁻¹, hz'⟩ =
      (conjQuot K₁ K₁ n h₁ (φ ⟨z, hz⟩).1, conjQuot K₂ K₂ n h₂ (φ ⟨z, hz⟩).2) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hc.exists_mul hz
  have hm₁ : n * k₁ * n⁻¹ ∈ K₁ := by
    have := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hk₁
    rw [h₁] at this
    exact this
  have hm₂ : n * k₂ * n⁻¹ ∈ K₂ := by
    have := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hk₂
    rw [h₂] at this
    exact this
  have e : n * (k₁ * k₂) * n⁻¹ = (n * k₁ * n⁻¹) * (n * k₂ * n⁻¹) := by group
  have hz'' : (n * k₁ * n⁻¹) * (n * k₂ * n⁻¹) ∈ K₁ ⊔ K₂ := e ▸ hz'
  rw [show (⟨n * (k₁ * k₂) * n⁻¹, hz'⟩ : ↥(K₁ ⊔ K₂)) = ⟨_, hz''⟩ from Subtype.ext e,
    hc.app_mul hm₁ hm₂, hc.app_mul hk₁ hk₂, conjQuot_mk h₁ hk₁ hm₁, conjQuot_mk h₂ hk₂ hm₂]

theorem app_conj_swap (hc : PairCtx H K₁ K₂ φ) {g : G}
    (h₁₂ : K₁.map (MulAut.conj g).toMonoidHom = K₂)
    (h₂₁ : K₂.map (MulAut.conj g).toMonoidHom = K₁)
    {z : G} (hz : z ∈ K₁ ⊔ K₂) (hz' : g * z * g⁻¹ ∈ K₁ ⊔ K₂) :
    φ ⟨g * z * g⁻¹, hz'⟩ =
      (conjQuot K₂ K₁ g h₂₁ (φ ⟨z, hz⟩).2, conjQuot K₁ K₂ g h₁₂ (φ ⟨z, hz⟩).1) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hc.exists_mul hz
  have hm₁ : g * k₁ * g⁻¹ ∈ K₂ := by
    have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk₁
    rw [h₁₂] at this
    exact this
  have hm₂ : g * k₂ * g⁻¹ ∈ K₁ := by
    have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk₂
    rw [h₂₁] at this
    exact this
  have e : g * (k₁ * k₂) * g⁻¹ = (g * k₁ * g⁻¹) * (g * k₂ * g⁻¹) := by group
  have hz'' : (g * k₁ * g⁻¹) * (g * k₂ * g⁻¹) ∈ K₁ ⊔ K₂ := e ▸ hz'
  rw [show (⟨g * (k₁ * k₂) * g⁻¹, hz'⟩ : ↥(K₁ ⊔ K₂)) = ⟨_, hz''⟩ from Subtype.ext e,
    hc.app_mul' hm₂ hm₁, hc.app_mul hk₁ hk₂, conjQuot_mk h₂₁ hk₂ hm₂, conjQuot_mk h₁₂ hk₁ hm₁]

end PairCtx

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
