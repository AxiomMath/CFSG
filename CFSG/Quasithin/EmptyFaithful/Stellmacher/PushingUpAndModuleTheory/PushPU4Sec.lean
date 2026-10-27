module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDict
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
public import CFSG.Quasithin.EmptyFaithful.SzF53MUni

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

section Quotient

variable {X S Z : Subgroup G}

theorem relIndex_core_eq_120 (e : OTwoQuot X ≃* Perm (Fin 5)) :
    (pCoreOf 2 X).relIndex X = 120 := by
  have h1 : (pCoreOf 2 X).relIndex X = (CFSG.Open.pCore 2 ↥X).index := by
    unfold Subgroup.relIndex Subgroup.subgroupOf pCoreOf
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  rw [h1, Subgroup.index_eq_card, show Nat.card (↥X ⧸ CFSG.Open.pCore 2 ↥X) =
    Nat.card (Perm (Fin 5)) from Nat.card_congr e.toEquiv, Nat.card_perm]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem relIndex_core_sylow_eq_eight [Finite G] (h : PushHyp X S Z)
    (e : OTwoQuot X ≃* Perm (Fin 5)) : (pCoreOf 2 X).relIndex S = 8 := by
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) S X h.core_le h.le_self
  rw [relIndex_core_eq_120 e] at h1
  have hodd : ¬ 2 ∣ S.relIndex X := h.sylow.2.2
  obtain ⟨n, hn⟩ := h.sylow.2.1.index ((pCoreOf 2 X).subgroupOf S)
  have hn' : (pCoreOf 2 X).relIndex S = 2 ^ n := hn
  rw [hn'] at h1 ⊢
  rcases n with _ | _ | _ | _ | n
  · exfalso; apply hodd; rw [pow_zero, one_mul] at h1; rw [h1]; norm_num
  · exfalso; apply hodd; have : S.relIndex X = 60 := by omega
    rw [this]; norm_num
  · exfalso; apply hodd; have : S.relIndex X = 30 := by omega
    rw [this]; norm_num
  · rfl
  · exfalso
    have : 120 = 16 * (2 ^ n * S.relIndex X) := by rw [← h1]; ring
    omega

theorem exists_mem_residual_of_odd [Finite G] {Y X : Subgroup G} (hYX : Y ≤ X)
    (θ : ↥X →* Perm (Fin 5)) {x : G} (hx : x ∈ Y) {σ : Perm (Fin 5)}
    (hσ : θ ⟨x, hYX hx⟩ = σ) {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1) :
    ∃ l ∈ pResidualOf 2 Y, ∃ hl : l ∈ X, θ ⟨l, hl⟩ = σ := by
  obtain ⟨k, hk⟩ := exists_pow_mem_pResidualOf Y hx
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hm)
  by_cases hm1 : m = 1
  · subst hm1
    have h1 : σ = 1 := by simpa using hσm
    refine ⟨1, one_mem _, X.one_mem, ?_⟩
    rw [h1]
    exact map_one θ
  have hm1' : 1 < m := by obtain ⟨t, rfl⟩ := hm; omega
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm1'
  have hl : (x ^ 2 ^ k) ^ j ∈ pResidualOf 2 Y := Subgroup.pow_mem _ hk _
  have hlX : (x ^ 2 ^ k) ^ j ∈ X := hYX (pResidualOf_le_self Y hl)
  refine ⟨_, hl, hlX, ?_⟩
  have e : (⟨(x ^ 2 ^ k) ^ j, hlX⟩ : ↥X) = ⟨x, hYX hx⟩ ^ (2 ^ k * j) := by
    apply Subtype.ext
    simp [pow_mul]
  rw [e, map_pow, hσ]
  conv_rhs => rw [← pow_one σ]
  rw [← Nat.div_add_mod (2 ^ k * j) m, pow_add, pow_mul, hσm, one_pow, one_mul, hj]

end Quotient

section Twist

variable {K L X : Subgroup G} [(L.subgroupOf X).Normal] {Ψ : ↥K →* Perm (Fin 5)}
  {β : orth.W →* ↥X ⧸ L.subgroupOf X}

theorem secData_twist (h : SecData orth K L X Ψ β) (g : Perm (Fin 5)) :
    SecData orth K L X ((MulAut.conj g⁻¹).toMonoidHom.comp Ψ) (β.comp (orth.act g).toMonoidHom) := by
  refine ⟨fun y => ?_, fun a b hab => ?_, fun k u x hu => ?_⟩
  · obtain ⟨u, hu⟩ := h.surj y
    exact ⟨(orth.act g).symm u, by simpa using hu⟩
  · exact (MulEquiv.injective _) (h.inj hab)
  · obtain ⟨hkx, h1⟩ := h.equiv k (orth.act g u) x hu
    refine ⟨hkx, ?_⟩
    have e : (orth.act g) ((orth.act ((MulAut.conj g⁻¹).toMonoidHom (Ψ k))) u) =
        orth.act (Ψ k) (orth.act g u) := by
      rw [← act_mul_apply, ← act_mul_apply]
      congr 2
      simp [mul_assoc]
    show β ((orth.act g) ((orth.act ((MulAut.conj g⁻¹).toMonoidHom (Ψ k))) u)) = _
    rw [e]
    exact h1

end Twist

structure OrthFacts (X S Z Z₀ : Subgroup G) (θ : ↥X →* Perm (Fin 5)) : Prop where
  surj : Function.Surjective θ
  ker : ∀ (x : G) (hx : x ∈ X), θ ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 X
  map_S : (S.subgroupOf X).map θ = S5Syl
  relIndex_fix : ∀ A : Subgroup G, A ≤ X →
    (fixSecIn A Z₀ Z).relIndex Z =
      (fixW orth ((A.subgroupOf X).map θ)).index
  mem_fix : ∀ (A : Subgroup G) (z : G),
    z ∈ fixSecIn A Z₀ Z ↔
      z ∈ Z ∧ ∀ a ∈ A, a * z * a⁻¹ * z⁻¹ ∈ Z₀
  norm : X ≤ Subgroup.normalizer (Z₀ : Set G)
  relIndex_Z0 : Z₀.relIndex Z = 16

section Facts

variable [Finite G] {X S Z Z₀ : Subgroup G}

theorem exists_orthFacts (h : PushHyp X S Z) (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hZ₀Z : Z₀ ≤ Z) (hO : IsOrthSec X Z₀ Z) :
    ∃ θ : ↥X →* Perm (Fin 5), OrthFacts X S Z Z₀ θ := by
  obtain ⟨e⟩ := hq
  obtain ⟨hn, θ₀, β₀, hθ₀s, hθ₀k, hsd₀⟩ := id hO
  have : (Z₀.subgroupOf Z).Normal := hn
  have hle : (pCoreOf 2 X).subgroupOf X ≤ θ₀.ker := by
    intro x hx
    have hxQ : (x : G) ∈ pCoreOf 2 X := hx
    rw [hθ₀k, Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨x.2, fun y hy => ?_⟩
    have hc : y * (x : G) = (x : G) * y :=
      Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer hxQ) y hy
    have e1 : (x : G) * y * (x : G)⁻¹ * y⁻¹ = 1 := by rw [← hc]; group
    rw [e1]
    exact Z₀.one_mem
  have hidx0 : θ₀.ker.index = 120 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθ₀s, Subgroup.card_top, Nat.card_perm]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hker : θ₀.ker = (pCoreOf 2 X).subgroupOf X := by
    have h1 := Subgroup.relIndex_mul_index hle
    have h2 : ((pCoreOf 2 X).subgroupOf X).index = 120 := relIndex_core_eq_120 e
    rw [hidx0, h2] at h1
    have h3 : ((pCoreOf 2 X).subgroupOf X).relIndex θ₀.ker = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) hle
  have hcard : Nat.card ((S.subgroupOf X).map θ₀) = 8 := by
    rw [← Subgroup.relIndex_ker (S.subgroupOf X) θ₀, hker, Subgroup.relIndex_subgroupOf h.le_self]
    exact relIndex_core_sylow_eq_eight h e
  obtain ⟨g, hg⟩ := exists_conj_S5Syl hcard
  have hsd := secData_twist hsd₀ g
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp θ₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj g⁻¹).surjective.comp hθ₀s
  · intro x hx
    show (MulAut.conj g⁻¹) (θ₀ ⟨x, hx⟩) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  · rw [← Subgroup.map_map, hg]
    ext σ
    rw [mem_map_conj, mem_map_conj]
    simp [mul_assoc]
  · exact fun A hA => hsd.relIndex_fixSecIn hZ₀Z hA
  · exact fun A z => X1512.mem_fixSecIn hZ₀Z
  · exact (IsModelSec.isSec hO hZ₀Z).normL
  · exact hsd₀.relIndex_eq.trans card_orth

end Facts

end CFSG.Quasithin.F53Push
