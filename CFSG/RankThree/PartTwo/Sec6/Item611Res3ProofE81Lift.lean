module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofE81
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item64
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def KS611E81Inv : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* Blueprint.NativeSporadic.McL) ∨ Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      Nonempty (X ≃* projSU 4 3 1)) →
    ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → 81 ≤ Nat.card B →
      ∃ t ∈ Subgroup.normalizer (B : Set X), t ≠ 1 ∧ t ^ 2 = 1 ∧
        Nat.card (B ⊓ Subgroup.centralizer {t} : Subgroup X) = 9

namespace Res611E81

section General

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem card_eq_card_map_mul_card_inf_ker {X : Type*} [Group X] (f : H →* X) (S : Subgroup H) :
    Nat.card S = Nat.card (S.map f) * Nat.card (S ⊓ f.ker : Subgroup H) := by
  set g : S →* X := f.comp S.subtype with hg
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at h1
  have hr : g.range = S.map f := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : Nat.card g.ker = Nat.card (S ⊓ f.ker : Subgroup H) := by
    have hmem : ∀ x : S, x ∈ g.ker ↔ (x : H) ∈ f.ker := fun x => by
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hg, MonoidHom.comp_apply, Subgroup.coe_subtype]
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : H), Subgroup.mem_inf.mpr ⟨x.1.2, (hmem x.1).mp x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩,
          (hmem _).mpr (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [h1, hr, hk]

theorem exists_conj_sylow_three {C P₁ P₂ : Subgroup H}
    (h₁ : P₁ ≤ C ∧ IsPGroup 3 P₁ ∧ ¬ 3 ∣ P₁.relIndex C)
    (h₂ : P₂ ≤ C ∧ IsPGroup 3 P₂ ∧ ¬ 3 ∣ P₂.relIndex C) :
    ∃ g ∈ C, ∀ x, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hP₁C, hP₁p, hidx₁⟩ := h₁
  obtain ⟨hP₂C, hP₂p, hidx₂⟩ := h₂
  have hp₁ : IsPGroup 3 (P₁.subgroupOf C) :=
    hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
  have hp₂ : IsPGroup 3 (P₂.subgroupOf C) :=
    hP₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂C).symm
  let S₁ : Sylow 3 ↥C := hp₁.toSylow hidx₁
  let S₂ : Sylow 3 ↥C := hp₂.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have h1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ x ∈ P₂ := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) ↔ (g : H)⁻¹ * x * g ∈ P₁ :=
      Subgroup.mem_subgroupOf (H := P₁) (K := C) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (hP₂C h)
    have hxP₁ : (g : H)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := C.mul_mem (C.mul_mem g.2 (hP₁C h)) (C.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

theorem exists_mem_mul_mem_normalizer {N P : Subgroup H} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (hP : IsPGroup 3 P) {s : H} (hs : ∀ x ∈ P, s * x * s⁻¹ ∈ P ⊔ N) :
    ∃ y ∈ N, y * s ∈ Subgroup.normalizer (P : Set H) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := P ⊔ N with hQ
  set X := P.map (MulAut.conj s).toMonoidHom with hX
  have hXQ : X ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hs x hx
  have hPQ : P ≤ Q := le_sup_left
  have hXcard : Nat.card X = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdisj : Disjoint P N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN))
  have hQcard : Nat.card Q = Nat.card P * Nat.card N := by
    have h1 := Subgroup.relIndex_mul_card N Q
    rw [inf_eq_left.mpr le_sup_right, hQ, Subgroup.relIndex_sup_right] at h1
    have h2 := Subgroup.relIndex_mul_card N P
    rw [inf_comm, hdisj.eq_bot, Subgroup.card_bot, mul_one] at h2
    rw [← h1, h2]
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hidx : ∀ Y : Subgroup H, Y ≤ Q → Nat.card Y = Nat.card P → Y.relIndex Q = Nat.card N := by
    intro Y hYQ hY
    have h := Subgroup.relIndex_mul_card Y Q
    rw [inf_eq_left.mpr hYQ, hQcard, hY, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hPpos h
  have hXp : IsPGroup 3 X := hP.map _
  obtain ⟨g, hgQ, hg⟩ := exists_conj_sylow_three (C := Q) (P₁ := X) (P₂ := P)
    ⟨hXQ, hXp, by rw [hidx X hXQ hXcard]; exact hN⟩
    ⟨hPQ, hP, by rw [hidx P hPQ rfl]; exact hN⟩
  have hPN : P ≤ Subgroup.normalizer (N : Set H) := fun x _ => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P N hPN] at hgQ
  obtain ⟨a, haP, n, hnN, rfl⟩ := hgQ
  refine ⟨n, hnN, ?_⟩
  have key : ∀ x, x ∈ P ↔ n⁻¹ * x * n ∈ X := by
    intro x
    constructor
    · intro hx
      have h1 := (hg (a * x * a⁻¹)).mp (P.mul_mem (P.mul_mem haP hx) (P.inv_mem haP))
      rwa [show (a * n)⁻¹ * (a * x * a⁻¹) * (a * n) = n⁻¹ * x * n by group] at h1
    · intro hx
      have h1 : (a * n)⁻¹ * (a * x * a⁻¹) * (a * n) ∈ X := by
        rwa [show (a * n)⁻¹ * (a * x * a⁻¹) * (a * n) = n⁻¹ * x * n by group]
      have h2 := (hg (a * x * a⁻¹)).mpr h1
      have := P.mul_mem (P.mul_mem (P.inv_mem haP) h2) haP
      simpa [mul_assoc] using this
  have hmemX : ∀ z, z ∈ X ↔ s⁻¹ * z * s ∈ P := by
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [mul_assoc] using hx
    · intro hz
      refine ⟨s⁻¹ * z * s, hz, ?_⟩
      simp [mul_assoc]
  have hinv : (n * s)⁻¹ ∈ Subgroup.normalizer (P : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [key x, hmemX]
    constructor <;> intro h <;> simpa [mul_assoc] using h
  simpa using Subgroup.inv_mem _ hinv

theorem exists_involution_lift {X : Type*} [Group X] (ρ : H →* X) (hρ : Function.Surjective ρ)
    {N P : Subgroup H} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (hNρ : N ≤ ρ.ker)
    (hker : ρ.ker ≤ P ⊔ N) (hodd : ∀ k ∈ ρ.ker, Odd (orderOf k)) (hP : IsPGroup 3 P) {t : X}
    (ht : t ∈ Subgroup.normalizer ((P.map ρ : Subgroup X) : Set X)) (ht2 : t ^ 2 = 1) :
    ∃ t₀ : H, t₀ ∈ Subgroup.normalizer (P : Set H) ∧ t₀ ^ 2 = 1 ∧ ρ t₀ = t := by
  obtain ⟨s, rfl⟩ := hρ t
  have hs : ∀ x ∈ P, s * x * s⁻¹ ∈ P ⊔ N := by
    intro x hx
    have h1 : ρ (s * x * s⁻¹) ∈ P.map ρ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp ht (ρ x)).mp ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hpx⟩ := h1
    have h2 : p⁻¹ * (s * x * s⁻¹) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, inv_mul_cancel]
    have h3 := (P ⊔ N).mul_mem (Subgroup.mem_sup_left hp) (hker h2)
    rwa [mul_inv_cancel_left] at h3
  obtain ⟨y, hyN, hyP⟩ := exists_mem_mul_mem_normalizer hN hP hs
  set s' := y * s with hs'
  have hρs' : ρ s' = ρ s := by
    rw [hs', map_mul, MonoidHom.mem_ker.mp (hNρ hyN), one_mul]
  have hsq : s' ^ 2 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hρs', ht2]
  obtain ⟨j, hj⟩ := hodd _ hsq
  refine ⟨s' ^ orderOf (s' ^ 2), Subgroup.pow_mem _ hyP _, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  · rw [map_pow, hρs', hj, pow_succ, pow_mul, ht2, one_pow, one_mul]

end General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {L S : Subgroup G} (hSL : S ≤ L) {t : L}
    (ht : t ∈ Subgroup.normalizer ((S.subgroupOf L : Subgroup L) : Set L)) :
    (t : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := (Subgroup.mem_normalizer_iff.mp ht ⟨x, hSL hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h
  · intro hx
    have hxL : x ∈ L := by
      have h1 := L.mul_mem (L.mul_mem (L.inv_mem t.2) (hSL hx)) t.2
      simpa [mul_assoc] using h1
    have h := (Subgroup.mem_normalizer_iff.mp ht ⟨x, hxL⟩).mpr (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp h

theorem inf_theta_eq_bot {L B : Subgroup G} (hB : IsPGroup 3 B) :
    B ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hB.exists_card_eq
  exact (Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (theta_solvable_and_not_dvd L).2))).eq_bot

omit [Finite G] in
theorem pow_three_of_mem_zpowers {c x : G} (hc : c ^ 3 = 1) (hx : x ∈ Subgroup.zpowers c) :
    x ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

omit [Finite G] in
theorem card_theta_eq (L : Subgroup G) :
    Nat.card (aschbacherSolvableCore 3 L) = Nat.card (inSubgroup (aschbacherSolvableCore 3) L) :=
  (Subgroup.card_map_of_injective L.subtype_injective).symm

theorem zpowers_inf_eq_bot {L : Subgroup G} {c : G} (hc3 : orderOf c = 3) (hcL : c ∉ L) :
    Subgroup.zpowers c ⊓ L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro y ⟨hy, hyL⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hy3 : y ^ 3 = 1 := pow_three_of_mem_zpowers (by rw [← hc3, pow_orderOf_eq_one]) hy
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have heq : Subgroup.zpowers y = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hyo])
  exact hcL ((Subgroup.zpowers_le.mpr hyL) (heq ▸ Subgroup.mem_zpowers c))

theorem card_eq_three_mul_card_inf {D L : Subgroup G} (hDe : CFSG.Assembly.IsElemAbelian 3 D)
    {c : G} (hcD : c ∈ D) (hc1 : c ≠ 1) (hcL : c ∉ L) (hdec : D = Subgroup.zpowers c ⊔ (D ⊓ L)) :
    Nat.card D = 3 * Nat.card (D ⊓ L : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hDe.2 c hcD) hc1
  apply le_antisymm (Res611Res3.card_le_three_mul_card_inf hDe hcD hc1 hdec)
  let f : Subgroup.zpowers c × (D ⊓ L : Subgroup G) → D := fun p =>
    ⟨(p.1 : G) * p.2, D.mul_mem (Subgroup.zpowers_le.mpr hcD p.1.2) (Subgroup.mem_inf.mp p.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨x₁, hx₁⟩, ⟨b₁, hb₁⟩⟩ ⟨⟨x₂, hx₂⟩, ⟨b₂, hb₂⟩⟩ h
    have h' : x₁ * b₁ = x₂ * b₂ := congrArg Subtype.val h
    have hxb : x₂⁻¹ * x₁ = b₂ * b₁⁻¹ := by
      calc x₂⁻¹ * x₁ = x₂⁻¹ * (x₁ * b₁) * b₁⁻¹ := by group
        _ = x₂⁻¹ * (x₂ * b₂) * b₁⁻¹ := by rw [h']
        _ = b₂ * b₁⁻¹ := by group
    have hmem : x₂⁻¹ * x₁ ∈ Subgroup.zpowers c ⊓ L :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₂) hx₁, by
        rw [hxb]
        exact L.mul_mem (Subgroup.mem_inf.mp hb₂).2 (L.inv_mem (Subgroup.mem_inf.mp hb₁).2)⟩
    rw [zpowers_inf_eq_bot hc3 hcL, Subgroup.mem_bot] at hmem
    have hx : x₁ = x₂ := (eq_of_inv_mul_eq_one hmem).symm
    subst hx
    have hb : b₁ = b₂ := mul_left_cancel h'
    subst hb
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_zpowers, hc3] at h

end Res611E81

open Res611E81

theorem item611E81Lift_of (h45 : Sec4.Item4_5) (hK : KS611E81Inv) : Item611E81Lift := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ hcase
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hAp : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLc : L ∈ thetaComponentsAt 3 c := hL.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_mem_thetaComponentsAt hLc
  obtain ⟨m, hm5, hAcard⟩ := exists_card_eq_of_four_lt_pRank hAe hrank
  have h243 : 243 ≤ Nat.card A := by
    rw [hAcard]
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  set θ := aschbacherSolvableCore 3 L with hθdef
  have hθodd : Odd (Nat.card θ) := by
    rw [card_theta_eq]
    exact Res611Res3.odd_card_theta_of_config h45 hst hA hrank hcA hc1 hLc
  have hθ3 : ¬ 3 ∣ Nat.card θ := three_not_dvd_card_aschbacherSolvableCore
  have hθord : ∀ k ∈ θ, Odd (orderOf k) := fun k hk => by
    have h := orderOf_dvd_natCard (⟨k, hk⟩ : θ)
    rw [Subgroup.orderOf_mk] at h
    exact hθodd.of_dvd_nat h
  set π : L →* L ⧸ θ := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  have hπker : π.ker = θ := QuotientGroup.ker_mk' θ
  have hcC : c ∈ thetaQuotCentralizer L := by
    have h : c ∈ A ⊓ thetaQuotCentralizer L := hCA ▸ Subgroup.mem_zpowers c
    exact h.2
  have hAθ : A ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ := inf_theta_eq_bot hAp
  rcases hcase with ⟨hAL, K, hKn, hKc, hX⟩ | ⟨hdec, hcL, hX⟩
  ·
    have hcL : c ∈ L := hAL hcA
    set A₀ : Subgroup L := A.subgroupOf L with hA₀
    have hA₀p : IsPGroup 3 A₀ := hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm
    have hA₀card : Nat.card A₀ = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    set C₀ : Subgroup L := (Subgroup.zpowers c).subgroupOf L with hC₀
    have hC₀A₀ : C₀ ≤ A₀ := fun x hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.zpowers_le.mpr hcA (Subgroup.mem_subgroupOf.mp hx))
    have hC₀card : Nat.card C₀ = 3 := by
      rw [show Nat.card C₀ = Nat.card (Subgroup.zpowers c) from Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcL)).toEquiv,
        Nat.card_zpowers, hc3]
    set ρ : L →* (L ⧸ θ) ⧸ K := (QuotientGroup.mk' K).comp π with hρ
    have hρs : Function.Surjective ρ := (QuotientGroup.mk'_surjective K).comp hπs
    have hρker : ∀ x : L, x ∈ ρ.ker ↔ π x ∈ K := fun x => by
      rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    have hkerA₀ : ∀ x ∈ A₀, x ∈ ρ.ker → x ∈ C₀ := by
      intro x hx hxk
      rw [hρker, hKc] at hxk
      obtain ⟨z, hz, hzx⟩ := hxk
      have hzx' : z⁻¹ * x ∈ θ := by
        rw [← QuotientGroup.eq]
        exact hzx
      have h1 : ((z⁻¹ * x : L) : G) ∈ A ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
        ⟨A.mul_mem (A.inv_mem (Subgroup.mem_subgroupOf.mp (hC₀A₀ hz)))
          (Subgroup.mem_subgroupOf.mp hx), ⟨_, hzx', rfl⟩⟩
      rw [hAθ, Subgroup.mem_bot] at h1
      have h2 : z⁻¹ * x = 1 := Subtype.ext h1
      rw [← eq_of_inv_mul_eq_one h2]
      exact hz
    have hθρ : θ ≤ ρ.ker := fun x hx => (hρker x).mpr (by
      rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact K.one_mem)
    have hkerle : ρ.ker ≤ A₀ ⊔ θ := by
      intro x hxk
      rw [hρker, hKc] at hxk
      obtain ⟨z, hz, hzx⟩ := hxk
      have hzx' : z⁻¹ * x ∈ θ := by
        rw [← QuotientGroup.eq]
        exact hzx
      have h := (A₀ ⊔ θ).mul_mem (Subgroup.mem_sup_left (hC₀A₀ hz)) (Subgroup.mem_sup_right hzx')
      rwa [mul_inv_cancel_left] at h
    have hkerodd : ∀ k ∈ ρ.ker, Odd (orderOf k) := by
      intro k hk
      rw [hρker, hKc] at hk
      obtain ⟨z, hz, hzk⟩ := hk
      have hz3 : z ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact pow_three_of_mem_zpowers (hAe.2 c hcA) (Subgroup.mem_subgroupOf.mp hz))
      have hk3 : k ^ 3 ∈ θ := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hπ,
          ← hzk, ← map_pow, hz3, map_one]
      have hodd3 := hθord _ hk3
      have hdvd : orderOf k ∣ 3 * orderOf (k ^ 3) :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
      exact (Odd.mul (by decide) hodd3).of_dvd_nat hdvd
    set B : Subgroup ((L ⧸ θ) ⧸ K) := A₀.map ρ with hB
    have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ρ A₀
        (isElemAbelian_subgroupOf hAe)
    have hB81 : 81 ≤ Nat.card B := by
      have h := card_eq_card_map_mul_card_inf_ker ρ A₀
      have hle : Nat.card (A₀ ⊓ ρ.ker : Subgroup L) ≤ 3 :=
        (Subgroup.card_le_of_le fun x hx =>
          hkerA₀ x (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2).trans hC₀card.le
      rw [hA₀card] at h
      have hpos : 0 < Nat.card (A₀ ⊓ ρ.ker : Subgroup L) := Nat.card_pos
      nlinarith
    have hX' : Nonempty ((L ⧸ θ) ⧸ K ≃* Blueprint.NativeSporadic.McL) ∨
        Nonempty ((L ⧸ θ) ⧸ K ≃* projSL 4 (GaloisField 3 1)) ∨
        Nonempty ((L ⧸ θ) ⧸ K ≃* projSU 4 3 1) := by
      rcases hX with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    obtain ⟨tb, htbN, htb1, htb2, htbC⟩ := hK _ hX' B hBe hB81
    obtain ⟨t₀, ht₀N, ht₀2, ht₀ρ⟩ :=
      exists_involution_lift ρ hρs (N := θ) hθ3 hθρ hkerle hkerodd hA₀p htbN htb2
    have htN : (t₀ : G) ∈ Subgroup.normalizer (A : Set G) :=
      mem_normalizer_of_mem_normalizer_subgroupOf hAL ht₀N
    have ht1 : (t₀ : G) ≠ 1 := fun h => htb1 (by
      rw [← ht₀ρ, show t₀ = 1 from Subtype.ext h, map_one])
    have ht2 : (t₀ : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ht₀2, Subgroup.coe_one]
    have htc : (t₀ : G) * c = c * (t₀ : G) := by
      have h1 := (mem_thetaQuotCentralizer_iff.mp hcC).2 (t₀ : G) t₀.2
      have h2 : (t₀ : G)⁻¹ * c * (t₀ : G) ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) c).mp hcA
        simpa using this
      have h3 : (t₀ : G)⁻¹ * (c * (t₀ : G) * c⁻¹) ∈ A ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
        ⟨by
          rw [show (t₀ : G)⁻¹ * (c * (t₀ : G) * c⁻¹) = ((t₀ : G)⁻¹ * c * (t₀ : G)) * c⁻¹ by group]
          exact A.mul_mem h2 (A.inv_mem hcA), h1⟩
      rw [hAθ, Subgroup.mem_bot] at h3
      have h4 : c * (t₀ : G) * c⁻¹ = (t₀ : G) := by
        have := congrArg ((t₀ : G) * ·) h3
        simpa [mul_assoc] using this
      calc (t₀ : G) * c = c * (t₀ : G) * c⁻¹ * c := by rw [h4]
        _ = c * (t₀ : G) := by group
    refine ⟨t₀, t₀.2, htN, ht1, ht2, ?_⟩
    set D := A ⊓ Subgroup.centralizer ({(t₀ : G)} : Set G) with hD
    have hDL : D ≤ L := inf_le_left.trans hAL
    have hcD : c ∈ D := ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr htc.symm⟩
    have hcomm' : Commute (t₀ : G) c := htc
    have htt : (t₀ : G) * (t₀ : G) = 1 := by
      rw [← pow_two]
      exact ht2
    have hc3' : c ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hAe.2 c hcA
    have hDcard : Nat.card D = 27 := by
      set D₀ : Subgroup L := D.subgroupOf L with hD₀
      have hD₀card : Nat.card D₀ = Nat.card D :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
      have h := card_eq_card_map_mul_card_inf_ker ρ D₀
      have hker : D₀ ⊓ ρ.ker = C₀ := by
        apply le_antisymm
        · intro x hx
          have hx' := Subgroup.mem_inf.mp hx
          exact hkerA₀ x (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx'.1).1) hx'.2
        · intro x hx
          refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr ?_, (hρker x).mpr ?_⟩
          · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
            rw [← hj]
            exact D.zpow_mem hcD j
          · rw [hKc]
            exact ⟨x, hx, rfl⟩
      have himg : D₀.map ρ = B ⊓ Subgroup.centralizer {tb} := by
        apply le_antisymm
        · rintro _ ⟨x, hx, rfl⟩
          have hxD := Subgroup.mem_subgroupOf.mp hx
          refine Subgroup.mem_inf.mpr ⟨⟨x, Subgroup.mem_subgroupOf.mpr hxD.1, rfl⟩,
            Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          rw [← ht₀ρ, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxD.2)
        · intro y hy
          obtain ⟨⟨a, ha, rfl⟩, hac⟩ := Subgroup.mem_inf.mp hy
          have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
          have hcomm : t₀ * a * t₀⁻¹ * a⁻¹ ∈ ρ.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ht₀ρ,
              (Subgroup.mem_centralizer_singleton_iff.mp hac).symm]
            group
          have hmem : t₀ * a * t₀⁻¹ * a⁻¹ ∈ A₀ := by
            refine A₀.mul_mem ?_ (A₀.inv_mem ha)
            exact (Subgroup.mem_normalizer_iff.mp ht₀N a).mp ha
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
            (Subgroup.mem_subgroupOf.mp (hkerA₀ _ hmem hcomm))
          have hj2 : (t₀ : G) * a * (t₀ : G)⁻¹ * (a : G)⁻¹ = c ^ j := by
            rw [hj]
            simp
          have hj' : (t₀ : G) * a * (t₀ : G)⁻¹ = c ^ j * a := by
            calc (t₀ : G) * a * (t₀ : G)⁻¹ = ((t₀ : G) * a * (t₀ : G)⁻¹ * (a : G)⁻¹) * a := by
                  group
              _ = c ^ j * a := by rw [hj2]
          have htcj : (t₀ : G) * c ^ j * (t₀ : G)⁻¹ = c ^ j := by
            rw [(hcomm'.zpow_right j).eq, mul_inv_cancel_right]
          have h1 : (a : G) = c ^ j * c ^ j * a := by
            calc (a : G) = ((t₀ : G) * (t₀ : G)) * a * ((t₀ : G) * (t₀ : G))⁻¹ := by
                  rw [htt]
                  group
              _ = (t₀ : G) * ((t₀ : G) * a * (t₀ : G)⁻¹) * (t₀ : G)⁻¹ := by group
              _ = (t₀ : G) * (c ^ j * a) * (t₀ : G)⁻¹ := by rw [hj']
              _ = ((t₀ : G) * c ^ j * (t₀ : G)⁻¹) * ((t₀ : G) * a * (t₀ : G)⁻¹) := by group
              _ = c ^ j * (c ^ j * a) := by rw [htcj, hj']
              _ = c ^ j * c ^ j * a := by group
          have h2 : c ^ j * c ^ j = 1 :=
            mul_right_cancel (b := (a : G)) (by rw [one_mul]; exact h1.symm)
          have h3 : c ^ (2 * j) = 1 := by
            rw [two_mul, zpow_add]
            exact h2
          have h4 := orderOf_dvd_iff_zpow_eq_one.mpr h3
          rw [hc3] at h4
          have h5 : (3 : ℤ) ∣ j := by
            have h4' : (3 : ℤ) ∣ 2 * j := by exact_mod_cast h4
            omega
          obtain ⟨i, hi⟩ := h5
          have hcj : c ^ j = 1 := by rw [hi, zpow_mul, hc3', one_zpow]
          refine ⟨a, Subgroup.mem_subgroupOf.mpr ⟨haA,
            Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, rfl⟩
          have h6 : (t₀ : G) * a * (t₀ : G)⁻¹ = a := by rw [hj', hcj, one_mul]
          calc (a : G) * (t₀ : G) = (t₀ : G) * a * (t₀ : G)⁻¹ * (t₀ : G) := by rw [h6]
            _ = (t₀ : G) * a := by group
      rw [himg, htbC, hker, hC₀card] at h
      rw [← hD₀card, h]
    refine ⟨isElemAbelian_of_le hAe inf_le_left, hDcard, Subgroup.zpowers (t₀ : G), ?_, ?_, ?_⟩
    · intro h
      exact ht1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers _))
    · exact IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
    · intro x hx
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxt : Commute (t₀ : G) x :=
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2).symm
      exact (hxt.zpow_left k).eq
  ·
    have hAL : A ⊓ L ≤ L := inf_le_right
    set A₀ : Subgroup L := (A ⊓ L).subgroupOf L with hA₀
    have hA₀p : IsPGroup 3 A₀ :=
      (hAp.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe hAL).symm
    have hA₀card : Nat.card A₀ = Nat.card (A ⊓ L : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
    have hAL81 : 81 ≤ Nat.card (A ⊓ L : Subgroup G) := by
      have := Res611Res3.card_le_three_mul_card_inf hAe hcA hc1 hdec
      omega
    set B : Subgroup (L ⧸ θ) := A₀.map π with hB
    have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π A₀
        (isElemAbelian_subgroupOf (isElemAbelian_of_le hAe inf_le_left))
    have hinj : Set.InjOn π (A₀ : Set L) := injOn_mk_of_isPGroup Nat.prime_three hA₀p
    have hBcard : Nat.card B = Nat.card A₀ := by
      change Nat.card ((A₀.map π : Set (L ⧸ θ))) = Nat.card (A₀ : Set L)
      rw [Subgroup.coe_map]
      exact Nat.card_image_of_injOn hinj
    obtain ⟨tb, htbN, htb1, htb2, htbC⟩ := hK _ hX B hBe (by rw [hBcard, hA₀card]; exact hAL81)
    obtain ⟨t₀, ht₀N, ht₀2, ht₀π⟩ := exists_involution_lift π hπs (N := θ) hθ3
      (by rw [hπker]) (by rw [hπker]; exact le_sup_right) (by rw [hπker]; exact hθord) hA₀p
      htbN htb2
    have htAL : (t₀ : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_of_mem_normalizer_subgroupOf hAL ht₀N
    have htc : (t₀ : G) * c = c * (t₀ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLC t₀.2)
    have htN : (t₀ : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [hdec, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp htAL, MonoidHom.map_zpowers]
      congr 2
      change (t₀ : G) * c * (t₀ : G)⁻¹ = c
      rw [htc, mul_inv_cancel_right]
    have ht1 : (t₀ : G) ≠ 1 := fun h => htb1 (by
      rw [← ht₀π, show t₀ = 1 from Subtype.ext h, map_one])
    have ht2 : (t₀ : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ht₀2, Subgroup.coe_one]
    refine ⟨t₀, t₀.2, htN, ht1, ht2, ?_⟩
    set D := A ⊓ Subgroup.centralizer ({(t₀ : G)} : Set G) with hD
    have hDe : CFSG.Assembly.IsElemAbelian 3 D := isElemAbelian_of_le hAe inf_le_left
    have hcD : c ∈ D := ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr htc.symm⟩
    have hDL9 : Nat.card (D ⊓ L : Subgroup G) = 9 := by
      have hDLL : D ⊓ L ≤ L := inf_le_right
      set D₀ : Subgroup L := (D ⊓ L).subgroupOf L with hD₀
      have hD₀card : Nat.card D₀ = Nat.card (D ⊓ L : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDLL).toEquiv
      have hD₀A₀ : D₀ ≤ A₀ := fun x hx => Subgroup.mem_subgroupOf.mpr
        ⟨(Subgroup.mem_subgroupOf.mp hx).1.1, (Subgroup.mem_subgroupOf.mp hx).2⟩
      have hD₀map : Nat.card (D₀.map π) = Nat.card D₀ := by
        change Nat.card ((D₀.map π : Set (L ⧸ θ))) = Nat.card (D₀ : Set L)
        rw [Subgroup.coe_map]
        exact Nat.card_image_of_injOn (hinj.mono hD₀A₀)
      have himg : D₀.map π = B ⊓ Subgroup.centralizer {tb} := by
        apply le_antisymm
        · rintro _ ⟨x, hx, rfl⟩
          have hxD := Subgroup.mem_subgroupOf.mp hx
          refine Subgroup.mem_inf.mpr ⟨⟨x, hD₀A₀ hx, rfl⟩,
            Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          rw [← ht₀π, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxD.1.2)
        · intro y hy
          obtain ⟨⟨a, ha, rfl⟩, hac⟩ := Subgroup.mem_inf.mp hy
          have hconj : t₀ * a * t₀⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.mp ht₀N a).mp ha
          have heq : π (t₀ * a * t₀⁻¹) = π a := by
            rw [map_mul, map_mul, map_inv, ht₀π,
              (Subgroup.mem_centralizer_singleton_iff.mp hac).symm, mul_inv_cancel_right]
          have h1 : t₀ * a * t₀⁻¹ = a := hinj hconj ha heq
          have haG := Subgroup.mem_subgroupOf.mp ha
          refine ⟨a, Subgroup.mem_subgroupOf.mpr ⟨⟨haG.1,
            Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, haG.2⟩, rfl⟩
          have h2 : (t₀ : G) * a * (t₀ : G)⁻¹ = a := congrArg Subtype.val h1
          calc (a : G) * (t₀ : G) = (t₀ : G) * a * (t₀ : G)⁻¹ * (t₀ : G) := by rw [h2]
            _ = (t₀ : G) * a := by group
      rw [← hD₀card, ← hD₀map, himg, htbC]
    have hdecD : D = Subgroup.zpowers c ⊔ (D ⊓ L) := by
      apply le_antisymm
      · intro d hd
        have hdA : d ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hdec ▸ hd.1
        have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
          rw [Subgroup.zpowers_le]
          refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
          · have h1 : c * y * c⁻¹ = y := by
              rw [hAcomm c hcA y hy.1, mul_inv_cancel_right]
            rw [h1]
            exact hy
          · have hyA : y ∈ A := by
              have := A.mul_mem (A.mul_mem (A.inv_mem hcA) hy.1) hcA
              simpa [mul_assoc] using this
            have h2 : c * y * c⁻¹ = y := by
              rw [hAcomm c hcA y hyA, mul_inv_cancel_right]
            rw [← h2]
            exact hy
        rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hdA
        obtain ⟨x, hx, b, hb, rfl⟩ := hdA
        have hxD : x ∈ D := Subgroup.zpowers_le.mpr hcD hx
        have hbD : b ∈ D := by
          have := D.mul_mem (D.inv_mem hxD) hd
          simpa using this
        exact Subgroup.mul_mem_sup hx ⟨hbD, hb.2⟩
      · exact sup_le (Subgroup.zpowers_le.mpr hcD) inf_le_left
    have hDcard : Nat.card D = 27 := by
      rw [card_eq_three_mul_card_inf hDe hcD hc1 hcL hdecD, hDL9]
    refine ⟨hDe, hDcard, Subgroup.zpowers (t₀ : G), ?_, ?_, ?_⟩
    · intro h
      exact ht1 (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers _))
    · exact IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
    · intro x hx
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxt : Commute (t₀ : G) x :=
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2).symm
      exact (hxt.zpow_left k).eq

end CFSG.RankThree.PartTwo.Sec6
