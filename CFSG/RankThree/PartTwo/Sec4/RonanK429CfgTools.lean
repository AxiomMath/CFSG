module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res5Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts

section Theta

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_bot_of_isComponent (hθ : aschbacherSolvableCore 3 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) : aschbacherSolvableCore 3 L = ⊥ := by
  have h := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL.2
  rw [hθ, inf_bot_eq, inSubgroup] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h

theorem isPGroup_center_of_isComponent (hθ : aschbacherSolvableCore 3 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) : IsPGroup 3 (Subgroup.center L) :=
  (Census.isPGroup_center_thetaQuotient L).of_equiv
    (Subgroup.centerCongr (thetaBotEquiv (theta_eq_bot_of_isComponent hθ hL)))

end Theta

section DescAut

variable {G : Type} [Group G]

@[expose] noncomputable def descAut (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ Subgroup.center L) :=
  (centerDescend L).comp L.normalizerMonoidHom

theorem descAut_mk (L : Subgroup G) (n : Subgroup.normalizer (L : Set G)) (l : L) :
    descAut L n (l : L ⧸ Subgroup.center L) =
      ((L.normalizerMonoidHom n l : L) : L ⧸ Subgroup.center L) :=
  rfl

theorem descAut_eq_one_iff {L : Subgroup G} (hL : Group.IsPerfect L)
    (n : Subgroup.normalizer (L : Set G)) :
    descAut L n = 1 ↔ (n : G) ∈ Subgroup.centralizer (L : Set G) := by
  haveI := hL
  have hker : L.normalizerMonoidHom n = 1 ↔ (n : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  rw [← hker]
  constructor
  · intro h
    apply Res423Five.centerDescend_injective
    rw [map_one]
    exact h
  · intro h
    change centerDescend L (L.normalizerMonoidHom n) = 1
    rw [h, map_one]

variable [Finite G]

@[expose] noncomputable def aBar {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup (MulAut (L ⧸ Subgroup.center L)) :=
  ((descAut L).comp (Subgroup.inclusion hAN)).range

theorem descAut_mem_aBar {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G)) {a : G}
    (ha : a ∈ A) : descAut L ⟨a, hAN ha⟩ ∈ aBar hAN :=
  ⟨⟨a, ha⟩, rfl⟩

theorem mem_aBar_iff {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G))
    {x : MulAut (L ⧸ Subgroup.center L)} :
    x ∈ aBar hAN ↔ ∃ (a : G) (ha : a ∈ A), descAut L ⟨a, hAN ha⟩ = x := by
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact descAut_mem_aBar hAN ha

theorem descAut_comp_inclusion_injective {L A : Subgroup G} (hL : Group.IsPerfect L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    Function.Injective ((descAut L).comp (Subgroup.inclusion hAN)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 := (descAut_eq_one_iff hL _).mp ha
  have h2 : (a : G) ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨a.2, h1⟩
  rw [hAC, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem isE27_aBar {L A : Subgroup G} (hL : Group.IsPerfect L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hA : Late.IsE27 A) :
    Late.IsE27 (aBar hAN) := by
  have hinj := descAut_comp_inclusion_injective hL hAN hAC
  have hcomm : ∀ a b : G, a ∈ A → b ∈ A → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ha, hx⟩ := (mem_aBar_iff hAN).mp x.2
    obtain ⟨b, hb, hy⟩ := (mem_aBar_iff hAN).mp y.2
    apply Subtype.ext
    change (x : MulAut (L ⧸ Subgroup.center L)) * y = y * x
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm a b ha hb)
  · obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
    rw [← map_pow]
    have h3 : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (hA.1.2 a ha)
    rw [h3, map_one]
  · rw [← hA.2]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end DescAut

section Core

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem pCore_two_le_center {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K) :
    CFSG.pCore 2 K ≤ Subgroup.center K := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK
      (inferInstance : (CFSG.pCore 2 K).Normal) with h | h
  · exfalso
    have h2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    rw [h] at h2
    have hp : IsPGroup 2 K := h2.of_equiv Subgroup.topEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hK.1
    haveI : Nontrivial K := by
      haveI : Nontrivial (K ⧸ Subgroup.center K) := hK.2.1.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
    exact Group.IsPerfect.not_isNilpotent K hp.isNilpotent
  · exact h

theorem inf_eq_bot_of_center_eq_bot {K P : Subgroup Γ} (hK : IsQuasisimple K)
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) (hP : P ≤ Subgroup.center Γ)
    (hP3 : IsPGroup 3 P) : K ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  set k : K := ⟨x, hx.1⟩
  have hkZ : k ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hP hx.2) (y : Γ))
  have hkbar : (k : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hkZ y]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hkbar
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨k, hkbar⟩
  obtain ⟨b, hb⟩ := hP3 ⟨x, hx.2⟩
  have ha' : x ^ 2 ^ a = 1 := by
    have := congrArg (fun w : CFSG.pCore 2 K => ((w : K) : Γ)) ha
    simpa using this
  have hb' : x ^ 3 ^ b = 1 := by
    have := congrArg (fun w : P => (w : Γ)) hb
    simpa using this
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha')
    (orderOf_dvd_of_pow_eq_one hb'))

theorem mem_centralizer_of_conj_mem_pCoreOf {K : Subgroup Γ} (hK : IsQuasisimple K) {a : Γ}
    (ha : a ∈ Subgroup.normalizer (K : Set Γ))
    (h : ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    a ∈ Subgroup.centralizer (K : Set Γ) := by
  haveI : Group.IsPerfect K := hK.1
  have hO := pCore_two_le_center hK
  have hα : K.normalizerMonoidHom ⟨a, ha⟩ = 1 := by
    apply mulAut_eq_of_inv_mul_mem_center
    intro s
    obtain ⟨w, hw, hws⟩ := h s s.2
    have hwZ : w ∈ Subgroup.center K := hO hw
    have hs : ((1 : MulAut K) s)⁻¹ * K.normalizerMonoidHom ⟨a, ha⟩ s = s⁻¹ * w * s := by
      apply Subtype.ext
      change (s : Γ)⁻¹ * (a * s * a⁻¹) = (s : Γ)⁻¹ * (w : Γ) * s
      rw [show (w : Γ) = a * s * a⁻¹ * (s : Γ)⁻¹ from hws]
      group
    have hsw : s⁻¹ * w * s = w := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hwZ s, inv_mul_cancel_left]
    rw [hs, hsw]
    exact hwZ
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have := congrArg (fun α : MulAut K => ((α ⟨k, hk⟩ : K) : Γ)) hα
  change a * k * a⁻¹ = k at this
  calc k * a = a * k * a⁻¹ * a := by rw [this]
    _ = a * k := by group

end Core

section Maps

theorem isSubnormal_subgroupOf_trans {X : Type*} [Group X] {H K J : Subgroup X} (hHK : H ≤ K)
    (hKJ : K ≤ J) (h₁ : (H.subgroupOf K).IsSubnormal) (h₂ : (K.subgroupOf J).IsSubnormal) :
    (H.subgroupOf J).IsSubnormal := by
  refine Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono J hHK) ?_ h₂
  set e : K.subgroupOf J ≃* K := Subgroup.subgroupOfEquivOfLe hKJ with he
  have heq : (H.subgroupOf J).subgroupOf (K.subgroupOf J) = (H.subgroupOf K).comap e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  rw [heq]
  exact h₁.comap _

theorem pCoreOf_map_of_injective {X Y : Type*} [Group X] [Group Y] (p : ℕ) (f : X →* Y)
    {H : Subgroup X} (hf : Function.Injective (f.comp H.subtype)) :
    CFSG.Open.pCoreOf p (H.map f) = (CFSG.Open.pCoreOf p H).map f := by
  have hrange : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  set φ : H ≃* H.map f := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange) with hφ
  have hcore : CFSG.pCore p (H.map f) = (CFSG.pCore p H).map φ.toMonoidHom :=
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv p φ).symm
  unfold CFSG.Open.pCoreOf
  rw [hcore, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_mem_pCoreOf_map_iff {X Y : Type*} [Group X] [Group Y] (p : ℕ) (f : X →* Y)
    {H : Subgroup X} (hf : Function.Injective (f.comp H.subtype)) {x : X} (hx : x ∈ H) :
    f x ∈ CFSG.Open.pCoreOf p (H.map f) ↔ x ∈ CFSG.Open.pCoreOf p H := by
  rw [pCoreOf_map_of_injective p f hf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyH : y ∈ H := by
      obtain ⟨z, -, rfl⟩ := hy
      exact z.2
    have : (⟨y, hyH⟩ : H) = ⟨x, hx⟩ := hf hyx
    have hxy : y = x := congrArg Subtype.val this
    rw [← hxy]
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

end Maps

end CFSG.RankThree.PartTwo.Sec4.RonanK429
