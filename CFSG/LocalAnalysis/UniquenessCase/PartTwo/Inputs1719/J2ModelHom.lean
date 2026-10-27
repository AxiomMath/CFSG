module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestJ2F
public import CFSG.Quasithin.EmptyFaithful.S153Odd
public import CFSG.GroupTheory.SylowInfNormal
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Recognition.GoldschmidtF112RJ2Lat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F112R CFSG.Quasithin.A312J2
open CFSG.Sporadic.Schreier (centralizerIn)

theorem j2Cover_autModel :
    AutModel P R where
  le := P_le_R
  conj_mem x hx p hp := by
    have hN := R_le_normalizer hx
    exact (hN p).1 hp
  surj α := by
    refine ⟨(rAutEquiv.symm α : R), (rAutEquiv.symm α).2, fun p => ?_⟩
    have h1 : rConj (rAutEquiv.symm α) = α := MulEquiv.apply_symm_apply rAutEquiv α
    have h2 := rConj_apply (rAutEquiv.symm α) p
    rw [h1] at h2
    exact h2
  inj x hx hc := by
    have hmem : x ∈ Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (hc p hp).symm
    rw [centralizer_P] at hmem
    exact (Subgroup.mem_bot).1 hmem

theorem embed_ker_eq_centralizer {M : Type*} [Group M] {P R : Subgroup M}
    (h : AutModel P R) {X : Type*} [Group X] (S : Subgroup X) [S.Normal] (θ : S ≃* P) :
    (h.embed S θ).ker = centralizer (S : Set X) := by
  ext x
  rw [MonoidHom.mem_ker, AutModel.embed, MonoidHom.comp_apply, ← map_one h.hom,
    h.hom_injective.eq_iff, mem_centralizer_iff]
  constructor
  · intro h1 s hs
    have h2 := congrArg (fun α : MulAut P => (α (θ ⟨s, hs⟩) : P)) h1
    simp only [transportAut_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val (θ.injective h2)
    rw [MulAut.conjNormal_apply] at h3
    calc s * x = x * s * x⁻¹ * x := by rw [h3]
      _ = x * s := by group
  · intro hx
    refine MulEquiv.ext fun p => ?_
    rw [transportAut_apply, MulAut.one_apply]
    have e : MulAut.conjNormal x (θ.symm p) = θ.symm p := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, ← hx _ (θ.symm p).2]
      group
    rw [e, MulEquiv.apply_symm_apply]

theorem exists_conj_eq_permTwoA
    (T : Sylow 2 P) (z : P) (hzT : z ∈ (T : Subgroup P))
    (hzc : ∀ t ∈ (T : Subgroup P), z * t = t * z) (hz1 : z ≠ 1) :
    ∃ g ∈ P, g * (z : Equiv.Perm (Fin 315)) * g⁻¹ = permTwoA := by
  classical
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup P) ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.2 ⟨T.isPGroup', T.not_dvd_index⟩
  have hz2c : ∀ t ∈ (T : Subgroup P), z * z * t = t * (z * z) := by
    intro t ht
    rw [mul_assoc, hzc t ht, ← mul_assoc, hzc t ht, mul_assoc]
  have hzz : z * z = 1 := by
    rcases CFSG.Quasithin.ModH.centerSmall_j2_P (T : Subgroup P) hT z (z * z) hzT
        (mul_mem hzT hzT) hzc hz2c with h | h | h
    · exact absurd h hz1
    · exact h
    · exact absurd (mul_left_cancel ((mul_one z).trans h)).symm hz1
  have hord : orderOf (z : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two, hzz]) hz1
  obtain ⟨-, -, -, -, -, hUnot, -, -, -, -, -, -, hcls, -, hcA, -, -, -, -, -⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, c, hc, e⟩ := hcls (z : Equiv.Perm (Fin 315)) (P_le_R z.2) hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  ·
    exfalso
    let T' : Subgroup (Equiv.Perm (Fin 315)) :=
      ((T : Subgroup P).map P.subtype).map (MulAut.conj c⁻¹).toMonoidHom
    have hle : T' ≤ CFSG.Sporadic.Schreier.centralizerIn P permA := by
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show c⁻¹ * (t : Equiv.Perm (Fin 315)) * c⁻¹⁻¹ ∈ P
        rw [inv_inv]
        exact P.mul_mem (P.mul_mem (P.inv_mem hc) t.2) hc
      · show c⁻¹ * (t : Equiv.Perm (Fin 315)) * c⁻¹⁻¹ ∈ Subgroup.centralizer {permA}
        rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        have hzt : (z : Equiv.Perm (Fin 315)) * t = t * z := congrArg Subtype.val (hzc t ht)
        have ha : permA = c⁻¹ * (z : Equiv.Perm (Fin 315)) * c := by rw [e]; group
        show permA * (c⁻¹ * (t : Equiv.Perm (Fin 315)) * c⁻¹⁻¹) =
          c⁻¹ * (t : Equiv.Perm (Fin 315)) * c⁻¹⁻¹ * permA
        rw [ha]
        calc c⁻¹ * (z : Equiv.Perm (Fin 315)) * c * (c⁻¹ * (t : Equiv.Perm (Fin 315)) * c⁻¹⁻¹)
            = c⁻¹ * ((z : Equiv.Perm (Fin 315)) * t) * c := by group
          _ = c⁻¹ * ((t : Equiv.Perm (Fin 315)) * z) * c := by rw [hzt]
          _ = c⁻¹ * (t : Equiv.Perm (Fin 315)) * c⁻¹⁻¹ *
              (c⁻¹ * (z : Equiv.Perm (Fin 315)) * c) := by
            group
    have hcardT : Nat.card (T : Subgroup P) = 2 ^ 7 :=
      CFSG.Quasithin.ModH.card_eq_pow_of_isSylowTwoOf_top hT
        (by rw [card_P]; norm_num : Nat.card ↥P = 2 ^ 7 * 4725) (by norm_num)
    have hcardT' : Nat.card T' = 2 ^ 7 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective,
        Subgroup.card_map_of_injective P.subtype_injective, hcardT]
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardT', hcA] at hdvd
    norm_num at hdvd
  · exact ⟨c⁻¹, P.inv_mem hc, by rw [e]; group⟩
  ·
    exfalso
    apply hUnot
    have hu : permU = c⁻¹ * (z : Equiv.Perm (Fin 315)) * c := by rw [e]; group
    rw [hu]
    exact P.mul_mem (P.mul_mem (P.inv_mem hc) z.2) hc

section ModelHom


theorem exists_center_facts {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) (hKn : K.Normal)
    (hK : IsSpor ↥K .J2) (S : Subgroup Y) (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) :
    ∃ c₀ ∈ K, c₀ ∈ S ∧ c₀ ≠ 1 ∧ (∀ s ∈ S, s * c₀ = c₀ * s) ∧
      CFSG.QuasithinUnique.IsSylowTwoOf ((S ⊓ K).subgroupOf K) ⊤ ∧
      ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → ∀ k ∈ K, k * c₀ = c₀ * k → c * k = k * c := by
  classical
  have := hKn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
  have hS2 : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := ⟨hS.1, hS.2.1, hS.2.2⟩
  have hP : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K := by
    have h := CFSG.isSylowTwoOf_inf_of_normal (G := Y) (S := S) (X := ⊤) (N := K)
      hS2 le_top hnorm
    simpa [inf_comm] using h
  let T : Subgroup ↥K := (S ⊓ K).subgroupOf K
  have hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact IsPGroup.comap_subtype (K := K) hP.2.1
    · change ¬ 2 ∣ T.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      simpa [T] using hP.2.2
  let e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2 := Classical.choice hK
  have hcs : ∀ x y : ↥K, x ∈ T → y ∈ T →
      (∀ t ∈ T, x * t = t * x) → (∀ t ∈ T, y * t = t * y) →
        x = 1 ∨ y = 1 ∨ x = y := by
    intro x y hx hy hxc hyc
    have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
      CFSG.Quasithin.ModH.isSylowTwoOf_map_equiv e hT
    have hx' : e x ∈ T.map e.toMonoidHom := ⟨x, hx, rfl⟩
    have hy' : e y ∈ T.map e.toMonoidHom := ⟨y, hy, rfl⟩
    have hxc' : ∀ t ∈ T.map e.toMonoidHom, e x * t = t * e x := by
      rintro _ ⟨s, hs, rfl⟩
      simpa using congrArg e (hxc s hs)
    have hyc' : ∀ t ∈ T.map e.toMonoidHom, e y * t = t * e y := by
      rintro _ ⟨s, hs, rfl⟩
      simpa using congrArg e (hyc s hs)
    rcases CFSG.Quasithin.ModH.sylowFactsJ2_unfolded.1 (T.map e.toMonoidHom) hT'
        (e x) (e y) hx' hy' hxc' hyc' with h | h | h
    · left
      exact e.injective (by simpa using h)
    · right; left
      exact e.injective (by simpa using h)
    · right; right
      exact e.injective h
  have hY' : ∀ T' : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2),
      CFSG.QuasithinUnique.IsSylowTwoOf T' ⊤ →
        ∀ α : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J2),
          (∀ t ∈ T', α t = t) →
            ∃ z ∈ T', (∀ t ∈ T', z * t = t * z) ∧ ∀ g, α g = z * g * z⁻¹ := by
    intro T' hT' α hα
    obtain ⟨hp, hidx⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hT'
    let P' : Sylow 2 (CFSG.Blueprint.NativeSporadic.Carrier .J2) := hp.toSylow hidx
    have hP' : (P' : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2)) = T' :=
      IsPGroup.toSylow_coe hp hidx
    obtain ⟨z, hzcent, hz⟩ := CFSG.Quasithin.ModH.sylowFactsJ2_unfolded.2 P' α (fun t ht => hα t ht)
    refine ⟨(z : CFSG.Blueprint.NativeSporadic.Carrier .J2), hP' ▸ z.2, ?_, ?_⟩
    · intro t ht
      have hcomm := congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hzcent) (⟨t, ht⟩ : ↥(P' : Subgroup _)))
      simpa using hcomm.symm
    · intro g
      exact hz g
  have hcardK : Nat.card ↥K = 604800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hKcard : Nat.card ↥K = 2 ^ 7 * 4725 := by
    rw [hcardK]
    norm_num
  have hTcard : Nat.card T = 2 ^ 7 :=
    CFSG.Quasithin.ModH.card_eq_pow_of_isSylowTwoOf_top hT hKcard (by norm_num)
  have hSK : S ⊓ K ≠ ⊥ := by
    intro h
    have h1 : Nat.card T = 1 := by
      rw [show T = (S ⊓ K).subgroupOf K from rfl, h, Subgroup.bot_subgroupOf, Subgroup.card_bot]
    rw [hTcard] at h1
    norm_num at h1
  have hSn : S ≤ Subgroup.normalizer ((S ⊓ K : Subgroup Y) : Set Y) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxS, hxK⟩
      exact ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), hKn.conj_mem x hxK s⟩
    · rintro ⟨hxS, hxK⟩
      refine ⟨?_, ?_⟩
      · have := S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs
        simpa [mul_assoc] using this
      · have := hKn.conj_mem _ hxK s⁻¹
        simpa [mul_assoc] using this
  obtain ⟨c₀, hc₀SK, hc₀1, hc₀c⟩ :=
    CFSG.Quasithin.exists_ne_one_mem_center_of_normalized hS2.2.1 inf_le_left hSK hSn
  have hc₀S : c₀ ∈ S := hc₀SK.1
  have hc₀K : c₀ ∈ K := hc₀SK.2
  let c₀K : ↥K := ⟨c₀, hc₀K⟩
  have hc₀T : c₀K ∈ T := Subgroup.mem_subgroupOf.2 hc₀SK
  have hc₀comm : ∀ t ∈ T, c₀K * t = t * c₀K := fun t ht =>
    Subtype.ext (hc₀c _ (Subgroup.mem_subgroupOf.1 ht).1).symm
  refine ⟨c₀, hc₀K, hc₀S, hc₀1, hc₀c, hT, ?_⟩
  intro c hcS hcc k hk hkc
  let cN : Subgroup.normalizer (K : Set Y) := ⟨c, by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top c⟩
  let α : MulAut ↥K := K.normalizerMonoidHom cN
  have hα : ∀ t ∈ T, α t = t := by
    intro t ht
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show c * (t : Y) * c⁻¹ = t
    rw [← hcc _ (Subgroup.mem_subgroupOf.1 ht).1, mul_inv_cancel_right]
  obtain ⟨c', hc'T, hc'Z, hc'α⟩ := CFSG.Quasithin.ModH.pointwise_of_equiv e hY' T hT α hα
  have hc_eq : c' = 1 ∨ c' = c₀K := by
    rcases hcs c' c₀K hc'T hc₀T hc'Z hc₀comm with h | h | h
    · exact Or.inl h
    · exact absurd (congrArg Subtype.val h) hc₀1
    · exact Or.inr h
  have hkc' : (⟨k, hk⟩ : ↥K) * c₀K = c₀K * ⟨k, hk⟩ := Subtype.ext hkc
  have hαk : α ⟨k, hk⟩ = ⟨k, hk⟩ := by
    rw [hc'α]
    rcases hc_eq with h | h
    · rw [h, one_mul, inv_one, mul_one]
    · rw [h, ← hkc', mul_inv_cancel_right]
  have h1 : ((α ⟨k, hk⟩ : ↥K) : Y) = c * k * c⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe K cN ⟨k, hk⟩
  rw [hαk] at h1
  calc c * k = c * k * c⁻¹ * c := by group
    _ = k * c := by rw [← h1]

theorem exists_j2Model_hom {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) (hKn : K.Normal)
    (hK : IsSpor ↥K .J2) (hidx : ∃ n : ℕ, K.index = 2 ^ n) (S : Subgroup Y)
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) :
    ∃ ρ : Y →* Equiv.Perm (Fin 315),
      ρ.ker = Subgroup.centralizer (K : Set Y) ∧ IsPGroup 2 ρ.ker ∧
        (∀ k ∈ K, ρ k ∈ P) ∧ (ρ.range = P ∨ ρ.range = R) ∧
        (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)).map ρ =
          centralizerIn ρ.range permTwoA := by
  classical
  have := hKn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, hc₀K, hc₀S, hc₀1, hc₀c, hT, hcent⟩ := exists_center_facts K hKn hK S hS
  obtain ⟨e0⟩ := hK
  let θ : ↥K ≃* ↥P := e0.trans nativeEquivP
  have hT' := CFSG.Quasithin.ModH.isSylowTwoOf_map_equiv θ hT
  obtain ⟨hp, hidx'⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.1 hT'
  let T' : Sylow 2 ↥P := hp.toSylow hidx'
  have hT'eq : (T' : Subgroup ↥P) = ((S ⊓ K).subgroupOf K).map θ.toMonoidHom :=
    IsPGroup.toSylow_coe hp hidx'
  have hc₀T : (⟨c₀, hc₀K⟩ : ↥K) ∈ (S ⊓ K).subgroupOf K :=
    Subgroup.mem_subgroupOf.2 ⟨hc₀S, hc₀K⟩
  have hz1 : θ ⟨c₀, hc₀K⟩ ≠ 1 := by
    intro h
    exact hc₀1 (congrArg Subtype.val (θ.injective (h.trans (map_one θ).symm)))
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_permTwoA T' (θ ⟨c₀, hc₀K⟩)
    (by rw [hT'eq]; exact ⟨_, hc₀T, rfl⟩)
    (by
      rw [hT'eq]
      rintro _ ⟨w, hw, rfl⟩
      change θ ⟨c₀, hc₀K⟩ * θ w = θ w * θ ⟨c₀, hc₀K⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc₀c _ (Subgroup.mem_subgroupOf.1 hw).1).symm) hz1
  let ρ₀ : Y →* Equiv.Perm (Fin 315) := j2Cover_autModel.embed K θ
  let ρ : Y →* Equiv.Perm (Fin 315) := (MulAut.conj g).toMonoidHom.comp ρ₀
  have hρ : ∀ y, ρ y = g * ρ₀ y * g⁻¹ := fun y => rfl
  have hρK : ∀ k : ↥K, ρ k = g * (θ k : Equiv.Perm (Fin 315)) * g⁻¹ := fun k => by
    rw [hρ, show ρ₀ k = θ k from j2Cover_autModel.embed_coe K θ k]
  have hρc₀ : ρ c₀ = permTwoA := (hρK ⟨c₀, hc₀K⟩).trans hgz
  have hρinj : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ρ k₁ = ρ k₂ → k₁ = k₂ := by
    intro k₁ h₁ k₂ h₂ h
    have h3 : g * (θ ⟨k₁, h₁⟩ : Equiv.Perm (Fin 315)) * g⁻¹ =
        g * (θ ⟨k₂, h₂⟩ : Equiv.Perm (Fin 315)) * g⁻¹ := by
      rw [← hρK, ← hρK]
      exact h
    have h4 := θ.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h3)))
    exact congrArg Subtype.val h4
  have hker : ρ.ker = Subgroup.centralizer (K : Set Y) := by
    rw [← embed_ker_eq_centralizer j2Cover_autModel K θ]
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρ]
    constructor
    · intro h
      have h' : g * ρ₀ y * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
      exact mul_left_cancel (mul_right_cancel h')
    · intro h
      show g * ρ₀ y * g⁻¹ = 1
      rw [show ρ₀ y = 1 from h]
      group
  have hCK : ∀ x ∈ Subgroup.centralizer (K : Set Y), x ∈ K → x = 1 := by
    intro x hx hxK
    have hc : ((θ ⟨x, hxK⟩ : ↥P) : Equiv.Perm (Fin 315)) ∈
        Subgroup.centralizer (P : Set (Equiv.Perm (Fin 315))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      obtain ⟨k, hk⟩ := θ.surjective ⟨p, hp⟩
      have hkx : (k : Y) * x = x * k := Subgroup.mem_centralizer_iff.1 hx k k.2
      have h2 := congrArg (fun w => ((θ w : ↥P) : Equiv.Perm (Fin 315)))
        (show k * ⟨x, hxK⟩ = ⟨x, hxK⟩ * k from Subtype.ext hkx)
      simp only [map_mul, Subgroup.coe_mul, hk] at h2
      exact h2
    rw [centralizer_P, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val (θ.injective ((Subtype.ext hc : θ ⟨x, hxK⟩ = 1).trans
      (map_one θ).symm))
  have hker2 : IsPGroup 2 ρ.ker := by
    rw [hker]
    obtain ⟨n, hn⟩ := hidx
    have hQ : IsPGroup 2 (Y ⧸ K) := IsPGroup.of_card (n := n) (by rw [← hn]; rfl)
    let f : ↥(Subgroup.centralizer (K : Set Y)) →* Y ⧸ K :=
      (QuotientGroup.mk' K).comp (Subgroup.centralizer (K : Set Y)).subtype
    refine hQ.of_injective f ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hfx
    rw [MonoidHom.mem_ker] at hfx
    have hxK : x ∈ K := (QuotientGroup.eq_one_iff x).1 hfx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hCK x hx hxK)
  have hρP : ∀ k ∈ K, ρ k ∈ P := by
    intro k hk
    show ρ ((⟨k, hk⟩ : ↥K) : Y) ∈ P
    rw [hρK]
    exact P.mul_mem (P.mul_mem hg (θ _).2) (P.inv_mem hg)
  have hpre : ∀ x ∈ P, ∃ k ∈ K, ρ k = x := by
    intro x hx
    have hq : g⁻¹ * x * g ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hg) hx) hg
    refine ⟨((θ.symm ⟨_, hq⟩ : ↥K) : Y), (θ.symm ⟨_, hq⟩).2, ?_⟩
    rw [hρK, MulEquiv.apply_symm_apply]
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have hPrange : P ≤ ρ.range := by
    intro x hx
    obtain ⟨k, -, hk⟩ := hpre x hx
    exact ⟨k, hk⟩
  have hrangeR : ρ.range ≤ R := by
    rintro _ ⟨y, rfl⟩
    rw [hρ]
    exact R.mul_mem (R.mul_mem (P_le_R hg) (j2Cover_autModel.embed_mem K θ y))
      (R.inv_mem (P_le_R hg))
  have hrange : ρ.range = P ∨ ρ.range = R := by
    have h1 := Subgroup.card_dvd_of_le hPrange
    have h2 := Subgroup.card_dvd_of_le hrangeR
    rw [card_P] at h1
    rw [card_R] at h2
    obtain ⟨m, hm⟩ := h1
    have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 604800)
      (show 604800 * m ∣ 604800 * 2 from hm ▸ h2)
    rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h | h
    · left
      exact (Subgroup.eq_of_le_of_card_ge hPrange (by rw [hm, h, card_P])).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hrangeR (by rw [hm, h, card_R])
  have hc₀Z : c₀ ∈ (Subgroup.center S).map S.subtype := by
    refine ⟨⟨c₀, hc₀S⟩, ?_, rfl⟩
    show (⟨c₀, hc₀S⟩ : ↥S) ∈ Subgroup.center S
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hc₀c s s.2)
  have hsub : (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)).map ρ ≤
      centralizerIn ρ.range permTwoA := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    show ρ y ∈ Subgroup.centralizer {permTwoA}
    rw [Subgroup.mem_centralizer_singleton_iff, ← hρc₀, ← map_mul, ← map_mul]
    exact congrArg ρ ((Subgroup.mem_centralizer_iff.1 hy) c₀ hc₀Z).symm
  have hCK0 : ∀ k ∈ K, k * c₀ = c₀ * k →
      k ∈ Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y) := by
    intro k hk hkc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    have hcc : ∀ s ∈ S, s * (c : Y) = (c : Y) * s := fun s hs =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨s, hs⟩)
    exact hcent c c.2 hcc k hk hkc
  have hCP : centralizerIn P permTwoA ≤
      (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)).map ρ := by
    rintro x ⟨hxP, hxz⟩
    obtain ⟨k, hkK, hρk⟩ := hpre x hxP
    refine ⟨k, hCK0 k hkK ?_, hρk⟩
    apply hρinj _ (K.mul_mem hkK hc₀K) _ (K.mul_mem hc₀K hkK)
    rw [map_mul, map_mul, hρk, hρc₀]
    exact Subgroup.mem_centralizer_singleton_iff.1 hxz
  have hSC : S ≤ Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨s, hs⟩)).symm
  refine ⟨ρ, hker, hker2, hρP, hrange, ?_⟩
  rcases hrange with h | h
  · rw [h] at hsub ⊢
    exact le_antisymm hsub hCP
  · rw [h] at hsub ⊢
    have hKS : K ⊔ S = ⊤ := by
      obtain ⟨n, hn⟩ := hidx
      have h1 : (K ⊔ S).index ∣ 2 ^ n := by
        rw [← hn]
        exact Subgroup.index_dvd_of_le le_sup_left
      have h2 : ¬ 2 ∣ (K ⊔ S).index := by
        intro h2
        apply hS.2.2
        rw [Subgroup.relIndex_top_right]
        exact h2.trans (Subgroup.index_dvd_of_le le_sup_right)
      obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      rcases j with _ | j
      · rw [pow_zero] at hj'
        exact Subgroup.index_eq_one.1 hj'
      · exact absurd (by rw [hj']; exact dvd_pow_self 2 (Nat.succ_ne_zero j)) h2
    have hex : ∃ s ∈ S, ρ s ∉ P := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      have hle : ρ.range ≤ P := by
        rw [MonoidHom.range_eq_map, ← hKS, Subgroup.map_sup, sup_le_iff]
        refine ⟨?_, ?_⟩
        · rintro _ ⟨k, hk, rfl⟩
          exact hρP k hk
        · rintro _ ⟨s, hs, rfl⟩
          exact hne s hs
      rw [h] at hle
      have := Subgroup.card_le_of_le hle
      rw [card_R, card_P] at this
      norm_num at this
    obtain ⟨s, hs, hsP⟩ := hex
    have hcR := Kernel.centralizerIn_R_permTwoA.2.1
    have hcP := Kernel.centralizerIn_P_permTwoA.2.1
    have hd1 := Subgroup.card_dvd_of_le hCP
    have hd2 := Subgroup.card_dvd_of_le hsub
    rw [hcP] at hd1
    rw [hcR] at hd2
    have hne : Nat.card ((Subgroup.centralizer
        (((Subgroup.center S).map S.subtype) : Set Y)).map ρ) ≠ 1920 := by
      intro hc
      have heq := Subgroup.eq_of_le_of_card_ge hCP (by rw [hc, hcP])
      have hmem : ρ s ∈ (Subgroup.centralizer
          (((Subgroup.center S).map S.subtype) : Set Y)).map ρ := ⟨s, hSC hs, rfl⟩
      rw [← heq] at hmem
      exact hsP hmem.1
    obtain ⟨m, hm⟩ := hd1
    have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 1920)
      (show 1920 * m ∣ 1920 * 2 from hm ▸ hd2)
    apply Subgroup.eq_of_le_of_card_ge hsub
    rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with h1 | h1
    · exact (hne (by rw [hm, h1, mul_one])).elim
    · rw [hcR, hm, h1]

end ModelHom

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact
