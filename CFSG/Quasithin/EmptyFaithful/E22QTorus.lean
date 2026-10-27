module

public import CFSG.Quasithin.EmptyFaithful.E22QLift
public import CFSG.Quasithin.EmptyFaithful.E22PL2PglC
import CFSG.Quasithin.EmptyFaithful.E22QWit
import CFSG.Quasithin.EmptyFaithful.E22PD1
import CFSG.Quasithin.EmptyFaithful.E22PTor
import CFSG.Quasithin.EmptyFaithful.E22PTr
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.Quasithin.E22L2
  CFSG.GorensteinWalter
open scoped Pointwise commutatorElement
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal
  pslRange_index_eq_two outerTorusOrder outerTorusOrder_mod_four six_le_outerTorusOrder
  outer_involution_centralizer zpowers_le_normalizer_of_inverting odd_card_of_isOddPrimePower)

theorem typeIIo_torus_pgl2 {K : Type} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7)
    (hq7 : 7 ≤ Nat.card K) {S A : Subgroup (PGL2 K)} {z : PGL2 K} (hS : IsSylowIn 2 S ⊤)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ S, z * x = x * z) (hAS : A ≤ S)
    (hAab : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) (hAJ : ¬ A ≤ pslRange K) :
    Nat.card A = 4 ∧ z ∈ A ∧ ∃ (r : ℕ) (P₀ : Subgroup (PGL2 K)) (b : PGL2 K), r.Prime ∧ r ≠ 2 ∧
      P₀ ≠ ⊥ ∧ IsPGroup r P₀ ∧ P₀ ≤ pslRange K ∧ b ∈ A ∧ b ≠ 1 ∧
      (∀ x ∈ P₀, b * x = x * b) ∧ (∀ x ∈ P₀, z * x * z⁻¹ = x⁻¹) ∧
      (∀ a ∈ A, a ∈ Subgroup.normalizer (P₀ : Set (PGL2 K))) ∧
      (∀ t ∈ S, (∀ a ∈ A, t * a = a * t) → t ∈ Subgroup.normalizer (P₀ : Set (PGL2 K))) := by
  have := e22pl2pgl_finite K
  have hcard3 : 3 < Nat.card K := by omega
  have : (pslRange K).Normal := pslRange_normal hodd hcard3
  obtain ⟨m, hm3, ⟨e⟩⟩ := e22pl2pgl_sylow_dihedral_q hodd hq8 hS
  have hm2 : 2 ≤ m := by omega
  obtain ⟨z₀, hz₀T, hz₀2, hz₀c, hz₀V, hAV⟩ := dihedral_sylow_data hm2 e
  have hzT : z ∈ S := e22qwit_mem_of_commute hS hz2 hzc
  have hzz : z = z₀ := e22qwit_central_involution_unique hm2 e hzT hz₀T hz2 hz₀2 hzc hz₀c
  obtain ⟨hAcard, hAK⟩ := hAV A hAS hAab hA4
  have hzA : z ∈ A := hzz ▸ hz₀V A hAS hAK
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  obtain ⟨t, -, htz⟩ := dihedral_central_involution_sq hm2 e hzT hz2 hzc
  have hzJ : z ∈ pslRange K := by
    rw [← htz]
    have := Subgroup.pow_index_mem (pslRange K) t
    rwa [pslRange_index_eq_two hodd] at this
  refine ⟨hAcard, hzA, ?_⟩
  obtain ⟨b, hbA, hbJ⟩ : ∃ b ∈ A, b ∉ pslRange K := by
    by_contra h
    push Not at h
    exact hAJ h
  have hb2' : b ^ 2 = 1 := hAab.2 b hbA
  have hb1 : b ≠ 1 := fun h => hbJ (h ▸ (pslRange K).one_mem)
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  obtain ⟨U, w, hUc, hUcard, hbU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hodd hcard3 hb2' hbJ
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set (PGL2 K)) :=
    zpowers_le_normalizer_of_inverting hww hwinv
  have hzb : b * z = z * b := by
    have := hAab.1.is_comm.comm (⟨b, hbA⟩ : ↥A) ⟨z, hzA⟩
    exact congrArg Subtype.val this
  have hzC : z ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact hzb.symm
  have hzmul : z ∈ (U : Set (PGL2 K)) * (Subgroup.zpowers w : Set (PGL2 K)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U _ hnorm]
    exact hzC
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hzmul
  have hzU : z ∉ U := by
    intro hzU
    exact hbJ ((e22pl2pgl_involution_unique hUc hzU hbU hz2' hb2' hz1 hb1) ▸ hzJ)
  have hvw : v = w := by
    rcases e22pl2pgl_mem_zpowers_involution hww hv with h | h
    · exfalso
      apply hzU
      rw [← huv, h, mul_one]
      exact hu
    · exact h
  subst hvw
  have hzinv : ∀ x ∈ U, z * x * z⁻¹ = x⁻¹ := by
    intro x hx
    rw [← huv]
    have h1 : u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
    rw [h1, hwinv x hx]
    have h2 := hUcomm u hu x⁻¹ (U.inv_mem hx)
    calc u * x⁻¹ * u⁻¹ = x⁻¹ * u * u⁻¹ := by rw [h2]
      _ = x⁻¹ := by group
  have hbU' : ∀ x ∈ U, b * x = x * b := fun x hx => hUcomm b hbU x hx
  have hab : z ∉ Subgroup.zpowers b := by
    intro hzb'
    rcases e22pl2pgl_mem_zpowers_involution (by rw [← sq]; exact hb2') hzb' with h | h
    · exact hz1 h
    · exact hbJ (h ▸ hzJ)
  have hCN : Subgroup.centralizer ({b} : Set (PGL2 K)) ≤
      Subgroup.normalizer (U : Set (PGL2 K)) := by
    rw [hC]
    exact sup_le Subgroup.le_normalizer hnorm
  have hqodd := odd_card_of_isOddPrimePower hodd
  have h5 : 5 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  obtain ⟨r, hr, hr2, hrU⟩ := e22pl2pgl_exists_odd_prime (n := Nat.card U)
    (by rw [hUcard]; exact outerTorusOrder_mod_four hqodd)
    (by rw [hUcard]; exact six_le_outerTorusOrder hqodd h5)
  have hr' : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨P₀, hP₀⟩ := e22ptor_exists_torsion r hUcomm
  have hPU : P₀ ≤ U := fun x hx => ((hP₀ x).1 hx).1
  have hPgrp : IsPGroup r P₀ := fun x => by
    obtain ⟨k, hk⟩ := ((hP₀ x).1 x.2).2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hPne : P₀ ≠ ⊥ := by
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥U) r hrU
    have hxo : orderOf (x : PGL2 K) = r := (Subgroup.orderOf_coe x).trans hx
    have hxP : (x : PGL2 K) ∈ P₀ :=
      (hP₀ _).2 ⟨x.2, 1, by rw [pow_one]; exact hxo ▸ pow_orderOf_eq_one _⟩
    have hx1 : (x : PGL2 K) ≠ 1 := fun h => by
      rw [h, orderOf_one] at hxo
      exact hr.one_lt.ne hxo
    intro hbot
    exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxP))
  have hNP : ∀ t ∈ Subgroup.normalizer (U : Set (PGL2 K)),
      t ∈ Subgroup.normalizer (P₀ : Set (PGL2 K)) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    intro x hx
    obtain ⟨hxU, k, hk⟩ := (hP₀ x).1 hx
    refine (hP₀ _).2 ⟨(Subgroup.mem_normalizer_iff.mp ht x).mp hxU, k, ?_⟩
    rw [conj_pow, hk]
    group
  have hAact : ∀ y ∈ A, ∀ u ∈ U, y * u * y⁻¹ = u ∨ y * u * y⁻¹ = u⁻¹ := by
    intro y hy u hu
    rcases e22ptor_mem_four hAcard hbA hzA hb1 hab hy with h | h | h | h
    · left
      rw [h]
      group
    · right
      rw [h]
      exact hzinv u hu
    · left
      rw [h, hbU' u hu]
      group
    · right
      have : y * u * y⁻¹ = z * (b * u * b⁻¹) * z⁻¹ := by rw [h]; group
      rw [this, hbU' u hu]
      simpa using hzinv u hu
  refine ⟨r, P₀, b, hr, hr2, hPne, hPgrp, ?_, hbA, hb1, fun x hx => hbU' x (hPU hx),
    fun x hx => hzinv x (hPU hx), ?_, ?_⟩
  · intro x hx
    obtain ⟨hxU, k, hk⟩ := (hP₀ x).1 hx
    obtain ⟨j, hj⟩ := e22ptor_exists_sq hr' hk
    rw [← hj]
    have := Subgroup.pow_index_mem (pslRange K) (x ^ j)
    rwa [pslRange_index_eq_two hodd] at this
  · intro y hy
    apply mem_normalizer_of_conj_mem
    intro x hx
    rcases hAact y hy x ((hP₀ x).1 hx).1 with h | h
    · rw [h]
      exact hx
    · rw [h]
      exact P₀.inv_mem hx
  · intro t _ htA
    apply hNP
    apply hCN
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htA b hbA

theorem typeIIo_transport {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {J : Subgroup H} [J.Normal] (hJ : IsPSL 2 p 1 ↥J)
    (hC : Subgroup.centralizer (J : Set H) = ⊥) :
    J = ⊤ ∨ ∃ e : H ≃* PGL2 (ZMod p), J = (pslRange (ZMod p)).comap e.toMonoidHom := by
  have hp : p.Prime := Fact.out
  have hodd : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by simp⟩
  have hcard : 3 < Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    omega
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.equiv_psl2_zmod_of_model hJ
  obtain ⟨ι, hι, hPSL, hcore⟩ := CFSG.ABGDGroups.exists_embedding_of_normal_psl2 hodd hcard e hC
  have hPGL : ι.range ≤ pGammaL2PGLRange (ZMod p) :=
    le_top.trans_eq (e22ptr_pGammaL2PGLRange_eq_top (ZMod p)).symm
  rcases e22ptr_eq_psl_or_eq_pgl (ZMod p) hodd hPSL hPGL with h | h
  · left
    refine eq_top_iff.mpr fun x _ => ?_
    rw [← hcore]
    show ι x ∈ pGammaL2PSLRange (ZMod p)
    rw [← h]
    exact ⟨x, rfl⟩
  · right
    let e' : H ≃* PGL2 (ZMod p) :=
      (MonoidHom.ofInjective hι).trans ((MulEquiv.subgroupCongr h).trans
        (pGammaL2PGLRangeEquiv _).symm)
    have he' : ∀ x : H, (SemidirectProduct.inl (e' x) : PGammaL2 (ZMod p)) = ι x := by
      intro x
      have h1 := congrArg Subtype.val
        ((pGammaL2PGLRangeEquiv (ZMod p)).apply_symm_apply
          ((MulEquiv.subgroupCongr h) (MonoidHom.ofInjective hι x)))
      rw [pGammaL2PGLRangeEquiv_coe] at h1
      exact h1
    refine ⟨e', ?_⟩
    ext x
    rw [← hcore]
    show ι x ∈ pGammaL2PSLRange (ZMod p) ↔ e' x ∈ pslRange (ZMod p)
    rw [← he' x]
    unfold pGammaL2PSLRange
    rw [MonoidHom.range_comp, Subgroup.mem_map_iff_mem SemidirectProduct.inl_injective]

theorem typeIIo_torus_abstract {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hp7 : 7 ≤ p) {H : Type} [Group H] [Finite H] {J S A : Subgroup H} [J.Normal]
    (hJ : IsPSL 2 p 1 ↥J) (hC : Subgroup.centralizer (J : Set H) = ⊥) (hS : IsSylowIn 2 S ⊤)
    {z : H} (hz2 : orderOf z = 2) (hzc : ∀ x ∈ S, z * x = x * z) (hAS : A ≤ S)
    (hAab : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) (hAJ : ¬ A ≤ J) :
    Nat.card A = 4 ∧ z ∈ A ∧ ∃ (r : ℕ) (P₀ : Subgroup H) (b : H), r.Prime ∧ r ≠ 2 ∧
      P₀ ≠ ⊥ ∧ IsPGroup r P₀ ∧ P₀ ≤ J ∧ b ∈ A ∧ b ≠ 1 ∧
      (∀ x ∈ P₀, b * x = x * b) ∧ (∀ x ∈ P₀, z * x * z⁻¹ = x⁻¹) ∧
      (∀ a ∈ A, a ∈ Subgroup.normalizer (P₀ : Set H)) ∧
      (∀ t ∈ S, (∀ a ∈ A, t * a = a * t) → t ∈ Subgroup.normalizer (P₀ : Set H)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases typeIIo_transport hp7 hJ hC with hJtop | ⟨e, he⟩
  · exact absurd (hJtop ▸ le_top) hAJ
  · have hK : Nat.card (ZMod p) = p := Nat.card_zmod p
    have hodd : IsOddPrimePower (Nat.card (ZMod p)) := e22pl2pgl_isOddPrimePower hp7 hK
    have hq8 : Nat.card (ZMod p) % 8 = 1 ∨ Nat.card (ZMod p) % 8 = 7 := by rwa [hK]
    have hq7 : 7 ≤ Nat.card (ZMod p) := by rwa [hK]
    have := e22pl2pgl_finite (ZMod p)
    have htop : (⊤ : Subgroup H).map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.surjective
    have hS' : IsSylowIn 2 (S.map e.toMonoidHom) ⊤ := by
      have := (E1.isSylowIn_map_mulEquiv e (P := S) (H := ⊤)).mpr hS
      rwa [htop] at this
    have hz2' : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz2
    have hzc' : ∀ x ∈ S.map e.toMonoidHom, e z * x = x * e z := by
      rintro _ ⟨t, ht, rfl⟩
      show e z * e t = e t * e z
      rw [← map_mul, ← map_mul, hzc t ht]
    have hAab' : IsElemAbelian 2 (A.map e.toMonoidHom) :=
      isElemAbelian_map_hom e.toMonoidHom hAab
    have hcard : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective e.injective
    have hAJ' : ¬ A.map e.toMonoidHom ≤ pslRange (ZMod p) := by
      intro h
      apply hAJ
      rw [he]
      intro a ha
      exact h (Subgroup.mem_map_of_mem _ ha)
    obtain ⟨hAcard, hzA, r, P₀, b, hr, hr2, hPne, hPg, hPJ, hbA, hb1, hbP, hzP, hAP, hSP⟩ :=
      typeIIo_torus_pgl2 hodd hq8 hq7 hS' hz2' hzc' (Subgroup.map_mono hAS) hAab'
        (hcard ▸ hA4) hAJ'
    have hmemP : ∀ x : H, x ∈ P₀.comap e.toMonoidHom ↔ e x ∈ P₀ := fun x => Iff.rfl
    refine ⟨hcard ▸ hAcard, ?_, r, P₀.comap e.toMonoidHom, e.symm b, hr, hr2, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact (Subgroup.mem_map_iff_mem e.injective).mp hzA
    · intro hbot
      apply hPne
      refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
      have : e.symm y ∈ P₀.comap e.toMonoidHom := by
        rw [hmemP]
        simpa using hy
      rw [hbot, Subgroup.mem_bot] at this
      have h1 : e (e.symm y) = e 1 := congrArg e this
      simpa using h1
    · exact hPg.comap_of_injective e.toMonoidHom e.injective
    · intro x hx
      have := hPJ hx
      rw [he]
      exact this
    · exact (Subgroup.mem_map_equiv.mp hbA)
    · intro h
      apply hb1
      have := congrArg e h
      simpa using this
    · intro x hx
      apply e.injective
      rw [map_mul, map_mul]
      have hx' : e x ∈ P₀ := hx
      simpa using hbP _ hx'
    · intro x hx
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv]
      exact hzP _ hx
    · intro a ha
      apply mem_normalizer_of_conj_mem
      intro x hx
      have hx' : e x ∈ P₀ := hx
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (hAP (e a) (Subgroup.mem_map_of_mem _ ha)) (e x)).mp hx'
      show e (a * x * a⁻¹) ∈ P₀
      simpa using h1
    · intro t ht htA
      apply mem_normalizer_of_conj_mem
      intro x hx
      have hx' : e x ∈ P₀ := hx
      have hcomm : ∀ a' ∈ A.map e.toMonoidHom, e t * a' = a' * e t := by
        rintro _ ⟨a, ha, rfl⟩
        show e t * e a = e a * e t
        rw [← map_mul, ← map_mul, htA a ha]
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (hSP (e t) (Subgroup.mem_map_of_mem _ ht) hcomm) (e x)).mp hx'
      show e (t * x * t⁻¹) ∈ P₀
      simpa using h1

theorem typeIIo_local {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp7 : 7 ≤ p) {T A Q D : Subgroup G} {z : G}
    (hAT : A ≤ T) (hAQ : A ≤ Q) (hAab : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A)
    (hDQ : D ≤ Q) (hDn : (D.subgroupOf Q).Normal) (hDp : IsPSL 2 p 1 ↥D)
    (hDs : IsSimpleGroup ↥D) (hDnc : ∃ a b : ↥D, a * b ≠ b * a)
    (hTQ : IsSylowIn 2 (T ⊓ Q) Q)
    (hAD : ∃ a ∈ A, ∀ y ∈ D, ∀ y₀ ∈ Subgroup.centralizer (D : Set G), a ≠ y * y₀)
    (hAC : ∀ a ∈ A, a ∈ Subgroup.centralizer (D : Set G) → a = 1)
    (hzD : z ∈ D) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ T ⊓ Q, z * x = x * z) :
    ∃ (r : ℕ) (P₀ : Subgroup G) (b w : G), r.Prime ∧ r ≠ 2 ∧ P₀ ≤ D ∧ P₀ ≠ ⊥ ∧
      IsPGroup r P₀ ∧ Nat.card A = 4 ∧ b ∈ A ∧ b ≠ 1 ∧ w ∈ A ∧
      (∀ g ∈ D, w * g * w⁻¹ = z * g * z⁻¹) ∧
      (∀ a ∈ A, a ∈ Subgroup.normalizer (P₀ : Set G)) ∧ (∀ x ∈ P₀, b * x = x * b) ∧
      (∀ x ∈ P₀, z * x * z⁻¹ = x⁻¹) ∧
      (∀ t ∈ T ⊓ Q, (∀ a ∈ A, t * a = a * t) → t ∈ Subgroup.normalizer (P₀ : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hTQle : T ⊓ Q ≤ Q := inf_le_right
  have hDle : D ≤ Q := hDQ
  set Y : Subgroup ↥Q := (Subgroup.centralizer (D : Set G)).subgroupOf Q with hY
  have hYn : Y.Normal := by
    refine ⟨fun y hy q => ?_⟩
    rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hy ⊢
    intro d hd
    have hd' : (q : G)⁻¹ * d * (q : G) ∈ D := by
      have := hDn.conj_mem ⟨d, hDle hd⟩ (Subgroup.mem_subgroupOf.mpr hd) q⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have h1 := hy _ hd'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    calc d * ((q : G) * (y : G) * (q : G)⁻¹) = (q : G) * ((q : G)⁻¹ * d * (q : G) * (y : G)) *
          (q : G)⁻¹ := by group
      _ = (q : G) * ((y : G) * ((q : G)⁻¹ * d * (q : G))) * (q : G)⁻¹ := by rw [h1]
      _ = (q : G) * (y : G) * (q : G)⁻¹ * d := by group
  have : Y.Normal := hYn
  set π : ↥Q →* ↥Q ⧸ Y := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  have hZ : Subgroup.center ↥D = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnc).2
  have hDC : ∀ d ∈ D, d ∈ Subgroup.centralizer (D : Set G) → d = 1 := by
    intro d hd hdC
    have hmem : (⟨d, hd⟩ : ↥D) ∈ Subgroup.center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hdC y y.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set DQ : Subgroup ↥Q := D.subgroupOf Q with hDQdef
  set TQ : Subgroup ↥Q := (T ⊓ Q).subgroupOf Q with hTQdef
  set AQ : Subgroup ↥Q := A.subgroupOf Q with hAQdef
  have hATQ : A ≤ T ⊓ Q := le_inf hAT hAQ
  have hinj : ∀ a b : ↥Q, a ∈ DQ → b ∈ DQ → π a = π b → a = b := by
    intro a b ha hb hab
    have h1 : a⁻¹ * b ∈ Y := QuotientGroup.eq.mp hab
    rw [hY, Subgroup.mem_subgroupOf] at h1
    have h2 : (a⁻¹ * b : ↥Q) ∈ DQ := DQ.mul_mem (DQ.inv_mem ha) hb
    rw [hDQdef, Subgroup.mem_subgroupOf] at h2
    have h3 := hDC _ h2 h1
    have : a⁻¹ * b = 1 := Subtype.ext h3
    exact inv_mul_eq_one.mp this
  set JH : Subgroup (↥Q ⧸ Y) := DQ.map π with hJH
  have hJHn : JH.Normal := Subgroup.Normal.map hDn π hπs
  have hJHp : IsPSL 2 p 1 ↥JH := by
    let φ : ↥DQ →* ↥JH := π.subgroupMap DQ
    have hφi : Function.Injective φ := by
      intro a b hab
      have : π (a : ↥Q) = π (b : ↥Q) := congrArg Subtype.val hab
      exact Subtype.ext (hinj _ _ a.2 b.2 this)
    have hφs : Function.Surjective φ := π.subgroupMap_surjective DQ
    let e : ↥D ≃* ↥JH := (Subgroup.subgroupOfEquivOfLe hDle).symm.trans
      (MulEquiv.ofBijective φ ⟨hφi, hφs⟩)
    exact CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm hDp
  have hCJH : Subgroup.centralizer (JH : Set (↥Q ⧸ Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    obtain ⟨q, rfl⟩ := hπs h
    rw [Subgroup.mem_bot]
    have hqY : q ∈ Y := by
      rw [hY, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro d hd
      have hdQ : (⟨d, hDle hd⟩ : ↥Q) ∈ DQ := Subgroup.mem_subgroupOf.mpr hd
      have hc := Subgroup.mem_centralizer_iff.mp hh (π ⟨d, hDle hd⟩) (Subgroup.mem_map_of_mem π hdQ)
      have h1 : (q⁻¹ * ⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) ∈ Y := by
        have hc' : π (⟨d, hDle hd⟩ * q) = π (q * ⟨d, hDle hd⟩) := by
          rw [map_mul, map_mul]; exact hc
        have := QuotientGroup.eq.mp hc'
        simpa [mul_assoc] using this
      have h2 : (q⁻¹ * ⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) ∈ DQ := by
        refine DQ.mul_mem (?_) hdQ
        have := hDn.conj_mem _ (DQ.inv_mem hdQ) q⁻¹
        simpa [mul_assoc] using this
      rw [hY, Subgroup.mem_subgroupOf] at h1
      rw [hDQdef, Subgroup.mem_subgroupOf] at h2
      have h3 := hDC _ h2 h1
      have h4 : (q⁻¹ * ⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) = 1 := Subtype.ext h3
      have h5 : (⟨d, hDle hd⟩ : ↥Q) * q = q * ⟨d, hDle hd⟩ := by
        have h6 : q⁻¹ * (⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) = 1 := by
          rw [← h4]; group
        have h7 : q = (⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩ : ↥Q) := inv_mul_eq_one.mp h6
        calc (⟨d, hDle hd⟩ : ↥Q) * q = ⟨d, hDle hd⟩ * (⟨d, hDle hd⟩⁻¹ * q * ⟨d, hDle hd⟩) := by
              rw [← h7]
          _ = q * ⟨d, hDle hd⟩ := by group
      exact congrArg Subtype.val h5
    exact (QuotientGroup.eq_one_iff q).mpr hqY
  have hTQ' : IsSylowIn 2 TQ ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ Q) (K := Q) (H := Q) hTQle
      le_rfl).mpr hTQ
    rwa [Subgroup.subgroupOf_self] at h
  set TH : Subgroup (↥Q ⧸ Y) := TQ.map π with hTH
  have hTH' : IsSylowIn 2 TH ⊤ := isSylowIn_top_map π hπs hTQ'
  have hzQ : z ∈ Q := hDle hzD
  set zQ : ↥Q := ⟨z, hzQ⟩ with hzQdef
  have hzY : zQ ∉ Y := by
    intro h
    rw [hY, Subgroup.mem_subgroupOf] at h
    have := hDC z hzD h
    rw [this, orderOf_one] at hz2
    omega
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hzQ2 : zQ ^ 2 = 1 := Subtype.ext (by simpa using hz2')
  have hzH2 : orderOf (π zQ) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hzQ2, map_one]
    · intro h
      exact hzY ((QuotientGroup.eq_one_iff zQ).mp h)
  have hzHc : ∀ x ∈ TH, π zQ * x = x * π zQ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have ht' : (t : G) ∈ T ⊓ Q := Subgroup.mem_subgroupOf.mp ht
    exact Subtype.ext (hzc _ ht')
  have hAQ' : AQ ≤ TQ := by
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr (hATQ (Subgroup.mem_subgroupOf.mp ha))
  set AH : Subgroup (↥Q ⧸ Y) := AQ.map π with hAH
  have hAHT : AH ≤ TH := Subgroup.map_mono hAQ'
  have hAHab : IsElemAbelian 2 AH := isElemAbelian_map_hom π (isElemAbelian_subgroupOf hAQ hAab)
  have hAinj : ∀ a b : ↥Q, a ∈ AQ → b ∈ AQ → π a = π b → a = b := by
    intro a b ha hb hab
    have h1 : a⁻¹ * b ∈ Y := QuotientGroup.eq.mp hab
    rw [hY, Subgroup.mem_subgroupOf] at h1
    have h2 : (a⁻¹ * b : ↥Q) ∈ AQ := AQ.mul_mem (AQ.inv_mem ha) hb
    rw [hAQdef, Subgroup.mem_subgroupOf] at h2
    have h3 := hAC _ h2 h1
    have : a⁻¹ * b = 1 := Subtype.ext h3
    exact inv_mul_eq_one.mp this
  have hcardAH : Nat.card AH = Nat.card A := by
    let φ : ↥AQ →* ↥AH := π.subgroupMap AQ
    have hφi : Function.Injective φ := by
      intro a b hab
      have : π (a : ↥Q) = π (b : ↥Q) := congrArg Subtype.val hab
      exact Subtype.ext (hAinj _ _ a.2 b.2 this)
    have hφs : Function.Surjective φ := π.subgroupMap_surjective AQ
    rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv
  have hAHJ : ¬ AH ≤ JH := by
    intro hle
    obtain ⟨a, ha, haD⟩ := hAD
    have haQ : (⟨a, hAQ ha⟩ : ↥Q) ∈ AQ := Subgroup.mem_subgroupOf.mpr ha
    obtain ⟨d, hd, hda⟩ := hle (Subgroup.mem_map_of_mem π haQ)
    have h2 : d⁻¹ * ⟨a, hAQ ha⟩ ∈ Y := QuotientGroup.eq.mp hda
    rw [hY, Subgroup.mem_subgroupOf] at h2
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    exact haD (d : G) hdD ((d : G)⁻¹ * a) h2 (by group)
  obtain ⟨hAHcard, hzAH, r, Pbar, bbar, hr, hr2, hPne, hPg, hPJ, hbbarA, hbbar1, hbbarP, hzP, hAP,
      hTP⟩ :=
    typeIIo_torus_abstract (J := JH) hp hp8 hp7 hJHp hCJH hTH' hzH2 hzHc hAHT hAHab
      (hcardAH ▸ hA4) hAHJ
  have hcj : ∀ s q : ↥Q, q ∈ DQ → s * q * s⁻¹ ∈ DQ ∧
      π (s * q * s⁻¹) = π s * π q * (π s)⁻¹ := by
    intro s q hq
    exact ⟨hDn.conj_mem q hq s, by rw [map_mul, map_mul, map_inv]⟩
  set P₀ : Subgroup G := ((Pbar.comap π) ⊓ DQ).map Q.subtype with hP₀def
  have hP₀mem : ∀ g : G, g ∈ P₀ ↔ ∃ q : ↥Q, π q ∈ Pbar ∧ q ∈ DQ ∧ (q : G) = g := by
    intro g
    simp only [hP₀def, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap,
      Subgroup.subtype_apply]
    constructor
    · rintro ⟨q, ⟨h1, h2⟩, h3⟩
      exact ⟨q, h1, h2, h3⟩
    · rintro ⟨q, h1, h2, h3⟩
      exact ⟨q, ⟨h1, h2⟩, h3⟩
  have hP₀D : P₀ ≤ D := by
    intro g hg
    obtain ⟨q, -, hq, rfl⟩ := (hP₀mem g).1 hg
    exact Subgroup.mem_subgroupOf.mp hq
  have hP₀ne : P₀ ≠ ⊥ := by
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hPne
    have hxJ : (x : ↥Q ⧸ Y) ∈ DQ.map π := by
      rw [← hJH]
      exact hPJ x.2
    obtain ⟨d, hd, hdx⟩ := hxJ
    intro hbot
    have hdP : (d : G) ∈ P₀ := (hP₀mem _).2 ⟨d, by rw [hdx]; exact x.2, hd, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hdP
    have hd1 : d = 1 := Subtype.ext hdP
    apply hx1
    apply Subtype.ext
    rw [← hdx, hd1, map_one]
    rfl
  have hP₀g : IsPGroup r P₀ := by
    intro g
    obtain ⟨q, hqP, hqD, hq⟩ := (hP₀mem g.1).1 g.2
    obtain ⟨k, hk⟩ := hPg ⟨π q, hqP⟩
    refine ⟨k, ?_⟩
    have h1 : (π q) ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : q ^ r ^ k = 1 := by
      apply hinj _ _ (DQ.pow_mem hqD _) DQ.one_mem
      rw [map_pow, map_one]
      exact h1
    apply Subtype.ext
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3 ⊢
    rw [← hq]
    exact h3
  have hnormP : ∀ s : ↥Q, π s ∈ Subgroup.normalizer (Pbar : Set (↥Q ⧸ Y)) →
      (s : G) ∈ Subgroup.normalizer (P₀ : Set G) := by
    intro s hs
    apply mem_normalizer_of_conj_mem
    intro g hg
    obtain ⟨q, hqP, hqD, rfl⟩ := (hP₀mem g).1 hg
    obtain ⟨h1, h2⟩ := hcj s q hqD
    refine (hP₀mem _).2 ⟨s * q * s⁻¹, ?_, h1, rfl⟩
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp hs (π q)).mp hqP
  obtain ⟨bQ, hbQA, hbQ⟩ := hbbarA
  obtain ⟨wQ, hwQA, hwQ⟩ := hzAH
  have hbc : ∀ x ∈ P₀, (bQ : G) * x = x * bQ := by
    intro g hg
    obtain ⟨q, hqP, hqD, rfl⟩ := (hP₀mem g).1 hg
    obtain ⟨h1, h2⟩ := hcj bQ q hqD
    have h3 : bQ * q * bQ⁻¹ = q := by
      apply hinj _ _ h1 hqD
      rw [h2, hbQ]
      have := hbbarP (π q) hqP
      calc bbar * π q * bbar⁻¹ = (π q * bbar) * bbar⁻¹ := by rw [this]
        _ = π q := by group
    have h4 : bQ * q = q * bQ := by
      calc bQ * q = (bQ * q * bQ⁻¹) * bQ := by group
        _ = q * bQ := by rw [h3]
    exact congrArg Subtype.val h4
  have hwz : ∀ g ∈ D, (wQ : G) * g * (wQ : G)⁻¹ = z * g * z⁻¹ := by
    intro g hg
    have hgQ : (⟨g, hDle hg⟩ : ↥Q) ∈ DQ := Subgroup.mem_subgroupOf.mpr hg
    obtain ⟨h1, h2⟩ := hcj wQ _ hgQ
    obtain ⟨h1', h2'⟩ := hcj zQ _ hgQ
    have h3 : wQ * ⟨g, hDle hg⟩ * wQ⁻¹ = zQ * ⟨g, hDle hg⟩ * zQ⁻¹ := by
      apply hinj _ _ h1 h1'
      rw [h2, h2', hwQ]
    exact congrArg Subtype.val h3
  have hzinv : ∀ x ∈ P₀, z * x * z⁻¹ = x⁻¹ := by
    intro g hg
    obtain ⟨q, hqP, hqD, rfl⟩ := (hP₀mem g).1 hg
    obtain ⟨h1, h2⟩ := hcj zQ q hqD
    have h3 : zQ * q * zQ⁻¹ = q⁻¹ := by
      apply hinj _ _ h1 (DQ.inv_mem hqD)
      rw [h2, map_inv]
      exact hzP (π q) hqP
    exact congrArg Subtype.val h3
  have hAn : ∀ a ∈ A, a ∈ Subgroup.normalizer (P₀ : Set G) := by
    intro a ha
    exact hnormP ⟨a, hAQ ha⟩
      (hAP _ (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)))
  have htn : ∀ t ∈ T ⊓ Q, (∀ a ∈ A, t * a = a * t) → t ∈ Subgroup.normalizer (P₀ : Set G) := by
    intro t ht htA
    have htQ : t ∈ Q := ht.2
    refine hnormP ⟨t, htQ⟩ (hTP (π ⟨t, htQ⟩) (Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr ht)) ?_)
    rintro _ ⟨aQ, haQ, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (htA _ (Subgroup.mem_subgroupOf.mp haQ))
  refine ⟨r, P₀, bQ, wQ, hr, hr2, hP₀D, hP₀ne, hP₀g, hcardAH ▸ hAHcard,
    Subgroup.mem_subgroupOf.mp hbQA, ?_, Subgroup.mem_subgroupOf.mp hwQA, hwz, hAn, hbc, hzinv,
    htn⟩
  intro h1
  apply hbbar1
  rw [← hbQ]
  have : bQ = 1 := Subtype.ext h1
  rw [this, map_one]

end CFSG.Quasithin.E2.E22N
