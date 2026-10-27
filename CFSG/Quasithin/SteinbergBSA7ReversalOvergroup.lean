module

public import CFSG.LocalAnalysis.SteinbergBVA7OddQuotientIndexTwo
public import CFSG.LocalAnalysis.SteinbergBVA7ConstantRankFactorization
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG CFSG.QuasithinUnique CFSG.LocalAnalysis.SteinbergBV
open CFSG.LocalAnalysis.SteinbergBV.ConstantRank
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace ReversalOvergroup

theorem le_normalizer_of_conj_mem {H V : Subgroup G}
    (h : ∀ g ∈ H, ∀ v ∈ V, g * v * g⁻¹ ∈ V) : H ≤ normalizer (V : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro v
  refine ⟨h g hg v, fun hv => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hv
  rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at this

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  change (H ⊔ K).map (MulAut.conj g⁻¹).toMonoidHom = H ⊔ K
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjugate_eq_self_of_mem_normalizer hH)
    (conjugate_eq_self_of_mem_normalizer hK)

theorem conjugate_conjugate_eq (H : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate H a) b = CFSG.conjugate H (a * b) := by
  ext z
  simp only [mem_conjugate_iff_conj]
  rw [show a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ by group]

theorem conj_mem_of_characteristic {P S : Subgroup G} (hSP : S ≤ P)
    (hS : (S.subgroupOf P).Characteristic) {g : G} (hg : g ∈ normalizer (P : Set G)) {s : G}
    (hs : s ∈ S) : g * s * g⁻¹ ∈ S := by
  have hPg : P.map ((MulAut.conj g : G ≃* G) : G →* G) = P := by
    have := conjugate_eq_self_of_mem_normalizer (inv_mem hg)
    rwa [CFSG.conjugate, inv_inv] at this
  let φ : P ≃* P := ((MulAut.conj g).subgroupMap P).trans (MulEquiv.subgroupCongr hPg)
  have hmem : (⟨s, hSP hs⟩ : P) ∈ (S.subgroupOf P).comap φ.toMonoidHom := by
    rw [hS.fixed φ]
    exact hs
  exact hmem

variable [Finite G]

theorem le_of_isPGroup_of_odd_relIndex {P R D : Subgroup G} (hPR : P ≤ R) (hRD : R ≤ D)
    (hR : IsPGroup 2 R) (hodd : Odd (P.relIndex D)) : R ≤ P := by
  obtain ⟨n, hn⟩ := hR.index (P.subgroupOf R)
  have hdvd : P.relIndex R ∣ P.relIndex D :=
    Dvd.intro _ (relIndex_mul_relIndex P R D hPR hRD)
  have hn' : P.relIndex R = 2 ^ n := hn
  rw [hn'] at hdvd
  have h1 : n = 0 := by
    rcases n with _ | n
    · rfl
    · obtain ⟨k, hk⟩ := hodd
      obtain ⟨j, hj⟩ := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
      omega
  rw [h1, pow_zero] at hn'
  exact relIndex_eq_one.1 hn'

end ReversalOvergroup

open ReversalOvergroup

variable [Finite G]

theorem odd_conjugates_construct_actual_reversal_overgroup (T : Sylow 2 G)
    {P S U Q K D V X : Subgroup G} (hPT : P ≤ T) (hTP : P.relIndex T = 2) (hSP : S ≤ P)
    (hS : (S.subgroupOf P).Characteristic) (hUS : U ≤ S) (hUab : U ≤ centralizer (U : Set G))
    (hPU : P ≤ normalizer (U : Set G)) (hQ : Q = S ⊓ centralizer (U : Set G))
    (hodd : ∀ y ∈ normalizer (P : Set G), Odd (orderOf y) → ⁅U, CFSG.conjugate U y⁆ = ⊥)
    {x t : G} (hx : x ∈ normalizer (P : Set G)) (hxQ : ¬ CFSG.conjugate U x ≤ Q)
    (htT : t ∈ T) (htP : t ∉ P) (ht : ⁅U, CFSG.conjugate U t⁆ = ⊥) (hQK : ⁅Q, K⁆ ≤ U)
    (hD : D = closure ((P : Set G) ∪ {y | y ∈ normalizer (P : Set G) ∧ Odd (orderOf y)}))
    (hV : V = conjJoin D U) (hX : X = D ⊔ K) :
    U ≠ ⊥ ∧ U ≤ V ∧ V ≤ Q ∧ Q ≤ P ∧ V ≤ X ∧ X ≤ normalizer (V : Set G) ∧
      D ≤ normalizer (P : Set G) ∧ D.relIndex (normalizer (P : Set G)) = 2 ∧
      X ⊓ normalizer (P : Set G) = D ∧ IsSylowTwoOf P X ∧ x ∉ X ∧ t ∉ X ∧
      ¬ D ≤ normalizer (U : Set G) ∧
      ¬ X ⊓ normalizer (P : Set G) ≤ X ⊓ normalizer (U : Set G) := by
  classical
  set Y := normalizer (P : Set G) with hYdef
  have hP2 : IsPGroup 2 P := T.isPGroup'.to_le hPT
  have hTY : (T : Subgroup G) ≤ Y :=
    (normal_subgroupOf_iff_le_normalizer hPT).1 (normal_of_index_eq_two hTP)
  have hPY : P ≤ Y := le_normalizer
  have hTodd : ¬ 2 ∣ (T : Subgroup G).relIndex Y := fun h =>
    T.not_dvd_index (h.trans (Dvd.intro _ (relIndex_mul_index hTY)))
  have hmodd : Odd ((T : Subgroup G).relIndex Y) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hTodd)
  have hPYidx : P.relIndex Y = 2 * (T : Subgroup G).relIndex Y := by
    rw [← relIndex_mul_relIndex P T Y hPT hTY, hTP]
  have hP'2 : IsPGroup 2 (P.subgroupOf Y) :=
    hP2.comap_of_injective Y.subtype Y.subtype_injective
  obtain ⟨hD'n, hD'idx, hPD'rel, -, -, hdec', -⟩ :=
    normal_two_kernel_odd_quotient_index_two (P.subgroupOf Y) hP'2 hmodd hPYidx
      (closure (((P.subgroupOf Y : Subgroup Y) : Set Y) ∪ {y | Odd (orderOf y)})) rfl
  set D' : Subgroup Y :=
    closure (((P.subgroupOf Y : Subgroup Y) : Set Y) ∪ {y | Odd (orderOf y)}) with hD'
  have hDmap : D = D'.map Y.subtype := by
    rw [hD, hD', MonoidHom.map_closure, Set.image_union]
    have h1 : (P : Set G) = Y.subtype '' ((P.subgroupOf Y : Subgroup Y) : Set Y) := by
      ext g
      constructor
      · intro hg
        exact ⟨⟨g, hPY hg⟩, hg, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    have h2 : {y | y ∈ Y ∧ Odd (orderOf y)} = Y.subtype '' {y : Y | Odd (orderOf y)} := by
      ext g
      constructor
      · rintro ⟨hgY, hgo⟩
        refine ⟨⟨g, hgY⟩, ?_, rfl⟩
        change Odd (orderOf (⟨g, hgY⟩ : Y))
        rw [← Subgroup.orderOf_coe]
        exact hgo
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
        exact hy
    rw [h1, h2]
  have hDY : D ≤ Y := by
    rw [hDmap]
    exact map_subtype_le D'
  have hD'eq : D.subgroupOf Y = D' := by
    rw [hDmap]
    exact comap_map_eq_self_of_injective Y.subtype_injective D'
  have hDidx : D.relIndex Y = 2 := by
    change (D.subgroupOf Y).index = 2
    rw [hD'eq]
    exact hD'idx
  have hPD : P ≤ D := by
    rw [hD]
    exact fun p hp => subset_closure (Or.inl hp)
  have hPDodd : Odd (P.relIndex D) := by
    rw [← relIndex_subgroupOf hDY, hD'eq, hPD'rel]
    exact hmodd
  have hdec : ∀ d ∈ D, ∃ p ∈ P, ∃ y ∈ Y, Odd (orderOf y) ∧ d = p * y := by
    intro d hd
    rw [hDmap] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨p, hp, y, hy, rfl⟩ := hdec' d' hd'
    exact ⟨p, hp, y, y.2, by rwa [Subgroup.orderOf_coe], rfl⟩
  have hDnorm : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro y hy d hd
    rw [hDmap] at hd ⊢
    obtain ⟨d', hd', rfl⟩ := hd
    exact ⟨⟨y, hy⟩ * d' * ⟨y, hy⟩⁻¹, hD'n.conj_mem d' hd' ⟨y, hy⟩, rfl⟩
  have hsyl : ∀ R : Subgroup G, P ≤ R → R ≤ D → IsPGroup 2 R → R ≤ P :=
    fun R h1 h2 h3 => le_of_isPGroup_of_odd_relIndex h1 h2 h3 hPDodd
  have hconjS : ∀ y ∈ Y, CFSG.conjugate U y ≤ S := by
    intro y hy z hz
    rw [mem_conjugate_iff_conj] at hz
    have := conj_mem_of_characteristic hSP hS (inv_mem hy) (hUS hz)
    rwa [show y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z by group] at this
  have hconjQ : ∀ d ∈ D, CFSG.conjugate U d ≤ Q := by
    intro d hd
    obtain ⟨p, hp, y, hy, hyo, rfl⟩ := hdec d hd
    have heq : CFSG.conjugate U (p * y) = CFSG.conjugate U y := by
      ext z
      rw [mem_conjugate_iff_conj, mem_conjugate_iff_conj,
        show p * y * z * (p * y)⁻¹ = p * (y * z * y⁻¹) * p⁻¹ by group]
      exact ((mem_normalizer_iff.1 (hPU hp)) _).symm
    rw [heq, hQ]
    exact le_inf (hconjS y hy)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hodd y hy hyo)))
  have hVQ : V ≤ Q := by
    rw [hV, conjJoin]
    refine iSup_le fun s => ?_
    have : U.map (MulAut.conj (s : G)).toMonoidHom = CFSG.conjugate U (s : G)⁻¹ := by
      rw [CFSG.conjugate, inv_inv]
    rw [this]
    exact hconjQ _ (inv_mem s.2)
  have hUV : U ≤ V := by
    rw [hV, conjJoin]
    refine le_trans ?_ (le_iSup _ (⟨1, one_mem D⟩ : D))
    intro u hu
    exact ⟨u, hu, by simp⟩
  have hQP : Q ≤ P := hQ ▸ inf_le_left.trans hSP
  have hDV : D ≤ normalizer (V : Set G) := by
    refine le_normalizer_of_conj_mem fun d hd v hv => ?_
    rw [hV, conjJoin] at hv ⊢
    refine Subgroup.iSup_induction (C := fun w => d * w * d⁻¹ ∈
        ⨆ s : D, U.map (MulAut.conj (s : G)).toMonoidHom) _ hv (fun s w hw => ?_) ?_
      (fun a b ha hb => ?_)
    · obtain ⟨u, hu, rfl⟩ := hw
      refine Subgroup.mem_iSup_of_mem (⟨d * s, mul_mem hd s.2⟩ : D) ⟨u, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [show d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) by group]
      exact mul_mem ha hb
  have hKV : K ≤ normalizer (V : Set G) := by
    refine le_normalizer_of_conj_mem fun k hk v hv => ?_
    have hc : ⁅k, v⁆ ∈ V := by
      refine hUV (hQK ?_)
      rw [commutator_comm]
      exact commutator_mem_commutator hk (hVQ hv)
    rw [show k * v * k⁻¹ = ⁅k, v⁆ * v by rw [commutatorElement_def]; group]
    exact mul_mem hc hv
  have hXV : X ≤ normalizer (V : Set G) := hX ▸ sup_le hDV hKV
  have hDX : D ≤ X := hX ▸ le_sup_left
  have hVX : V ≤ X := hVQ.trans (hQP.trans (hPD.trans hDX))
  have hxX : x ∉ X := by
    intro hxX
    apply hxQ
    intro z hz
    rw [mem_conjugate_iff_conj] at hz
    have h2 := (mem_normalizer_iff.1 (hXV (inv_mem hxX)) _).1 (hUV hz)
    rw [show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z by group] at h2
    exact hVQ h2
  have hXY : X ⊓ Y = D := by
    have hle : D ≤ X ⊓ Y := le_inf hDX hDY
    have hmul := relIndex_mul_relIndex D (X ⊓ Y) Y hle inf_le_right
    rw [hDidx] at hmul
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ hmul) with h | h
    · exact absurd ((relIndex_eq_one.1 h) hx).1 hxX
    · rw [h] at hmul
      have h1 : D.relIndex (X ⊓ Y) = 1 := by omega
      exact le_antisymm (relIndex_eq_one.1 h1) hle
  have hPX : P ≤ X := hPD.trans hDX
  have hsylX : IsSylowTwoOf P X := by
    refine ⟨hPX, hP2, ?_⟩
    obtain ⟨A, hA⟩ := (hP2.comap_of_injective X.subtype X.subtype_injective).exists_le_sylow
    have hA₀2 : IsPGroup 2 ((A : Subgroup X).map X.subtype) := A.isPGroup'.map X.subtype
    have hPA₀ : P ≤ (A : Subgroup X).map X.subtype := fun p hp => ⟨⟨p, hPX hp⟩, hA hp, rfl⟩
    have hA₀P : (A : Subgroup X).map X.subtype = P := by
      by_contra hne
      obtain ⟨a, ⟨haA, haN⟩, haP⟩ := exists_mem_inf_normalizer_of_ne hA₀2 hPA₀ (Ne.symm hne)
      have haD : a ∈ D := hXY ▸ ⟨map_subtype_le _ haA, haN⟩
      exact haP (hsyl _ (le_inf hPA₀ hPD) inf_le_right (hA₀2.to_le inf_le_left) ⟨haA, haD⟩)
    have hAeq : P.subgroupOf X = A := by
      rw [← hA₀P]
      exact comap_map_eq_self_of_injective X.subtype_injective _
    rw [hAeq]
    exact A.not_dvd_index
  have htY : t ∈ Y := hTY htT
  have htX : t ∉ X := by
    intro htX
    have htD : t ∈ D := hXY ▸ ⟨htX, htY⟩
    exact htP (hsyl _ (le_inf hPT hPD) inf_le_right (T.isPGroup'.to_le inf_le_left) ⟨htT, htD⟩)
  have hDU : ¬ D ≤ normalizer (U : Set G) := by
    intro hDU
    have hconjN : ∀ g, t * g * t⁻¹ ∈ normalizer (U : Set G) →
        g ∈ normalizer ((CFSG.conjugate U t : Subgroup G) : Set G) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro z
      rw [mem_conjugate_iff_conj, mem_conjugate_iff_conj,
        show t * (g * z * g⁻¹) * t⁻¹ = (t * g * t⁻¹) * (t * z * t⁻¹) * (t * g * t⁻¹)⁻¹ by group]
      exact (mem_normalizer_iff.1 hg) _
    have hFn : ∀ g, g ∈ normalizer (U : Set G) → t * g * t⁻¹ ∈ normalizer (U : Set G) →
        g ∈ normalizer ((U ⊔ CFSG.conjugate U t : Subgroup G) : Set G) :=
      fun g h1 h2 => mem_normalizer_sup h1 (hconjN g h2)
    have hDF : ∀ d ∈ D, d ∈ normalizer ((U ⊔ CFSG.conjugate U t : Subgroup G) : Set G) :=
      fun d hd => hFn d (hDU hd) (hDU (hDnorm t htY d hd))
    have hPF : ∀ p ∈ P, p ∈ normalizer ((U ⊔ CFSG.conjugate U t : Subgroup G) : Set G) :=
      fun p hp => hFn p (hPU hp) (hPU ((mem_normalizer_iff.1 (hTY htT) p).1 hp))
    have hTP2 : (P.subgroupOf T).index = 2 := hTP
    have htt : t * t ∈ P :=
      (mul_mem_iff_of_index_two hTP2 (a := ⟨t, htT⟩) (b := ⟨t, htT⟩)).2 Iff.rfl
    have htF : t ∈ normalizer ((U ⊔ CFSG.conjugate U t : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conjugate_eq
      change (U ⊔ CFSG.conjugate U t).map (MulAut.conj t⁻¹).toMonoidHom = _
      rw [Subgroup.map_sup]
      change CFSG.conjugate U t ⊔ CFSG.conjugate (CFSG.conjugate U t) t = _
      rw [conjugate_conjugate_eq, conjugate_eq_self_of_mem_normalizer (hPU htt), sup_comm]
    have hTF : ∀ g ∈ (T : Subgroup G),
        g ∈ normalizer ((U ⊔ CFSG.conjugate U t : Subgroup G) : Set G) := by
      intro g hg
      by_cases hgP : g ∈ P
      · exact hPF g hgP
      · have h : g * t⁻¹ ∈ P :=
          (mul_mem_iff_of_index_two hTP2 (a := ⟨g, hg⟩) (b := ⟨t, htT⟩⁻¹)).2
            ⟨fun h => absurd h hgP, fun h => absurd (by simpa [mem_subgroupOf] using h) htP⟩
        rw [show g = g * t⁻¹ * t by group]
        exact mul_mem (hPF _ h) htF
    have hD2 : (D.subgroupOf Y).index = 2 := hDidx
    have htD : t ∉ D := fun h => htX (hDX h)
    have hYF : ∀ y ∈ Y, y ∈ normalizer ((U ⊔ CFSG.conjugate U t : Subgroup G) : Set G) := by
      intro y hy
      by_cases hyD : y ∈ D
      · exact hDF y hyD
      · have h : y * t⁻¹ ∈ D :=
          (mul_mem_iff_of_index_two hD2 (a := ⟨y, hy⟩) (b := ⟨t, htY⟩⁻¹)).2
            ⟨fun h => absurd h hyD, fun h => absurd (by simpa [mem_subgroupOf] using h) htD⟩
        rw [show y = y * t⁻¹ * t by group]
        exact mul_mem (hDF _ h) (hTF t htT)
    have hFC : U ⊔ CFSG.conjugate U t ≤ centralizer (U : Set G) :=
      sup_le hUab (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ht))
    apply hxQ
    rw [hQ]
    refine le_inf (hconjS x hx) fun z hz => hFC ?_
    rw [mem_conjugate_iff_conj] at hz
    have := (mem_normalizer_iff.1 (inv_mem (hYF x hx)) _).1
      ((le_sup_left : U ≤ U ⊔ CFSG.conjugate U t) hz)
    rwa [show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z by group] at this
  refine ⟨?_, hUV, hVQ, hQP, hVX, hXV, hDY, hDidx, hXY, hsylX, hxX, htX, hDU, ?_⟩
  · rintro rfl
    apply hxQ
    intro z hz
    rw [mem_conjugate_iff_conj, mem_bot, conj_eq_one_iff] at hz
    rw [hz]
    exact one_mem _
  · rw [hXY]
    exact fun h => hDU (h.trans inf_le_right)

end CFSG.Quasithin.SteinbergBS
