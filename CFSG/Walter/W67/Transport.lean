module

public import CFSG.Walter.W67.Lemma21

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_lt_of_ne_top {M : Subgroup G} (hM : M ≠ ⊤) : Nat.card M < Nat.card G := by
  rw [← Subgroup.card_top (G := G)]
  exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hM)

theorem Hyp.sylow_of_subgroup (h : Hyp G) {M : Subgroup G}
    (hM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M) (P : Sylow 2 M) :
    IsMulCommutative (P : Subgroup M) ∧ Nat.card (P : Subgroup M) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ((P : Subgroup M).map M.subtype) := P.isPGroup'.map _
  have hab := h.isMulCommutative_of_isPGroup hP2
  have eP := (P : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective
  refine ⟨⟨⟨fun a b => eP.injective (by rw [map_mul, map_mul]; exact hab.is_comm.comm _ _)⟩⟩, ?_⟩
  apply le_antisymm
  · have := h.card_le_eight hP2
    rwa [Subgroup.card_map_of_injective M.subtype_injective] at this
  · obtain ⟨S, hSM⟩ := hM
    have hS2 : IsPGroup 2 ((S : Subgroup G).subgroupOf M) :=
      S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
    obtain ⟨Q, hQ⟩ := hS2.exists_le_sylow
    have h8 : Nat.card ((S : Subgroup G).subgroupOf M) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, h.card_sylow S]
    rw [← h8, Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity Q]
    exact Subgroup.card_le_of_le hQ

@[expose] noncomputable def Hyp.ofSubgroup (h : Hyp G) {M : Subgroup G}
    (hM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M) {J' : G} (hJ'M : J' ∈ M)
    (hJ' : orderOf J' = 2) {K' : Subgroup G} (hK'M : K' ≤ M)
    (hK'C : K' ≤ Subgroup.centralizer ({J'} : Set G))
    (hK'n : ∀ x ∈ M, x * J' = J' * x → ∀ k ∈ K', x * k * x⁻¹ ∈ K')
    (p' f' : ℕ) [Fact p'.Prime] (hp' : p' ≠ 2) (hf' : 0 < f')
    (e : K' ≃* PSL(2, GaloisField p' f')) : Hyp M where
  p := p'
  f := f'
  p_ne_two := hp'
  f_pos := hf'
  abelian_sylow P := (h.sylow_of_subgroup hM P).1
  card_sylow P := (h.sylow_of_subgroup hM P).2
  J := ⟨J', hJ'M⟩
  orderOf_J := by rw [Subgroup.orderOf_mk, hJ']
  K := K'.subgroupOf M
  le_centralizer := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hK'C hk))
  normal := by
    have hle : K'.subgroupOf M ≤ Subgroup.centralizer ({(⟨J', hJ'M⟩ : M)} : Set M) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hK'C hk))
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro k x hk hx
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact hK'n x x.2 (congrArg Subtype.val hx') k hk
  iso := (Subgroup.subgroupOfEquivOfLe hK'M).trans e

section ofSubgroup

variable (h : Hyp G) {M : Subgroup G} (hM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M) {J' : G}
  (hJ'M : J' ∈ M) (hJ' : orderOf J' = 2) {K' : Subgroup G} (hK'M : K' ≤ M)
  (hK'C : K' ≤ Subgroup.centralizer ({J'} : Set G))
  (hK'n : ∀ x ∈ M, x * J' = J' * x → ∀ k ∈ K', x * k * x⁻¹ ∈ K')
  (p' f' : ℕ) [Fact p'.Prime] (hp' : p' ≠ 2) (hf' : 0 < f')
  (e : K' ≃* PSL(2, GaloisField p' f'))

@[simp] theorem Hyp.ofSubgroup_p :
    (h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).p = p' := rfl

@[simp] theorem Hyp.ofSubgroup_f :
    (h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).f = f' := rfl

@[simp] theorem Hyp.ofSubgroup_q :
    (h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).q = p' ^ f' := rfl

@[simp] theorem Hyp.ofSubgroup_J :
    ((h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).J : G) = J' := rfl

@[simp] theorem Hyp.ofSubgroup_K :
    (h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).K = K'.subgroupOf M := rfl

end ofSubgroup

theorem Hyp.case2_ofSubgroup (h : Hyp G) {M : Subgroup G}
    (hM : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M) {J' : G} (hJ'M : J' ∈ M)
    (hJ' : orderOf J' = 2) {K' : Subgroup G} (hK'M : K' ≤ M)
    (hK'C : K' ≤ Subgroup.centralizer ({J'} : Set G))
    (hK'n : ∀ x ∈ M, x * J' = J' * x → ∀ k ∈ K', x * k * x⁻¹ ∈ K')
    (p' f' : ℕ) [Fact p'.Prime] (hp' : p' ≠ 2) (hf' : 0 < f')
    (e : K' ≃* PSL(2, GaloisField p' f'))
    (hc : Case2 (h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e)) :
    ∃ L : Subgroup G, L ≤ M ∧ (L.subgroupOf M).Normal ∧ Odd (L.subgroupOf M).index ∧
      (∃ g ∈ M, Subgroup.zpowers g ⊔ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G))) = M) ∧
      (∃ K'' : Subgroup G, K'' ≤ L ⊓ Subgroup.centralizer ({J'} : Set G) ∧ J' ∉ K'' ∧
        L ⊓ Subgroup.centralizer ({J'} : Set G) = Subgroup.zpowers J' ⊔ K'' ∧
        Nonempty (K'' ≃* PSL(2, GaloisField p' f'))) ∧
      (p' ^ f' % 8 = 3 ∨ p' ^ f' % 8 = 5) := by
  obtain ⟨L', hL'n, hodd, ⟨g, hg⟩, ⟨K₃, hK₃, hJK₃, hC, ⟨eK⟩⟩, h8⟩ := hc
  set ι := M.subtype
  have hι : Function.Injective ι := M.subtype_injective
  have hrange : ι.range = M := Subgroup.range_subtype M
  have hcomap : ∀ X : Subgroup M, (X.map ι).subgroupOf M = X := fun X =>
    Subgroup.comap_map_eq_self_of_injective hι X
  have hCJ : (Subgroup.centralizer
      ({(h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).J} : Set M)).map ι =
      M ⊓ Subgroup.centralizer ({J'} : Set G) := by
    rw [JT.map_centralizer_singleton_of_injective ι hι, hrange]
    rfl
  set L := L'.map ι
  have hLM : L ≤ M := Subgroup.map_subtype_le L'
  refine ⟨L, hLM, by rw [hcomap]; exact hL'n, by rw [hcomap]; exact hodd, ⟨g, g.2, ?_⟩,
    ⟨K₃.map ι, ?_, ?_, ?_, ⟨(K₃.equivMapOfInjective ι hι).symm.trans eK⟩⟩, h8⟩
  · have := congrArg (Subgroup.map ι) hg
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      JT.map_centralizer_of_injective ι hι, hrange, ← MonoidHom.range_eq_map, hrange] at this
    exact this
  · have := Subgroup.map_mono (f := ι) hK₃
    rw [Subgroup.map_inf_eq _ _ _ hι, hCJ] at this
    exact this.trans (inf_le_inf_left _ inf_le_right)
  · rintro ⟨x, hx, hxJ⟩
    apply hJK₃
    have : x = (h.ofSubgroup hM hJ'M hJ' hK'M hK'C hK'n p' f' hp' hf' e).J := Subtype.ext hxJ
    rw [← this]
    exact hx
  · have := congrArg (Subgroup.map ι) hC
    rw [Subgroup.map_inf_eq _ _ _ hι, hCJ, Subgroup.map_sup, MonoidHom.map_zpowers] at this
    calc L ⊓ Subgroup.centralizer ({J'} : Set G) =
          L ⊓ (M ⊓ Subgroup.centralizer ({J'} : Set G)) := by
          rw [← inf_assoc, inf_eq_left.mpr hLM]
      _ = _ := this

theorem Hyp.exists_normal_index_two_of_case1 {X : Type} [Group X] [Finite X] (h : Hyp X)
    (hc : Case1 h) : ∃ N : Subgroup X, N.Normal ∧ N.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨M, hMn, hJM, hMC, hsup, -⟩, -⟩ := hc
  set O := CFSG.pPrimeCore 2 X
  have hO : Odd (Nat.card O) := by
    have := CFSG.pPrimeCore_coprime_card (p := 2) (G := X)
    rwa [Nat.coprime_two_left] at this
  set j : X ⧸ O := QuotientGroup.mk h.J
  have hj : orderOf j = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← QuotientGroup.mk_pow, pow_two, h.J_mul_J, QuotientGroup.mk_one]
    · rw [QuotientGroup.eq_one_iff] at h1
      have := Subgroup.orderOf_dvd_natCard O h1
      rw [h.orderOf_J] at this
      exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr this)
  have hc : ∀ x ∈ Subgroup.zpowers j, ∀ y ∈ M, x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hMC hy)).symm n).eq
  have hd : Subgroup.zpowers j ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers hj hx.1 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.2) hJM
  obtain ⟨hcard, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [hd, Subgroup.card_bot, mul_one, hsup, Subgroup.card_top, Nat.card_zpowers, hj] at hcard
  refine ⟨M.comap (QuotientGroup.mk' O), hMn.comap _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective O)]
  have := M.card_mul_index
  rw [hcard] at this
  have hpos : 0 < Nat.card M := Nat.card_pos
  nlinarith

section Quotient

variable (h : Hyp G) (N : Subgroup G) [N.Normal]

theorem Hyp.K_inf_eq_bot_of_odd (hN : Odd (Nat.card N)) : h.K ⊓ N = ⊥ := by
  refine PSL2Sub.eq_bot_of_odd h.iso h.odd_p h.f_pos inf_le_left (fun k hk w hw => ?_) ?_
  · exact ⟨h.K.mul_mem (h.K.mul_mem hk hw.1) (h.K.inv_mem hk),
      ‹N.Normal›.conj_mem w hw.2 k⟩
  · exact Odd.of_dvd_nat hN (Subgroup.card_dvd_of_le inf_le_right)

noncomputable def mapQuotientEquiv {X : Subgroup G} (hX : X ⊓ N = ⊥) :
    X ≃* X.map (QuotientGroup.mk' N) :=
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp X.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have : (x : G) ∈ X ⊓ N := ⟨x.2, hx⟩
    rw [hX, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]))

include h in
theorem Hyp.sylow_of_quotient (hN : Odd (Nat.card N)) (P : Sylow 2 (G ⧸ N)) :
    IsMulCommutative (P : Subgroup (G ⧸ N)) ∧ Nat.card (P : Subgroup (G ⧸ N)) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) 2 P
  rw [Sylow.coe_mapSurjective]
  have hQN : (Q : Subgroup G) ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact eq_one_of_odd_of_isPGroup Q.isPGroup' hx.1
      (Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard _ hx.2))
  have eQ := mapQuotientEquiv N hQN
  have hab := h.abelian_sylow Q
  refine ⟨⟨⟨fun a b => eQ.symm.injective (by rw [map_mul, map_mul]; exact hab.is_comm.comm _ _)⟩⟩,
    ?_⟩
  rw [← Nat.card_congr eQ.toEquiv, h.card_sylow Q]

theorem Hyp.orderOf_mk_J (hN : Odd (Nat.card N)) :
    orderOf (QuotientGroup.mk h.J : G ⧸ N) = 2 := by
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← QuotientGroup.mk_pow, pow_two, h.J_mul_J, QuotientGroup.mk_one]
  · rw [QuotientGroup.eq_one_iff] at h1
    have := Subgroup.orderOf_dvd_natCard N h1
    rw [h.orderOf_J] at this
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr this)

@[expose] noncomputable def Hyp.quotient (hN : Odd (Nat.card N)) : Hyp (G ⧸ N) where
  p := h.p
  f := h.f
  p_ne_two := h.p_ne_two
  f_pos := h.f_pos
  abelian_sylow P := (h.sylow_of_quotient N hN P).1
  card_sylow P := (h.sylow_of_quotient N hN P).2
  J := QuotientGroup.mk h.J
  orderOf_J := h.orderOf_mk_J N hN
  K := h.K.map (QuotientGroup.mk' N)
  le_centralizer := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change QuotientGroup.mk (k * h.J) = QuotientGroup.mk (h.J * k)
    rw [h.commute_J (h.K_le_H hk)]
  normal := by
    have hle : h.K.map (QuotientGroup.mk' N) ≤
        Subgroup.centralizer ({(QuotientGroup.mk h.J : G ⧸ N)} : Set (G ⧸ N)) := by
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change QuotientGroup.mk (k * h.J) = QuotientGroup.mk (h.J * k)
      rw [h.commute_J (h.K_le_H hk)]
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ x ⟨k, hk, rfl⟩ hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨c, hc, hcx⟩ := Suzuki.exists_commute_mk_eq N hN h.J_mul_J hx
    rw [← hcx]
    exact ⟨c * k * c⁻¹, h.conj_mem_K (h.mem_H_iff.mpr hc) hk, rfl⟩
  iso := (mapQuotientEquiv N (h.K_inf_eq_bot_of_odd N hN)).symm.trans h.iso

section quotient

variable (hN : Odd (Nat.card N))

@[simp] theorem Hyp.quotient_p : (h.quotient N hN).p = h.p := rfl

@[simp] theorem Hyp.quotient_f : (h.quotient N hN).f = h.f := rfl

@[simp] theorem Hyp.quotient_q : (h.quotient N hN).q = h.q := rfl

@[simp] theorem Hyp.quotient_J : (h.quotient N hN).J = QuotientGroup.mk h.J := rfl

@[simp] theorem Hyp.quotient_K : (h.quotient N hN).K = h.K.map (QuotientGroup.mk' N) := rfl

end quotient

end Quotient

theorem IsJRSubgroup.nonempty_jrGroup : S_IsJRSubgroup_nonempty_jrGroup := by
  intro G _ _ L K' J p g _ hp hg hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSL, hSe, hS8⟩ := hL.sylow
  have hK'L : K' ≤ L := hL.K_le.trans inf_le_left
  set ι := L.subtype
  have hι : Function.Injective ι := L.subtype_injective
  have hsylL : ∀ P : Sylow 2 L, Nat.card (P : Subgroup L) = 8 ∧
      ∃ x : G, ∀ y ∈ (P : Subgroup L).map ι, x * y * x⁻¹ ∈ (S : Subgroup G) := by
    intro P
    have hS2 : IsPGroup 2 ((S : Subgroup G).subgroupOf L) :=
      S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
    obtain ⟨Q, hQ⟩ := hS2.exists_le_sylow
    have hSL8 : Nat.card ((S : Subgroup G).subgroupOf L) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hS8]
    have hP8 : Nat.card (P : Subgroup L) = 8 := by
      apply le_antisymm
      · have hP2 : IsPGroup 2 ((P : Subgroup L).map ι) := P.isPGroup'.map _
        obtain ⟨S', hS'⟩ := hP2.exists_le_sylow
        have h1 := Subgroup.card_le_of_le hS'
        rw [Subgroup.card_map_of_injective hι] at h1
        have h2 : Nat.card (S' : Subgroup G) = Nat.card (S : Subgroup G) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
        rw [h2, hS8] at h1
        exact h1
      · rw [← hSL8, Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity Q]
        exact Subgroup.card_le_of_le hQ
    refine ⟨hP8, ?_⟩
    have hPG : Nat.card ((P : Subgroup L).map ι) = 2 ^ (Nat.card G).factorization 2 := by
      rw [Subgroup.card_map_of_injective hι, hP8, ← hS8, Sylow.card_eq_multiplicity]
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G (Sylow.ofCard _ hPG) S
    refine ⟨x, fun y hy => ?_⟩
    rw [← hx]
    change x * y * x⁻¹ ∈ MulAut.conj x • ((P : Subgroup L).map ι)
    have := Subgroup.smul_mem_pointwise_smul y (MulAut.conj x) ((P : Subgroup L).map ι) hy
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hCJ : (Subgroup.centralizer ({(⟨J, hL.J_mem⟩ : L)} : Set L)).map ι =
      L ⊓ Subgroup.centralizer ({J} : Set G) := by
    rw [JT.map_centralizer_singleton_of_injective ι hι, Subgroup.range_subtype]
    rfl
  let hL' : JRGroup L :=
    { p := p
      f := g
      p_ne_two := hp
      f_pos := hg
      index_ne_two := fun N hN => by
        have h1 := hL.index_ne_two (N.map ι) (Subgroup.map_subtype_le N)
        rw [show (N.map ι).subgroupOf L = N from
          Subgroup.comap_map_eq_self_of_injective hι N] at h1
        exact h1 hN
      card_sylow := fun P => (hsylL P).1
      elementary_sylow := fun P => by
        obtain ⟨x, hx⟩ := (hsylL P).2
        have hcomm : ∀ a b : (P : Subgroup L), a * b = b * a := by
          intro a b
          have ha := hx _ ⟨a, a.2, rfl⟩
          have hb := hx _ ⟨b, b.2, rfl⟩
          have hab := congrArg Subtype.val
            (hSe.toIsMulCommutative.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
          apply Subtype.ext
          apply Subtype.ext
          have : x * ((a : L) : G) * x⁻¹ * (x * ((b : L) : G) * x⁻¹) =
              x * ((b : L) : G) * x⁻¹ * (x * ((a : L) : G) * x⁻¹) := hab
          have h2 := congrArg (fun w => x⁻¹ * w * x) this
          simpa [mul_assoc] using h2
        have : IsMulCommutative (P : Subgroup L) := ⟨⟨hcomm⟩⟩
        refine ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_⟩
        have ha := hx _ ⟨a, a.2, rfl⟩
        have : IsElementaryAbelian 2 (S : Subgroup G) := hSe
        have h2 : (x * ((a : L) : G) * x⁻¹) ^ 2 = 1 :=
          elemPow_eq_one_of_isElementaryAbelian (A := (S : Subgroup G)) _ ha
        rw [conj_pow] at h2
        have h3 : ((a : L) : G) ^ 2 = 1 := by
          have := congrArg (fun w => x⁻¹ * w * x) h2
          simpa [mul_assoc] using this
        apply Subtype.ext
        apply Subtype.ext
        simpa using h3
      J := ⟨J, hL.J_mem⟩
      orderOf_J := by rw [Subgroup.orderOf_mk]; exact hL.orderOf_J
      K := K'.subgroupOf L
      le_centralizer := by
        intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hL.K_le hk).2)
      J_not_mem := fun h1 => hL.J_not_mem h1
      centralizer_eq := by
        apply Subgroup.map_injective hι
        rw [hCJ, Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hK'L]
        exact hL.centralizer_eq
      iso := (Subgroup.subgroupOfEquivOfLe hK'L).trans (Classical.choice hL.iso) }
  refine ⟨hL', rfl, rfl, rfl, ?_⟩
  change (K'.subgroupOf L).map ι = K'
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK'L]

end CFSG.Walter.W67
