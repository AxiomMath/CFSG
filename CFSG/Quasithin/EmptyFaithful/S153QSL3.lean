module

public import CFSG.Quasithin.EmptyFaithful.S153QPC7
public import CFSG.Quasithin.EmptyFaithful.S153QSL2
public import CFSG.Quasithin.EmptyFaithful.SBc17L45

public section

namespace CFSG.Quasithin.SBc17

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.QP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_map_of_mem_normalizer_nc {A B : Type*} [Group A] [Group B] (ψ : A →* B)
    {K : Subgroup A} {x : A} (hx : x ∈ Subgroup.normalizer (K : Set A)) :
    ψ x ∈ Subgroup.normalizer ((K.map ψ : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨x * k * x⁻¹, (hx k).mp hk, by simp⟩
  · rintro ⟨k, hk, hkeq⟩
    refine ⟨x⁻¹ * k * x, (hx _).mpr ?_, ?_⟩
    · have e : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
      rw [e]
      exact hk
    · rw [map_mul, map_mul, map_inv, hkeq]
      group

theorem false_of_l45_core_nc {d : ℕ} (hd : d = 4 ∨ d = 5)
    {J M V K₁ : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J) (h5 : pRank 5 J ≤ 1)
    (φ : ↥(autOn J V) ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2))
    (hpar : IsParabolic2 (autOn J V) (autOn (M ⊓ J) V))
    (hK₁ : K₁ ≤ M ⊓ J) (hK₁N : M ⊓ J ≤ Subgroup.normalizer (K₁ : Set G))
    (hshape : IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ ∃ (O : Subgroup ↥K₁) (_ : O.Normal), IsPGroup 2 O ∧
      Nonempty (↥K₁ ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    {a : G} (haK : a ∈ K₁) (ha5 : orderOf a = 5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKJ : K₁ ≤ J := hK₁.trans inf_le_right
  have haJ : a ∈ J := hKJ haK
  have h5J := forall_isCyclic_of_pRank_le_one h5
  have hne : actOn hJV ⟨a, haJ⟩ ≠ 1 := actHom_ne_one_of_orderOf_five hJV hq hD h5J haJ ha5
  have hā5 : orderOf (actOn hJV ⟨a, haJ⟩) = 5 := by
    refine orderOf_eq_prime ?_ hne
    rw [← map_pow]
    have : (⟨a, haJ⟩ : ↥J) ^ 5 = 1 := Subtype.ext (by simp [← ha5, pow_orderOf_eq_one])
    rw [this, map_one]
  rcases hshape with h2 | ⟨O, hO, hO2, ⟨eO⟩⟩
  · obtain ⟨-, S₀, hS₀, hS₀P⟩ := hpar
    set S₁ : Subgroup ↥(autOn J V) := S₀.subgroupOf (autOn J V) with hS₁
    have hS₁p : IsPGroup 2 ↥S₁ := hS₀.2.1.comap_subtype
    set S' : Subgroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := S₁.map φ.toMonoidHom
      with hS'
    have hS'syl : IsSylowTwoOf S' ⊤ := by
      refine ⟨le_top, hS₁p.map _, ?_⟩
      show ¬ 2 ∣ S'.relIndex ⊤
      rw [Subgroup.relIndex_top_right, hS']
      exact (Subgroup.index_map_equiv S₁ φ).symm ▸ hS₀.2.2
    let ψ : ↥J →* Matrix.SpecialLinearGroup (Fin d) (ZMod 2) := φ.toMonoidHom.comp (actOn hJV)
    set N : Subgroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := (K₁.subgroupOf J).map ψ
      with hN
    have hxN : ψ ⟨a, haJ⟩ ∈ N := ⟨⟨a, haJ⟩, haK, rfl⟩
    let π₁ : ↥K₁ →* ↥N := (ψ.comp (Subgroup.inclusion hKJ)).codRestrict N
      (fun k => ⟨Subgroup.inclusion hKJ k, k.2, rfl⟩)
    have hπ₁ : Function.Surjective π₁ := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨(k : G), hk⟩, rfl⟩
    have hNX : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥N), (⊤ : Subgroup ↥N)⁆ :=
      solv2_of_surjective π₁ hπ₁ (solv2_of_commutator K₁ h2)
    have hSN : S' ≤ Subgroup.normalizer (N : Set (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) := by
      rintro _ ⟨σ, hσ, rfl⟩
      have hσP : (σ : MulAut ↥V) ∈ autOn (M ⊓ J) V :=
        hS₀P ⟨σ.2, Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hσ)⟩
      obtain ⟨x, hxV, hxM, hxσ⟩ := mem_autOn_iff.mp hσP
      have hxJ : x ∈ J := hxM.2
      have hσx : σ = actOn hJV ⟨x, hxJ⟩ := Subtype.ext hxσ.symm
      subst hσx
      refine mem_normalizer_map_of_mem_normalizer_nc ψ ?_
      rw [Subgroup.mem_normalizer_iff]
      intro k
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hK₁N hxM) (k : G)
    exact false_of_sylow_solv2 (F := ZMod 2) (by simp) hd hS'syl hSN hNX hxN
      ((orderOf_injective φ.toMonoidHom φ.injective _).trans hā5)
  ·
    have hK₁J' : K₁ ≤ J := hKJ
    let ψ : ↥J →* Matrix.SpecialLinearGroup (Fin d) (ZMod 2) := φ.toMonoidHom.comp (actOn hJV)
    set N : Subgroup (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := (K₁.subgroupOf J).map ψ with hN
    have hxN : ψ ⟨a, haJ⟩ ∈ N := ⟨⟨a, haJ⟩, haK, rfl⟩
    let π₁ : ↥K₁ →* ↥N := (ψ.comp (Subgroup.inclusion hK₁J')).codRestrict N
      (fun k => ⟨Subgroup.inclusion hK₁J' k, k.2, rfl⟩)
    have hπ₁ : Function.Surjective π₁ := by
      rintro ⟨_, k, hk, rfl⟩
      exact ⟨⟨(k : G), hk⟩, rfl⟩
    rcases isPGroup_two_or_seventeen_dvd π₁ hπ₁ hO2 eO with h | h
    · exfalso
      obtain ⟨m, hm⟩ := h ⟨ψ ⟨a, haJ⟩, hxN⟩
      have hpow : (ψ ⟨a, haJ⟩) ^ 2 ^ m = 1 := congrArg Subtype.val hm
      have hord : orderOf (ψ ⟨a, haJ⟩) = 5 :=
        (orderOf_injective φ.toMonoidHom φ.injective _).trans hā5
      have hdvd : orderOf (ψ ⟨a, haJ⟩) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hpow
      rw [hord] at hdvd
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd) (by norm_num)
    · exact not_seventeen_dvd_card_sl hd (h.trans (Subgroup.card_subgroup_dvd_card N))

theorem false_of_c27L45_nc {H R M J V K₁ : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hD : J ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn J) (h5 : pRank 5 J ≤ 1)
    (hK₁ : K₁ ≤ M ⊓ J) (hK₁N : M ⊓ J ≤ Subgroup.normalizer (K₁ : Set G))
    (hshape : IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ ∃ (O : Subgroup ↥K₁) (_ : O.Normal), IsPGroup 2 O ∧
      Nonempty (↥K₁ ⧸ O ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    {a : G} (haK : a ∈ K₁) (ha5 : orderOf a = 5) (h : C27L45 H R M J V) : False := by
  obtain ⟨hiso, hpar, -⟩ := h
  rcases hiso with h4 | h5'
  · obtain ⟨e⟩ := h4
    exact false_of_l45_core_nc (d := 4) (Or.inl rfl) hJV hq hD h5
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm) hpar hK₁
      hK₁N hshape haK ha5
  · obtain ⟨e⟩ := h5'
    exact false_of_l45_core_nc (d := 5) (Or.inr rfl) hJV hq hD h5
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm) hpar hK₁
      hK₁N hshape haK ha5

theorem input14615ContraInnerE_of_F_nc (iIF : Input14615ContraInnerF) :
    Input14615ContraInnerE := by
  intro G _ _ hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
    hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL hrem
  rcases hrem with h | h
  · exact iIF G hC27 T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ hfix hHyp hchar
      hPcore J hJc hJq hJle hJK hJ5 hK₁N hK₂N hK₂c hWG hin hJn ha hK₁J hZB hL h
  · exfalso
    obtain ⟨a, haO, ha5⟩ := hdec.exists_order_p_P14 hred.prime hred.odd
    have haK₁ : a ∈ K₁ := hset.oTwo₁ haO
    have ha5' : orderOf a = 5 := by rw [ha5, hctx.1]
    have hK₁M : K₁ ≤ g12_14615 T K₂ ⊓ J := fun x hx =>
      ⟨⟨sup_le_mcOf_14615 S hred hset (Subgroup.mem_sup_left hx),
        le_of_mem_cComp hJc (hK₁J hx)⟩, hK₁J hx⟩
    have hK₁Nm : g12_14615 T K₂ ⊓ J ≤ Subgroup.normalizer (K₁ : Set G) := fun x hx =>
      hfix x hx.1.1 hx.1.2
    have hR : pCoreOf 2 (mcOf T) ≤ Subgroup.normalizer (J : Set G) := hHyp.radical.1.trans hJn
    obtain ⟨hJV, hD, -⟩ := inner_facts hC27 hHyp hJc hJq hchar hJle hR
    exact false_of_c27L45_nc hJV hJq hD hJ5 hK₁M hK₁Nm (kOne_shape hctx.1 hdec hset)
      haK₁ ha5' h

end CFSG.Quasithin.SBc17
