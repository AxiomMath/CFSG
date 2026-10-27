module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Quasithin.Vol2.Ch8Sec2KG
public import CFSG.Quasithin.Vol2.Ch8Sec2L8213A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section L8213C

variable {X : Type} [Group X] [Finite X]

theorem commutator_eq_top_of_quasisimple_82 {K : Type} [Group K]
    (hK : CFSG.Open.IsQuasisimple K) : commutator K = ⊤ := hK.1

theorem card_of_hatM22_82 {K : Type} [Group K]
    (hKZ : Nat.card ↥(Subgroup.center K) = 3) (hKM : IsSporadic .M22 (K ⧸ Subgroup.center K)) :
    Nat.card K = 3 * 443520 := by
  obtain ⟨e⟩ := hKM
  have h8 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [Nat.card_congr e.toEquiv, hKZ] at h8
  have h9 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  rw [h9] at h8
  omega

theorem card_le_two_mul_82
    (K : Subgroup X) [K.Normal] (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKZ : Nat.card ↥(Subgroup.center ↥K) = 3) (hKM : IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K))
    (hCK : Subgroup.centralizer (K : Set X) = (Subgroup.center ↥K).map K.subtype) :
    Nat.card X ≤ 2 * Nat.card ↥K := by
  have h7 := card_of_hatM22_82 hKZ hKM
  obtain ⟨e⟩ := hKM
  have h1 := card_le_centralizer_mul_mulAut_82 K
  have h2 : Nat.card ↥(Subgroup.centralizer (K : Set X)) = 3 := by
    rw [hCK, Subgroup.card_map_of_injective K.subtype_injective, hKZ]
  have h3 : Nat.card (MulAut ↥K) ≤ 2 * 443520 := by
    have h4 := card_mulAut_le_quotCenter_82 (commutator_eq_top_of_quasisimple_82 hKq)
    have h5 : Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) = Nat.card (MulAut NativeSporadic.M22) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have h6 := CFSG.Sporadic.Schreier.m22_mulAut_card
    rw [CFSG.Sporadic.Mathieu.card_M22] at h6
    omega
  rw [h2] at h1
  rw [h7]
  calc Nat.card X ≤ 3 * Nat.card (MulAut ↥K) := h1
    _ ≤ 3 * (2 * 443520) := Nat.mul_le_mul_left 3 h3
    _ = 2 * (3 * 443520) := by ring

omit [Finite X] in
theorem ker_conjNormal_82 (K : Subgroup X) [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set X) := by
  have happ : ∀ (x : X) (k : ↥K), ((MulAut.conjNormal (H := K) x k : ↥K) : X) = x * k * x⁻¹ :=
    fun x k => MulAut.conjNormal_apply x k
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) h
    simp only [happ, MulAut.one_apply] at h2
    calc k * x = x * k * x⁻¹ * x := by rw [h2]
      _ = x * k := by group
  · intro h
    ext k
    rw [happ, MulAut.one_apply, ← h k k.2]
    group

theorem isAutTripleM22_82
    (hOut : KG82HatM22Out)
    (K : Subgroup X) [K.Normal] (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hKZ : Nat.card ↥(Subgroup.center ↥K) = 3) (hKM : IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K))
    (hCK : Subgroup.centralizer (K : Set X) = (Subgroup.center ↥K).map K.subtype)
    (hX : Nat.card X = 2 * Nat.card ↥K) : J4.IsAutTripleM22 X := by
  obtain ⟨e⟩ := hKM
  have hK : commutator ↥K = ⊤ := commutator_eq_top_of_quasisimple_82 hKq
  set Z := (Subgroup.center ↥K).map K.subtype with hZdef
  have hZK : Z ≤ K := Subgroup.map_subtype_le _
  have happ : ∀ (x : X) (k : ↥K), ((MulAut.conjNormal (H := K) x k : ↥K) : X) = x * k * x⁻¹ :=
    fun x k => MulAut.conjNormal_apply x k
  have hZ3 : Nat.card ↥Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective K.subtype_injective, hKZ]
  have hKc : Nat.card ↥K = 3 * 443520 := card_of_hatM22_82 hKZ ⟨e⟩
  have hinv : ∀ g : X, g ∉ K → ∀ x ∈ Z, g * x * g⁻¹ = x⁻¹ := by
    intro g hg x hx
    have hnot : ∀ k : ↥K, MulAut.conjNormal (H := K) g ≠ MulAut.conj k := by
      intro k hk
      apply hg
      have hgk : ∀ y : ↥K, g * (y : X) * g⁻¹ = k * y * (k : X)⁻¹ := by
        intro y
        have h1 := congrArg (fun φ : MulAut ↥K => ((φ y : ↥K) : X)) hk
        simp only [happ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
        exact h1
      have hc : g * (k : X)⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 := hgk ⟨(k : X)⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem k.2) hy) k.2⟩
        calc y * (g * (k : X)⁻¹) = (k * ((k : X)⁻¹ * y * k) * (k : X)⁻¹) * (g * (k : X)⁻¹) := by
              group
          _ = (g * ((k : X)⁻¹ * y * k) * g⁻¹) * (g * (k : X)⁻¹) := by rw [← h1]
          _ = g * (k : X)⁻¹ * y := by group
      rw [hCK] at hc
      have := K.mul_mem (hZK hc) k.2
      simpa using this
    obtain ⟨ζ, hζ, rfl⟩ := hx
    have h1 := hOut ↥K hKq hKZ ⟨e⟩ (MulAut.conjNormal g) hnot ζ hζ
    have h2 := congrArg Subtype.val h1
    rw [happ] at h2
    simpa using h2
  have hZc : ∀ ζ ∈ Z, ∀ k ∈ K, k * ζ = ζ * k := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)
  have hD : Subgroup.centralizer (Z : Set X) = K := by
    apply le_antisymm
    · intro g hg
      by_contra hgK
      obtain ⟨ζ, hζ, hζ1⟩ : ∃ ζ ∈ Z, ζ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hcon
        rw [this, Subgroup.card_bot] at hZ3
        norm_num at hZ3
      have h1 := hinv g hgK ζ hζ
      have h2 : ζ * g = g * ζ := Subgroup.mem_centralizer_iff.mp hg ζ hζ
      have h3 : g * ζ * g⁻¹ = ζ := by rw [← h2, mul_inv_cancel_right]
      rw [h3] at h1
      have h4 : ζ ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [h1]
        exact mul_inv_cancel ζ
      have h5 : ζ ^ 3 = 1 := by
        have h6 := pow_card_eq_one' (G := ↥Z) (x := ⟨ζ, hζ⟩)
        rw [hZ3] at h6
        exact congrArg Subtype.val h6
      apply hζ1
      calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
        _ = 1 := by rw [h4, h5, inv_one, mul_one]
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro ζ hζ
      exact (hZc ζ hζ k hk).symm
  have hZn : Z.Normal := by
    rw [← hCK]
    infer_instance
  let ψ : ↥K →* J4.M22 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  let θ : X →* MulAut J4.M22 := (MulAut.congr e).toMonoidHom.comp
    ((mulAutQuotCenter82 ↥K).comp (MulAut.conjNormal (H := K)))
  have hψs : Function.Surjective ψ := by
    intro m
    obtain ⟨q, rfl⟩ := e.surjective m
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) q
    exact ⟨k, rfl⟩
  have hψk : ψ.ker = Z.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥K)) k = 1 := by
        apply e.injective
        rw [map_one]
        exact hk
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨k, h1, rfl⟩
    · rintro ⟨c, hc, hck⟩
      have hck' : c = k := Subtype.ext hck
      subst hck'
      change e (QuotientGroup.mk' (Subgroup.center ↥K) c) = 1
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc, map_one]
  have hθψ : ∀ (g : X) (d : ↥K) (h : g * d * g⁻¹ ∈ K),
      θ g (ψ d) = ψ ⟨g * d * g⁻¹, h⟩ := by
    intro g d h
    change e (mulAutQuotCenter82 ↥K (MulAut.conjNormal (H := K) g)
      (e.symm (e (d : ↥K ⧸ Subgroup.center ↥K)))) =
        e ((⟨g * d * g⁻¹, h⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)
    rw [MulEquiv.symm_apply_apply, mulAutQuotCenter82_mk]
    congr 2
  have hθker : θ.ker = Z := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg
      have h1 : mulAutQuotCenter82 ↥K (MulAut.conjNormal (H := K) g) = 1 := by
        apply (MulAut.congr e).injective
        rw [map_one]
        exact hg
      have h2 : MulAut.conjNormal (H := K) g = 1 := by
        apply injective_mulAutQuotCenter_82 hK
        rw [h1, map_one]
      have h3 : g ∈ (MulAut.conjNormal (H := K)).ker := h2
      rw [ker_conjNormal_82, hCK] at h3
      exact h3
    · intro hg
      have h3 : g ∈ (MulAut.conjNormal (H := K)).ker := by
        rw [ker_conjNormal_82, hCK]
        exact hg
      have h2 : MulAut.conjNormal (H := K) g = 1 := h3
      change (MulAut.congr e) (mulAutQuotCenter82 ↥K (MulAut.conjNormal (H := K) g)) = 1
      rw [h2, map_one, map_one]
  have hθs : Function.Surjective θ := by
    have : Finite (MulAut J4.M22) := finite_mulAut_82
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_le_card
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, hθker, hZ3, hX, hKc]
      at h1
    have h2 := CFSG.Sporadic.Schreier.m22_mulAut_card
    rw [CFSG.Sporadic.Mathieu.card_M22] at h2
    change Nat.card (MulAut ↥NativeSporadic.M22) ≤ _
    omega
  have hθK : ∀ k : ↥K, θ k = MulAut.conj (ψ k) := by
    intro k
    ext m
    obtain ⟨d, rfl⟩ := hψs m
    rw [hθψ k d (K.mul_mem (K.mul_mem k.2 d.2) (K.inv_mem k.2)), MulAut.conj_apply,
      ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hKθ : K.map θ = CFSG.ComponentClassification.OuterAutomorphisms.inner J4.M22 := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨ψ ⟨k, hk⟩, (hθK ⟨k, hk⟩).symm⟩
    · rintro _ ⟨m, rfl⟩
      obtain ⟨d, rfl⟩ := hψs m
      exact ⟨d, d.2, hθK d⟩
  have hidx : K.index = 2 := by
    have h1 := K.card_mul_index
    rw [hX] at h1
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    have h2 : Nat.card ↥K * K.index = Nat.card ↥K * 2 := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  refine ⟨Z, hZn, hZ3, ?_⟩
  rw [hD]
  exact ⟨hidx, ⟨hK⟩, rfl, hinv, ψ, θ, hψs, hψk, hθψ, hθs, hθker, hKθ⟩

end L8213C

end CFSG.Quasithin.H13
