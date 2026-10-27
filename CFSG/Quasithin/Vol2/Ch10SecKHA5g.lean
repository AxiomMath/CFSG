module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5f
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Hat

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem IsSL25Group.center_le_pCore {B : Type} [Group B] (hD : IsSL25Group B) :
    Subgroup.center B ≤ CFSG.pCore 2 B := by
  obtain ⟨α, hαs, hαk⟩ := hD.alt
  intro z hz
  rw [← hαk, MonoidHom.mem_ker]
  have : α z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro σ
    obtain ⟨y, rfl⟩ := hαs σ
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y)]
  rw [A5.G3.center_alt5_eq_bot] at this
  exact this

theorem sl25_inf_center_eq_bot {X : Type} [Group X] [Finite X] {B Z : Subgroup X}
    (hD : IsSL25Group ↥B) (hZ : Z ≤ Subgroup.center X) (hodd : ¬ 2 ∣ Nat.card Z) :
    B ⊓ Z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro z ⟨hzB, hzZ⟩
  have hzc : (⟨z, hzB⟩ : ↥B) ∈ Subgroup.center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZ hzZ) (y : X))
  have hzp := hD.center_le_pCore hzc
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥B) (p := 2)) ⟨_, hzp⟩
  have h1 : z ^ (2 ^ k) = 1 := congrArg (fun w : ↥B => (w : X)) (congrArg Subtype.val hk)
  have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf z ∣ Nat.card Z := by
    have := orderOf_dvd_natCard (⟨z, hzZ⟩ : ↥Z)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (orderOf z) 2 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp h2 with ⟨i, -, hi⟩
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [hi, h0]
      simp
    · exfalso
      apply hodd
      have : 2 ∣ orderOf z := by
        rw [hi]
        exact dvd_pow_self 2 (by omega)
      exact this.trans h3
  have : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right _ hcop) (dvd_refl _) h2
  exact orderOf_eq_one_iff.mp this

theorem noSL25Norm_of_central_quotient {X : Type} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (hZ : Z ≤ Subgroup.center X) (hodd : ¬ 2 ∣ Nat.card Z)
    (h : NoSL25Norm (X ⧸ Z)) : NoSL25Norm X := by
  intro T B hT hTB hD
  have hBZ : B ⊓ Z = ⊥ := sl25_inf_center_eq_bot hD hZ hodd
  set π : X →* X ⧸ Z := QuotientGroup.mk' Z with hπ
  have hT' : IsSylowTwoOf (T.map π) ⊤ :=
    isSylowTwoOf_top_map_of_surjective hT π (QuotientGroup.mk'_surjective Z)
  have hinj : Function.Injective (π.comp B.subtype) := by
    intro b b' hbb
    have h1 : ((b⁻¹ * b' : ↥B) : X) ∈ Z := by
      have : π (b : X) = π (b' : X) := hbb
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      simpa using this
    have h2 : ((b⁻¹ * b' : ↥B) : X) ∈ B ⊓ Z := ⟨(b⁻¹ * b' : ↥B).2, h1⟩
    rw [hBZ, Subgroup.mem_bot] at h2
    have : b⁻¹ * b' = 1 := Subtype.ext h2
    exact (inv_mul_eq_one.mp this)
  have hrange : (π.comp B.subtype).range = B.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hD' : IsSL25Group ↥(B.map π) :=
    hD.of_equiv ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
  have key : ∀ x : X, π x ∈ B.map π ↔ x ∈ B ⊔ Z := by
    intro x
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
  have hconj : ∀ t ∈ T, ∀ x : X, x ∈ B ⊔ Z → t * x * t⁻¹ ∈ B ⊔ Z := by
    intro t ht x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hy' : t * y * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hTB ht) y).mp hy
    have hz' : t * z * t⁻¹ ∈ Z := Subgroup.Normal.conj_mem inferInstance z hz t
    have : t * (y * z) * t⁻¹ = (t * y * t⁻¹) * (t * z * t⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy' hz'
  have hN : T.map π ≤ Subgroup.normalizer ((B.map π : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : (x : X ⧸ Z) = π x := rfl
    have hxt : π t * (x : X ⧸ Z) * (π t)⁻¹ = π (t * x * t⁻¹) := by
      rw [hx]
      simp
    rw [hxt, hx, key, key]
    constructor
    · exact hconj t ht x
    · intro hx'
      have := hconj t⁻¹ (T.inv_mem ht) _ hx'
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at this
  exact h (T.map π) (B.map π) hT' hN hD'

theorem noSL25Norm_hat_m22
    {L : Type} [Group L] [Finite L]
    (h : IsHat L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : NoSL25Norm L := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  refine noSL25Norm_of_central_quotient (Subgroup.center L) le_rfl ?_
    (NoSL25Norm.of_mulEquiv e.symm (noSL25Norm_m22 ⟨MulEquiv.refl _⟩))
  rw [hc]
  omega

theorem noSL25In_of_noPair {X : Type} [Group X] [Finite X] (hX : A5.G3.NoPairTwoFive X) :
    NoSL25In X := by
  intro T hT B hB hne hTB hD
  obtain ⟨x, hx5, u, hu, hxu⟩ := hD.five
  have hV : IsElemAbelian 2 ((CFSG.pCore 2 ↥B).map B.subtype) :=
    Lin2.isElemAbelian_map' hD.isElemAbelian_pCore B.subtype
  have hx5' : orderOf (x : X) = 5 := by rw [Subgroup.orderOf_coe]; exact hx5
  have hnorm : ∀ v ∈ (CFSG.pCore 2 ↥B).map B.subtype,
      (x : X) * v * (x : X)⁻¹ ∈ (CFSG.pCore 2 ↥B).map B.subtype := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨x * w * x⁻¹, (CFSG.pCore_normal (G := ↥B) (p := 2)).conj_mem _ hw x, by simp⟩
  have h := A5.G3.centralizes_of_noPair hX hV hx5' hnorm (u : X) ⟨u, hu, rfl⟩
  apply hxu
  apply Subtype.ext
  have := mul_inv_eq_iff_eq_mul.mp h
  simpa using this

theorem noSL25In_j2
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J2 X) : NoSL25In X :=
  noSL25In_of_noPair (A5.G3.noPairTwoFive_of_isSporadic h)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
