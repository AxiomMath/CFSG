module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCSteps

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_L_le614 {T M L V : Subgroup G} (h : Hyp611 G T M L V 4) :
    pCoreOf 2 L ≤ T ⊓ L := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    (h.toHyp5_0_1.sup_le_M).trans h.toHyp5_0_1.normal
  have hS : IsSylowTwoOf T (L ⊔ T) := h.toHyp5_0_1.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal hS le_sup_left hLT
  exact B6.pCoreOf_two_le_of_isSylowTwoOf hSL

theorem oTwoUpper_hImg614 {K T X : Subgroup G} (hXK : X ≤ K)
    (hsyl : IsSylowTwoOf T (K ⊔ T)) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hX2 : X = oTwoUpper X) :
    oTwoUpper (((X ⊔ (T ⊓ K)).subgroupOf K).map (mk614 K)) =
      (X.subgroupOf K).map (mk614 K) := by
  have hH₀K : X ⊔ (T ⊓ K) ≤ K := sup_le hXK inf_le_right
  have hO : oTwoUpper (X ⊔ (T ⊓ K)) = X := by
    apply le_antisymm
    · exact oTwoUpper_le_of_pow_mem fun x hx =>
        CFSG.Quasithin.E1.exists_pow_mem_of_mem_sup (hsyl.2.1.to_le inf_le_left)
          (inf_le_left.trans hTX) hx
    · exact (le_of_eq hX2).trans (oTwoUpper_mono le_sup_left)
  rw [oTwoUpper_map, A4.oTwoUpper_subgroupOf hH₀K, hO]

theorem conj_normalizes_TL614 {T M L V : Subgroup G} (h : Hyp611 G T M L V 4)
    {ℓ : Subgroup.normalizer (V : Set G)} (hℓL : (ℓ : G) ∈ L)
    (hℓN : conjAct V ℓ ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V)))
    {t : G} (ht : t ∈ T ⊓ L) : (ℓ : G) * t * (ℓ : G)⁻¹ ∈ T ⊓ L := by
  have htN : t ∈ Subgroup.normalizer (V : Set G) := h.L_le_normalizer ht.2
  have htA : conjAct V ⟨t, htN⟩ ∈ autOn (T ⊓ L) V := by
    unfold autOn
    exact Subgroup.mem_map.mpr ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hm : conjAct V (ℓ * ⟨t, htN⟩ * ℓ⁻¹) ∈ autOn (T ⊓ L) V := by
    have e : conjAct V (ℓ * ⟨t, htN⟩ * ℓ⁻¹) =
        conjAct V ℓ * conjAct V ⟨t, htN⟩ * (conjAct V ℓ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hℓN _).mp htA
  unfold autOn at hm
  obtain ⟨w, hw, hwm⟩ := Subgroup.mem_map.mp hm
  have hwT : (w : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hw
  set m : G := (ℓ : G) * t * (ℓ : G)⁻¹ with hmdef
  have hgC : (w : G)⁻¹ * m ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hwm
    simp only [conjAct_apply614, Subgroup.coe_mul, Subgroup.coe_inv] at hv'
    have key : (w : G)⁻¹ * (m * v * m⁻¹) * (w : G) = v := by
      rw [hmdef, ← hv']
      group
    have hg : (w : G)⁻¹ * m * v * ((w : G)⁻¹ * m)⁻¹ = v := by
      calc (w : G)⁻¹ * m * v * ((w : G)⁻¹ * m)⁻¹
          = (w : G)⁻¹ * (m * v * m⁻¹) * (w : G) := by group
        _ = v := key
    calc v * ((w : G)⁻¹ * m) = (((w : G)⁻¹ * m) * v * ((w : G)⁻¹ * m)⁻¹) *
          ((w : G)⁻¹ * m) := by rw [hg]
      _ = ((w : G)⁻¹ * m) * v := by group
  have hgL : (w : G)⁻¹ * m ∈ L := by
    refine L.mul_mem (L.inv_mem hwT.2) ?_
    rw [hmdef]
    exact L.mul_mem (L.mul_mem hℓL ht.2) (L.inv_mem hℓL)
  have hg2 : (w : G)⁻¹ * m ∈ pCoreOf 2 L :=
    h.toHyp5_0_1.inf_centralizer_le h.L_le_normalizer h.module.2.2
      (Subgroup.mem_inf.mpr ⟨hgL, hgC⟩)
  have hg3 := pCoreOf_L_le614 h hg2
  have hmT : m ∈ T ⊓ L := by
    have : m = (w : G) * ((w : G)⁻¹ * m) := by group
    rw [this]
    exact (T ⊓ L).mul_mem hwT hg3
  exact hmT

theorem exists_cartan_three614 (hO2 : L216ModuleFact) (hO4 : L216NormalizerFact)
    {T M L V X : Subgroup G} (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    (hXL : X ≤ L) (hX2 : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    ∃ d : G, d ∈ L ∧ d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
      d ∈ Subgroup.normalizer (V : Set G) ∧ orderOf d = 3 ∧
      d ∈ Subgroup.normalizer ((X ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := (hO2 G T M L V h horth).1
  have h3 : 3 ∣ Nat.card ↥(autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))) := by
    rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp x.2
  have hxL' := hxL
  unfold autOn at hxL'
  obtain ⟨ℓ, hℓ, hℓx⟩ := Subgroup.mem_map.mp hxL'
  have hℓL : (ℓ : G) ∈ L := Subgroup.mem_subgroupOf.mp hℓ
  have hℓx' : conjAct V ℓ = (x : MulAut V) := hℓx
  have hℓN : conjAct V ℓ ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [hℓx']; exact hxN
  have hℓinv : conjAct V ℓ⁻¹ ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [map_inv, hℓx']
    exact Subgroup.inv_mem _ hxN
  have hNℓ : (ℓ : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact conj_normalizes_TL614 h hℓL hℓN ht
    · intro ht
      have hℓinvL : (((ℓ⁻¹ : Subgroup.normalizer (V : Set G))) : G) ∈ L := by
        rw [Subgroup.coe_inv]
        exact L.inv_mem hℓL
      have := conj_normalizes_TL614 h (ℓ := ℓ⁻¹) hℓinvL hℓinv ht
      have e : (((ℓ⁻¹ : Subgroup.normalizer (V : Set G))) : G) * ((ℓ : G) * t * (ℓ : G)⁻¹) *
          (((ℓ⁻¹ : Subgroup.normalizer (V : Set G))) : G)⁻¹ = t := by
        rw [Subgroup.coe_inv]
        group
      rw [e] at this
      exact this
  have hx3 : (x : MulAut V) ^ 3 = 1 := by
    have h1 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h2 := congrArg (fun y : ↥(autOn L V ⊓ Subgroup.normalizer
      ((autOn (T ⊓ L) V : Subgroup (MulAut V)) : Set (MulAut V))) => (y : MulAut V)) h1
    simpa using h2
  have hℓ3 : conjAct V (ℓ ^ 3) = 1 := by
    rw [map_pow, hℓx', hx3]
  have hℓ3C : (ℓ : G) ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hℓ3
    simp only [conjAct_apply614, MulAut.one_apply, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hℓ3P : (ℓ : G) ^ 3 ∈ pCoreOf 2 L :=
    h.toHyp5_0_1.inf_centralizer_le h.L_le_normalizer h.module.2.2
      (Subgroup.mem_inf.mpr ⟨L.pow_mem hℓL 3, hℓ3C⟩)
  obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨(ℓ : G) ^ 3, hℓ3P⟩
  have hb' : ((ℓ : G) ^ 3) ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hd3 : ((ℓ : G) ^ 2 ^ b) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hb'
  have hd1 : (ℓ : G) ^ 2 ^ b ≠ 1 := by
    intro hd
    have hd' : (ℓ : Subgroup.normalizer (V : Set G)) ^ 2 ^ b = 1 :=
      Subtype.ext (by simpa using hd)
    have hxb : (x : MulAut V) ^ 2 ^ b = 1 := by
      rw [← hℓx', ← map_pow, hd', map_one]
    have hxb' : x ^ 2 ^ b = 1 := Subtype.ext (by simpa using hxb)
    have hdvd := orderOf_dvd_of_pow_eq_one hxb'
    rw [hx] at hdvd
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at h32
  have hord : orderOf ((ℓ : G) ^ 2 ^ b) = 3 := orderOf_eq_prime hd3 hd1
  have hdL : (ℓ : G) ^ 2 ^ b ∈ L := L.pow_mem hℓL _
  have hdTL : (ℓ : G) ^ 2 ^ b ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)).pow_mem hNℓ _
  have hdV : (ℓ : G) ^ 2 ^ b ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).pow_mem ℓ.2 _
  have hdX : (ℓ : G) ^ 2 ^ b ∈ Subgroup.normalizer ((X ⊔ pCoreOf 2 L : Subgroup G) : Set G) :=
    hO4 G T M L V X h horth hXL hX2 hX5 hXn hTX (Subgroup.mem_inf.mpr ⟨hdTL, hdL⟩)
  exact ⟨(ℓ : G) ^ 2 ^ b, hdL, hdTL, hdV, hord, hdX⟩

end CFSG.Quasithin.H13.T614

end
