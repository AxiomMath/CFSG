module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentySevenGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.GroupTheory.FiveElementTwoGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC22.F11 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem cElt_eq_centModInM (D : Data G) (V₀ : Subgroup G) (v : G) :
    CElt D.M V₀ v = centModInM D V₀ v := by
  ext m
  simp only [CElt, centModInM, centModEl, Subgroup.mem_mk, Subgroup.mem_inf, Set.mem_setOf_eq]
  constructor <;> intro h <;> exact ⟨h.1, h.2.1, h.2.2⟩

theorem map_sylow_le_centralizer_of_central {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : IsElemAbelian 2 V₀) (hV₀le : V₀ ≤ V) {v : G} (hv : v ∈ V)
    (Q : Sylow 5 ↥(CElt M V₀ v))
    (hQ : Opp 5 (CElt M V₀ v) ≤ Subgroup.centralizer (V₀ : Set G)) :
    (Q : Subgroup ↥(CElt M V₀ v)).map (CElt M V₀ v).subtype ≤
      Subgroup.centralizer ({v} : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rintro x ⟨q, hq, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  let qQ : ↥Q := ⟨q, hq⟩
  obtain ⟨k, hk⟩ := (Sylow.isPGroup' Q).exists_orderOf_eq_pow qQ
  have hk' : orderOf ((q : ↥(CElt M V₀ v)) : G) = 5 ^ k := by
    have h1 : orderOf ((q : ↥(CElt M V₀ v)) : G) = orderOf q :=
      orderOf_injective (Subgroup.subtype (CElt M V₀ v)) Subtype.coe_injective q
    have h2 : orderOf q = orderOf qQ := by
      exact orderOf_injective ((Q : Subgroup ↥(CElt M V₀ v)).subtype)
        Subtype.coe_injective (⟨q, hq⟩ : ↥Q)
    rw [h1, h2, hk]
  have hqopp : ((q : ↥(CElt M V₀ v)) : G) ∈ Opp 5 (CElt M V₀ v) := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.subset_closure ⟨q.2, k, hk'⟩
  have hqC : ((q : ↥(CElt M V₀ v)) : G) ∈ Subgroup.centralizer (V₀ : Set G) := hQ hqopp
  have hqc : ∀ d ∈ V₀, ((q : ↥(CElt M V₀ v)) : G) * d * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = d := by
    intro d hd
    have hcomm := (Subgroup.mem_centralizer_iff.mp hqC) d hd
    calc ((q : ↥(CElt M V₀ v)) : G) * d * ((q : ↥(CElt M V₀ v)) : G)⁻¹
        = d * ((q : ↥(CElt M V₀ v)) : G) * ((q : ↥(CElt M V₀ v)) : G)⁻¹ := by rw [hcomm]
      _ = d := by group
  have hqv : ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ * v⁻¹ ∈ V₀ :=
    q.2.2.2
  set d : G := ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ * v⁻¹ with hd
  have hdmem : d ∈ V₀ := hqv
  have hstep : ∀ i : ℕ, ((q : ↥(CElt M V₀ v)) : G) ^ i * v *
      (((q : ↥(CElt M V₀ v)) : G) ^ i)⁻¹ = v * d ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hqd : ((q : ↥(CElt M V₀ v)) : G) * d ^ i * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = d ^ i :=
        hqc _ (V₀.pow_mem hdmem i)
      have hqv' : ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = v * d := by
        have hcomm : d * v = v * d := by
          have hc := (show IsMulCommutative ↥V from hV.1).is_comm.comm
            (⟨d, hV₀le hdmem⟩ : ↥V) (⟨v, hv⟩ : ↥V)
          simpa using hc
        have h1 : ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = d * v := by
          rw [hd]; group
        rw [h1, hcomm]
      calc ((q : ↥(CElt M V₀ v)) : G) ^ (i + 1) * v *
            (((q : ↥(CElt M V₀ v)) : G) ^ (i + 1))⁻¹
          = ((q : ↥(CElt M V₀ v)) : G) * (((q : ↥(CElt M V₀ v)) : G) ^ i * v *
              (((q : ↥(CElt M V₀ v)) : G) ^ i)⁻¹) *
              ((q : ↥(CElt M V₀ v)) : G)⁻¹ := by group
        _ = ((q : ↥(CElt M V₀ v)) : G) * (v * d ^ i) *
              ((q : ↥(CElt M V₀ v)) : G)⁻¹ := by rw [ih]
        _ = (((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹) *
              (((q : ↥(CElt M V₀ v)) : G) * d ^ i *
                ((q : ↥(CElt M V₀ v)) : G)⁻¹) := by group
        _ = (v * d) * d ^ i := by rw [hqv', hqd]
        _ = v * d ^ (i + 1) := by group
  have hdv : d = 1 := by
    have h := hstep (orderOf ((q : ↥(CElt M V₀ v)) : G))
    rw [pow_orderOf_eq_one] at h
    simp only [one_mul, inv_one, mul_one] at h
    have hdn : d ^ orderOf ((q : ↥(CElt M V₀ v)) : G) = 1 := by
      have h' := congrArg (fun z => v⁻¹ * z) h
      simpa [mul_assoc] using h'.symm
    have hd2 : d ^ 2 = 1 := hV₀.2 d hdmem
    have hcop : Nat.Coprime 2 (orderOf ((q : ↥(CElt M V₀ v)) : G)) := by
      rw [hk']
      exact (show Nat.Coprime 2 5 by norm_num).pow_right k
    have hdiv : orderOf d ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hd2)
        (orderOf_dvd_iff_pow_eq_one.mpr hdn)
    have ho1 : orderOf d = 1 := Nat.dvd_one.mp hdiv
    exact orderOf_eq_one_iff.mp ho1
  have hqv' : ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = v * d := by
    have hcomm : d * v = v * d := by
      have hc := (show IsMulCommutative ↥V from hV.1).is_comm.comm
        (⟨d, hV₀le hdmem⟩ : ↥V) (⟨v, hv⟩ : ↥V)
      simpa using hc
    have h1 : ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = d * v := by
      rw [hd]; group
    rw [h1, hcomm]
  have hfix : ((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹ = v := by
    rw [hqv', hdv, mul_one]
  calc ((q : ↥(CElt M V₀ v)) : G) * v
      = (((q : ↥(CElt M V₀ v)) : G) * v * ((q : ↥(CElt M V₀ v)) : G)⁻¹) *
          ((q : ↥(CElt M V₀ v)) : G) := by group
    _ = v * ((q : ↥(CElt M V₀ v)) : G) := by rw [hfix]

theorem irrOn_of_not_le_centralizer {V₀ H : Subgroup G}
    (hV0el : CFSG.Open.IsElemAbelian 2 V₀) (hm : mSub V₀ ≤ 4)
    (hHV0 : H ≤ normalizer (V₀ : Set G))
    (hnot : ¬ Opp 5 H ≤ Subgroup.centralizer (V₀ : Set G)) :
    ∀ U : Subgroup G, U ≤ V₀ → H ≤ normalizer (U : Set G) → U = ⊥ ∨ U = V₀ := by
  intro U hU hHU
  have h16 : Nat.card V₀ ≤ 16 := by
    rw [card_eq_two_pow_mSub (IsElemAbelian.isPGroup hV0el)]
    calc 2 ^ mSub V₀ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm
      _ = 16 := by norm_num
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    by_contra htop
    apply hnot
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, k, hxord⟩
    exact CFSG.GroupTheory.mem_centralizer_of_orderOf_five_pow_of_invariant hV0el h16 hU hbot htop
      (hHV0 hxH) (hHU hxH) hxord

theorem nineteen_five (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) (h4 : R19_4At D V₀ V p L K h) :
    R19_5At D V₀ V p L K h := by
  intro v hv hv0
  rw [← cElt_eq_centModInM D V₀ v]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hV0 : InCalV0 D.M V₀ V :=
    inCalV0_of_hyp125 h.hyp.hyp125 (ne_bot_of_one_lt_mSub h.hyp.big)
  have hVE : IsElemAbelian 2 V₀ := hV0.1.2.2.2
  have hV0le : V₀ ≤ V := hV0.2.2.1
  have hVel : IsElemAbelian 2 V := h.hyp.isElemAbelian
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hVel.comm ha hb
  have hm : mSub V₀ ≤ 4 := h4
  set C : Subgroup G := CElt D.M V₀ v with hCdef
  have hCM : C ≤ D.M := fun x hx => (hCdef ▸ hx : x ∈ CElt D.M V₀ v).1
  have hCV0 : C ≤ normalizer (V₀ : Set G) :=
    fun x hx => (hCdef ▸ hx : x ∈ CElt D.M V₀ v).2.1
  have hCv : ∀ x ∈ C, x * v * x⁻¹ * v⁻¹ ∈ V₀ :=
    fun x hx => (hCdef ▸ hx : x ∈ CElt D.M V₀ v).2.2
  by_cases hcent : Opp 5 C ≤ Subgroup.centralizer (V₀ : Set G)
  · obtain ⟨Q⟩ := Sylow.nonempty (p := 5) (G := ↥C)
    exact ⟨Q, map_sylow_le_centralizer_of_central (M := D.M) hVel hVE hV0le hv Q hcent⟩
  · have hirr : ∀ U : Subgroup G, U ≤ V₀ → C ≤ normalizer (U : Set G) → U = ⊥ ∨ U = V₀ :=
      irrOn_of_not_le_centralizer hVE hm hCV0 hcent
    have hgen : ∀ d ∈ V₀, ∃ x ∈ D.M ⊓ Subgroup.centralizer (V₀ : Set G),
        CentralizesMod V₀ V x ∧ x * v * x⁻¹ = v * d :=
      fun d hd => exists_conj_eq_mul_of_inCalV0_gen (M := D.M) (V₀ := V₀) (V := V) (X := C)
        hV0 hv hv0 hCM hCv hirr hd
    let _ : MulAction ↥C G := MulAction.compHom G (MulAut.conj.comp C.subtype)
    have horbit_mem : ∀ x : ↥(MulAction.orbit (↥C) v), v⁻¹ * (x : G) ∈ V₀ := by
      intro x
      obtain ⟨c, hc⟩ := MulAction.mem_orbit_iff.mp x.2
      rw [← hc]
      change v⁻¹ * ((c : G) * v * (c : G)⁻¹) ∈ V₀
      have hmem : (c : G) * v * (c : G)⁻¹ * v⁻¹ ∈ V₀ := hCv (c : G) c.2
      have h1 : v⁻¹ * ((c : G) * v * (c : G)⁻¹) =
          ((c : G) * v * (c : G)⁻¹ * v⁻¹) := by
        calc v⁻¹ * ((c : G) * v * (c : G)⁻¹)
            = v⁻¹ * (((c : G) * v * (c : G)⁻¹ * v⁻¹) * v) := by group
          _ = v⁻¹ * (v * ((c : G) * v * (c : G)⁻¹ * v⁻¹)) := by
                rw [hcommV _ (hV0le hmem) v hv]
          _ = ((c : G) * v * (c : G)⁻¹ * v⁻¹) := by group
      rw [h1]
      exact hmem
    have horbit_mem' : ∀ d : ↥V₀, v * (d : G) ∈ MulAction.orbit (↥C) v := by
      intro d
      obtain ⟨x, hxM, hxcent, hxeq⟩ := hgen (d : G) d.2
      have hvd : v * (d : G) * v⁻¹ = (d : G) := by
        calc v * (d : G) * v⁻¹ = (d : G) * v * v⁻¹ := by
              rw [hcommV v hv (d : G) (hV0le d.2)]
          _ = (d : G) := by group
      have hxv : x * v * x⁻¹ * v⁻¹ ∈ V₀ := by
        rw [hxeq, hvd]
        exact d.2
      have hxC : x ∈ C := by
        rw [hCdef]
        exact ⟨hxM.1, (Subgroup.centralizer_le_normalizer (V₀ : Set G)) hxM.2, hxv⟩
      refine MulAction.mem_orbit_iff.mpr ⟨⟨x, hxC⟩, ?_⟩
      show (⟨x, hxC⟩ : ↥C) • v = v * (d : G)
      change x * v * x⁻¹ = v * (d : G)
      exact hxeq
    let e : ↥(MulAction.orbit (↥C) v) ≃ ↥V₀ :=
      { toFun := fun x => ⟨v⁻¹ * (x : G), horbit_mem x⟩
        invFun := fun d => ⟨v * (d : G), horbit_mem' d⟩
        left_inv := fun x => by
          apply Subtype.ext
          show v * (v⁻¹ * (x : G)) = (x : G)
          group
        right_inv := fun d => by
          apply Subtype.ext
          show v⁻¹ * (v * (d : G)) = (d : G)
          group }
    have horbitCard : Nat.card (MulAction.orbit (↥C) v) = Nat.card ↥V₀ := Nat.card_congr e
    set K : Subgroup G := C ⊓ Subgroup.centralizer ({v} : Set G) with hKdef
    have hKC : K ≤ C := hKdef.le.trans inf_le_left
    have hKcent : K ≤ Subgroup.centralizer ({v} : Set G) := hKdef.le.trans inf_le_right
    have hstab : MulAction.stabilizer (↥C) v = K.subgroupOf C := by
      ext c
      show c ∈ MulAction.stabilizer (↥C) v ↔ (c : G) ∈ K
      rw [MulAction.mem_stabilizer_iff]
      constructor
      · intro hc
        refine ⟨c.2, ?_⟩
        change ∀ y ∈ ({v} : Set G), y * (c : G) = (c : G) * y
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have h1 : (c : G) * v * (c : G)⁻¹ = v := by
          have h2 : (c : ↥C) • v = v := hc
          change (c : G) * v * (c : G)⁻¹ = v at h2
          exact h2
        calc v * (c : G) = ((c : G) * v * (c : G)⁻¹) * (c : G) := by rw [h1]
          _ = (c : G) * v := by group
      · rintro ⟨-, hcv⟩
        change ∀ y ∈ ({v} : Set G), y * (c : G) = (c : G) * y at hcv
        have hcomm : (c : G) * v = v * (c : G) := (hcv v (Set.mem_singleton v)).symm
        show (c : ↥C) • v = v
        change (c : G) * v * (c : G)⁻¹ = v
        rw [hcomm]
        group
    have hidx : (K.subgroupOf C).index = Nat.card ↥V₀ := by
      have horbitIdx : Nat.card (MulAction.orbit (↥C) v) =
          (MulAction.stabilizer (↥C) v).index := by
        calc Nat.card (MulAction.orbit (↥C) v) =
              Nat.card (↥C ⧸ MulAction.stabilizer (↥C) v) :=
              Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥C) v)
          _ = (MulAction.stabilizer (↥C) v).index :=
              (MulAction.stabilizer (↥C) v).index_eq_card.symm
      rw [← hstab, ← horbitIdx]
      exact horbitCard
    have h5not : ¬ 5 ∣ K.relIndex C := by
      have hKrel : K.relIndex C = (K.subgroupOf C).index := rfl
      have hcardV0 : Nat.card ↥V₀ = 2 ^ mSub V₀ := by
        exact card_eq_two_pow_mSub (IsElemAbelian.isPGroup hVE)
      rw [hKrel, hidx, hcardV0]
      intro h
      have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at h52
    obtain ⟨R⟩ := Sylow.nonempty (p := 5) (G := ↥K)
    let P : Subgroup G := (R : Subgroup ↥K).map K.subtype
    have hPK : P ≤ K := Subgroup.map_subtype_le _
    have hPp : IsPGroup 5 P := R.isPGroup'.map K.subtype
    have hPKrel : ¬ 5 ∣ P.relIndex K := by
      have h : IsSylowOf 5 P K := ⟨R, rfl⟩
      exact (isSylowOf_iff.mp h).2.2
    have hPsy : IsSylowOf 5 P C := by
      refine isSylowOf_iff.mpr ⟨hPK.trans hKC, hPp, ?_⟩
      rw [← Subgroup.relIndex_mul_relIndex P K C hPK hKC]
      intro h
      rcases Nat.prime_five.dvd_mul.mp h with h' | h'
      · exact hPKrel h'
      · exact h5not h'
    obtain ⟨Q, hQ⟩ := hPsy.exists_sylow_eq_subgroupOf
    refine ⟨Q, ?_⟩
    rw [hQ, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans (hPK.trans hKcent)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
