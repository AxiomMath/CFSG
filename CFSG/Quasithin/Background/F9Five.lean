module

public import CFSG.Quasithin.Background.F9Section

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

section Fin

variable [Finite G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem F95_1 (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H) :
    Vp = V ⊓ pCoreOf 2 H ∧
      Nat.card (autOn (tildeOf V₁ V) (tildeOf V₁ (conjClosure Vp H))) = 2 := by
  have hle : Vp ≤ V ⊓ pCoreOf 2 H :=
    le_inf h.Vp_le_V ((le_conjClosure Vp H).trans h.conjClosure_Vp_le_pCoreOf)
  have hmul := Subgroup.relIndex_mul_relIndex Vp (V ⊓ pCoreOf 2 H) V hle inf_le_left
  rw [hidx] at hmul
  have hne : (V ⊓ pCoreOf 2 H).relIndex V ≠ 1 := fun h1 =>
    hV (inf_le_right.trans' (Subgroup.relIndex_eq_one.mp h1))
  have hdvd : (V ⊓ pCoreOf 2 H).relIndex V ∣ 2 := Dvd.intro_left _ hmul
  have h2 : (V ⊓ pCoreOf 2 H).relIndex V = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
  have h3 : Vp.relIndex (V ⊓ pCoreOf 2 H) = 1 := by
    rw [h2] at hmul
    omega
  have heq : Vp = V ⊓ pCoreOf 2 H := le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)
  refine ⟨heq, ?_⟩
  rw [h.card_autOn_tilde h.V_le_H]
  exact h2

theorem F95_comm_mem (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {u q v : G} (hu : u ∈ conjClosure Vp H) (hq : q ∈ pCoreOf 2 H)
    (hv : v ∈ V) : u * (q * v) * u⁻¹ * (q * v)⁻¹ ∈ Vp := by
  obtain ⟨hVp, -⟩ := h.F95_1 hidx hV
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le h.sylow_H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have huv : u * v * u⁻¹ * v⁻¹ ∈ Vp := by
    rw [hVp]
    refine ⟨?_, ?_⟩
    · have h1 : u * v * u⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (h.T_normalizes_V (hQT (hUQ hu))) v).mp hv
      exact V.mul_mem h1 (V.inv_mem hv)
    · have h2 : v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hQn (h.V_le_H hv)) u⁻¹).mp
          ((pCoreOf 2 H).inv_mem (hUQ hu))
      have e : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 H).mul_mem (hUQ hu) h2
  have hqw : q * (u * v * u⁻¹ * v⁻¹) * q⁻¹ ∈ Vp := by
    have hw : u * v * u⁻¹ * v⁻¹ ∈ conjClosure Vp H := by
      have : Vp ≤ conjClosure Vp H := le_conjClosure Vp H
      exact this huv
    have h1 := h.commutator_conjClosure_le _ hw q hq
    have e : q * (u * v * u⁻¹ * v⁻¹) * q⁻¹ =
        ((u * v * u⁻¹ * v⁻¹) * q * (u * v * u⁻¹ * v⁻¹)⁻¹ * q⁻¹)⁻¹ * (u * v * u⁻¹ * v⁻¹) := by
      group
    rw [e]
    exact Vp.mul_mem (Vp.inv_mem (h.V₁_le_Vp h1)) huv
  have huq : u * q * u⁻¹ * q⁻¹ ∈ Vp := h.V₁_le_Vp (h.commutator_conjClosure_le u hu q hq)
  have e : u * (q * v) * u⁻¹ * (q * v)⁻¹ =
      (u * q * u⁻¹ * q⁻¹) * (q * (u * v * u⁻¹ * v⁻¹) * q⁻¹) := by group
  rw [e]
  exact Vp.mul_mem huq hqw

theorem F95_2_aux (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) :
    ⁅conjClosure Vp H, V⁆ ⊔ V₁ = Vp ∧ ⁅conjClosure Vp H, V⁆ ≤ Vp ∧
      ⁅pCoreOf 2 H, V⁆ ≤ Vp := by
  obtain ⟨hVp, -⟩ := h.F95_1 hidx hV
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le h.sylow_H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hQV : ⁅pCoreOf 2 H, V⁆ ≤ Vp := by
    refine Subgroup.commutator_le.mpr fun q hq v hv => ?_
    rw [hVp]
    refine ⟨?_, ?_⟩
    · have h1 : q * v * q⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (h.T_normalizes_V (hQT hq)) v).mp hv
      exact V.mul_mem h1 (V.inv_mem hv)
    · have h2 : v * q⁻¹ * v⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hQn (h.V_le_H hv)) q⁻¹).mp ((pCoreOf 2 H).inv_mem hq)
      have e : q * v * q⁻¹ * v⁻¹ = q * (v * q⁻¹ * v⁻¹) := by group
      show q * v * q⁻¹ * v⁻¹ ∈ pCoreOf 2 H
      rw [e]
      exact (pCoreOf 2 H).mul_mem hq h2
  have hUV : ⁅conjClosure Vp H, V⁆ ≤ Vp := (Subgroup.commutator_mono hUQ le_rfl).trans hQV
  have hMle : ⁅conjClosure Vp H, V⁆ ⊔ V₁ ≤ Vp := sup_le hUV h.V₁_le_Vp
  have hXU : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    h.L₁T_le_H.trans (le_normalizer_conjClosure Vp H)
  have hXV₁ : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
    h.L₁T_le_H.trans h.H_normalizes_V₁
  have hMn : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer
      ((⁅conjClosure Vp H, V⁆ ⊔ V₁ : Subgroup G) : Set G) :=
    (le_inf (F9.le_normalizer_commutator_of_le hXU h.L₁T_normalizes_V) hXV₁).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hirr := h.irred _ le_sup_right hMle hMn
  refine ⟨hirr.resolve_left fun hM => hV ?_, hUV, hQV⟩
  intro v hv
  rw [h.pCoreOf_eq_centralizerMod]
  refine ⟨h.V_le_H hv, h.V_le_normalizer_V₁ hv, fun u hu => ?_⟩
  have h1 : u * v * u⁻¹ * v⁻¹ ∈ ⁅conjClosure Vp H, V⁆ ⊔ V₁ :=
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hv)
  rw [hM] at h1
  have := V₁.inv_mem h1
  have e : (u * v * u⁻¹ * v⁻¹)⁻¹ = v * u * v⁻¹ * u⁻¹ := by group
  rwa [e] at this

theorem F95_2 (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H) :
    tildeOf V₁ ⁅pCoreOf 2 H, V⁆ = tildeOf V₁ Vp ∧
      tildeOf V₁ ⁅conjClosure Vp H, V⁆ = tildeOf V₁ Vp := by
  obtain ⟨hM, hUV, hQV⟩ := h.F95_2_aux hidx hV
  have hUQ := h.conjClosure_Vp_le_pCoreOf
  have hN : ⁅conjClosure Vp H, V⁆ ≤ Subgroup.normalizer (V₁ : Set G) :=
    hUV.trans (h.Vp_le_T.trans h.T_normalizes_V₁)
  have h1 : tildeOf V₁ ⁅conjClosure Vp H, V⁆ = tildeOf V₁ Vp := by
    have e := tildeOf_sup_self hN
    rw [hM] at e
    exact e.symm
  refine ⟨le_antisymm (secImg_mono hQV) ?_, h1⟩
  rw [← h1]
  exact secImg_mono (Subgroup.commutator_mono hUQ le_rfl)

theorem F95_3 (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H) :
    centralizerMod (pCoreOf 2 H) H V = H ⊓ Subgroup.normalizer (Vp : Set G) ∧
      H ⊓ Subgroup.normalizer (Vp : Set G) = H ⊓ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hM, hUV, hQV⟩ := h.F95_2_aux hidx hV
  obtain ⟨hVp, -⟩ := h.F95_1 hidx hV
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hi : centralizerMod (pCoreOf 2 H) H V ≤ H ⊓ Subgroup.normalizer (Vp : Set G) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    apply mem_normalizer_of_conjSub_eq
    have hle : conjSub x Vp ≤ Vp := by
      rw [← hM, conjSub_sup, ← conjSub_commutator,
        F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H hx.1),
        F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ hx.1)]
      refine sup_le ?_ le_sup_right
      refine Subgroup.commutator_le.mpr fun u hu y hy => ?_
      rw [mem_conjSub] at hy
      have hvV := hy
      have e : y = (x * (x⁻¹ * y * x) * x⁻¹ * (x⁻¹ * y * x)⁻¹) * (x⁻¹ * y * x) := by group
      have hq : x * (x⁻¹ * y * x) * x⁻¹ * (x⁻¹ * y * x)⁻¹ ∈ pCoreOf 2 H := hx.2.2 _ hvV
      have := h.F95_comm_mem hidx hV hu hq hvV
      rw [← e] at this
      rw [← hM] at this
      exact this
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hiii : H ⊓ Subgroup.normalizer (V : Set G) ≤ centralizerMod (pCoreOf 2 H) H V := by
    rintro x ⟨hxH, hxV⟩
    refine ⟨hxH, hQn hxH, fun v hv => ?_⟩
    have hw : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
    by_cases hvQ : v ∈ pCoreOf 2 H
    · have hwQ : x * v * x⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp (hQn hxH) v).mp hvQ
      exact (pCoreOf 2 H).mul_mem hwQ ((pCoreOf 2 H).inv_mem hvQ)
    · obtain ⟨a, haV, ha⟩ := Subgroup.relIndex_dvd_two_iff.mp (hidx ▸ dvd_refl (2 : ℕ) :
        Vp.relIndex V ∣ 2)
      have hvp : v * a ∈ Vp := (ha v hv).resolve_right fun hvp => hvQ (by
        rw [hVp] at hvp; exact hvp.2)
      have hwp : (x * v * x⁻¹) * a ∈ Vp := (ha _ hw).resolve_right fun hwp => hvQ (by
        have hwQ : x * v * x⁻¹ ∈ pCoreOf 2 H := by rw [hVp] at hwp; exact hwp.2
        have := (Subgroup.mem_normalizer_iff.mp (hQn (H.inv_mem hxH)) _).mp hwQ
        simpa [mul_assoc] using this)
      have hprod : (x * v * x⁻¹) * v⁻¹ ∈ Vp := by
        have := Vp.mul_mem hwp (Vp.inv_mem hvp)
        have e : (x * v * x⁻¹ * a) * (v * a)⁻¹ = x * v * x⁻¹ * v⁻¹ := by group
        rwa [e] at this
      rw [hVp] at hprod
      exact hprod.2
  have hii : H ⊓ Subgroup.normalizer (Vp : Set G) ≤ H ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf inf_le_left h.normalizer_le
  exact ⟨le_antisymm hi (hii.trans hiii), le_antisymm hii (hiii.trans hi)⟩

theorem F95_4 (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2) (hV : ¬ V ≤ pCoreOf 2 H)
    {k : G} (hk : k ∈ H) (hVk : conjSub k⁻¹ V ≤ pCoreOf 2 H ⊔ V) : conjSub k⁻¹ V = V := by
  obtain ⟨hM, hUV, hQV⟩ := h.F95_2_aux hidx hV
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 H) V
    (h.V_le_H.trans hQn)
  have hle : conjSub k⁻¹ Vp ≤ Vp := by
    rw [← hM, conjSub_sup, ← conjSub_commutator,
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure Vp H (H.inv_mem hk)),
      F7.conjSub_eq_of_mem_normalizer (h.H_normalizes_V₁ (H.inv_mem hk))]
    refine sup_le ?_ le_sup_right
    refine Subgroup.commutator_le.mpr fun u hu y hy => ?_
    have hy' : y ∈ ((pCoreOf 2 H : Subgroup G) : Set G) * (V : Set G) := by
      rw [← hmul]; exact hVk hy
    obtain ⟨q, hq, v, hv, rfl⟩ := hy'
    have := h.F95_comm_mem hidx hV hu hq hv
    rw [← hM] at this
    exact this
  have heq : conjSub k⁻¹ Vp = Vp :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  have hkN : k⁻¹ ∈ H ⊓ Subgroup.normalizer (Vp : Set G) :=
    ⟨H.inv_mem hk, mem_normalizer_of_conjSub_eq heq⟩
  exact F7.conjSub_eq_of_mem_normalizer (h.normalizer_le hkN)

end HypF91

end Fin

end CFSG.Quasithin
