module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem16D

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem three_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11)
    (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    conjClosure V (hCh611 T) ⊓ centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V) =
      conjClosure V (hCh611 T) ⊓ centralizerMod (zCh611 T) (hCh611 T) (uCh611 T L V) := by
  obtain ⟨-, hZZU, -, -, -, -, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hle := h.centralizerMod_K_le_ch615 h331 h432 h512 h614 h615 h6210 h6211 h6212 hlt
  apply le_antisymm
  · rintro k ⟨hkK, hkC⟩
    exact ⟨hkK, hle (mem_centralizerMod.mpr ⟨hkK, (mem_centralizerMod.mp hkC).2.1,
      (mem_centralizerMod.mp hkC).2.2⟩)⟩
  · rintro k ⟨hkK, hkC⟩
    obtain ⟨hkH, -, hkU⟩ := mem_centralizerMod.mp hkC
    exact ⟨hkK, mem_centralizerMod.mpr ⟨hkH, hCh611_le_normalizer_centerOf_ch615 T L V hkH,
      fun u hu => hZZU (hkU u hu)⟩⟩

theorem U_le_CH_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) :
    uCh611 T L V ≤ centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V) := by
  obtain ⟨hcomm, hZZU, -, -, -, -, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  have hUH : uCh611 T L V ≤ hCh611 T := h.uCh611_le_h h331 h432 h512 h614 h615
  intro u hu
  refine mem_centralizerMod.mpr ⟨hUH hu, hCh611_le_normalizer_centerOf_ch615 T L V (hUH hu),
    fun u' hu' => ?_⟩
  have := hZZU (hcomm u hu u' hu')
  rwa [commutatorElement_def] at this

theorem le_normalizer_VU_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) {x : G}
    (hx : x ∈ centralizerMod (centralizerMod (centerOf (uCh611 T L V)) (hCh611 T) (uCh611 T L V))
      (hCh611 T) V) :
    x ∈ Subgroup.normalizer ((V ⊓ uCh611 T L V : Subgroup G) : Set G) := by
  set U := uCh611 T L V with hUdef
  set Z := zCh611 T with hZdef
  set H := hCh611 T with hHdef
  obtain ⟨hxH, -, hxV⟩ := mem_centralizerMod.mp hx
  obtain ⟨hcomm, -, -, -, -, -, -⟩ := h.ustruct_ch616 h331 h432 h512 h614 h615
  obtain ⟨-, -, -, -, hVUc⟩ := h6210 G T M L V h
  have h3 := h.three_ch616 h331 h432 h512 h614 h615 h6210 h6211 h6212 hlt
  have hle := h.le_commutator_sup_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt
  have hW : ⁅V, U⁆ ⊔ Z = V ⊓ U := le_antisymm (sup_le hVUc fun z hz =>
    ⟨((h.omega_le_ZS h331 h432 h512 h614 h615).trans inf_le_left) hz,
      (le_conjClosure (ch6ZS T L V) H) (h.omega_le_ZS h331 h432 h512 h614 h615 hz)⟩) hle
  have hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hCh611_le_normalizer_u T L V hxH) u).mp hu
  have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    rw [← (Subgroup.mem_centralizer_iff.mp hxH z hz), mul_inv_cancel_right]
  have hcC : ∀ w ∈ V, x * w * x⁻¹ * w⁻¹ ∈ centralizerMod Z H U := by
    intro w hw
    have hK : x * w * x⁻¹ * w⁻¹ ∈ conjClosure V H := by
      have hwK : w ∈ conjClosure V H := le_conjClosure V H hw
      exact (conjClosure V H).mul_mem (mem_conjClosure hxH hw) ((conjClosure V H).inv_mem hwK)
    have : x * w * x⁻¹ * w⁻¹ ∈ conjClosure V H ⊓ centralizerMod (centerOf U) H U := ⟨hK, hxV w hw⟩
    rw [h3] at this
    exact this.2
  refine mem_normalizer_of_forall_conj_mem_of_le fun e he => ?_
  rw [← hW] at he ⊢
  have hcl : ⁅V, U⁆ ⊔ Z ≤ (⁅V, U⁆ ⊔ Z).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le ((Subgroup.commutator_le).mpr fun w hw u hu => ?_) fun z hz => ?_
    · show x * ⁅w, u⁆ * x⁻¹ ∈ ⁅V, U⁆ ⊔ Z
      set c := x * w * x⁻¹ * w⁻¹ with hc
      obtain ⟨-, -, hcU⟩ := mem_centralizerMod.mp (hcC w hw)
      set u' := x * u * x⁻¹ with hu'
      have hu'U : u' ∈ U := hxU u hu
      have hwu' : ⁅w, u'⁆ ∈ U := (hVUc (Subgroup.commutator_mem_commutator hw hu'U)).2
      have hc1 := hcU _ hwu'
      have hc2 := hcU _ hu'U
      have e : x * ⁅w, u⁆ * x⁻¹ = ⁅w, u'⁆ * ((⁅w, u'⁆⁻¹ * (c * ⁅w, u'⁆ * c⁻¹ * ⁅w, u'⁆⁻¹) *
          ⁅w, u'⁆) * (c * u' * c⁻¹ * u'⁻¹)) := by
        rw [hc, hu']
        simp only [commutatorElement_def]
        group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hw hu'U))
        (Subgroup.mem_sup_right (Z.mul_mem ?_ hc2))
      have hcz : (c * ⁅w, u'⁆ * c⁻¹ * ⁅w, u'⁆⁻¹) * ⁅w, u'⁆ = ⁅w, u'⁆ * (c * ⁅w, u'⁆ * c⁻¹ *
          ⁅w, u'⁆⁻¹) := by
        exact Subgroup.mem_centralizer_iff.mp
          (h.uCh611_le_h h331 h432 h512 h614 h615 hwu') _ hc1
      have e2 : ⁅w, u'⁆⁻¹ * (c * ⁅w, u'⁆ * c⁻¹ * ⁅w, u'⁆⁻¹) * ⁅w, u'⁆ =
          c * ⁅w, u'⁆ * c⁻¹ * ⁅w, u'⁆⁻¹ := by
        rw [mul_assoc, hcz, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e2]
      exact hc1
    · show x * z * x⁻¹ ∈ ⁅V, U⁆ ⊔ Z
      rw [hxZ z hz]
      exact Subgroup.mem_sup_right hz
  exact hcl he

theorem five_sub_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h625 : Stmt6_2_5) (h626 : Stmt6_2_6)
    (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12)
    (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    hCh611 T ⊓ centralizerMod (centralizerMod (centerOf (uCh611 T L V)) (hCh611 T)
        (uCh611 T L V)) (hCh611 T) V =
      hCh611 T ⊓ Subgroup.normalizer
        (((V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V) : Subgroup G) : Set G) ∧
    hCh611 T ⊓ Subgroup.normalizer
        (((V ⊓ uCh611 T L V) ⊔ centerOf (uCh611 T L V) : Subgroup G) : Set G) = hCh611 T ⊓ M := by
  set U := uCh611 T L V with hUdef
  set ZU := centerOf U with hZUdef
  set H := hCh611 T with hHdef
  set P := (V ⊓ U) ⊔ ZU with hPdef
  obtain ⟨-, ⟨-, hNM, -⟩, -, -, -⟩ := h6210 G T M L V h
  obtain ⟨hHM, -, -, -⟩ := stmt6_2_9 h331 h432 h512 h614 h615 G T M L V h
  have hHM' : H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) := hHM
  have hNV : ∀ x ∈ H, x ∈ Subgroup.normalizer (V : Set G) →
      x ∈ Subgroup.normalizer (P : Set G) := by
    intro x hxH hxN
    have hxU := hCh611_le_normalizer_u T L V hxH
    have hxZU := hCh611_le_normalizer_centerOf_ch615 T L V hxH
    refine mem_normalizer_of_forall_conj_mem_of_le fun e he => ?_
    have hcl : P ≤ P.comap (MulAut.conj x).toMonoidHom := sup_le
      (fun a ha => Subgroup.mem_sup_left ⟨(Subgroup.mem_normalizer_iff.mp hxN a).mp ha.1,
        (Subgroup.mem_normalizer_iff.mp hxU a).mp ha.2⟩)
      (fun n hn => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hxZU n).mp hn))
    exact hcl he
  have hVUV : ∀ x ∈ H, x ∈ Subgroup.normalizer ((V ⊓ U : Subgroup G) : Set G) →
      x ∈ Subgroup.normalizer (V : Set G) := by
    intro x hxH hxN
    have h2 : (V ⊓ U).relIndex V = 2 := by
      have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
      have hVU8 : Nat.card ↥(V ⊓ U) = 8 := by
        have := (stmt6_2_14_of h6210 h6211 h6212 G T M L V h hlt).2
        rw [this]; norm_num
      have h1 := Subgroup.relIndex_mul_card (V ⊓ U) V
      rw [inf_of_le_left inf_le_left, hVU8, hV16] at h1
      omega
    have hle : V ⊓ U ≤ conjSubgroup V x := by
      intro a ha
      rw [mem_conjSubgroup_iff]
      exact ((Subgroup.mem_normalizer_iff.mp hxN a).mp ha).1
    have heq := (h625 G T M L V h).2.2.2.2.2.2 (V ⊓ U) inf_le_left h2 x hle
    refine mem_normalizer_of_forall_conj_mem_of_le fun a ha => ?_
    have : a ∈ conjSubgroup V x := heq.symm ▸ ha
    rwa [mem_conjSubgroup_iff] at this
  have hA : H ⊓ centralizerMod (centralizerMod ZU H U) H V ≤ H ⊓ M := fun x hx => by
    rw [hHM']
    exact ⟨hx.1, hVUV x hx.1
      (h.le_normalizer_VU_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hx.2)⟩
  have hB : H ⊓ M ≤ H ⊓ Subgroup.normalizer (P : Set G) := by
    rw [hHM']
    exact fun x hx => ⟨hx.1, hNV x hx.1 hx.2⟩
  have hC : H ⊓ Subgroup.normalizer (P : Set G) ≤
      H ⊓ centralizerMod (centralizerMod ZU H U) H V := fun x hx =>
    ⟨hx.1, h.mem_centralizerMod_of_normalizer_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211
      h6212 hlt hx.1 hx.2⟩
  exact ⟨le_antisymm (hA.trans hB) hC, le_antisymm (hC.trans hA) hB⟩

end Hyp6Sec2

end CFSG.Quasithin.H13
