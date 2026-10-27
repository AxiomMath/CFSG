module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Base

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem hXD : X ≤ normalizer ((L ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have hxL := Subgroup.mem_normalizer_iff.1 (h.hn hx)
  constructor
  · rintro ⟨hdL, hdC⟩
    exact ⟨(hxL d).1 hdL, C124.conj_mem_centralizer_of_le h.hXN hx hdC⟩
  · rintro ⟨hdL, hdC⟩
    refine ⟨(hxL d).2 hdL, ?_⟩
    have := C124.conj_mem_centralizer_of_le h.hXN (X.inv_mem hx) hdC
    simpa [mul_assoc] using this

theorem C_le_D_mul_T {c : G} (hc : c ∈ X ⊓ centralizer (V : Set G)) :
    ∃ d ∈ L ⊓ centralizer (V : Set G), ∃ t ∈ T, c = d * t := by
  obtain ⟨l, hl, t, ht, hct⟩ := h.hprod c hc.1
  have hLN : L ≤ normalizer (V : Set G) := h.hLX.trans h.hXN
  have hlN : l ∈ normalizer (V : Set G) := hLN hl
  have htN : t ∈ normalizer (V : Set G) := h.hXN (h.hT.1 ht)
  have hcN : c ∈ normalizer (V : Set G) := h.hXN hc.1
  have hstar : convI h.hVe ⟨l, hlN⟩ ∈ autI h.hVe T := by
    have h1 : convI h.hVe ⟨c, hcN⟩ = 1 := (convI_eq_one_iff h.hVe _).2 hc.2
    have h2 : (⟨c, hcN⟩ : ↥(normalizer (V : Set G))) = ⟨l, hlN⟩ * ⟨t, htN⟩ := Subtype.ext hct
    rw [h2, map_mul, mul_eq_one_iff_eq_inv] at h1
    rw [h1]
    exact (autI h.hVe T).inv_mem (convI_mem_autI h.hVe ht htN)
  have hSyl : IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal h.hT h.hLX h.hn
  have hSylI : IsSylowTwoOf (autI h.hVe (T ⊓ L)) (autI h.hVe L) :=
    B2F.isSylowTwoOf_autI h.hVe hLN hSyl
  have hSylT : IsSylowTwoOf (autI h.hVe T) (autI h.hVe X) :=
    B2F.isSylowTwoOf_autI h.hVe h.hXN h.hT
  have heq : autI h.hVe L ⊓ autI h.hVe T = autI h.hVe (T ⊓ L) :=
    IsSylowTwoOf.eq_of_le hSylI
      (le_inf (autI_mono h.hVe inf_le_right) (autI_mono h.hVe inf_le_left)) inf_le_left
      (hSylT.2.1.to_le inf_le_right)
  have hmem : convI h.hVe ⟨l, hlN⟩ ∈ autI h.hVe (T ⊓ L) := by
    rw [← heq]
    exact ⟨convI_mem_autI h.hVe hl hlN, hstar⟩
  obtain ⟨s, hsTL, hs⟩ := (mem_autI h.hVe).1 hmem
  have hd : convI h.hVe (⟨l, hlN⟩ * s⁻¹) = 1 := by
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  have hdC : l * (s : G)⁻¹ ∈ centralizer (V : Set G) :=
    (convI_eq_one_iff h.hVe (⟨l, hlN⟩ * s⁻¹)).1 hd
  refine ⟨l * (s : G)⁻¹, ⟨L.mul_mem hl (L.inv_mem hsTL.2), hdC⟩, (s : G) * t,
    T.mul_mem hsTL.1 ht, ?_⟩
  rw [hct]
  group

theorem D_le_of_maximal {M : Subgroup G} (hTM : T ≤ M) (hMX : M < X)
    (hmax : ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) :
    L ⊓ centralizer (V : Set G) ≤ M := by
  by_contra hD
  have hDX : L ⊓ centralizer (V : Set G) ≤ X := inf_le_left.trans h.hLX
  have hsup : M ⊔ (L ⊓ centralizer (V : Set G)) = X := by
    rcases hmax _ le_sup_left (sup_le hMX.le hDX) with h1 | h1
    · exact absurd (h1 ▸ (le_sup_right : _ ≤ M ⊔ (L ⊓ centralizer (V : Set G)))) hD
    · exact h1
  have hOLM : pCoreOf 2 L ≤ M := h.toBaum.hOL_le_Q.trans (h.hQT.trans hTM)
  have hLM : L ≤ M := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    set N : Subgroup ↥L := (M ⊓ L).subgroupOf L with hN
    have hNZ : N.map π ⊔ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hyX : (y : G) ∈ (↑(M ⊔ (L ⊓ centralizer (V : Set G))) : Set G) := by
        rw [hsup]
        exact h.hLX y.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right M _ (hMX.le.trans h.hXD)] at hyX
      obtain ⟨m, hm, d, hd, hmd⟩ := hyX
      have hdL : d ∈ L := hd.1
      have hmL : m ∈ L := by
        have : m = (y : G) * d⁻¹ := by rw [← hmd]; group
        rw [this]
        exact L.mul_mem y.2 (L.inv_mem hdL)
      have hdz : d ∈ A6.o2Z L := h.D_eq_o2Z ▸ hd
      obtain ⟨hdL', hdc⟩ := mem_o2Z_gc.1 hdz
      have hyy : y = (⟨m, hmL⟩ : ↥L) * ⟨d, hdL⟩ := Subtype.ext hmd.symm
      rw [hyy, QuotientGroup.mk_mul]
      exact Subgroup.mul_mem_sup ⟨⟨m, hmL⟩, Subgroup.mem_subgroupOf.2 ⟨hm, hmL⟩, rfl⟩ hdc
    have htop := eq_top_of_sup_le_center_gc h.hhat.1 le_rfl hNZ
    intro l hl
    have hq : π ⟨l, hl⟩ ∈ N.map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnπ⟩ := hq
    have hnl : (n : G) ∈ M := (Subgroup.mem_subgroupOf.1 hn).1
    have hk : n⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnπ
      exact hnπ
    have hk' : ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ pCoreOf 2 L := coe_mem_pCoreOf_iff.2 hk
    have hl' : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by
      simp
    rw [hl']
    exact M.mul_mem hnl (hOLM hk')
  have hXM : X ≤ M := by
    intro x hx
    obtain ⟨l, hl, t, ht, rfl⟩ := h.hprod x hx
    exact M.mul_mem (hLM hl) (hTM ht)
  exact hMX.not_ge hXM

theorem C_le_of_maximal {M : Subgroup G} (hTM : T ≤ M) (hMX : M < X)
    (hmax : ∀ H : Subgroup G, M ≤ H → H ≤ X → H = M ∨ H = X) :
    X ⊓ centralizer (V : Set G) ≤ M := by
  intro c hc
  obtain ⟨d, hd, t, ht, rfl⟩ := h.C_le_D_mul_T hc
  exact M.mul_mem (h.D_le_of_maximal hTM hMX hmax hd) (hTM ht)

end H6Ctx

end CFSG.Quasithin.H13.U3.GC137
