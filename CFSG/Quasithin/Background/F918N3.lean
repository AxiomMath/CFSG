module

public import CFSG.Quasithin.EmptyFaithful.S1417Blocks
public import CFSG.Quasithin.Background.F918N1
public import CFSG.Quasithin.Background.F918N2
public import CFSG.Quasithin.Background.F918N4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix commutatorElement

section Generic

private theorem n3_commutator_central {G : Type*} [Group G] {H : Subgroup G} {z a b : G}
    (hz : ∀ y ∈ H, z * y = y * z) (ha : a ∈ H) (hb : b ∈ H) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h1 := hz (a * b * a⁻¹) (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha))
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * z * z⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

variable {W : Type} [CommGroup W]

private theorem n3_mem_stabSub_of_map_eq {U : Subgroup W} {g : MulAut W}
    (h : U.map g.toMonoidHom = U) : g ∈ stabSub U :=
  CFSG.Quasithin.S1417.mem_stabSub_of_map_eq h

private theorem n3_mem_stabSub_sup {A B : Subgroup W} {g : MulAut W} (hA : g ∈ stabSub A)
    (hB : g ∈ stabSub B) : g ∈ stabSub (A ⊔ B) := by
  apply n3_mem_stabSub_of_map_eq
  rw [Subgroup.map_sup, map_eq_of_mem_stabSub hA, map_eq_of_mem_stabSub hB]

private theorem n3_map_le_of_le_sup {X : Subgroup (MulAut W)} {V C : Subgroup W}
    (hcomm : commSub V X = V) (hCf : C ≤ fixV X) {t : MulAut W}
    (htN : t ∈ Subgroup.normalizer (X : Set (MulAut W))) (hle : V.map t.toMonoidHom ≤ V ⊔ C) :
    V.map t.toMonoidHom ≤ V := by
  conv_lhs => rw [← hcomm]
  rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hv, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  have hx' : t * x * t⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp htN x).mp hx
  obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.1 (hle ⟨v, hv, rfl⟩)
  have hcx : (t * x * t⁻¹) c = c := hCf hc _ hx'
  have h1 : t (x v) = (t * x * t⁻¹) (t v) := by simp [MulAut.mul_apply]
  have e : t.toMonoidHom (x v * v⁻¹) = (t * x * t⁻¹) a * a⁻¹ := by
    have h2 : t v = a * c := hac.symm
    rw [MulEquiv.coe_toMonoidHom, map_mul, map_inv, h1, h2, map_mul (t * x * t⁻¹), hcx, mul_inv_rev,
      mul_assoc, mul_inv_cancel_left]
  rw [e, ← hcomm]
  exact Subgroup.subset_closure ⟨_, hx', a, ha, rfl⟩

end Generic

section Section

variable {W : Type} [CommGroup W]

private theorem n3_mk_mem_sec35Img {VT C V : Subgroup W} (hCV : C ≤ VT) (u : ↥VT) :
    (QuotientGroup.mk u : Sec VT C) ∈ sec35Img VT C V ↔ (u : W) ∈ V ⊔ C := by
  unfold sec35Img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hau⟩
    have h1 : a * u⁻¹ ∈ C.subgroupOf VT := (mk_eq_mk_iff a u).1 hau
    rw [Subgroup.mem_subgroupOf] at h1 ha
    have e : (u : W) = (a : W) * ((a * u⁻¹ : ↥VT) : W)⁻¹ := by simp
    rw [e]
    exact Subgroup.mul_mem_sup ha (C.inv_mem h1)
  · intro hu
    obtain ⟨v, hv, c, hc, hvc⟩ := Subgroup.mem_sup.1 hu
    have ev : v = (u : W) * c⁻¹ := by rw [← hvc, mul_inv_cancel_right]
    have hvT : v ∈ VT := by
      rw [ev]
      exact VT.mul_mem u.2 (VT.inv_mem (hCV hc))
    refine ⟨⟨v, hvT⟩, hv, ?_⟩
    show (QuotientGroup.mk _ : Sec VT C) = QuotientGroup.mk u
    rw [mk_eq_mk_iff, Subgroup.mem_subgroupOf]
    have e : ((⟨v, hvT⟩ * u⁻¹ : ↥VT) : W) = c⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ev, mul_inv_cancel_comm]
    rw [e]
    exact C.inv_mem hc

private theorem n3_sec35Img_sup {VT C V V₂ : Subgroup W} (hV : V ≤ VT) (hV₂ : V₂ ≤ VT) :
    sec35Img VT C V ⊔ sec35Img VT C V₂ = sec35Img VT C (V ⊔ V₂) := by
  unfold sec35Img
  rw [Subgroup.subgroupOf_sup hV hV₂, Subgroup.map_sup]

private theorem n3_map_sec35Img {VT C V : Subgroup W} (hV : V ≤ VT) (g : stabSub VT)
    (hg : resHom VT g ∈ stabSub (C.subgroupOf VT)) :
    (sec35Img VT C V).map (quotHom (C.subgroupOf VT) ⟨resHom VT g, hg⟩).toMonoidHom =
      sec35Img VT C (V.map (g : MulAut W).toMonoidHom) := by
  unfold sec35Img
  rw [Subgroup.map_map]
  have e1 : (quotHom (C.subgroupOf VT) ⟨resHom VT g, hg⟩).toMonoidHom.comp
      (QuotientGroup.mk' (C.subgroupOf VT)) =
      (QuotientGroup.mk' (C.subgroupOf VT)).comp (resHom VT g).toMonoidHom := by
    ext u
    rfl
  rw [e1, ← Subgroup.map_map]
  congr 1
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨v, hv, hvu⟩
    exact ⟨⟨v, hV hv⟩, hv, Subtype.ext hvu⟩

private theorem n3_quotHom_inv_mul {VT : Subgroup W} {C' : Subgroup ↥VT} (g h : stabSub VT)
    (hg : resHom VT g ∈ stabSub C') (hh : resHom VT h ∈ stabSub C')
    (hgh : resHom VT (g⁻¹ * h) ∈ stabSub C') :
    (quotHom C' ⟨resHom VT g, hg⟩)⁻¹ * quotHom C' ⟨resHom VT h, hh⟩ =
      quotHom C' ⟨resHom VT (g⁻¹ * h), hgh⟩ := by
  rw [← map_inv (quotHom C'), ← map_mul (quotHom C')]
  congr 1

private theorem n3_mem_stab_sec_of {VT C V : Subgroup W} (hCV : C ≤ VT) (g : stabSub VT)
    (hg : resHom VT g ∈ stabSub (C.subgroupOf VT)) (hgV : (g : MulAut W) ∈ stabSub V)
    (hgC : (g : MulAut W) ∈ stabSub C) :
    quotHom (C.subgroupOf VT) ⟨resHom VT g, hg⟩ ∈ stabSub (sec35Img VT C V) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
    rw [quotHom_mk, n3_mk_mem_sec35Img hCV, n3_mk_mem_sec35Img hCV]
    exact n3_mem_stabSub_sup hgV hgC u

private theorem n3_map_le_sup_of_mem_stab {VT C V : Subgroup W} (hCV : C ≤ VT) (hVT : V ≤ VT)
    (g : stabSub VT) (hg : resHom VT g ∈ stabSub (C.subgroupOf VT))
    (h : quotHom (C.subgroupOf VT) ⟨resHom VT g, hg⟩ ∈ stabSub (sec35Img VT C V)) :
    V.map (g : MulAut W).toMonoidHom ≤ V ⊔ C := by
  rintro _ ⟨v, hv, rfl⟩
  have h1 : (QuotientGroup.mk (⟨v, hVT hv⟩ : ↥VT) : Sec VT C) ∈ sec35Img VT C V :=
    (n3_mk_mem_sec35Img hCV _).2 (Subgroup.mem_sup_left hv)
  have h2 := (h _).2 h1
  rw [quotHom_mk, n3_mk_mem_sec35Img hCV] at h2
  exact h2

private theorem n3_isSumMod_of_isIntDirect {VT C V V₂ : Subgroup W} (hCV : C ≤ VT) (hV : V ≤ VT)
    (hV₂ : V₂ ≤ VT) (h : IsIntDirect (sec35Img VT C V) (sec35Img VT C V₂) ⊤) :
    IsSumMod C V V₂ VT := by
  obtain ⟨hsup, hinf⟩ := h
  rw [n3_sec35Img_sup hV hV₂] at hsup
  refine ⟨le_antisymm (fun w hw => ?_) (sup_le (sup_le hV hV₂) hCV), fun x hx => ?_⟩
  · have hmem : (QuotientGroup.mk (⟨w, hw⟩ : ↥VT) : Sec VT C) ∈ sec35Img VT C (V ⊔ V₂) := by
      rw [hsup]
      exact Subgroup.mem_top _
    exact (n3_mk_mem_sec35Img hCV _).1 hmem
  · have hxT : x ∈ VT := sup_le hV hCV hx.1
    have h1 := (n3_mk_mem_sec35Img (V := V) hCV ⟨x, hxT⟩).2 hx.1
    have h2 := (n3_mk_mem_sec35Img (V := V₂) hCV ⟨x, hxT⟩).2 hx.2
    have h3 : (QuotientGroup.mk (⟨x, hxT⟩ : ↥VT) : Sec VT C) ∈
        sec35Img VT C V ⊓ sec35Img VT C V₂ := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
    exact h3

end Section

section Dictionary

variable {W : Type} [CommGroup W] [Finite W]

theorem z35_of_d3Std {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g) :
    Z35 (autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp)) (autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp))
      (autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)) (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V) :=
  ⟨z35g_exp hD, z35g_qsqtk hD, z35g_sylow hD, z35g_quasi hD hlt hC, z35g_Mp_eq hD, z35g_comm_conj hD,
    z35m_irr hD, z35m_indep hD, z35m_gen hD, z35m_fix hD, z35m_homog hD, z35g_o2 hD, z35g_qhat hD,
    z35m_nontriv hD hC, z35m_lt hD hlt⟩

end Dictionary

section D3

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem n3_L_le_Mp (hD : D3Std M Mp T L V) : L ≤ Mp := by
  rw [hD.hyp.Mp_eq]
  exact le_conjClosure L T

private theorem n3_T_le_normalizer (hD : D3Std M Mp T L V) :
    T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
  rw [hD.hyp.Mp_eq]
  exact le_normalizer_conjClosure L T

private theorem n3_dict (hD : D3Std M Mp T L V) (g : stabSub (orbSup T V))
    (hgT : (g : MulAut W) ∈ T)
    (hg : resHom (orbSup T V) g ∈ stabSub ((orbSup T V ⊓ fixV Mp).subgroupOf (orbSup T V))) :
    quotHom ((orbSup T V ⊓ fixV Mp).subgroupOf (orbSup T V)) ⟨resHom (orbSup T V) g, hg⟩ ∈
        stabSub (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V) ↔
      (g : MulAut W) ∈ stabSub V := by
  constructor
  · intro h
    have hle := n3_map_le_sup_of_mem_stab inf_le_left (le_orbSup T V) g hg h
    have hcomm : commSub V Mp = V := (mem_irrPlus_top_iff.mp hD.hyp.irr).2.1
    have hle' := n3_map_le_of_le_sup hcomm inf_le_right (n3_T_le_normalizer hD hgT) hle
    have heq : V.map (g : MulAut W).toMonoidHom = V :=
      Subgroup.eq_of_le_of_card_ge hle'
        (Subgroup.card_map_of_injective (g : MulAut W).injective).ge
    exact n3_mem_stabSub_of_map_eq heq
  · intro hgV
    exact n3_mem_stab_sec_of inf_le_left g hg hgV
      ((le_sup_right.trans ((n1_sup_le_stabSub_sec hD.hyp).trans inf_le_right)) hgT)

theorem d35_one_of_sec (hD : D3Std M Mp T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g)
    (h : autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) = autSec L (orbSup T V) (orbSup T V ⊓ fixV Mp)) :
    Mp = L := by
  have _ := hlt
  have hLMp := n3_L_le_Mp hD
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hMpS : Mp ≤ stabSub (orbSup T V) := le_sup_left.trans (hG.trans inf_le_left)
  have hMpC : Mp ≤ stabSub (orbSup T V ⊓ fixV Mp) := le_sup_left.trans (hG.trans inf_le_right)
  have hdec : ∀ x ∈ Mp, ∃ l ∈ L, ∀ y ∈ Mp, x * l⁻¹ * y = y * (x * l⁻¹) := by
    intro x hx
    have hxC : resHom (orbSup T V) ⟨x, hMpS hx⟩ ∈
        stabSub ((orbSup T V ⊓ fixV Mp).subgroupOf (orbSup T V)) :=
      autSub_le_stabSub_subgroupOf hMpC (mem_autSub.mpr ⟨⟨x, hMpS hx⟩, hx, rfl⟩)
    have hmem : quotHom _ ⟨resHom (orbSup T V) ⟨x, hMpS hx⟩, hxC⟩ ∈
        autSec Mp (orbSup T V) (orbSup T V ⊓ fixV Mp) :=
      B1Red.mem_autSec_iff.mpr ⟨⟨x, hMpS hx⟩, hx, hxC, rfl⟩
    rw [h] at hmem
    obtain ⟨g, hgL, hgC, hgx⟩ := B1Red.mem_autSec_iff.mp hmem
    have hk : x * (g : MulAut W)⁻¹ ∈ Mp := Mp.mul_mem hx (Mp.inv_mem (hLMp hgL))
    have hkc : x * (g : MulAut W)⁻¹ ∈ centSec (orbSup T V) (orbSup T V ⊓ fixV Mp) := by
      refine mem_centSec.mpr ⟨(stabSub _).mul_mem (hMpS hx) ((stabSub _).inv_mem g.2), fun w hw => ?_⟩
      have hw' : (g : MulAut W)⁻¹ w ∈ orbSup T V := ((stabSub _).inv_mem g.2 w).2 hw
      have h1 := congrArg (fun φ : MulAut (Sec (orbSup T V) (orbSup T V ⊓ fixV Mp)) =>
        φ (QuotientGroup.mk (⟨(g : MulAut W)⁻¹ w, hw'⟩ : ↥(orbSup T V)))) hgx
      simp only [quotHom_mk] at h1
      have h2 := (mk_eq_mk_iff _ _).1 h1
      rw [Subgroup.mem_subgroupOf] at h2
      have h3 : (g : MulAut W) ((g : MulAut W)⁻¹ w) * (x ((g : MulAut W)⁻¹ w))⁻¹ ∈
          orbSup T V ⊓ fixV Mp := h2
      rw [MulAut.apply_inv_self] at h3
      have e : (x * (g : MulAut W)⁻¹) w * w⁻¹ = (w * (x ((g : MulAut W)⁻¹ w))⁻¹)⁻¹ := by
        rw [MulAut.mul_apply, mul_inv_rev, inv_inv]
      rw [e]
      exact Subgroup.inv_mem _ h3
    have htr := n1_inf_centSec_le_centSub hD ⟨(le_sup_left : Mp ≤ Mp ⊔ T) hk, hkc⟩
    exact ⟨g, hgL, hC _ hk fun v hv => htr v (le_orbSup T V hv)⟩
  have hcomm : ⁅Mp, Mp⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨l₁, hl₁, hz₁⟩ := hdec a ha
    obtain ⟨l₂, hl₂, hz₂⟩ := hdec b hb
    have hb' : b * l₂⁻¹ * l₂ ∈ Mp := by rw [inv_mul_cancel_right]; exact hb
    rw [← inv_mul_cancel_right a l₁, ← inv_mul_cancel_right b l₂,
      n3_commutator_central hz₁ (hLMp hl₁) hb', ← commutatorElement_inv,
      n3_commutator_central hz₂ (hLMp hl₂) (hLMp hl₁), commutatorElement_def]
    exact L.inv_mem (L.mul_mem (L.mul_mem (L.mul_mem hl₂ hl₁) (L.inv_mem hl₂)) (L.inv_mem hl₁))
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hD.hyp.comp
  have hMpc : Mp ≤ ⁅Mp, Mp⁆ := by
    conv_lhs => rw [hD.hyp.Mp_eq]
    refine conjClosure_le fun t ht l hl => ?_
    have hmap : L.map (MulAut.conj t).toMonoidHom ≤ Mp := by
      rintro _ ⟨l', hl', rfl⟩
      rw [hD.hyp.Mp_eq]
      exact mem_conjClosure ht hl'
    have h1 : (MulAut.conj t).toMonoidHom l ∈ ⁅L, L⁆.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (hperf.symm ▸ hl)
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono hmap hmap h1
  exact le_antisymm (hMpc.trans hcomm) hLMp

theorem d35_four_of_sec (hD : D3Std M Mp T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ Mp, (∀ v ∈ V, g v = v) → ∀ x ∈ Mp, g * x = x * g) (hMpL : Mp = L)
    (h4 : (∃ t ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
        t ∉ stabSub (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V)) ∧
      ∀ t ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
        t ∉ stabSub (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V) →
        (∀ s ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp),
          s ∈ stabSub (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V) ∨
            t⁻¹ * s ∈ stabSub (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V)) ∧
          IsIntDirect (sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V)
            ((sec35Img (orbSup T V) (orbSup T V ⊓ fixV Mp) V).map t.toMonoidHom) ⊤) :
    (∃ t ∈ T, t ∉ stabSub V) ∧
      (∀ t ∈ T, t ∉ stabSub V →
        (∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V) ∧
          IsSumMod (orbSup T V ⊓ fixV L) V (V.map t.toMonoidHom) (orbSup T V)) := by
  have _ := hlt
  have _ := hC
  have hTS : T ≤ stabSub (orbSup T V) := le_stabSub_orbSup T V
  have hTC : T ≤ stabSub (orbSup T V ⊓ fixV Mp) :=
    le_sup_right.trans ((n1_sup_le_stabSub_sec hD.hyp).trans inf_le_right)
  have hres : ∀ g : stabSub (orbSup T V), (g : MulAut W) ∈ T →
      resHom (orbSup T V) g ∈ stabSub ((orbSup T V ⊓ fixV Mp).subgroupOf (orbSup T V)) :=
    fun g hg => autSub_le_stabSub_subgroupOf hTC (mem_autSub.mpr ⟨g, hg, rfl⟩)
  obtain ⟨h4a, h4b⟩ := h4
  refine ⟨?_, fun t ht htV => ?_⟩
  · obtain ⟨φ, hφ, hφV⟩ := h4a
    obtain ⟨g, hgT, hgC, rfl⟩ := B1Red.mem_autSec_iff.mp hφ
    exact ⟨g, hgT, fun hgV => hφV ((n3_dict hD g hgT hgC).2 hgV)⟩
  · let g : stabSub (orbSup T V) := ⟨t, hTS ht⟩
    have hgC := hres g ht
    have hφ : quotHom _ ⟨resHom _ g, hgC⟩ ∈ autSec T (orbSup T V) (orbSup T V ⊓ fixV Mp) :=
      B1Red.mem_autSec_iff.mpr ⟨g, ht, hgC, rfl⟩
    obtain ⟨h1, h2⟩ := h4b _ hφ fun h => htV ((n3_dict hD g ht hgC).1 h)
    refine ⟨fun s hs => ?_, ?_⟩
    · let g' : stabSub (orbSup T V) := ⟨s, hTS hs⟩
      have hg'C := hres g' hs
      rcases h1 _ (B1Red.mem_autSec_iff.mpr ⟨g', hs, hg'C, rfl⟩) with h | h
      · exact Or.inl ((n3_dict hD g' hs hg'C).1 h)
      · have hT' : ((g⁻¹ * g' : stabSub (orbSup T V)) : MulAut W) ∈ T := T.mul_mem (T.inv_mem ht) hs
        have hC' := hres (g⁻¹ * g') hT'
        rw [n3_quotHom_inv_mul g g' hgC hg'C hC'] at h
        exact Or.inr ((n3_dict hD (g⁻¹ * g') hT' hC').1 h)
    · rw [← hMpL]
      rw [n3_map_sec35Img (le_orbSup T V) g hgC] at h2
      exact n3_isSumMod_of_isIntDirect inf_le_left (le_orbSup T V) (map_le_orbSup ht) h2

end D3

theorem d35_of_z35Main (hmain : Z35Main) (hA21 : AsA21SQTKSection) (hNC : AsA36NoOddCover) : D35 := by
  intro W _ _ M Mp T L V hD hlt hC
  obtain ⟨h1, h2, h3, h5⟩ := hmain _ _ _ _ _ (z35_of_d3Std hD hlt hC)
  have hMpL := d35_one_of_sec hD hlt hC h1
  have h4 := d35_four_of_sec hD hlt hC hMpL ⟨h2, h3⟩
  exact ⟨hMpL, h4.1, h4.2,
    d35_five_of_sec hD hMpL (z35m_fix hD) (d35_faithful hA21 hNC hD hlt hC hMpL h5) h5⟩

end CFSG.Quasithin
