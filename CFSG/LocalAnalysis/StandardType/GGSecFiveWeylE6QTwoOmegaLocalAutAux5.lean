module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocalAutAux4

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

public theorem Ebar_isElemAbelian {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (hBs : IsElemAbelian 3 Bs)
    (hEbot : (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype = ⊥) :
    IsElemAbelian 3 (Ebar Bs L θ) := by
  have h1 : IsElemAbelian 3 (Bs ⊓ L) := hBs.mono (inf_le_left : Bs ⊓ L ≤ Bs)
  have h2 : CFSG.IsElementaryAbelian 3 ↥(Bs ⊓ L) :=
    (isElemAbelian_iff_isElementaryAbelian (p := 3) (E := Bs ⊓ L)).mp h1
  have hbij : Function.Bijective (qE Bs L θ) :=
    ⟨qE_injective Bs L θ hEbot, qE_surjective Bs L θ⟩
  exact (isElemAbelian_iff_isElementaryAbelian (p := 3) (E := Ebar Bs L θ)).mpr
    (CFSG.IsElementaryAbelian.of_mulEquiv (MulEquiv.ofBijective _ hbij) h2)

public theorem Ebar_card {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hEbot : (Bs ⊓ L) ⊓ (Subgroup.center L).map L.subtype = ⊥)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) :
    Nat.card ↥(Ebar Bs L θ) = 3 ^ 4 := by
  rw [← Nat.card_congr (Equiv.ofBijective (qE Bs L θ)
    ⟨qE_injective Bs L θ hEbot, qE_surjective Bs L θ⟩), hcardE]

public theorem exists_frameSignedDataRPlus {Bs L : Subgroup G} {x : G}
    (hK : Nat.card K = 2) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5)
    (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    ∃ Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ),
      (∀ g : OrthRest.RPlus K 4, g ∈ Subgroup.normalizer (Ebar Bs L θ : Set _) →
        ∀ w : MulAut (Fin 4 → Multiplicative (ZMod 3)),
          (∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ = (Θ (w f) : OrthRest.RPlus K 4)) →
            IsSignedPerm ⇑w) ∧
      (∀ (a : Fin 4) (g : OrthRest.RPlus K 4),
        (∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ = (Θ (sgnAut a f) : OrthRest.RPlus K 4)) →
          False) ∧
      (∀ y : OmPlusIdx 4, ∃ g ∈ Subgroup.normalizer (Ebar Bs L θ : Set _),
        ∀ f, g * (Θ f : OrthRest.RPlus K 4) * g⁻¹ = (Θ (omPlusRefl 3 y f) : OrthRest.RPlus K 4)) := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  obtain ⟨-, -, -, hEbot, -⟩ := bstar_basic hZ2 hBs hx1 hBL
  obtain ⟨Θ, h1, h2, h3, -⟩ :=
    frameSignedData_RPlus (K := K) hK (E := Ebar Bs L θ) (Ebar_isElemAbelian θ hBs hEbot)
      (Ebar_card θ hEbot hcardE)
      (fun g hg hg3 => Ebar_selfCent hZ2 hBs hcard hcardE hx1 hLx hBL hstar θ g hg hg3)
  exact ⟨Θ, h1, h2, h3⟩

public theorem mem_E_of_pow_three {Bs L : Subgroup G} {y : ↥L}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hy : qMap (K := K) θ y ∈ Ebar Bs L θ) (hy3 : y ^ 3 = 1) :
    (y : G) ∈ Bs ⊓ L := by
  classical
  obtain ⟨e, he, hq⟩ := (mem_Ebar θ).mp hy
  have hz : y * e⁻¹ ∈ Subgroup.center ↥L := by
    rw [← qMap_ker (K := K) θ, MonoidHom.mem_ker, map_mul, map_inv, hq, mul_inv_cancel]
  have hye : y = (y * e⁻¹) * e := by group
  have he3 : e ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 (e : G) (mem_EL.mp he).1
  have hz3 : (y * e⁻¹) ^ 3 = 1 := by
    have hcomm : Commute (y * e⁻¹) e := (Subgroup.mem_center_iff.mp hz e).symm
    have h1 : ((y * e⁻¹) * e) ^ 3 = 1 := by rw [← hye]; exact hy3
    rwa [hcomm.mul_pow, he3, mul_one] at h1
  have hz1 : y * e⁻¹ = 1 := by
    obtain ⟨n, hn⟩ := hZ2 ⟨y * e⁻¹, hz⟩
    have h2 : (y * e⁻¹) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hdvd3 : orderOf (y * e⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have hdvd2 : orderOf (y * e⁻¹) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    have hcop : Nat.Coprime 3 (2 ^ n) := (by norm_num : Nat.Coprime 3 2).pow_right n
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2)
  have hye2 : y = e := by rw [hye, hz1, one_mul]
  rw [hye2]
  exact mem_EL.mp he

public theorem exists_lift_mem_NL {Bs L : Subgroup G} {x : G}
    (hZ2 : IsPGroup 2 (Subgroup.center L)) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 5) (hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4)
    (hx1 : x ≠ 1) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    {r : OrthRest.RPlus K 4}
    (hr : r ∈ Subgroup.normalizer (Ebar Bs L θ : Set (OrthRest.RPlus K 4))) :
    ∃ l : ↥L, qMap (K := K) θ l = r ∧ (l : G) ∈ NL L Bs := by
  classical
  obtain ⟨hxBs, hxL, hxord, hEbot, hExbot⟩ := bstar_basic hZ2 hBs hx1 hBL
  obtain ⟨l₀, hl₀⟩ := qMap_surjective θ r
  have hEmaps : (Bs ⊓ L).map (MulAut.conj (l₀ : G)) ≤ (Bs ⊓ L) := by
    rintro - ⟨e, he, rfl⟩
    have hq : qMap (K := K) θ (l₀ * ⟨(e : G), he.2⟩ * l₀⁻¹) ∈ Ebar Bs L θ := by
      rw [map_mul, map_mul, map_inv, hl₀]
      exact (Subgroup.mem_normalizer_iff.mp hr (qMap (K := K) θ ⟨(e : G), he.2⟩)).mp
        ((mem_Ebar θ).mpr ⟨⟨(e : G), he.2⟩, mem_EL.mpr he, rfl⟩)
    have he3 : (⟨(e : G), he.2⟩ : ↥L) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBs.2 (e : G) he.1
    have h3 : (l₀ * ⟨(e : G), he.2⟩ * l₀⁻¹) ^ 3 = 1 := by
      rw [conj_pow, he3, mul_one, mul_inv_cancel]
    have hmem := mem_E_of_pow_three hZ2 hBs θ hq h3
    exact hmem
  have hEeq : (Bs ⊓ L).map (MulAut.conj (l₀ : G)) = (Bs ⊓ L) := by
    refine Subgroup.eq_of_le_of_card_ge hEmaps ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (l₀ : G)).injective]
  have hxconj : MulAut.conj (l₀ : G) x = x := by
    rw [MulAut.conj_apply]
    have h0 : (l₀ : G) * x = x * (l₀ : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLx l₀.2)
    rw [h0, mul_assoc, mul_inv_cancel, mul_one]
  have hZeq : (Subgroup.zpowers x).map (MulAut.conj (l₀ : G)) = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hxconj
  have hsup : Bs = (Bs ⊓ L) ⊔ Subgroup.zpowers x :=
    bstar_eq_sup hBs hcard hcardE hxBs hxord hExbot
  have hBsmap : Bs.map (MulAut.conj (l₀ : G)) = Bs := by
    rw [hsup, Subgroup.map_sup, hEeq, hZeq]
  have hN : (l₀ : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hBsmap
  exact ⟨l₀, hl₀, mem_NL.mpr ⟨l₀.2, hN⟩⟩

end CFSG.StandardType.E6QTwo

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.Open SpCoord
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {K : Type} [Field K] [Finite K]

@[expose] public def NLtoL (L Bs : Subgroup G) : ↥(NL L Bs) →* ↥L :=
  Subgroup.inclusion (inf_le_left : NL L Bs ≤ L)

@[expose] public def NLqMap (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) :
    ↥(NL L Bs) →* OrthRest.RPlus K 4 :=
  (qMap (K := K) θ).comp (NLtoL L Bs)

public theorem NLqMap_apply (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4) (l : ↥(NL L Bs)) :
    NLqMap Bs L θ l = qMap (K := K) θ (NLtoL L Bs l) := rfl

@[expose] public noncomputable def conjC (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3))) :
    ↥(NL L Bs) →* MulAut (Fin 4 → Multiplicative (ZMod 3)) :=
  (MulAut.congr ΘE).toMonoidHom.comp (conjE L Bs)

public theorem conjC_apply (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3)))
    (l : ↥(NL L Bs)) (e : ↥(Bs ⊓ L)) :
    conjC Bs L θ ΘE l (ΘE e) = ΘE (conjE L Bs l e) := by
  rw [conjC, MonoidHom.comp_apply]
  simp [MulAut.congr]

public theorem qE_conjE_coe (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (l : ↥(NL L Bs)) (e : ↥(Bs ⊓ L)) :
    ((qE Bs L θ (conjE L Bs l e) : ↥(Ebar Bs L θ)) : OrthRest.RPlus K 4) =
      NLqMap Bs L θ l * ((qE Bs L θ e : ↥(Ebar Bs L θ)) : OrthRest.RPlus K 4) *
        (NLqMap Bs L θ l)⁻¹ := by
  rw [qE_apply, qE_apply, NLqMap_apply]
  have h1 : (⟨(((conjE L Bs l e : ↥(Bs ⊓ L)) : G)), (conjE L Bs l e).2.2⟩ : ↥L) =
      NLtoL L Bs l * ⟨(e : G), e.2.2⟩ * (NLtoL L Bs l)⁻¹ := by
    apply Subtype.ext
    show (((conjE L Bs l e : ↥(Bs ⊓ L)) : G)) = (l : G) * (e : G) * (l : G)⁻¹
    rw [conjE_coe]
  rw [h1, map_mul, map_mul, map_inv]

public theorem conjC_relation (Bs L : Subgroup G)
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (Θ : (Fin 4 → Multiplicative (ZMod 3)) ≃* ↥(Ebar Bs L θ))
    (ΘE : ↥(Bs ⊓ L) ≃* (Fin 4 → Multiplicative (ZMod 3)))
    (hΘE : ∀ e, Θ (ΘE e) = qE Bs L θ e)
    (l : ↥(NL L Bs)) (f : Fin 4 → Multiplicative (ZMod 3)) :
    NLqMap Bs L θ l * (Θ f : OrthRest.RPlus K 4) * (NLqMap Bs L θ l)⁻¹ =
      (Θ (conjC Bs L θ ΘE l f) : OrthRest.RPlus K 4) := by
  have hf : (Θ f : OrthRest.RPlus K 4) =
      ((qE Bs L θ (ΘE.symm f) : ↥(Ebar Bs L θ)) : OrthRest.RPlus K 4) := by
    conv_lhs => rw [show f = ΘE (ΘE.symm f) from (MulEquiv.apply_symm_apply ΘE f).symm]
    exact congrArg Subtype.val (hΘE (ΘE.symm f))
  have hf2 : conjC Bs L θ ΘE l f = ΘE (conjE L Bs l (ΘE.symm f)) := by
    conv_lhs => rw [show f = ΘE (ΘE.symm f) from (MulEquiv.apply_symm_apply ΘE f).symm]
    rw [conjC_apply]
  rw [hf, hf2, hΘE]
  exact (qE_conjE_coe Bs L θ l (ΘE.symm f)).symm

end CFSG.StandardType.E6QTwo

end
