module

public import CFSG.Quasithin.Vol2.Ch7Lem776a
public import CFSG.Quasithin.Background.HSL3S77SD
public import CFSG.Quasithin.Vol2.Ch7Lem774
public import CFSG.Quasithin.Vol2.Ch7Sec77Coord

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

abbrev vp (p : PairMod (ZMod 2)) : Vec × Vec := (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2)

abbrev pv (x : Vec × Vec) : PairMod (ZMod 2) :=
  (Multiplicative.ofAdd x.1, Multiplicative.ofAdd x.2)

theorem pv_injective : Function.Injective pv := fun x y h => by
  have h1 := congrArg vp h
  exact h1

theorem vp_injective : Function.Injective vp := fun _ _ h =>
  Prod.ext (Multiplicative.toAdd.injective (congrArg Prod.fst h))
    (Multiplicative.toAdd.injective (congrArg Prod.snd h))

theorem vp_rho (g : SL32) (p : PairMod (ZMod 2)) :
    vp (SL3One.rho g p) = (act g (vp p).1, dact g (vp p).2) := by
  rw [vp, rho_fst, rho_snd]

theorem vp_swap (p : PairMod (ZMod 2)) : vp (swapAut (ZMod 2) p) = ((vp p).2, (vp p).1) := rfl

@[expose] def sdSet : Set (PairMod (ZMod 2)) := {p | SingDiag (vp p).1 (vp p).2}

theorem ncard_sdSet : sdSet.ncard = 21 := by
  have h : sdSet = pv '' (↑(Finset.univ.filter (fun q : Vec × Vec => SingDiag q.1 q.2)) :
      Set (Vec × Vec)) := by
    ext p
    constructor
    · intro hp
      have hp' : SingDiag (vp p).1 (vp p).2 := hp
      exact ⟨vp p, by simpa using hp', rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' : SingDiag x.1 x.2 := by simpa using hx
      exact hx'
  rw [h, Set.ncard_image_of_injective _ pv_injective, Set.ncard_coe_finset, sd_card]

theorem orbit_eq_sdSet {p : PairMod (ZMod 2)} (hp : p ∈ sdSet) :
    MulAction.orbit (↥(pairNorm (ZMod 2))) p = sdSet := by
  ext q
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨g, rfl | rfl⟩ := mem_pairNorm_iff.mp hx
    · change SingDiag (vp (SL3One.rho g p)).1 (vp (SL3One.rho g p)).2
      rw [vp_rho]
      exact sd_act g hp
    · change SingDiag (vp (swapAut (ZMod 2) (SL3One.rho g p))).1
        (vp (swapAut (ZMod 2) (SL3One.rho g p))).2
      rw [vp_swap, vp_rho]
      exact sd_swap (sd_act g hp)
  · intro hq
    obtain ⟨g₁, hg₁, hg₁'⟩ := sd_trans hq
    obtain ⟨g₂, hg₂, hg₂'⟩ := sd_trans hp
    have hp' : p = SL3One.rho g₂ (pv (e1, e3)) := by
      apply vp_injective
      rw [vp_rho]
      exact Prod.ext hg₂.symm hg₂'.symm
    have hq' : q = SL3One.rho g₁ (pv (e1, e3)) := by
      apply vp_injective
      rw [vp_rho]
      exact Prod.ext hg₁.symm hg₁'.symm
    refine ⟨⟨SL3One.rho (g₁ * g₂⁻¹), pairSL_le_pairNorm (SL3One.rho_mem_pairSL _)⟩, ?_⟩
    change SL3One.rho (g₁ * g₂⁻¹) p = q
    rw [hp', hq', map_mul, MulAut.mul_apply]
    congr 1
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

namespace Setup

variable (S : Setup T L I)
include S

theorem I_ne : I ≠ ⊥ ∧ I ≠ fsuV T I := by
  obtain ⟨t, -, hsup, hinf, -⟩ := S.exists_twist
  have hI1 : I ≠ ⊥ := S.hyp.fsu.irrPlus.2.1
  have hItV : CFSG.conjugate I t ≤ fsuV T I := by
    rw [← hsup]
    exact le_sup_right
  refine ⟨hI1, fun h => S.conjugate_ne_bot t ?_⟩
  rw [eq_bot_iff, ← hinf]
  exact le_inf (hItV.trans h.ge) le_rfl

theorem map_autI_top_eq {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)}
    (he : (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2)) :
    (autI S.hV ⊤).map (congrHom e) = pairNorm (ZMod 2) := by
  have hle : (autI S.hV ⊤).map (congrHom e) ≤ pairNorm (ZMod 2) := by
    have h3 : (Subgroup.normalizer (autI S.hV (fsuL0 T L) :
        Set (MulAut (IntMod (fsuV T I) S.hV)))).map (congrHom e) =
          Subgroup.normalizer (((autI S.hV (fsuL0 T L)).map (congrHom e) :
            Subgroup (MulAut (PairMod (ZMod 2)))) : Set (MulAut (PairMod (ZMod 2)))) :=
      Subgroup.map_equiv_normalizer_eq _ (MulAut.congr e)
    exact (Subgroup.map_mono S.autI_top_le).trans (h3.trans (congrArg
      (fun X : Subgroup (MulAut (PairMod (ZMod 2))) =>
        Subgroup.normalizer (X : Set (MulAut (PairMod (ZMod 2))))) he)).le
  have hrho : ∀ h : SL32, SL3One.rho h ∈ (autI S.hV ⊤).map (congrHom e) := fun h =>
    Subgroup.map_mono (autI_mono S.hV le_top)
      ((SetLike.ext_iff.mp he _).mpr (SL3One.rho_mem_pairSL h))
  refine le_antisymm hle ?_
  obtain ⟨t, htT, -, hinf, -⟩ := S.exists_twist
  have htN : t⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := S.T_le_normalizer_V (T.inv_mem htT)
  set y := convI S.hV ⟨t⁻¹, htN⟩ with hy
  have hyA : y ∈ autI S.hV ⊤ := convI_mem_autI S.hV (Subgroup.mem_top _) htN
  have hyN := hle ⟨y, hyA, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : SL32, congrHom e y = swapAut (ZMod 2) * SL3One.rho g' := by
    obtain ⟨g', hg' | hg'⟩ := mem_pairNorm_iff.mp hyN
    · exfalso
      have hyL : y ∈ autI S.hV (fsuL0 T L) := by
        have h1 : congrHom e y ∈ (autI S.hV (fsuL0 T L)).map (congrHom e) :=
          (SetLike.ext_iff.mp he _).mpr (hg' ▸ SL3One.rho_mem_pairSL g')
        obtain ⟨y', hy', hyy'⟩ := h1
        rwa [← congrHom_injective e hyy']
      obtain ⟨l, hlL, hle'⟩ := (mem_autI S.hV).1 hyL
      have hlL' : (l : G) ∈ L := by rw [S.hL]; exact hlL
      obtain ⟨hI1, -⟩ := S.I_ne
      apply hI1
      rw [eq_bot_iff]
      intro v hv
      have hvV : v ∈ fsuV T I := le_fsuV I T hv
      have h1 := congrArg (fun φ : MulAut (IntMod (fsuV T I) S.hV) =>
        (φ (IntMod.mk S.hV ⟨v, hvV⟩)).val) hle'
      simp only [convI_apply_val] at h1
      have h2 : (l : G) * v * (l : G)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (S.L_le_normalizer_I hlL') v).mp hv
      have h3 : t⁻¹ * v * t ∈ I := by
        have h1' : (l : G) * v * (l : G)⁻¹ = t⁻¹ * v * t⁻¹⁻¹ := h1
        rw [h1', inv_inv] at h2
        exact h2
      have h5 : t⁻¹ * v * t ∈ CFSG.conjugate I t := by
        rw [mem_conjugate_iff']
        simpa [mul_assoc] using hv
      have h6 : t⁻¹ * v * t ∈ I ⊓ CFSG.conjugate I t := ⟨h3, h5⟩
      rw [hinf, Subgroup.mem_bot] at h6
      rw [Subgroup.mem_bot]
      calc v = t * (t⁻¹ * v * t) * t⁻¹ := by group
        _ = 1 := by rw [h6]; group
    · exact ⟨g', hg'⟩
  intro x hx
  obtain ⟨g, rfl | rfl⟩ := mem_pairNorm_iff.mp hx
  · exact hrho g
  · obtain ⟨x', hx'A, hx'e⟩ := hrho (g'⁻¹ * g)
    refine ⟨y * x', Subgroup.mul_mem _ hyA hx'A, ?_⟩
    refine MulEquiv.ext fun p => ?_
    rw [map_mul, MulAut.mul_apply, hx'e]
    have h1 := congrArg (fun f : MulAut (PairMod (ZMod 2)) => f (SL3One.rho (g'⁻¹ * g) p)) hg'
    refine h1.trans ?_
    change swapAut (ZMod 2) (SL3One.rho g' (SL3One.rho (g'⁻¹ * g) p)) =
      swapAut (ZMod 2) (SL3One.rho g p)
    congr 1
    change (SL3One.rho g' * SL3One.rho (g'⁻¹ * g)) p = SL3One.rho g p
    rw [← map_mul, mul_inv_cancel_left]

theorem autI_fsuM_eq_top : autI S.hV (fsuM T L) = autI S.hV ⊤ := by
  refine le_antisymm (autI_mono S.hV le_top) ?_
  intro φ hφ
  obtain ⟨g, -, rfl⟩ := (mem_autI S.hV).1 hφ
  exact (mem_autI S.hV).2 ⟨g, S.hNM g.2, rfl⟩

theorem exists_hom {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)}
    (he : (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2)) :
    ∃ φ' : ↥(fsuM T L) →* ↥(pairNorm (ZMod 2)), Function.Surjective φ' ∧
      ∀ x, (φ' x : MulAut (PairMod (ZMod 2))) = congrHom e (convI S.hV ⟨x, S.hMN x.2⟩) := by
  have hN := S.map_autI_top_eq he
  have hR : ((congrHom e).comp (convHom S.hV (fsuM T L) S.hMN)).range = pairNorm (ZMod 2) := by
    rw [MonoidHom.range_comp, range_convHom, S.autI_fsuM_eq_top, hN]
  have hφN : ∀ x, (congrHom e).comp (convHom S.hV (fsuM T L) S.hMN) x ∈ pairNorm (ZMod 2) :=
    fun x => hR ▸ ⟨x, rfl⟩
  refine ⟨((congrHom e).comp (convHom S.hV (fsuM T L) S.hMN)).codRestrict _ hφN, ?_,
    fun x => rfl⟩
  rintro ⟨y, hy⟩
  rw [← hR] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

theorem relIndex_centralizer_sd {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)}
    (he : (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2)) {w : G}
    (hwV : w ∈ fsuV T I) (hw : e (IntMod.mk S.hV ⟨w, hwV⟩) ∈ sdSet) :
    (fsuM T L ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (fsuM T L) = 21 := by
  obtain ⟨φ', hφ's, hφ'⟩ := S.exists_hom he
  set p := e (IntMod.mk S.hV ⟨w, hwV⟩) with hp
  have hstab : (fsuM T L ⊓ Subgroup.centralizer ({w} : Set G)).subgroupOf (fsuM T L) =
      (MulAction.stabilizer (↥(pairNorm (ZMod 2))) p).comap φ' := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
      Subgroup.mem_inf]
    have hsymm : (x : G) ∈ Subgroup.centralizer ({w} : Set G) ↔
        w ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      exact eq_comm
    rw [hsymm, mem_centralizer_iff_convI S.hV (S.hMN x.2) hwV]
    change _ ↔ (φ' x : MulAut (PairMod (ZMod 2))) p = p
    rw [hφ']
    constructor
    · rintro ⟨-, h⟩
      change e (convI S.hV ⟨x, S.hMN x.2⟩ (e.symm p)) = p
      rw [hp, MulEquiv.symm_apply_apply, h]
    · intro h
      refine ⟨x.2, e.injective ?_⟩
      have h' : e (convI S.hV ⟨x, S.hMN x.2⟩ (e.symm p)) = p := h
      rwa [hp, MulEquiv.symm_apply_apply] at h'
  rw [Subgroup.relIndex, hstab, Subgroup.index_comap_of_surjective _ hφ's,
    MulAction.index_stabilizer, orbit_eq_sdSet hw, ncard_sdSet]

theorem exists_sylow_of_singDiag {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)}
    (he : (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2)) {w : G}
    (hwV : w ∈ fsuV T I) (hw : e (IntMod.mk S.hV ⟨w, hwV⟩) ∈ sdSet) :
    ∃ S₀ : Subgroup G, IsSylowTwoOf S₀ ⊤ ∧ w ∈ S₀ ∧
      w ∈ Subgroup.centralizer (S₀ : Set G) := by
  have hidx := S.relIndex_centralizer_sd he hwV hw
  obtain ⟨S₀, hS₀, -⟩ := A4.exists_isSylowTwoOf_ge (bot_le : ⊥ ≤ fsuM T L ⊓
    Subgroup.centralizer ({w} : Set G)) IsPGroup.of_bot
  have hS₀M : IsSylowTwoOf S₀ (fsuM T L) := isSylowTwoOf_of_odd hS₀ inf_le_left (by
    rw [hidx]
    norm_num)
  have hMG : ¬ 2 ∣ (fsuM T L).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    intro h
    exact S.hyp.fsu.sylow.2 (h.trans (Subgroup.index_dvd_of_le S.T_le_fsuM))
  have hS₀G : IsSylowTwoOf S₀ ⊤ := isSylowTwoOf_of_odd hS₀M le_top hMG
  have hVM : fsuV T I ≤ fsuM T L := S.hVLT.trans (by rw [S.fsuL0_eq]; exact S.uniq.1.2)
  have hVS₀ : fsuV T I ≤ S₀ := A4.le_of_normal_of_isSylowTwoOf hS₀M hVM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVM).mpr S.hMN) S.isPGroup_fsuV
  refine ⟨S₀, hS₀G, hVS₀ hwV, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hS₀.1 hx).2

end Setup

end CFSG.Quasithin.H13.Sec77
