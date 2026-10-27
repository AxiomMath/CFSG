module

public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFusion
import CFSG.LocalAnalysis.SeitzReduction.E7PilotOuter
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFacts
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210a

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.LieType.ChevTwo CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

theorem le_centralizer_of_omegaPlusSix_marking {G : Type} [Group G] [Finite G] {K E T : Subgroup G}
    (hm : LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1))
    (hZ : Subgroup.center ↥K = ⊥) (hEK : E ≤ K) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 6 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaPlusSix_of_marking hm hZ
  exact le_centralizer_of_goodQ (goodQ_plus (n := 5) (by norm_num))
    (omegaTwoAutInduced_plus_of_four_le (n := 5) (by norm_num)) (by decide) e hZ hEK hE
    (by simpa [Fintype.card_sum] using hcard) hT hTN hET

section E7


theorem le_centralizer_of_E7Two_torus {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2) {G : Type} [Group G] [Finite G] {K E T : Subgroup G}
    (φ : ↥K ≃* adjointGroup .E7 k) (hEK : E ≤ K) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 7 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have hZ : Subgroup.center ↥K = ⊥ :=
    CFSG.SeitzReduction.E7Pilot.center_eq_bot_of_mulEquiv_E7 φ
  set N : Subgroup G := Subgroup.normalizer (K : Set G)
  set c : ↥N →* MulAut ↥K := Subgroup.normalizerMonoidHom (H := K) with hcdef
  have hNinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    intro a b hab
    have hmem : b⁻¹ * a ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun f : MulAut ↥K => f x) hab
      simp only [MulAut.conj_apply] at h
      calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
        _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = (b⁻¹ * a) * x := by group
    have h1 : b⁻¹ * a = 1 := by
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  have hNsurj : Function.Surjective (MulAut.conj : ↥K →* MulAut ↥K) := fun ψ =>
    CFSG.SeitzReduction.E7Pilot.forall_mem_range_conj_of_mulEquiv_E7_two hk φ ψ
  set e : ↥K ≃* MulAut ↥K := MulEquiv.ofBijective _ ⟨hNinj, hNsurj⟩ with hedef
  set lam : ↥N →* ↥K := e.symm.toMonoidHom.comp c with hlamdef
  have hlam_l : ∀ l : ↥K, lam ⟨l, Subgroup.le_normalizer l.2⟩ = l := by
    intro l
    have hc : c ⟨l, Subgroup.le_normalizer l.2⟩ = MulAut.conj l := by
      ext x
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    change e.symm (c ⟨l, Subgroup.le_normalizer l.2⟩) = l
    rw [hc]
    exact e.symm_apply_apply l
  set R : Subgroup ↥K := (T.subgroupOf N).map lam with hRdef
  set E' : Subgroup ↥K := E.subgroupOf K with hE'def
  have hTsub : IsPGroup 2 ↥(T.subgroupOf N) := by
    rw [Subgroup.subgroupOf]
    exact hT.comap_of_injective N.subtype N.subtype_injective
  have hR2 : IsPGroup 2 R := hTsub.map lam
  have hE'el : IsElemAbelian 3 E' := hE.subgroupOf K
  have hcardE' : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hER : E' ≤ Subgroup.normalizer (R : Set ↥K) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx r hr
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hr
    have hxE : (x : G) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    let n : ↥N := ⟨(x : G), Subgroup.le_normalizer x.2⟩
    have hlam_n : lam n = x := hlam_l x
    have hmemT : (n * t * n⁻¹ : ↥N) ∈ T.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have h := (Subgroup.mem_normalizer_iff.mp (hET hxE)) (t : G)
      exact h.mp htT
    refine Subgroup.mem_map.mpr ⟨n * t * n⁻¹, hmemT, ?_⟩
    simp only [map_mul, map_inv, hlam_n]
  have hE2el : IsElemAbelian 3 (E'.map φ.toMonoidHom) := hE'el.map φ.toMonoidHom
  have hcardE2 : 3 ^ 7 ≤ Nat.card (E'.map φ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective φ.injective, hcardE']
    exact hcard
  obtain ⟨c0, hc0⟩ :=
    TableBExcTwoTB.exists_conj_frame_of_card_E7 (K := k) hk hE2el hcardE2
  let φ' : ↥K ≃* adjointGroup .E7 k := φ.trans (MulAut.conj c0⁻¹)
  have hφ' : φ'.toMonoidHom = (MulAut.conj c0⁻¹).toMonoidHom.comp φ.toMonoidHom := by
    simp [φ']
  have hconj : ((TableBExcTwoTB.tE k TableBExcTwo.frameE7).range.map
      (MulAut.conj c0).toMonoidHom).map (MulAut.conj c0⁻¹).toMonoidHom =
      (TableBExcTwoTB.tE k TableBExcTwo.frameE7).range := by
    have h : (MulAut.conj c0⁻¹).toMonoidHom.comp (MulAut.conj c0).toMonoidHom =
        MonoidHom.id ↥(adjointGroup .E7 k) := by
      ext y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      group
    rw [Subgroup.map_map, h, Subgroup.map_id]
  have hE'map : E'.map φ'.toMonoidHom =
      (TableBExcTwoTB.tE k TableBExcTwo.frameE7).range := by
    rw [hφ', ← Subgroup.map_map, hc0, hconj]
  have hP : P13aConclusion ↥K E' 7 := p13a6_E7 hk φ' hE'map
  have hRbot : R = ⊥ := by
    by_contra hRne
    have hcop : Nat.Coprime 3 (Nat.card R) := by
      obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hR2
      exact Nat.Coprime.of_dvd_right hn (Nat.Coprime.pow_right n (by norm_num))
    have h3 : 3 ≤ Nat.card E' := by
      rw [hcardE']
      exact le_trans (by norm_num) hcard
    have hRle : ¬ R ≤ ⊥ := fun h => hRne (le_bot_iff.mp h)
    obtain ⟨F, hF, hFU⟩ :=
      CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210g.exists_hyperplane_not_le
        (Γ := ↥K) Nat.prime_three hE'el h3 hER hcop hRle
    have hFE : F ≤ E' := hF.1
    have hidx : F.relIndex E' = 3 := by
      have h1 := Subgroup.relIndex_mul_card F E'
      rw [inf_of_le_left hFE, hF.2] at h1
      exact Nat.mul_right_cancel Nat.card_pos h1
    have hcommE : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val
        ((isMulCommutative_iff.mp hE'el.1) ⟨x, hx⟩ ⟨y, hy⟩)
    have hEU : E' ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer (F : Set ↥K) : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      rw [Subgroup.mem_inf] at hy ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hER hx) y).mp hy.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro f hf
      have hxf : f * x = x * f := hcommE f (hFE hf) x hx
      have hyf : f * y = y * f := hy.2 f hf
      have hxf' : x⁻¹ * f = f * x⁻¹ := by
        have hc : Commute f x := hxf
        exact hc.inv_right.symm
      calc
        f * (x * y * x⁻¹) = (f * x) * y * x⁻¹ := by group
        _ = (x * f) * y * x⁻¹ := by rw [hxf]
        _ = x * (f * y) * x⁻¹ := by group
        _ = x * (y * f) * x⁻¹ := by rw [hyf]
        _ = x * y * (f * x⁻¹) := by group
        _ = x * y * (x⁻¹ * f) := by rw [← hxf']
        _ = (x * y * x⁻¹) * f := by group
    have hUbot : R ⊓ Subgroup.centralizer (F : Set ↥K) = ⊥ :=
      p13a7_of_conclusion hP hFE hidx inf_le_right (IsPGroup.to_inf_left hR2) hEU
    exact hFU (le_of_eq hUbot)
  intro t ht
  have htn : (⟨t, hTN ht⟩ : ↥N) ∈ T.subgroupOf N := Subgroup.mem_subgroupOf.mpr ht
  have hmemR : lam ⟨t, hTN ht⟩ ∈ R :=
    Subgroup.mem_map.mpr ⟨⟨t, hTN ht⟩, htn, rfl⟩
  rw [hRbot, Subgroup.mem_bot] at hmemR
  have hlam1 : lam ⟨t, hTN ht⟩ = 1 := hmemR
  have hc1 : c ⟨t, hTN ht⟩ = 1 := by
    have h2 : e (lam ⟨t, hTN ht⟩) = c ⟨t, hTN ht⟩ := by
      rw [hlamdef]
      exact e.apply_symm_apply (c ⟨t, hTN ht⟩)
    rw [hlam1, map_one] at h2
    exact h2.symm
  have hker : (⟨t, hTN ht⟩ : ↥N) ∈ (Subgroup.normalizerMonoidHom (H := K)).ker := by
    rw [MonoidHom.mem_ker]
    exact hc1
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  have htC : t ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_subgroupOf.mp hker
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp htC) l hl

end E7

theorem le_centralizer_bstar_of_normal {G : Type} [Group G] {Bs K T : Subgroup G} {z : G}
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal)
    (hsup : Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs)
    (hK : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.normalizer (K : Set G) →
      Bs ⊓ K ≤ Subgroup.normalizer (T : Set G) → T ≤ Subgroup.centralizer (K : Set G))
    (hT : IsPGroup 2 T) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (hBsT : Bs ≤ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.centralizer (Bs : Set G) := by
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    hTz.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKz).mp hKn)
  have hKT : T ≤ Subgroup.centralizer (K : Set G) :=
    hK T hT hTN (inf_le_left.trans hBsT)
  rw [← hsup, Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
  · exact inf_le_right.trans (Subgroup.le_centralizer_iff.mp hKT)

end CFSG.StandardType.FrameRoute
