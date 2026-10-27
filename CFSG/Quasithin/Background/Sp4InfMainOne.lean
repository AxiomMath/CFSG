module

public import CFSG.Quasithin.Background.Sp4InfMain
public import CFSG.Quasithin.Background.Sp4InfNorm
public import CFSG.Quasithin.Background.Sp4InfField
public import CFSG.Quasithin.Background.FFC2Sp4

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.PairG
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open B6

namespace Sp4Inf

theorem le_alt_of_perfect {N : Subgroup (Equiv.Perm (Fin 6))} (hN : Group.IsPerfect N) :
    N ≤ alternatingGroup (Fin 6) := by
  have h1 : ⁅N, N⁆ = N := Subgroup.commutator_eq_self
  rw [← h1, Subgroup.commutator_le]
  intro g _ h _
  rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

theorem isAlt6Sub_of_perfect_normal {D : Subgroup (StatedSp 2 (ZMod 2))} (hP : Group.IsPerfect D)
    (hn : D.Normal) (hne : D ≠ ⊥) : IsAlt6Sub D := by
  have hP' : Group.IsPerfect (D.map iotaSp.toMonoidHom) := Group.IsPerfect.map _
  have hle : D.map iotaSp.toMonoidHom ≤ alternatingGroup (Fin 6) := le_alt_of_perfect hP'
  have hnorm : (D.map iotaSp.toMonoidHom).Normal := hn.map _ iotaSp.surjective
  rcases CFSG.QuasithinUnique.Bridge.Alt57Model.normal_eq_bot_or_alt_le hnorm with h | h
  · exact absurd ((Subgroup.map_eq_bot_iff_of_injective (f := iotaSp.toMonoidHom) D iotaSp.injective).1 h) hne
  · exact le_antisymm hle h

theorem matrix_map_refl {ι : Type} (M : Matrix ι ι (ZMod 2)) : M.map (RingEquiv.refl (ZMod 2)) = M :=
  rfl

end Sp4Inf

namespace B69

theorem secL_le_secGroup {V : Type} [CommGroup V] (L A : Subgroup (MulAut V))
    (I : Subgroup ↥(redU L A)) : secL L A I ≤ secGroup L A I :=
  autSec_mono le_sup_left _ _

theorem secL_conj_mem {V : Type} [CommGroup V] {L A : Subgroup (MulAut V)}
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (I : Subgroup ↥(redU L A))
    {ψ φ : MulAut (Sec I (I ⊓ fixV (autSub L (redU L A))))}
    (hψ : ψ ∈ secGroup L A I) (hφ : φ ∈ secL L A I) : ψ * φ * ψ⁻¹ ∈ secL L A I := by
  have hconjA : ∀ a : stabSub (redU L A), (a : MulAut V) ∈ A → ∀ x ∈ autSub L (redU L A),
      resHom (redU L A) a * x * (resHom (redU L A) a)⁻¹ ∈ autSub L (redU L A) := by
    intro a ha x hx
    obtain ⟨l, hlL, rfl⟩ := mem_autSub.1 hx
    refine mem_autSub.2 ⟨a * l * a⁻¹, hAn _ ha _ hlL, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hle : autSub L (redU L A) ⊔ autSub A (redU L A) ≤
      Subgroup.normalizer (autSub L (redU L A) : Set (MulAut ↥(redU L A))) := by
    refine sup_le Subgroup.le_normalizer fun a' ha' => ?_
    obtain ⟨a, haA, rfl⟩ := mem_autSub.1 ha'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconjA a haA x hx, fun hx => ?_⟩
    have := hconjA a⁻¹ (A.inv_mem haA) _ hx
    simpa [map_inv, mul_assoc] using this
  obtain ⟨h, hhX, hU, rfl⟩ := B1Red.mem_autSec_iff.1 hψ
  obtain ⟨g, hgX, hU', rfl⟩ := B1Red.mem_autSec_iff.1 hφ
  have hN : (h : MulAut ↥(redU L A)) ∈
      Subgroup.normalizer (autSub L (redU L A) : Set (MulAut ↥(redU L A))) := hle hhX
  have hkX : ((h * g * h⁻¹ : stabSub I) : MulAut ↥(redU L A)) ∈ autSub L (redU L A) :=
    (Subgroup.mem_normalizer_iff.1 hN _).1 hgX
  have hkU : resHom I (h * g * h⁻¹) ∈
      stabSub ((I ⊓ fixV (autSub L (redU L A))).subgroupOf I) := by
    rw [map_mul, map_mul, map_inv]
    exact (stabSub _).mul_mem ((stabSub _).mul_mem hU hU') ((stabSub _).inv_mem hU)
  refine B1Red.mem_autSec_iff.2 ⟨h * g * h⁻¹, hkX, hkU, ?_⟩
  have hsub : (⟨resHom I (h * g * h⁻¹), hkU⟩ :
      stabSub ((I ⊓ fixV (autSub L (redU L A))).subgroupOf I)) =
      ⟨resHom I h, hU⟩ * ⟨resHom I g, hU'⟩ * ⟨resHom I h, hU⟩⁻¹ :=
    Subtype.ext (show resHom I (h * g * h⁻¹) = resHom I h * resHom I g * (resHom I h)⁻¹ by
      rw [map_mul, map_mul, map_inv])
  rw [hsub, map_mul, map_mul, map_inv]

theorem noStrongSp4One
    : AsB69NoStrongSp4One := by
  intro V _ _ hV X S M A L hdata ⟨I, hI, hn, hq⟩
  obtain ⟨-, hmp, -, hA, hAs, hL, hLA⟩ := hdata
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLX : L ≤ X := hL.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hJ : ffJ (secGroup L A I) ≤ secGroup L A I := B6.ffJ_le _
  have hGJ : secGroup L A I ≤ ffJ (secGroup L A I) :=
    FFC.le_of_binaryNaturalSp4_one
      (fun g hg h hh => (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ _ hg) _).1 hh) hn
  have hLH : secL L A I ≤ ffJ (secGroup L A I) := (secL_le_secGroup L A I).trans hGJ
  have hnormH : ((secL L A I).subgroupOf (ffJ (secGroup L A I))).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    exact secL_conj_mem hAn I (hJ g.2) hn'
  obtain ⟨K, hKf, hKfin, hK, r, -, hrn, hrne, e₁, he₁⟩ := exists_natural_data_sp4_gen hI hLH hn
  have hrnorm : r.range.Normal := hrn hnormH
  have hrne' : r.range ≠ ⊥ := hrne (secL_nontrivial hI)
  have hW₁ := B1Red.mem_irrPlus_of_autSub (le_stabSub_redU L A) hI
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  let r' : ↥L →* StatedSp 2 (ZMod 2) := (Sp4Inf.mapSp e).toMonoidHom.comp r
  let e₁' := e₁.trans (Sp4Inf.stdMapEquiv e)
  have he₁' : ∀ (hLW : L ≤ stabSub (I.map (redU L A).subtype)) (hLU : L ≤ stabSub (fixV L))
      (l : ↥L) (s : Sec (I.map (redU L A).subtype) (fixV L)),
      e₁' (B5.secHom L hLW hLU l s) =
        matAut ((r' l : ↥(StatedSp 2 (ZMod 2))) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₁' s) := by
    intro hLW hLU l s
    show Sp4Inf.stdMapEquiv e (e₁ (B5.secHom L hLW hLU l s)) = _
    rw [he₁ hLW hLU l s, Sp4Inf.stdMapEquiv_matAut]
    rfl
  have hrange : r'.range = r.range.map (Sp4Inf.mapSp e).toMonoidHom :=
    MonoidHom.range_comp (Sp4Inf.mapSp e).toMonoidHom r
  have hnormD : r'.range.Normal := by
    rw [hrange]
    exact hrnorm.map _ (Sp4Inf.mapSp e).surjective
  have hneD : r'.range ≠ ⊥ := by
    rw [hrange]
    intro h
    exact hrne' ((Subgroup.map_eq_bot_iff_of_injective (f := (Sp4Inf.mapSp e).toMonoidHom) r.range
      (Sp4Inf.mapSp e).injective).1 h)
  have hLperf : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hperfD : Group.IsPerfect ↥(r'.range) := Group.IsPerfect.range r'
  have hDalt : Sp4Inf.IsAlt6Sub r'.range := Sp4Inf.isAlt6Sub_of_perfect_normal hperfD hnormD hneD
  have hDalt' : r'.range.map Sp4Inf.iotaSp.toMonoidHom = alternatingGroup (Fin 6) := hDalt
  have hmemA : ∀ l : ↥L, Sp4Inf.iotaSp (r' l) ∈ alternatingGroup (Fin 6) := fun l => by
    have h1 : Sp4Inf.iotaSp (r' l) ∈ r'.range.map Sp4Inf.iotaSp.toMonoidHom := ⟨r' l, ⟨l, rfl⟩, rfl⟩
    rwa [hDalt'] at h1
  let π₀ : ↥L →* ↥(alternatingGroup (Fin 6)) :=
    (Sp4Inf.iotaSp.toMonoidHom.comp r').codRestrict (alternatingGroup (Fin 6)) hmemA
  have hπ₀ : Function.Surjective π₀ := by
    intro y
    have : (y : Equiv.Perm (Fin 6)) ∈ r'.range.map Sp4Inf.iotaSp.toMonoidHom := by
      rw [hDalt']
      exact y.2
    obtain ⟨x, ⟨l, rfl⟩, hx⟩ := this
    exact ⟨l, Subtype.ext hx⟩
  have hcenter : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hker₀ : π₀.ker = Subgroup.center ↥L := ker_eq_center_of_surj hLq hcenter π₀ hπ₀
  have hLhat : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := isComponentOf_subgroupOf hL
  let e0 : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let πh : ↥(L.subgroupOf X) →* ↥(alternatingGroup (Fin 6)) := π₀.comp e0.toMonoidHom
  have hπh : Function.Surjective πh := hπ₀.comp e0.surjective
  have hkerh : πh.ker = Subgroup.center ↥(L.subgroupOf X) :=
    ker_eq_center_of_surj hLhat.2.2 hcenter πh hπh
  have hev : Even (Nat.card ↥(alternatingGroup (Fin 6))) := by
    rw [Sp4Inf.card_alt_six']
    exact ⟨180, by norm_num⟩
  obtain ⟨t, -, htN, hall⟩ := exists_swap Sp4Inf.swapGeo_alt6 hev hmp hLhat πh hπh hkerh
  have ht : ∀ x ∈ L, (t : MulAut V) * x * (t : MulAut V)⁻¹ ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp htN ⟨x, hLX hx⟩).mp hx'
    exact this
  have ht' : ∀ x ∈ L, (t : MulAut V)⁻¹ * x * (t : MulAut V) ∈ L := by
    intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥X) ∈ (L.subgroupOf X) := hx
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) ⟨x, hLX hx⟩).mp hx'
    exact this
  have htV : (t : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    mem_normalizer_of_forall_mem ht ht'
  obtain ⟨thb, hthb⟩ := exists_aut_of_ker_eq π₀ hπ₀ (indAut L (t : MulAut V)) (by
    intro l
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker₀]
    exact mem_center_map_iff _ l)
  have hind : ∀ l l' : ↥L, (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
      indAut L (t : MulAut V) l = l' := by
    intro l l' hl'
    apply Subtype.ext
    rw [coe_indAut_apply htV, hl']
  have hnot : ¬ Sp4Inf.InducedByS6 thb := by
    refine hall thb fun l l' hl' => ?_
    have h1 : indAut L (t : MulAut V) (e0 l) = e0 l' := by
      apply hind
      show ((l' : ↥X) : MulAut V) = _
      rw [hl']
      rfl
    show thb (π₀ (e0 l)) = π₀ (e0 l')
    rw [hthb, h1]
  obtain ⟨γ₁, hγ₁⟩ := (Sp4Inf.ext_alt6 thb).resolve_left hnot
  have htw : ∃ (A' : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (σ : ZMod 2 ≃+* ZMod 2), ∀ l l' : ↥L,
      (l' : MulAut V) = (t : MulAut V) * l * (t : MulAut V)⁻¹ →
        (((r' l' : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
          (A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) *
            (((tauSp (r' l) : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)).map σ *
            (((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    refine ⟨(γ₁ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)), RingEquiv.refl _, fun l l' hl' => ?_⟩
    have h1 := hγ₁ (π₀ l)
    have h2 : thb (π₀ l) = π₀ l' := by rw [hthb, hind l l' hl']
    rw [h2] at h1
    have h3 : Sp4Inf.iotaSp (r' l') = Sp4Inf.iotaSp (γ₁ * tauSp (r' l) * γ₁⁻¹) := by
      have h1' : Sp4Inf.iotaSp (r' l') = Sp4Inf.iotaSp
          (γ₁ * tauSp (Sp4Inf.iotaSp.symm (Sp4Inf.iotaSp (r' l))) * γ₁⁻¹) := h1
      rwa [MulEquiv.symm_apply_apply] at h1'
    have h4 : (r' l' : StatedSp 2 (ZMod 2)) = γ₁ * tauSp (r' l) * γ₁⁻¹ :=
      Sp4Inf.iotaSp.injective h3
    rw [h4, Sp4Inf.matrix_map_refl]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hniso : ∀ Φ : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) ≃* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2),
      (∀ (l : ↥L) (x : StdMod (Fin 2 ⊕ Fin 2) (ZMod 2)),
        Φ (matAut ((r' l : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) x) =
          matAut ((tauSp (r' l) : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (Φ x)) →
        False := by
    intro Φ hΦ
    refine Sp4Inf.no_tau_iso hDalt Φ (fun γ hγ x => ?_)
    obtain ⟨l, rfl⟩ := hγ
    exact hΦ l x
  exact false_of_twist_sp4_gen hV hA hAs hLq hLA (n := 1) le_rfl (by simp) r' hW₁ e₁' he₁'
    (t : MulAut V) ht ht' htw hniso fun x hx h₁ h₂ =>
      Sp4Inf.mem_pairNormSp_of_normalizes hDalt hx h₁ h₂

theorem noStrongSp4
    : AsB69NoStrongSp4 := noStrongSp4_of_one noStrongSp4One

end B69

end CFSG.Quasithin
