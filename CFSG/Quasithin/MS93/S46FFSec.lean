module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin

theorem card_hom_units {E : Type*} [CommGroup E] [Finite E] :
    Nat.card (E →* ℂˣ) = Nat.card E := by
  have : NeZero (Monoid.exponent E) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity E ℂ

section Pairing

variable {V : Type} [CommGroup V] [Finite V]

theorem relIndex_le_of_pairing (f : V →* V →* ℂˣ) {P₀ P Q₀ Q : Subgroup V}
    (h0 : ∀ p ∈ P₀, ∀ q ∈ Q, f p q = 1) (hnd : ∀ q ∈ Q, (∀ p ∈ P, f p q = 1) → q ∈ Q₀) :
    Q₀.relIndex Q ≤ P₀.relIndex P := by
  let Φ : ↥Q →* (↥P ⧸ P₀.subgroupOf P →* ℂˣ) :=
    { toFun := fun q => QuotientGroup.lift (P₀.subgroupOf P) ((f.flip q).comp P.subtype)
        (fun p hp => by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.flip_apply]
          exact h0 p (Subgroup.mem_subgroupOf.mp hp) q q.2)
      map_one' := by
        apply QuotientGroup.monoidHom_ext
        ext p
        simp
      map_mul' := fun q q' => by
        apply QuotientGroup.monoidHom_ext
        ext p
        simp }
  have hker : Φ.ker ≤ Q₀.subgroupOf Q := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    refine hnd q q.2 fun p hp => ?_
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hq) (QuotientGroup.mk ⟨p, hp⟩)
    simpa [Φ] using this
  have hE := card_hom_units (E := ↥P ⧸ P₀.subgroupOf P)
  have : Finite (↥P ⧸ P₀.subgroupOf P →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hE]; exact Nat.card_pos.ne')
  calc Q₀.relIndex Q = (Q₀.subgroupOf Q).index := rfl
    _ ≤ Φ.ker.index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hker)
    _ = Nat.card Φ.range := Subgroup.index_ker Φ
    _ ≤ Nat.card (↥P ⧸ P₀.subgroupOf P →* ℂˣ) := Subgroup.card_le_card_group _
    _ = P₀.relIndex P := hE

theorem card_mul_le_of_pairing (f : V →* V →* ℂˣ) {P₀ P Q₀ Q : Subgroup V} (hP : P₀ ≤ P)
    (hQ : Q₀ ≤ Q) (h0 : ∀ p ∈ P₀, ∀ q ∈ Q, f p q = 1)
    (hnd : ∀ q ∈ Q, (∀ p ∈ P, f p q = 1) → q ∈ Q₀) :
    Nat.card Q * Nat.card P₀ ≤ Nat.card P * Nat.card Q₀ := by
  have h := relIndex_le_of_pairing f h0 hnd
  have hQr := Subgroup.relIndex_mul_card Q₀ Q
  have hPr := Subgroup.relIndex_mul_card P₀ P
  rw [inf_eq_left.mpr hQ] at hQr
  rw [inf_eq_left.mpr hP] at hPr
  rw [← hQr, ← hPr]
  calc Q₀.relIndex Q * Nat.card Q₀ * Nat.card P₀
      ≤ P₀.relIndex P * Nat.card Q₀ * Nat.card P₀ := by gcongr
    _ = P₀.relIndex P * Nat.card P₀ * Nat.card Q₀ := by ring

end Pairing

section Perp

variable {V : Type} [CommGroup V] {M : Type*} [CommGroup M]

@[expose] def perpIn (f : V →* V →* M) (X U : Subgroup V) : Subgroup V where
  carrier := {x | x ∈ X ∧ ∀ u ∈ U, f x u = 1}
  one_mem' := ⟨X.one_mem, fun u _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, fun u hu => by
    rw [map_mul, MonoidHom.mul_apply, ha.2 u hu, hb.2 u hu, mul_one]⟩
  inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, fun u hu => by
    rw [map_inv, MonoidHom.inv_apply, ha.2 u hu, inv_one]⟩

theorem perpIn_le (f : V →* V →* M) (X U : Subgroup V) : perpIn f X U ≤ X := fun _ hx => hx.1

theorem perpIn_anti (f : V →* V →* M) (X : Subgroup V) {U U' : Subgroup V} (h : U ≤ U') :
    perpIn f X U' ≤ perpIn f X U := fun _ hx => ⟨hx.1, fun u hu => hx.2 u (h hu)⟩

theorem perpIn_perpIn [Finite V] (f : V →* V →* ℂˣ) (hskew : ∀ v w, f v w = 1 → f w v = 1)
    {X U : Subgroup V} (hRU : perpIn f X X ≤ U) (hUX : U ≤ X) :
    perpIn f X (perpIn f X U) = U := by
  have hR' : perpIn f X X ≤ perpIn f X U := perpIn_anti f X hUX
  have hβ := card_mul_le_of_pairing f (P₀ := perpIn f X X) (P := U) (Q₀ := perpIn f X U)
    (Q := X) hRU (perpIn_le f X U) (fun p hp q hq => hp.2 q hq)
    (fun q hq h => ⟨hq, fun u hu => hskew _ _ (h u hu)⟩)
  have hα := card_mul_le_of_pairing f (P₀ := perpIn f X (perpIn f X U)) (P := X)
    (Q₀ := perpIn f X X) (Q := perpIn f X U) (perpIn_le f X _) hR'
    (fun p hp q hq => hp.2 q hq) (fun q hq h => ⟨hq.1, fun y hy => hskew _ _ (h y hy)⟩)
  have hle : U ≤ perpIn f X (perpIn f X U) := fun u hu =>
    ⟨hUX hu, fun x hx => hskew _ _ (hx.2 u hu)⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hpos : 0 < Nat.card (perpIn f X U) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card (perpIn f X U) * Nat.card (perpIn f X (perpIn f X U))
      ≤ Nat.card X * Nat.card (perpIn f X X) := hα
    _ ≤ Nat.card U * Nat.card (perpIn f X U) := hβ
    _ = Nat.card (perpIn f X U) * Nat.card U := mul_comm _ _

end Perp

section Sec

variable {G : Type*} [Group G] {V : Type} [CommGroup V] (ρ : G →* MulAut V)

theorem range_le_stabSub {U : Subgroup V} (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    ρ.range ≤ stabSub U := by
  rintro _ ⟨g, rfl⟩ u
  refine ⟨fun h => ?_, hU g u⟩
  have := hU g⁻¹ _ h
  rwa [map_inv, MulAut.inv_apply_self] at this

variable {W U : Subgroup V} (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U)

@[expose] def secRho : G →* MulAut (Sec W U) :=
  (B5.secHom ρ.range (range_le_stabSub ρ hW) (range_le_stabSub ρ hU)).comp ρ.rangeRestrict

theorem secRho_mk (g : G) (w : ↥W) :
    secRho ρ hW hU g (QuotientGroup.mk w) = QuotientGroup.mk ⟨ρ g w, hW g w w.2⟩ :=
  rfl

theorem range_secRho : (secRho ρ hW hU).range = autSec ρ.range W U := by
  rw [secRho, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ρ.rangeRestrict_surjective,
    ← MonoidHom.range_eq_map, B5.range_secHom]

theorem secRho_eq_one_iff (g : G) : secRho ρ hW hU g = 1 ↔ ρ g ∈ centSec W U := by
  rw [← MonoidHom.mem_ker]
  exact B5.mem_ker_secHom ρ.range (range_le_stabSub ρ hW) (range_le_stabSub ρ hU)
    (ρ.rangeRestrict g)

omit [Group G] in
theorem sec_sq (hV2 : ∀ v : V, v ^ 2 = 1) (s : Sec W U) : s ^ 2 = 1 := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  rw [← QuotientGroup.mk_pow]
  have : w ^ 2 = 1 := Subtype.ext (by simpa using hV2 (w : V))
  rw [this, QuotientGroup.mk_one]

theorem sec_nt {g : G} {w : V} (hw : w ∈ W) (hg : ρ g w * w⁻¹ ∉ U) :
    ∃ g s, secRho ρ hW hU g s ≠ s := by
  refine ⟨g, QuotientGroup.mk ⟨w, hw⟩, fun h => hg ?_⟩
  rw [secRho_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at h
  simpa using h

theorem sec_irr (hUW : U ≤ W)
    (hirr : ∀ J : Subgroup V, (∀ g, ∀ w ∈ J, ρ g w ∈ J) → U ≤ J → J ≤ W → J = U ∨ J = W) :
    ∀ J' : Subgroup (Sec W U), (∀ g, ∀ s ∈ J', secRho ρ hW hU g s ∈ J') →
      J' = ⊥ ∨ J' = ⊤ := by
  intro J' hJ'
  set π : ↥W →* Sec W U := QuotientGroup.mk' (U.subgroupOf W) with hπ
  set J : Subgroup V := (J'.comap π).map W.subtype with hJ
  have hJinv : ∀ g, ∀ w ∈ J, ρ g w ∈ J := by
    intro g w hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.1 hw
    exact Subgroup.mem_map.2 ⟨⟨ρ g w', hW g w' w'.2⟩, hJ' g _ hw', rfl⟩
  have hUJ : U ≤ J := by
    intro u hu
    refine Subgroup.mem_map.2 ⟨⟨u, hUW hu⟩, ?_, rfl⟩
    show π ⟨u, hUW hu⟩ ∈ J'
    have : π ⟨u, hUW hu⟩ = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hu
    rw [this]
    exact J'.one_mem
  rcases hirr J hJinv hUJ (Subgroup.map_subtype_le _) with h | h
  · left
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective s
    have hw : (w' : V) ∈ J := Subgroup.mem_map.2 ⟨w', hs, rfl⟩
    rw [h] at hw
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hw
  · right
    rw [eq_top_iff]
    intro s _
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective s
    have hw : (w' : V) ∈ J := by rw [h]; exact w'.2
    obtain ⟨w2, hw2, hw3⟩ := Subgroup.mem_map.1 hw
    have : w2 = w' := Subtype.ext hw3
    rw [this] at hw2
    exact hw2

include hW hU in
theorem isElemAbelian2_autSec {A : Subgroup (MulAut V)} (hAK : A ≤ ρ.range)
    (hAe : IsElemAbelian2 A) : IsElemAbelian2 (autSec A W U) := by
  have hmap := B5.map_secHom_eq_autSec ρ.range (range_le_stabSub ρ hW) (range_le_stabSub ρ hU) hAK
  rw [← hmap]
  constructor
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAe.1 _ ha _ hb)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 _ ha)
    rw [this, map_one]

theorem sec_ff [Finite V] (hUW : U ≤ W) {A : Subgroup (MulAut V)} (hAK : A ≤ ρ.range)
    (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hcard : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) (hfaith : A ⊓ centSec W U = ⊥) :
    IsFFModule (secRho ρ hW hU).range := by
  have hAW : A ≤ stabSub W := hAK.trans (range_le_stabSub ρ hW)
  have hAU : A ≤ stabSub U := hAK.trans (range_le_stabSub ρ hU)
  have hcA : Nat.card (autSec A W U) = Nat.card A := by
    have := card_autSec_mul hAW hAU
    rwa [hfaith, Subgroup.card_bot, mul_one] at this
  refine ⟨autSec A W U, ?_, ?_, isElemAbelian2_autSec ρ hW hU hAK hAe, ?_⟩
  · rw [range_secRho]
    exact autSec_mono hAK W U
  · intro hbot
    apply hA1
    have h1 : Nat.card A = 1 := by rw [← hcA, hbot, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq A h1
  · have h1 := card_sup_mul_card_inf W (fixV A)
    have h2 : Nat.card ↥(W ⊔ fixV A) ≤ Nat.card V := Subgroup.card_le_card_group _
    have h3 := card_inf_fixV_le_autSec hUW hAW (U := U)
    have h4 : Nat.card ↥(U ⊓ fixV A) ≤ Nat.card U := Subgroup.card_le_of_le inf_le_left
    have h5 := card_sec_mul hUW
    have hC : 0 < Nat.card (fixV A) := Nat.card_pos
    have hW' : Nat.card W ≤ Nat.card A * Nat.card ↥(W ⊓ fixV A) := by
      refine Nat.le_of_mul_le_mul_right ?_ hC
      calc Nat.card W * Nat.card (fixV A) = Nat.card ↥(W ⊔ fixV A) * Nat.card ↥(W ⊓ fixV A) :=
            h1.symm
        _ ≤ Nat.card V * Nat.card ↥(W ⊓ fixV A) := Nat.mul_le_mul_right _ h2
        _ ≤ (Nat.card A * Nat.card (fixV A)) * Nat.card ↥(W ⊓ fixV A) :=
            Nat.mul_le_mul_right _ hcard
        _ = Nat.card A * Nat.card ↥(W ⊓ fixV A) * Nat.card (fixV A) := by ring
    have hU0 : 0 < Nat.card U := Nat.card_pos
    rw [hcA]
    refine Nat.le_of_mul_le_mul_right ?_ hU0
    calc Nat.card (Sec W U) * Nat.card U = Nat.card W := h5
      _ ≤ Nat.card A * Nat.card ↥(W ⊓ fixV A) := hW'
      _ ≤ Nat.card A * (Nat.card (fixV (autSec A W U)) * Nat.card U) :=
          Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ h4))
      _ = Nat.card A * Nat.card (fixV (autSec A W U)) * Nat.card U := by ring

end Sec

section SecForm

variable {V : Type} [CommGroup V] {W U : Subgroup V} {M : Type*} [CommGroup M]

@[expose] def secForm (f : V →* V →* M) (h1 : ∀ u ∈ U, ∀ w ∈ W, f u w = 1)
    (h2 : ∀ w ∈ W, ∀ u ∈ U, f w u = 1) : Sec W U →* Sec W U →* M :=
  QuotientGroup.lift (U.subgroupOf W)
    { toFun := fun w => QuotientGroup.lift (U.subgroupOf W) ((f w).comp W.subtype)
          (fun x hx => by
            rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
            exact h2 w w.2 x (Subgroup.mem_subgroupOf.mp hx))
      map_one' := by
        apply QuotientGroup.monoidHom_ext
        ext x
        simp
      map_mul' := fun w w' => by
        apply QuotientGroup.monoidHom_ext
        ext x
        simp }
    (fun u hu => by
      rw [MonoidHom.mem_ker]
      apply QuotientGroup.monoidHom_ext
      ext x
      simpa using h1 u (Subgroup.mem_subgroupOf.mp hu) x x.2)

theorem secForm_mk (f : V →* V →* M) (h1 : ∀ u ∈ U, ∀ w ∈ W, f u w = 1)
    (h2 : ∀ w ∈ W, ∀ u ∈ U, f w u = 1) (w w' : ↥W) :
    secForm f h1 h2 (QuotientGroup.mk w) (QuotientGroup.mk w') = f w w' :=
  rfl

theorem secForm_inv {G : Type*} [Group G] (ρ : G →* MulAut V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (f : V →* V →* M) (h1 : ∀ u ∈ U, ∀ w ∈ W, f u w = 1)
    (h2 : ∀ w ∈ W, ∀ u ∈ U, f w u = 1) (hf : ∀ g v w, f (ρ g v) (ρ g w) = f v w) (g : G)
    (s s' : Sec W U) :
    secForm f h1 h2 (secRho ρ hW hU g s) (secRho ρ hW hU g s') = secForm f h1 h2 s s' := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective s'
  rw [secRho_mk, secRho_mk, secForm_mk, secForm_mk]
  exact hf g w w'

theorem eq_one_of_secForm_eq_one {f : V →* V →* M} {h1 : ∀ u ∈ U, ∀ w ∈ W, f u w = 1}
    {h2 : ∀ w ∈ W, ∀ u ∈ U, f w u = 1} (h : secForm f h1 h2 = 1) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W) : f w w' = 1 := by
  have := DFunLike.congr_fun (DFunLike.congr_fun h (QuotientGroup.mk ⟨w, hw⟩))
    (QuotientGroup.mk ⟨w', hw'⟩)
  rw [secForm_mk] at this
  exact this

end SecForm

section SecPre

variable {V : Type} [CommGroup V]

@[expose] def secPre (W U : Subgroup V) (Q : Subgroup (Sec W U)) : Subgroup V :=
  (Q.comap (QuotientGroup.mk' (U.subgroupOf W))).map W.subtype

theorem mem_secPre {W U : Subgroup V} {Q : Subgroup (Sec W U)} {v : V} :
    v ∈ secPre W U Q ↔ ∃ hv : v ∈ W, (QuotientGroup.mk ⟨v, hv⟩ : Sec W U) ∈ Q := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hv, hq⟩
    exact ⟨⟨v, hv⟩, hq, rfl⟩

theorem secPre_le (W U : Subgroup V) (Q : Subgroup (Sec W U)) : secPre W U Q ≤ W :=
  Subgroup.map_subtype_le _

theorem le_secPre {W U : Subgroup V} (hUW : U ≤ W) (Q : Subgroup (Sec W U)) :
    U ≤ secPre W U Q := fun u hu => mem_secPre.mpr ⟨hUW hu, by
  rw [(QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hu)]
  exact Q.one_mem⟩

theorem card_secPre [Finite V] {W U : Subgroup V} (hUW : U ≤ W) (Q : Subgroup (Sec W U)) :
    Nat.card Q * Nat.card U = Nat.card (secPre W U Q) := by
  set q := QuotientGroup.mk' (U.subgroupOf W) with hq
  have h1 := B1More.card_map_mul_card_inf_ker (Q.comap q) q
  have hmap : (Q.comap q).map q = Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Q
  have hker : Q.comap q ⊓ q.ker = U.subgroupOf W := by
    rw [hq, QuotientGroup.ker_mk', inf_eq_right]
    intro w hw
    show (QuotientGroup.mk w : Sec W U) ∈ Q
    rw [(QuotientGroup.eq_one_iff w).mpr hw]
    exact Q.one_mem
  have hcU : Nat.card ↥(U.subgroupOf W) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW).toEquiv
  have hcP : Nat.card ↥(Q.comap q) = Nat.card (secPre W U Q) :=
    (Subgroup.card_map_of_injective W.subtype_injective).symm
  rw [hmap, hker, hcU, hcP] at h1
  exact h1

theorem exists_of_mem_autSec {A : Subgroup (MulAut V)} {W U : Subgroup V}
    {φ : MulAut (Sec W U)} (hφ : φ ∈ autSec A W U) :
    ∃ a ∈ A, ∃ ha : a ∈ stabSub W, ∀ w : ↥W,
      φ (QuotientGroup.mk w) = QuotientGroup.mk ⟨a w, (ha w).2 w.2⟩ := by
  obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
  obtain ⟨g', hg'A, hg'⟩ := mem_autSub.mp hg
  refine ⟨g', hg'A, g'.2, fun w => ?_⟩
  rw [quotHom_mk]
  congr 1
  apply Subtype.ext
  rw [← hg']
  rfl

theorem secPre_commV_le {A : Subgroup (MulAut V)} {W U Z : Subgroup V} (hUZ : U ≤ Z)
    (hgen : ∀ a ∈ A, ∀ w ∈ W, a w * w⁻¹ ∈ Z) : secPre W U (commV (autSec A W U)) ≤ Z := by
  intro q hq
  obtain ⟨hqW, hqs⟩ := mem_secPre.mp hq
  suffices key : ∀ s ∈ commV (autSec A W U), ∀ w : ↥W, QuotientGroup.mk w = s →
      (w : V) ∈ Z from key _ hqs ⟨q, hqW⟩ rfl
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨φ, hφ, s₀, rfl⟩ := hz
    obtain ⟨a, haA, ha, hφa⟩ := exists_of_mem_autSec hφ
    obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective s₀
    intro w hw
    rw [hφa, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mk_eq_mk_iff,
      Subgroup.mem_subgroupOf] at hw
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hw
    have hw' : (w : V) = (a w₀ * (w₀ : V)⁻¹) * ((w : V) * (a w₀ * (w₀ : V)⁻¹)⁻¹) := by
      rw [mul_left_comm, mul_inv_cancel, mul_one]
    rw [hw']
    exact Z.mul_mem (hgen a haA w₀ w₀.2) (hUZ hw)
  | one =>
    intro w hw
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hw
    exact hUZ hw
  | mul s₁ s₂ _ _ ih₁ ih₂ =>
    intro w hw
    obtain ⟨w₁, hw₁⟩ := QuotientGroup.mk_surjective s₁
    have hw₂ : (QuotientGroup.mk (w₁⁻¹ * w) : Sec W U) = s₂ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw₁, hw, inv_mul_cancel_left]
    have e : (w : V) = (w₁ : V) * ((w₁⁻¹ * w : ↥W) : V) := by simp
    rw [e]
    exact Z.mul_mem (ih₁ w₁ hw₁) (ih₂ _ hw₂)
  | inv s _ ih =>
    intro w hw
    have h1 := Z.inv_mem (ih w⁻¹ (by rw [QuotientGroup.mk_inv, hw, inv_inv]))
    simpa using h1

end SecPre

section SecCard

variable {V : Type} [CommGroup V]

theorem map_secRho {G : Type*} [Group G] (ρ : G →* MulAut V) {W U : Subgroup V}
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (A : Subgroup G) :
    A.map (secRho ρ hW hU) = autSec (A.map ρ) W U := by
  rw [secRho, ← Subgroup.map_map, ← B5.map_secHom_eq_autSec ρ.range (range_le_stabSub ρ hW)
    (range_le_stabSub ρ hU) (Subgroup.map_le_range ρ A)]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨a, ha, rfl⟩
  · intro hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_subgroupOf.mp hx
    exact ⟨a, ha, Subtype.ext hax⟩

theorem sec_card_le {G : Type*} [Group G] [Finite V] (ρ : G →* MulAut V) {W U : Subgroup V}
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (hUW : U ≤ W)
    (A : Subgroup G) {a : ℕ} (hcard : Nat.card V ≤ a * Nat.card (fixV (A.map ρ))) :
    Nat.card (Sec W U) ≤ a * Nat.card (fixV (A.map (secRho ρ hW hU))) := by
  rw [map_secRho]
  have hAW : A.map ρ ≤ stabSub W := (Subgroup.map_le_range ρ A).trans (range_le_stabSub ρ hW)
  have h1 := card_sup_mul_card_inf W (fixV (A.map ρ))
  have h2 : Nat.card ↥(W ⊔ fixV (A.map ρ)) ≤ Nat.card V := Subgroup.card_le_card_group _
  have h3 := card_inf_fixV_le_autSec hUW hAW (U := U)
  have h4 : Nat.card ↥(U ⊓ fixV (A.map ρ)) ≤ Nat.card U := Subgroup.card_le_of_le inf_le_left
  have h5 := card_sec_mul hUW
  have hC : 0 < Nat.card (fixV (A.map ρ)) := Nat.card_pos
  have hW' : Nat.card W ≤ a * Nat.card ↥(W ⊓ fixV (A.map ρ)) := by
    refine Nat.le_of_mul_le_mul_right ?_ hC
    calc Nat.card W * Nat.card (fixV (A.map ρ))
        = Nat.card ↥(W ⊔ fixV (A.map ρ)) * Nat.card ↥(W ⊓ fixV (A.map ρ)) := h1.symm
      _ ≤ Nat.card V * Nat.card ↥(W ⊓ fixV (A.map ρ)) := Nat.mul_le_mul_right _ h2
      _ ≤ (a * Nat.card (fixV (A.map ρ))) * Nat.card ↥(W ⊓ fixV (A.map ρ)) :=
          Nat.mul_le_mul_right _ hcard
      _ = a * Nat.card ↥(W ⊓ fixV (A.map ρ)) * Nat.card (fixV (A.map ρ)) := by ring
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card U)
  calc Nat.card (Sec W U) * Nat.card U = Nat.card W := h5
    _ ≤ a * Nat.card ↥(W ⊓ fixV (A.map ρ)) := hW'
    _ ≤ a * (Nat.card (fixV (autSec (A.map ρ) W U)) * Nat.card U) :=
        Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ h4))
    _ = a * Nat.card (fixV (autSec (A.map ρ) W U)) * Nat.card U := by ring

theorem card_sec_bot [Finite V] (W : Subgroup V) : Nat.card (Sec W ⊥) = Nat.card W := by
  have := card_sec_mul (bot_le : (⊥ : Subgroup V) ≤ W)
  rwa [Subgroup.card_bot, mul_one] at this

end SecCard

end CFSG.Quasithin.MS93.S46
