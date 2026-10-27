module

public import CFSG.Quasithin.Vol2.E2NineMembers
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

omit [Finite G] in
theorem star_mono {A B : Subgroup G} (hAB : A ≤ B) : star M H A ≤ star M H B :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H hAB)

omit [Finite G] in
theorem starMap_mem_star {X : Subgroup G} {x : G} (hxH : x ∈ H) (hx : x ∈ X) :
    E2P.starMap M H ⟨x, hxH⟩ ∈ star M H X :=
  ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

omit [Finite G] in
theorem star_sup {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    star M H (A ⊔ B) = star M H A ⊔ star M H B := by
  simp only [star]
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
theorem star_conjSub {X : Subgroup G} {g : G} (hg : g ∈ H) :
    star M H (conjSub g X) = conjSub (E2P.starMap M H ⟨g, hg⟩) (star M H X) := by
  ext y
  constructor
  · rintro ⟨⟨w, hwH⟩, hw, rfl⟩
    replace hw : w ∈ conjSub g X := hw
    rw [mem_conjSub] at hw
    rw [mem_conjSub]
    have hu : g⁻¹ * w * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hwH) hg
    refine ⟨⟨g⁻¹ * w * g, hu⟩, Subgroup.mem_subgroupOf.2 hw, ?_⟩
    have e : (⟨g⁻¹ * w * g, hu⟩ : H) = (⟨g, hg⟩ : H)⁻¹ * ⟨w, hwH⟩ * ⟨g, hg⟩ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv]
  · intro hy
    rw [mem_conjSub] at hy
    obtain ⟨⟨u, huH⟩, hu, hue⟩ := hy
    replace hu : u ∈ X := hu
    have hw : g * u * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg huH) (H.inv_mem hg)
    refine ⟨⟨g * u * g⁻¹, hw⟩, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · rw [mem_conjSub]
      simpa [mul_assoc] using hu
    · have e : (⟨g * u * g⁻¹, hw⟩ : H) = ⟨g, hg⟩ * ⟨u, huH⟩ * (⟨g, hg⟩ : H)⁻¹ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_inv, hue]
      group

omit [Finite G] in
theorem starMap_mem_normalizer {A : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    E2P.starMap M H ⟨x, hxH⟩ ∈ Subgroup.normalizer (star M H A : Set (StarQuot M H)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨⟨z, hzH⟩, rfl⟩ := E2P.starMap_surjective M H y
  have hmem : ∀ w : H, (w : G) ∈ A → E2P.starMap M H w ∈ star M H A := fun w hw =>
    ⟨w, Subgroup.mem_subgroupOf.2 hw, rfl⟩
  have hconj : E2P.starMap M H ⟨x, hxH⟩ * E2P.starMap M H ⟨z, hzH⟩ *
      (E2P.starMap M H ⟨x, hxH⟩)⁻¹ = E2P.starMap M H ⟨x * z * x⁻¹,
        H.mul_mem (H.mul_mem hxH hzH) (H.inv_mem hxH)⟩ := by
    rw [← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [hconj]
  constructor
  · rintro ⟨w, hw, hwz⟩
    replace hw : (w : G) ∈ A := hw
    have hk : (w : G)⁻¹ * z ∈ kerIn M H := by
      have := QuotientGroup.eq.1 hwz
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hxw : x * w * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hx _).mp hw
    refine ⟨⟨x * w * x⁻¹, H.mul_mem (H.mul_mem hxH w.2) (H.inv_mem hxH)⟩,
      Subgroup.mem_subgroupOf.2 hxw, ?_⟩
    show QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have : x * (w : G)⁻¹ * z * x⁻¹ ∈ kerIn M H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H hxH) _).mp hk
      simpa [mul_assoc] using this
    simpa [mul_assoc] using this
  · rintro ⟨w, hw, hwz⟩
    replace hw : (w : G) ∈ A := hw
    have hk : (w : G)⁻¹ * (x * z * x⁻¹) ∈ kerIn M H := by
      have := QuotientGroup.eq.1 hwz
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hxw : x⁻¹ * w * x ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp hw
      simpa using this
    refine ⟨⟨x⁻¹ * w * x, H.mul_mem (H.mul_mem (H.inv_mem hxH) w.2) hxH⟩,
      Subgroup.mem_subgroupOf.2 hxw, ?_⟩
    show QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have : x⁻¹ * ((w : G)⁻¹ * (x * z * x⁻¹)) * x ∈ kerIn M H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H (H.inv_mem hxH)) _).mp hk
      simpa [mul_assoc] using this
    simpa [mul_assoc] using this

theorem Hyp28.star (h : Hyp28 H T M V) (hsq : SQTKGroup ↥(⊤ : Subgroup (StarQuot M H))) :
    Hyp28 (⊤ : Subgroup (StarQuot M H)) (star M H T) (star M H M) (star M H V) := by
  have := E2P.finite_starQuot M H
  have hVH := h.le_H
  refine ⟨E2P.minParabolic_star h.minParabolic, hsq, star_mono h.le_T, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨t, htH⟩, ht, rfl⟩
    exact starMap_mem_normalizer htH (h.normal_T (Subgroup.mem_subgroupOf.1 ht))
  · refine ⟨⟨⟨fun ⟨a, x, hx, hxa⟩ ⟨b, y, hy, hyb⟩ => Subtype.ext ?_⟩⟩, ?_⟩
    · subst hxa hyb
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      have hc := h.elem.1.is_comm.comm (⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩ : V)
        ⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩
      exact Subtype.ext (congrArg (fun z : V => (z : G)) hc)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact h.elem.2 _ (Subgroup.mem_subgroupOf.1 hx))
      rw [this, map_one]
  · refine (star_mono h.le_pCoreOf).trans ?_
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (star_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 M)) ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_injective
        (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans
          h.minParabolic.maximal.1.le)).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe _).injective |>.map _)
    rintro _ ⟨⟨m, hmH⟩, hm, rfl⟩
    exact starMap_mem_normalizer hmH
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (Subgroup.mem_subgroupOf.1 hm))
  · rw [E2P.kerIn_star]
    intro hle
    apply h.not_le_kerIn
    intro v hv
    have h1 := hle (starMap_mem_star (M := M) (hVH hv) hv)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact h1

theorem isSylowTwoOf_of_sup {S N Y : Subgroup G} (hSY : S ≤ Y) (hNY : N ≤ Y)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hS : IsPGroup 2 S)
    (hSNsyl : IsSylowTwoOf (S ⊓ N) N) (hodd : ¬ 2 ∣ (S ⊔ N).relIndex Y) : IsSylowTwoOf S Y := by
  refine ⟨hSY, hS, ?_⟩
  have h1 : S.relIndex Y = S.relIndex (S ⊔ N) * (S ⊔ N).relIndex Y :=
    (Subgroup.relIndex_mul_relIndex S (S ⊔ N) Y le_sup_left (sup_le hSY hNY)).symm
  have h2 : S.relIndex (S ⊔ N) = (S ⊓ N).relIndex N := by
    have e1 := Subgroup.relIndex_mul_card (H := S) (K := S ⊔ N)
    have e2 := Subgroup.relIndex_mul_card (H := N) (K := S ⊔ N)
    have e3 := Subgroup.relIndex_mul_card (H := N) (K := S)
    have e4 := Subgroup.relIndex_mul_card (H := S ⊓ N) (K := N)
    rw [inf_of_le_left le_sup_left] at e1
    rw [inf_of_le_left le_sup_right] at e2
    rw [inf_comm] at e3
    rw [inf_of_le_left inf_le_right] at e4
    have e5 : N.relIndex (S ⊔ N) = N.relIndex S := A4.relIndex_sup_eq_of_le_normalizer' hSN
    have hpos : 0 < N.relIndex S := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at e3
      exact (Nat.card_pos (α := S)).ne' e3.symm
    have hcard : 0 < Nat.card (S ⊓ N : Subgroup G) := Nat.card_pos
    have h3 : S.relIndex (S ⊔ N) * (N.relIndex S * Nat.card (S ⊓ N : Subgroup G)) =
        N.relIndex S * ((S ⊓ N).relIndex N * Nat.card (S ⊓ N : Subgroup G)) := by
      rw [e3, e4, e1, ← e5, e2]
    have h4 : S.relIndex (S ⊔ N) * Nat.card (S ⊓ N : Subgroup G) =
        (S ⊓ N).relIndex N * Nat.card (S ⊓ N : Subgroup G) := by
      have : N.relIndex S * (S.relIndex (S ⊔ N) * Nat.card (S ⊓ N : Subgroup G)) =
          N.relIndex S * ((S ⊓ N).relIndex N * Nat.card (S ⊓ N : Subgroup G)) := by
        rw [← h3]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    exact Nat.eq_of_mul_eq_mul_right hcard h4
  rw [show (S.subgroupOf Y).index = S.relIndex Y from rfl, h1, h2]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
  · exact hSNsyl.2.2 h
  · exact hodd h

omit [Finite G] in
theorem relIndex_star {A B : Subgroup G} (hJA : kerIn M H ≤ A) (hJB : kerIn M H ≤ B)
    (hBH : B ≤ H) : (star M H A).relIndex (star M H B) = A.relIndex B := by
  simp only [star]
  rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk',
    sup_of_le_left (Subgroup.subgroupOf_mono H hJA),
    sup_of_le_left (Subgroup.subgroupOf_mono H hJB), Subgroup.relIndex_subgroupOf hBH]

omit [Finite G] in
theorem star_kerIn : star M H (kerIn M H) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hx

theorem exists_pullback (h : Hyp28 H T M V) {I₀ : Subgroup (StarQuot M H)}
    (hgen : ∃ g ∈ I₀, I₀ = star M H V ⊔ conjSub g (star M H V))
    (hsyl₀ : IsSylowTwoOf (star M H T ⊓ I₀) I₀) :
    ∃ g ∈ H, g ∈ V ⊔ conjSub g V ∧ star M H (V ⊔ conjSub g V) = I₀ ∧
      IsSylowTwoOf (T ⊓ (V ⊔ conjSub g V)) (V ⊔ conjSub g V) := by
  have hVH := h.le_H
  have hconjH : ∀ {x : G}, x ∈ H → conjSub x V ≤ H := by
    intro x hx w hw
    rw [mem_conjSub] at hw
    have := H.mul_mem (H.mul_mem hx (hVH hw)) (H.inv_mem hx)
    simpa [mul_assoc] using this
  have hstarI : ∀ {x : G} (hx : x ∈ H), star M H (V ⊔ conjSub x V) =
      star M H V ⊔ conjSub (E2P.starMap M H ⟨x, hx⟩) (star M H V) := by
    intro x hx
    rw [star_sup hVH (hconjH hx), star_conjSub hx]
  obtain ⟨g₀, hg₀, hI₀eq⟩ := hgen
  obtain ⟨⟨g₁, hg₁H⟩, rfl⟩ := E2P.starMap_surjective M H g₀
  set P : G → Prop := fun x => ∃ hx : x ∈ H, E2P.starMap M H ⟨x, hx⟩ ∈ I₀ ∧
    star M H (V ⊔ conjSub x V) = I₀ with hPdef
  have hP₁ : P g₁ := ⟨hg₁H, hg₀, by rw [hstarI hg₁H, hI₀eq]⟩
  obtain ⟨g, ⟨hgH, hgI₀, hgI⟩, hgmin⟩ :=
    (measure fun x : G => Nat.card (V ⊔ conjSub x V : Subgroup G)).wf.has_min {x | P x} ⟨g₁, hP₁⟩
  set I := V ⊔ conjSub g V with hIdef
  have hIH : I ≤ H := sup_le hVH (hconjH hgH)
  have hgI' : E2P.starMap M H ⟨g, hgH⟩ ∈ star M H I := by rw [hgI]; exact hgI₀
  obtain ⟨⟨g₂, hg₂H⟩, hg₂I, hg₂e⟩ := hgI'
  replace hg₂I : g₂ ∈ I := hg₂I
  have hI₂ : V ⊔ conjSub g₂ V ≤ I := by
    refine sup_le le_sup_left ?_
    intro w hw
    rw [mem_conjSub] at hw
    have := I.mul_mem (I.mul_mem hg₂I (le_sup_left (a := V) hw)) (I.inv_mem hg₂I)
    simpa [mul_assoc] using this
  have hP₂ : P g₂ := ⟨hg₂H, by rw [hg₂e]; exact hgI₀, by
    rw [hstarI hg₂H, hg₂e, ← hstarI hgH, hgI]⟩
  have hI₂eq : V ⊔ conjSub g₂ V = I := by
    refine Subgroup.eq_of_le_of_card_ge hI₂ ?_
    by_contra hlt
    push Not at hlt
    exact hgmin g₂ hP₂ hlt
  refine ⟨g₂, hg₂H, by rw [hI₂eq]; exact hg₂I, by rw [hI₂eq]; exact hgI, ?_⟩
  rw [hI₂eq]
  set J := kerIn M H with hJ
  set I₁ := I ⊔ J with hI₁
  have hJH : J ≤ H := h.minParabolic.kerIn_le_H
  have hI₁H : I₁ ≤ H := sup_le hIH hJH
  have hJn : H ≤ Subgroup.normalizer (J : Set G) := le_normalizer_kerIn M H
  have hstarI₁ : star M H I₁ = I₀ := by
    rw [star_sup hIH hJH, star_kerIn, sup_bot_eq, hgI]
  have hTI₁ : star M H (T ⊓ I₁) = star M H T ⊓ I₀ := by
    refine le_antisymm (le_inf (star_mono inf_le_left) (hstarI₁ ▸ star_mono inf_le_right)) ?_
    rintro y ⟨⟨⟨t, htH⟩, ht, rfl⟩, hyI₀⟩
    rw [← hstarI₁] at hyI₀
    obtain ⟨⟨x, hxH⟩, hx, hxe⟩ := hyI₀
    replace hx : x ∈ I₁ := hx
    have hk : x⁻¹ * t ∈ J := by
      have := QuotientGroup.eq.1 hxe
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have htI₁ : t ∈ I₁ := by
      have e : t = x * (x⁻¹ * t) := by group
      rw [e]
      exact I₁.mul_mem hx (le_sup_right (b := J) hk)
    exact ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 ht, htI₁⟩, rfl⟩
  have hsyl₁ : IsSylowTwoOf (T ⊓ I₁) I₁ := by
    refine isSylowTwoOf_of_sup inf_le_right le_sup_right
      ((inf_le_right.trans hI₁H).trans hJn) (h.minParabolic.isSylow.2.1.to_le inf_le_left) ?_ ?_
    · rw [inf_assoc, inf_of_le_right (le_sup_right : J ≤ I₁)]
      exact isSylowTwoOf_inf_normal h.minParabolic.isSylow hJH hJn
    · rw [← relIndex_star le_sup_right le_sup_right hI₁H, star_sup (inf_le_right.trans hI₁H) hJH,
        star_kerIn, sup_bot_eq, hTI₁, hstarI₁]
      exact hsyl₀.2.2
  set Q := pCoreOf 2 H with hQ
  have hQN : Q ≤ Subgroup.normalizer (I : Set G) := pCoreOf_le_normalizer h hgH
  have hcomm : ⁅J, I⁆ ≤ Q := commutator_kerIn_le h hgH
  have hX : Q ⊔ I ≤ I₁ := sup_le (h.minParabolic.pCoreOf_le_kerIn.trans le_sup_right) le_sup_left
  have hXn : I₁ ≤ Subgroup.normalizer ((Q ⊔ I : Subgroup G) : Set G) := by
    have hJX : J ≤ Subgroup.normalizer ((Q ⊔ I : Subgroup G) : Set G) := by
      intro j hj
      have key : ∀ j ∈ J, ∀ x ∈ Q ⊔ I, j * x * j⁻¹ ∈ Q ⊔ I := by
        intro j hj x hx
        have hjQ : j ∈ Subgroup.normalizer (Q : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hJH hj)
        have hjI : ∀ i ∈ I, j * i * j⁻¹ ∈ Q ⊔ I := by
          intro i hi
          have hc : j * i * j⁻¹ * i⁻¹ ∈ Q := by
            have := hcomm (Subgroup.commutator_mem_commutator hj hi)
            rwa [commutatorElement_def] at this
          have e : j * i * j⁻¹ = (j * i * j⁻¹ * i⁻¹) * i := by group
          rw [e]
          exact Subgroup.mul_mem_sup hc hi
        have hle : Q ⊔ I ≤ (Q ⊔ I).comap (MulAut.conj j).toMonoidHom := by
          refine sup_le (fun q hq => ?_) (fun i hi => hjI i hi)
          exact le_sup_left (b := I) ((Subgroup.mem_normalizer_iff.mp hjQ q).mp hq)
        exact hle hx
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => key j hj x hx, fun hx => ?_⟩
      have := key j⁻¹ (J.inv_mem hj) _ hx
      simpa [mul_assoc] using this
    have hIX : I ≤ Subgroup.normalizer ((Q ⊔ I : Subgroup G) : Set G) := by
      intro i hi
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        (Subgroup.mem_normalizer_iff_map_conj_eq).1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hIH hi)),
        (Subgroup.mem_normalizer_iff_map_conj_eq).1 (Subgroup.le_normalizer hi)]
    exact sup_le hIX hJX
  have hsylX := isSylowTwoOf_inf_normal hsyl₁ hX hXn
  have hIXn : Q ⊔ I ≤ Subgroup.normalizer (I : Set G) := sup_le hQN Subgroup.le_normalizer
  have hsylI := isSylowTwoOf_inf_normal hsylX le_sup_right hIXn
  have heq : T ⊓ I₁ ⊓ (Q ⊔ I) ⊓ I = T ⊓ I := by
    rw [inf_assoc, inf_assoc, inf_of_le_right (le_sup_right : I ≤ Q ⊔ I),
      inf_of_le_right (le_sup_left : I ≤ I₁)]
  rwa [heq] at hsylI

omit [Finite G] in
theorem mem_kerIn_iff_star {I : Subgroup G} (hIH : I ≤ H) {x : G} (hxI : x ∈ I) :
    x ∈ kerIn (M ⊓ I) I ↔
      E2P.starMap M H ⟨x, hIH hxI⟩ ∈ kerIn (star M H M ⊓ star M H I) (star M H I) := by
  constructor
  · intro hx b hb
    obtain ⟨⟨y, hyH⟩, hy, rfl⟩ := hb
    replace hy : y ∈ I := hy
    have h1 := hx y hy
    have e : E2P.starMap M H ⟨y, hyH⟩ * E2P.starMap M H ⟨x, hIH hxI⟩ *
        (E2P.starMap M H ⟨y, hyH⟩)⁻¹ = E2P.starMap M H ⟨y * x * y⁻¹, hIH h1.2⟩ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e]
    exact ⟨starMap_mem_star (hIH h1.2) h1.1, starMap_mem_star (hIH h1.2) h1.2⟩
  · intro hx y hy
    have hyx : y * x * y⁻¹ ∈ I := I.mul_mem (I.mul_mem hy hxI) (I.inv_mem hy)
    refine ⟨?_, hyx⟩
    have h1 := hx (E2P.starMap M H ⟨y, hIH hy⟩) (starMap_mem_star (hIH hy) hy)
    have e : E2P.starMap M H ⟨y, hIH hy⟩ * E2P.starMap M H ⟨x, hIH hxI⟩ *
        (E2P.starMap M H ⟨y, hIH hy⟩)⁻¹ = E2P.starMap M H ⟨y * x * y⁻¹, hIH hyx⟩ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    rw [e] at h1
    obtain ⟨⟨m, hmH⟩, hm, hme⟩ := h1.1
    replace hm : m ∈ M := hm
    have hk : m⁻¹ * (y * x * y⁻¹) ∈ kerIn M H := by
      have := QuotientGroup.eq.1 hme
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have e2 : y * x * y⁻¹ = m * (m⁻¹ * (y * x * y⁻¹)) := by group
    rw [e2]
    exact M.mul_mem hm (kerIn_le hk)

theorem isSylowTwoOf_pCoreOf_kerIn_of_star (h : Hyp28 H T M V) {g : G} (hgH : g ∈ H)
    (hcl : IsSylowTwoOf (pCoreOf 2 (kerIn (star M H M ⊓ star M H (V ⊔ conjSub g V))
        (star M H (V ⊔ conjSub g V))))
      (kerIn (star M H M ⊓ star M H (V ⊔ conjSub g V)) (star M H (V ⊔ conjSub g V)))) :
    IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ (V ⊔ conjSub g V)) (V ⊔ conjSub g V)))
      (kerIn (M ⊓ (V ⊔ conjSub g V)) (V ⊔ conjSub g V)) := by
  set I := V ⊔ conjSub g V with hIdef
  have hVH := h.le_H
  have hIH : I ≤ H := sup_le hVH (by
    intro w hw
    rw [mem_conjSub] at hw
    have := H.mul_mem (H.mul_mem hgH (hVH hw)) (H.inv_mem hgH)
    simpa [mul_assoc] using this)
  set K := kerIn (M ⊓ I) I with hK
  set K₀ := kerIn (star M H M ⊓ star M H I) (star M H I) with hK₀
  set P₀ := pCoreOf 2 K₀ with hP₀
  set J := kerIn M H with hJ
  set Q := pCoreOf 2 H with hQ
  have hKI : K ≤ I := kerIn_le.trans inf_le_right
  have hKH : K ≤ H := hKI.trans hIH
  have hcomm : ⁅J, I⁆ ≤ Q := commutator_kerIn_le h hgH
  set R : Subgroup G := K ⊓ ((P₀.comap (E2P.starMap M H)).map H.subtype) with hR
  have hmemR : ∀ {x : G} (hx : x ∈ K), x ∈ R ↔ E2P.starMap M H ⟨x, hKH hx⟩ ∈ P₀ := by
    intro x hx
    constructor
    · rintro ⟨-, ⟨y, hy, hyx⟩⟩
      have : y = ⟨x, hKH hx⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hP
      exact ⟨hx, ⟨⟨x, hKH hx⟩, hP, rfl⟩⟩
  have hRK : R ≤ K := inf_le_left
  have hstarK : ∀ {x : G} (hx : x ∈ K), E2P.starMap M H ⟨x, hKH hx⟩ ∈ K₀ := fun hx =>
    (mem_kerIn_iff_star hIH (hKI hx)).1 hx
  have hRn : K ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ k ∈ K, ∀ x ∈ R, k * x * k⁻¹ ∈ R := by
      intro k hk x hx
      have hxK := hRK hx
      have hy : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)
      rw [hmemR hy]
      have hxP := (hmemR hxK).1 hx
      have e : E2P.starMap M H ⟨k * x * k⁻¹, hKH hy⟩ =
          E2P.starMap M H ⟨k, hKH hk⟩ * E2P.starMap M H ⟨x, hKH hxK⟩ *
            (E2P.starMap M H ⟨k, hKH hk⟩)⁻¹ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀ (hstarK hk)) _).mp hxP
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have := key k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hRH : R ≤ H := hRK.trans hKH
  obtain ⟨S, hS, -⟩ := B6.exists_isSylowTwoOf_ge (X := ⊥) (J := R) IsPGroup.of_bot bot_le
  have hQRS : Q ⊓ R ≤ S := by
    refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf hS)
    intro r hr
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hRH hr), Subgroup.le_normalizer hr⟩
  have hJS : R ⊓ J ≤ Subgroup.normalizer (S : Set G) := by
    have key : ∀ j ∈ R ⊓ J, ∀ x ∈ S, j * x * j⁻¹ ∈ S := by
      intro j hj x hx
      have hxR : x ∈ R := hS.1 hx
      have hc : j * x * j⁻¹ * x⁻¹ ∈ Q ⊓ R := by
        refine ⟨?_, R.mul_mem (R.mul_mem (R.mul_mem hj.1 hxR) (R.inv_mem hj.1)) (R.inv_mem hxR)⟩
        have := hcomm (Subgroup.commutator_mem_commutator hj.2 (hKI (hRK hxR)))
        rwa [commutatorElement_def] at this
      have e : j * x * j⁻¹ = (j * x * j⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact S.mul_mem (hQRS hc) hx
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key j hj x hx, fun hx => ?_⟩
    have := key j⁻¹ ((R ⊓ J).inv_mem hj) _ hx
    simpa [mul_assoc] using this
  have hRJn : ((R ⊓ J).subgroupOf R).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro r hr
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hr, le_normalizer_kerIn M H (hRH hr)⟩
  have h2grp : IsPGroup 2 (↥R ⧸ (R ⊓ J).subgroupOf R) := by
    intro z
    obtain ⟨⟨x, hxR⟩, rfl⟩ := QuotientGroup.mk_surjective z
    have hxP := (hmemR (hRK hxR)).1 hxR
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀) ⟨_, hxP⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h1 : E2P.starMap M H ⟨x ^ 2 ^ k, H.pow_mem (hRH hxR) _⟩ = 1 := by
      have : (⟨x ^ 2 ^ k, H.pow_mem (hRH hxR) _⟩ : H) = ⟨x, hRH hxR⟩ ^ 2 ^ k := Subtype.ext rfl
      rw [this, map_pow]
      simpa using congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact ⟨R.pow_mem hxR _, h1⟩
  have hidx2 : ∃ n : ℕ, (R ⊓ J).relIndex R = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2grp
    exact ⟨n, by rw [Subgroup.relIndex, Subgroup.index, hn]⟩
  have hW : R ≤ (R ⊓ J) ⊔ S := by
    have hWR : (R ⊓ J) ⊔ S ≤ R := sup_le inf_le_left hS.1
    rw [← Subgroup.relIndex_eq_one]
    obtain ⟨n, hn⟩ := hidx2
    have h1 : ((R ⊓ J) ⊔ S).relIndex R ∣ 2 ^ n :=
      hn ▸ Subgroup.relIndex_dvd_of_le_left R le_sup_left
    have h2 : ((R ⊓ J) ⊔ S).relIndex R ∣ S.relIndex R :=
      Subgroup.relIndex_dvd_of_le_left R le_sup_right
    have hodd : ¬ 2 ∣ S.relIndex R := hS.2.2
    obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases m with _ | m
    · simpa using hmeq
    · exfalso
      apply hodd
      rw [hmeq] at h2
      exact (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans h2
  have hSn : R ≤ Subgroup.normalizer (S : Set G) :=
    hW.trans (sup_le hJS Subgroup.le_normalizer)
  have hSR : IsSylowTwoOf (pCoreOf 2 R) R := by
    have heq : pCoreOf 2 R = S := le_antisymm (B6.pCoreOf_two_le_of_isSylowTwoOf hS)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS.1 hSn hS.2.1)
    rw [heq]
    exact hS
  have hKRn : (R.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).2 hRn
  have hP₀n : (P₀.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 K₀)).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀)
  set m := (P₀.subgroupOf K₀).index with hm
  have hmodd : ¬ 2 ∣ m := hcl.2.2
  have hpowR : ∀ x (hx : x ∈ K), x ^ m ∈ R := by
    intro x hx
    have hyK₀ := hstarK hx
    have h1 : ((⟨_, hyK₀⟩ : K₀) : ↥K₀ ⧸ P₀.subgroupOf K₀) ^ m = 1 := by
      rw [hm, Subgroup.index]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have hxm : x ^ m ∈ K := K.pow_mem hx m
    rw [hmemR hxm]
    have e : E2P.starMap M H ⟨x ^ m, hKH hxm⟩ = (E2P.starMap M H ⟨x, hKH hx⟩) ^ m := by
      rw [← map_pow]
      rfl
    rw [e]
    simpa using h1
  have hRKodd : ¬ 2 ∣ R.relIndex K := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥K ⧸ R.subgroupOf K) 2 h2
    obtain ⟨⟨x, hxK⟩, rfl⟩ := QuotientGroup.mk_surjective z
    have hz1 : ((⟨x, hxK⟩ : K) : ↥K ⧸ R.subgroupOf K) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hpowR x hxK
    exact hmodd (hz ▸ orderOf_dvd_of_pow_eq_one hz1)
  have hle : pCoreOf 2 R ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 R).trans hRK)
      (hRn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 R))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R)
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 K, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K, ?_⟩
  intro h2
  have h3 : (pCoreOf 2 K).relIndex K ∣ (pCoreOf 2 R).relIndex R * R.relIndex K := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ (CFSG.LieType.BorelTits.pCoreOf_le 2 R) hRK]
    exact Subgroup.relIndex_dvd_of_le_left K hle
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2.trans h3) with h | h
  · exact hSR.2.2 h
  · exact hRKodd h

section Transport

variable {A B : Type} [Group A] [Group B]

theorem isPSL_of_mulEquiv (e : A ≃* B) {k : ℕ} (h : IsPSL 2 2 k B) : IsPSL 2 2 k A := by
  obtain ⟨hadm, K, h1, h2, hK, ⟨f⟩⟩ := h
  exact ⟨hadm, K, h1, h2, hK, ⟨e.trans f⟩⟩

theorem isPSp4_of_mulEquiv (e : A ≃* B) {k : ℕ} (h : IsPSp4 2 k B) : IsPSp4 2 k A := by
  obtain ⟨hadm, K, h1, h2, hK, ⟨f⟩⟩ := h
  exact ⟨hadm, K, h1, h2, hK, ⟨e.trans f⟩⟩

theorem isSz_of_mulEquiv' (e : A ≃* B) {k : ℕ} (h : IsSz k B) : IsSz k A := by
  obtain ⟨h2, a, ha, K, hK1, hK2, hn, hcard, ⟨f⟩⟩ := h
  exact ⟨h2, a, ha, K, hK1, hK2, hn, hcard, ⟨e.trans f⟩⟩

theorem isSp4C_of_mulEquiv (e : A ≃* B) {k : ℕ} (h : ASInputs.IsSp4C k B) :
    ASInputs.IsSp4C k A := by
  rcases h with h | ⟨hk, ⟨f⟩⟩
  · exact Or.inl (isPSp4_of_mulEquiv e h)
  · exact Or.inr ⟨hk, ⟨e.trans f⟩⟩

theorem isSp4Prime_of_mulEquiv (e : A ≃* B) {n : ℕ} (h : IsSp4Prime n B) : IsSp4Prime n A := by
  unfold IsSp4Prime at h ⊢
  split_ifs at h ⊢ with hn
  · obtain ⟨f⟩ := h
    exact ⟨e.trans f⟩
  · exact isPSp4_of_mulEquiv e h

theorem isSylowTwoOf_map_mulEquiv (e : A ≃* B) {S : Subgroup A} (hS : IsSylowTwoOf S ⊤) :
    IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  have e1 : ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have e2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right _
  have e3 : (S.map e.toMonoidHom).index = S.index := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.index_map_equiv S e
  rw [e1, e3]
  have := hS.2.2
  rwa [e2] at this

theorem map_map_symm_equiv (e : A ≃* B) (Q : Subgroup B) :
    (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
  rw [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B from
    MonoidHom.ext fun x => by simp, Subgroup.map_id]

theorem isBorelIn_of_map_equiv (e : A ≃* B) {X : Subgroup A}
    (h : IsBorelIn ⊤ (X.map e.toMonoidHom)) : IsBorelIn ⊤ X := by
  obtain ⟨S, hS, hSeq⟩ := h
  refine ⟨S.map e.symm.toMonoidHom, isSylowTwoOf_map_mulEquiv e.symm hS, ?_⟩
  rw [top_inf_eq] at hSeq ⊢
  have h1 := congrArg (Subgroup.map e.symm.toMonoidHom) hSeq
  rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A from
    MonoidHom.ext fun x => by simp, Subgroup.map_id] at h1
  rw [h1]
  exact Subgroup.map_equiv_normalizer_eq S e.symm

theorem isParabolic2_map_equiv (e : A ≃* B) {P : Subgroup A} (h : IsParabolic2 ⊤ P) :
    IsParabolic2 ⊤ (P.map e.toMonoidHom) := by
  obtain ⟨-, S, hS, hle⟩ := h
  refine ⟨le_top, S.map e.toMonoidHom, isSylowTwoOf_map_mulEquiv e hS, ?_⟩
  rw [top_inf_eq] at hle ⊢
  rw [← Subgroup.map_equiv_normalizer_eq S e]
  exact Subgroup.map_mono hle

theorem map_symm_map_equiv (e : A ≃* B) (P : Subgroup A) :
    (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  rw [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id A from
    MonoidHom.ext fun x => by simp, Subgroup.map_id]

theorem isMaxParabolic2_map_equiv (e : A ≃* B) {P : Subgroup A} (h : IsMaxParabolic2 ⊤ P) :
    IsMaxParabolic2 ⊤ (P.map e.toMonoidHom) := by
  obtain ⟨hP, hne, hmax⟩ := h
  refine ⟨isParabolic2_map_equiv e hP, fun h1 => hne ?_, fun Q hQ hQne hPQ => ?_⟩
  · rw [← map_symm_map_equiv e P, h1, Subgroup.map_top_of_surjective _ e.symm.surjective]
  · have h2 := hmax (Q.map e.symm.toMonoidHom) (isParabolic2_map_equiv e.symm hQ)
      (fun h3 => hQne (by
        rw [← map_map_symm_equiv e Q, h3, Subgroup.map_top_of_surjective _ e.surjective]))
      (by rw [← map_symm_map_equiv e P]; exact Subgroup.map_mono hPQ)
    rw [← map_map_symm_equiv e Q, h2]

theorem map_inf_centralizer_equiv (e : A ≃* B) (P : Subgroup A) :
    (P ⊓ Subgroup.centralizer (P : Set A)).map e.toMonoidHom =
      P.map e.toMonoidHom ⊓ Subgroup.centralizer (P.map e.toMonoidHom : Set B) := by
  rw [Subgroup.map_inf_eq _ _ _ e.injective]
  congr 1
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    show e z * e x = e x * e z
    rw [← map_mul, ← map_mul, hx z hz]
  · intro hy
    refine ⟨e.symm y, fun z hz => ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e z) ⟨z, hz, rfl⟩

theorem map_twoGen_equiv (e : A ≃* B) (P : Subgroup A) :
    (ASInputs.twoGen P).map e.toMonoidHom = ASInputs.twoGen (P.map e.toMonoidHom) := by
  rw [ASInputs.twoGen, ASInputs.twoGen, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, ⟨hxP, k, hk⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hxP, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hxP, k, e.injective ?_⟩, rfl⟩
    rw [map_pow, hk, map_one]

theorem map_rootGroupOf_equiv (e : A ≃* B) (P : Subgroup A) :
    (ASInputs.rootGroupOf P).map e.toMonoidHom = ASInputs.rootGroupOf (P.map e.toMonoidHom) := by
  rw [ASInputs.rootGroupOf, ASInputs.rootGroupOf, map_inf_centralizer_equiv, map_twoGen_equiv]

end Transport

section Equiv

variable {I : Subgroup G}

@[expose] noncomputable def toStar (M : Subgroup G) (hIH : I ≤ H) : ↥I →* ↥(star M H I) :=
  ((E2P.starMap M H).comp (Subgroup.inclusion hIH)).codRestrict (star M H I)
    fun x => starMap_mem_star (hIH x.2) x.2

omit [Finite G] in
theorem toStar_surjective (hIH : I ≤ H) : Function.Surjective (toStar M hIH) := by
  rintro ⟨y, ⟨x, hx, rfl⟩⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[expose] noncomputable def toStarQuot (M : Subgroup G) (hIH : I ≤ H) :
    ↥I →* StarQuot (star M H M ⊓ star M H I) (star M H I) :=
  (QuotientGroup.mk' _).comp (toStar M hIH)

omit [Finite G] in
theorem ker_toStarQuot (hIH : I ≤ H) :
    (toStarQuot M hIH).ker = (kerIn (M ⊓ I) I).subgroupOf I := by
  ext x
  rw [MonoidHom.mem_ker, toStarQuot, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact (mem_kerIn_iff_star hIH x.2).symm

omit [Finite G] in
theorem toStarQuot_surjective (hIH : I ≤ H) : Function.Surjective (toStarQuot M hIH) :=
  (QuotientGroup.mk'_surjective _).comp (toStar_surjective hIH)

@[expose] noncomputable def starEquiv (M : Subgroup G) (hIH : I ≤ H) :
    StarQuot (M ⊓ I) I ≃* StarQuot (star M H M ⊓ star M H I) (star M H I) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toStarQuot hIH).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toStarQuot_surjective hIH))

omit [Finite G] in
theorem map_starEquiv (hIH : I ≤ H) {X : Subgroup G} (hXI : X ≤ I) :
    (star (M ⊓ I) I X).map (starEquiv M hIH).toMonoidHom =
      star (star M H M ⊓ star M H I) (star M H I) (star M H X) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨toStar M hIH x, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (starMap_mem_star (hIH x.2) (Subgroup.mem_subgroupOf.1 hx))
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨⟨w, hwH⟩, hw, hwy⟩ := Subgroup.mem_subgroupOf.1 hy
    replace hw : w ∈ X := hw
    refine ⟨QuotientGroup.mk' _ (⟨w, hXI hw⟩ : I), ⟨⟨w, hXI hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩,
      ?_⟩
    show toStarQuot M hIH ⟨w, hXI hw⟩ = _
    rw [toStarQuot, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hwy

end Equiv

omit [Finite G] in
noncomputable def starTopEquiv (M H : Subgroup G) :
    StarQuot (star M H M) (⊤ : Subgroup (StarQuot M H)) ≃* StarQuot M H :=
  ((QuotientGroup.quotientMulEquivOfEq (by
    rw [E2P.kerIn_star]; exact Subgroup.bot_subgroupOf _)).trans QuotientGroup.quotientBot).trans
    Subgroup.topEquiv

theorem isSp4Prime_oTwoUpper_of_starTop {n : ℕ}
    (h : IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (StarQuot (star M H M)
      (⊤ : Subgroup (StarQuot M H)))))) :
    IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (StarQuot M H))) := by
  have := E2P.finite_starQuot M H
  set f := starTopEquiv M H
  have hmap : (oTwoUpper (⊤ : Subgroup (StarQuot (star M H M) (⊤ : Subgroup (StarQuot M H))))).map
      f.toMonoidHom = oTwoUpper (⊤ : Subgroup (StarQuot M H)) := by
    rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ f.surjective]
  exact isSp4Prime_of_mulEquiv ((f.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).symm h

theorem exists_isInIHTVC_of_star (h : Hyp28 H T M V)
    (hn : E1.nParam (⊤ : Subgroup (StarQuot M H)) = E1.nParam H) {I₀ : Subgroup (StarQuot M H)}
    (hI₀ : ASInputs.IsInIHTVC ⊤ (star M H T) (star M H M) (star M H V) I₀) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have := E2P.finite_starQuot M H
  obtain ⟨g, hgH, hgI, hIeq, hsyl⟩ := exists_pullback h hI₀.2.1 hI₀.2.2.1
  set I := V ⊔ conjSub g V with hIdef
  have hVH := h.le_H
  have hIH : I ≤ H := sup_le hVH (by
    intro w hw
    rw [mem_conjSub] at hw
    have := H.mul_mem (H.mul_mem hgH (hVH hw)) (H.inv_mem hgH)
    simpa [mul_assoc] using this)
  have hVI : V ≤ I := le_sup_left
  obtain ⟨-, -, -, hcl₀, k, ⟨m, hm⟩, hc⟩ := hI₀
  rw [← hIeq] at hcl₀ hc
  refine ⟨I, hIH, ⟨g, hgI, rfl⟩, hsyl, isSylowTwoOf_pCoreOf_kerIn_of_star h hgH hcl₀, k,
    ⟨m, hn ▸ hm⟩, ?_⟩
  set e := starEquiv M hIH with he
  have hMI : (star (M ⊓ I) I (M ⊓ I)).map e.toMonoidHom =
      star (star M H M ⊓ star M H I) (star M H I) (star M H M ⊓ star M H I) := by
    rw [map_starEquiv hIH inf_le_right, E2P.star_inf_M]
  have hVe : (star (M ⊓ I) I V).map e.toMonoidHom =
      star (star M H M ⊓ star M H I) (star M H I) (star M H V) := map_starEquiv hIH hVI
  rcases hc with ⟨hk, hY, hB⟩ | ⟨hk, p, a, hp, hp2, ha, ⟨d⟩⟩ | ⟨hO, hk, hY, hB, hV, hP⟩
  · refine Or.inl ⟨hk, ?_, isBorelIn_of_map_equiv e (hMI ▸ hB)⟩
    rcases hY with hY | hY
    · exact Or.inl (isPSL_of_mulEquiv e hY)
    · exact Or.inr (isSz_of_mulEquiv' e hY)
  · exact Or.inr (Or.inl ⟨hk, p, a, hp, hp2, ha, ⟨e.trans d⟩⟩)
  · refine Or.inr (Or.inr ⟨?_, hk, isSp4C_of_mulEquiv e hY,
      isBorelIn_of_map_equiv e (hMI ▸ hB), ?_, ?_⟩)
    · obtain ⟨n, hn'⟩ := hO
      exact ⟨n, isSp4Prime_oTwoUpper_of_starTop hn'⟩
    ·
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hTI : (star (M ⊓ I) I (T ⊓ I)).map e.toMonoidHom ≤
          star (star M H M ⊓ star M H I) (star M H I) (star M H T ⊓ star M H I) := by
        rw [map_starEquiv hIH inf_le_right]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono _
          (le_inf (star_mono inf_le_left) (star_mono inf_le_right)))
      have h1 := Subgroup.mem_centralizer_iff.1 (hV (hVe ▸ ⟨x, hx, rfl⟩ : e x ∈ _))
        (e t) (hTI ⟨t, ht, rfl⟩)
      apply e.injective
      rw [map_mul, map_mul]
      exact h1
    ·
      intro P hPmax hMP hVP
      apply hP (P.map e.toMonoidHom) (isMaxParabolic2_map_equiv e hPmax)
        (hMI ▸ Subgroup.map_mono hMP)
      rw [← hVe, ← map_rootGroupOf_equiv]
      exact Subgroup.map_mono hVP

end E2

end CFSG.Quasithin
