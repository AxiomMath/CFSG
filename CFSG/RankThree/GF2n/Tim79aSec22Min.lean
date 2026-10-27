module

public import CFSG.RankThree.GF2n.Tim79aSec2Central

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

theorem le_normalizer_closure {S : Set G} {K : Subgroup G}
    (h : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ Subgroup.closure S) :
    K ≤ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ k ∈ K, ∀ r ∈ Subgroup.closure S, k * r * k⁻¹ ∈ Subgroup.closure S := by
    intro k hk r hr
    induction hr using Subgroup.closure_induction with
    | mem z hz => exact h k hk z hz
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show k * (a * b) * k⁻¹ = k * a * k⁻¹ * (k * b * k⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  intro k hk
  refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨key k hk r, fun hr => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ hr
  simpa [mul_assoc] using this

variable {M V Q P H : Subgroup G} [Finite G]

@[expose] def x1Of (V H : Subgroup G) (d : G) : Subgroup G :=
  Subgroup.closure ({y | ∃ x ∈ xOf V H, y = x * d * x⁻¹} ∪ (wOf V H : Set G))

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem x1Of_le_xOf {d : G} (hd : d ∈ V) : x1Of V H d ≤ xOf V H := by
  have hVΩ : V ∈ omegaOf V H := ⟨1, H.one_mem, (conjSubgroup_one V).symm⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro y (⟨x, hx, rfl⟩ | hy)
  · exact (xOf V H).mul_mem ((xOf V H).mul_mem hx (le_xOf hVΩ hd)) ((xOf V H).inv_mem hx)
  · exact wOf_le_xOf V H hy

theorem wOf_le_x1Of (d : G) : wOf V H ≤ x1Of V H d := fun _ hw =>
  Subgroup.subset_closure (Or.inr hw)

theorem self_mem_x1Of {d : G} (hd : d ∈ V) : d ∈ x1Of V H d :=
  Subgroup.subset_closure (Or.inl ⟨1, (xOf V H).one_mem, by group⟩)

theorem xOf_le_normalizer_x1Of {d : G} (_hd : d ∈ V) :
    xOf V H ≤ Subgroup.normalizer (x1Of V H d : Set G) := by
  refine le_normalizer_closure ?_
  rintro k hk s (⟨x, hx, rfl⟩ | hs)
  · exact Subgroup.subset_closure (Or.inl ⟨k * x, (xOf V H).mul_mem hk hx, by group⟩)
  · exact Subgroup.subset_closure (Or.inr
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hk)) s).mp hs))

theorem P_le_normalizer_x1Of {d : G} (hd : d ∈ V) :
    P ≤ Subgroup.normalizer (x1Of V H d : Set G) := by
  refine le_normalizer_closure ?_
  rintro p hp s (⟨x, hx, rfl⟩ | hs)
  · have hpH : p ∈ H := hc.PleH hp
    have hpd : p * d * p⁻¹ = d := by
      have : d * p = p * d := Subgroup.mem_centralizer_iff.mp (hc.hP ▸ hp : p ∈ Q ⊓
        Subgroup.centralizer (V : Set G)).2 d hd
      rw [mul_inv_eq_iff_eq_mul]; exact this.symm
    have hx' : p * x * p⁻¹ ∈ xOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H hpH) x).mp hx
    refine Subgroup.subset_closure (Or.inl ⟨p * x * p⁻¹, hx', ?_⟩)
    calc p * (x * d * x⁻¹) * p⁻¹ = (p * x * p⁻¹) * (p * d * p⁻¹) * (p * x * p⁻¹)⁻¹ := by group
      _ = (p * x * p⁻¹) * d * (p * x * p⁻¹)⁻¹ := by rw [hpd]
  · exact Subgroup.subset_closure (Or.inr
      ((Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (hc.PleH hp)) s).mp hs))

theorem x1Of_sup_P_eq_H {d : G} (hdV : d ∈ V) (hdW : d ∉ wOf V H) :
    x1Of V H d ⊔ P = H := by
  set X₁ := x1Of V H d with hX₁
  have hPN : P ≤ Subgroup.normalizer (X₁ : Set G) := hc.P_le_normalizer_x1Of hdV
  have hX₁H : X₁ ≤ H := (hc.x1Of_le_xOf hdV).trans (xOf_le_H hc.V_le_H)
  have hKH : X₁ ⊔ P ≤ H := sup_le hX₁H hc.PleH
  by_contra hne
  have hlt : X₁ ⊔ P < H := lt_of_le_of_ne hKH hne
  have hKnorm : X₁ ⊔ P ≤ Subgroup.normalizer (wOf V H : Set G) := fun k hk =>
    H_le_normalizer_wOf V H (hKH hk)
  have hWK : wOf V H ≤ inSubgroup (pCore 2) (X₁ ⊔ P) :=
    Tim78.le_inSubgroup_pCore (hc.wOf_le_x1Of d |>.trans le_sup_left) hKnorm
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian)
  have hO : inSubgroup (pCore 2) (X₁ ⊔ P) ≠ ⊥ := by
    intro hbot
    apply hc.V_inf_wOf_ne_bot
    rw [eq_bot_iff]
    intro x hx
    have := hWK hx.2
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hV := hc.min (X₁ ⊔ P) le_sup_right hO hlt
  have hdK : d ∈ inSubgroup (pCore 2) (X₁ ⊔ P) := hV hdV
  have hT2 : IsPGroup 2 ↥(inSubgroup (pCore 2) (X₁ ⊔ P) ⊓ X₁ : Subgroup G) :=
    (inSubgroup_pCore_two (X₁ ⊔ P)).1.to_le inf_le_left
  have hTn : X₁ ≤ Subgroup.normalizer
      ((inSubgroup (pCore 2) (X₁ ⊔ P) ⊓ X₁ : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf ((inSubgroup_pCore_two (X₁ ⊔ P)).2.2 (Subgroup.mem_sup_left hk))
      (Subgroup.le_normalizer hk)
  have hTO : inSubgroup (pCore 2) (X₁ ⊔ P) ⊓ X₁ ≤ inSubgroup (pCore 2) X₁ :=
    Tim78.le_inSubgroup_pCore inf_le_right hTn hT2
  have hX₁X : X₁ ≤ xOf V H := hc.x1Of_le_xOf hdV
  have hOX : inSubgroup (pCore 2) X₁ ≤ inSubgroup (pCore 2) (xOf V H) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 X₁ (xOf V H) hX₁X
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hX₁X).2 (hc.xOf_le_normalizer_x1Of hdV))
  have hdO : d ∈ inSubgroup (pCore 2) H :=
    hc.pCore_xOf_le_pCore (hOX (hTO ⟨hdK, hc.self_mem_x1Of hdV⟩))
  have : d ∈ V ⊓ wOf V H := by
    rw [hc.V_inf_wOf_eq]; exact ⟨hdV, hdO⟩
  exact hdW this.2

theorem xOf_sup_P_eq_H : xOf V H ⊔ P = H := by
  obtain ⟨d, hdV, hdW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  refine le_antisymm (sup_le (xOf_le_H hc.V_le_H) hc.PleH) ?_
  calc H = x1Of V H d ⊔ P := (hc.x1Of_sup_P_eq_H hdV hdW).symm
    _ ≤ xOf V H ⊔ P := sup_le_sup_right (hc.x1Of_le_xOf hdV) P

theorem exists_conj_xOf {h : G} (hh : h ∈ H) :
    ∃ x ∈ xOf V H, conjSubgroup h V = conjSubgroup x V := by
  have hh' : h ∈ xOf V H ⊔ P := by rw [hc.xOf_sup_P_eq_H]; exact hh
  obtain ⟨x, hx, p, hp, rfl⟩ := exists_mul_of_mem_sup
    (fun p hp => H_le_normalizer_xOf V H (hc.PleH hp)) hh'
  refine ⟨x, hx, ?_⟩
  have hpN : p ∈ Subgroup.normalizer (V : Set G) :=
    hc.normalizer_eq ▸ (inSubgroup_pCore_two M).2.1 (hc.hQ ▸ hc.P_le_Q hp)
  rw [← conjSubgroup_conjSubgroup, mem_normalizer_iff_conjSubgroup_eq.mp hpN]

theorem dbarOf_not_mem_pCoreOf :
    ∀ y ∈ dbarOf V H, y ∉ pCoreOf 2 (barOf V H (xOf V H)) := by
  intro y hy hyO
  obtain ⟨d, ⟨hd1, U, hU, hdU⟩, hdW, rfl⟩ := mem_dbarOf_iff.mp hy
  set X := xOf V H with hX
  set Xb := barOf V H X with hXb
  have hker : IsPGroup 2 (piBar V H).ker := by
    have e : (piBar V H).ker = (wOf V H).subgroupOf H := QuotientGroup.ker_mk' _
    rw [e]
    exact (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hc.wOf_isElemAbelian).of_equiv
      (Subgroup.subgroupOfEquivOfLe (wOf_le_H V H)).symm
  have hT'2 : IsPGroup 2 ((pCoreOf 2 Xb).comap (piBar V H)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Xb).comap_of_ker_isPGroup (piBar V H) hker
  set T : Subgroup G := ((pCoreOf 2 Xb).comap (piBar V H)).map H.subtype with hT
  have hT2 : IsPGroup 2 ↥T := hT'2.map H.subtype
  have hTmem : ∀ t : ↥H, (t : G) ∈ T ↔ piBar V H t ∈ pCoreOf 2 Xb := by
    intro t
    rw [hT, Subgroup.mem_map]
    constructor
    · rintro ⟨t', ht', hte⟩
      have : t' = t := Subtype.ext hte
      subst this
      exact ht'
    · intro ht; exact ⟨t, ht, rfl⟩
  have hTH : ∀ t ∈ T, t ∈ H := by
    intro t ht
    obtain ⟨t', -, rfl⟩ := Subgroup.mem_map.mp ht
    exact t'.2
  have hTX : T ≤ X := by
    intro t ht
    have htH : t ∈ H := hTH t ht
    have h1 := (hTmem ⟨t, htH⟩).1 ht
    obtain ⟨x, hxX, hx⟩ := mem_barOf_iff.mp ((CFSG.LieType.BorelTits.pCoreOf_le (r := 2) Xb) h1)
    have hw : ((x⁻¹ * ⟨t, htH⟩ : ↥H) : G) ∈ wOf V H := by
      apply (piBar_eq_one_iff _).1
      rw [map_mul, map_inv, hx]; simp
    have : t = (x : G) * ((x : G)⁻¹ * t) := by group
    rw [this]
    exact X.mul_mem hxX (wOf_le_xOf V H (by simpa using hw))
  have key : ∀ x ∈ X, ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    intro x hx t ht
    have hxH : x ∈ H := xOf_le_H hc.V_le_H hx
    have htH : t ∈ H := hTH t ht
    have hxb : piBar V H ⟨x, hxH⟩ ∈ Xb := mem_barOf_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) Xb hxb
    have hxtH : x * t * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH htH) (H.inv_mem hxH)
    have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp ((hTmem ⟨t, htH⟩).1 ht)
    have e : piBar V H ⟨x * t * x⁻¹, hxtH⟩ =
        piBar V H ⟨x, hxH⟩ * piBar V H ⟨t, htH⟩ * (piBar V H ⟨x, hxH⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    exact (hTmem ⟨x * t * x⁻¹, hxtH⟩).2 (by rw [e]; exact h2)
  have hXT : X ≤ Subgroup.normalizer (T : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun t => ⟨key x hx t, fun ht => by
      have := key x⁻¹ (X.inv_mem hx) _ ht
      simpa [mul_assoc] using this⟩
  have hTO : T ≤ inSubgroup (pCore 2) X := Tim78.le_inSubgroup_pCore hTX hXT hT2
  have hdT : (d : G) ∈ T := (hTmem d).2 hyO
  have hdO : (d : G) ∈ inSubgroup (pCore 2) H := hc.pCore_xOf_le_pCore (hTO hdT)
  exact hdW (inf_pCore_le_wOf hU ⟨hdU, hdO⟩)

end MinCex

end CFSG.RankThree.GF2n.Tim79a
