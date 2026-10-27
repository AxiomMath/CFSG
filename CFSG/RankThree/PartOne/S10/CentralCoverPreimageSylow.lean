module

public import CFSG.RankThree.PartOne.S10.CentralCoverContract

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace CentralCoverSylow

section Kernel

variable {W K : Type*} [Group W] [Finite W] [Group K]

theorem exists_normal_sylow_of_central_kernel {r : ℕ} (hr : r.Prime) (f : W →* K)
    (hf : Function.Surjective f) (hK : IsPGroup r K) (hker : f.ker ≤ Subgroup.center W) :
    ∃ T : Subgroup W, IsPGroup r T ∧ (∀ S : Subgroup W, IsPGroup r S → S ≤ T) ∧
      T.map f = ⊤ ∧ f.ker ⊔ T = ⊤ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Finite K := Finite.of_surjective f hf
  obtain ⟨P0⟩ : Nonempty (Sylow r W) := inferInstance
  have hTK : (P0 : Subgroup W).map f = ⊤ :=
    ((P0.mapSurjective hf).is_maximal' (hK.to_subgroup ⊤) le_top).symm
  have hsup : f.ker ⊔ (P0 : Subgroup W) = ⊤ := by
    refine eq_top_iff.mpr fun w _ => ?_
    have hw : f w ∈ (P0 : Subgroup W).map f := hTK ▸ Subgroup.mem_top _
    obtain ⟨t, ht, hft⟩ := hw
    have hk : w * t⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hft, mul_inv_cancel]
    have := Subgroup.mul_mem_sup hk ht
    rwa [inv_mul_cancel_right] at this
  have hnormal : (P0 : Subgroup W).Normal := ⟨fun n hn g => by
    have hg : g ∈ f.ker ⊔ (P0 : Subgroup W) := hsup ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
    obtain ⟨k, hk, t, ht, rfl⟩ := hg
    have hkc := Subgroup.mem_center_iff.mp (hker hk)
    have hconj : ∀ x : W, k * x * k⁻¹ = x := fun x => by
      rw [← hkc x]
      group
    have e : k * t * n * (k * t)⁻¹ = k * (t * n * t⁻¹) * k⁻¹ := by group
    rw [e, hconj]
    exact P0.1.mul_mem (P0.1.mul_mem ht hn) (P0.1.inv_mem ht)⟩
  refine ⟨P0, P0.isPGroup', fun S hS => ?_, hTK, hsup⟩
  obtain ⟨Q, hSQ⟩ := hS.exists_le_sylow
  have := Sylow.unique_of_normal P0 hnormal
  rw [Subsingleton.elim Q P0] at hSQ
  exact hSQ

end Kernel

section Preimage

variable {G : Type*} [Group G] [Finite G]

theorem exists_preimage_sylow {r : ℕ} (hr : r.Prime) (U : Subgroup (G ⧸ Subgroup.center G))
    (hU : IsPGroup r U) :
    ∃ T : Subgroup G, T ≤ U.comap (centerQuotientMap G) ∧ IsPGroup r T ∧
      (∀ T' : Subgroup G, T' ≤ U.comap (centerQuotientMap G) → IsPGroup r T' → T' ≤ T) ∧
      T.map (centerQuotientMap G) = U ∧
      U.comap (centerQuotientMap G) = Subgroup.center G ⊔ T := by
  classical
  set q := centerQuotientMap G with hq
  set W := U.comap q with hW
  have hmem : ∀ x : W, q (x : G) ∈ U := fun x => x.2
  let f : W →* U := (q.comp W.subtype).codRestrict U hmem
  have hf : Function.Surjective f := by
    intro u
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) (u : G ⧸ Subgroup.center G)
    have hxW : x ∈ W := by
      rw [hW, Subgroup.mem_comap]
      change (QuotientGroup.mk' (Subgroup.center G)) x ∈ U
      rw [hx]
      exact u.2
    exact ⟨⟨x, hxW⟩, Subtype.ext hx⟩
  have hker : ∀ w : W, w ∈ f.ker ↔ (w : G) ∈ Subgroup.center G := fun w => by
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change q (w : G) = 1 ↔ _
    rw [hq, centerQuotientMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerc : f.ker ≤ Subgroup.center W := fun w hw => by
    have hwc := Subgroup.mem_center_iff.mp ((hker w).mp hw)
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hwc (g : G))
  obtain ⟨TW, hTW2, hTWmax, hTWf, hTWsup⟩ :=
    exists_normal_sylow_of_central_kernel hr f hf hU hkerc
  refine ⟨TW.map W.subtype, Subgroup.map_subtype_le _, hTW2.map _, fun T' hT' hT'2 => ?_, ?_, ?_⟩
  · have h := hTWmax (T'.subgroupOf W) (hT'2.comap_subtype)
    have := Subgroup.map_mono (f := W.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hT'] at this
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      exact w.2
    · intro u hu
      have : (⟨u, hu⟩ : U) ∈ TW.map f := hTWf ▸ Subgroup.mem_top _
      obtain ⟨t, ht, hft⟩ := this
      exact ⟨t, ⟨t, ht, rfl⟩, congrArg Subtype.val hft⟩
  · refine le_antisymm (fun x hx => ?_) (sup_le (fun z hz => ?_) (Subgroup.map_subtype_le _))
    · have hxW : (⟨x, hx⟩ : W) ∈ f.ker ⊔ TW := hTWsup ▸ Subgroup.mem_top _
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hxW
      obtain ⟨k, hk, t, ht, hkt⟩ := hxW
      have hx' : x = (k : G) * (t : G) := congrArg Subtype.val hkt.symm
      rw [hx']
      exact Subgroup.mul_mem_sup ((hker k).mp hk) ⟨t, ht, rfl⟩
    · change q z ∈ U
      rw [hq, centerQuotientMap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
      exact U.one_mem


omit [Finite G] in
theorem preimage_normalizer_eq {r : ℕ} (U : Subgroup (G ⧸ Subgroup.center G)) (T : Subgroup G)
    (hT2 : IsPGroup r T)
    (hTmax : ∀ T' : Subgroup G, T' ≤ U.comap (centerQuotientMap G) → IsPGroup r T' → T' ≤ T)
    (hTU : T.map (centerQuotientMap G) = U) :
    (Subgroup.normalizer (U : Set (G ⧸ Subgroup.center G))).comap (centerQuotientMap G) =
        Subgroup.normalizer (T : Set G) ∧
      (Subgroup.normalizer (T : Set G)).map (centerQuotientMap G) =
        Subgroup.normalizer (U : Set (G ⧸ Subgroup.center G)) ∧
      Subgroup.center G ≤ Subgroup.normalizer (T : Set G) := by
  set q := centerQuotientMap G with hq
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective (Subgroup.center G)
  have key : ∀ y : G, q y ∈ Subgroup.normalizer (U : Set (G ⧸ Subgroup.center G)) →
      ∀ t ∈ T, y * t * y⁻¹ ∈ T := by
    intro y hy t ht
    have hsub : T.map (MulAut.conj y).toMonoidHom ≤ U.comap q := by
      rintro _ ⟨t', ht', rfl⟩
      have h1 : q t' ∈ U := hTU ▸ Subgroup.mem_map_of_mem q ht'
      have h2 := (Subgroup.mem_normalizer_iff.mp hy (q t')).mp h1
      change q (y * t' * y⁻¹) ∈ U
      rwa [map_mul, map_mul, map_inv]
    exact hTmax _ hsub (hT2.map _) ⟨t, ht, rfl⟩
  have hcomap : (Subgroup.normalizer (U : Set (G ⧸ Subgroup.center G))).comap q =
      Subgroup.normalizer (T : Set G) := by
    ext x
    constructor
    · intro hx
      have hxN : q x ∈ Subgroup.normalizer (U : Set (G ⧸ Subgroup.center G)) := hx
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨fun hg => key x hxN g hg, fun hg => ?_⟩
      have hxinv : q x⁻¹ ∈ Subgroup.normalizer (U : Set (G ⧸ Subgroup.center G)) := by
        rw [map_inv]
        exact Subgroup.inv_mem _ hxN
      have := key x⁻¹ hxinv _ hg
      simpa [mul_assoc] using this
    · intro hx
      have h := Subgroup.le_normalizer_map q (Subgroup.mem_map_of_mem q hx)
      rw [hTU] at h
      exact h
  refine ⟨hcomap, ?_, Subgroup.center_le_normalizer (T : Set G)⟩
  rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hsurj]

end Preimage


section PCore

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_center_le_centerPCore {p : ℕ} (hp : p.Prime) (S : Subgroup G) (hS : IsPGroup p S) :
    S ⊓ Subgroup.center G ≤ centerPCore p G := by
  have : Fact p.Prime := ⟨hp⟩
  set Z := Subgroup.center G with hZ
  set S' := (S ⊓ Z).subgroupOf Z with hS'
  have hSn : S'.Normal := ⟨fun n hn g => by
    have hg : g * n = n * g := Subtype.ext (Subgroup.mem_center_iff.mp n.2 (g : G))
    rw [hg, mul_inv_cancel_right]
    exact hn⟩
  have hSp : IsPGroup p S' := (hS.to_le inf_le_left).comap_subtype
  have hSle : S' ≤ CFSG.pCore p ↥Z := le_sSup ⟨hSn, hSp⟩
  have := Subgroup.map_mono (f := Z.subtype) hSle
  rwa [hS', Subgroup.map_subgroupOf_eq_of_le inf_le_right] at this

omit [Finite G] in
theorem inf_center_eq_centerPCore {p : ℕ} (hp : p.Prime) (E : Subgroup (G ⧸ Subgroup.center G))
    (P : Subgroup G) (hP : IsPGroup p P)
    (hmax : ∀ P' : Subgroup G, P' ≤ E.comap (centerQuotientMap G) → IsPGroup p P' → P' ≤ P) :
    P ⊓ Subgroup.center G = centerPCore p G := by
  apply le_antisymm (inf_center_le_centerPCore hp P hP)
  refine le_inf (hmax _ ?_ ?_) (Subgroup.map_subtype_le _)
  · intro x hx
    have hxZ : x ∈ Subgroup.center G := Subgroup.map_subtype_le _ hx
    change centerQuotientMap G x ∈ E
    rw [centerQuotientMap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hxZ]
    exact E.one_mem
  · exact (CFSG.pCore_isPGroup (p := p)).map _

end PCore

end CentralCoverSylow

end CFSG.RankThree.PartOne
