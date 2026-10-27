module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Basic
public import CFSG.Timmesfeld.RootInvolutionCenter
public import CFSG.CGT.Timmesfeld75.StrongClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

private theorem timti_map_conj_aux {G H : Type*} [Group G] [Group H] (π : G →* H)
    (A : Subgroup G) (g : G) :
    (A.map π).map (MulAut.conj (π g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map π := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : G →* H => Subgroup.map f A)
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem timti_map_conj {G H : Type*} [Group G] [Group H] (π : G →* H)
    (A : Subgroup G) (g : G) :
    conjSubgroup (A.map π) (π g) = (conjSubgroup A g).map π := by
  have h := timti_map_conj_aux π A g⁻¹
  simp only [conjSubgroup] at h ⊢
  rwa [map_inv] at h

private theorem timti_map_conj75 {G H : Type*} [Group G] [Group H] (π : G →* H)
    (A : Subgroup G) (g : G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup (π g) (A.map π) =
      (CFSG.CGT.Timmesfeld75.conjSubgroup g A).map π := by
  have h := timti_map_conj_aux π A g
  simp only [CFSG.CGT.Timmesfeld75.conjSubgroup] at h ⊢
  exact h

private theorem timti_isPGroup_of_elemAbelian (h : Hyp X S) : IsPGroup 2 ↥S := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro x
  exact ⟨1, by simpa using orderOf_dvd_of_pow_eq_one (h.elem.2 x x.2)⟩

namespace Hyp

theorem card_map_center (h : Hyp X S) :
    Nat.card (S.map (QuotientGroup.mk' (Subgroup.center X))) = Nat.card S := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  change Nat.card (S.map π) = Nat.card S
  have hmap : (π.comp S.subtype).range = S.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hmap]
  refine (Nat.card_congr (MonoidHom.ofInjective (f := π.comp S.subtype) ?_)).symm
  intro x y hxy
  have hxy' : π (x : X) = π (y : X) := hxy
  have h1 : π ((x : X)⁻¹ * (y : X)) = 1 := by
    rw [map_mul, map_inv, hxy', inv_mul_cancel]
  have hmem : (x : X)⁻¹ * (y : X) ∈ Subgroup.center X :=
    (QuotientGroup.eq_one_iff _).mp h1
  have hS : (x : X)⁻¹ * (y : X) ∈ S := S.mul_mem (S.inv_mem x.2) y.2
  have hbot : (x : X)⁻¹ * (y : X) ∈ (⊥ : Subgroup X) := by
    rw [← h.inf_center_eq_bot]
    exact Subgroup.mem_inf.mpr ⟨hS, hmem⟩
  have hxy1 : (x : X)⁻¹ * (y : X) = 1 := Subgroup.mem_bot.mp hbot
  refine Subtype.ext ?_
  have hc := congrArg (fun w : X => (x : X) * w) hxy1
  have hc' : (y : X) = (x : X) := by simpa using hc
  exact hc'.symm

theorem isElemAbelian_map_center (h : Hyp X S) :
    IsElemAbelian 2 (S.map (QuotientGroup.mk' (Subgroup.center X))) := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  change IsElemAbelian 2 (S.map π)
  refine ⟨?_, ?_⟩
  · haveI : IsMulCommutative ↥S := h.elem.1
    infer_instance
  · rintro x ⟨s, hs, rfl⟩
    rw [← map_pow, h.elem.2 s hs, map_one]

theorem isTI_map_center (h : Hyp X S) :
    CFSG.CGT.Timmesfeld75.IsTI (S.map (QuotientGroup.mk' (Subgroup.center X))) := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  change CFSG.CGT.Timmesfeld75.IsTI (S.map π)
  intro g
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) g
  rcases Subgroup.bot_or_exists_ne_one
      (S.map π ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (π g₀) (S.map π)) with
    hbot | ⟨x, hx, hx1⟩
  · exact Or.inl hbot
  · right
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hxT
    obtain ⟨y, hy, hy_eq⟩ := Subgroup.mem_map.mp hxC
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    have hzu : π (g₀ * t * g₀⁻¹) = π s := by
      rw [← hy_eq]
      simp [MulAut.conj_apply]
    obtain ⟨z, hz, hzx⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := Subgroup.center X)).mp hzu
    have hs2 : s ^ 2 = 1 := h.elem.2 s hs
    have hu2 : (g₀ * t * g₀⁻¹) ^ 2 = 1 := by
      have ht2 : t ^ 2 = 1 := h.elem.2 t ht
      have hmap2 : (MulAut.conj g₀) (t ^ 2) = 1 := by rw [ht2, map_one]
      rw [map_pow, MulAut.conj_apply] at hmap2
      exact hmap2
    have hzs : (g₀ * t * g₀⁻¹) * z = z * (g₀ * t * g₀⁻¹) :=
      Subgroup.mem_center_iff.mp hz (g₀ * t * g₀⁻¹)
    have hu_s : (g₀ * t * g₀⁻¹) * s = s * (g₀ * t * g₀⁻¹) := by
      have hs_eq : s = (g₀ * t * g₀⁻¹) * z := hzx.symm
      calc (g₀ * t * g₀⁻¹) * s
          = (g₀ * t * g₀⁻¹) * ((g₀ * t * g₀⁻¹) * z) := by rw [hs_eq]
        _ = ((g₀ * t * g₀⁻¹) * (g₀ * t * g₀⁻¹)) * z := by rw [← mul_assoc]
        _ = z := by rw [← pow_two, hu2, one_mul]
        _ = ((g₀ * t * g₀⁻¹) * z) * (g₀ * t * g₀⁻¹) := by
              rw [hzs, mul_assoc, ← pow_two, hu2, mul_one]
        _ = s * (g₀ * t * g₀⁻¹) := by rw [← hs_eq]
    have hcomm : Commute (g₀ * t * g₀⁻¹) s := hu_s
    have hz2 : z ^ 2 = 1 := by
      have hz_eq : z = (g₀ * t * g₀⁻¹)⁻¹ * s := by
        rw [hzx.symm, inv_mul_cancel_left]
      rw [hz_eq, Commute.mul_pow hcomm.inv_left, inv_pow, hu2, inv_one, hs2, mul_one]
    have hz1 : z = 1 := by
      have hdiv2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have hdivZ : orderOf z ∣ Nat.card (Subgroup.center X) :=
        Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        rw [h1] at hdivZ
        exact (Nat.not_even_iff_odd.mpr h.odd_card_center) (even_iff_two_dvd.mpr hdivZ)
    have hs_eq_u : s = g₀ * t * g₀⁻¹ := by
      rw [hzx.symm, hz1, mul_one]
    have hs1 : s ≠ 1 := by
      intro h1
      exact hx1 (by rw [h1, map_one])
    have hs_mem : s ∈ S ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g₀ S := by
      refine Subgroup.mem_inf.mpr ⟨hs, ?_⟩
      rw [hs_eq_u]
      exact Subgroup.mem_map.mpr ⟨t, ht, by simp [MulAut.conj_apply]⟩
    have hle : S ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g₀ S := by
      rcases h.ti g₀ with hbot' | hsup
      · exfalso
        have : s ∈ (⊥ : Subgroup X) := hbot' ▸ hs_mem
        exact hs1 (Subgroup.mem_bot.mp this)
      · calc S = S ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g₀ S := hsup.symm
          _ ≤ CFSG.CGT.Timmesfeld75.conjSubgroup g₀ S := inf_le_right
    exact inf_eq_left.mpr
      ((Subgroup.map_mono hle).trans_eq (timti_map_conj75 π S g₀).symm)

theorem mem_image_dSet_of_mem_map (h : Hyp X S) {a : X ⧸ Subgroup.center X}
    (ha : a ∈ S.map (QuotientGroup.mk' (Subgroup.center X))) (ha1 : a ≠ 1) :
    a ∈ QuotientGroup.mk' (Subgroup.center X) '' dSet S := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
  refine ⟨s, mem_dSet_of_mem hs ?_, rfl⟩
  intro hs1
  exact ha1 (by rw [hs1, map_one])

theorem classD_map_center (h : Hyp X S) :
    CFSG.CGT.Timmesfeld75.classD (S.map (QuotientGroup.mk' (Subgroup.center X))) =
      QuotientGroup.mk' (Subgroup.center X) '' dSet S := by
  ext x
  constructor
  · rintro ⟨g, t, ht, ht1, rfl⟩
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) g
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    have hs1 : s ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
    refine ⟨g₀⁻¹ * s * g₀, ?_, ?_⟩
    · simpa using conj_mem_dSet g₀⁻¹ (mem_dSet_of_mem hs hs1)
    · simp [map_mul, map_inv]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hxS, hx1, hxy⟩ := mem_dSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    refine ⟨(QuotientGroup.mk' (Subgroup.center X) c)⁻¹,
      QuotientGroup.mk' (Subgroup.center X) x,
      Subgroup.mem_map.mpr ⟨x, hxS, rfl⟩, ?_, ?_⟩
    · intro h1
      exact h.not_mem_center (mem_dSet_of_mem hxS hx1) ((QuotientGroup.eq_one_iff x).1 h1)
    · rw [← hc]
      simp [map_mul, map_inv]

theorem isRootInvolutionSet_image (h : Hyp X S) :
    CFSG.Timmesfeld.IsRootInvolutionSet (QuotientGroup.mk' (Subgroup.center X) '' dSet S) := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  change CFSG.Timmesfeld.IsRootInvolutionSet (π '' dSet S)
  have hset : {x : X | x ∈ dSet S ∧ π x ≠ 1} = dSet S := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, fun h1 =>
      h.not_mem_center hx ((QuotientGroup.eq_one_iff x).1 h1)⟩⟩
  have hroot := CFSG.Timmesfeld.isRootInvolutionSet_image_ne_one π h.root
  rwa [hset] at hroot

theorem eq_bot_of_normal_isSolvable_quot (h : Hyp X S) (N : Subgroup (X ⧸ Subgroup.center X))
    (hN : N.Normal) (hs : Group.IsSolvable N) : N = ⊥ := by
  haveI := hN
  exact CFSG.Timmesfeld.solvable_normal_eq_bot_quotient_center h.le_center_of_isSolvable N hs

private theorem timti_isPGroup_sup_conj (h : Hyp X S) (g₀ : X)
    (h2 : IsPGroup 2 ↥(S.map (QuotientGroup.mk' (Subgroup.center X)) ⊔
      conjSubgroup (S.map (QuotientGroup.mk' (Subgroup.center X)))
        (QuotientGroup.mk' (Subgroup.center X) g₀))) :
    IsPGroup 2 ↥(S ⊔ conjSubgroup S g₀) := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  change IsPGroup 2 ↥(S.map π ⊔ conjSubgroup (S.map π) (π g₀)) at h2
  let H : Subgroup X := S ⊔ conjSubgroup S g₀
  have hHmap : H.map π = S.map π ⊔ conjSubgroup (S.map π) (π g₀) := by
    show (S ⊔ conjSubgroup S g₀).map π = _
    rw [Subgroup.map_sup, timti_map_conj π S g₀]
  have h2' : IsPGroup 2 ↥(H.map π) := hHmap ▸ h2
  haveI : Group.IsNilpotent ↥((π.domRestrict H).range) := by
    rw [MonoidHom.domRestrict_range]
    exact IsPGroup.isNilpotent h2'
  have hker : (π.domRestrict H).ker ≤ Subgroup.center H := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by
      have hz' : (z : X) ∈ Subgroup.center X := Subgroup.mem_subgroupOf.mp hz
      have := Subgroup.mem_center_iff.mp hz' (y : X)
      simpa using this)
  haveI : Group.IsNilpotent H :=
    Subgroup.isNilpotent_of_ker_le_center ((π.domRestrict H).rangeRestrict) (by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker)
  have hSsub : IsPGroup 2 ↥(S.subgroupOf H) := by
    rw [← Subgroup.comap_subtype S H]
    exact (timti_isPGroup_of_elemAbelian h).comap_subtype
  have hC2 : IsPGroup 2 ↥(conjSubgroup S g₀) :=
    (timti_isPGroup_of_elemAbelian h).map (MulAut.conj g₀⁻¹).toMonoidHom
  have hCsub : IsPGroup 2 ↥((conjSubgroup S g₀).subgroupOf H) := by
    rw [← Subgroup.comap_subtype (conjSubgroup S g₀) H]
    exact hC2.comap_subtype
  obtain ⟨P₁, hP₁⟩ := hSsub.exists_le_sylow
  haveI : Unique (Sylow 2 H) := Sylow.unique_of_normal P₁ inferInstance
  obtain ⟨P₂, hP₂⟩ := hCsub.exists_le_sylow
  have hP₂eq : P₂ = P₁ := Subsingleton.elim P₂ P₁
  have hCsub_le : (conjSubgroup S g₀).subgroupOf H ≤ (P₁ : Subgroup H) := by
    rw [hP₂eq] at hP₂
    exact hP₂
  have hPeq : P₁.map H.subtype = H := by
    refine le_antisymm (Subgroup.map_subtype_le (H := H) P₁) ?_
    refine sup_le ?_ ?_
    · intro s hs
      refine ⟨⟨s, Subgroup.mem_sup_left hs⟩, ?_, rfl⟩
      exact hP₁ (Subgroup.mem_subgroupOf.mpr hs)
    · intro y hy
      refine ⟨⟨y, Subgroup.mem_sup_right hy⟩, ?_, rfl⟩
      exact hCsub_le (Subgroup.mem_subgroupOf.mpr hy)
  change IsPGroup 2 ↥H
  rw [← hPeq]
  exact P₁.isPGroup'.map H.subtype

theorem pair_map_center (h : Hyp X S) (g : X ⧸ Subgroup.center X)
    (h2 : IsPGroup 2 ↥(S.map (QuotientGroup.mk' (Subgroup.center X)) ⊔
      conjSubgroup (S.map (QuotientGroup.mk' (Subgroup.center X))) g)) :
    ∀ a ∈ S.map (QuotientGroup.mk' (Subgroup.center X)),
      ∀ b ∈ conjSubgroup (S.map (QuotientGroup.mk' (Subgroup.center X))) g, a * b = b * a := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) g
  have hHP : IsPGroup 2 ↥(S ⊔ conjSubgroup S g₀) := timti_isPGroup_sup_conj h g₀ h2
  intro a ha b hb
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  have hu : g₀⁻¹ * t * g₀ ∈ conjSubgroup S g₀ := by
    rw [mem_conjSubgroup_iff]
    convert ht using 1
    group
  have hcomm := h.pair g₀ hHP s hs (g₀⁻¹ * t * g₀) hu
  simpa [map_mul, map_inv, MulAut.conj_apply] using
    congrArg (QuotientGroup.mk' (Subgroup.center X)) hcomm

theorem isWeaklyClosedIn_of_isWC (h : Hyp X S)
    (hwc : CFSG.CGT.Timmesfeld75.IsWC (S.map (QuotientGroup.mk' (Subgroup.center X))))
    (T : Sylow 2 X) (hST : S ≤ T) : IsWeaklyClosedIn S T := by
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  change CFSG.CGT.Timmesfeld75.IsWC (S.map π) at hwc
  intro g hg
  have h2 : IsPGroup 2 ↥(S ⊔ conjSubgroup S g) :=
    T.isPGroup'.to_le (sup_le hST hg)
  obtain ⟨s, hs, -, -, hs1, -, -⟩ := h.exists_ne_ne_one
  have hsD : s ∈ dSet S := mem_dSet_of_mem hs hs1
  have hsZ : s ∉ Subgroup.center X := h.not_mem_center hsD
  have hts1 : π s ≠ 1 := fun h1 => hsZ ((QuotientGroup.eq_one_iff s).1 h1)
  have hle : CFSG.CGT.Timmesfeld75.conjSubgroup (π g)⁻¹ (S.map π) ≤
      Subgroup.centralizer ({π s} : Set (X ⧸ Subgroup.center X)) := by
    intro y hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hy_eq : y = π (g⁻¹ * s' * g) := by
      rw [← hay]
      simp [MulAut.conj_apply]
    rw [hy_eq]
    have hs'g : g⁻¹ * s' * g ∈ conjSubgroup S g := by
      rw [mem_conjSubgroup_iff]
      convert hs' using 1
      group
    have hcomm := h.pair g h2 s hs (g⁻¹ * s' * g) hs'g
    simpa [map_mul, map_inv] using congrArg π hcomm
  have hEq : CFSG.CGT.Timmesfeld75.conjSubgroup (π g)⁻¹ (S.map π) = S.map π :=
    (hwc.2 (π s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩) hts1).2 (π g)⁻¹ hle
  have hmap_eq : (conjSubgroup S g).map π = S.map π := by
    rw [← timti_map_conj π S g]
    exact hEq
  have hleS : conjSubgroup S g ≤ S := by
    intro x hx
    have hxmap : π x ∈ S.map π := by
      rw [← hmap_eq]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨s'', hs'', hs''eq⟩ := Subgroup.mem_map.mp hxmap
    obtain ⟨z, hz, hzx⟩ := (QuotientGroup.mk'_eq_mk' (N := Subgroup.center X)).mp hs''eq
    have hx2 : x ^ 2 = 1 := by
      have hxS : g * x * g⁻¹ ∈ S := mem_conjSubgroup_iff.mp hx
      have hgc := h.elem.2 (g * x * g⁻¹) hxS
      have hgc' := congrArg (fun w : X => g⁻¹ * w * g) hgc
      simpa [pow_two, mul_assoc] using hgc'
    have hs''2 : s'' ^ 2 = 1 := h.elem.2 s'' hs''
    have hcomm_us : s'' * x = x * s'' := by
      have hzs := Subgroup.mem_center_iff.mp hz s''
      calc s'' * x = s'' * (s'' * z) := by rw [hzx.symm]
        _ = (s'' * s'') * z := by rw [← mul_assoc]
        _ = z := by rw [← pow_two, hs''2, one_mul]
        _ = (s'' * z) * s'' := by rw [hzs, mul_assoc, ← pow_two, hs''2, mul_one]
        _ = x * s'' := by rw [← hzx.symm]
    have hcomm_sx : Commute s'' x := hcomm_us
    have hz2 : z ^ 2 = 1 := by
      have hz_eq : z = (s'')⁻¹ * x := by
        rw [hzx.symm, inv_mul_cancel_left]
      rw [hz_eq, Commute.mul_pow hcomm_sx.inv_left, inv_pow, hs''2, inv_one, hx2, mul_one]
    have hz1 : z = 1 := by
      have hdiv2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have hdivZ : orderOf z ∣ Nat.card (Subgroup.center X) :=
        Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        rw [h1] at hdivZ
        exact (Nat.not_even_iff_odd.mpr h.odd_card_center) (even_iff_two_dvd.mpr hdivZ)
    rw [← hzx, hz1, mul_one]
    exact hs''
  refine Subgroup.eq_of_le_of_card_ge hleS ?_
  have hcard : Nat.card (conjSubgroup S g) = Nat.card S :=
    Subgroup.card_map_of_injective (K := S) (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective
  exact le_of_eq hcard.symm

theorem exists_sylow_isWeaklyClosedIn (h : Hyp X S)
    (hwc : CFSG.CGT.Timmesfeld75.IsWC (S.map (QuotientGroup.mk' (Subgroup.center X)))) :
    ∃ T : Sylow 2 X, S ≤ T ∧ IsWeaklyClosedIn S T := by
  obtain ⟨T, hST⟩ := (timti_isPGroup_of_elemAbelian h).exists_le_sylow
  exact ⟨T, hST, h.isWeaklyClosedIn_of_isWC hwc T hST⟩

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
