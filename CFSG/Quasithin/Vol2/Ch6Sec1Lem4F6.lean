module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F4
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F5

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

variable {K : Type*} [Field K] [Finite K]

theorem pgl2_outer_involution_data614 (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {z : PGL2 K}
    (hzJ : z ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) :
    ∃ (U : Subgroup (PGL2 K)) (w : PGL2 K), IsCyclic U ∧ z ∈ U ∧ w * w = 1 ∧ w ∉ U ∧
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({z} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w ∧
      ¬ U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  classical
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  obtain ⟨U, s, -, w, hUc, -, -, hsU, hsJ, hs1, hss, -, -, -, -, -, hwU, hww, hwinv, hC⟩ :=
    pgl2_low_two_part_torus_reflection_data K hK hcard
  have hsI : BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [pow_two]; exact hss⟩
  obtain ⟨g, hg'⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate K hK hcard hsI hz hsJ
    (hJ ▸ hzJ))
  set c := (MulAut.conj g).toMonoidHom with hc
  refine ⟨U.map c, g * w * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : IsCyclic ↥U := hUc
    exact isCyclic_of_surjective (c.subgroupMap U) (c.subgroupMap_surjective U)
  · exact ⟨s, hsU, by rw [← hg']; rfl⟩
  · rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, hww]
    group
  · rintro ⟨x, hx, hxe⟩
    have : x = w := by
      have hxe' : g * x * g⁻¹ = g * w * g⁻¹ := hxe
      simpa using hxe'
    exact hwU (this ▸ hx)
  · rintro _ ⟨x, hx, rfl⟩
    show g * w * g⁻¹ * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ = (g * x * g⁻¹)⁻¹
    have := hwinv x hx
    calc g * w * g⁻¹ * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ = g * (w * x * w⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹)⁻¹ := by rw [this]; group
  · have e1 : Subgroup.centralizer ({z} : Set (PGL2 K)) =
        (Subgroup.centralizer ({s} : Set (PGL2 K))).map c := by
      ext x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
      constructor
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [hc, MulAut.conj_apply, mul_assoc]⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hg'] at hx
        calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [hx]
          _ = s * (g⁻¹ * x * g) := by group
      · rintro ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hy
        rw [← hg']
        show g * y * g⁻¹ * (g * s * g⁻¹) = g * s * g⁻¹ * (g * y * g⁻¹)
        calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
          _ = g * (s * y) * g⁻¹ := by rw [hy]
          _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e1, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · intro hle
    exact hzJ (hle ⟨s, hsU, by rw [← hg']; rfl⟩)

theorem pgl2_order_five_reflections614 (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {y z : PGL2 K} (hy5 : orderOf y = 5)
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) (hyz : Commute y z) :
    (∃ r, r ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ∧
        r ^ 2 = 1 ∧ r ≠ 1 ∧ r * y * r⁻¹ = y⁻¹) ∧
      ∃ h r : PGL2 K, r ^ 2 = 1 ∧ r * y * r⁻¹ = y⁻¹ ∧ h * z * h⁻¹ = r := by
  classical
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range with hJdef
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  have hJidx : J.index = 2 := pgl2_psl2Range_index_eq_two K hK
  have hdata : ∃ (U : Subgroup (PGL2 K)) (w : PGL2 K), IsCyclic U ∧ z ∈ U ∧ w * w = 1 ∧
      w ∉ U ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({z} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w ∧ ¬ U ≤ J := by
    by_cases hzJ : z ∈ J
    · exact pgl2_inner_involution_data614 hK hcard hzJ hz
    · exact pgl2_outer_involution_data614 hK hcard hzJ hz
  obtain ⟨U, w, hUc, hzU, hww, hwU, hwinv, hC, hUJ⟩ := hdata
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have : IsCyclic ↥U := hUc
    let _ : CommGroup ↥U := IsCyclic.commGroup
    have := mul_comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hUw : ∀ u ∈ U, ∀ x ∈ U, (u * w) * x * (u * w)⁻¹ = x⁻¹ := by
    intro u hu x hx
    calc (u * w) * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hwinv x hx]
      _ = x⁻¹ := by rw [hUcomm u hu _ (U.inv_mem hx)]; group
  have hsq : ∀ u ∈ U, (u * w) ^ 2 = 1 := by
    intro u hu
    rw [pow_two]
    calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
      _ = u * u⁻¹ * (w * w) := by rw [hwinv u hu]
      _ = 1 := by rw [hww]; group
  have hne : ∀ u ∈ U, u * w ≠ 1 := by
    intro u hu h
    apply hwU
    have : w = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact U.inv_mem hu
  have hyU : y ∈ U := by
    have hyC : y ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hC, Subgroup.mem_centralizer_singleton_iff]
      exact hyz.eq
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hyC with h | ⟨u, hu, rfl⟩
    · exact h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one (hsq u hu)
      rw [hy5] at this
      norm_num at this
  obtain ⟨u₁, hu₁, hu₁J⟩ := Set.not_subset.mp hUJ
  have hboth : ∃ ri ∈ U, ∃ ro ∈ U, ri * w ∈ J ∧ ro * w ∉ J := by
    by_cases hwJ : w ∈ J
    · refine ⟨1, U.one_mem, u₁, hu₁, by rwa [one_mul], ?_⟩
      rw [Subgroup.mul_mem_iff_of_index_two hJidx]
      exact fun h => hu₁J (h.mpr hwJ)
    · refine ⟨u₁, hu₁, 1, U.one_mem, ?_, by rwa [one_mul]⟩
      rw [Subgroup.mul_mem_iff_of_index_two hJidx]
      exact iff_of_false hu₁J hwJ
  obtain ⟨ui, hui, uo, huo, hiJ, hoJ⟩ := hboth
  have hinvol : ∀ u ∈ U, BenderSuzuki.PFAppendixIII.IsInvolution (u * w) :=
    fun u hu => ⟨hne u hu, hsq u hu⟩
  refine ⟨⟨uo * w, hoJ, hsq uo huo, hne uo huo, hUw uo huo y hyU⟩, ?_⟩
  by_cases hzJ : z ∈ J
  · obtain ⟨g, -, hg⟩ := pgl2_inner_involutions_conjugate hK hcard (hJ ▸ hzJ) hz (hJ ▸ hiJ)
      (hinvol ui hui)
    exact ⟨g, ui * w, hsq ui hui, hUw ui hui y hyU, hg⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate K hK hcard hz
      (hinvol uo huo) (hJ ▸ hzJ) (hJ ▸ hoJ))
    exact ⟨g, uo * w, hsq uo huo, hUw uo huo y hyU, hg⟩

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

theorem eq_one_or_eq_of_sq614 (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    {y z : PGammaL2 F} (hyN : y ∈ pGammaL2PSLRange F) (hy5 : orderOf y = 5)
    (hzN : z ∈ pGammaL2PSLRange F) (hzI : BenderSuzuki.PFAppendixIII.IsInvolution z)
    (hyz : Commute y z) :
    ∀ e ∈ pGammaL2PGLRange F, e ^ 2 = 1 → Commute e y → e = 1 ∨ e = z := by
  classical
  set ι₂ := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hinj₂ : Function.Injective ι₂ := SemidirectProduct.inl_injective
  obtain ⟨y₁, rfl⟩ := hyN
  obtain ⟨z₁, rfl⟩ := hzN
  have hy₀5 : orderOf (Matrix.ProjectiveSpecialLinearGroup.toPGL y₁) = 5 := by
    rw [← orderOf_injective _ hinj₂]
    exact hy5
  have hz₀I : BenderSuzuki.PFAppendixIII.IsInvolution
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) z₁) := by
    refine ⟨fun h => hzI.1 (by show ι₂ _ = 1; rw [h, map_one]), ?_⟩
    apply hinj₂
    rw [map_pow, map_one]
    exact hzI.2
  have hyz₀ : Commute (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) y₁)
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) z₁) :=
    hinj₂ (by rw [map_mul, map_mul]; exact hyz.eq)
  obtain ⟨hinv, -⟩ := pgl2_inner_order_five614 hK hcard hy₀5 ⟨y₁, rfl⟩ ⟨z₁, rfl⟩ hz₀I hyz₀
  rintro e ⟨e₀, rfl⟩ he2 hey
  have he₀2 : e₀ ^ 2 = 1 := hinj₂ (by rw [map_pow, map_one]; exact he2)
  have he₀y : Commute e₀ (Matrix.ProjectiveSpecialLinearGroup.toPGL y₁) :=
    hinj₂ (by rw [map_mul, map_mul]; exact hey.eq)
  rcases hinv e₀ he₀2 he₀y with h | h
  · left; rw [h, map_one]
  · right; rw [h]; rfl

theorem mem_normalizer_not_mem_centralizer614 {G : Type*} [Group G] {w y : G}
    (hy5 : orderOf y = 5) (hw : w * y * w⁻¹ = y⁻¹) :
    w ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) ∧
      w ∉ Subgroup.centralizer ({y} : Set G) := by
  have hw' : w⁻¹ * y * w = y⁻¹ := by
    have := congrArg (fun x => w⁻¹ * x⁻¹ * w) hw
    simp only [inv_inv] at this
    rw [← this]
    group
  refine ⟨mem_normalizer_zpowers_of_conj614 ?_ ?_, ?_⟩
  · rw [hw]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
  · rw [hw']; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers y)
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    have h2 : y = y⁻¹ := by
      calc y = w * y * w⁻¹ := by rw [h]; group
        _ = y⁻¹ := hw
    have h3 : y ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [h2]; exact mul_inv_cancel y
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hy5] at this
    norm_num at this

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

theorem fieldFus614_of_card_sq (hF : Nat.card F = p ^ 2) (hp2 : p ≠ 2) : FieldFus614 F := by
  classical
  intro T E y hTs hyN hy5 hTy hET hEC hEa hEP
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    rcases hpo with ⟨s, hs⟩
    omega
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, 2, hp.out, hpo, by norm_num, hF⟩
  have hcard : 3 < Nat.card F := by
    rw [hF]
    nlinarith
  set N := pGammaL2PSLRange F with hNdef
  have hNn : N.Normal := pGammaL2PSLRange_normal F hK hcard
  have hNP : N ≤ pGammaL2PGLRange F := by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨z, hzN, hzI, hyz⟩ := exists_involution_commute614 hK hcard hTs hy5 hTy
  have huniq := eq_one_or_eq_of_sq614 hK hcard hyN hy5 hzN hzI hyz
  obtain ⟨f, hfE, hfP⟩ := Set.not_subset.mp hEP
  have hf2 : f ^ 2 = 1 := hEa.2 f hfE
  have hfy : Commute f y := Subgroup.mem_centralizer_singleton_iff.mp (hEC hfE)
  set τ := f.right with hτdef
  have hτ : τ ≠ 1 := by
    intro h
    apply hfP
    refine ⟨f.left, ?_⟩
    have := SemidirectProduct.inl_left_mul_inr_right f
    rw [← hτdef, h, map_one, mul_one] at this
    exact this
  have hfz : f * z * f⁻¹ = z := by
    have hmem : f * z * f⁻¹ ∈ pGammaL2PGLRange F := hNP (hNn.conj_mem z hzN f)
    have hsq : (f * z * f⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hzI.2]
      group
    have hcomm : Commute (f * z * f⁻¹) y := by
      have hfy' : f * y * f⁻¹ = y := by rw [hfy.eq]; group
      show f * z * f⁻¹ * y = y * (f * z * f⁻¹)
      calc f * z * f⁻¹ * y = f * z * f⁻¹ * (f * y * f⁻¹) := by rw [hfy']
        _ = f * (z * y) * f⁻¹ := by group
        _ = f * (y * z) * f⁻¹ := by rw [hyz.eq]
        _ = f * y * f⁻¹ * (f * z * f⁻¹) := by group
        _ = y * (f * z * f⁻¹) := by rw [hfy']
    rcases huniq _ hmem hsq hcomm with h | h
    · exfalso
      apply hzI.1
      have : z = f⁻¹ * (f * z * f⁻¹) * f := by group
      rw [this, h]
      group
    · exact h
  have hfz' : Commute f z := by
    show f * z = z * f
    calc f * z = f * z * f⁻¹ * f := by group
      _ = z * f := by rw [hfz]
  have hEel : ∀ e ∈ E, e = 1 ∨ e = z ∨ e = f ∨ e = z * f := by
    intro e he
    have he2 : e ^ 2 = 1 := hEa.2 e he
    have hey : Commute e y := Subgroup.mem_centralizer_singleton_iff.mp (hEC he)
    by_cases heP : e ∈ pGammaL2PGLRange F
    · rcases huniq e heP he2 hey with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hef : e * f ∈ pGammaL2PGLRange F := by
        have hr : (e * f).right = 1 := by
          rw [SemidirectProduct.mul_right]
          have h1 : e.right ≠ 1 := by
            intro h
            apply heP
            refine ⟨e.left, ?_⟩
            have := SemidirectProduct.inl_left_mul_inr_right e
            rw [h, map_one, mul_one] at this
            exact this
          have hτ' : ∀ x, e.right x = f.right x := fun x => by
            rw [ringEquiv_apply_eq_pow614 hF h1, ringEquiv_apply_eq_pow614 hF hτ]
          have : e.right = f.right := RingEquiv.ext hτ'
          rw [this, ← pow_two, ← hτdef, ringEquiv_sq_eq_one614 hF hτ]
        refine ⟨(e * f).left, ?_⟩
        have := SemidirectProduct.inl_left_mul_inr_right (e * f)
        rw [hr, map_one, mul_one] at this
        exact this
      have hcomm_ef : Commute e f := by
        have := hEa.1.is_comm.comm (⟨e, he⟩ : ↥E) ⟨f, hfE⟩
        exact congrArg Subtype.val this
      have hef2 : (e * f) ^ 2 = 1 := by
        rw [hcomm_ef.mul_pow, he2, hf2, one_mul]
      have hefy : Commute (e * f) y := hey.mul_left hfy
      have hfi : f⁻¹ = f := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hf2]
      rcases huniq _ hef hef2 hefy with h | h
      · right; right; left
        calc e = e * f * f⁻¹ := by group
          _ = f := by rw [h, one_mul, hfi]
      · right; right; right
        calc e = e * f * f⁻¹ := by group
          _ = z * f := by rw [h, hfi]
  obtain ⟨b, hb⟩ := exists_conj_eq_inr614 hF f hf2 hfP
  set c : PGammaL2 F := SemidirectProduct.inl b with hc
  set y' := c * y * c⁻¹ with hy'
  set z' := c * z * c⁻¹ with hz'
  have hy'N : y' ∈ N := hNn.conj_mem y hyN c
  have hz'N : z' ∈ N := hNn.conj_mem z hzN c
  have hy'τ : SemidirectProduct.inr τ * y' * (SemidirectProduct.inr τ)⁻¹ = y' := by
    rw [← hb, hy']
    have hfy' : f * y * f⁻¹ = y := by rw [hfy.eq]; group
    calc c * f * c⁻¹ * (c * y * c⁻¹) * (c * f * c⁻¹)⁻¹ = c * (f * y * f⁻¹) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [hfy']
  have hz'τ : SemidirectProduct.inr τ * z' * (SemidirectProduct.inr τ)⁻¹ = z' := by
    rw [← hb, hz']
    calc c * f * c⁻¹ * (c * z * c⁻¹) * (c * f * c⁻¹)⁻¹ = c * (f * z * f⁻¹) * c⁻¹ := by group
      _ = c * z * c⁻¹ := by rw [hfz]
  obtain ⟨y'₀, hy'₀⟩ := hNP hy'N
  obtain ⟨z'₀, hz'₀⟩ := hNP hz'N
  have hfix : ∀ x₀ : PGL2 F, SemidirectProduct.inr τ * SemidirectProduct.inl x₀ *
      (SemidirectProduct.inr τ)⁻¹ = (SemidirectProduct.inl x₀ : PGammaL2 F) →
      pgl2FieldAut F τ x₀ = x₀ := by
    intro x₀ hx₀
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    rw [SemidirectProduct.inl_aut, map_inv]
    exact hx₀
  have hy'₀τ : pgl2FieldAut F τ y'₀ = y'₀ := hfix y'₀ (by rw [hy'₀]; exact hy'τ)
  have hz'₀τ : pgl2FieldAut F τ z'₀ = z'₀ := hfix z'₀ (by rw [hz'₀]; exact hz'τ)
  obtain ⟨yR, hyR⟩ := exists_iotaR614_eq_of_fixed hF hτ hy'₀τ
  obtain ⟨zR, hzR⟩ := exists_iotaR614_eq_of_fixed hF hτ hz'₀τ
  set ι : PGL2 (fixedField614 τ) →* PGammaL2 F :=
    (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (iotaR614 (fixedField614 τ)) with hιdef
  have hιinj : Function.Injective ι :=
    SemidirectProduct.inl_injective.comp (iotaR614_injective (fixedField614 τ))
  have hιy : ι yR = y' := by rw [hιdef, MonoidHom.comp_apply, hyR, hy'₀]
  have hιz : ι zR = z' := by rw [hιdef, MonoidHom.comp_apply, hzR, hz'₀]
  have hy'5 : orderOf y' = 5 := by
    rw [hy', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy5
  have hyR5 : orderOf yR = 5 := by
    rw [← orderOf_injective ι hιinj, hιy]
    exact hy'5
  have hzRI : BenderSuzuki.PFAppendixIII.IsInvolution zR := by
    refine ⟨fun h => hzI.1 ?_, ?_⟩
    · have : z' = 1 := by rw [← hιz, h, map_one]
      have e : z = c⁻¹ * z' * c := by rw [hz']; group
      rw [e, this]; group
    · apply hιinj
      rw [map_pow, hιz, map_one, hz']
      rw [conj_pow, hzI.2]
      group
  have hyzR : Commute yR zR := by
    apply hιinj
    rw [map_mul, map_mul, hιy, hιz, hy', hz']
    calc c * y * c⁻¹ * (c * z * c⁻¹) = c * (y * z) * c⁻¹ := by group
      _ = c * (z * y) * c⁻¹ := by rw [hyz.eq]
      _ = c * z * c⁻¹ * (c * y * c⁻¹) := by group
  have hRcard : Nat.card (fixedField614 τ) = p := card_fixedField614 hF hτ
  have hp3' : p ≠ 3 := by
    intro h3
    have h1 := orderOf_dvd_natCard yR
    rw [hyR5, pgl2_card_formula, hRcard, h3] at h1
    norm_num at h1
  have hRK : IsOddPrimePower (Nat.card (fixedField614 τ)) :=
    ⟨p, 1, hp.out, hpo, le_rfl, by rw [hRcard, pow_one]⟩
  have hRc : 3 < Nat.card (fixedField614 τ) := by rw [hRcard]; omega
  obtain ⟨⟨ro, hroJ, hro2, hro1, hroy⟩, ⟨h, r, hr2, hry, hhz⟩⟩ :=
    pgl2_order_five_reflections614 hRK hRc hyR5 hzRI hyzR
  have hinvert : ∀ x : PGL2 (fixedField614 τ), x * yR * x⁻¹ = yR⁻¹ →
      (c⁻¹ * ι x * c) * y * (c⁻¹ * ι x * c)⁻¹ = y⁻¹ := by
    intro x hx
    have h1 : ι x * y' * (ι x)⁻¹ = y'⁻¹ := by
      rw [← hιy, ← map_inv, ← map_mul, ← map_mul, hx, map_inv]
    have e : y = c⁻¹ * y' * c := by rw [hy']; group
    calc (c⁻¹ * ι x * c) * y * (c⁻¹ * ι x * c)⁻¹ = c⁻¹ * (ι x * y' * (ι x)⁻¹) * c := by
          rw [e]; group
      _ = c⁻¹ * y'⁻¹ * c := by rw [h1]
      _ = y⁻¹ := by rw [e]; group
  by_cases hzE : z ∈ E
  ·
    set g := c⁻¹ * ι h * c with hg
    have hgN : g ∈ N := by
      obtain ⟨s, hs⟩ := iotaR614_mem_range614 hF hp2 hτ h
      have : ι h ∈ N := ⟨s, by
        show SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL s) =
          SemidirectProduct.inl (iotaR614 (fixedField614 τ) h)
        rw [hs]⟩
      have := hNn.conj_mem _ this c⁻¹
      simpa [hg, mul_assoc] using this
    have hgf : g * f * g⁻¹ = f := by
      have hcomm : SemidirectProduct.inr τ * ι h = ι h * SemidirectProduct.inr τ := by
        have := SemidirectProduct.inl_aut (φ := pgl2FieldAut F) τ (iotaR614 (fixedField614 τ) h)
        rw [pgl2FieldAut_iotaR614, map_inv] at this
        show SemidirectProduct.inr τ * SemidirectProduct.inl (iotaR614 (fixedField614 τ) h) =
          SemidirectProduct.inl (iotaR614 (fixedField614 τ) h) * SemidirectProduct.inr τ
        calc SemidirectProduct.inr τ * SemidirectProduct.inl (iotaR614 (fixedField614 τ) h) =
              SemidirectProduct.inr τ * SemidirectProduct.inl (iotaR614 (fixedField614 τ) h) *
                (SemidirectProduct.inr τ)⁻¹ * SemidirectProduct.inr τ := by group
          _ = SemidirectProduct.inl (iotaR614 (fixedField614 τ) h) * SemidirectProduct.inr τ := by
              rw [← this]
      have h1 : ι h * SemidirectProduct.inr τ * (ι h)⁻¹ = SemidirectProduct.inr τ := by
        rw [← hcomm]
        group
      have ef : f = c⁻¹ * SemidirectProduct.inr τ * c := by rw [← hb]; group
      rw [hg, ef]
      calc c⁻¹ * ι h * c * (c⁻¹ * SemidirectProduct.inr τ * c) * (c⁻¹ * ι h * c)⁻¹ =
            c⁻¹ * (ι h * SemidirectProduct.inr τ * (ι h)⁻¹) * c := by group
        _ = c⁻¹ * SemidirectProduct.inr τ * c := by rw [h1]
    have hgz : g * z * g⁻¹ = c⁻¹ * ι r * c := by
      have e : z = c⁻¹ * z' * c := by rw [hz']; group
      rw [hg, e, ← hιz, ← hhz]
      simp only [map_mul, map_inv]
      group
    have hrinv := hinvert r hry
    obtain ⟨hrN, hrC⟩ := mem_normalizer_not_mem_centralizer614 hy5 hrinv
    have hfN : f ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F)) := by
      have hfy' : f * y * f⁻¹ = y := by rw [hfy.eq]; group
      have hfy'' : f⁻¹ * y * f = y := by
        calc f⁻¹ * y * f = f⁻¹ * (f * y * f⁻¹) * f := by rw [hfy']
          _ = y := by group
      refine mem_normalizer_zpowers_of_conj614 ?_ ?_
      · rw [hfy']; exact Subgroup.mem_zpowers y
      · rw [hfy'']; exact Subgroup.mem_zpowers y
    refine ⟨g, Subgroup.mem_sup_left hgN, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      show g * e * g⁻¹ ∈ _
      rcases hEel e he with h0 | h0 | h0 | h0
      · rw [h0, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
      · rw [h0, hgz]; exact hrN
      · rw [h0, hgf]; exact hfN
      · rw [h0, show g * (z * f) * g⁻¹ = (g * z * g⁻¹) * (g * f * g⁻¹) by group, hgz, hgf]
        exact Subgroup.mul_mem _ hrN hfN
    · intro hle
      apply hrC
      rw [← hgz]
      exact hle ⟨z, hzE, rfl⟩
  ·
    obtain ⟨k, hkJ, hk⟩ := exists_conj_inr_eq614 hF hp2 hτ ro hro2 hro1 hroJ
    set g := c⁻¹ * SemidirectProduct.inl k * c with hg
    have hgN : g ∈ N := by
      obtain ⟨k₁, rfl⟩ := hkJ
      have : (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL k₁) :
          PGammaL2 F) ∈ N := ⟨k₁, rfl⟩
      have := hNn.conj_mem _ this c⁻¹
      simpa [hg, mul_assoc] using this
    have hgf : g * f * g⁻¹ = c⁻¹ * (ι ro * SemidirectProduct.inr τ) * c := by
      have ef : f = c⁻¹ * SemidirectProduct.inr τ * c := by rw [← hb]; group
      rw [hg, ef]
      calc c⁻¹ * SemidirectProduct.inl k * c * (c⁻¹ * SemidirectProduct.inr τ * c) *
            (c⁻¹ * SemidirectProduct.inl k * c)⁻¹ =
          c⁻¹ * (SemidirectProduct.inl k * SemidirectProduct.inr τ *
            (SemidirectProduct.inl k)⁻¹) * c := by group
        _ = c⁻¹ * (ι ro * SemidirectProduct.inr τ) * c := by rw [hk]; rfl
    have hwinv : (g * f * g⁻¹) * y * (g * f * g⁻¹)⁻¹ = y⁻¹ := by
      have h1 : (ι ro * SemidirectProduct.inr τ) * y' * (ι ro * SemidirectProduct.inr τ)⁻¹ =
          y'⁻¹ := by
        have h2 : ι ro * y' * (ι ro)⁻¹ = y'⁻¹ := by
          rw [← hιy, ← map_inv, ← map_mul, ← map_mul, hroy, map_inv]
        calc (ι ro * SemidirectProduct.inr τ) * y' * (ι ro * SemidirectProduct.inr τ)⁻¹ =
              ι ro * (SemidirectProduct.inr τ * y' * (SemidirectProduct.inr τ)⁻¹) *
                (ι ro)⁻¹ := by group
          _ = y'⁻¹ := by rw [hy'τ, h2]
      have e : y = c⁻¹ * y' * c := by rw [hy']; group
      rw [hgf]
      calc c⁻¹ * (ι ro * SemidirectProduct.inr τ) * c * y *
            (c⁻¹ * (ι ro * SemidirectProduct.inr τ) * c)⁻¹ =
          c⁻¹ * ((ι ro * SemidirectProduct.inr τ) * y' * (ι ro * SemidirectProduct.inr τ)⁻¹) *
            c := by rw [e]; group
        _ = c⁻¹ * y'⁻¹ * c := by rw [h1]
        _ = y⁻¹ := by rw [e]; group
    obtain ⟨hwN, hwC⟩ := mem_normalizer_not_mem_centralizer614 hy5 hwinv
    have hEf : ∀ e ∈ E, e = 1 ∨ e = f := by
      intro e he
      rcases hEel e he with h0 | h0 | h0 | h0
      · exact Or.inl h0
      · exact absurd (h0 ▸ he) hzE
      · exact Or.inr h0
      · exfalso
        apply hzE
        have hfi : f⁻¹ = f := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hf2]
        have : z = e * f := by rw [h0, mul_assoc, ← pow_two, hf2, mul_one]
        rw [this]
        exact E.mul_mem he hfE
    refine ⟨g, Subgroup.mem_sup_left hgN, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      show g * e * g⁻¹ ∈ _
      rcases hEf e he with h0 | h0
      · rw [h0, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
      · rw [h0]; exact hwN
    · intro hle
      exact hwC (hle ⟨f, hfE, rfl⟩)

end

section

theorem kg614FusionL2Field_holds : KG614FusionL2Field := by
  intro F _ _ p hp hp2 hF
  have : Fact p.Prime := ⟨hp⟩
  exact fieldFus614_of_card_sq hF hp2

theorem kg614FusionL2_holds : KG614FusionL2 :=
  kg614FusionL2_of_field kg614FusionL2Field_holds

end

end CFSG.Quasithin.H13
