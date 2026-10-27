module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixInner
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTorus
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylXA
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylGen
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEvenOrbit
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_single_eq_sum : ∀ c k : Fin 6, k ≠ c →
    (Pi.single k 1 : DVec 6) = 2 • ((∑ j ∈ Finset.univ.erase c,
      (Pi.single k 1 + -Pi.single j 1 : DVec 6)) + (1 + -Pi.single c 1)) := by
  decide

theorem ggQTwoDUnitSix_addSubgroup_eq_top {c : Fin 6} {A : AddSubgroup (DVec 6)}
    (h1 : (1 : DVec 6) ∈ A) (hc : Pi.single c 1 ∈ A)
    (hS : ∀ i j : Fin 6, i ≠ c → j ≠ c → i ≠ j → Pi.single i 1 + -Pi.single j 1 ∈ A) :
    A = ⊤ := by
  classical
  have hsingle : ∀ k : Fin 6, Pi.single k 1 ∈ A := by
    intro k
    by_cases hkc : k = c
    · rw [hkc]
      exact hc
    · rw [ggQTwoDUnitSix_single_eq_sum c k hkc]
      refine A.nsmul_mem (A.add_mem (A.sum_mem fun j hj => ?_)
        (A.add_mem h1 (A.neg_mem hc))) 2
      by_cases hjk : j = k
      · rw [hjk, add_neg_cancel]
        exact A.zero_mem
      · exact hS k j hkc (Finset.mem_erase.mp hj).1 (Ne.symm hjk)
  rw [eq_top_iff]
  intro v _
  rw [← Finset.univ_sum_single v]
  refine A.sum_mem fun i _ => ?_
  rcases (by decide : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2) (v i) with h0 | h1' | h2
  · rw [h0, Pi.single_zero]
    exact A.zero_mem
  · rw [h1']
    exact hsingle i
  · rw [h2, show (2 : ZMod 3) = 1 + 1 by decide, Pi.single_add]
    exact A.add_mem (hsingle i) (hsingle i)

theorem ggQTwoDUnitSix_perm_lift (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {x : G} (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {c : Fin 6} {J₁ : Subgroup G}
    (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁] (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G)) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ c = c) :
    ∃ n ∈ J₁, ∃ hn : n ∈ Subgroup.normalizer (Bs : Set G), ∀ s : ↥Bs,
      βL (Additive.ofMul (ggConjAut Bs hn s)) = dPerm 6 σ (βL (Additive.ofMul s)) := by
  classical
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hBsNL : ∀ s : ↥Bs, (s : G) ∈ Subgroup.normalizer (L : Set G) := fun s => hD.BsN s.2
  have hπ : ψ (ggPermSU (K := K) (f := 1) σ⁻¹) ∈
      NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ := by
    rw [hJ₁]
    exact Subgroup.mem_map_of_mem _ (qtwoDB14_perm_mem_coordBlockSU σ hσ)
  obtain ⟨u, huJ, hfu⟩ := NsQuot.mem_img.mp hπ
  have hinj : ∀ v w : ↥(Subgroup.normalizer (L : Set G)), (v : G) ∈ J₁ → (w : G) ∈ J₁ →
      f v = f w → v = w := by
    intro v w hv hw hvw
    have hk : v⁻¹ * w ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvw, inv_mul_cancel]
    have hZ : ((v⁻¹ * w : ↥(Subgroup.normalizer (L : Set G))) : G) ∈ twoCentral L :=
      (hD.mem_ker_iff _).mp hk
    have h1 := hJ₁Z _ (J₁.mul_mem (J₁.inv_mem hv) hw) (by simpa using hZ)
    have h2 : v⁻¹ * w = 1 := Subtype.ext (by simpa using h1)
    exact (inv_mul_eq_one.mp h2)
  let A : AddSubgroup (DVec 6) :=
    { carrier := {v | ∃ t : ↥Bs, (t : G) = (u : G) * ((Additive.toMul (βL.symm v) : ↥Bs) : G) *
        (u : G)⁻¹ ∧ βL (Additive.ofMul t) = dPerm 6 σ v}
      add_mem' := fun {v w} hv hw => by
        obtain ⟨t₁, ht₁, hβ₁⟩ := hv
        obtain ⟨t₂, ht₂, hβ₂⟩ := hw
        refine ⟨t₁ * t₂, ?_, ?_⟩
        · simp only [map_add, toMul_add, Subgroup.coe_mul, ht₁, ht₂]
          group
        · rw [ofMul_mul, map_add, hβ₁, hβ₂, map_add]
      zero_mem' := ⟨1, by simp, by simp⟩
      neg_mem' := fun {v} hv => by
        obtain ⟨t, ht, hβ⟩ := hv
        refine ⟨t⁻¹, ?_, ?_⟩
        · simp only [map_neg, toMul_neg, Subgroup.coe_inv, ht]
          group
        · rw [ofMul_inv, map_neg, hβ, map_neg] }
  have hmemA : ∀ s t : ↥Bs, (t : G) = (u : G) * (s : G) * (u : G)⁻¹ →
      βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)) →
        βL (Additive.ofMul s) ∈ A := fun s t ht hβ =>
    ⟨t, by simpa using ht, hβ⟩
  have h1 : (1 : DVec 6) ∈ A := by
    have hux : (u : G) * x * (u : G)⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp hxL _ (hJ₁L huJ)]
      group
    have h := hmemA ⟨x, hxBs⟩ ⟨x, hxBs⟩ hux.symm (by
      rw [hxcoord]
      funext i
      rw [dPerm_apply_apply])
    rwa [hxcoord] at h
  have hc : Pi.single c 1 ∈ A := by
    have hub : (u : G) * b' * (u : G)⁻¹ = b' := by
      rw [Subgroup.mem_centralizer_iff.mp hb'J _ huJ]
      group
    have h := hmemA b' b' hub.symm (by
      rw [hb']
      funext i
      rw [dPerm_apply_apply]
      have hσs : σ.symm c = c := by
        rw [Equiv.symm_apply_eq]
        exact hσ.symm
      by_cases hi : i = c
      · rw [hi, hσs]
      · rw [Pi.single_eq_of_ne hi,
          Pi.single_eq_of_ne (fun h => hi (((Equiv.symm_apply_eq σ).mp h).trans hσ))])
    rwa [hb'] at h
  have hS : ∀ i j : Fin 6, i ≠ c → j ≠ c → i ≠ j → Pi.single i 1 + -Pi.single j 1 ∈ A := by
    intro i j hic hjc hij
    have hiT : i ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hic, Finset.mem_univ i⟩
    have hjT : j ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hjc, Finset.mem_univ j⟩
    obtain ⟨t, htJ, hβt⟩ := ggQTwoDUnitSix_sub_single_mem hK hD hψk hε hind hpermβ
      (T := Finset.univ.erase c) (by omega) hJ₁L hJ₁Z hJ₁ hiT hjT hij
    have hq : f u * f ⟨t, hBsNL t⟩ * (f u)⁻¹ ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs :=
      by rw [hfu]; exact hε σ _ (NsQuot.mem_img.mpr ⟨⟨t, hBsNL t⟩, t.2, rfl⟩)
    obtain ⟨w, hwBs, hfw⟩ := NsQuot.mem_img.mp hq
    let t' : ↥Bs := ⟨w, hwBs⟩
    have hβt' : βL (Additive.ofMul t') = dPerm 6 σ (βL (Additive.ofMul t)) := by
      refine hpermβ σ t t' (hBsNL t) (hBsNL t') ?_
      rw [← hfu]
      exact hfw
    have hσi : σ i ≠ c := fun h => hic (σ.injective (h.trans hσ.symm))
    have hσj : σ j ≠ c := fun h => hjc (σ.injective (h.trans hσ.symm))
    obtain ⟨t'', ht''J, hβt''⟩ := ggQTwoDUnitSix_sub_single_mem hK hD hψk hε hind hpermβ
      (T := Finset.univ.erase c) (by omega) hJ₁L hJ₁Z hJ₁
      (Finset.mem_erase.mpr ⟨hσi, Finset.mem_univ _⟩)
      (Finset.mem_erase.mpr ⟨hσj, Finset.mem_univ _⟩) (fun h => hij (σ.injective h))
    have hcoord : βL (Additive.ofMul t') = βL (Additive.ofMul t'') := by
      rw [hβt', hβt, hβt'']
      funext k
      rw [dPerm_apply_apply]
      simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply, Equiv.symm_apply_eq,
        eq_comm (a := k)]
    have htt'' : t' = t'' := by
      have h := βL.injective hcoord
      simpa using h
    have ht'J : (w : G) ∈ J₁ := by
      have h : ((t' : ↥Bs) : G) ∈ J₁ := by rw [htt'']; exact ht''J
      exact h
    have hnt : (u * ⟨t, hBsNL t⟩ * u⁻¹ : ↥(Subgroup.normalizer (L : Set G))) = w := by
      refine hinj _ _ ?_ ht'J ?_
      · exact J₁.mul_mem (J₁.mul_mem huJ htJ) (J₁.inv_mem huJ)
      · rw [map_mul, map_mul, map_inv]
        exact hfw.symm
    have h := hmemA t t' (by
      have := congrArg Subtype.val hnt
      simpa using this.symm) hβt'
    rwa [hβt] at h
  have hA : A = ⊤ := ggQTwoDUnitSix_addSubgroup_eq_top h1 hc hS
  have hall : ∀ s : ↥Bs, ∃ t : ↥Bs, (t : G) = (u : G) * (s : G) * (u : G)⁻¹ ∧
      βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)) := by
    intro s
    have hmem : βL (Additive.ofMul s) ∈ A := by rw [hA]; exact AddSubgroup.mem_top _
    obtain ⟨t, ht, hβ⟩ := hmem
    exact ⟨t, by simpa using ht, hβ⟩
  have hnN : (u : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨t, ht, -⟩ := hall ⟨s, hs⟩
      show (u : G) * s * (u : G)⁻¹ ∈ Bs
      rw [← ht]
      exact t.2
    · rw [Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective]
  refine ⟨u, huJ, hnN, fun s => ?_⟩
  obtain ⟨t, ht, hβ⟩ := hall s
  have hts : ggConjAut Bs hnN s = t := Subtype.ext (by rw [ggConjAut_apply, ht])
  rw [hts, hβ]

theorem ggQTwoDUnitSix_weyl_X (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {x : G} (hxBs : x ∈ Bs) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hxcoord : βL (Additive.ofMul ⟨x, hxBs⟩) = fun _ => 1) {a c : Fin 6} (hac : a ≠ c)
    {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (hb'J : (b' : G) ∈ Subgroup.centralizer (J₁ : Set G)) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {a' : MulAut ↥Bs}
    {w : DVec 6 ≃ₗ[ZMod 3] DVec 6} (hw : w ∈ dEven 6) (hwc : w (Pi.single c 1) = Pi.single c 1)
    (ha'w : ∀ s : ↥Bs, βL (Additive.ofMul (a' s)) = w (βL (Additive.ofMul s))) :
    a' ∈ ggAutomizer (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs := by
  classical
  let H : Subgroup (DVec 6 ≃ₗ[ZMod 3] DVec 6) :=
    (ggAutomizer (J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom) Bs).map (ggLin (p := 3) βL)
  have hlin : ∀ {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G))
      {v : DVec 6 ≃ₗ[ZMod 3] DVec 6},
      (∀ s : ↥Bs, βL (Additive.ofMul (ggConjAut Bs hn s)) = v (βL (Additive.ofMul s))) →
        ggLin (p := 3) βL (ggConjAut Bs hn) = v := by
    intro n hn v hv
    refine LinearEquiv.ext fun y => ?_
    obtain ⟨s, rfl⟩ := βL.surjective y
    obtain ⟨t, rfl⟩ : ∃ t : ↥Bs, Additive.ofMul t = s := ⟨Additive.toMul s, ofMul_toMul s⟩
    rw [ggLin_apply_ofMul, hv t]
  have hperm : ∀ σ : Equiv.Perm (Fin 6), σ c = c → dPerm 6 σ ∈ H := by
    intro σ hσ
    obtain ⟨n, hnJ, hnN, hnact⟩ := ggQTwoDUnitSix_perm_lift hK hD hψk hε hind hpermβ hxBs hxL
      hxcoord hJ₁L hJ₁Z hJ₁ hb' hb'J hσ
    exact Subgroup.mem_map.mpr ⟨ggConjAut Bs hnN,
      ggConjAut_mem_ggAutomizer (Subgroup.mem_sup_left hnJ) hnN, hlin hnN hnact⟩
  have hαinv : ∀ s : ↥Bs, βL (Additive.ofMul (α⁻¹ s)) =
      dSign 6 a c (βL (Additive.ofMul s)) := by
    intro s
    have h' := congrArg (dSign 6 a c) (hα (α⁻¹ s))
    rw [show α (α⁻¹ s) = s by rw [MulAut.apply_inv_self], ← LinearEquiv.mul_apply,
      qtwoDB37_dSign_double] at h'
    simpa [LinearEquiv.coe_one] using h'.symm
  have hconj : ∀ σ : Equiv.Perm (Fin 6), σ c = c →
      dSign 6 a c * dPerm 6 σ * dSign 6 a c ∈ H := by
    intro σ hσ
    obtain ⟨n, hnJ, hnN, hnact⟩ := ggQTwoDUnitSix_perm_lift hK hD hψk hε hind hpermβ hxBs hxL
      hxcoord hJ₁L hJ₁Z hJ₁ hb' hb'J hσ
    have hgnN : g * n * g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hnN) (Subgroup.inv_mem _ hgN)
    refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hgnN, ggConjAut_mem_ggAutomizer
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨n, hnJ, rfl⟩)) hgnN, hlin hgnN fun s => ?_⟩
    have hs : ggConjAut Bs hgnN s = α (ggConjAut Bs hnN (α⁻¹ s)) := by
      apply Subtype.ext
      rw [ggConjAut_apply, hg, ggConjAut_apply]
      have h3 : ((α⁻¹ s : ↥Bs) : G) = g⁻¹ * (s : G) * g := by
        have h := hg (α⁻¹ s)
        rw [show α (α⁻¹ s) = s by rw [MulAut.apply_inv_self]] at h
        rw [h]
        group
      rw [h3]
      group
    rw [hs, hα, hnact, hαinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hsign : ∀ k : Fin 6, k ≠ a → k ≠ c → dSign 6 a k ∈ H := by
    intro k hka hkc
    have hσ : Equiv.swap a k c = c := Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hkc)
    rw [ggQTwoDUnit_dSign_eq_comm hac hka hkc]
    exact H.mul_mem (hperm _ hσ) (hconj _ hσ)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, b₀ ∈ (Finset.univ.erase c).erase a :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩),
        Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
      norm_num)
  have hb₀a : b₀ ≠ a := (Finset.mem_erase.mp hb₀).1
  have hb₀c : b₀ ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hb₀).2).1
  have hsb : ∀ k : Fin 6, k ≠ a → k ≠ b₀ → k ≠ c → dSign 6 b₀ k ∈ H := by
    intro k hka hkb hkc
    have hσ : Equiv.swap b₀ k c = c :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hb₀c) (Ne.symm hkc)
    rw [ggQTwoDUnit_dSign_eq_comm (a := b₀) (b := a) (k := k) hb₀a hkb hka,
      qtwoDB37_dSign_comm b₀ a]
    exact H.mul_mem (hperm _ hσ)
      (H.mul_mem (H.mul_mem (hsign b₀ hb₀a hb₀c) (hperm _ hσ)) (hsign b₀ hb₀a hb₀c))
  have hwH : w ∈ H :=
    ggQTwoDUnit_dEven_fix_mem (m := 6) (by norm_num) (Ne.symm hb₀a) (Ne.symm hac) (Ne.symm hb₀c)
      H hperm (fun k hka _ hkc => hsign k hka hkc) hsb hw hwc
  obtain ⟨φ, hφX, hφw⟩ := Subgroup.mem_map.mp hwH
  have hgg : ggLin (p := 3) βL a' = w := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ := βL.surjective v
    obtain ⟨t, rfl⟩ : ∃ t : ↥Bs, Additive.ofMul t = s := ⟨Additive.toMul s, ofMul_toMul s⟩
    rw [ggLin_apply_ofMul, ha'w t]
  have hφa : φ = a' := ggLin_injective (p := 3) βL (hφw.trans hgg.symm)
  rw [← hφa]
  exact hφX

end CFSG.StandardType.QTwo

end
