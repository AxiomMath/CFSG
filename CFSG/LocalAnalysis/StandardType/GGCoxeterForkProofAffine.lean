module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofTypeA

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V]

theorem ggFalse_of_opposite_roots (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {ψ₁ ψ₂ : MulAut ↥Bs} (h₁ : ψ₁ ∈ ggInduced ⊤ Bs)
    (h₂ : ψ₂ ∈ ggInduced ⊤ Bs) {x₁ x₂ : V} {f₁ f₂ : Module.Dual (ZMod p) V} (hfx₁ : f₁ x₁ = 2)
    (hfx₂ : f₂ x₂ = 2) (hl₁ : ∀ z, ggLin (p := p) ι ψ₁ z = z - f₁ z • x₁)
    (hl₂ : ∀ z, ggLin (p := p) ι ψ₂ z = z - f₂ z • x₂) (hf : f₁ + f₂ = 0) (hx : x₁ + x₂ ≠ 0) :
    False := by
  have hf1 : f₁ = -f₂ := eq_neg_of_add_eq_zero_left hf
  have h2 := zmod_two_ne_zero hp2
  have hf₂x₁ : f₂ x₁ = -2 := by
    rw [← hfx₁, hf1, LinearMap.neg_apply, neg_neg]
  refine hNT (ψ₁ * ψ₂) (mul_mem_ggInduced h₁ h₂)
    (ggIsTransvection_of_apply ι (w := x₁ + x₂) (f := -f₂) hx (fun h0 => ?_) ?_ fun z => ?_)
  · have := congrArg (fun F : Module.Dual (ZMod p) V => F x₂) h0
    simp only [LinearMap.neg_apply, hfx₂, LinearMap.zero_apply, neg_eq_zero] at this
    exact h2 this
  · rw [LinearMap.neg_apply, map_add, hf₂x₁, hfx₂]
    ring
  · simp only [map_mul, LinearEquiv.mul_apply, hl₂, hl₁, hf1, LinearMap.neg_apply, map_sub,
      map_smul, hfx₂, smul_eq_mul]
    module

theorem ggLin_conj_reflection_of_eq (ι : Additive ↥Bs ≃+ V) {φ ψ : MulAut ↥Bs} {x y : V}
    {f g : Module.Dual (ZMod p) V} (hgy : g y = 2)
    (hψ : ∀ w, ggLin (p := p) ι ψ w = w - f w • x)
    (hφ : ∀ w, ggLin (p := p) ι φ w = w - g w • y) {s t : ZMod p} (hs : f y = s) (ht : g x = t)
    (z : V) : ggLin (p := p) ι (φ * ψ * φ⁻¹) z = z - (f - s • g) z • (x - t • y) := by
  rw [ggLin_conj_reflection ι hgy hψ hφ z, hs, ht, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]

theorem ggSum_Ico_of_eq_ite {m : ℕ} (hm : 1 ≤ m) {f : ℕ → ZMod p} {k : ZMod p}
    (hf : ∀ j < m, f j = if j = 0 then k else 0) : ∑ j ∈ Finset.Ico 0 m, f j = k := by
  rw [Finset.sum_eq_single 0]
  · rw [hf 0 (by omega), ite_eq_left rfl]
  · intro j hj hj0
    rw [hf j (Finset.mem_Ico.mp hj).2, ite_eq_right hj0]
  · intro h0
    exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) h0

theorem ggChainRoot_zero_eq_add (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) {m : ℕ} (hm : 1 ≤ m)
    {φJ : ℕ → MulAut ↥Bs} {φa : MulAut ↥Bs} {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V}
    {ha : V} {αa : Module.Dual (ZMod p) V} (hP : GGChainPairing m hJ αJ ha αa)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha) :
    ggChainRoot m αJ αa 0 = αa + ∑ j ∈ Finset.Ico 0 m, αJ j ∧
      ggChainCoroot m hJ ha 0 = ha + ∑ j ∈ Finset.Ico 0 m, hJ j := by
  have hc : ggChainCoroot m hJ ha m = ha := hP.chainCoroot_self_eq hp2 hm
    (fun j => ggLin (p := p) ι (φJ j)) hlinJ (ggLin (p := p) ι φa) hlina
  have hβ : ggChainRoot m αJ αa m = αa := by
    have hconj := ggChainConj_apply hP (fun j => ggLin (p := p) ι (φJ j)) hlinJ
      (ggLin (p := p) ι φa) hlina m le_rfl
    have hha : ha ≠ 0 := (ne_zero_of_apply_eq_two hp2 hP.aa).1
    refine LinearMap.ext fun z => ?_
    have h1 := hconj z
    rw [ggChainProd_self, one_mul, inv_one, mul_one, hlina, hc] at h1
    have h2 : (ggChainRoot m αJ αa m z - αa z) • ha = 0 := by
      rw [sub_smul, ← sub_right_injective h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hha)
  refine ⟨?_, ?_⟩
  · rw [ggChainRoot_zero_eq le_rfl, hβ, Finset.range_eq_Ico, add_comm]
  · rw [ggChainCoroot_zero_eq le_rfl, hc, Finset.range_eq_Ico, add_comm]

theorem ggFork_affine_false_BC (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {m : ℕ} (hm : 1 ≤ m) {φJ : ℕ → MulAut ↥Bs}
    {φa φb φt : MulAut ↥Bs} (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs)
    (hφa : φa ∈ ggInduced ⊤ Bs) (hφb : φb ∈ ggInduced ⊤ Bs) (hφt : φt ∈ ggInduced ⊤ Bs)
    {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V} {ha hb ht : V}
    {αa αb αt : Module.Dual (ZMod p) V} (hPa : GGChainPairing m hJ αJ ha αa)
    (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb)
    (hlint : ∀ w, ggLin (p := p) ι φt w = w - αt w • ht) (htt : αt ht = 2) {k₁ k₂ : ZMod p}
    (hjt : ∀ j < m, αJ j ht = if j = 0 then k₁ else 0)
    (htj : ∀ j < m, αt (hJ j) = if j = 0 then k₂ else 0) (hk : k₁ * k₂ = 2)
    (hta : αt ha = 0) (hat : αa ht = 0) (htb : αt hb = 0) (hbt : αb ht = 0) (hab : αa hb = 0)
    (hba : αb ha = 0)
    (hspan : Submodule.span (ZMod p) ({ha, hb, ht} ∪ hJ '' Set.Iio m) = ⊤)
    (hha : ha ∉ Submodule.span (ZMod p) ({hb, ht} ∪ hJ '' Set.Iio m)) : False := by
  obtain ⟨hψa, hlinψa⟩ := ggNearEnd_reflection ι hφJ hφa hPa hlinJ hlina
  obtain ⟨hψb, hlinψb⟩ := ggNearEnd_reflection ι hφJ hφb hPb hlinJ hlinb
  obtain ⟨hβa, hca⟩ := ggChainRoot_zero_eq_add hp2 ι hm hPa hlinJ hlina
  obtain ⟨hβb, hcb⟩ := ggChainRoot_zero_eq_add hp2 ι hm hPb hlinJ hlinb
  have hJsum : ∑ j ∈ Finset.Ico 0 m, αJ j ht = k₁ := ggSum_Ico_of_eq_ite hm hjt
  have htsum : ∑ j ∈ Finset.Ico 0 m, αt (hJ j) = k₂ := ggSum_Ico_of_eq_ite hm htj
  have hβat : ggChainRoot m αJ αa 0 ht = k₁ := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, hat, hJsum, zero_add]
  have hβbt : ggChainRoot m αJ αb 0 ht = k₁ := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hbt, hJsum, zero_add]
  have hαtca : αt (ggChainCoroot m hJ ha 0) = k₂ := by
    rw [hca, map_add, map_sum, hta, htsum, zero_add]
  have hβaa : ggChainRoot m αJ αa 0 ha = 1 := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, hPa.aa, hPa.sum_ja hm]
    ring
  have hβba : ggChainRoot m αJ αb 0 ha = -1 := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hba, hPa.sum_ja hm]
    ring
  have hβab : ggChainRoot m αJ αa 0 hb = -1 := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, hab, hPb.sum_ja hm]
    ring
  have hβbb : ggChainRoot m αJ αb 0 hb = 1 := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hPb.aa, hPb.sum_ja hm]
    ring
  refine ggFalse_of_opposite_roots hp2 hNT ι
    (mul_mem_ggInduced (mul_mem_ggInduced hφt hψa) (inv_mem_ggInduced hφt)) hψb ?_
    (hPb.chainRoot_chainCoroot 0 (Nat.zero_le _))
    (ggLin_conj_reflection_of_eq ι htt hlinψa hlint hβat hαtca) hlinψb ?_ ?_
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul,
      hPa.chainRoot_chainCoroot 0 (Nat.zero_le _), hβat, hαtca, htt]
    ring
  · refine LinearMap.ext_on hspan fun z hz => ?_
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_Iio] at hz
    rcases hz with (h | h | h) | ⟨j, hj, h⟩
    · rw [h, hβaa, hβba, hta]
      ring
    · rw [h, hβab, hβbb, htb]
      ring
    · rw [h, hβat, hβbt, htt]
      ring
    · rw [← h, hPa.chainRoot_zero_apply hj, hPb.chainRoot_zero_apply hj, htj j hj]
      split_ifs
      · linear_combination -hk
      · ring
  · intro h0
    apply hha
    set S := Submodule.span (ZMod p) ({hb, ht} ∪ hJ '' Set.Iio m)
    have hsJS : ∑ j ∈ Finset.Ico 0 m, hJ j ∈ S := Submodule.sum_mem _ fun j hj =>
      Submodule.subset_span (Or.inr ⟨j, (Finset.mem_Ico.mp hj).2, rfl⟩)
    have hbS : hb ∈ S := Submodule.subset_span (Or.inl (Set.mem_insert _ _))
    have htS : ht ∈ S :=
      Submodule.subset_span (Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rw [hca, hcb] at h0
    have key : ha = (ha + ∑ j ∈ Finset.Ico 0 m, hJ j - k₂ • ht +
        (hb + ∑ j ∈ Finset.Ico 0 m, hJ j)) - ∑ j ∈ Finset.Ico 0 m, hJ j + k₂ • ht -
        (hb + ∑ j ∈ Finset.Ico 0 m, hJ j) := by
      abel
    rw [key, h0, zero_sub]
    exact S.sub_mem (S.add_mem (S.neg_mem hsJS) (S.smul_mem _ htS)) (S.add_mem hbS hsJS)

theorem ggFork_affine_false_D (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {m : ℕ} (hm : 1 ≤ m) {φJ : ℕ → MulAut ↥Bs}
    {φa φb φt φs : MulAut ↥Bs} (hφJ : ∀ j < m, φJ j ∈ ggInduced ⊤ Bs)
    (hφa : φa ∈ ggInduced ⊤ Bs) (hφb : φb ∈ ggInduced ⊤ Bs) (hφt : φt ∈ ggInduced ⊤ Bs)
    (hφs : φs ∈ ggInduced ⊤ Bs) {hJ : ℕ → V} {αJ : ℕ → Module.Dual (ZMod p) V}
    {ha hb ht hs : V} {αa αb αt αs : Module.Dual (ZMod p) V}
    (hPa : GGChainPairing m hJ αJ ha αa) (hPb : GGChainPairing m hJ αJ hb αb)
    (hlinJ : ∀ j < m, ∀ w, ggLin (p := p) ι (φJ j) w = w - αJ j w • hJ j)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hlinb : ∀ w, ggLin (p := p) ι φb w = w - αb w • hb)
    (hlint : ∀ w, ggLin (p := p) ι φt w = w - αt w • ht)
    (hlins : ∀ w, ggLin (p := p) ι φs w = w - αs w • hs) (htt : αt ht = 2) (hss : αs hs = 2)
    (hjt : ∀ j < m, αJ j ht = if j = 0 then -1 else 0)
    (htj : ∀ j < m, αt (hJ j) = if j = 0 then -1 else 0)
    (hjs : ∀ j < m, αJ j hs = if j = 0 then -1 else 0)
    (hsj : ∀ j < m, αs (hJ j) = if j = 0 then -1 else 0) (hts : αt hs = 0) (hst : αs ht = 0)
    (hta : αt ha = 0) (hat : αa ht = 0) (htb : αt hb = 0) (hbt : αb ht = 0) (hsa : αs ha = 0)
    (has : αa hs = 0) (hsb : αs hb = 0) (hbs : αb hs = 0) (hab : αa hb = 0) (hba : αb ha = 0)
    (hspan : Submodule.span (ZMod p) ({ha, hb, ht, hs} ∪ hJ '' Set.Iio m) = ⊤)
    (hha : ha ∉ Submodule.span (ZMod p) ({hb, ht, hs} ∪ hJ '' Set.Iio m)) : False := by
  obtain ⟨hψa, hlinψa⟩ := ggNearEnd_reflection ι hφJ hφa hPa hlinJ hlina
  obtain ⟨hψb, hlinψb⟩ := ggNearEnd_reflection ι hφJ hφb hPb hlinJ hlinb
  obtain ⟨hβa, hca⟩ := ggChainRoot_zero_eq_add hp2 ι hm hPa hlinJ hlina
  obtain ⟨hβb, hcb⟩ := ggChainRoot_zero_eq_add hp2 ι hm hPb hlinJ hlinb
  have hJt : ∑ j ∈ Finset.Ico 0 m, αJ j ht = -1 := ggSum_Ico_of_eq_ite hm hjt
  have hJs : ∑ j ∈ Finset.Ico 0 m, αJ j hs = -1 := ggSum_Ico_of_eq_ite hm hjs
  have htJ : ∑ j ∈ Finset.Ico 0 m, αt (hJ j) = -1 := ggSum_Ico_of_eq_ite hm htj
  have hsJ : ∑ j ∈ Finset.Ico 0 m, αs (hJ j) = -1 := ggSum_Ico_of_eq_ite hm hsj
  have hβat : ggChainRoot m αJ αa 0 ht = -1 := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, hat, hJt, zero_add]
  have hβas : ggChainRoot m αJ αa 0 hs = -1 := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, has, hJs, zero_add]
  have hβbt : ggChainRoot m αJ αb 0 ht = -1 := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hbt, hJt, zero_add]
  have hβbs : ggChainRoot m αJ αb 0 hs = -1 := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hbs, hJs, zero_add]
  have hαtca : αt (ggChainCoroot m hJ ha 0) = -1 := by
    rw [hca, map_add, map_sum, hta, htJ, zero_add]
  have hαsca : αs (ggChainCoroot m hJ ha 0) = -1 := by
    rw [hca, map_add, map_sum, hsa, hsJ, zero_add]
  have hβaa : ggChainRoot m αJ αa 0 ha = 1 := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, hPa.aa, hPa.sum_ja hm]
    ring
  have hβba : ggChainRoot m αJ αb 0 ha = -1 := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hba, hPa.sum_ja hm]
    ring
  have hβab : ggChainRoot m αJ αa 0 hb = -1 := by
    rw [hβa, LinearMap.add_apply, LinearMap.sum_apply, hab, hPb.sum_ja hm]
    ring
  have hβbb : ggChainRoot m αJ αb 0 hb = 1 := by
    rw [hβb, LinearMap.add_apply, LinearMap.sum_apply, hPb.aa, hPb.sum_ja hm]
    ring
  have hl1 := ggLin_conj_reflection_of_eq ι htt hlinψa hlint hβat hαtca
  have hs1 : (ggChainRoot m αJ αa 0 - (-1 : ZMod p) • αt) hs = -1 := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hβas, hts, smul_zero, sub_zero]
  have ht1 : αs (ggChainCoroot m hJ ha 0 - (-1 : ZMod p) • ht) = -1 := by
    rw [map_sub, map_smul, hαsca, hst, smul_zero, sub_zero]
  have hl2 := ggLin_conj_reflection_of_eq ι hss hl1 hlins hs1 ht1
  refine ggFalse_of_opposite_roots hp2 hNT ι
    (mul_mem_ggInduced (mul_mem_ggInduced hφs
      (mul_mem_ggInduced (mul_mem_ggInduced hφt hψa) (inv_mem_ggInduced hφt)))
      (inv_mem_ggInduced hφs)) hψb ?_ (hPb.chainRoot_chainCoroot 0 (Nat.zero_le _)) hl2 hlinψb
    ?_ ?_
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul,
      hPa.chainRoot_chainCoroot 0 (Nat.zero_le _), hβat, hβas, hαtca, hαsca, htt, hss, hts,
      hst]
    ring
  · refine LinearMap.ext_on hspan fun z hz => ?_
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_Iio] at hz
    rcases hz with (h | h | h | h) | ⟨j, hj, h⟩
    · rw [h, hβaa, hβba, hta, hsa]
      ring
    · rw [h, hβab, hβbb, htb, hsb]
      ring
    · rw [h, hβat, hβbt, htt, hst]
      ring
    · rw [h, hβas, hβbs, hts, hss]
      ring
    · rw [← h, hPa.chainRoot_zero_apply hj, hPb.chainRoot_zero_apply hj, htj j hj, hsj j hj]
      split_ifs <;> ring
  · intro h0
    apply hha
    set S := Submodule.span (ZMod p) ({hb, ht, hs} ∪ hJ '' Set.Iio m)
    have hsJS : ∑ j ∈ Finset.Ico 0 m, hJ j ∈ S := Submodule.sum_mem _ fun j hj =>
      Submodule.subset_span (Or.inr ⟨j, (Finset.mem_Ico.mp hj).2, rfl⟩)
    have hbS : hb ∈ S := Submodule.subset_span (Or.inl (Set.mem_insert _ _))
    have htS : ht ∈ S :=
      Submodule.subset_span (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    have hsS : hs ∈ S := Submodule.subset_span
      (Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    rw [hca, hcb] at h0
    have key : ha = (ha + ∑ j ∈ Finset.Ico 0 m, hJ j - (-1 : ZMod p) • ht - (-1 : ZMod p) • hs +
        (hb + ∑ j ∈ Finset.Ico 0 m, hJ j)) - ∑ j ∈ Finset.Ico 0 m, hJ j +
        (-1 : ZMod p) • ht + (-1 : ZMod p) • hs - (hb + ∑ j ∈ Finset.Ico 0 m, hJ j) := by
      abel
    rw [key, h0, zero_sub]
    exact S.sub_mem (S.add_mem (S.add_mem (S.neg_mem hsJS) (S.smul_mem _ htS))
      (S.smul_mem _ hsS)) (S.add_mem hbS hsJS)

end GG

end CFSG.StandardType
