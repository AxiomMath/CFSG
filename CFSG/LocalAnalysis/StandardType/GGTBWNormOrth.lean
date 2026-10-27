module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormSigned
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGEvenSignedNormalizer
public import CFSG.LocalAnalysis.StandardType.GGEvenSignedDiagram
public import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace OrthExcEven

open SpCoord Multiplicative

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem inv_pow_mul_pred_eq (hp : p.Prime) {k : ℕ} (x : Fin k → Multiplicative (ZMod p))
    (c : ℕ) : x⁻¹ ^ (c * (p - 1)) = x ^ c := by
  have hx : x ^ p = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (x i), ← ofAdd_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, ofAdd_zero]
  rw [inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
  have hcp : c * (p - 1) + c = p * c := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hcp, pow_mul, hx, one_pow]

theorem exists_evenSignedModelSC_normalizer_odd (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R Odd)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A) {φ : MulAut ↥A}
    (hφ : φ ∈ Subgroup.normalizer
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A))) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (w : MulAut ↥A),
      3 ≤ k ∧ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
        IsSignedPerm ⇑((MulAut.congr Θ).symm w) ∧ ∃ c : ℕ, ∀ a, φ a = (w a) ^ c := by
  obtain ⟨k, Θ, hk, hko, -, hD, hP, -, hN⟩ :=
    exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hWdef
  have hWin : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α) → MulAut.congr Θ α ∈ W := by
    rintro α ⟨n, hn, hnα⟩
    rw [← hnα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  set Wc := W.comap (MulAut.congr Θ).toMonoidHom with hWc
  have hWcsp : ∀ u ∈ Wc, IsSignedPerm ⇑u := by
    intro u hu
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hu
    have hv' : MulAut.congr Θ u = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    have h1 := hN n hcN
    rwa [← hv', MulEquiv.symm_apply_apply] at h1
  have hdW : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ Wc := fun i j hij =>
    hWin _ (hD i j hij)
  have htW : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ Wc := fun a b _ =>
    hWin _ (hP _)
  obtain ⟨i₀⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hM := negAut_mul_sgnAut_mem hdW hko i₀
  have hsplit : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      u ∈ Wc ∨ u * negAut ∈ Wc := by
    intro u hu
    rcases mem_or_mul_mem_of_isSignedPerm hdW htW i₀ hu with h1 | h1
    · exact Or.inl h1
    · right
      have h2 := Wc.mul_mem h1 hM
      rwa [negAut_mul_comm, show u * sgnAut i₀ * (sgnAut i₀ * negAut) =
        u * (sgnAut i₀ * sgnAut i₀) * negAut by group, sgnAut_mul_self, mul_one] at h2
  set φ' := (MulAut.congr Θ).symm φ with hφ'
  have hφφ' : φ = MulAut.congr Θ φ' := (MulEquiv.apply_symm_apply _ _).symm
  have hnorm : ∀ u ∈ Wc, φ' * u * φ'⁻¹ ∈ Wc := fun u hu => by
    show MulAut.congr Θ (φ' * u * φ'⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv, ← hφφ']
    exact (Subgroup.mem_normalizer_iff.mp hφ _).mp hu
  have hnorm' : ∀ u ∈ Wc, φ'⁻¹ * u * φ' ∈ Wc := fun u hu => by
    show MulAut.congr Θ (φ'⁻¹ * u * φ') ∈ W
    rw [map_mul, map_mul, map_inv, ← hφφ']
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hφ) _).mp hu
    rwa [inv_inv] at h1
  have hconjN : ∀ (x y u : MulAut (Fin k → Multiplicative (ZMod p))),
      x * u * y = x * (u * negAut) * y * negAut := fun x y u => by
    calc x * u * y = x * u * y * (negAut * negAut) := by rw [negAut_mul_self, mul_one]
      _ = x * u * (y * negAut) * negAut := by group
      _ = x * u * (negAut * y) * negAut := by rw [negAut_mul_comm y]
      _ = x * (u * negAut) * y * negAut := by group
  have h1 : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ' * u * φ'⁻¹) := by
    intro u hu
    rcases hsplit u hu with hw | hw
    · exact hWcsp _ (hnorm u hw)
    · rw [hconjN φ' φ'⁻¹ u]
      exact isSignedPerm_mul_negAut (hWcsp _ (hnorm _ hw))
  have h2 : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ'⁻¹ * u * φ') := by
    intro u hu
    rcases hsplit u hu with hw | hw
    · exact hWcsp _ (hnorm' u hw)
    · rw [hconjN φ'⁻¹ φ' u]
      exact isSignedPerm_mul_negAut (hWcsp _ (hnorm' _ hw))
  obtain ⟨w, hw, c, hc⟩ := exists_isSignedPerm_pow hp hp2 hk h1 h2
  rcases hsplit w hw with hw' | hw'
  · refine ⟨k, Θ, MulAut.congr Θ w, hk, hw', by simpa only [MulEquiv.symm_apply_apply] using hw,
      c, fun a => ?_⟩
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [hφφ', MulAut.congr_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hc, map_pow]
  · refine ⟨k, Θ, MulAut.congr Θ (w * negAut), hk, hw',
      by simpa only [MulEquiv.symm_apply_apply] using isSignedPerm_mul_negAut hw,
      c * (p - 1), fun a => ?_⟩
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [hφφ', MulAut.congr_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mul_apply, negAut_apply]
    rw [hc, map_inv, ← map_pow Θ ((w f)⁻¹) (c * (p - 1)), inv_pow_mul_pred_eq hp]

theorem ggTorusWNormSC_of_evenSignedPermEltSC_odd (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R Odd) :
    GGTorusWNormSC p R I :=
  ggTorusWNormSC_of_signedNormalizer hp2 fun hψ hker hperf hA hAI h3 hsc hφ =>
    exists_evenSignedModelSC_normalizer_odd hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc hφ

theorem exists_coordBasis {Y : Type} [Group Y] {A : Subgroup Y} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V) {k : ℕ}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) :
    ∃ b : Module.Basis (Fin k) (ZMod p) V,
      ∀ f, ι (Additive.ofMul (Θ f)) = ∑ i, toAdd (f i) • b i := by
  let ξ : Additive (Fin k → Multiplicative (ZMod p)) ≃+ (Fin k → ZMod p) :=
    (MulEquiv.toAdditive (MulEquiv.piMultiplicative (fun _ : Fin k => ZMod p)).symm).trans
      (AddEquiv.additiveMultiplicative (Fin k → ZMod p))
  let η : (Fin k → ZMod p) ≃+ V := ξ.symm.trans ((MulEquiv.toAdditive Θ).trans ι)
  let T : (Fin k → ZMod p) ≃ₗ[ZMod p] V :=
    LinearEquiv.ofBijective (η.toAddMonoidHom.toZModLinearMap p) η.bijective
  refine ⟨(Pi.basisFun (ZMod p) (Fin k)).map T, fun f => ?_⟩
  have h1 : ι (Additive.ofMul (Θ f)) = T (fun i => toAdd (f i)) := rfl
  rw [h1]
  conv_lhs => rw [← (Pi.basisFun (ZMod p) (Fin k)).sum_repr (fun i => toAdd (f i))]
  simp only [map_sum, map_smul, Module.Basis.map_apply, Pi.basisFun_repr]

theorem ggLin_congr_apply_ofMul [Fact p.Prime] {Y : Type} [Group Y] {A : Subgroup Y} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V) {k : ℕ}
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (u : MulAut (Fin k → Multiplicative (ZMod p)))
    (f : Fin k → Multiplicative (ZMod p)) :
    ggLin (p := p) ι (MulAut.congr Θ u) (ι (Additive.ofMul (Θ f))) =
      ι (Additive.ofMul (Θ (u f))) := by
  rw [ggLin_apply_ofMul, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem exists_evenSignedDatum_basis [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type}
    [Group Y] {A : Subgroup Y} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥A ≃+ V) {k : ℕ} (hk : 2 ≤ k) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    {Λ : Type} [Fintype Λ] (φ : Λ → MulAut ↥A) (hh : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • hh i)
    (hφD : ∀ i, (MulAut.congr Θ).symm (φ i) ∈ DScalarTorus.evenSignedGroup (p := p) (N := k))
    (hdsc : ∀ a a' : Fin k, a ≠ a' →
      MulAut.congr Θ (sgnAut a * sgnAut a') ∈ Subgroup.closure (Set.range φ)) :
    ∃ b : Module.Basis (Fin k) (ZMod p) V,
      (∀ (j : Fin k) (x : ZMod p), ι (Additive.ofMul (Θ (Pi.mulSingle j (ofAdd x)))) = x • b j) ∧
      (∀ i, ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p), (∀ a, c a = 1 ∨ c a = -1) ∧
        ∏ a, c a = 1 ∧ ∀ a, b a - α i (b a) • hh i = c a • b (σ a)) ∧
      (∀ v : V, (∀ i, α i v = 0) → v = 0) ∧ k ≤ Fintype.card Λ := by
  obtain ⟨b, hbf⟩ := exists_coordBasis (p := p) ι Θ
  have hδ : ∀ (j : Fin k) (x : ZMod p),
      ι (Additive.ofMul (Θ (Pi.mulSingle j (ofAdd x)))) = x • b j := by
    intro j x
    rw [hbf]
    simp only [toAdd_mulSingle, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  have hcongr := ggLin_congr_apply_ofMul (p := p) ι Θ
  have hrD : ∀ i, ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p),
      (∀ a, c a = 1 ∨ c a = -1) ∧ ∏ a, c a = 1 ∧
        ∀ a, b a - α i (b a) • hh i = c a • b (σ a) := by
    intro i
    obtain ⟨σ, c, hc1, hc2, hu⟩ := hφD i
    refine ⟨σ, c, hc1, hc2, fun a => ?_⟩
    rw [← hlin, ← one_smul (ZMod p) (b a), ← hδ, ← MulEquiv.apply_symm_apply
      (MulAut.congr Θ) (φ i), hcongr, IsSignedPerm.apply_mulSingle hu, mul_one, hδ]
  have hsep : ∀ v : V, (∀ i, α i v = 0) → v = 0 := by
    intro v hv
    obtain ⟨g, rfl⟩ := (Additive.ofMul.trans ι.toEquiv).surjective v
    obtain ⟨f, rfl⟩ := Θ.surjective g
    let S : Subgroup (MulAut ↥A) :=
      { carrier := {u | ggLin (p := p) ι u (ι (Additive.ofMul (Θ f))) =
          ι (Additive.ofMul (Θ f))}
        one_mem' := by simp
        mul_mem' := fun {u u'} hu hu' => by
          simp only [Set.mem_ofPred_eq, map_mul, LinearEquiv.mul_apply] at hu hu' ⊢
          rw [hu', hu]
        inv_mem' := fun {u} hu => by
          simp only [Set.mem_ofPred_eq, map_inv] at hu ⊢
          conv_lhs => rw [← hu]
          exact LinearEquiv.symm_apply_apply _ _ }
    have hSφ : Subgroup.closure (Set.range φ) ≤ S := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      show ggLin (p := p) ι (φ i) _ = _
      change ggLin (p := p) ι (φ i) (Equiv.toFun _ _) = _
      rw [hlin]
      simp only [Equiv.toFun_as_coe, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
        EquivLike.coe_coe] at hv ⊢
      rw [hv i, zero_smul, sub_zero]
    have hf : f = 1 := by
      funext a
      obtain ⟨a', ha'⟩ : ∃ a' : Fin k, a' ≠ a := ⟨if a.val = 0 then ⟨1, by omega⟩ else
        ⟨0, by omega⟩, by
          split_ifs with h0
          · intro h1
            have := congrArg Fin.val h1
            simp at this
            omega
          · intro h1
            have := congrArg Fin.val h1
            simp at this
            omega⟩
      have h1 := hSφ (hdsc a a' (Ne.symm ha'))
      change ggLin (p := p) ι _ _ = _ at h1
      rw [hcongr] at h1
      have h2 := Θ.injective (Additive.ofMul.injective (ι.injective h1))
      have h3 := congrArg (fun g : Fin k → Multiplicative (ZMod p) => toAdd (g a)) h2
      simp only [MulAut.mul_apply, sgnAut_apply, Function.update_self,
        Function.update_of_ne (Ne.symm ha'), toAdd_inv] at h3
      have h4 := coord_eq_zero_of_eq_neg hp hp2 h3.symm
      simpa using congrArg ofAdd h4
    simp [hf]
  have hcard : k ≤ Fintype.card Λ := by
    let Lα : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi fun i => α i
    have hinj : Function.Injective Lα := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      exact hsep v fun i => congrFun hv i
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
      at h1
  exact ⟨b, hδ, hrD, hsep, hcard⟩

theorem ggTorusWNormSC_of_evenSignedPermEltSC_ge_five (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedPermEltSC p R (5 ≤ ·)) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ hh α
    hM hC hpair hlin hgen ψ' hψ'
  have : (MulAut.conj : L' →* MulAut L').range.Normal :=
    RootCentExc.normal_range_mulAutConj
  have hn := mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal
    (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A) hψ'
  obtain ⟨k, Θ, hk3, hk5, -, hD, hP, -, hN⟩ :=
    exists_evenSignedPermModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hWdef
  have hWin : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ u) → MulAut.congr Θ u ∈ W := by
    rintro u ⟨n, hn, hnu⟩
    rw [← hnu]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  set Wc := W.comap (MulAut.congr Θ).toMonoidHom with hWc
  have hWcsp : ∀ u ∈ Wc, IsSignedPerm ⇑u := by
    intro u hu
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hu
    have hv' : MulAut.congr Θ u = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    have h1 := hN n hcN
    rwa [← hv', MulEquiv.symm_apply_apply] at h1
  have hdW : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ Wc := fun i j hij =>
    hWin _ (hD i j hij)
  have hpW : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ Wc := fun σ => hWin _ (hP σ)
  have htW : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ Wc := fun a b _ => hpW _
  set φ' := (MulAut.congr Θ).symm ψ' with hφ'
  have hφφ' : ψ' = MulAut.congr Θ φ' := (MulEquiv.apply_symm_apply _ _).symm
  have hnorm : ∀ u ∈ Wc, φ' * u * φ'⁻¹ ∈ Wc := fun u hu => by
    show MulAut.congr Θ (φ' * u * φ'⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv, ← hφφ']
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp hu
  have hnorm' : ∀ u ∈ Wc, φ'⁻¹ * u * φ' ∈ Wc := fun u hu => by
    show MulAut.congr Θ (φ'⁻¹ * u * φ') ∈ W
    rw [map_mul, map_mul, map_inv, ← hφφ']
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp hu
    rwa [inv_inv] at h1
  obtain ⟨w0, hw0, c, hc⟩ :=
    exists_isSignedPerm_pow_of_normalizes_dk hp hp2 hk5 hWcsp hdW hpW hnorm hnorm'
  have hcl : Subgroup.closure (Set.range φ) ≤ (ggHL ι φ hh α).comap (ggLin (p := p) ι) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure (Or.inl (Or.inl (Set.mem_range_self i)))
  have hclosure : ∀ u ∈ Wc, ggLin (p := p) ι (MulAut.congr Θ u) ∈ ggHL ι φ hh α :=
    fun u hu => hcl (hgen ▸ hu)
  have hwin : ggLin (p := p) ι (MulAut.congr Θ w0) ∈ ggHL ι φ hh α := by
    by_cases hw0W : w0 ∈ Wc
    · exact hclosure _ hw0W
    have hDle : DScalarTorus.evenSignedGroup ≤ Wc := DScalarTorus.evenSignedGroup_le hp2 hdW hpW
    have hDd : ∀ i j : Fin k, i ≠ j →
        sgnAut i * sgnAut j ∈ DScalarTorus.evenSignedGroup (p := p) (N := k) :=
      fun i j hij => DScalarTorus.sgnAut_pair_mem_evenSignedGroup hij
    have hDt : ∀ a b : Fin k, a ≠ b →
        permAut (Equiv.swap a b) ∈ DScalarTorus.evenSignedGroup (p := p) (N := k) :=
      fun a b _ => DScalarTorus.permAut_mem_evenSignedGroup _
    obtain ⟨i₀⟩ : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    have hWcD : Wc ≤ DScalarTorus.evenSignedGroup := by
      intro u hu
      by_contra huD
      rcases mem_or_mul_mem_of_isSignedPerm hDd hDt i₀ (hWcsp u hu) with h1 | h1
      · exact huD h1
      have hs0 : sgnAut i₀ ∈ Wc := by
        have h2 := Wc.mul_mem (Wc.inv_mem hu) (hDle h1)
        rwa [inv_mul_cancel_left] at h2
      have hs : ∀ j, sgnAut j ∈ Wc := by
        intro j
        by_cases hj : j = i₀
        · rw [hj]
          exact hs0
        · have h2 := Wc.mul_mem (hdW j i₀ hj) hs0
          rwa [mul_assoc, sgnAut_mul_self, mul_one] at h2
      exact hw0W (mem_of_isSignedPerm hs htW hw0)
    obtain ⟨b, hδ, hrD, -, hcard⟩ := exists_evenSignedDatum_basis hp hp2 ι (by omega) Θ φ hh α
      hlin (fun i => hWcD (show MulAut.congr Θ ((MulAut.congr Θ).symm (φ i)) ∈ W by
        rw [MulEquiv.apply_symm_apply, hgen]
        exact Subgroup.subset_closure (Set.mem_range_self i)))
      (fun a a' h => hgen ▸ hWin _ (hD a a' h))
    have hcongr := ggLin_congr_apply_ofMul (p := p) ι Θ
    obtain ⟨y, g, hg, hgy, hga⟩ :=
      exists_signChange_mem_ggDiagramSet hp2 b hM hC hh α hpair hrD hk3 hcard
    have hgs : ggLin (p := p) ι (MulAut.congr Θ (sgnAut y)) = g := by
      refine b.ext' fun a => ?_
      have hba : b a = ι (Additive.ofMul (Θ (Pi.mulSingle a (ofAdd 1)))) := by
        rw [hδ, one_smul]
      rw [hba, hcongr, ← hba]
      by_cases hay : a = y
      · subst hay
        rw [sgnAut_mulSingle_self, hgy, ← Pi.mulSingle_inv, ← ofAdd_neg, hδ, neg_one_smul]
      · rw [sgnAut_mulSingle_of_ne hay, hga a hay, ← hba]
    have hw1 : w0 * sgnAut y ∈ Wc := by
      rcases mem_or_mul_mem_of_isSignedPerm hDd hDt y hw0 with h1 | h1
      · exact absurd (hDle h1) hw0W
      · exact hDle h1
    have he : MulAut.congr Θ w0 = MulAut.congr Θ (w0 * sgnAut y) * MulAut.congr Θ (sgnAut y) := by
      rw [← map_mul, mul_assoc, sgnAut_mul_self, mul_one]
    rw [he, map_mul, hgs]
    exact Subgroup.mul_mem _ (hclosure _ hw1) (Subgroup.subset_closure (Or.inr hg))
  refine ggWNormConcl_of_signed hp2 ι φ hh α hk3 Θ hwin
    (by simpa only [MulEquiv.symm_apply_apply] using hw0) (c := c) fun a => ?_
  obtain ⟨f, rfl⟩ := Θ.surjective a
  rw [hφφ', MulAut.congr_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hc, map_pow]


end OrthExcEven

section Certificates


theorem ggTorusWNormSC_omegaPlus_signed {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    (hm : 5 ≤ m) (hmo : Odd m) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (OrthRest.RPlus K m) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m)
  exact ggTorusWNormSC_of_signedEltSC hp hp2 subset_rfl hZ hcp
    (ggOrthSignedTorusInput_holds.1 K m p hm hmo hp hpq)

theorem ggTorusWNormSC_omegaMinus_signed {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    {b c : K} (hm : 3 ≤ m) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ (Odd m ∧ p ∣ Nat.card K + 1)) :
    GGTorusWNormSC p (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  exact ggTorusWNormSC_of_signedEltSC hp hp2 subset_rfl hZ hcp
    (ggOrthSignedTorusInput_holds.2 K m p b c hm hbc hp hpq)

theorem largeEvenLabelAll_wnorm_orth_signed {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : GGOrthSignedLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, l, n⟩
  rcases hlab with ⟨htag, hl, hodd, hpq⟩ | ⟨htag, hl, hpq⟩
  · dsimp only at htag hl hodd hpq ⊢
    subst htag
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_omegaPlus_signed hl hodd hp hp2 (by rw [hK]; exact hpq)
  · dsimp only at htag hl hpq ⊢
    subst htag
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, b, c, hbc, hQ, ?_⟩
    refine ggTorusWNormSC_omegaMinus_signed (by omega) hbc hp hp2 ?_
    rw [hK]
    rcases hpq with h | ⟨hev, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, h⟩
      obtain ⟨j, hj⟩ := hev
      exact ⟨j - 1, by omega⟩


open OrthExcEven

theorem ggTorusWNormSC_omegaPlus_evenOdd {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    (hm : 5 ≤ m) (hmo : Odd m) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusWNormSC p (OrthRest.RPlus K m) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m)
  exact ggTorusWNormSC_of_evenSignedPermEltSC_odd hp hp2 subset_rfl hZ hcp
    ((ggOrthEvenTorusInput_holds.1 K m p (by omega) hp (Or.inl hpq)).mono fun k hk => by
      rw [hk]; exact hmo)

theorem ggTorusWNormSC_omegaMinus_evenOdd {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    {b c : K} (hm : 4 ≤ m) (hme : Even m) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ m) hbc
  exact ggTorusWNormSC_of_evenSignedPermEltSC_odd hp hp2 subset_rfl hZ hcp
    ((ggOrthEvenTorusInput_holds.2 K m p b c hm hme hbc hp hpq).mono fun k hk => by
      rw [hk]; exact hme.add_one)

theorem largeEvenLabelAll_wnorm_orth_evenOdd {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : GGOrthEvenOddLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, l, n⟩
  rcases hlab with ⟨htag, hl, hodd, hpq⟩ | ⟨htag, hl, hodd, hpq⟩
  · dsimp only at htag hl hodd hpq ⊢
    subst htag
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
    exact ggTorusWNormSC_omegaPlus_evenOdd hl hodd hp hp2 (by rw [hK]; exact hpq)
  · dsimp only at htag hl hodd hpq ⊢
    subst htag
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hQ ⊢
    obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, hfield, hfinite, hK, b, c, hbc, hQ, ?_⟩
    refine ggTorusWNormSC_omegaMinus_evenOdd (by omega) ?_ hbc hp hp2 (by rw [hK]; exact hpq)
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j, by omega⟩

theorem ggTorusWNormSC_omegaPlus_evenEven {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    (hm : 6 ≤ m) (hme : Even m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) :
    GGTorusWNormSC p (OrthRest.RPlus K m) (LargeEvenInnSet _) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m)
  exact ggTorusWNormSC_of_evenSignedPermEltSC_ge_five hp hp2 subset_rfl hZ hcp
    ((ggOrthEvenTorusInput_holds.1 K m p (by omega) hp (hpq.imp id fun h => ⟨hme, h⟩)).mono
      fun k hk => by rw [hk]; omega)

theorem largeEvenLabelAll_wnorm_orth_evenEven {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : lab.tag = .D ∧ 6 ≤ lab.rank ∧ Even lab.rank ∧
      (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, l, n⟩
  obtain ⟨htag, hl, hev, hpq⟩ := hlab
  dsimp only at htag hl hev hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [ite_eq_right (by omega)] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_omegaPlus_evenEven hl hev hp hp2 (by rw [hK]; exact hpq)

end Certificates

end CFSG.StandardType

end
