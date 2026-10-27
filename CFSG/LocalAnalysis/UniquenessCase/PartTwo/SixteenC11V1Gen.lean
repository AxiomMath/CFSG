module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Restrict
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Pull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

section Helpers

private theorem s16c11_v1_comm_ident {V : Type} [CommGroup V] (p q s c : V) :
    (p * q * s⁻¹)⁻¹ * (q * s⁻¹ * c) = (p * c⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {W₁ W₂ : Type} [CommGroup W₁] [CommGroup W₂]

private theorem s16c11_v1_commSub_map {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)}
    {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w))
    (hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w)) (S : Subgroup W₁) :
    (commSub S A).map κ = commSub (S.map κ) B := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨a, ha, w, hw, rfl⟩, rfl⟩
    obtain ⟨b, hb, hab⟩ := hAB a ha
    exact ⟨b, hb, κ w, ⟨w, hw, rfl⟩, by rw [map_mul, map_inv, hab w]⟩
  · rintro ⟨b, hb, _, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨a, ha, hab⟩ := hBA b hb
    exact ⟨a w * w⁻¹, ⟨a, ha, w, hw, rfl⟩, by rw [map_mul, map_inv, hab w]⟩

private theorem s16c11_v1_stable_comap {κ : W₁ →* W₂} {A : Subgroup (MulAut W₁)}
    {B : Subgroup (MulAut W₂)}
    (hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w)) {I : Subgroup W₂}
    (hI : StableUnder B I) : StableUnder A (I.comap κ) := by
  intro a ha w hw
  obtain ⟨b, hb, hab⟩ := hAB a ha
  show κ (a w) ∈ I
  rw [hab w]
  exact hI b hb _ hw

end Helpers

section HelpersOne

variable {W : Type} [CommGroup W]

private theorem s16c11_v1_stable_commSub {A : Subgroup (MulAut W)} {Y : Subgroup W}
    (hY : StableUnder A Y) : StableUnder A (commSub Y A) := by
  intro l hl r hr
  induction hr using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨l * x * l⁻¹, A.mul_mem (A.mul_mem hl hx) (A.inv_mem hl),
      l w, hY l hl w hw, ?_⟩
    simp [MulAut.mul_apply]
  | one => simpa using (commSub Y A).one_mem
  | mul a b ha hb iha ihb => simpa [map_mul] using (commSub Y A).mul_mem iha ihb
  | inv a ha ih => simpa [map_inv] using (commSub Y A).inv_mem ih

private theorem s16c11_v1_commSub_commSub {A : Subgroup (MulAut W)} (hperf : ⁅A, A⁆ = A)
    {Y : Subgroup W} (hY : StableUnder A Y) : commSub (commSub Y A) A = commSub Y A := by
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  apply le_antisymm
  · exact commSub_le_of_invariant fun l hl r hr => s16c11_v1_stable_commSub hY l hl r hr
  · refine (Subgroup.closure_le (commSub (commSub Y A) A)).mpr ?_
    rintro _ ⟨x, hx, s, hs, rfl⟩
    set R := commSub Y A with hR
    set E := commSub R A with hE
    let Ψ : ↥A →* W ⧸ E :=
      { toFun := fun y => QuotientGroup.mk (((y : MulAut W) s) * s⁻¹)
        map_one' := by simp
        map_mul' := fun y z => by
          show (QuotientGroup.mk ((((y * z : ↥A)) : MulAut W) s * s⁻¹) : W ⧸ E) =
            QuotientGroup.mk (((y : MulAut W) s) * s⁻¹) *
              QuotientGroup.mk (((z : MulAut W) s) * s⁻¹)
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
          have hc : ((z : MulAut W) s * s⁻¹ : W) ∈ R :=
            Subgroup.subset_closure ⟨z, z.2, s, hs, rfl⟩
          have hgen : ((y : MulAut W) ((z : MulAut W) s * s⁻¹)) *
              ((z : MulAut W) s * s⁻¹)⁻¹ ∈ E :=
            Subgroup.subset_closure ⟨y, y.2, _, hc, rfl⟩
          have e0 : (((y * z : ↥A)) : MulAut W) s = (y : MulAut W) ((z : MulAut W) s) :=
            rfl
          have e1 : (((y * z : ↥A)) : MulAut W) s =
              (y : MulAut W) ((z : MulAut W) s * s⁻¹) * (y : MulAut W) s := by
            rw [e0, map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
          rw [e1, s16c11_v1_comm_ident]
          exact E.inv_mem hgen }
    have hker : Ψ.ker = ⊤ := by
      have := Abelianization.commutator_subset_ker Ψ
      rw [Group.IsPerfect.commutator_eq_top] at this
      exact top_le_iff.mp this
    have h1 : Ψ ⟨x, hx⟩ = 1 := by
      have : (⟨x, hx⟩ : ↥A) ∈ Ψ.ker := hker ▸ Subgroup.mem_top _
      exact this
    exact (QuotientGroup.eq_one_iff _).mp h1

end HelpersOne

theorem s16c11_v1_kernel_eq_bot {W W' : Type} [CommGroup W] [Finite W] [CommGroup W']
    (hW2 : ∀ w : W, w ^ 2 = 1) {κ : W →* W'} (hκ : Function.Surjective κ)
    {A : Subgroup (MulAut W)} {B : Subgroup (MulAut W')} (hperf : ⁅A, A⁆ = A)
    (e : ↥B →* ↥A) (he : Function.Surjective e)
    (hequiv : ∀ (b : ↥B) (w : W), κ ((e b : MulAut W) w) = (b : MulAut W') (κ w))
    (hker : ∀ w, κ w = 1 → w ∈ fixV A) (hcomm : commV A = ⊤)
    {I₀ I₁ : Subgroup W'} (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤)
    (hI₀ : StableUnder B I₀) (hI₁ : StableUnder B I₁)
    (hc₀ : commSub I₀ B = I₀) (hc₁ : commSub I₁ B = I₁)
    (hfix₀ : fixV B ⊓ I₀ = ⊥) (hfix₁ : fixV B ⊓ I₁ = ⊥)
    {D₀ D₁ : FFModel} (hR₀ : D₀.Realizes B I₀ ⊥) (hR₁ : D₁.Realizes B I₁ ⊥)
    (hD₀ : S16C11V1ModelCover D₀) (hD₁ : S16C11V1ModelCover D₁) : κ.ker = ⊥ := by
  have hAB : ∀ a ∈ A, ∃ b ∈ B, ∀ w, κ (a w) = b (κ w) := by
    intro a ha
    obtain ⟨b, hb⟩ := he ⟨a, ha⟩
    refine ⟨b.1, b.2, fun w => ?_⟩
    have h1 := hequiv b w
    have hb' : (e b : MulAut W) = a := congrArg Subtype.val hb
    rw [hb'] at h1
    exact h1
  have hBA : ∀ b ∈ B, ∃ a ∈ A, ∀ w, κ (a w) = b (κ w) := by
    intro b hb
    exact ⟨(e ⟨b, hb⟩).1, (e ⟨b, hb⟩).2, fun w => hequiv ⟨b, hb⟩ w⟩
  set Y₀ : Subgroup W := I₀.comap κ with hY₀
  set J₀ : Subgroup W := commSub Y₀ A with hJ₀
  set Y₁ : Subgroup W := I₁.comap κ with hY₁
  set J₁ : Subgroup W := commSub Y₁ A with hJ₁
  have hYst₀ : StableUnder A Y₀ := s16c11_v1_stable_comap hAB hI₀
  have hYst₁ : StableUnder A Y₁ := s16c11_v1_stable_comap hAB hI₁
  have hJst₀ : StableUnder A J₀ := s16c11_v1_stable_commSub hYst₀
  have hJst₁ : StableUnder A J₁ := s16c11_v1_stable_commSub hYst₁
  have hJc₀ : commSub J₀ A = J₀ := by
    rw [hJ₀]; exact s16c11_v1_commSub_commSub hperf hYst₀
  have hJc₁ : commSub J₁ A = J₁ := by
    rw [hJ₁]; exact s16c11_v1_commSub_commSub hperf hYst₁
  have hYmap₀ : Y₀.map κ = I₀ := by
    rw [hY₀]; exact Subgroup.map_comap_eq_self_of_surjective hκ I₀
  have hYmap₁ : Y₁.map κ = I₁ := by
    rw [hY₁]; exact Subgroup.map_comap_eq_self_of_surjective hκ I₁
  have hκJ₀ : J₀.map κ = I₀ := by
    rw [hJ₀, s16c11_v1_commSub_map hAB hBA, hYmap₀, hc₀]
  have hκJ₁ : J₁.map κ = I₁ := by
    rw [hJ₁, s16c11_v1_commSub_map hAB hBA, hYmap₁, hc₁]
  have hker_le : κ.ker ≤ fixV A := fun w hw => hker w (MonoidHom.mem_ker.1 hw)
  have hfixJ₀ : fixV A ⊓ J₀ = J₀ ⊓ κ.ker := by
    refine le_antisymm ?_ (le_inf (inf_le_right.trans hker_le) inf_le_left)
    rintro u ⟨huA, huJ⟩
    refine ⟨huJ, MonoidHom.mem_ker.2 ?_⟩
    have hIu : κ u ∈ I₀ := by
      rw [← hκJ₀]; exact ⟨u, huJ, rfl⟩
    have hfixu : κ u ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      have h1 := hequiv ⟨b, hb⟩ u
      have h2 : (e ⟨b, hb⟩ : MulAut W) u = u :=
        (mem_fixV.1 huA) (e ⟨b, hb⟩) (e ⟨b, hb⟩).2
      rw [h2] at h1
      exact h1.symm
    have : κ u ∈ fixV B ⊓ I₀ := ⟨hfixu, hIu⟩
    rw [hfix₀, Subgroup.mem_bot] at this
    exact this
  have hfixJ₁ : fixV A ⊓ J₁ = J₁ ⊓ κ.ker := by
    refine le_antisymm ?_ (le_inf (inf_le_right.trans hker_le) inf_le_left)
    rintro u ⟨huA, huJ⟩
    refine ⟨huJ, MonoidHom.mem_ker.2 ?_⟩
    have hIu : κ u ∈ I₁ := by
      rw [← hκJ₁]; exact ⟨u, huJ, rfl⟩
    have hfixu : κ u ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      have h1 := hequiv ⟨b, hb⟩ u
      have h2 : (e ⟨b, hb⟩ : MulAut W) u = u :=
        (mem_fixV.1 huA) (e ⟨b, hb⟩) (e ⟨b, hb⟩).2
      rw [h2] at h1
      exact h1.symm
    have : κ u ∈ fixV B ⊓ I₁ := ⟨hfixu, hIu⟩
    rw [hfix₁, Subgroup.mem_bot] at this
    exact this
  have hR₀' : D₀.Realizes A J₀ (fixV A ⊓ J₀) :=
    s16c11_v1_realizes_pull hκ e he hequiv hker hκJ₀ hfix₀ hJst₀ hR₀
  have hR₁' : D₁.Realizes A J₁ (fixV A ⊓ J₁) :=
    s16c11_v1_realizes_pull hκ e he hequiv hker hκJ₁ hfix₁ hJst₁ hR₁
  have hcov₀ : fixV A ⊓ J₀ = ⊥ :=
    s16c11_v1_cover_restrict hD₀ hW2 hJst₀ hJc₀ hR₀'
  have hcov₁ : fixV A ⊓ J₁ = ⊥ :=
    s16c11_v1_cover_restrict hD₁ hW2 hJst₁ hJc₁ hR₁'
  have hJker₀ : J₀ ⊓ κ.ker = ⊥ := by
    rw [← hfixJ₀]; exact hcov₀
  have hJker₁ : J₁ ⊓ κ.ker = ⊥ := by
    rw [← hfixJ₁]; exact hcov₁
  have hmap : (J₀ ⊔ J₁).map κ = ⊤ := by
    rw [Subgroup.map_sup, hκJ₀, hκJ₁, hsup]
  have hdecomp : (J₀ ⊔ J₁) ⊔ κ.ker = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : κ w ∈ (J₀ ⊔ J₁).map κ := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hjw⟩ := hw
    refine Subgroup.mem_sup.2 ⟨j, hj, j⁻¹ * w, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hjw, inv_mul_cancel]
    · group
  have hsupJst : StableUnder A (J₀ ⊔ J₁) := by
    intro a ha u hu
    obtain ⟨j₀, hj₀, j₁, hj₁, rfl⟩ := Subgroup.mem_sup.1 hu
    simpa [map_mul] using Subgroup.mul_mem_sup (hJst₀ a ha j₀ hj₀) (hJst₁ a ha j₁ hj₁)
  have hle : commSub ⊤ A ≤ J₀ ⊔ J₁ := by
    rw [← hdecomp, commSub, Subgroup.closure_le]
    rintro _ ⟨a, ha, u, hu, rfl⟩
    obtain ⟨j, hj, z, hz, rfl⟩ := Subgroup.mem_sup.1 hu
    have hzfix : a z = z := (mem_fixV.1 (hker z (MonoidHom.mem_ker.1 hz))) a ha
    have hmem : a j * j⁻¹ ∈ commSub (J₀ ⊔ J₁) A :=
      Subgroup.subset_closure ⟨a, ha, j, hj, rfl⟩
    have hfin : a j * j⁻¹ ∈ J₀ ⊔ J₁ := commSub_le_of_invariant hsupJst hmem
    have heq : a (j * z) * (j * z)⁻¹ = a j * j⁻¹ := by
      rw [map_mul, hzfix, mul_inv_rev]
      group
    rw [heq]
    exact hfin
  have htopJ : J₀ ⊔ J₁ = ⊤ := by
    have := hle
    rw [← commV_eq_commSub, hcomm] at this
    exact top_le_iff.1 this
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzJ : z ∈ J₀ ⊔ J₁ := by rw [htopJ]; exact Subgroup.mem_top _
  obtain ⟨j₀, hj₀, j₁, hj₁, hz_eq⟩ := Subgroup.mem_sup.1 hzJ
  have hkj : κ j₀ * κ j₁ = 1 := by
    rw [← map_mul, hz_eq, MonoidHom.mem_ker.1 hz]
  have hI₀ : κ j₀ ∈ I₀ := by rw [← hκJ₀]; exact ⟨j₀, hj₀, rfl⟩
  have hI₁ : κ j₁ ∈ I₁ := by rw [← hκJ₁]; exact ⟨j₁, hj₁, rfl⟩
  have hboth : κ j₀ ∈ I₀ ⊓ I₁ := by
    refine ⟨hI₀, ?_⟩
    have hkj' : κ j₀ = (κ j₁)⁻¹ := eq_inv_of_mul_eq_one_left hkj
    rw [hkj']; exact I₁.inv_mem hI₁
  have hzero : κ j₀ = 1 := by
    rw [hinf, Subgroup.mem_bot] at hboth
    exact hboth
  have hj₀bot : j₀ = 1 := by
    have : j₀ ∈ J₀ ⊓ κ.ker := ⟨hj₀, MonoidHom.mem_ker.2 hzero⟩
    rw [hJker₀, Subgroup.mem_bot] at this
    exact this
  have hzero₁ : κ j₁ = 1 := by
    rw [hzero, one_mul] at hkj
    exact hkj
  have hj₁bot : j₁ = 1 := by
    have : j₁ ∈ J₁ ⊓ κ.ker := ⟨hj₁, MonoidHom.mem_ker.2 hzero₁⟩
    rw [hJker₁, Subgroup.mem_bot] at this
    exact this
  rw [← hz_eq, hj₀bot, hj₁bot, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
