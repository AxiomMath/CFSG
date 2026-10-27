module

public import CFSG.Quasithin.Vol2.Ch11SecBK2D
public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.H13.NQCatParabolicSp4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace BK2

section Sylow

variable {W : Type} [Group W] [Finite W]

theorem exists_mem_iff_of_sylow {H S P Q : Subgroup (MulAut W)} {Z U₁ U₂ Y : Subgroup W}
    {q : ℕ} (hSH : S ≤ H ⊓ Ch11.SecA.stabW U₂) (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z)
    (hP : QuasithinUnique.IsSylowTwoOf P H) (hPS : P ≤ S)
    (huniq : ∀ Y' : Subgroup W, Z ≤ Y' → Y' ≤ U₂ → Z.relIndex Y' = q →
      P ≤ Ch11.SecA.stabW Y' → ∀ w, w ∈ Y' ↔ w ∈ U₁)
    (hQ : QuasithinUnique.IsSylowTwoOf Q S) (hZY : Z ≤ Y) (hYU : Y ≤ U₂)
    (hYi : Z.relIndex Y = q) (hQY : Q ≤ Ch11.SecA.stabW Y) :
    ∃ x ∈ S, ∀ w, w ∈ Y ↔ x w ∈ U₁ := by
  have hPS' := C1GN.isSylowTwoOf_of_le hP hPS (hSH.trans inf_le_left)
  obtain ⟨x₀, hx₀, rfl⟩ := hPS'.exists_conj hQ
  have hx₀H : x₀ ∈ H := (Subgroup.mem_inf.mp (hSH hx₀)).1
  have hx₀U : x₀ ∈ Ch11.SecA.stabW U₂ := (Subgroup.mem_inf.mp (hSH hx₀)).2
  set Y' : Subgroup W := Y.comap (x₀ : MulAut W).toMonoidHom with hY'
  have hmem : ∀ w, w ∈ Y' ↔ x₀ w ∈ Y := fun w => Iff.rfl
  have hZc : Z.comap (x₀ : MulAut W).toMonoidHom = Z := by
    ext w
    refine ⟨fun hw => ?_, fun hw => hHZ x₀ hx₀H w hw⟩
    have h1 := hHZ x₀⁻¹ (H.inv_mem hx₀H) _ hw
    rwa [MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self] at h1
  have hY'i : Z.relIndex Y' = q := by
    calc Z.relIndex Y' = (Z.comap (x₀ : MulAut W).toMonoidHom).relIndex Y' := by rw [hZc]
      _ = Z.relIndex (Y'.map (x₀ : MulAut W).toMonoidHom) := Subgroup.relIndex_comap _ _ _
      _ = q := by rw [hY', Subgroup.map_comap_eq_self_of_surjective x₀.surjective, hYi]
  have key := huniq Y' (fun z hz => hZY (hHZ x₀ hx₀H z hz))
    (fun w hw => (Ch11.SecA.mem_stabW.mp hx₀U w).mpr (hYU hw)) hY'i (fun p hp => by
      rw [Ch11.SecA.mem_stabW]
      intro w
      have hc : x₀ * p * x₀⁻¹ ∈ Subgroup.map (MulAut.conj x₀).toMonoidHom P :=
        ⟨p, hp, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have h1 := (Ch11.SecA.mem_stabW.mp (hQY hc)) (x₀ w)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
      rw [hmem, hmem, h1])
  refine ⟨x₀⁻¹, S.inv_mem hx₀, fun w => ?_⟩
  rw [← key, hmem, MulAut.apply_inv_self]

end Sylow

section Sp4

variable {K : Type} [Field K] [Finite K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

omit [Finite K] in
theorem e0_ne_zero_sp (g : StatedSp 2 K) : mat 2 K g *ᵥ KGNat.vec4 (1 : K) 0 0 0 ≠ 0 := by
  intro h0
  have := congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h0
  simp only [KGNat.mat_inv_mulVec, Matrix.mulVec_zero] at this
  exact one_ne_zero (congrFun this (.inl 0))

omit [Finite K] in
theorem conj_g_mulVec_sp (g u : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (g * u * g⁻¹) *ᵥ (mat 2 K g *ᵥ x) = mat 2 K g *ᵥ (mat 2 K u *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
    show g * u * g⁻¹ * g = g * u by group]

theorem mem_pre_line_iff_of_stable_sp
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {Y : Subgroup W} (hZY : Z ≤ Y)
    (hYU : Y ≤ hf.pre (KGNat.gmapSp g (KGNat.spPlane K)).toAddSubgroup)
    (hYi : Z.relIndex Y = Nat.card K)
    (hst : ∀ r : K, ∀ w ∈ Y, ((π (g * nSp r * g⁻¹) : ↥H) : MulAut W) w ∈ Y) :
    ∀ w, w ∈ Y ↔ w ∈ hf.pre (KGNat.gmapSp g (KGNat.spLine K)).toAddSubgroup := by
  set v₀ := mat 2 K g *ᵥ KGNat.vec4 (1 : K) 0 0 0 with hv₀def
  have hv₀ : v₀ ≠ 0 := e0_ne_zero_sp g
  have hI : Nat.card (hf.img Y) = Nat.card K := by rw [hf.card_img, hYi]
  have hline : ∀ y ∈ hf.img Y, ∃ c : K, y = c • v₀ := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, mat 2 K g⁻¹ *ᵥ f w = x := ⟨_, rfl⟩
    have hfw : f w = mat 2 K g *ᵥ x := by rw [← hx, KGNat.mat_mulVec_inv]
    have hpl : x ∈ KGNat.spPlane K := by
      rw [← hx]
      exact KGNat.mem_gmapSp.mp (hYU hw)
    obtain ⟨h2, h3⟩ := KGNat.mem_spPlane.mp hpl
    by_cases h1 : x (.inl 1) = 0
    · refine ⟨x (.inl 0), ?_⟩
      have he : x = x (.inl 0) • KGNat.vec4 (1 : K) 0 0 0 :=
        KGNat.vec4_eq (by simp [KGNat.vec4]) (by simp [KGNat.vec4, h1])
          (by simp [KGNat.vec4, h2]) (by simp [KGNat.vec4, h3])
      rw [hfw]
      conv_lhs => rw [he]
      rw [Matrix.mulVec_smul]
    · exfalso
      have hall : ∀ c : K, c • v₀ ∈ hf.img Y := by
        intro c
        refine ⟨((π (g * nSp (c / x (.inl 1)) * g⁻¹) : ↥H) : MulAut W) w * w⁻¹,
          Y.mul_mem (hst _ w hw) (Y.inv_mem hw), ?_⟩
        have hu : mat 2 K (nSp (c / x (.inl 1))) *ᵥ x = x + c • KGNat.vec4 (1 : K) 0 0 0 := by
          rw [KGNat.nSp_mulVec]
          refine KGNat.vec4_eq ?_ (by simp [KGNat.vec4]) (by simp [KGNat.vec4])
            (by simp [KGNat.vec4, h2])
          simp only [KGNat.vec4_apply_inl0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [div_mul_cancel₀ c h1]
          simp
        rw [hf.map_mul_inv, hf.act4, hfw, conj_g_mulVec_sp, hu, Matrix.mulVec_add,
          Matrix.mulVec_smul, add_sub_cancel_left]
      refine false_of_line hv₀ hI hall ⟨w, hw, rfl⟩ fun c hc => h1 ?_
      have h3' : x = c • KGNat.vec4 (1 : K) 0 0 0 := by
        rw [← hx, hc, Matrix.mulVec_smul, KGNat.mat_inv_mulVec]
      rw [h3']
      simp [KGNat.vec4]
  have hall := eq_line_of_card hv₀ hI hline
  intro w
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hline _ ⟨w, hw, rfl⟩
    exact KGNat.mem_gmapSp_spLine_iff.mpr ⟨c, hc⟩
  · intro hw
    obtain ⟨c, hc⟩ := KGNat.mem_gmapSp_spLine_iff.mp hw
    rw [hf.mem_iff hZY w, hc]
    exact hall c

theorem l2Point_Sp4 {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π)
    {P : Subgroup (MulAut W)} (hP : QuasithinUnique.IsSylowTwoOf P H) {U₁ U₂ : Subgroup W}
    (hU₁ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 1 U₁) (hU₂ : Ch11.SecA.IsFlagW H P Z (2 ^ n) 2 U₂)
    {Q : Subgroup (MulAut W)}
    (hQ : QuasithinUnique.IsSylowTwoOf Q (perfectCore (H ⊓ Ch11.SecA.stabW U₂)))
    {Y : Subgroup W} (hZY : Z ≤ Y) (hYU : Y ≤ U₂) (hYi : Z.relIndex Y = 2 ^ n)
    (hQY : Q ≤ Ch11.SecA.stabW Y) :
    ∃ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW U₂), ∀ w, w ∈ Y ↔ x w ∈ U₁ := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
    (KGNat.four_le_card hn hK)
  obtain ⟨f, hf, g, hg, rfl⟩ := KGNat.KA.exists_point_coords hn hK hW hπ hP hU₁
  rw [← hK] at hU₂ hYi
  obtain ⟨S, hS, hc, rfl⟩ := KGNat.exists_eq_pre_of_isFlagW_sp hW hf hg hU₂
  obtain rfl := (KGNat.eq_std_of_stable_sp hS).2.1 hc
  have hPS : P ≤ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (KGNat.gmapSp g (KGNat.spPlane K)).toAddSubgroup)) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    rw [show perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (KGNat.gmapSp g (KGNat.spPlane K)).toAddSubgroup)) = Ch11.SecS.gammaW H
          (hf.pre (KGNat.gmapSp g (KGNat.spPlane K)).toAddSubgroup) from rfl,
      Ch11.SecS.C11P9A.gammaW_pre_eq hf g 1 _ KGNat.flag_two_eq]
    rw [Ch11.SecS.C11P9A.Usp_eq_unipotent] at hu
    exact ⟨u, CFSG.Quasithin.H13.NQCat.Sp4.unipotent_le_perfectCore hK4 1 hu, rfl⟩
  refine exists_mem_iff_of_sylow (perfectCore_le _)
    (fun h hh z hz => hπ.2.2.2.2.1 ⟨h, hh⟩ z hz) hP hPS (fun Y' hZY' hY'U hY'i hPY' => ?_)
    hQ hZY hYU hYi hQY
  exact mem_pre_line_iff_of_stable_sp hf g hZY' hY'U hY'i fun r w hw =>
    (Ch11.SecA.mem_stabW.mp (hPY' ((hg _).mpr ⟨_, KGNat.nSp_mem_Usp r, rfl⟩)) w).mp hw

end Sp4

end BK2

end CFSG.Quasithin.Vol2.Ch11.SecB
