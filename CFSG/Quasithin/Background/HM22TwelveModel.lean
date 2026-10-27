module

public import CFSG.Quasithin.Background.H12OneHatM22PfTrans

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.H.Mathieu.H12Pf

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem fpf_of_isHat
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (hW : Nat.card W = 4096) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (hz1 : z ≠ 1) :
    ∀ w : W, (z : MulAut W) w = w → w = 1 := by
  set zz : MulAut W := (z : MulAut W) with hzz
  have hz3 : ∀ w : W, zz (zz (zz w)) = w := by
    have h1 : (⟨z, hz⟩ : ↥(Subgroup.center ↥L)) ^ 3 = 1 := by
      rw [← hL.2.1]
      exact pow_card_eq_one'
    have h2 : zz ^ 3 = 1 := by
      have := congrArg (fun x : ↥(Subgroup.center ↥L) => ((x : ↥L) : MulAut W)) h1
      simpa [hzz] using this
    intro w
    have := congrArg (fun φ : MulAut W => φ w) h2
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcomm : ∀ (g : ↥L) (w : W), zz ((g : MulAut W) w) = (g : MulAut W) (zz w) := by
    intro g w
    have := congrArg (fun x : ↥L => (x : MulAut W) w) (Subgroup.mem_center_iff.mp hz g)
    simpa [hzz, MulAut.mul_apply] using this.symm
  have hsq : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hV w
  let N : W →* W := MonoidHom.id W * zz.toMonoidHom * (zz * zz).toMonoidHom
  have hN : ∀ w, N w = w * zz w * zz (zz w) := fun w => rfl
  have hfixN : ∀ w ∈ N.ker, zz w = w → w = 1 := by
    intro w hw hzw
    rw [MonoidHom.mem_ker, hN, hzw, hzw, hsq, one_mul] at hw
    exact hw
  have hinvN : ∀ g : ↥L, ∀ w ∈ N.ker, (g : MulAut W) w ∈ N.ker := by
    intro g w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    rw [hN, hcomm, hcomm, ← map_mul, ← map_mul, ← hN, hw, map_one]
  have hne : N.ker ≠ ⊥ := by
    have hzz1 : zz ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
    obtain ⟨w, hw⟩ : ∃ w, zz w ≠ w := by
      by_contra hall
      push Not at hall
      exact hzz1 (MulEquiv.ext hall)
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨w * zz w, ?_⟩, fun h1 => hw ?_⟩
    · rw [MonoidHom.mem_ker, hN, map_mul, map_mul, hz3]
      calc w * zz w * (zz w * zz (zz w)) * (zz (zz w) * w)
          = (w * w) * (zz w * zz w) * (zz (zz w) * zz (zz w)) := by ac_rfl
        _ = 1 := by simp only [hsq]
    · have h2 : w * zz w = 1 := congrArg Subtype.val h1
      calc zz w = w * (w * zz w) := by rw [← mul_assoc, hsq, one_mul]
        _ = w := by rw [h2, mul_one]
  have hcard := le_card_of_fpf hV hL (by rw [hW]; norm_num) hz _ N.ker rfl hne hinvN hfixN
  have htop : N.ker = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) (hW ▸ hcard))
  intro w hw
  have h1 : N w = 1 := by
    rw [← MonoidHom.mem_ker, htop]
    exact Subgroup.mem_top w
  rw [hN, hw, hw, hsq, one_mul] at h1
  exact h1

theorem isIrrSec_of_isHat
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (hW : Nat.card W = 4096) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ := by
  have : Nontrivial ↥(Subgroup.center ↥L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hL.2.1]
    norm_num
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥L))
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hfix := fpf_of_isHat hV hW hL hz hz1'
  refine ⟨bot_lt_iff_ne_bot.mpr fun h0 => ?_, fun J hJ _ _ => ?_⟩
  · have : Nat.card (⊤ : Subgroup W) = 1 := by rw [h0, Subgroup.card_bot]
    rw [Subgroup.card_top, hW] at this
    norm_num at this
  · by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · right
      have hcard := le_card_of_fpf hV hL (by rw [hW]; norm_num) hz _ J rfl hJ0
        (fun g u hu => hJ g u hu) (fun u _ hu => hfix u hu)
      exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _)
        (hW ▸ hcard))

theorem exists_model_of_isHat
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (hW : Nat.card W = 4096) (hL : IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    ∃ (ψ : ↥H12Cert.G ≃* ↥L) (θ : W ≃* Multiplicative (Fin 12 → ZMod 2)),
      ∀ (g : ↥H12Cert.G) (w : W),
        Multiplicative.toAdd (θ (((ψ g : ↥L) : MulAut W) w)) =
          ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
            (Multiplicative.toAdd (θ w)) := by
  have hirr := isIrrSec_of_isHat hV hW hL
  obtain ⟨π, hπ⟩ := hatM22SmallModules_holds W hV L hL hirr (by rw [hW]; norm_num)
  have hπinj := hπ.injective_of_faithful (FFModel.nat_faithful hatM22Γ₀)
  obtain ⟨E, hE⟩ := exists_coord_of_realizesVia hπ
  let ψ : ↥H12Cert.G ≃* ↥L := hatEquivG.symm.trans (MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩)
  let θ : W ≃* Multiplicative (Fin 12 → ZMod 2) := E.trans realAddEquiv.toMultiplicative
  refine ⟨ψ, θ, fun g w => ?_⟩
  obtain ⟨γ, rfl⟩ := hatEquivG.surjective g
  have hψ : ψ (hatEquivG γ) = π γ := by
    simp only [ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hθ : ∀ x, Multiplicative.toAdd (θ x) = realV (Multiplicative.toAdd (E x)) := fun _ => rfl
  rw [hψ, hatEquivG_val, hθ, hθ]
  exact (congrArg realV (hE γ w)).trans (realV_mulVec_GL _ _)

end CFSG.Quasithin.H.Mathieu.M22Link
