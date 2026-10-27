module

public import CFSG.Quasithin.Background.Harris.Sp4.Rank
public import CFSG.Quasithin.Background.Harris.Sp4.Descent
public import CFSG.Quasithin.Background.Harris.Sp4.Parity
public import CFSG.Quasithin.Background.Harris.Sp4.Numerics
public import CFSG.Quasithin.Background.Harris.Sp4.Natural
public import CFSG.Quasithin.Background.Harris.Sp4.SelfDual
public import CFSG.Quasithin.Background.Harris.Sp4.End
public import CFSG.Quasithin.Background.SmithB42Sp4Ident

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem m_bounds {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m) {f : ℕ}
    (hf : 2 ≤ f) (φ : ↥L ≃* antiSp (GaloisField 2 f)) :
    m ≤ 3 * f + 1 ∧ (Even f → m ≤ 3 * f) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨h1, h2, -⟩ := card_le_of_offender hf hK (offender_of_setting hs φ)
  rw [hs.A_card] at h1 h2
  exact ⟨(Nat.pow_le_pow_iff_right (by norm_num)).mp h1,
    fun hev => (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2 hev)⟩

theorem m_add_two_le {m f : ℕ} (hf : 2 ≤ f) (h : m ≤ 3 * f + 1 ∧ (Even f → m ≤ 3 * f)) :
    m + 2 ≤ 4 * f := by
  rcases Nat.even_or_odd f with hev | hodd
  · have := h.2 hev
    omega
  · obtain ⟨k, hk⟩ := hodd
    have := h.1
    omega

theorem m_le_of_label {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m) {f : ℕ}
    (hf : 2 ≤ f) (φ : ↥L ≃* antiSp (GaloisField 2 f)) {d j : ℕ} (hd : 1 ≤ d)
    (hdisp : ∀ z : antiSp (GaloisField 2 f), z * z = 1 →
      dispRank (piOf L φ z) = d * (if j % 2 = 0 then rk0 z else rk1 z)) : m ≤ 3 * f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases Nat.even_or_odd f with hev | hodd
  · exact (m_bounds hs hf φ).2 hev
  · have H := offender_of_setting hs φ
    obtain ⟨-, -, h3⟩ := card_le_of_offender hf hK H
    have := h3 (fun a => normAut_mem_inner_of_odd hf hodd hK H hd hdisp a)
    rw [hs.A_card] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

theorem finrank_eq_of_addEquiv {F : Type} [Field F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (θ : V ≃+ (Fin 4 → F)) : Module.finrank (ZMod 2) V = 4 * f := by
  have h1 := CFSG.Quasithin.B42Sp4.natCard_eq_two_pow_finrank (U := V)
  have h2 : Nat.card V = 2 ^ (f * 4) := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_fun, hF, ← pow_mul, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [h2] at h1
  have := Nat.pow_right_injective le_rfl h1
  omega

theorem case9_holds {Γ A L : Subgroup (GLV V)} {m : ℕ} (hs : OneCompSetting Γ A L m) {f : ℕ}
    (hf : 2 ≤ f) (φ : ↥L ≃* antiSp (GaloisField 2 f)) : G93Case9 L m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hKf : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have hirr : Fact (CFSG.Quasithin.B42Sp4.repOf (piOf L φ)).IsIrreducible :=
    ⟨repOf_piOf_isIrreducible φ hs.L_irr⟩
  have hnt : ∃ g, CFSG.Quasithin.B42Sp4.repOf (piOf L φ) g ≠ 1 :=
    ⟨invX _, fun h1 => invX_ne_one (piOf_injective L φ (LinearEquiv.toLinearMap_injective
      (h1.trans (map_one (CFSG.Quasithin.B42Sp4.repOf (piOf L φ))).symm)))⟩
  have hm := m_add_two_le hf (m_bounds hs hf φ)
  obtain ⟨d, S, hd1, hDcard, -, hfd, hdimD, hsingle⟩ := exists_label hKf (by omega) (piOf L φ) hnt
  have hdimV : Module.finrank (ZMod 2) V = d * 4 ^ S.card := by
    rw [finrank_eq_mul_of_card hDcard, hdimD]
  have hs1 : S.card = 1 := s_eq_one hfd (hdimV ▸ hs.bound) hm
  have hdim4 : Module.finrank (EndRing (CFSG.Quasithin.B42Sp4.repOf (piOf L φ))) V = 4 := by
    rw [hdimD, hs1]; norm_num
  obtain ⟨i, θ, hθ⟩ := CFSG.Quasithin.B42Sp4.exists_natural_of_four hKf (by omega) (piOf L φ)
    hnt hdim4
  have hV : Module.finrank (ZMod 2) V = 4 * f := finrank_eq_of_addEquiv hK θ
  have hdf : d = f := by
    rw [hdimV, hs1] at hV
    omega
  obtain ⟨j, hj⟩ := hsingle hs1
  have hm3 : m ≤ 3 * f := m_le_of_label hs hf φ hd1 hj
  refine ⟨f, ⟨by omega, hV, ?_, hm3, isNatural_of_twist hf φ i θ hθ, fun h => absurd h (by omega)⟩,
    ?_, ?_⟩
  · have := hs.bound
    omega
  · refine endIsField_of_natCard hs.L_irr ?_
    rw [natCard_endCommutant_eq L φ, hDcard, hdf]
  · let ψ : V ≃ₗ[ZMod 2] (Fin 4 → GaloisField 2 f) :=
      LinearEquiv.mk (AddMonoidHom.toZModLinearMap 2 θ.toAddMonoidHom) θ.symm θ.left_inv
        θ.right_inv
    refine selfDual_of_symplectic (L := L) ψ
      (fun h => glMat (((minorAut (GaloisField 2 f) ^ i) (φ h) : antiSp (GaloisField 2 f)) :
        GL (Fin 4) (GaloisField 2 f))) (fun h v => ?_) (fun h => ?_)
    · have := hθ (φ h) v
      rw [piOf_apply, MulEquiv.symm_apply_apply] at this
      exact this
    · exact mem_antiSp.mp ((minorAut (GaloisField 2 f) ^ i) (φ h)).2

end CFSG.Quasithin.G11.Harris.Sp4
