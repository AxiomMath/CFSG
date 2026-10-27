module

public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
import CFSG.Quasithin.Background.B5FinSp
import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG4OrthUPrim
import CFSG.Quasithin.Background.SimsG4Sp
import CFSG.Quasithin.Background.SimsG49FStar
import CFSG.Quasithin.Background.SimsG49Inv
import CFSG.Quasithin.Background.SimsG49Six

public section

namespace CFSG.Quasithin.SimsG4

namespace G49

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

private theorem nonempty_mulEquiv_statedSp [Finite F] [CharP F 2] (B : LinearMap.BilinForm F V)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F)
    (hb : IsSympBasis B b)
    (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) {k : ℕ} (hk : 0 < k)
    (hcard : Nat.card F₀ = 2 ^ k) :
    Nonempty (↥G₀ ≃* ↥(CFSG.Open.StatedSp 2 (GaloisField 2 k))) := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_symplectic B G₀ b F₀ hb hG hk hcard
  exact ⟨ψ.trans
    ((TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) (GaloisField 2 k)).symm.trans
      (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm))⟩

theorem exists_simple_normal_of_subfield [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) (b : Module.Basis (Fin 4) F V)
    (F₀ : Subfield F) (hb : IsSympBasis B b)
    (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) :
    ∃ N ≤ G₀, (∀ g ∈ G₀, ∀ m ∈ N, g * m * g⁻¹ ∈ N) ∧ IsSimpleGroup ↥N ∧
      (∀ x ∈ G₀, ∀ g ∈ G₀, x * (g * x * g⁻¹) ∈ N) ∧ (∀ c ∈ G₀, c * c ∈ N) ∧
      ∃ t ∈ G₀, ∀ h ∈ G₀, h ∈ N ∨ h * t ∈ N := by
  obtain ⟨k, hk, -, hcard⟩ := exists_card_subfield n hn F₀
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp B G₀ b F₀ hb hG hk hcard
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    obtain rfl : k = 1 := by omega
    letI := Fintype.ofFinite (GaloisField 2 1)
    have hc2 : Fintype.card (GaloisField 2 1) = 2 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
    exact exists_index_two_simple_of_mulEquiv_perm
      (e.trans (CFSG.Quasithin.B5FinSp.theta
        (ZMod.ringEquivOfPrime (GaloisField 2 1) Nat.prime_two hc2)).symm)
  ·
    have h4 : 4 ≤ Nat.card (GaloisField 2 k) := by
      rw [GaloisField.card 2 k hk.ne']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    haveI := CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le
      (K := GaloisField 2 k) (n := 2) h4 (by norm_num)
    exact ⟨G₀, le_rfl, fun g hg m hm => G₀.mul_mem (G₀.mul_mem hg hm) (G₀.inv_mem hg),
      e.isSimpleGroup, fun x hx g hg => G₀.mul_mem hx (G₀.mul_mem (G₀.mul_mem hg hx)
        (G₀.inv_mem hg)), fun c hc => G₀.mul_mem hc hc, 1, G₀.one_mem, fun h hh => Or.inl hh⟩

end G49

theorem g49_case1 {F : Type} [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hprim : ¬ IsImprimitiveOnV G₀) (hD : (transvSet G₀).Nonempty)
    (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (hb : IsSympBasis B b)
    (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) :
    IsSimpleGroup ↥(fStarOf (transvGen G₀)) ∧
      (∃ x ∈ fStarOf (transvGen G₀), ∃ y ∈ fStarOf (transvGen G₀), x * y ≠ y * x) ∧
      (∃ i ∈ invSet B G₀, i ∈ fStarOf (transvGen G₀)) ∧
      IsIrredOnV (fStarOf (transvGen G₀)) := by
  obtain ⟨hfinV, heven⟩ := finite_even_card (F := F) (V := V) hdim
  haveI : Finite V := hfinV
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V)) DFunLike.coe_injective
  rw [transvGen_eq_self_of_subfield B G₀ b F₀ hb halt hnd hG]
  obtain ⟨N, hNG, hNn, hNs, hNx, hNsq, t, ht, hcos⟩ :=
    G49.exists_simple_normal_of_subfield n hn B G₀ b F₀ hb hG
  obtain ⟨t₀, t₁, t₂, t₃, g, ht₀, ht₃, hg, rfl, rfl, hinv, hne⟩ :=
    G49.exists_symplTransv_basis B halt b hnd hb G₀ F₀ hG
  have hx : t₀ * (g * t₀ * g⁻¹) ∈ N := hNx t₀ ht₀ g hg
  have hy : t₃ * (g * t₃ * g⁻¹) ∈ N := hNx t₃ ht₃ g hg
  have hnab : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := ⟨_, hx, _, hy, hne⟩
  have hC : ∀ c ∈ G₀, (∀ m ∈ N, c * m = m * c) → c = 1 := by
    set P : Subgroup (V ≃ₗ[F] V) := G₀ ⊓ Subgroup.centralizer (N : Set (V ≃ₗ[F] V)) with hP
    have hP2 : IsPGroup 2 ↥P := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨hxG, hxC⟩ := Subgroup.mem_inf.mp x.2
      have h1 : (x : V ≃ₗ[F] V) * x = 1 := by
        refine G49.eq_one_of_forall_commute hNs hnab (hNsq _ hxG) fun m hm => ?_
        have hxm : Commute (x : V ≃ₗ[F] V) m := (Subgroup.mem_centralizer_iff.mp hxC m hm).symm
        exact (hxm.mul_left hxm).eq
      simpa [pow_one, pow_two] using h1
    have hPG : ∀ c ∈ G₀, ∀ h ∈ P, c * h * c⁻¹ ∈ P := by
      intro c hc h hh
      obtain ⟨hhG, hhC⟩ := Subgroup.mem_inf.mp hh
      refine Subgroup.mem_inf.mpr ⟨G₀.mul_mem (G₀.mul_mem hc hhG) (G₀.inv_mem hc),
        Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      have hm' : c⁻¹ * m * c⁻¹⁻¹ ∈ N := hNn c⁻¹ (G₀.inv_mem hc) m hm
      rw [inv_inv] at hm'
      have h1 := Subgroup.mem_centralizer_iff.mp hhC _ hm'
      calc m * (c * h * c⁻¹) = c * (c⁻¹ * m * c * h) * c⁻¹ := by group
        _ = c * (h * (c⁻¹ * m * c)) * c⁻¹ := by rw [h1]
        _ = c * h * c⁻¹ * m := by group
    have hbot := core_trivial G₀ hirr heven P hP2 hPG
    intro c hc hcm
    have hcP : c ∈ P := Subgroup.mem_inf.mpr
      ⟨hc, Subgroup.mem_centralizer_iff.mpr fun m hm => (hcm m hm).symm⟩
    rw [hbot] at hcP
    exact Subgroup.mem_bot.mp hcP
  rw [fStarOf_eq_of_simple_normal hNG hNn hNs hnab hC]
  exact ⟨hNs, hnab, ⟨_, hinv, hx⟩, irreducible_of_index_two hirr hprim hNn ht hcos⟩

end CFSG.Quasithin.SimsG4
