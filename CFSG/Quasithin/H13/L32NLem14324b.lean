module

public import CFSG.Quasithin.H13.L32NLem14324a
public import CFSG.Quasithin.Background.F6ResL28
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Fact
public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.GH74.SmallRanks.PSU3
public import CFSG.Adapters.GeneralizedFitting
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.L14324

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem lt_of_concl11 (hXΓ : X ≤ Γ) {k : ℕ} (hk : Nat.card X = 2 ^ k)
    (h11 : G112Concl11 Γ) : Nat.card X < 16 := by
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, ⟨φ⟩⟩ := h11
  let N : Subgroup ↥Γ := genFittingFStar ↥Γ
  have hNn : N.Normal := A7Mod.genFittingFStar_normal' ↥Γ
  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 3) = Fintype.card CFSG.Quasithin.GF8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    rfl
  let ψ : ↥N ≃* F6.L28Res.G8 :=
    φ.trans ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans F6.L28Res.slEquiv)
  have hZ : Subgroup.center ↥N = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : ψ z ∈ Subgroup.center F6.L28Res.G8 := Subgroup.mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := ψ.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y']
    have h2 : Subgroup.center F6.L28Res.G8 = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have h3 : F6.L28Res.slEquiv.symm w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
          CFSG.Quasithin.GF8) := Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨y', rfl⟩ := F6.L28Res.slEquiv.symm.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y']
      rw [F6.L28Res.sl_center_eq_bot, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_bot]
      simpa using congrArg F6.L28Res.slEquiv h3
    rw [h2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact ψ.injective (h1.trans (map_one ψ).symm)
  let c : ↥Γ →* MulAut ↥N := MulAut.conjNormal
  have hc : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (N : Set ↥Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : ↥Γ)) hg
      simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc n * g = g * n * g⁻¹ * g := by rw [h1]
        _ = g * n := by group
    have hgN : g ∈ N := CFSG.Adapters.generalized_fitting_self_centralizing ↥Γ hgC
    have hgZ : (⟨g, hgN⟩ : ↥N) ∈ Subgroup.center ↥N := Subgroup.mem_center_iff.mpr fun n =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC n n.2)
    rw [hZ, Subgroup.mem_bot] at hgZ
    exact congrArg Subtype.val hgZ
  have hAut : Nat.card (MulAut ↥N) = 1512 := by
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv, F6.L28Res.card_mulAut]
  have hdvdΓ : Nat.card ↥Γ ∣ 1512 := by
    have h1 := Subgroup.card_subgroup_dvd_card c.range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hc).toEquiv, hAut] at h1
  have hXs : Nat.card (X.subgroupOf Γ) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv
  have hdvdX : 2 ^ k ∣ 2 ^ 3 * 189 := by
    rw [← hk, ← hXs]
    exact (Subgroup.card_subgroup_dvd_card _).trans hdvdΓ
  have hk3 := le_of_two_pow_dvd (by decide) hdvdX
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk3
  omega

theorem lt_of_concl6U33
    (hXΓ : X ≤ Γ) (hX : IsElemAbelian 2 X) {k : ℕ} (hk : Nat.card X = 2 ^ k)
    (h : G11.IsG2NaturalModule Γ ⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆) :
    Nat.card X < 8 := by
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨φ, -⟩ := h
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨u⟩ := lred3_equiv_g2derived_psu33 (K := GaloisField 2 1) hK
  let P := Assembly.LowTwoRank.StatedProj
    (Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1)))
  let ψ : ↥Γ ≃* P := φ.trans u.symm
  have : Finite P := Finite.of_equiv ↥Γ ψ.toEquiv
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel P .PSU 3 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1), inferInstance,
      inferInstance, by
        rw [GaloisField.card 3 (2 * 1) (by norm_num)]
        norm_num, ⟨MulEquiv.refl _⟩⟩
  have h2 := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_three hmodel
  have := hX.1
  let f : ↥X →* P := ψ.toMonoidHom.comp (Subgroup.inclusion hXΓ)
  have hf : Function.Injective f := ψ.injective.comp (Subgroup.inclusion_injective hXΓ)
  have hkle : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup P) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num)
      (fun a b => mul_comm' a b) (fun a => Subtype.ext (hX.2 a a.2)) hk f hf le_top
  have hk2 : k ≤ 2 := hkle.trans h2
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hk2
  omega

end CFSG.Quasithin.H13.L14324
