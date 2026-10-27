module

public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerKey
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerTorus
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerLift
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS

theorem ggRootKer_of_chevalleyExtras {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : ChevalleyExtras D k x C O) (hdiv : D.divisible = ∅)
    (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    (hconn : GGSimplyLacedConnected (coxeterMatrix D.isFiniteType)) (h3 : 3 ≤ D.rank) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : kˣ} (hζ : orderOf ζ = p) {ν : GGWeyl D →* K}
    (hν : GGWeylLift D ν) (u : GGWeyl D) (i : Fin D.rank) :
    (∀ β ∈ D.roots, D.rootGroup β ≤ Subgroup.centralizer
          (ggTorusRootKer D p (weylAction D.isFiniteType u (Pi.single i 1))) →
      β = weylAction D.isFiniteType u (Pi.single i 1) ∨
        β = -weylAction D.isFiniteType u (Pi.single i 1)) ∧
    ∀ w : GGWeyl D, (∀ h ∈ ggTorusRootKer D p (weylAction D.isFiniteType u (Pi.single i 1)),
        ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center K) →
      w = 1 ∨ w = u * (coxeterMatrix D.isFiniteType).simple i * u⁻¹ := by
  set γ := weylAction D.isFiniteType u (Pi.single i 1)
  have hsymm := cartan_symm_of_posDef hpd
  have hroots : ∀ {β}, β ∈ D.roots → β ∈ roots D.isFiniteType ∅ := fun hβ => hdiv ▸ hβ
  have hγ : γ ∈ D.roots := weylAction_mem_roots D.isFiniteType u (single_mem_roots i)
  have hcard : 3 ≤ Fintype.card (Fin D.rank) := by rwa [Fintype.card_fin]
  have hord : ∀ m : ℤ, ζ ^ m = 1 ↔ (p : ℤ) ∣ m := fun m => by
    rw [← hζ, orderOf_dvd_iff_zpow_eq_one]
  have hgen : ∀ e : Fin D.rank → ℤ, (p : ℤ) ∣ cartanPair D.cartan γ e →
      ∃ g ∈ ggTorusRootKer D p γ, ∀ β ∈ D.roots, ∀ c : k,
        g * x β c * g⁻¹ = x β (((ζ ^ cartanPair D.cartan β e : kˣ) : k) * c) := by
    intro e he
    obtain ⟨g, hgT, hgp, hg⟩ := ggRootKer_exists_gen hE e (hζ ▸ pow_orderOf_eq_one ζ)
    refine ⟨g, ⟨hgT, hgp, fun z hz => ?_⟩, hg⟩
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 z).mp hz
    have h1 : g * x γ c * g⁻¹ = x γ (((ζ ^ cartanPair D.cartan γ e : kˣ) : k) * c) :=
      hg γ hγ c
    rw [(hord _).mpr he, Units.val_one, one_mul] at h1
    have hcg := mul_inv_eq_iff_eq_mul.mp h1
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact hcg
  refine ⟨fun β hβ hle => ?_, fun w hw => ?_⟩
  ·
    have key := ggRootKer_eq_or_reflect D.isFiniteType hpd hconn hcard hp hp2 (hroots hγ)
      (hroots hβ) (hroots hγ) fun e he => ?_
    · rcases key with h | h
      · exact Or.inl h
      · right
        have hq : cartanPair D.cartan γ γ = 2 :=
          cartanForm_eq_two D.isFiniteType hsymm (hroots hγ)
        rw [h, hq, two_smul, sub_add_cancel_left]
    · obtain ⟨g, hgE, hg⟩ := hgen e he
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (hle (((hE.param β hβ).1 _).mpr ⟨1, rfl⟩)) g hgE
      have h1 : x β (((ζ ^ cartanPair D.cartan β e : kˣ) : k) * 1) = x β 1 := by
        rw [← hg β hβ 1, hcomm, mul_inv_cancel_right]
      have h2 := (hE.param β hβ).2.2 h1
      rw [mul_one] at h2
      rw [ggRootKer_cartanPair_sub_left]
      exact dvd_sub ((hord _).mp (Units.ext h2)) he
  ·
    refine ggRootKer_eq_one_or_conj D.isFiniteType hsymm u i w fun β hβ' => ?_
    have hβ : β ∈ D.roots := by
      show β ∈ roots D.isFiniteType D.divisible
      rw [hdiv]
      exact hβ'
    obtain ⟨a, ha⟩ := ggRootKer_weylLift_conj hE hν w hβ
    have hwβ : weylAction D.isFiniteType w β ∈ D.roots :=
      weylAction_mem_roots D.isFiniteType w hβ
    refine ggRootKer_eq_or_reflect D.isFiniteType hpd hconn hcard hp hp2 hβ' (hroots hwβ)
      (hroots hγ) fun e he => ?_
    obtain ⟨g, hgE, hg⟩ := hgen e he
    have hz := Subgroup.mem_center_iff.mp (hw g hgE)
    have e1 : (ν w * g) * x β 1 * (ν w * g)⁻¹ = x (weylAction D.isFiniteType w β)
        ((a : k) * ((ζ ^ cartanPair D.cartan β e : kˣ) : k)) := by
      calc (ν w * g) * x β 1 * (ν w * g)⁻¹ = ν w * (g * x β 1 * g⁻¹) * (ν w)⁻¹ := by group
        _ = _ := by rw [hg β hβ 1, ha, mul_one]
    have e2 : (ν w * g) * x β 1 * (ν w * g)⁻¹ = x (weylAction D.isFiniteType w β)
        (((ζ ^ cartanPair D.cartan (weylAction D.isFiniteType w β) e : kˣ) : k) *
          (a : k)) := by
      set z := ν w * g * (ν w)⁻¹ * g⁻¹
      have hνg : ν w * g = z * g * ν w := by simp only [z]; group
      rw [hνg]
      calc z * g * ν w * x β 1 * (z * g * ν w)⁻¹ =
          z * (g * (ν w * x β 1 * (ν w)⁻¹) * g⁻¹) * z⁻¹ := by group
        _ = z * x (weylAction D.isFiniteType w β)
            (((ζ ^ cartanPair D.cartan (weylAction D.isFiniteType w β) e : kˣ) : k) *
              (a : k)) * z⁻¹ := by rw [ha, mul_one, hg _ hwβ]
        _ = _ := by rw [← hz, mul_inv_cancel_right]
    have h3 := (hE.param _ hwβ).2.2 (e1.symm.trans e2)
    have h4 : ζ ^ cartanPair D.cartan β e =
        ζ ^ cartanPair D.cartan (weylAction D.isFiniteType w β) e :=
      Units.ext (mul_left_cancel₀ a.ne_zero (h3.trans (mul_comm _ _)))
    rw [ggRootKer_cartanPair_sub_left]
    exact (hord _).mp (by rw [zpow_sub, h4, mul_inv_cancel])

end CFSG.StandardType

end
