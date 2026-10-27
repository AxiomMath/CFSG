module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveY
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup CFSG.Open

theorem gap5X_exists_pi {X Y : Type} [Group X] [Finite X] [Group Y] {n : ℕ} (ψ : X →* Y)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker))
    (e₀ : X ⧸ fusionOddCore X ≃* Perm (Fin n)) :
    ∃ π : Y →* Perm (Fin n), Function.Surjective π ∧
      (∀ x, π (ψ x) = e₀ (QuotientGroup.mk x)) ∧ Odd (Nat.card π.ker) ∧
      (∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N ≤ π.ker) ∧
      ∀ y ∈ π.ker, ∃ x ∈ fusionOddCore X, ψ x = y := by
  classical
  have hker : ψ.ker ≤ fusionOddCore X :=
    CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
  let g₀ : X →* Perm (Fin n) :=
    e₀.toMonoidHom.comp (QuotientGroup.mk' (fusionOddCore X))
  have hg₀ : ψ.ker ≤ g₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    show e₀ (QuotientGroup.mk' (fusionOddCore X) x) = 1
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 (hker hx), map_one]
  let π : Y →* Perm (Fin n) := (MonoidHom.liftOfSurjective ψ hψ) ⟨g₀, hg₀⟩
  have hπψ : ∀ x, π (ψ x) = e₀ (QuotientGroup.mk x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨g₀, hg₀⟩ x
  have hπs : Function.Surjective π := by
    intro z
    obtain ⟨q, hq⟩ := e₀.surjective z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N := fusionOddCore X) q
    exact ⟨ψ x, by rw [hπψ x]; exact hq⟩
  have hker_eq : π.ker = (fusionOddCore X).map ψ := by
    ext y
    constructor
    · intro hy
      rw [MonoidHom.mem_ker] at hy
      obtain ⟨x, rfl⟩ := hψ y
      rw [hπψ x] at hy
      have hmk : (QuotientGroup.mk x : X ⧸ fusionOddCore X) = 1 :=
        e₀.injective (by rw [hy, map_one])
      exact Subgroup.mem_map.2 ⟨x, (QuotientGroup.eq_one_iff x).1 hmk, rfl⟩
    · intro hy
      rw [MonoidHom.mem_ker]
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [hπψ x, (QuotientGroup.eq_one_iff x).2 hx, map_one]
  have hπodd : Odd (Nat.card π.ker) := by
    rw [hker_eq]
    exact Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X)
      (Subgroup.card_map_dvd (fusionOddCore X) ψ)
  have hπmax : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N ≤ π.ker := by
    intro N hNn hNodd
    haveI : (N.comap ψ).Normal := hNn.comap ψ
    have hcomap_odd : Odd (Nat.card (N.comap ψ)) := by
      rw [CFSG.EvenSporadicStandard.Fin76b.natCard_comap_eq_card_ker_mul ψ hψ N]
      exact hodd.mul hNodd
    have hle : N.comap ψ ≤ fusionOddCore X :=
      CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hcomap_odd
    rw [hker_eq]
    calc N = (N.comap ψ).map ψ := (Subgroup.map_comap_eq_self_of_surjective hψ N).symm
      _ ≤ (fusionOddCore X).map ψ := Subgroup.map_mono hle
  have hπker : ∀ y ∈ π.ker, ∃ x ∈ fusionOddCore X, ψ x = y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hψ y
    rw [hπψ x] at hy
    have hmk : (QuotientGroup.mk x : X ⧸ fusionOddCore X) = 1 :=
      e₀.injective (by rw [hy, map_one])
    exact ⟨x, (QuotientGroup.eq_one_iff x).1 hmk, rfl⟩
  exact ⟨π, hπs, hπψ, hπodd, hπmax, hπker⟩

theorem gap5_X {X Y : Type} [Group X] [Finite X] [Group Y] {S Z₁ : Subgroup X} {n : ℕ}
    (hS : BarSituation X S) (h2 : Nat.card S = 2) (hc : CentralInSylow X S)
    (hZ₁ : Z₁ ≤ Subgroup.center X) (ψ : X →* Y) (hψ : Function.Surjective ψ)
    (hψk : ∀ x, ψ x = 1 ↔ x ∈ Z₁) (hn : IsSymGp (X ⧸ fusionOddCore X) n)
    {b : MulAut Y} (hb1 : b ≠ 1) (hb2 : b * b = 1) (hbS : ∀ s ∈ S, b (ψ s) = ψ s)
    (hbO : ∀ o ∈ fusionOddCore X, b (ψ o) = ψ o) :
    6 ≤ n ∧ ∃ (e : Y ≃* Perm (Fin n)) (d : Y), S.map ψ = Subgroup.zpowers d ∧ d * d = 1 ∧
      d ≠ 1 ∧ (7 ≤ n → (e d).IsSwap) := by
  haveI : Finite Y := Finite.of_surjective ψ hψ
  have hker : ψ.ker = Z₁ := Subgroup.ext fun x => by rw [MonoidHom.mem_ker, hψk]
  have hodd : Odd (Nat.card ψ.ker) := by
    rw [hker]
    exact Odd.of_dvd_nat (odd_card_center_of_pCore_eq_bot hS.pCore_eq_bot)
      (Subgroup.card_dvd_of_le hZ₁)
  obtain ⟨d, hdd, hd1, hSd, hcl⟩ := barSituation_map_two hS h2 ψ hψ hodd
  obtain ⟨e₀⟩ := hn
  obtain ⟨π, hπs, -, hπodd, hπmax, hπker⟩ := gap5X_exists_pi ψ hψ hodd e₀
  obtain ⟨s₀, hs₀, hs₀d⟩ : ∃ s ∈ S, ψ s = d := by
    have hd : d ∈ S.map ψ := hSd ▸ Subgroup.mem_zpowers d
    obtain ⟨s, hs, hsd⟩ := Subgroup.mem_map.1 hd
    exact ⟨s, hs, hsd⟩
  have hY : Gap5YHyp π d b :=
    { surjective := hπs
      odd_ker := hπodd
      max := hπmax
      mul_self := hdd
      oddTranspClass := hcl
      central := by simpa only [hSd] using centralInSylow_map ψ hψ S hc
      b_ne_one := hb1
      b_mul_self := hb2
      b_apply := by rw [← hs₀d]; exact hbS s₀ hs₀
      b_ker := fun o ho => by
        obtain ⟨x, hx, rfl⟩ := hπker o ho
        exact hbO x hx }
  obtain ⟨hk, h6, hswap⟩ := gap5_Y hY
  refine ⟨h6, MulEquiv.ofBijective π ⟨?_, hπs⟩, d, hSd, hdd, hd1, hswap⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  exact hk

end CFSG.LocalAnalysis.WeakClosure81

end
