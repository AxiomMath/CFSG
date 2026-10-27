module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBstarPlus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNodeMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

open TableBSymp SeitzReduction.OmegaPilot
open scoped commutatorElement

variable {K : Type} [Field K]

section MinusBstar

theorem fixSub_mono {ι : Type} [Fintype ι] [DecidableEq ι] {S S' : ι → Prop}
    (h : ∀ i, S' i → S i) : fixSub (K := K) S ≤ fixSub S' :=
  fun _ hg i hi => hg i (h i hi)

theorem blockInl_mem_fixSub {m : ℕ} {S : Fin m ⊕ Fin m → Prop} {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ fixSub S) :
    blockInl g ∈ fixSub (fun i : LargeEvenMinusIdx m => Sum.elim S (fun _ => True) i) := by
  intro i hi i'
  rw [coe_blockInl]
  rcases i with x | t <;> rcases i' with x' | t'
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Sum.inl.injEq]
    have := hg x hi x'
    rw [Matrix.one_apply] at this
    exact this
  · simp
  · simp
  · simp [Matrix.one_apply]

variable [Finite K] [CharP K 2]

theorem ggBstarElt_omegaMinusGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGBstarElt p m (LargeEvenOmega (LargeEvenQMinus m b c)) := by
  intro E₀ hE₀ hr _ φ hφ hφE
  have := Fact.mk hp
  obtain ⟨ζ, hζo, hζ, hζ1, hζ2⟩ := exists_zeta (K := K) hp hp2 hpq
  have hAGO : E₀.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype ≤
      LargeEvenOrthGroup (LargeEvenQMinus m b c) :=
    (Subgroup.map_subtype_le E₀).trans (omega_le_orth _)
  have hAGc : Nat.card (E₀.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype) = Nat.card E₀ :=
    (Nat.card_congr (E₀.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hAGe : IsElemAbelian p (E₀.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype) :=
    TableB.isElemAbelian_map hE₀ _
  obtain ⟨g, hgO, χ, hχ, hsurj⟩ := exists_orth_conj_minus hp2 hζo hirr hAGO hAGe (hAGc ▸ hr)
  have hcA : ∀ (a : LargeEvenOmega (LargeEvenQMinus m b c)) (ha : a ∈ E₀),
      ((conjOmega hgO a : LargeEvenOmega (LargeEvenQMinus m b c)) : GL (LargeEvenMinusIdx m) K) =
      blockInl (TauCeti.diagGL
        (pairedUnits fun j => χ j ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩)) := by
    intro a ha
    have h1 := hχ ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩
    rw [coe_conjOmega]
    rw [← h1]
  have hE₁blk : ∀ e ∈ E₀.map (conjOmega hgO).toMonoidHom, ∃ u : Fin m → Kˣ,
      (e : GL (LargeEvenMinusIdx m) K) = blockInl (TauCeti.diagGL (pairedUnits u)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, hcA a ha⟩
  have hE₁diag : ∀ e ∈ E₀.map (conjOmega hgO).toMonoidHom,
      ∃ δ, (e : GL (LargeEvenMinusIdx m) K) = TauCeti.diagGL δ := by
    intro e he
    obtain ⟨u, hu⟩ := hE₁blk e he
    exact ⟨_, hu.trans (blockInl_diagGL _)⟩
  have hE₁surj : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) →
      ∃ e ∈ E₀.map (conjOmega hgO).toMonoidHom,
        (e : GL (LargeEvenMinusIdx m) K) = blockInl (TauCeti.diagGL (pairedUnits u)) := by
    intro u hu
    obtain ⟨x, hx⟩ := hsurj u hu
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    refine ⟨conjOmega hgO a, ⟨a, ha, rfl⟩, ?_⟩
    have hx' : x = ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩ := Subtype.ext hax.symm
    rw [hcA a ha, ← hx']
    congr 3
    funext j
    exact hx j
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have h01 : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hζinv1 : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hζ1
  have hne : ζ ≠ ζ⁻¹ := fun h => hζ2 (by nth_rewrite 2 [h]; exact mul_inv_cancel ζ)
  have hpow1 : ∀ (j : Fin m) (z : Kˣ), z ^ p = 1 → ∀ k, (Pi.mulSingle j z : Fin m → Kˣ) k ^ p = 1 :=
    fun j z hz k => by
      rw [Pi.mulSingle_apply]
      split_ifs
      · exact hz
      · exact one_pow p
  have hζinvp : ζ⁻¹ ^ p = 1 := by rw [inv_pow, hζ, inv_one]
  set u₁ : Fin m → Kˣ := Pi.mulSingle i₀ ζ * Pi.mulSingle i₁ ζ⁻¹ with hu₁
  have hu₁p : ∀ k, u₁ k ^ p = 1 := fun k => by
    rw [hu₁, Pi.mul_apply, mul_pow, hpow1 i₀ ζ hζ k, hpow1 i₁ ζ⁻¹ hζinvp k, one_mul]
  have hu₁0 : u₁ i₀ = ζ := by
    rw [hu₁, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm h01), mul_one]
  have hu₁1 : u₁ i₁ = ζ⁻¹ := by
    rw [hu₁, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, one_mul]
  have hu₁o : ∀ j, j ≠ i₀ → j ≠ i₁ → u₁ j = 1 := fun j h0 h1 => by
    rw [hu₁, Pi.mul_apply, Pi.mulSingle_eq_of_ne h0, Pi.mulSingle_eq_of_ne h1, one_mul]
  set E₁ := E₀.map (conjOmega hgO).toMonoidHom with hE₁
  set H : Set (LargeEvenOmega (LargeEvenQMinus m b c)) := {h | h ∈ E₁ ∧
    ((h : GL (LargeEvenMinusIdx m) K) = blockInl (TauCeti.diagGL (pairedUnits u₁)) ∨
      ∃ j : Fin m, j ≠ i₀ ∧ j ≠ i₁ ∧ (h : GL (LargeEvenMinusIdx m) K) =
        blockInl (TauCeti.diagGL (pairedUnits (Pi.mulSingle j ζ))))} with hH
  have hHE : H ⊆ E₁ := fun h hh => hh.1
  obtain ⟨h₁, h₁E, hh₁⟩ := hE₁surj u₁ hu₁p
  have hHsiegel : ∀ h ∈ H, ∃ u : Fin m → Kˣ, (h : GL (LargeEvenMinusIdx m) K) =
      blockInl (TauCeti.diagGL (pairedUnits u)) ∧ (u i₀ : K) * (u i₁ : K) = 1 := by
    rintro h ⟨-, hh | ⟨j, hj0, hj1, hh⟩⟩
    · refine ⟨u₁, hh, ?_⟩
      rw [hu₁0, hu₁1]
      exact Units.mul_inv ζ
    · refine ⟨Pi.mulSingle j ζ, hh, ?_⟩
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hj0), Pi.mulSingle_eq_of_ne (Ne.symm hj1), Units.val_one,
        one_mul]
  have hsieΩ : ∀ x : K, blockInl (siegelGL i₀ i₁ x) ∈ LargeEvenOmega (LargeEvenQMinus m b c) :=
    fun x => blockInl_mem_omegaMinus b c (siegelGL_mem_omegaPlus hζ hζ1 h01 x)
  set Y : Subgroup (LargeEvenOmega (LargeEvenQMinus m b c)) :=
    (blockInl.comp (siegelHom i₀ i₁)).range.comap
      (LargeEvenOmega (LargeEvenQMinus m b c)).subtype with hY
  have hmemY : ∀ y : LargeEvenOmega (LargeEvenQMinus m b c), y ∈ Y ↔
      ∃ x : K, blockInl (siegelGL i₀ i₁ x) = (y : GL (LargeEvenMinusIdx m) K) := by
    intro y
    rw [hY, Subgroup.mem_comap]
    exact ⟨fun ⟨x, hx⟩ => ⟨Multiplicative.toAdd x, hx⟩, fun ⟨x, hx⟩ => ⟨Multiplicative.ofAdd x, hx⟩⟩
  have hconjB : ∀ (u : Fin m → Kˣ) (x : K),
      blockInl (TauCeti.diagGL (pairedUnits u)) * blockInl (siegelGL i₀ i₁ x) *
        (blockInl (TauCeti.diagGL (pairedUnits u)))⁻¹ =
      blockInl (siegelGL i₀ i₁ ((u i₀ : K) * (u i₁ : K) * x)) := by
    intro u x
    rw [← map_inv, ← map_mul, ← map_mul, diagGL_pairedUnits_conj_siegelGL]
  have hYF : BFam H E₁ Y := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := (hmemY y).mp y.2
      refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hx, sq, ← map_mul, siegelGL_mul, CharTwo.add_self_eq_zero,
        show siegelGL i₀ i₁ (0 : K) = 1 from Units.ext (siegelMat_zero i₀ i₁), map_one]
    · intro y hy h hh
      obtain ⟨x, hx⟩ := (hmemY y).mp hy
      obtain ⟨u, hu, hu1⟩ := hHsiegel h hh
      apply Subtype.ext
      have h1 := hconjB u x
      rw [hu1, one_mul, ← hu, hx] at h1
      simp only [Subgroup.coe_mul]
      calc (y : GL (LargeEvenMinusIdx m) K) * (h : GL (LargeEvenMinusIdx m) K) =
          (h : GL (LargeEvenMinusIdx m) K) * (y : GL (LargeEvenMinusIdx m) K) *
            (h : GL (LargeEvenMinusIdx m) K)⁻¹ * (h : GL (LargeEvenMinusIdx m) K) := by rw [h1]
        _ = (h : GL (LargeEvenMinusIdx m) K) * (y : GL (LargeEvenMinusIdx m) K) := by group
    · intro e he y hy
      obtain ⟨x, hx⟩ := (hmemY y).mp hy
      obtain ⟨a, ha, rfl⟩ := he
      rw [hmemY]
      set u := fun j => χ j ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩ with hu
      refine ⟨(u i₀ : K) * (u i₁ : K) * x, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, hcA a ha, ← hx]
      exact (hconjB u x).symm
    · intro y hy
      obtain ⟨x, hx⟩ := (hmemY y).mp hy
      obtain ⟨t₀, ht₀E, ht₀⟩ := hE₁surj (Pi.mulSingle i₀ ζ) (hpow1 i₀ ζ hζ)
      have hζK : (1 : K) - (ζ : K) ≠ 0 := sub_ne_zero.mpr fun h => hζ1 (Units.ext h.symm)
      set x' := x / ((1 : K) - (ζ : K)) with hx'
      obtain ⟨y', hy'⟩ : ∃ y' : LargeEvenOmega (LargeEvenQMinus m b c),
          (y' : GL (LargeEvenMinusIdx m) K) = blockInl (siegelGL i₀ i₁ x') := ⟨⟨_, hsieΩ x'⟩, rfl⟩
      have hy'Y : y' ∈ Y := (hmemY y').mpr ⟨x', hy'.symm⟩
      have hcomm : ⁅y', t₀⁆ = y := by
        apply Subtype.ext
        rw [commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht₀]
        have h1 := hconjB (Pi.mulSingle i₀ ζ) (-x')
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, Units.val_one, mul_one] at h1
        calc (y' : GL (LargeEvenMinusIdx m) K) *
              blockInl (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ))) *
              (y' : GL (LargeEvenMinusIdx m) K)⁻¹ *
              (blockInl (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ))))⁻¹ =
            blockInl (siegelGL i₀ i₁ x') *
              (blockInl (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ))) *
              blockInl (siegelGL i₀ i₁ (-x')) *
              (blockInl (TauCeti.diagGL (pairedUnits (Pi.mulSingle i₀ ζ))))⁻¹) := by
              rw [hy', ← map_inv blockInl (siegelGL i₀ i₁ x'), siegelGL_inv]
              group
          _ = blockInl (siegelGL i₀ i₁ (x' + (ζ : K) * -x')) := by
              rw [h1, ← map_mul, siegelGL_mul]
          _ = (y : GL (LargeEvenMinusIdx m) K) := by
            rw [← hx]
            congr 2
            rw [hx']
            field_simp
            ring
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hy'Y ht₀E
  have hYU : Y ≤ (fixSub fun i => i ≠ Sum.inl (Sum.inr i₀) ∧ i ≠ Sum.inl (Sum.inr i₁)).comap
      (LargeEvenOmega (LargeEvenQMinus m b c)).subtype := by
    intro y hy
    obtain ⟨x, hx⟩ := (hmemY y).mp hy
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, ← hx]
    refine fixSub_mono ?_ (blockInl_mem_fixSub (siegelGL_mem_fixSub i₀ i₁ x))
    rintro (i | t) hi
    · exact ⟨fun h => hi.1 (by rw [h]), fun h => hi.2 (by rw [h])⟩
    · trivial
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    have h1 : (⟨blockInl (siegelGL i₀ i₁ 1), hsieΩ 1⟩ : LargeEvenOmega (LargeEvenQMinus m b c)) ∈
        Y := (hmemY _).mpr ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    have h3 : siegelGL i₀ i₁ (1 : K) = siegelGL i₀ i₁ 0 := by
      rw [show siegelGL i₀ i₁ (0 : K) = 1 from Units.ext (siegelMat_zero i₀ i₁)]
      exact blockInl_injective (h2.trans (map_one _).symm)
    exact one_ne_zero (siegelGL_injective h01 h3)
  set φ₁ := MulAut.congr (conjOmega hgO) φ with hφ₁
  have hφ₁p : φ₁ ^ p = 1 := by rw [hφ₁, ← map_pow, hφ, map_one]
  have hφ₁E : ∀ e ∈ E₁, φ₁ e = e := by
    rintro _ ⟨a, ha, rfl⟩
    simp [hφ₁, hφE a ha]
  obtain ⟨t₀, ht₀E, ht₀⟩ := hE₁surj (Pi.mulSingle i₀ ζ) (hpow1 i₀ ζ hζ)
  have hval : ∀ (u : Fin m → Kˣ) (j : Fin m), (Sum.elim (pairedUnits u) 1 :
      LargeEvenMinusIdx m → Kˣ) (Sum.inl (Sum.inl j)) = u j := fun _ _ => rfl
  have hval' : ∀ (u : Fin m → Kˣ) (j : Fin m), (Sum.elim (pairedUnits u) 1 :
      LargeEvenMinusIdx m → Kˣ) (Sum.inl (Sum.inr j)) = (u j)⁻¹ := fun _ _ => rfl
  have hvalt : ∀ (u : Fin m → Kˣ) (t : Fin 2), (Sum.elim (pairedUnits u) 1 :
      LargeEvenMinusIdx m → Kˣ) (Sum.inr t) = 1 := fun _ _ => rfl
  have hsep : ∀ i, i ≠ Sum.inl (Sum.inl i₀) → i ≠ Sum.inl (Sum.inr i₀) →
      i ≠ Sum.inl (Sum.inl i₁) → i ≠ Sum.inl (Sum.inr i₁) → ∀ k,
      (∀ h ∈ H, ∀ δ, (h : GL (LargeEvenMinusIdx m) K) = TauCeti.diagGL δ → δ k = δ i) →
      ∀ e ∈ E₁, ∀ δ, (e : GL (LargeEvenMinusIdx m) K) = TauCeti.diagGL δ → δ k = δ i := by
    intro i hi0 hi0' hi1 hi1' k hk e he δ hδ
    have hsepj : ∀ j : Fin m, j ≠ i₀ → j ≠ i₁ →
        ∃ h ∈ H, (h : GL (LargeEvenMinusIdx m) K) =
          TauCeti.diagGL (Sum.elim (pairedUnits (Pi.mulSingle j ζ)) 1) := by
      intro j hj0 hj1
      obtain ⟨hj, hjE, hhj⟩ := hE₁surj (Pi.mulSingle j ζ) (hpow1 j ζ hζ)
      exact ⟨hj, ⟨hjE, Or.inr ⟨j, hj0, hj1, hhj⟩⟩, hhj.trans (blockInl_diagGL _)⟩
    have hk1 : ∀ h ∈ H, (h : GL (LargeEvenMinusIdx m) K) =
        TauCeti.diagGL (Sum.elim (pairedUnits u₁) 1) → (Sum.elim (pairedUnits u₁) 1 :
          LargeEvenMinusIdx m → Kˣ) k = Sum.elim (pairedUnits u₁) 1 i :=
      fun h hh hδh => hk h hh _ hδh
    have hH1 : h₁ ∈ H := ⟨h₁E, Or.inl hh₁⟩
    have hk1' := hk1 h₁ hH1 (hh₁.trans (blockInl_diagGL _))
    have hki : k = i ∨ (∃ t, k = Sum.inr t) ∧ (∃ t, i = Sum.inr t) := by
      rcases i with (j | j) | t
      · have hj0 : j ≠ i₀ := fun h => hi0 (by rw [h])
        have hj1 : j ≠ i₁ := fun h => hi1 (by rw [h])
        obtain ⟨hj, hjH, hhj⟩ := hsepj j hj0 hj1
        have h1 := hk hj hjH _ hhj
        rw [hval, Pi.mulSingle_eq_same] at h1
        left
        rcases k with (k | k) | t
        · by_cases hkj : k = j
          · rw [hkj]
          · rw [hval, Pi.mulSingle_eq_of_ne hkj] at h1
            exact absurd h1.symm hζ1
        · exfalso
          rw [hval'] at h1
          by_cases hkj : k = j
          · rw [hkj, Pi.mulSingle_eq_same] at h1
            exact hne h1.symm
          · rw [Pi.mulSingle_eq_of_ne hkj, inv_one] at h1
            exact hζ1 h1.symm
        · exfalso
          rw [hvalt] at h1
          exact hζ1 h1.symm
      · have hj0 : j ≠ i₀ := fun h => hi0' (by rw [h])
        have hj1 : j ≠ i₁ := fun h => hi1' (by rw [h])
        obtain ⟨hj, hjH, hhj⟩ := hsepj j hj0 hj1
        have h1 := hk hj hjH _ hhj
        rw [hval', Pi.mulSingle_eq_same] at h1
        left
        rcases k with (k | k) | t
        · exfalso
          rw [hval] at h1
          by_cases hkj : k = j
          · rw [hkj, Pi.mulSingle_eq_same] at h1
            exact hne h1
          · rw [Pi.mulSingle_eq_of_ne hkj] at h1
            exact hζinv1 h1.symm
        · by_cases hkj : k = j
          · rw [hkj]
          · rw [hval', Pi.mulSingle_eq_of_ne hkj, inv_one] at h1
            exact absurd h1.symm hζinv1
        · exfalso
          rw [hvalt] at h1
          exact hζinv1 h1.symm
      ·
        right
        refine ⟨?_, ⟨t, rfl⟩⟩
        rcases k with (k | k) | t'
        · exfalso
          rw [hvalt, hval] at hk1'
          by_cases hk0 : k = i₀
          · rw [hk0, hu₁0] at hk1'
            exact hζ1 hk1'
          · by_cases hk1'' : k = i₁
            · rw [hk1'', hu₁1] at hk1'
              exact hζinv1 hk1'
            · obtain ⟨hj, hjH, hhj⟩ := hsepj k hk0 hk1''
              have h1 := hk hj hjH _ hhj
              rw [hval, hvalt, Pi.mulSingle_eq_same] at h1
              exact hζ1 h1
        · exfalso
          rw [hvalt, hval'] at hk1'
          by_cases hk0 : k = i₀
          · rw [hk0, hu₁0] at hk1'
            exact hζinv1 hk1'
          · by_cases hk1'' : k = i₁
            · rw [hk1'', hu₁1, inv_inv] at hk1'
              exact hζ1 hk1'
            · obtain ⟨hj, hjH, hhj⟩ := hsepj k hk0 hk1''
              have h1 := hk hj hjH _ hhj
              rw [hval', hvalt, Pi.mulSingle_eq_same] at h1
              exact hζinv1 h1
        · exact ⟨t', rfl⟩
    rcases hki with hki | ⟨⟨t, rfl⟩, ⟨t', rfl⟩⟩
    · rw [hki]
    · obtain ⟨u, hu⟩ := hE₁blk e he
      rw [blockInl_diagGL] at hu
      rw [TauCeti.diagGL_injective (hδ.symm.trans hu), hvalt, hvalt]
  have hδ₁o : ∀ j, j ≠ Sum.inl (Sum.inl i₀) → j ≠ Sum.inl (Sum.inr i₀) →
      j ≠ Sum.inl (Sum.inl i₁) → j ≠ Sum.inl (Sum.inr i₁) →
      (Sum.elim (pairedUnits u₁) 1 : LargeEvenMinusIdx m → Kˣ) j ≠ ζ ∧
        (Sum.elim (pairedUnits u₁) 1 : LargeEvenMinusIdx m → Kˣ) j ≠ ζ⁻¹ := by
    intro j hj0 hj0' hj1 hj1'
    rcases j with (j | j) | t
    · rw [hval, hu₁o j (fun h => hj0 (by rw [h])) (fun h => hj1 (by rw [h]))]
      exact ⟨hζ1.symm, hζinv1.symm⟩
    · rw [hval', hu₁o j (fun h => hj0' (by rw [h])) (fun h => hj1' (by rw [h])), inv_one]
      exact ⟨hζ1.symm, hζinv1.symm⟩
    · rw [hvalt]
      exact ⟨hζ1.symm, hζinv1.symm⟩
  obtain ⟨U₁, hU₁, hU₁2, hU₁E, hU₁φ⟩ := exists_invariant_twoSubgroup (QF := qMinusForm K m b c)
    (isHypCoord_qMinusForm b c i₀) (isHypCoord_qMinusForm b c i₁)
    (fun h => h01 (Sum.inl_injective (Sum.inl_injective h)).symm)
    (fun h => Sum.inl_ne_inr (Sum.inl_injective h))
    (fun h => Sum.inr_ne_inl (Sum.inl_injective h))
    (fun h => h01 (Sum.inr_injective (Sum.inl_injective h)).symm)
    (by rw [coe_qMinusForm]; exact omega_le_orth _) hHE hζ2 (δ₁ := Sum.elim (pairedUnits u₁) 1)
    ⟨h₁, ⟨h₁E, Or.inl hh₁⟩, hh₁.trans (blockInl_diagGL _)⟩ (by rw [hval, hu₁0])
    (by rw [hval', hu₁1, inv_inv]) (by rw [hval', hu₁0]) (by rw [hval, hu₁1]) hδ₁o hE₁diag hsep
    (δ₀ := Sum.elim (pairedUnits (Pi.mulSingle i₀ ζ)) 1)
    ⟨t₀, ht₀E, ht₀.trans (blockInl_diagGL _)⟩ (by rw [hval, Pi.mulSingle_eq_same])
    (by rw [hval', Pi.mulSingle_eq_of_ne h01, inv_one])
    hYF hYU hY1 (hp.odd_of_ne_two hp2) φ₁ hφ₁p hφ₁E
  exact bstar_conclusion_map (conjOmega hgO) hU₁ hU₁2 hU₁E hU₁φ

theorem ggBstarBound_omegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {m : ℕ} (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGBstarBound p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) :=
  ggBstarBound_of_elt hp subset_rfl (center_omegaMinus_eq_bot hp hp2 hpq hm hirr)
    (ggBstarElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot b c))
      (ggBstarElt_omegaMinusGroup hp hp2 hpq (by omega) hirr))

end MinusBstar

end TableBOrth

end CFSG.StandardType
