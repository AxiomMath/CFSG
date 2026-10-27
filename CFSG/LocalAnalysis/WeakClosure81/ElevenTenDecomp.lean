module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenTenAut
public import CFSG.Quasithin.Background.E6TwentyFiveA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G] {V : Subgroup G}

structure Eleven11Decomp (hV : IsElemAbelian 2 V) (M X U : Subgroup G) (s : ℕ)
    (Y : Fin s → Subgroup (MulAut (IntMod V hV))) (Vs : Fin s → Subgroup (IntMod V hV))
    (i₀ : Fin s) : Prop where
  body : E6.E624Body hV M X s Y Vs
  fixV_eq_bot : fixV (E6.e624Y hV M X) = ⊥
  fixV_map : (fixV (autI hV X)).map (E3.valHom hV) = U
  card_X : Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1
  card_commSub : Nat.card (commSub ⊤ (autI hV X)) = 2 ^ E3.mQuot V U
  odd_X : Odd (Nat.card (autI hV X))
  Y_le : ∀ i, Y i ≤ autI hV M
  Y_ne_bot : ∀ i, Y i ≠ ⊥
  vs_sup : ⨆ i, Vs i = ⊤
  vs_ne_bot : ∀ i, Vs i ≠ ⊥
  case : autI hV X = Y i₀ ∨
    (Nat.card (autI hV X) = 3 ∧ autI hV X ≤ Y i₀ ∧ Nat.card (Y i₀) = 21 ∧
      (∃ a ∈ Y i₀, ∃ b ∈ Y i₀, a * b ≠ b * a) ∧ ∀ j, Nat.card (Vs j) = 8)
  card_vs : autI hV X = Y i₀ → ∀ j, Nat.card (Vs j) = 2 ^ E3.mQuot V U

theorem e624Concl_of_hyp102 (h104 : Asc81c.Thm104) (hV : IsElemAbelian 2 V) {M X : Subgroup G}
    {r : ℕ} (hyp : Asc81c.Hyp102 (autI hV M) (autI hV X))
    (hXcard : Nat.card (autI hV X) = 2 ^ r - 1)
    (hcardc : Nat.card (commSub ⊤ (autI hV X)) = 2 ^ r) :
    E6.E624Concl hV M X := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  set Gb := autI hV M with hGb
  set Xb := autI hV X with hXb
  set Ω : Set (Subgroup (MulAut (IntMod V hV))) :=
    {Y | ∃ φ ∈ Gb, Y = Xb.map (MulAut.conj φ).toMonoidHom} with hΩdef
  have hconj1 : Xb.map (MulAut.conj (1 : MulAut (IntMod V hV))).toMonoidHom = Xb := by
    rw [map_one]
    exact Subgroup.map_id Xb
  have hXΩ : Xb ∈ Ω := ⟨1, Gb.one_mem, hconj1.symm⟩
  have hΩhyp : ∀ Y ∈ Ω, Asc81c.Hyp102 Gb Y := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact Asc81c.hyp102_map_conj hyp hφ
  have hmapmap : ∀ φ ψ : MulAut (IntMod V hV), (Xb.map (MulAut.conj φ).toMonoidHom).map
      (MulAut.conj ψ).toMonoidHom = Xb.map (MulAut.conj (ψ * φ)).toMonoidHom := by
    intro φ ψ
    rw [Subgroup.map_map, map_mul]
    rfl
  have hΩinv : ∀ g ∈ Gb, ∀ Y ∈ Ω, Y.map (MulAut.conj g).toMonoidHom ∈ Ω := by
    rintro g hg _ ⟨φ, hφ, rfl⟩
    exact ⟨g * φ, Gb.mul_mem hg hφ, hmapmap φ g⟩
  obtain ⟨n, L, hsup, hind, hcomm, hperm, hVsup, hVind, hdich⟩ :=
    h104 (IntMod V hV) hW Gb Ω hΩhyp hΩinv
  have hΩcard : ∀ Y ∈ Ω, Nat.card Y = Nat.card Xb := by
    rintro _ ⟨φ, -, rfl⟩
    exact Subgroup.card_map_of_injective (MulAut.conj φ).injective
  have hΩne : ∀ Y ∈ Ω, Y ≠ ⊥ := fun Y hY => (hΩhyp Y hY).1.2.1
  have hXodd : Odd (Nat.card Xb) := hyp.1.2.2.2.1
  have hdich' : ∀ Y ∈ Ω, ∃ j, Y ≤ L j := fun Y hY => by
    rcases hdich Y hY with ⟨j, hj⟩ | ⟨j, hj, -⟩
    · exact ⟨j, hj.le⟩
    · exact ⟨j, hj⟩
  have hLtype : ∀ i, L i ≠ ⊥ → L i ∈ Ω ∨
      (Nat.card (L i) = 21 ∧ ∃ a ∈ L i, ∃ b ∈ L i, a * b ≠ b * a) := by
    intro i hi
    obtain ⟨Y, hYΩ, hYL⟩ := Asc81c.exists_mem_le_of_ne_bot hsup hind hcomm hdich' hi
    rcases hdich Y hYΩ with ⟨j, hj⟩ | ⟨j, hj, h21, hna⟩
    · have hji : j = i := Asc81c.eq_of_le_of_le hind (hΩne Y hYΩ) hj.le hYL
      left
      rw [← hji, ← hj]
      exact hYΩ
    · have hji : j = i := Asc81c.eq_of_le_of_le hind (hΩne Y hYΩ) hj hYL
      right
      rw [← hji]
      exact ⟨h21, hna⟩
  have hLodd : ∀ i, Odd (Nat.card (L i)) := by
    intro i
    by_cases hi : L i = ⊥
    · rw [hi, Subgroup.card_bot]
      exact odd_one
    · rcases hLtype i hi with hΩ | ⟨h21, -⟩
      · rw [hΩcard _ hΩ]
        exact hXodd
      · rw [h21]
        decide
  have hYeq : sSup Ω = E6.e624Y hV M X := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ξ, hξ, rfl⟩
      exact Subgroup.subset_closure ⟨φ, hφ, ξ, hξ, rfl⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨φ, hφ, ξ, hξ, rfl⟩
      exact Subgroup.mem_sSup_of_mem (⟨φ, hφ, rfl⟩ : Xb.map (MulAut.conj φ).toMonoidHom ∈ Ω)
        (Subgroup.mem_map.2 ⟨ξ, hξ, rfl⟩)
  have hYodd : Odd (Nat.card (E6.e624Y hV M X)) := by
    rw [← hYeq, ← hsup]
    exact Asc81c.odd_card_iSup_of_commute hcomm hLodd
  let ι' := {i : Fin n // L i ≠ ⊥}
  let e := Fintype.equivFin ι'
  have hsup' : (⨆ k, L (e.symm k).1) = ⨆ i, L i := by
    rw [Equiv.iSup_comp (g := fun i : ι' => L i.1) e.symm]
    exact iSup_ne_bot_subtype L
  have htrans : ∀ i j, L i ≠ ⊥ → L j ≠ ⊥ →
      ∃ φ ∈ Gb, (L i).map (MulAut.conj φ).toMonoidHom = L j := by
    intro i j hi hj
    obtain ⟨Y₁, ⟨φ₁, hφ₁, rfl⟩, hY₁⟩ := Asc81c.exists_mem_le_of_ne_bot hsup hind hcomm hdich' hi
    obtain ⟨Y₂, ⟨φ₂, hφ₂, rfl⟩, hY₂⟩ := Asc81c.exists_mem_le_of_ne_bot hsup hind hcomm hdich' hj
    have hψ : φ₂ * φ₁⁻¹ ∈ Gb := Gb.mul_mem hφ₂ (Gb.inv_mem hφ₁)
    obtain ⟨k, hk⟩ := hperm _ hψ i
    refine ⟨φ₂ * φ₁⁻¹, hψ, ?_⟩
    have hle : Xb.map (MulAut.conj φ₂).toMonoidHom ≤ L k := by
      rw [← hk]
      have h1 := Subgroup.map_mono (f := (MulAut.conj (φ₂ * φ₁⁻¹)).toMonoidHom) hY₁
      rwa [hmapmap, inv_mul_cancel_right] at h1
    have hkj : k = j := Asc81c.eq_of_le_of_le hind (hΩne _ ⟨φ₂, hφ₂, rfl⟩) hle hY₂
    rw [hk, hkj]
  refine ⟨Fintype.card ι', fun k => L (e.symm k).1, fun k => commSub ⊤ (L (e.symm k).1),
    ⟨?_, ?_, ?_⟩, ⟨Asc81c.fixV_inf_commSub_eq_bot' hW hYodd,
      Asc81c.fixV_sup_commSub_eq_top' hW hYodd⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hsup', hsup, hYeq]
  · exact (iSupIndep_ne_bot.2 hind).comp e.symm.injective
  · intro k k' hkk'
    exact hcomm _ _ fun h0 => hkk' (e.symm.injective (Subtype.ext h0))
  ·
    rw [Equiv.iSup_comp (g := fun i : ι' => commSub ⊤ (L i.1)) e.symm, ← hYeq, ← hVsup]
    apply le_antisymm
    · exact iSup_le fun i => le_iSup_of_le i.1 le_rfl
    · refine iSup_le fun i => ?_
      by_cases hi : L i = ⊥
      · rw [hi, E6.commSub_bot']
        exact bot_le
      · exact le_iSup_of_le (⟨i, hi⟩ : ι') le_rfl
  · exact hVind.comp (Subtype.val_injective.comp e.symm.injective)
  · intro k
    exact ⟨rfl, Asc81c.commSub_commSub_eq' hW (hLodd _)⟩
  ·
    intro φ hφ k
    obtain ⟨j, hj⟩ := hperm φ hφ (e.symm k).1
    have hjne : L j ≠ ⊥ := by
      intro h0
      rw [h0] at hj
      exact (e.symm k).2 ((Subgroup.map_eq_bot_iff_of_injective _
        (MulAut.conj φ).injective).1 hj)
    refine ⟨e ⟨j, hjne⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hj
  · intro k k'
    exact htrans _ _ (e.symm k).2 (e.symm k').2
  ·
    rcases hdich Xb hXΩ with ⟨i, hi⟩ | ⟨i, hi, h21, hna⟩
    · have hine : L i ≠ ⊥ := hi ▸ hΩne Xb hXΩ
      left
      refine ⟨e ⟨i, hine⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact hi
    · right
      have hine : L i ≠ ⊥ := fun h0 => hΩne Xb hXΩ (le_bot_iff.1 (h0 ▸ hi))
      have hdvd : Nat.card Xb ∣ 21 := h21 ▸ Subgroup.card_dvd_of_le hi
      have h3 : Nat.card Xb = 3 := by
        have hne21 : Nat.card Xb ≠ 21 := by
          intro h0
          have hXL : Xb = L i := Subgroup.eq_of_le_of_card_ge hi (by rw [h0, h21])
          obtain ⟨a, ha, b, hb, hab⟩ := hna
          apply hab
          rw [← hXL] at ha hb
          have := hyp.1.2.2.1
          let _ : CommGroup Xb := IsCyclic.commGroup
          exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Xb) ⟨b, hb⟩)
        have hne1 : Nat.card Xb ≠ 1 := fun h0 =>
          hΩne Xb hXΩ (Subgroup.eq_bot_of_card_eq _ h0)
        have hne7 : Nat.card Xb ≠ 7 := by
          intro h7
          have hgen := Asc81c.le_sSup_inter hsup hind hcomm hdich' i
          have hall : sSup {Y | Y ∈ Ω ∧ Y ≤ L i} ≤ Xb := sSup_le fun Y hY =>
            (Asc81c.eq_of_card_seven h21 hY.2 hi (by rw [hΩcard Y hY.1, h7]) h7).le
          have := Subgroup.card_le_of_le (hgen.trans hall)
          rw [h21, h7] at this
          omega
        have hd : Nat.card Xb ∈ Nat.divisors 21 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
        have h21d : Nat.divisors 21 = {1, 3, 7, 21} := by decide
        rw [h21d] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with hd | hd | hd | hd
        · exact absurd hd hne1
        · exact hd
        · exact absurd hd hne7
        · exact absurd hd hne21
      have hn2 : 2 ^ r = 4 := by
        rw [hXcard] at h3
        omega
      have h8 : Nat.card (commSub ⊤ (L i)) = 8 :=
        Asc81c.card_commSub_frob21 hW h21 hna hi h3 (by rw [hcardc, hn2])
      refine ⟨h3, e ⟨i, hine⟩, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Equiv.symm_apply_apply]
        exact hi
      · simp only [Equiv.symm_apply_apply]
        exact (Asc81c.closure_conj_eq_of_frob21 h21 hna hi h3).symm
      · simp only [Equiv.symm_apply_apply]
        exact h21
      · simp only [Equiv.symm_apply_apply]
        exact hna
      · intro j
        obtain ⟨φ, -, hφ⟩ := htrans i (e.symm j).1 hine (e.symm j).2
        show Nat.card (commSub ⊤ (L (e.symm j).1)) = 8
        rw [← hφ, Asc81c.commSub_map_conj,
          Subgroup.card_map_of_injective (φ : MulAut (IntMod V hV)).injective, h8]


theorem eleven_fixV_e624Y_eq_bot {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X)
    (hfixmap : (fixV (autI hV X)).map (E3.valHom hV) = U) :
    fixV (E6.e624Y hV M X) = ⊥ := by
  classical
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  by_contra hne
  set W₀ := (fixV (E6.e624Y hV M X)).map (E3.valHom hV) with hW₀def
  have hfix : fixV (E6.e624Y hV M X) ≤ fixV (autI hV X) := fun v hv x hx =>
    hv x (E6.autI_le_e624Y hV M X hx)
  have hW₀U : W₀ ≤ U := hfixmap ▸ Subgroup.map_mono hfix
  have hW₀1 : W₀ ≠ ⊥ := fun h0 =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ (E3.valHom_injective hV)).1 h0)
  have hW₀2 : IsPGroup 2 W₀ := (B2F.isPGroup_of_isElemAbelian hV).to_le (E3.map_valHom_le hV _)
  have hYn : ∀ φ ∈ autI hV M, ∀ y ∈ E6.e624Y hV M X, φ * y * φ⁻¹ ∈ E6.e624Y hV M X := by
    intro φ hφ y hy
    refine Subgroup.closure_induction (p := fun y _ => φ * y * φ⁻¹ ∈ E6.e624Y hV M X) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨ψ, hψ, ξ, hξ, rfl⟩
      exact Subgroup.subset_closure ⟨φ * ψ, (autI hV M).mul_mem hφ hψ, ξ, hξ, by group⟩
    · simp only [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      have : φ * (a * b) * φ⁻¹ = (φ * a * φ⁻¹) * (φ * b * φ⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have : φ * a⁻¹ * φ⁻¹ = (φ * a * φ⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  have hfixinv : ∀ φ ∈ autI hV M, ∀ v ∈ fixV (E6.e624Y hV M X), φ v ∈ fixV (E6.e624Y hV M X) := by
    intro φ hφ v hv y hy
    have h1 := hv _ (hYn _ ((autI hV M).inv_mem hφ) y hy)
    have h2 : (φ⁻¹ * y * φ⁻¹⁻¹) v = v := h1
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h2
    have h3 := congrArg (fun w => φ w) h2
    simp only [MulAut.apply_inv_self] at h3
    exact h3
  have hN : M ≤ Subgroup.normalizer (W₀ : Set G) := by
    intro g hgM
    have hgN : g ∈ Subgroup.normalizer (V : Set G) := hd.setting.normal hgM
    have hle : W₀.map (MulAut.conj g).toMonoidHom ≤ W₀ := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨convI hV ⟨g, hgN⟩ v, hfixinv _ (convI_mem_autI hV hgM hgN) v hv, ?_⟩
      rw [E3.valHom_apply, convI_apply_val]
      rfl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have heq : Subgroup.normalizer (W₀ : Set G) = M :=
    hd.setting.maxLocal.2 _ ⟨W₀, hW₀1, hW₀2, rfl⟩ hN
  apply hUΓ.2.2.1
  rw [← heq]
  exact (Subgroup.centralizer_le hW₀U).trans (Subgroup.centralizer_le_normalizer _)


theorem exists_eleven11Decomp (h104 : Asc81c.Thm104)
    {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V) (hd : Eleven11Data M V Q U L X) :
    ∃ (s : ℕ) (Y : Fin s → Subgroup (MulAut (IntMod V hV)))
      (Vs : Fin s → Subgroup (IntMod V hV)) (i₀ : Fin s),
      Eleven11Decomp hV M X U s Y Vs i₀ := by
  classical
  obtain ⟨hyp, hfixmap, hXcard, hcardc⟩ := eleven_ten_hyp102 hV hd
  have hconcl := e624Concl_of_hyp102 h104 hV hyp hXcard hcardc
  obtain ⟨s, Y, Vs, hB⟩ := (E6.e624Concl_iff hV M X).1 hconcl
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  have hY0 : fixV (E6.e624Y hV M X) = ⊥ := eleven_fixV_e624Y_eq_bot hV hd hfixmap
  have hB' := hB
  obtain ⟨⟨hYsup, hYind, -⟩, ⟨-, hfix2⟩, ⟨hVsup, hVind, hVi⟩, ⟨hperm, htrans⟩, hdich⟩ := hB'
  have hVtop : commSub ⊤ (E6.e624Y hV M X) = ⊤ := by
    rw [hY0, bot_sup_eq] at hfix2
    exact hfix2
  have hXodd : Odd (Nat.card (autI hV X)) := hyp.1.2.2.2.1
  have hXne : autI hV X ≠ ⊥ := hyp.1.2.1
  have hYle : ∀ i, Y i ≤ autI hV M := fun i =>
    (le_iSup Y i).trans (hYsup ▸ E6.e624Y_le hV hXM)
  have hvsup : ⨆ i, Vs i = ⊤ := by rw [hVsup]; exact hVtop
  have hYne : ∀ i j, Y i ≠ ⊥ → Y j ≠ ⊥ := by
    intro i j hi h0
    obtain ⟨φ, -, hφ⟩ := htrans i j
    rw [h0] at hφ
    exact hi ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj φ).injective).1 hφ)
  have key : ∃ i₀ : Fin s, Y i₀ ≠ ⊥ ∧ (autI hV X = Y i₀ ∨
      (Nat.card (autI hV X) = 3 ∧ autI hV X ≤ Y i₀ ∧ Nat.card (Y i₀) = 21 ∧
        (∃ a ∈ Y i₀, ∃ b ∈ Y i₀, a * b ≠ b * a) ∧ ∀ j, Nat.card (Vs j) = 8)) := by
    rcases hdich with ⟨i, hi⟩ | ⟨h3, i, hi, -, h21, hna, h8⟩
    · exact ⟨i, hi ▸ hXne, Or.inl hi⟩
    · exact ⟨i, fun h0 => hXne (le_bot_iff.1 (h0 ▸ hi)), Or.inr ⟨h3, hi, h21, hna, h8⟩⟩
  obtain ⟨i₀, hi₀ne, hcase⟩ := key
  have hcardvs : autI hV X = Y i₀ → ∀ j, Nat.card (Vs j) = 2 ^ E3.mQuot V U := by
    intro hX j
    obtain ⟨φ, -, hφ⟩ := htrans i₀ j
    rw [← (hVi j).1, ← hφ, Asc81c.commSub_map_conj,
      Subgroup.card_map_of_injective (φ : MulAut (IntMod V hV)).injective, ← hX, hcardc]
  have hvne : ∀ i, Vs i ≠ ⊥ := by
    intro i h0
    have hcard1 : Nat.card (Vs i) = 1 := by rw [h0, Subgroup.card_bot]
    rcases hcase with hX | ⟨-, -, -, -, h8⟩
    · have h1 := hcardvs hX i
      rw [hcard1] at h1
      have hU1 : 1 < E3.mQuot V U := (eleven_ten_card_autI hV hd).2.2.2
      have h4 : 2 ^ 2 ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hU1
      omega
    · have h1 := h8 i
      omega
  exact ⟨s, Y, Vs, i₀, ⟨hB, hY0, hfixmap, hXcard, hcardc, hXodd, hYle,
    fun i => hYne i₀ i hi₀ne, hvsup, hvne, hcase, hcardvs⟩⟩


end CFSG.LocalAnalysis.WeakClosure81
