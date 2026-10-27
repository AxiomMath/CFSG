module

public import CFSG.RankThree.PartTwo.Sec19.Step1911EndKFact
public import CFSG.RankThree.PartTwo.Sec19.Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1917EqProof

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec19.Step1911EndProof (glConj glConj_inv_mem mulVec_mem_flagSpace
  finrank_map_flagSpace)

variable {F : Type} [Field F]

theorem exists_uniform_invariant_of_normalizes_parabolic [Finite F] [CharP F 2]
    {P : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : P ≠ ⊤)
    {T : Sylow 2 (SpecialLinearGroup (Fin 3) F)}
    (hNT : Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin 3) F)) ≤ P) :
    ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin 3) F,
      (∀ s ∈ P, glConj g s ∈ P) → ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) F) SU T
  have hT : (T : Subgroup (SpecialLinearGroup (Fin 3) F)) =
      (unitriangular 3 F).map (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
        SpecialLinearGroup (Fin 3) F) := by
    rw [← hx, coe_sylow_smul, hSU]
  have hN : Subgroup.normalizer (T : Set (SpecialLinearGroup (Fin 3) F)) =
      (upperTriangular 3 F).map (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
        SpecialLinearGroup (Fin 3) F) := by
    change Subgroup.normalizer (((T : Subgroup (SpecialLinearGroup (Fin 3) F))) :
      Set (SpecialLinearGroup (Fin 3) F)) = _
    rw [hT, normalizer_map_conj, normalizer_unitriangular]
  set P₀ := P.comap (MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
    SpecialLinearGroup (Fin 3) F) with hP₀
  have hB : upperTriangular 3 F ≤ P₀ := fun b hb =>
    Subgroup.mem_comap.mpr (hNT (hN ▸ Subgroup.mem_map_of_mem _ hb))
  have hP₀top : P₀ ≠ ⊤ := by
    intro htop
    apply hP
    rw [eq_top_iff]
    intro s _
    have hs : x⁻¹ * s * x ∈ P₀ := by rw [htop]; exact Subgroup.mem_top _
    have := Subgroup.mem_comap.mp hs
    simpa [mul_assoc] using this
  set I := borelOvergroupCuts P₀ with hIdef
  have hQ : P₀ = flagStabilizer 3 F I := (borel_overgroups P₀ hB).1
  have hI3 : ∀ j ∈ I, j < 3 := fun j hj => by
    obtain ⟨_, hjn, _⟩ := hj
    exact hjn
  obtain ⟨i, hi⟩ : I.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hI
    apply hP₀top
    rw [hQ, hI, flagStabilizer_empty]
  obtain ⟨hi1, hi3, -⟩ := id hi
  set X := SpecialLinearGroup.toGL x with hX
  have hconj : ∀ g : GL (Fin 3) F, (∀ s ∈ P, glConj g s ∈ P) →
      ∀ s ∈ P₀, glConj (X⁻¹ * g * X) s ∈ P₀ := by
    intro g hg s hs
    rw [Subgroup.mem_comap] at hs ⊢
    have h1 : (MulAut.conj x : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F)
        (glConj (X⁻¹ * g * X) s) = glConj g ((MulAut.conj x : SpecialLinearGroup (Fin 3) F →*
          SpecialLinearGroup (Fin 3) F) s) := by
      apply SpecialLinearGroup.toGL_injective
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul, map_inv,
        Step1911EndProof.toGL_glConj, hX]
      group
    rw [h1]
    exact hg _ hs
  have hW : ∀ g : GL (Fin 3) F, (∀ s ∈ P, glConj g s ∈ P) → ∀ v ∈ flagSpace 3 F i,
      ((X⁻¹ * g * X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ flagSpace 3 F i := by
    intro g hg
    refine mulVec_mem_flagSpace hI3 hi hi1 ?_
    rw [← hQ]
    exact glConj_inv_mem (hconj g hg)
  have hdim : Module.finrank F ((flagSpace 3 F i).map
      (mulVecLin (X : Matrix (Fin 3) (Fin 3) F))) = i := finrank_map_flagSpace X hi3.le
  refine ⟨(flagSpace 3 F i).map (mulVecLin (X : Matrix (Fin 3) (Fin 3) F)), ?_, ?_, ?_⟩
  · intro h
    rw [h, finrank_bot] at hdim
    omega
  · intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hdim
    omega
  · rintro g hg _ ⟨w, hw, rfl⟩
    refine ⟨_, hW g hg w hw, ?_⟩
    simp only [mulVecLin_apply, mulVec_mulVec]
    congr 1
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group

theorem exists_uniform_invariant_of_surjective [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (ρ : SpecialLinearGroup (Fin 3) F →* Y) (hρ : Function.Surjective ρ) {P : Subgroup Y}
    (hpar : IsProperParabolic P) :
    ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin 3) F,
      (∀ s, ρ s ∈ P → ρ (glConj g s) ∈ P) → ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPtop, T, hT⟩ := hpar
  have hP' : P.comap ρ ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    obtain ⟨s, rfl⟩ := hρ y
    have : s ∈ P.comap ρ := h ▸ Subgroup.mem_top s
    exact this
  obtain ⟨T', hT'⟩ := Sylow.mapSurjective_surjective hρ 2 T
  have hN : Subgroup.normalizer (T' : Set (SpecialLinearGroup (Fin 3) F)) ≤ P.comap ρ := by
    intro z hz
    apply hT
    have h1 : ρ z ∈ (Subgroup.normalizer ((T' : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F))).map ρ := Subgroup.mem_map_of_mem ρ hz
    have h2 := Subgroup.le_normalizer_map ρ h1
    rw [← Sylow.coe_mapSurjective hρ, hT'] at h2
    exact h2
  obtain ⟨W, hW0, hWtop, hW⟩ := exists_uniform_invariant_of_normalizes_parabolic hP' hN
  exact ⟨W, hW0, hWtop, fun g hg => hW g (fun s hs => hg s hs)⟩

theorem exists_invariant_of_surjective [Finite F] [CharP F 2] {Y : Type} [Group Y]
    (ρ : SpecialLinearGroup (Fin 3) F →* Y) (hρ : Function.Surjective ρ) {P : Subgroup Y}
    (hpar : IsProperParabolic P) {g : GL (Fin 3) F}
    (hg : ∀ s, ρ s ∈ P → ρ (glConj g s) ∈ P) :
    ∃ W : Submodule F (Fin 3 → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W := by
  obtain ⟨W, hW0, hWtop, hW⟩ := exists_uniform_invariant_of_surjective ρ hρ hpar
  exact ⟨W, hW0, hWtop, hW g hg⟩

@[expose] noncomputable def rhoPSL (q : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin 3) F →* projImage (Sec4.slPi true 3 q F) :=
  (SpecialLinearGroup.toPGL.codRestrict (projImage (Sec4.slPi true 3 q F)) fun s =>
    ⟨_, ((Sec4.slPiTrueEquiv q F).symm s).2, by
      rw [show (((Sec4.slPiTrueEquiv q F).symm s : Sec4.slPi true 3 q F) : GL (Fin 3) F) =
        SpecialLinearGroup.toGL s from Sec4.coe_statedSLEquiv_symm_eq_toGL s]
      rfl⟩)

theorem coe_rhoPSL (q : ℕ) (s : SpecialLinearGroup (Fin 3) F) :
    ((rhoPSL q F s : projImage (Sec4.slPi true 3 q F)) : ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL s) :=
  rfl

theorem rhoPSL_surjective (q : ℕ) : Function.Surjective (rhoPSL q F) := by
  rintro ⟨w, g, hg, rfl⟩
  refine ⟨Sec4.slPiTrueEquiv q F ⟨g, hg⟩, Subtype.ext ?_⟩
  rw [coe_rhoPSL, Sec4.toGL_slPiTrueEquiv]

theorem false_of_type3 [Finite F] [CharP F 2] {q : ℕ}
    {Q' : Subgroup (projImage (Sec4.slPi true 3 q F))} (hpar : IsProperParabolic Q')
    {y : GL (Fin 3) F} (hy : Sec4.Type123 true q F y 3)
    (hn : ∀ w ∈ Q', ∃ w' ∈ Q', (w' : ProjGenLinGroup (Fin 3) F) =
      ProjGenLinGroup.mk y * (w : ProjGenLinGroup (Fin 3) F) * (ProjGenLinGroup.mk y)⁻¹) :
    False := by
  obtain ⟨W, hW0, hWtop, hWinv⟩ := exists_invariant_of_surjective (rhoPSL q F)
    (rhoPSL_surjective q) hpar (g := y) (fun s hs => by
      obtain ⟨w', hw', he⟩ := hn _ hs
      have : w' = rhoPSL q F (glConj y s) := by
        apply Subtype.ext
        rw [he, coe_rhoPSL, coe_rhoPSL, Step1911EndProof.toGL_glConj, map_mul, map_mul, map_inv]
      exact this ▸ hw')
  rcases hy.2.2 W hWinv with h | h
  · exact hW0 h
  · exact hWtop h

variable {G : Type} [Group G] [Finite G]

theorem inv_of_orderFour {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {g : G} (hgB : ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    (h4 : ∀ b ∈ B, g ^ 4 * b * (g ^ 4)⁻¹ = b) (h2 : ∃ b ∈ B, g ^ 2 * b * (g ^ 2)⁻¹ ≠ b) :
    ∀ b ∈ B, g ^ 2 * b * (g ^ 2)⁻¹ = b⁻¹ := by
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  set h : G → G := fun b => g ^ 2 * b * (g ^ 2)⁻¹ with hhdef
  have hhB : ∀ b ∈ B, h b ∈ B := fun b hb => by
    have := hgB _ (hgB b hb)
    simpa [hhdef, pow_two, mul_assoc] using this
  have hhh : ∀ b ∈ B, h (h b) = b := fun b hb => by
    have e : h (h b) = g ^ 4 * b * (g ^ 4)⁻¹ := by simp only [hhdef]; group
    rw [e]
    exact h4 b hb
  have hmul : ∀ a b : G, h (a * b) = h a * h b := fun a b => by simp only [hhdef]; group
  have hinv : ∀ a : G, h a⁻¹ = (h a)⁻¹ := fun a => by simp only [hhdef]; group
  have hτh : ∀ b : G, h (g * b * g⁻¹) = g * h b * g⁻¹ := fun b => by simp only [hhdef]; group
  have hord : ∀ b ∈ B, b ≠ 1 → orderOf b = 3 := fun b hb hb1 =>
    orderOf_eq_prime (h3 b hb) hb1
  by_contra hcon
  push Not at hcon
  obtain ⟨b₀, hb₀, hb₀h⟩ := hcon
  obtain ⟨w₀, hw₀, hw₀h⟩ := h2
  set u := b₀ * h b₀ with hu
  have huB : u ∈ B := B.mul_mem hb₀ (hhB b₀ hb₀)
  have hu1 : u ≠ 1 := fun h1 => hb₀h (eq_inv_of_mul_eq_one_right h1)
  have huh : h u = u := by
    rw [hu, hmul, hhh b₀ hb₀]
    exact hcomm _ (hhB b₀ hb₀) _ hb₀
  set w := w₀ * (h w₀)⁻¹ with hw
  have hwB : w ∈ B := B.mul_mem hw₀ (B.inv_mem (hhB w₀ hw₀))
  have hw1 : w ≠ 1 := fun h1 => hw₀h (mul_inv_eq_one.mp h1).symm
  have hwh : h w = w⁻¹ := by
    rw [hw, hmul, hinv, hhh w₀ hw₀, _root_.mul_inv_rev, inv_inv]
  let Binv : Subgroup G :=
    { carrier := {b | b ∈ B ∧ h b = b⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, by
        rw [hmul, ha.2, hb.2, _root_.mul_inv_rev]
        exact hcomm _ (B.inv_mem ha.1) _ (B.inv_mem hb.1)⟩
      one_mem' := ⟨B.one_mem, by simp [hhdef]⟩
      inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, by rw [hinv, ha.2]⟩ }
  have hBinvB : Binv ≤ B := fun b hb => hb.1
  have hwBinv : w ∈ Binv := ⟨hwB, hwh⟩
  set v := g * w * g⁻¹ with hv
  have hvB : v ∈ B := hgB w hwB
  have hvh : h v = v⁻¹ := by
    rw [hv, hτh, hwh]
    group
  have hvBinv : v ∈ Binv := ⟨hvB, hvh⟩
  have hv1 : v ≠ 1 := by
    intro h1
    apply hw1
    have : w = g⁻¹ * v * g := by rw [hv]; group
    rw [this, h1]
    group
  by_cases hvw : v ∈ Subgroup.zpowers w
  ·
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvw
    have hk' : g * w * g⁻¹ = w ^ k := hk.symm
    have hhw : h w = w ^ (k * k) := by
      have e1 : h w = g * (g * w * g⁻¹) * g⁻¹ := by simp only [hhdef, pow_two]; group
      rw [e1, hk', ← conj_zpow, hk', ← _root_.zpow_mul]
    have hw3 : orderOf w = 3 := hord w hwB hw1
    have hk3 : ¬ (3 : ℤ) ∣ k := by
      rintro ⟨m, rfl⟩
      apply hv1
      rw [hv, hk', _root_.zpow_mul, show w ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; exact h3 w hwB,
        _root_.one_zpow]
    have hkk : w ^ (k * k) = w := by
      have hmod : (k * k) % 3 = 1 := by
        have : k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases this with h' | h' <;> simp [Int.mul_emod, h']
      rw [← zpow_mod_orderOf, hw3]
      push_cast
      rw [hmod, zpow_one]
    rw [hhw, hkk] at hwh
    have hw2 : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← hwh]
        _ = 1 := _root_.mul_inv_cancel w
    have : w ^ 3 = 1 := h3 w hwB
    apply hw1
    calc w = w ^ 3 * (w * w)⁻¹ := by group
      _ = 1 := by rw [this, hw2]; group
  ·
    have hlt : Subgroup.zpowers w < Binv :=
      lt_of_le_of_ne (Subgroup.zpowers_le.mpr hwBinv) (fun heq => hvw (heq ▸ hvBinv))
    have hw3 : orderOf w = 3 := hord w hwB hw1
    have hc3 : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hw3]
    have hdvd : Nat.card Binv ∣ 9 := hB9 ▸ Subgroup.card_dvd_of_le hBinvB
    have hlt' : 3 < Nat.card Binv := hc3 ▸ Subgroup.card_lt_of_lt hlt
    have h9 : Nat.card Binv = 9 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card Binv <;> first | rfl | exact absurd hdvd (by decide)
    have heq : Binv = B := Subgroup.eq_of_le_of_card_ge hBinvB (by rw [h9, hB9])
    have huBinv : u ∈ Binv := heq ▸ huB
    have huu : u = u⁻¹ := huh.symm.trans huBinv.2
    have hu2 : u * u = 1 := by
      calc u * u = u * u⁻¹ := by rw [← huu]
        _ = 1 := _root_.mul_inv_cancel u
    apply hu1
    calc u = u ^ 3 * (u * u)⁻¹ := by group
      _ = 1 := by rw [h3 u huB, hu2]; group

end CFSG.RankThree.PartTwo.Sec19.Step1917EqProof
