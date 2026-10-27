module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmPlus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace WitOm

section Coords

variable {K : Type} [Field K] {k : ℕ}

@[expose] def minusTwo (k : ℕ) :
    Fin (k + 2) ⊕ (Fin (k + 2) ⊕ Fin 2) ≃ (Fin 2 ⊕ Fin 2) ⊕ (Fin k ⊕ (Fin k ⊕ Fin 2)) where
  toFun := Sum.elim (fun i => (finSumFinEquiv.symm i).elim (fun j => .inr (.inl j))
      (fun t => .inl (.inl t)))
    (Sum.elim (fun i => (finSumFinEquiv.symm i).elim (fun j => .inr (.inr (.inl j)))
      (fun t => .inl (.inr t))) fun t => .inr (.inr (.inr t)))
  invFun := Sum.elim (Sum.elim (fun t => .inl (Fin.natAdd k t))
      (fun t => .inr (.inl (Fin.natAdd k t))))
    (Sum.elim (fun j => .inl (Fin.castAdd 2 j))
      (Sum.elim (fun j => .inr (.inl (Fin.castAdd 2 j))) fun t => .inr (.inr t)))
  left_inv := by
    rintro (i | i | t)
    · induction i using Fin.addCases <;> simp
    · induction i using Fin.addCases <;> simp
    · rfl
  right_inv := by
    rintro ((t | t) | j | j | t) <;> simp

theorem minusTwo_symm_aa (i : Fin 2) :
    (minusTwo k).symm (.inl (.inl i)) = .inl (Fin.natAdd k i) := rfl

theorem minusTwo_symm_bb (i : Fin 2) :
    (minusTwo k).symm (.inl (.inr i)) = .inr (.inl (Fin.natAdd k i)) := rfl

theorem minusTwo_symm_ra (j : Fin k) :
    (minusTwo k).symm (.inr (.inl j)) = .inl (Fin.castAdd 2 j) := rfl

theorem minusTwo_symm_rb (j : Fin k) :
    (minusTwo k).symm (.inr (.inr (.inl j))) = .inr (.inl (Fin.castAdd 2 j)) := rfl

theorem minusTwo_symm_rc (t : Fin 2) :
    (minusTwo k).symm (.inr (.inr (.inr t))) = .inr (.inr t) := rfl

theorem statedQuadMinus_minusTwo (b c : K) (v : Fin (k + 2) ⊕ (Fin (k + 2) ⊕ Fin 2) → K) :
    StatedQuadMinus (k + 3) K b c v =
      (∑ i, v ((minusTwo k).symm (.inl (.inl i))) * v ((minusTwo k).symm (.inl (.inr i)))) +
        StatedQuadMinus (k + 1) K b c fun x => v ((minusTwo k).symm (.inr x)) := by
  simp only [StatedQuadMinus, minusTwo_symm_aa, minusTwo_symm_bb, minusTwo_symm_ra,
    minusTwo_symm_rb, minusTwo_symm_rc]
  show (∑ i : Fin (k + 2), v (.inl i) * v (.inr (.inl i))) + v (.inr (.inr 0)) ^ 2 +
      b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 =
    (∑ i : Fin 2, v (.inl (Fin.natAdd k i)) * v (.inr (.inl (Fin.natAdd k i)))) +
      ((∑ i : Fin k, v (.inl (Fin.castAdd 2 i)) * v (.inr (.inl (Fin.castAdd 2 i)))) +
        v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2)
  rw [Fin.sum_univ_add]
  ring

end Coords

@[expose] def twoPlaneExpLast (p k : ℕ) : Fin (k + 2) → Multiplicative (ZMod p) :=
  Pi.mulSingle (Fin.natAdd k 0) (Multiplicative.ofAdd ((1 : ℕ) : ZMod p)) *
    Pi.mulSingle (Fin.natAdd k 1) (Multiplicative.ofAdd ((1 : ℕ) : ZMod p))

theorem zmodPowHom_twoPlaneExpLast {K : Type} [Field K] {p k : ℕ} {ζ : Kˣ} (hζp : ζ ^ p = 1)
    (i : Fin (k + 2)) :
    TableBSymp.zmodPowHom hζp (twoPlaneExpLast p k i) = if k ≤ (i : ℕ) then ζ else 1 := by
  have hg : TableBSymp.zmodPowHom hζp (Multiplicative.ofAdd ((1 : ℕ) : ZMod p)) = ζ := by
    rw [TableBSymp.zmodPowHom_natCast, pow_one]
  have h01 : (Fin.natAdd k (0 : Fin 2) : Fin (k + 2)) ≠ Fin.natAdd k 1 := by
    simp [Fin.ext_iff]
  rw [twoPlaneExpLast, Pi.mul_apply, map_mul]
  rcases Nat.lt_or_ge (i : ℕ) k with hi | hi
  · have hn2 : ¬ k ≤ (i : ℕ) := by omega
    simp only [hn2, ite_false]
    rw [Pi.mulSingle_eq_of_ne (fun h => by rw [h] at hi; simp at hi),
      Pi.mulSingle_eq_of_ne (fun h => by rw [h] at hi; simp at hi), map_one, mul_one]
  · simp only [hi, ite_true]
    rcases Nat.lt_or_ge (i : ℕ) (k + 1) with hi1 | hi1
    · have hi0 : i = Fin.natAdd k 0 := Fin.ext (by simp only [Fin.val_natAdd, Fin.val_zero]; omega)
      rw [hi0, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, map_one, mul_one, hg]
    · have hi1' : i = Fin.natAdd k 1 := Fin.ext (by
        simp only [Fin.val_natAdd, Fin.val_one]
        have := i.2
        omega)
      rw [hi1', Pi.mulSingle_eq_of_ne h01.symm, Pi.mulSingle_eq_same, map_one, one_mul, hg]

section Frame

open TableBOrth OrdPOm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem exists_minusSplit_frame {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (minusDatum n hirr) .POmegaMinus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpK : p ∣ Nat.card K - 1) (hp2 : p ≠ 2) :
    ∃ φ₀ : ↥(LargeEvenOmega (StatedQuadMinus n K b c)) →* G,
      Function.Injective φ₀ ∧ φ₀.range = ggG0 p B x L D J ∧
      ∀ y ∈ Bs, ∃ z, y = φ₀ z ∧ ∃ t : Fin (n - 1) → Kˣ,
        (z : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) = TauCeti.diagGL (minusUnits t) := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hBs : GGBstar p B Bs := hctx.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  set j := spinMatrix (quadMinus n K b c) with hjdef
  have hj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)
  have hjr : j.range = LargeEvenOmega (StatedQuadMinus n K b c) :=
    range_spinMatrix_quadMinus hn hirr
  have hin : ∀ c₀, GGPsiInnerDiag (minusDatum n hirr) ψ c₀ → c₀ ∈ ψ.range := by
    intro c₀ hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hBsψ : Bs ≤ ψ.range := fun y hy => hin y (hctx.2.2.2.2.2.2.1.2 y hy)
  obtain ⟨hA, hAj, -⟩ := transfer_range ψ hψ j hj hBs.2.1 hBsψ
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := p) hpK
  obtain ⟨g, hgO, χ, hχ⟩ := exists_orth_conj_minus_le hp2 hζ hirr (by omega)
    (hAj.trans (hjr.le.trans (omega_le_orth _))) hA
  set jΩ : spinGroup (quadMinus n K b c) ≃* ↥(LargeEvenOmega (StatedQuadMinus n K b c)) :=
    (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjr) with hjΩ
  have hjΩu : ∀ u, ((jΩ u : ↥(LargeEvenOmega (StatedQuadMinus n K b c))) :
      GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) = j u := fun u => rfl
  set φ₀ := ψ.comp (jΩ.symm.toMonoidHom.comp (conjOmega (inv_mem hgO)).toMonoidHom) with hφ₀def
  have hφ₀ : ∀ z, φ₀ z = ψ (jΩ.symm (conjOmega (inv_mem hgO) z)) := fun z => rfl
  refine ⟨φ₀, hψ.comp (jΩ.symm.injective.comp (conjOmega (inv_mem hgO)).injective), ?_, ?_⟩
  · rw [← hrange]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, (hφ₀ z).symm⟩
    · rintro ⟨u, rfl⟩
      refine ⟨(conjOmega (inv_mem hgO)).symm (jΩ u), ?_⟩
      rw [hφ₀, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  · intro y hy
    obtain ⟨u, rfl⟩ := hBsψ hy
    have hu : j u ∈ (Bs.comap ψ).map j := ⟨u, hy, rfl⟩
    have hgx := hχ ⟨j u, hu⟩
    have hjuΩ : j u ∈ LargeEvenOmega (StatedQuadMinus n K b c) := hjr ▸ ⟨u, rfl⟩
    have hDΩ : g * j u * g⁻¹ ∈ LargeEvenOmega (StatedQuadMinus n K b c) := by
      rw [← map_conj_omega hgO]
      exact ⟨j u, hjuΩ, rfl⟩
    refine ⟨⟨g * j u * g⁻¹, hDΩ⟩, ?_, _, hgx⟩
    rw [hφ₀]
    congr 1
    apply jΩ.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_conjOmega, hjΩu]
    change j u = g⁻¹ * (g * j u * g⁻¹) * g⁻¹⁻¹
    group

end Frame

section Main

open TableBOrth OrdPOm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem witnessAlt_POmegaMinus_split {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2 ^ f)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (minusDatum n hirr) .POmegaMinus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f - 1) (E : Subgroup G) (r : G) {s : G}
    (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaMinus f r s := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hadm := hctx.2.2.2.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hBs : GGBstar p B Bs := hctx.2.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hf hpq
  have hq4 : 4 ≤ 2 ^ f := by
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 := Nat.le_of_dvd (by omega) hpq
    have h3 := hp.two_le
    have h5 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hf2 : 2 ≤ f := by
    by_contra h
    have h1 : f = 1 := by omega
    rw [h1] at hq4
    norm_num at hq4
  obtain ⟨φ₀, hφinj, hφrange, hframe⟩ := exists_minusSplit_frame hirr hn4 hctx s1
    (by rw [hK]; exact hpq) hp2
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) (p := p)
    (by rw [hK]; exact hpq)
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hζ2 : ζ ≠ ζ⁻¹ := fun h => by
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel ζ
    have h3 := Nat.le_of_dvd (by norm_num) (hζo ▸ orderOf_dvd_of_pow_eq_one h2)
    have := hp.two_le
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hk1 : 0 < k := by omega
  set δ : Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2 → Kˣ :=
    minusUnits fun i => TableBSymp.zmodPowHom hζp (twoPlaneExpLast p k i) with hδ
  have hd₂Ω : TauCeti.diagGL δ ∈ LargeEvenOmega (StatedQuadMinus (k + 3) K b c) :=
    minusTorusGL_mem_omega (n := k + 3) hζp (hp.odd_of_ne_two hp2) (twoPlaneExpLast p k)
  set d : ↥(LargeEvenOmega (StatedQuadMinus (k + 3) K b c)) := ⟨TauCeti.diagGL δ, hd₂Ω⟩ with hd
  have hδl : ∀ i, δ (.inl i) = if k ≤ (i : ℕ) then ζ else 1 := fun i =>
    zmodPowHom_twoPlaneExpLast hζp i
  have hδm : ∀ i, δ (.inr (.inl i)) = (if k ≤ (i : ℕ) then ζ else 1)⁻¹ := fun i => by
    rw [hδ, minusUnits, Sum.elim_inr, Sum.elim_inl, zmodPowHom_twoPlaneExpLast hζp i]
  have hδn : ∀ t, δ (.inr (.inr t)) = 1 := fun t => rfl
  have hδa : ∀ i, δ ((minusTwo k).symm (.inl (.inl i))) = ζ := fun i => by
    rw [minusTwo_symm_aa, hδl, Fin.val_natAdd]
    simp
  have hδb : ∀ i, δ ((minusTwo k).symm (.inl (.inr i))) = ζ⁻¹ := fun i => by
    rw [minusTwo_symm_bb, hδm, Fin.val_natAdd]
    simp
  have hδrr : ∀ y, δ ((minusTwo k).symm (.inr y)) = 1 := fun y => by
    have hj : ∀ j : Fin k, ¬ k ≤ ((Fin.castAdd 2 j : Fin (k + 2)) : ℕ) := fun j => by
      rw [Fin.val_castAdd]
      exact Nat.not_le.mpr j.2
    rcases y with j | j | t
    · rw [minusTwo_symm_ra, hδl]
      simp only [hj j, ite_false]
    · rw [minusTwo_symm_rb, hδm]
      simp only [hj j, ite_false, inv_one]
    · rw [minusTwo_symm_rc, hδn]
  rw [← hφrange] at hs
  obtain ⟨v, rfl⟩ := hs
  have hvv : v * v = 1 := by
    have h2 := pow_orderOf_eq_one (φ₀ v)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hφinj (by rw [h2, map_one])
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hs2
    norm_num at hs2
  set QF := quadMinus (k + 3) K b c with hQF
  have hcoe : ⇑QF = StatedQuadMinus (k + 3) K b c := coe_quadMinus (k + 3) K b c
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite (k + 3) K hirr
  have h8 : 8 ≤ Fintype.card (Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hT : ∃ T : Submodule K (Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2 → K),
      Module.finrank K T = 3 ∧ ∀ y ∈ T, QF y = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim QF hnd (m := k + 3) (by omega) (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega)
  have hab : ∀ i : Fin 2, SeitzReduction.OmegaPilot.IsHypCoord QF (Sum.inl (Fin.natAdd k i))
      (Sum.inr (Sum.inl (Fin.natAdd k i))) := fun i =>
    isHypCoord_quadMinus (n := k + 3) b c (Fin.natAdd k i)
  set w : Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2 → K :=
    Pi.single (Sum.inl (Fin.castAdd 2 ⟨0, hk1⟩)) 1 +
      Pi.single (Sum.inr (Sum.inl (Fin.castAdd 2 ⟨0, hk1⟩))) 1 with hw
  have hwQ : QF w ≠ 0 := by
    rw [hw, (isHypCoord_quadMinus (n := k + 3) b c (Fin.castAdd 2 ⟨0, hk1⟩)).map_single_add]
    exact one_ne_zero
  have hne : ∀ i : Fin 2, (Fin.natAdd k i : Fin (k + 2)) ≠ Fin.castAdd 2 ⟨0, hk1⟩ := fun i h => by
    have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  have hwb : ∀ i : Fin 2, w (Sum.inr (Sum.inl (Fin.natAdd k i))) = 0 := fun i => by
    rw [hw, Pi.add_apply, Pi.single_eq_of_ne Sum.inr_ne_inl,
      Pi.single_eq_of_ne (fun h => hne i (Sum.inl_injective (Sum.inr_injective h))), add_zero]
  have hwa : ∀ i : Fin 2, w (Sum.inl (Fin.natAdd k i)) = 0 := fun i => by
    rw [hw, Pi.add_apply, Pi.single_eq_of_ne (fun h => hne i (Sum.inl_injective h)),
      Pi.single_eq_of_ne Sum.inl_ne_inr, add_zero]
  have hvO : (v : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K) ∈ LargeEvenOrthGroup ⇑QF := by
    rw [hcoe]
    exact omega_le_orth _ v.2
  have hvv' : (v : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K) * v = 1 :=
    congrArg Subtype.val hvv
  have hv1' : (v : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K) ≠ 1 := fun h =>
    hv1 (Subtype.ext h)
  obtain ⟨h, hhΩ, hE, hF⟩ := exists_omega_conj_stable (QF := QF) hnd h8 hT
    (a := fun i => Sum.inl (Fin.natAdd k i)) (b := fun i => Sum.inr (Sum.inl (Fin.natAdd k i)))
    hab (fun i j hij => Fin.natAdd_injective 2 k (Sum.inl_injective (Sum.inr_injective hij)))
    (fun i j => Sum.inl_ne_inr) hwQ hwb hwa hvO hvv' hv1'
  rw [hcoe] at hhΩ
  set M : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K := h⁻¹ * (v : GL _ _) * h with hM
  have hhO := omega_le_orth _ hhΩ
  have hMO : M ∈ LargeEvenOrthGroup ⇑QF := by
    rw [hcoe]
    exact mul_mem (mul_mem (inv_mem hhO) (omega_le_orth _ v.2)) hhO
  have hMM : M * M = 1 := by
    calc M * M = h⁻¹ * ((v : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K) *
          (v : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K)) * h := by rw [hM]; group
      _ = 1 := by rw [hvv']; group
  have hcomm := commute_diagGL_of_stable hMO hMM hab hE hF (δ := δ)
    (fun i => by rw [← minusTwo_symm_aa, ← minusTwo_symm_aa, hδa, hδa])
    (fun i => by rw [← minusTwo_symm_bb, ← minusTwo_symm_bb, hδb, hδb])
    (fun y hy => by
      obtain ⟨z, rfl⟩ := (minusTwo k).symm.surjective y
      rcases z with (i | i) | y
      · exact absurd (minusTwo_symm_aa i) (hy i).1
      · exact absurd (minusTwo_symm_bb i) (hy i).2
      · exact hδrr y)
  set hh : ↥(LargeEvenOmega (StatedQuadMinus (k + 3) K b c)) := ⟨h, hhΩ⟩ with hhh
  have hcommΩ : hh * d * hh⁻¹ * v = v * (hh * d * hh⁻¹) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhh, hd]
    have hvM : (v : GL (Fin (k + 3 - 1) ⊕ Fin (k + 3 - 1) ⊕ Fin 2) K) = h * M * h⁻¹ := by
      rw [hM]
      group
    rw [hvM]
    calc h * TauCeti.diagGL δ * h⁻¹ * (h * M * h⁻¹) = h * (TauCeti.diagGL δ * M) * h⁻¹ := by
          group
      _ = h * (M * TauCeti.diagGL δ) * h⁻¹ := by rw [hcomm]
      _ = h * M * h⁻¹ * (h * TauCeti.diagGL δ * h⁻¹) := by group
  have hMem : ∀ z, φ₀ z ∈ ggM p B x L D J := fun z =>
    Subgroup.le_normalizer (hφrange ▸ ⟨z, rfl⟩)
  have hdB : φ₀ d ∈ Bs := by
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_
    · obtain ⟨z, rfl, t, ht⟩ := hframe y hy
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ht, hd, ← map_mul, ← map_mul, mul_comm]
    · rw [← map_pow]
      have hdp : d ^ p = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        change (minusTorusGL hζp (twoPlaneExpLast p k)) ^ p = 1
        rw [← map_pow, TableBSymp.pow_card_eq_one_zmod, map_one])
      rw [hdp, map_one]
  have hd1 : φ₀ d ≠ 1 := by
    intro h1
    have h2 : d = 1 := hφinj (by rw [h1, map_one])
    have h3 : TauCeti.diagGL δ = TauCeti.diagGL 1 := by
      rw [map_one]
      exact congrArg Subtype.val h2
    have h4 := congrFun (TauCeti.diagGL_injective h3) ((minusTwo k).symm (.inl (.inl 0)))
    rw [hδa, Pi.one_apply] at h4
    exact hζ1 h4
  obtain ⟨L₁, hL₁, ⟨eL⟩⟩ := exists_component_levi (minusTwo k)
    (Q' := StatedQuadMinus (k + 1) K b c) (statedQuadMinus_minusTwo b c)
    (by rw [hK]; exact hq4) hζ1 hζ2 hδa hδb hδrr hφinj (d := d) rfl
  have hnex : ¬ GGSixSeventeenExcluded p .POmegaMinus f L₁ :=
    not_ggSixSeventeenExcluded_SL2 hK hf2 (by decide) (by decide) (fun h5 hf' => by
      rw [h5, hf'] at hpq
      norm_num at hpq) eL
  refine Or.inr (Or.inl ⟨φ₀ (hh * d * hh⁻¹), ?_, φ₀ hh⁻¹, hMem _, ?_⟩)
  · rw [← map_mul, ← map_mul, hcommΩ]
  · have hconj : φ₀ hh⁻¹ * φ₀ (hh * d * hh⁻¹) * (φ₀ hh⁻¹)⁻¹ = φ₀ d := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [hconj]
    exact ⟨hd1, Or.inr (Or.inr ⟨hdB, L₁, hφrange ▸ hL₁, Or.inr hnex⟩)⟩

end Main

end WitOm

section Inputs

theorem ggSixRootFusionWitnessOn_POmegaMinusSplit :
    GGSixRootFusionWitnessOn fun t _ f p => t = .POmegaMinus ∧ p ∣ 2 ^ f - 1 := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 _ E r _ _ _ s hs hs2
  obtain ⟨rfl, hpq⟩ := hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact WitOm.witnessAlt_POmegaMinus_split (K := GaloisField 2 f) (minusCoeffs_irr 2 f)
    (GaloisField.card 2 f (by have := hctx.2.2.2.1.1.2.1; omega)) hctx s1 hpq E r hs hs2

end Inputs

end CFSG.StandardType
