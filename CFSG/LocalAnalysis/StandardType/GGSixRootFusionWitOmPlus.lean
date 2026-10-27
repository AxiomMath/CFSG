module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmExcl
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open scoped Matrix

namespace WitOm

section Coords

variable {K : Type} [Field K] {k : ℕ}

@[expose] def plusTwo (k : ℕ) : Fin (2 + k) ⊕ Fin (2 + k) ≃ (Fin 2 ⊕ Fin 2) ⊕ (Fin k ⊕ Fin k) :=
  (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans
    (Equiv.sumSumSumComm (Fin 2) (Fin k) (Fin 2) (Fin k))

theorem plusTwo_symm_aa (i : Fin 2) :
    (plusTwo k).symm (.inl (.inl i)) = .inl (Fin.castAdd k i) := by
  simp [plusTwo]

theorem plusTwo_symm_bb (i : Fin 2) :
    (plusTwo k).symm (.inl (.inr i)) = .inr (Fin.castAdd k i) := by
  simp [plusTwo]

theorem plusTwo_symm_ra (j : Fin k) :
    (plusTwo k).symm (.inr (.inl j)) = .inl (Fin.natAdd 2 j) := by
  simp [plusTwo]

theorem plusTwo_symm_rb (j : Fin k) :
    (plusTwo k).symm (.inr (.inr j)) = .inr (Fin.natAdd 2 j) := by
  simp [plusTwo]

theorem largeEvenQPlus_plusTwo (v : Fin (2 + k) ⊕ Fin (2 + k) → K) :
    LargeEvenQPlus K (2 + k) v =
      (∑ i, v ((plusTwo k).symm (.inl (.inl i))) * v ((plusTwo k).symm (.inl (.inr i)))) +
        LargeEvenQPlus K k fun x => v ((plusTwo k).symm (.inr x)) := by
  simp only [largeEvenQPlus_def, plusTwo_symm_aa, plusTwo_symm_bb, plusTwo_symm_ra, plusTwo_symm_rb]
  rw [Fin.sum_univ_add]

end Coords

section Frame

open TableBOrth OrdPOm

theorem ne_two_of_dvd_two_pow_sub_one {p f : ℕ} (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1) : p ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h2 := Nat.dvd_sub h1 hpq
  rw [Nat.sub_sub_self (Nat.one_le_two_pow)] at h2
  exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)

theorem exists_plusSplit_frame {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n (GaloisField 2 f)) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (plusDatum n (GaloisField 2 f) hn) .POmegaPlus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f - 1) :
    ∃ φ₀ : ↥(LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n)) →* G,
      Function.Injective φ₀ ∧ φ₀.range = ggG0 p B x L D J ∧
      ∀ y ∈ Bs, ∃ z, y = φ₀ z ∧ ∃ t : Fin n → (GaloisField 2 f)ˣ,
        (z : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          TauCeti.diagGL (TableBSymp.pairedUnits t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hadm := hctx.2.2.2.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hBs : GGBstar p B Bs := hctx.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hf hpq
  have : Fact p.Prime := ⟨hp⟩
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  set j := spinMatrix (quadPlus n (GaloisField 2 f)) with hjdef
  have hj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero)
  have hjr : j.range = LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n) :=
    range_spinMatrix_quadPlus hn
  have hin : ∀ c, GGPsiInnerDiag (plusDatum n (GaloisField 2 f) hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨hA, hAj, -⟩ := transfer_range ψ hψ j hj hBs.2.1 hBsψ
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) (p := p)
    (by rw [GaloisField.card 2 f (by omega)]; exact hpq)
  obtain ⟨g, hgO, χ, hχ⟩ := exists_orth_conj_plus_le hp2 hζ
    (hAj.trans (hjr.le.trans (omega_le_orth _))) hA
  set jΩ : spinGroup (quadPlus n (GaloisField 2 f)) ≃*
      ↥(LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n)) :=
    (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjr) with hjΩ
  have hjΩu : ∀ u, ((jΩ u : ↥(LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n))) :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) = j u := fun u => rfl
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
    have hjuΩ : j u ∈ LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n) := hjr ▸ ⟨u, rfl⟩
    have hDΩ : g * j u * g⁻¹ ∈ LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n) := by
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

@[expose] def twoPlaneExp (p k : ℕ) : Fin (2 + k) → Multiplicative (ZMod p) :=
  Pi.mulSingle (Fin.castAdd k 0) (Multiplicative.ofAdd ((1 : ℕ) : ZMod p)) *
    Pi.mulSingle (Fin.castAdd k 1) (Multiplicative.ofAdd ((1 : ℕ) : ZMod p))

theorem zmodPowHom_twoPlaneExp {K : Type} [Field K] {p k : ℕ} {ζ : Kˣ} (hζp : ζ ^ p = 1)
    (i : Fin (2 + k)) :
    TableBSymp.zmodPowHom hζp (twoPlaneExp p k i) = if (i : ℕ) < 2 then ζ else 1 := by
  have hg : TableBSymp.zmodPowHom hζp (Multiplicative.ofAdd ((1 : ℕ) : ZMod p)) = ζ := by
    rw [TableBSymp.zmodPowHom_natCast, pow_one]
  have h01 : (Fin.castAdd k (0 : Fin 2) : Fin (2 + k)) ≠ Fin.castAdd k 1 := by
    simp [Fin.ext_iff]
  rw [twoPlaneExp, Pi.mul_apply, map_mul]
  rcases Nat.lt_or_ge (i : ℕ) 2 with hi | hi
  · rw [ite_eq_left hi]
    rcases Nat.lt_or_ge (i : ℕ) 1 with hi1 | hi1
    · have hi0 : i = Fin.castAdd k 0 := Fin.ext (by
        simp only [Fin.val_castAdd, Fin.val_zero]
        omega)
      rw [hi0, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, map_one, mul_one, hg]
    · have hi1' : i = Fin.castAdd k 1 := Fin.ext (by
        simp only [Fin.val_castAdd, Fin.val_one]
        omega)
      rw [hi1', Pi.mulSingle_eq_of_ne h01.symm, Pi.mulSingle_eq_same, map_one, one_mul, hg]
  · have hn2 : ¬ (i : ℕ) < 2 := by omega
    simp only [hn2, ite_false]
    rw [Pi.mulSingle_eq_of_ne (fun h => by rw [h] at hi; simp at hi),
      Pi.mulSingle_eq_of_ne (fun h => by rw [h] at hi; simp at hi), map_one, mul_one]

theorem witnessAlt_POmegaPlus_split {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n (GaloisField 2 f)) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (plusDatum n (GaloisField 2 f) hn) .POmegaPlus n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f - 1) (E : Subgroup G) (r : G) {s : G}
    (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaPlus f r s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hadm := hctx.2.2.2.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hBs : GGBstar p B Bs := hctx.2.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hf hpq
  have hcardK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
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
  obtain ⟨φ₀, hφinj, hφrange, hframe⟩ := exists_plusSplit_frame hn hctx s1 hpq
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) (p := p)
    (by rw [hcardK]; exact hpq)
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
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  set δ := TableBSymp.pairedUnits fun i => TableBSymp.zmodPowHom hζp (twoPlaneExp p k i) with hδ
  have hd₂Ω : TauCeti.diagGL δ ∈ LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) (2 + k)) :=
    TableBSymp.spTorusGL_mem_omegaPlus hζp (hp.odd_of_ne_two hp2) (twoPlaneExp p k)
  set d : ↥(LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) (2 + k))) :=
    ⟨TauCeti.diagGL δ, hd₂Ω⟩ with hd
  have hδl : ∀ i, δ (.inl i) = if (i : ℕ) < 2 then ζ else 1 := fun i =>
    zmodPowHom_twoPlaneExp hζp i
  have hδr' : ∀ i, δ (.inr i) = (if (i : ℕ) < 2 then ζ else 1)⁻¹ := fun i => by
    rw [hδ, TableBSymp.pairedUnits, Sum.elim_inr, zmodPowHom_twoPlaneExp hζp i]
  have hδa : ∀ i, δ ((plusTwo k).symm (.inl (.inl i))) = ζ := fun i => by
    rw [plusTwo_symm_aa, hδl, Fin.val_castAdd, ite_eq_left i.2]
  have hδb : ∀ i, δ ((plusTwo k).symm (.inl (.inr i))) = ζ⁻¹ := fun i => by
    rw [plusTwo_symm_bb, hδr', Fin.val_castAdd, ite_eq_left i.2]
  have hδrr : ∀ x, δ ((plusTwo k).symm (.inr x)) = 1 := fun x => by
    have hj : ∀ j : Fin k, ¬ ((Fin.natAdd 2 j : Fin (2 + k)) : ℕ) < 2 := fun j => by
      rw [Fin.val_natAdd]
      omega
    rcases x with j | j
    · rw [plusTwo_symm_ra, hδl]
      simp only [hj j, ite_false]
    · rw [plusTwo_symm_rb, hδr']
      simp only [hj j, ite_false, inv_one]
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
  set QF := qPlusForm (GaloisField 2 f) (2 + k) with hQF
  have hcoe : ⇑QF = LargeEvenQPlus (GaloisField 2 f) (2 + k) := coe_qPlusForm (2 + k)
  have hnd := nondegenerate_qPlusForm (K := GaloisField 2 f) (2 + k)
  have h8 : 8 ≤ Fintype.card (Fin (2 + k) ⊕ Fin (2 + k)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hT : ∃ T : Submodule (GaloisField 2 f) (Fin (2 + k) ⊕ Fin (2 + k) → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ y ∈ T, QF y = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim QF hnd (m := 2 + k) (by omega) (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega)
  have hk1 : 0 < k := by omega
  set w : Fin (2 + k) ⊕ Fin (2 + k) → GaloisField 2 f :=
    Pi.single (Sum.inl (Fin.natAdd 2 ⟨0, hk1⟩)) 1 + Pi.single (Sum.inr (Fin.natAdd 2 ⟨0, hk1⟩)) 1
    with hw
  have hwQ : QF w ≠ 0 := by
    rw [hcoe, hw, largeEvenQPlus_single_add_single]
    exact one_ne_zero
  have hne : ∀ i : Fin 2, (Fin.castAdd k i : Fin (2 + k)) ≠ Fin.natAdd 2 ⟨0, hk1⟩ := fun i h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have hwb : ∀ i : Fin 2, w (Sum.inr (Fin.castAdd k i)) = 0 := fun i => by
    rw [hw, Pi.add_apply, Pi.single_eq_of_ne Sum.inr_ne_inl,
      Pi.single_eq_of_ne (fun h => hne i (Sum.inr_injective h)), add_zero]
  have hwa : ∀ i : Fin 2, w (Sum.inl (Fin.castAdd k i)) = 0 := fun i => by
    rw [hw, Pi.add_apply, Pi.single_eq_of_ne (fun h => hne i (Sum.inl_injective h)),
      Pi.single_eq_of_ne Sum.inl_ne_inr, add_zero]
  have hvO : (v : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f)) ∈ LargeEvenOrthGroup ⇑QF := by
    rw [hcoe]
    exact omega_le_orth _ v.2
  have hvv' : (v : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f)) * v = 1 :=
    congrArg Subtype.val hvv
  have hv1' : (v : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f)) ≠ 1 := fun h =>
    hv1 (Subtype.ext h)
  have hab : ∀ i : Fin 2, SeitzReduction.OmegaPilot.IsHypCoord QF (Sum.inl (Fin.castAdd k i))
      (Sum.inr (Fin.castAdd k i)) := fun i => isHypCoord_qPlusForm (Fin.castAdd k i)
  obtain ⟨h, hhΩ, hE, hF⟩ := exists_omega_conj_stable (QF := QF) hnd h8 hT
    (a := fun i => Sum.inl (Fin.castAdd k i)) (b := fun i => Sum.inr (Fin.castAdd k i)) hab
    (Sum.inr_injective.comp (Fin.castAdd_injective 2 k)) (fun i j => Sum.inl_ne_inr) hwQ hwb hwa
    hvO hvv' hv1'
  rw [hcoe] at hhΩ
  set M : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f) := h⁻¹ * (v : GL _ _) * h with hM
  have hhO := omega_le_orth _ hhΩ
  have hMO : M ∈ LargeEvenOrthGroup ⇑QF := by
    rw [hcoe]
    exact mul_mem (mul_mem (inv_mem hhO) (omega_le_orth _ v.2)) hhO
  have hMM : M * M = 1 := by
    calc M * M = h⁻¹ * ((v : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f)) *
          (v : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f))) * h := by rw [hM]; group
      _ = 1 := by rw [hvv']; group
  have hcomm := commute_diagGL_of_stable hMO hMM hab hE hF (δ := δ)
    (fun i => by rw [← plusTwo_symm_aa, ← plusTwo_symm_aa, hδa, hδa])
    (fun i => by rw [← plusTwo_symm_bb, ← plusTwo_symm_bb, hδb, hδb])
    (fun y hy => by
      obtain ⟨z, rfl⟩ := (plusTwo k).symm.surjective y
      rcases z with (i | i) | y
      · exact absurd (plusTwo_symm_aa i) (hy i).1
      · exact absurd (plusTwo_symm_bb i) (hy i).2
      · exact hδrr y)
  set hh : ↥(LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) (2 + k))) := ⟨h, hhΩ⟩ with hhh
  have hcommΩ : hh * d * hh⁻¹ * v = v * (hh * d * hh⁻¹) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hhh, hd]
    have hvM : (v : GL (Fin (2 + k) ⊕ Fin (2 + k)) (GaloisField 2 f)) = h * M * h⁻¹ := by
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
        change (TableBSymp.spTorusGL hζp (twoPlaneExp p k)) ^ p = 1
        rw [← map_pow, TableBSymp.pow_card_eq_one_zmod, map_one])
      rw [hdp, map_one]
  have hd1 : φ₀ d ≠ 1 := by
    intro h1
    have h2 : d = 1 := hφinj (by rw [h1, map_one])
    have h3 : TauCeti.diagGL δ = TauCeti.diagGL 1 := by
      rw [map_one]
      exact congrArg Subtype.val h2
    have h4 := congrFun (TauCeti.diagGL_injective h3) ((plusTwo k).symm (.inl (.inl 0)))
    rw [hδa, Pi.one_apply] at h4
    exact hζ1 h4
  obtain ⟨L₁, hL₁, ⟨eL⟩⟩ := exists_component_levi (plusTwo k)
    (Q' := LargeEvenQPlus (GaloisField 2 f) k) largeEvenQPlus_plusTwo (by rw [hcardK]; exact hq4)
    hζ1 hζ2 hδa hδb hδrr hφinj (d := d) rfl
  have hnex : ¬ GGSixSeventeenExcluded p .POmegaPlus f L₁ :=
    not_ggSixSeventeenExcluded_SL2 hcardK hf2 (by decide) (by decide) (fun h5 hf' => by
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

theorem ggSixRootFusionWitnessOn_POmegaPlusSplit :
    GGSixRootFusionWitnessOn fun t _ f p => t = .POmegaPlus ∧ p ∣ 2 ^ f - 1 := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hpq⟩ := hP
  by_cases hn : 3 ≤ n
  · revert ψ
    rw [ggU_POmegaPlus_eq hn]
    intro ψ hctx s1 _ E r _ _ _ s hs hs2
    exact WitOm.witnessAlt_POmegaPlus_split hn hctx s1 hpq E r hs hs2
  · intro hctx
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

end Inputs

end CFSG.StandardType
