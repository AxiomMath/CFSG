module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim79a34TwWSplit
public import CFSG.RankThree.GF2n.Tim79a34TwBound
public import CFSG.RankThree.GF2n.Tim79a34SpRad

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section Radical

variable {n : ℕ} {F : Type} [Field F]

theorem spRad_mul_self_eq_one [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {g : StatedSp n F} (hg : g ∈ spRad a) : g * g = 1 := by
  obtain ⟨w, l, haw, hx⟩ := exists_param_of_mem_spRad ha hg
  refine eq_of_mat_mulVec_eq fun v => ?_
  rw [map_one, Matrix.one_mulVec, mat_mul_mulVec_of_param haw haw hx hx v, vec_add_self,
    spForm_zero_left, CaseM.spForm_self, CharTwo.add_self_eq_zero]
  simp

theorem exists_ne_zero_mat_eq_spTrans {a : Fin n ⊕ Fin n → F} {T : Subgroup (StatedSp n F)}
    (hT : CaseM.IsTransGroup a T) {t : StatedSp n F} (ht : t ∈ T) (ht1 : t ≠ 1) :
    ∃ c : F, c ≠ 0 ∧ SpExtras.mat n F t = CaseM.spTrans a c := by
  obtain ⟨c, hc⟩ := (hT.1 t).1 ht
  refine ⟨c, ?_, hc⟩
  rintro rfl
  apply ht1
  apply SpExtras.mat_injective
  rw [hc, ModelRank.spTrans_zero, map_one]

end Radical

theorem spRadGeneralStatement_holds : SpRadGeneralStatement := by
  intro n _ F _ _ _ a ha
  exact ⟨fun g hg h hh => spRadCommStmt_holds ha g hg h hh,
    fun g hg => spRad_mul_self_eq_one ha hg,
    by rw [spRad_card_eq_ker ha, natCard_ker_spFormL ha]⟩

theorem bigPLocalStatement_of_spRad (hR : SpRadGeneralStatement) : BigPLocalStatement := by
  intro G _ _ M V Q P H hH hZ hcP n f hf Φ ψ hNat a T ha hT hTV
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      apply ha
      funext i
      rcases i with i | i <;> exact i.elim0
    · omega
  have hq4 : 4 ≤ qBar V H := hH.q_big
  have hqpos : 0 < qBar V H := by omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [← hf] at hq4
    norm_num at hq4
  have hFcard : Nat.card (GaloisField 2 f) = qBar V H := by
    rw [GaloisField.card 2 f hf0, hf]
  have hWcard : Nat.card ↥(wOf V H) = qBar V H ^ (2 * n) := by
    have h1 : Nat.card (Fin n ⊕ Fin n → GaloisField 2 f) = Nat.card ↥(wOf V H) :=
      Nat.card_congr (ψ.toEquiv.trans Additive.toMul)
    rw [← h1, Nat.card_fun, Nat.card_sum, hFcard]
    simp [two_mul, Nat.card_eq_fintype_card]
  have hPW : Nat.card ↥(P ⊓ wOf V H) = qBar V H ^ (2 * n - 1) := by
    have h := twistedWSplit_holds G M V Q P H hH.setup hH.concl
    rw [hWcard, hH.module] at h
    have h2 : qBar V H ^ (2 * n) = qBar V H ^ (2 * n - 1) * qBar V H := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : Nat.card ↥(P ⊓ wOf V H) * qBar V H = qBar V H ^ (2 * n - 1) * qBar V H := by
      rw [← h, h2]
    exact Nat.eq_of_mul_eq_mul_right hqpos h3
  have hKcard : Nat.card ↥(LinearMap.ker (spFormL a)) = qBar V H ^ (2 * n - 1) := by
    rw [natCard_ker_spFormL ha, hFcard]
  have hSncard : Set.ncard {w : Fin n ⊕ Fin n → GaloisField 2 f | CaseM.spForm a w = 0} =
      qBar V H ^ (2 * n - 1) := by
    rw [← Nat.card_coe_set_eq, ← hKcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w =>
      (LinearMap.mem_ker (f := spFormL a) (y := w)).symm)
  have hLncard : Set.ncard {w : Fin n ⊕ Fin n → GaloisField 2 f |
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} = qBar V H ^ (2 * n - 1) := by
    have hinj : Function.Injective (fun w : Fin n ⊕ Fin n → GaloisField 2 f =>
        ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)) := by
      intro w w' h
      apply ψ.injective
      apply Additive.toMul.injective
      exact Subtype.ext h
    have himg : (fun w : Fin n ⊕ Fin n → GaloisField 2 f =>
        ((Additive.toMul (ψ w) : ↥(wOf V H)) : G)) ''
        {w | ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} =
          ((P ⊓ wOf V H : Subgroup G) : Set G) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact Subgroup.mem_inf.mpr ⟨hw, (Additive.toMul (ψ w)).2⟩
      · intro hx
        have hx' : x ∈ P ⊓ wOf V H := hx
        have hxW : x ∈ wOf V H := (Subgroup.mem_inf.mp hx').2
        refine ⟨ψ.symm (Additive.ofMul ⟨x, hxW⟩), ?_, ?_⟩
        · show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul ⟨x, hxW⟩))) : ↥(wOf V H)) : G) ∈ P
          rw [AddEquiv.apply_symm_apply]
          exact (Subgroup.mem_inf.mp hx').1
        · show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul ⟨x, hxW⟩))) : ↥(wOf V H)) : G) = x
          rw [AddEquiv.apply_symm_apply]
          rfl
    have h1 := Set.ncard_image_of_injective
      {w : Fin n ⊕ Fin n → GaloisField 2 f | ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} hinj
    rw [himg] at h1
    rw [← h1, ← hPW]
    exact (Nat.card_coe_set_eq _).symm
  have hfwd : ∀ w : Fin n ⊕ Fin n → GaloisField 2 f,
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P → CaseM.spForm a w = 0 := by
    intro w hw
    obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
    have hvX : v ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hvV
    have hxmem : xToXbar hVH ⟨v, hvX⟩ ∈ Vy V H :=
      Subgroup.mem_subgroupOf.mpr
        (mem_barOf_iff.mpr ⟨Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩, hvV, rfl⟩)
    have hmemT : xToXbar hVH ⟨v, hvX⟩ ∈ T.map Φ.toMonoidHom := by
      rw [hTV]
      exact hxmem
    have ht_mem : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ∈ T := Subgroup.mem_map_equiv.mp hmemT
    have ht1 : Φ.symm (xToXbar hVH ⟨v, hvX⟩) ≠ 1 := by
      intro h1
      apply hvW
      have h2 : xToXbar hVH ⟨v, hvX⟩ = 1 := by
        have h3 := Φ.apply_symm_apply (xToXbar hVH ⟨v, hvX⟩)
        rw [h1, map_one] at h3
        exact h3.symm
      have h4 : piBar V H (Subgroup.inclusion (xOf_le_H hVH) ⟨v, hvX⟩) = 1 := by
        rw [← coe_xToXbar hVH ⟨v, hvX⟩, h2, Subgroup.coe_one]
      exact (piBar_eq_one_iff _).mp h4
    obtain ⟨μ, hμ, hmat⟩ := exists_ne_zero_mat_eq_spTrans hT ht_mem ht1
    have key := hNat.equiv ⟨v, hvX⟩ w
    have hcomm := hc.commute_of_mem_P hw hvV
    have hval : ((⟨v, hvX⟩ : ↥(xOf V H)) : G) = v := rfl
    rw [hval, hcomm, mul_assoc, mul_inv_cancel, mul_one] at key
    have hσw := ψ.injective (Additive.toMul.injective (Subtype.ext key))
    rw [hmat, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec] at hσw
    have h0 : (μ * CaseM.spForm a w) • a = 0 := by
      have h5 := congrArg (fun y => y - w) hσw
      simpa using h5
    rcases smul_eq_zero.mp h0 with h | h
    · exact (mul_eq_zero.mp h).resolve_left hμ
    · exact absurd h ha
  have hsub : {w : Fin n ⊕ Fin n → GaloisField 2 f |
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P} ⊆ {w | CaseM.spForm a w = 0} :=
    fun w hw => hfwd w hw
  have hLS := Set.eq_of_subset_of_ncard_le hsub (by rw [hSncard, hLncard])
  have hiff : ∀ w : Fin n ⊕ Fin n → GaloisField 2 f,
      ((Additive.toMul (ψ w) : ↥(wOf V H)) : G) ∈ P ↔ CaseM.spForm a w = 0 :=
    fun w => Set.ext_iff.mp hLS w
  have hxOf : xOf V H = H := by
    have h := hH.concl.2.1
    rw [sup_eq_left.mpr (hcP.trans (wOf_le_xOf V H))] at h
    exact h
  have hπinj : Function.Injective (projZ V H) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff x).mp hx
    rw [hZ] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hΨbij : Function.Bijective ((projZ V H).comp Φ.toMonoidHom) :=
    ⟨hπinj.comp Φ.injective,
      (QuotientGroup.mk'_surjective (Subgroup.center (Xbar V H))).comp Φ.surjective⟩
  have hVZ : VZ V H = T.map ((projZ V H).comp Φ.toMonoidHom) := by
    unfold VZ
    rw [← hTV, Subgroup.map_map]
  have hnorm : Subgroup.normalizer ((T.map ((projZ V H).comp Φ.toMonoidHom) :
      Subgroup (XbarZ V H)) : Set (XbarZ V H)) =
      (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f)))).map
        ((projZ V H).comp Φ.toMonoidHom) :=
    (Subgroup.map_normalizer_eq_of_bijective T hΨbij).symm
  have hpc : pCoreOf 2 ((Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f)))).map
      ((projZ V H).comp Φ.toMonoidHom)) =
      (pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f))))).map
        ((projZ V H).comp Φ.toMonoidHom) :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective _ hΨbij) _
  have hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 f)))) =
      spRad a :=
    spCoreStmt_holds n (GaloisField 2 f) ha hT
  have hRt : Rtilde V H P = (spRad a).map ((projZ V H).comp Φ.toMonoidHom) := by
    have hP' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) :=
      hH.tilde
    rw [hP', hVZ, hnorm, hpc, hcore]
  have hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom := by
    refine Subgroup.map_injective hπinj ?_
    rw [Subgroup.map_map]
    exact hRt
  have hPH : P ≤ H := hc.PleH
  have hPX : P ≤ xOf V H := by
    rw [hxOf]
    exact hPH
  have hbarP : barOf V H P ≤ barOf V H (xOf V H) := barOf_mono hPX
  have hRcard : Nat.card ↥(Rbar V H P) = qBar V H ^ (2 * n - 1) := by
    rw [hRbar, Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective,
      (hR n hn (GaloisField 2 f) a ha).2.2, hFcard]
  have hbar_card : Nat.card ↥(barOf V H P) = qBar V H ^ (2 * n - 1) := by
    rw [← hRcard]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarP).toEquiv).symm
  have hPcard := twb_card_barOf_mul (V := V) (H := H) (K := P) hPH
  rw [hbar_card, hPW] at hPcard
  refine ⟨hiff, hRbar, hxOf, ?_⟩
  rw [← hPcard, ← pow_add]
  congr 1
  omega

theorem bigPLocalStatement_holds : BigPLocalStatement :=
  bigPLocalStatement_of_spRad spRadGeneralStatement_holds

end CFSG.RankThree.GF2n.Tim79a
