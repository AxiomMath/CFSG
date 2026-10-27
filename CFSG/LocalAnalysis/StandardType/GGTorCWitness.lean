module

public import CFSG.LocalAnalysis.StandardType.GGTorCRoots
public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus

public section

namespace CFSG.StandardType.TorC

open CFSG.Open CFSG.StandardType.SpJoin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Multiplicative
open CFSG.LieType.Universal.Symplectic (weylRep)

variable {F : Type} [Field F]

@[expose] noncomputable def rootCEquiv (n m : ℕ) (hm : Odd m) :
    (Fin n → Multiplicative (ZMod m)) ≃* (Fin n → Multiplicative (ZMod m)) :=
  have : NeZero m := ⟨hm.pos.ne'⟩
  MulEquiv.ofBijective (rootC n m)
    ⟨rootC_injective hm, Finite.injective_iff_surjective.mp (rootC_injective hm)⟩

theorem rootCEquiv_apply {n m : ℕ} (hm : Odd m) (c : Fin n → Multiplicative (ZMod m)) :
    rootCEquiv n m hm c = rootC n m c := rfl

theorem conj_mem_normalizer_scalarA {G : Type} [Group G] {E : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    MulAut.conj g ∈ Subgroup.normalizer ((scalarA E : Subgroup (MulAut G)) : Set (MulAut G)) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro a
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨g * e * g⁻¹, (hg e).mp he, by simp only [map_mul, map_inv]⟩
  · rintro ⟨e, he, hae⟩
    refine ⟨g⁻¹ * e * g, (hg _).mpr (by rw [show g * (g⁻¹ * e * g) * g⁻¹ = e by group]; exact he),
      ?_⟩
    have h1 : a = (MulAut.conj g)⁻¹ * MulAut.conj e * MulAut.conj g := by
      rw [hae]
      group
    rw [h1]
    simp only [map_mul, map_inv]

@[expose] noncomputable def spReflAut (n p : ℕ) (k : Fin n) :
    MulAut (Fin n → Multiplicative (ZMod p)) :=
  { spReflPerm n p k with
    map_mul' := fun f g => by
      funext i
      change spRefl n p k (f * g) i = spRefl n p k f i * spRefl n p k g i
      unfold spRefl
      split_ifs with h
      · rfl
      · by_cases hik : i = k
        · subst hik
          simp [mul_comm]
        · simp [Function.update_of_ne hik] }

theorem spReflAut_toPerm (n p : ℕ) (k : Fin n) :
    MulAut.toPerm _ (spReflAut n p k) = spReflPerm n p k := rfl

theorem exists_weylB_automizer [CharP F 2] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn2 : 2 ≤ n)
    {ζp : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hζp : Function.Injective ζp) (hζpw : ∀ a, sl2W * ζp a * sl2W⁻¹ = ζp a⁻¹)
    (hn : ∀ k, MulAut.conj (weylRep n F k) ∈ Subgroup.normalizer
      ((scalarA (spPlaneTorus n ζp).range : Subgroup (MulAut (StatedSp n F))) :
        Set (MulAut (StatedSp n F)))) :
    ∃ ρ : (CoxeterMatrix.B n).Group →* MulAut ↥(scalarA (spPlaneTorus n ζp).range),
      Function.Injective ρ ∧
      ρ.range = ggAutomizer (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range
        (scalarA (spPlaneTorus n ζp).range) ∧
      ∀ k (a : ↥(scalarA (spPlaneTorus n ζp).range)),
        ((ρ ((CoxeterMatrix.B n).simple k) a : ↥(scalarA (spPlaneTorus n ζp).range)) :
          MulAut (StatedSp n F)) =
          MulAut.conj (weylRep n F k) * (a : MulAut (StatedSp n F)) *
            (MulAut.conj (weylRep n F k))⁻¹ := by
  classical
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  set E := (spPlaneTorus n ζp).range with hEdef
  have hDp : Function.Injective (spPlaneTorus n ζp) := spPlaneTorus_injective hζp n
  have hcenter : Subgroup.center (StatedSp n F) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n
  have hconjG : Function.Injective (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  let κ0 : (Fin n → Multiplicative (ZMod p)) →* ↥(scalarA E) :=
    ((MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).comp (spPlaneTorus n ζp)).codRestrict
      (scalarA E) (fun f => ⟨spPlaneTorus n ζp f, ⟨f, rfl⟩, rfl⟩)
  have hκ0 : Function.Bijective κ0 := by
    refine ⟨fun f f' h => hDp (hconjG (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩⟩
    exact ⟨f, rfl⟩
  let κ : (Fin n → Multiplicative (ZMod p)) ≃* ↥(scalarA E) := MulEquiv.ofBijective κ0 hκ0
  have hκ : ∀ f, ((κ f : ↥(scalarA E)) : MulAut (StatedSp n F)) =
      MulAut.conj (spPlaneTorus n ζp f) := fun f => rfl
  let S : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
    (spSignedGroup n p).comap (MulAut.toPerm (Fin n → Multiplicative (ZMod p)))
  have htoPerm : Function.Injective (MulAut.toPerm (Fin n → Multiplicative (ZMod p))) :=
    fun u v h => MulEquiv.ext fun f => congrArg (fun σ : Equiv.Perm _ => σ f) h
  have hrange : spSignedGroup n p ≤ (MulAut.toPerm (Fin n → Multiplicative (ZMod p))).range := by
    rw [spSignedGroup, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨spReflAut n p k, spReflAut_toPerm n p k⟩
  let tS : ↥S →* ↥(spSignedGroup n p) :=
    ((MulAut.toPerm (Fin n → Multiplicative (ZMod p))).comp S.subtype).codRestrict _
      (fun u => u.2)
  have htS : Function.Bijective tS := by
    refine ⟨fun u v h => Subtype.ext (htoPerm (congrArg Subtype.val h)), ?_⟩
    rintro ⟨σ, hσ⟩
    obtain ⟨u, hu⟩ := hrange hσ
    exact ⟨⟨u, show MulAut.toPerm _ u ∈ spSignedGroup n p by rw [hu]; exact hσ⟩, Subtype.ext hu⟩
  let eS : ↥S ≃* ↥(spSignedGroup n p) := MulEquiv.ofBijective tS htS
  obtain ⟨e₀, he₀⟩ : ∃ e : (CoxeterMatrix.B n).Group ≃* ↥(spSignedGroup n p),
      ∀ i : Fin n, ((e ((CoxeterMatrix.B n).simple i) : ↥(spSignedGroup n p)) :
        Equiv.Perm (Fin n → Multiplicative (ZMod p))) = spReflPerm n p i := by
    have : Fact p.Prime := ⟨hp⟩
    exact ggRC_coxeterB_equiv_spSigned hp2 hn2
  let ρ : (CoxeterMatrix.B n).Group →* MulAut ↥(scalarA E) :=
    (MulAut.congr κ).toMonoidHom.comp (S.subtype.comp (eS.symm.toMonoidHom.comp e₀.toMonoidHom))
  have hρ : Function.Injective ρ :=
    (MulAut.congr κ).injective.comp (S.subtype_injective.comp (eS.symm.injective.comp e₀.injective))
  have hρsimple_val : ∀ k (f : Fin n → Multiplicative (ZMod p)),
      ρ ((CoxeterMatrix.B n).simple k) (κ f) = κ (spRefl n p k f) := by
    intro k f
    have hu : MulAut.toPerm _ ((eS.symm (e₀ ((CoxeterMatrix.B n).simple k)) : ↥S) :
        MulAut (Fin n → Multiplicative (ZMod p))) = spReflPerm n p k := by
      rw [← he₀ k]
      exact congrArg Subtype.val (eS.apply_symm_apply (e₀ ((CoxeterMatrix.B n).simple k)))
    change κ (((eS.symm (e₀ ((CoxeterMatrix.B n).simple k)) : ↥S) :
      MulAut (Fin n → Multiplicative (ZMod p))) (κ.symm (κ f))) = _
    rw [MulEquiv.symm_apply_apply]
    congr 1
    exact congrArg (fun σ : Equiv.Perm _ => σ f) hu
  have hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ ((CoxeterMatrix.B n).simple k) a : ↥(scalarA E)) : MulAut (StatedSp n F)) =
        MulAut.conj (weylRep n F k) * (a : MulAut (StatedSp n F)) *
          (MulAut.conj (weylRep n F k))⁻¹ := by
    intro k a
    obtain ⟨f, rfl⟩ := κ.surjective a
    rw [hρsimple_val, hκ, hκ, ← weylRep_conj_spPlaneTorus h2F ζp hζpw k f]
    simp only [map_mul, map_inv]
  have hρrange : ρ.range =
      ggAutomizer (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range (scalarA E) := by
    apply le_antisymm
    · have hgenM : Subgroup.closure (Set.range (CoxeterMatrix.B n).simple) = ⊤ := by
        simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
          (CoxeterMatrix.B n).toCoxeterSystem.subgroup_closure_range_simple
      rw [MonoidHom.range_eq_map, ← hgenM, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have heq : ρ ((CoxeterMatrix.B n).simple k) = ggConjAut (scalarA E) (hn k) := by
        apply MulEquiv.ext
        intro a
        apply Subtype.ext
        rw [ggConjAut_apply]
        exact hρsimple k a
      rw [heq]
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨_, rfl⟩) (hn k)
    · intro ψ' hψ'
      obtain ⟨c, ⟨g, rfl⟩, hcN, hψc⟩ := mem_ggAutomizer_iff.mp hψ'
      have hgE : ∀ f, ∃ f', g * spPlaneTorus n ζp f * g⁻¹ = spPlaneTorus n ζp f' := by
        intro f
        have h1 := (Subgroup.mem_normalizer_iff.mp hcN (MulAut.conj (spPlaneTorus n ζp f))).mp
          ⟨_, ⟨f, rfl⟩, rfl⟩
        obtain ⟨e, ⟨f', rfl⟩, he⟩ := h1
        refine ⟨f', hconjG ?_⟩
        rw [he]
        simp only [map_mul, map_inv]
      obtain ⟨π, ε, hε, hπ⟩ := exists_signedPerm_of_normalizes hp hp2 hζp g hgE
      set u : MulAut (Fin n → Multiplicative (ZMod p)) := (MulAut.congr κ).symm ψ' with hu
      have hψu : ψ' = MulAut.congr κ u := by rw [hu, MulEquiv.apply_symm_apply]
      have hu_apply : ∀ f, g * spPlaneTorus n ζp f * g⁻¹ = spPlaneTorus n ζp (u f) := by
        intro f
        apply hconjG
        have h1 : ((ψ' (κ f) : ↥(scalarA E)) : MulAut (StatedSp n F)) =
            MulAut.conj g * MulAut.conj (spPlaneTorus n ζp f) * (MulAut.conj g)⁻¹ := hψc (κ f)
        have h2 : ψ' (κ f) = κ (u f) := by
          rw [hψu, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
            MulEquiv.symm_apply_apply]
        rw [h2, hκ] at h1
        rw [h1]
        simp only [map_mul, map_inv]
      have hus : SpCoord.IsSignedPerm (u : (Fin n → Multiplicative (ZMod p)) →
          (Fin n → Multiplicative (ZMod p))) :=
        ⟨π, ε, hε, fun f i => hπ f (u f) (hu_apply f) i⟩
      have huS : u ∈ S := by
        refine SpCoord.mem_of_isSignedPerm (H := S) (fun i => ?_) (fun a b _ => ?_) hus
        · show MulAut.toPerm _ (SpCoord.sgnAut i) ∈ spSignedGroup n p
          have h1 : MulAut.toPerm _ (SpCoord.sgnAut i) = coordInv n p i := by
            ext f t
            rfl
          rw [h1]
          exact coordInv_mem_spSignedGroup i
        · show MulAut.toPerm _ (SpCoord.permAut (Equiv.swap a b)) ∈ spSignedGroup n p
          have h1 : MulAut.toPerm _ (SpCoord.permAut (Equiv.swap a b)) =
              coordPerm n p (Equiv.swap a b) := by
            ext f t
            rfl
          rw [h1]
          exact coordPerm_mem_spSignedGroup _
      refine ⟨e₀.symm (eS ⟨u, huS⟩), ?_⟩
      change MulAut.congr κ ((eS.symm (e₀ (e₀.symm (eS ⟨u, huS⟩))) : ↥S) :
        MulAut (Fin n → Multiplicative (ZMod p))) = ψ'
      rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply, hψu]
  exact ⟨ρ, hρ, hρrange, hρsimple⟩

theorem exists_ggTorusTorWit_sp [CharP F 2] {m p n : ℕ} (hm : Odd m) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : p ∣ m) (hn2 : 2 ≤ n)
    {ζm : Multiplicative (ZMod m) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hζm : Function.Injective ζm)
    (hζmw : ∀ a, sl2W * ζm a * sl2W⁻¹ = ζm a⁻¹)
    {ζp : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hζp : Function.Injective ζp)
    (hpm' : ∀ a, ∃ b, ζm b = ζp a) (hmp : ∀ b, ζm b ^ p = 1 → ∃ a, ζp a = ζm b)
    (hcent : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
      h * ζp (ofAdd 1) = ζp (ofAdd 1) * h → h ∈ ζm.range) :
    ∃ w : GGTorusTorWit m n (StatedSp n F) (scalarA (spPlaneTorus n ζp).range),
      w.Holds (CartanMatrix.C n) (CoxeterMatrix.B n) ∧
      (∀ τ ∈ w.T, ∃ s ∈ w.Tsc, τ = MulAut.conj s) ∧ Odd (Nat.card w.Tsc) := by
  classical
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have : NeZero m := ⟨hm.pos.ne'⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hζpw : ∀ a, sl2W * ζp a * sl2W⁻¹ = ζp a⁻¹ := fun a => by
    obtain ⟨b, hb⟩ := hpm' a
    rw [← hb, hζmw, map_inv ζm, map_inv ζp, hb]
  set D := spPlaneTorus n ζm with hDdef
  set E := (spPlaneTorus n ζp).range with hEdef
  have hD : Function.Injective D := spPlaneTorus_injective hζm n
  have hDp : Function.Injective (spPlaneTorus n ζp) := spPlaneTorus_injective hζp n
  set R := rootCEquiv n m hm with hRdef
  set φ : (Fin n → Multiplicative (ZMod m)) →* StatedSp n F := D.comp R.symm.toMonoidHom
    with hφdef
  have hφ : Function.Injective φ := hD.comp R.symm.injective
  have hφapp : ∀ a, φ a = D (R.symm a) := fun a => rfl
  have hφrange : φ.range = D.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨R.symm a, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨R c, by rw [hφapp, MulEquiv.symm_apply_apply]⟩
  have hRcor : ∀ k z, R.symm (corTuple (CartanMatrix.C n).transpose k z) = corC n m k z := by
    intro k z
    rw [MulEquiv.symm_apply_eq, hRdef, rootCEquiv_apply, rootC_corC]
  have hcenter : Subgroup.center (StatedSp n F) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n
  have hconjG : Function.Injective (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  have hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range := fun g => by
    rw [hφrange]
    exact mem_range_spPlaneTorus_iff n hζm hpm' hmp g
  set ζ0 : Multiplicative (ZMod m) := ofAdd ((m / p : ℕ) : ZMod m) with hζ0
  have hζ0p : ζ0 ^ p = 1 := by
    rw [hζ0, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hpm,
      ZMod.natCast_self, ofAdd_zero]
  have hζ01 : ζ0 ≠ 1 := by
    rw [hζ0, Ne, ofAdd_eq_one, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm.pos hpm) hp.pos
    have hlt : m / p < m := Nat.div_lt_self hm.pos hp.one_lt
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  have hn : ∀ k, MulAut.conj (weylRep n F k) ∈
      Subgroup.normalizer ((scalarA E : Subgroup (MulAut (StatedSp n F))) :
        Set (MulAut (StatedSp n F))) :=
    fun k => conj_mem_normalizer_scalarA (weylRep_mem_normalizer_spPlaneTorus h2F ζp hζpw k)
  have hnformula : ∀ k (a : Fin n → Multiplicative (ZMod m)),
      weylRep n F k * φ a * (weylRep n F k)⁻¹ =
        φ a * (φ (corTuple (CartanMatrix.C n).transpose k (a k)))⁻¹ := by
    intro k a
    have hra : rootC n m (R.symm a) = a := by
      rw [← rootCEquiv_apply hm, ← hRdef, MulEquiv.apply_symm_apply]
    rw [hφapp, hφapp, hRcor, weylRep_conj_spPlaneTorus h2F ζm hζmw k, spRefl_eq_mul_corC, hra,
      map_mul, map_inv]
  have hT0 : ζp (ofAdd 1) ≠ 1 := fun h => by
    have h1 := hζp (h.trans (map_one ζp).symm)
    exact one_ne_zero (ofAdd_eq_one.mp h1)
  have hT0p : ζp (ofAdd 1) ^ p = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero, map_one]
  have htr := trace_ne_zero_of_pow_eq_one hT0 hpodd hT0p
  have hcentE : Subgroup.centralizer (E : Set (StatedSp n F)) ≤ φ.range := by
    intro g hg
    rw [hφrange]
    refine mem_range_spPlaneTorus_of_commute htr hcent n g fun i => ?_
    have hmem : lam i (ζp (ofAdd 1)) ∈ E :=
      ⟨Pi.mulSingle i (ofAdd 1), spPlaneTorus_mulSingle ζp i _⟩
    exact (Subgroup.mem_centralizer_iff.mp hg _ hmem).symm
  obtain ⟨ρ, hρ, hρrange, hρsimple⟩ := exists_weylB_automizer hp hp2 hn2 hζp hζpw hn
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_C (m := m) (n := n) (by omega) hm
  obtain ⟨w, hwT, hwTsc, -, -, hw⟩ := exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod
    (m := m) (N := n) (p := p) (G := StatedSp n F) (μ := Multiplicative (ZMod m))
    (MulEquiv.refl _) φ hφ (CartanMatrix.C n) B hCB hBC hcenter E hE ζ0 hζ0p hζ01
    (weylRep n F) hn hnformula hcentE (CoxeterMatrix.B n) ρ hρ hρrange hρsimple
  refine ⟨w, hw, ?_, ?_⟩
  · rw [hwT, hwTsc]
    rintro _ ⟨a, rfl⟩
    exact ⟨φ a, ⟨a, rfl⟩, rfl⟩
  · rw [hwTsc, Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m), Nat.card_zmod]
    exact hm.pow

end CFSG.StandardType.TorC

end
