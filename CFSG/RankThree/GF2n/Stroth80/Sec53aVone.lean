module

public import CFSG.RankThree.GF2n.Stroth80.Sec53aProof
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootAux
public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.LieType.SeitzGeneration.SpFourData
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec53a_finrank_inf_sup_sup
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {SB SC T : Submodule K E} {n m : ℕ}
    (hSB : Module.finrank K ↥SB = n) (hSC : Module.finrank K ↥SC = n)
    (hT : Module.finrank K ↥T = 2 * m)
    (hBT : Module.finrank K ↥(SB ⊓ T) + 1 = 2 * m)
    (hCT : Module.finrank K ↥(SC ⊓ T) + 1 = 2 * m)
    (hBC : Module.finrank K ↥(SB ⊓ SC) + 1 = 2 * m)
    (hspan : T ≤ SB ⊔ SC) :
    Module.finrank K ↥((SB ⊔ T) ⊓ (SC ⊔ T)) = 2 * m + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq SB T
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq SC T
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (SB ⊔ T) (SC ⊔ T)
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq SB SC
  have hsup : (SB ⊔ T) ⊔ (SC ⊔ T) = SB ⊔ SC := by
    calc (SB ⊔ T) ⊔ (SC ⊔ T) = (SB ⊔ SC) ⊔ (T ⊔ T) := sup_sup_sup_comm SB T SC T
      _ = (SB ⊔ SC) ⊔ T := by rw [sup_idem]
      _ = SB ⊔ SC := sup_eq_left.mpr hspan
  rw [hsup] at h3
  omega

section ImgVone

variable {V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.mem_img_vone_iff {C : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hcC : Ctx M Q Z C) (hnoC : NoA2 Q Z (LB M Q C))
    (hD : GlobalModelData M Q Z γ M₀) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img V) (e : M₀.E) :
    e ∈ M₀.img (Vone Q B C V) ↔
      e ∈ (imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T) := by
  have hA1Q : Q ⊓ QB B ≤ Q := inf_le_left
  have hA2Q : Q ⊓ QB C ≤ Q := inf_le_left
  have hS1 : Z ≤ (Q ⊓ QB B) ⊔ V := hZV.trans le_sup_right
  have hS2 : Z ≤ (Q ⊓ QB C) ⊔ V := hZV.trans le_sup_right
  have hmem1 : ∀ e : M₀.E, e ∈ M₀.img ((Q ⊓ QB B) ⊔ V) ↔
      e ∈ (imgQInfQB M₀ B ⊔ T : Submodule K M₀.E) := by
    intro e
    rw [quadModel_img_sup M₀ hA1Q hVQ]
    constructor
    · intro he
      rw [AddSubgroup.mem_sup] at he
      obtain ⟨a, ha, v, hv, rfl⟩ := he
      exact Submodule.add_mem_sup (Submodule.subset_span ha) ((hTmem v).mpr hv)
    · intro he
      rw [Submodule.mem_sup] at he
      obtain ⟨a, ha, v, hv, rfl⟩ := he
      exact AddSubgroup.mem_sup.mpr
        ⟨a, (hc.mem_imgQInfQB_iff (X := B) hs.width hs.n_gt hs.noA2 hD a).mp ha,
          v, (hTmem v).mp hv, rfl⟩
  have hmem2 : ∀ e : M₀.E, e ∈ M₀.img ((Q ⊓ QB C) ⊔ V) ↔
      e ∈ (imgQInfQB M₀ C ⊔ T : Submodule K M₀.E) := by
    intro e
    rw [quadModel_img_sup M₀ hA2Q hVQ]
    constructor
    · intro he
      rw [AddSubgroup.mem_sup] at he
      obtain ⟨a, ha, v, hv, rfl⟩ := he
      exact Submodule.add_mem_sup (Submodule.subset_span ha) ((hTmem v).mpr hv)
    · intro he
      rw [Submodule.mem_sup] at he
      obtain ⟨a, ha, v, hv, rfl⟩ := he
      exact AddSubgroup.mem_sup.mpr
        ⟨a, (hcC.mem_imgQInfQB_iff (X := C) hs.width hs.n_gt hnoC hD a).mp ha,
          v, (hTmem v).mp hv, rfl⟩
  rw [Vone]
  rw [quadModel_img_inf M₀ hS1 hS2 (sup_le hA1Q hVQ) (sup_le hA2Q hVQ)]
  exact and_congr (hmem1 e) (hmem2 e)

end ImgVone

section CardVone

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.card_vone_of_finrank (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hV : SpMNat hc t m) {C : Subgroup G} (hcC : Ctx M Q Z C)
    (hnoC : NoA2 Q Z (LB M Q C)) (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBT : Module.finrank K ↥(imgQInfQB M₀ B ⊓ T) + 1 = 2 * m)
    (hCT : Module.finrank K ↥(imgQInfQB M₀ C ⊓ T) + 1 = 2 * m)
    (hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓ imgQInfQB M₀ C) + 1 = 2 * m)
    (hspan : T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ C) :
    Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z := by
  haveI : FiniteDimensional K M₀.E := M₀.fin
  haveI hTfin : FiniteDimensional K ↥T := FiniteDimensional.finiteDimensional_submodule T
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hK2 : 2 ≤ Nat.card K := by rw [hD.card]; exact hq2
  have hVcard : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) :=
    SpMNat.card_V hV
  have hTcard : Nat.card ↥T = Nat.card Z ^ (2 * m) := by
    have hVT : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card ↥T := by
      rw [M₀.card_eq hVQ hZV]
      exact congrArg (Nat.card Z * ·)
        (Nat.card_congr (Equiv.subtypeEquivRight fun e => (hTmem e).symm))
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
    calc Nat.card Z * Nat.card ↥T = Nat.card ↥(Vt M (LB M Q B) B Z t) := hVT.symm
      _ = Nat.card Z ^ (2 * m + 1) := hVcard
      _ = Nat.card Z * Nat.card Z ^ (2 * m) := by rw [pow_succ']
  have hT : Module.finrank K ↥T = 2 * m := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := ↥T)
    have h2 : Nat.card K ^ Module.finrank K ↥T = Nat.card K ^ (2 * m) := by
      rw [← h, hTcard, hD.card]
    exact Nat.pow_right_injective hK2 h2
  have hSB : Module.finrank K ↥(imgQInfQB M₀ B) = n :=
    (hc.imgQInfQB_lagr hs.width hs.n_gt hs.noA2 hD).1
  have hSC : Module.finrank K ↥(imgQInfQB M₀ C) = n :=
    (hcC.imgQInfQB_lagr hs.width hs.n_gt hnoC hD).1
  have hint : Module.finrank K ↥((imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T)) = 2 * m + 1 :=
    sec53a_finrank_inf_sup_sup hSB hSC hT hBT hCT hBC hspan
  have hcardimg : Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t))) = Nat.card K ^ (2 * m + 1) := by
    calc Nat.card ↥(M₀.img (Vone Q B C (Vt M (LB M Q B) B Z t)))
        = Nat.card ↥((imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T)) :=
          Nat.card_congr (Equiv.subtypeEquivRight fun e =>
            Ctx.mem_img_vone_iff hc hs hcC hnoC hD hVQ hZV T hTmem e)
      _ = Nat.card K ^ Module.finrank K
            ↥((imgQInfQB M₀ B ⊔ T) ⊓ (imgQInfQB M₀ C ⊔ T)) :=
          Module.natCard_eq_pow_finrank
      _ = Nat.card K ^ (2 * m + 1) := by rw [hint]
  have hV1 : Nat.card ↥(Vone Q B C (Vt M (LB M Q B) B Z t)) =
      Nat.card Z * Nat.card K ^ (2 * m + 1) := by
    rw [M₀.card_eq (vone_le_Q hVQ) (Z_le_vone), hcardimg]
  have hVcard' : Nat.card ↥(Vt M (LB M Q B) B Z t) =
      Nat.card Z * Nat.card K ^ (2 * m) := by
    rw [M₀.card_eq hVQ hZV]
    congr 1
    calc Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card ↥T :=
          Nat.card_congr (Equiv.subtypeEquivRight fun e => (hTmem e).symm)
      _ = Nat.card Z ^ (2 * m) := hTcard
      _ = Nat.card K ^ (2 * m) := by rw [hD.card]
  rw [hV1, hVcard', hD.card]
  rw [pow_succ]
  ring

end CardVone

section SpQB

theorem card_Vt_inf_QB_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m)
    (hV : SpMNat hc t m) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB B) = Nat.card Z ^ (2 * m) := by
  obtain ⟨K, iF, iFin, hK, hrep⟩ := hV
  letI := iF
  letI := iFin
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hnat : SpNat hc t := ⟨K, iF, iFin, hK, m, hm, hrep⟩
  obtain ⟨φ, hφ, hker, hact⟩ := hrep
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ₂, M₀₂, hD₂, θ, hθ, u, hu0, hBiff, hW⟩ :=
    Ctx.sp_perp_data h34 hc hs hnotQB hK hm φ hφ hker ψ hψ
  set V := Vt M (LB M Q B) B Z t with hVdef
  have hZW0 : Z ≤ V ⊓ QB B := le_inf sec39_Z_le_Vt hc.Z_le_QB.1
  have hcard := card_eq_of_secVec (Z := Z) ψ hZW0 inf_le_left
    {x : Fin m ⊕ Fin m → K | spForm m K x u = 0} (fun x => hW x)
  have hform : ∀ x y : Fin m ⊕ Fin m → K,
      spForm m K x y = CFSG.Timmesfeld.ARS.CaseM.spForm x y := fun x y =>
    (spForm_apply x y).trans rfl
  have hset : Nat.card {x : Fin m ⊕ Fin m → K | spForm m K x u = 0} =
      Nat.card (LinearMap.ker (CFSG.Timmesfeld.Transvection.ModelRank.spFormL
        (K := K) (n := m) u)) := by
    have hsetEq : {x : Fin m ⊕ Fin m → K | spForm m K x u = 0} =
        {x : Fin m ⊕ Fin m → K | CFSG.Timmesfeld.ARS.CaseM.spForm x u = 0} := by
      ext x
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hform x u]
    rw [hsetEq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [LinearMap.mem_ker]
    exact ⟨fun h => CFSG.Timmesfeld.Transvection.ModelRank.spForm_eq_zero_comm h,
      fun h => CFSG.Timmesfeld.Transvection.ModelRank.spForm_eq_zero_comm h⟩
  have hpow : Nat.card Z * Nat.card Z ^ (2 * m - 1) = Nat.card Z ^ (2 * m) := by
    rw [← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega]
  rw [hcard, hset, CFSG.RankThree.GF2n.Tim79a.natCard_ker_spFormL hu0, hK, hpow]

theorem card_Vt_inf_QB_sp_conj (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) {m : ℕ} (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)) = Nat.card Z ^ (2 * m) := by
  have hVtN : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt hs.mem hr
  have hconjV : conjSubgroup r (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr hVtN
  have hEq : Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) =
      conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) := by
    calc Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)
        = Vt M (LB M Q B) B Z t ⊓ conjSubgroup r (QB B) := by rw [QB_conj]
      _ = conjSubgroup r (Vt M (LB M Q B) B Z t) ⊓ conjSubgroup r (QB B) :=
          congrArg (fun z => z ⊓ conjSubgroup r (QB B)) hconjV.symm
      _ = conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) :=
          (conjSubgroup_inf r (Vt M (LB M Q B) B Z t) (QB B)).symm
  rw [hEq, card_conjSubgroup]
  exact card_Vt_inf_QB_sp h34 hRoot hc hs hm hV

end SpQB

section SpConjW

variable {K : Type} [Field K] [Finite K]

theorem Ctx.sp_perp_conj_W (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K)
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) {u : Fin m ⊕ Fin m → K}
    (hW : ∀ x : Fin m ⊕ Fin m → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ spForm m K x u = 0) :
    ∀ x : Fin m ⊕ Fin m → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) ∧ secVec ψ w = x) ↔
        spForm m K x ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) = 0 := by
  classical
  let A : StatedSp m K :=
    ⟨(φ ⟨r, hr⟩ : GL (Fin m ⊕ Fin m) K), by
      rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨⟨r, hr⟩, rfl⟩⟩
  have hmatA : CFSG.LieType.Universal.Symplectic.SpExtras.mat m K A =
      (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply]
  have hform : ∀ x y : Fin m ⊕ Fin m → K,
      spForm m K x y = CFSG.Timmesfeld.ARS.CaseM.spForm x y := fun x y =>
    (spForm_apply x y).trans rfl
  have hVtN : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt hs.mem hr
  have hconjV : conjSubgroup r (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr hVtN
  have hEqC : Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) =
      conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) := by
    calc Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B)
        = Vt M (LB M Q B) B Z t ⊓ conjSubgroup r (QB B) := by rw [QB_conj]
      _ = conjSubgroup r (Vt M (LB M Q B) B Z t) ⊓ conjSubgroup r (QB B) :=
          congrArg (fun z => z ⊓ conjSubgroup r (QB B)) hconjV.symm
      _ = conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) :=
          (conjSubgroup_inf r (Vt M (LB M Q B) B Z t) (QB B)).symm
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwConj : (w : G) ∈ conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) := by
      have hwVtC : (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) :=
        ⟨w.2, hw.2⟩
      rwa [hEqC] at hwVtC
    have hb : r⁻¹ * (w : G) * r ∈ Vt M (LB M Q B) B Z t ⊓ QB B :=
      mem_conjSubgroup.mp hwConj
    have hbV : r⁻¹ * (w : G) * r ∈ Vt M (LB M Q B) B Z t := (Subgroup.mem_inf.mp hb).1
    let b' : ↥(Vt M (LB M Q B) B Z t) := ⟨r⁻¹ * (w : G) * r, hbV⟩
    have hwb : (w : G) = r * b' * r⁻¹ := by
      simp only [b']
      group
    have hsec : secVec ψ w = (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        secVec ψ b' := by
      apply hψ ⟨r, hr⟩ b' w
      simpa using hwb
    have hbW : spForm m K (secVec ψ b') u = 0 := (hW (secVec ψ b')).mp ⟨b', hb, rfl⟩
    rw [hsec, hform ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ secVec ψ b')
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)]
    have hiso := CFSG.Timmesfeld.Transvection.ModelRank.spForm_mat_mulVec A (secVec ψ b') u
    rw [hmatA] at hiso
    rw [hiso, ← hform (secVec ψ b') u]
    exact hbW
  · intro h2
    let y : Fin m ⊕ Fin m → K :=
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat m K A⁻¹) *ᵥ x
    have hmul : CFSG.LieType.Universal.Symplectic.SpExtras.mat m K A *
        CFSG.LieType.Universal.Symplectic.SpExtras.mat m K A⁻¹ = 1 := by
      rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
        CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply]
      simpa using congrArg (fun u : GL (Fin m ⊕ Fin m) K =>
        (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) (mul_inv_cancel A)
    have hAy : (CFSG.LieType.Universal.Symplectic.SpExtras.mat m K A) *ᵥ y = x := by
      simp only [y]
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    have hsp_y : spForm m K y u = 0 := by
      have hiso := CFSG.Timmesfeld.Transvection.ModelRank.spForm_mat_mulVec A y u
      have h2' := h2
      rw [hform x ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)] at h2'
      rw [← hAy, ← hmatA] at h2'
      rw [hiso] at h2'
      rwa [← hform y u] at h2'
    obtain ⟨b', hb', hb'x⟩ := (hW y).mpr hsp_y
    let w : G := r * b' * r⁻¹
    have hwConj : w ∈ conjSubgroup r (Vt M (LB M Q B) B Z t ⊓ QB B) := by
      apply mem_conjSubgroup.mpr
      have h : r⁻¹ * w * r = b' := by
        simp only [w]
        group
      rwa [h]
    have hwVtC : w ∈ Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup r B) := by
      rwa [hEqC]
    have hwVt : w ∈ Vt M (LB M Q B) B Z t := (Subgroup.mem_inf.mp hwVtC).1
    have hsecw : secVec ψ ⟨w, hwVt⟩ =
        (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ secVec ψ b' := by
      apply hψ ⟨r, hr⟩ b' ⟨w, hwVt⟩
      simp only [w]
    have hsecw_x : secVec ψ ⟨w, hwVt⟩ = x := by
      rw [hsecw, hb'x]
      rw [hmatA] at hAy
      exact hAy
    exact ⟨⟨w, hwVt⟩, ⟨⟨hwVt, (Subgroup.mem_inf.mp hwVtC).2⟩, hsecw_x⟩⟩

end SpConjW

section SpOrthogonal

theorem spForm_orthogonal_sup_eq_top {m : ℕ} {K : Type} [Field K]
    {u u' : Fin m ⊕ Fin m → K} (huu' : spForm m K u u' ≠ 0) :
    (spForm m K).orthogonal (Submodule.span K {u}) ⊔
        (spForm m K).orthogonal (Submodule.span K {u'}) = ⊤ := by
  have hnd : (spForm m K).Nondegenerate := spForm_nondegenerate
  have hrefl : (spForm m K).IsRefl :=
    LinearMap.IsAlt.isRefl (fun e => spForm_isAlt e)
  have hli : LinearIndependent K ![u, u'] :=
    CFSG.LieType.SeitzGeneration.linearIndependent_pair_of_spForm huu'
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact huu' (by simp)
  have hnot : u' ∉ Submodule.span K {u} := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hp := (LinearIndependent.pair_iff).mp hli
    have hrel : (-c) • u + (1 : K) • u' = 0 := by
      rw [← hc]
      module
    obtain ⟨-, h2⟩ := hp (-c) 1 hrel
    exact one_ne_zero h2
  have hdisj : Disjoint (Submodule.span K {u}) (Submodule.span K {u'}) :=
    (Submodule.disjoint_span_singleton' hu'0).mpr hnot
  have horth : (spForm m K).orthogonal
      ((spForm m K).orthogonal (Submodule.span K {u}) ⊔
        (spForm m K).orthogonal (Submodule.span K {u'})) = ⊥ := by
    change Submodule.orthogonalBilin (spForm m K)
      ((spForm m K).orthogonal (Submodule.span K {u}) ⊔
        (spForm m K).orthogonal (Submodule.span K {u'})) = ⊥
    rw [Submodule.orthogonalBilin_sup (B := spForm m K)]
    change (spForm m K).orthogonal ((spForm m K).orthogonal (Submodule.span K {u})) ⊓
      (spForm m K).orthogonal ((spForm m K).orthogonal (Submodule.span K {u'})) = ⊥
    rw [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl,
      LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl, hdisj.eq_bot]
  calc (spForm m K).orthogonal (Submodule.span K {u}) ⊔
        (spForm m K).orthogonal (Submodule.span K {u'})
      = (spForm m K).orthogonal ((spForm m K).orthogonal
          ((spForm m K).orthogonal (Submodule.span K {u}) ⊔
            (spForm m K).orthogonal (Submodule.span K {u'}))) :=
        (LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl _).symm
    _ = (spForm m K).orthogonal ⊥ := by rw [horth]
    _ = ⊤ := LinearMap.BilinForm.orthogonal_bot

end SpOrthogonal

section SpSpan

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {K₂ : Type} [Field K₂] {γ : G → K₂} {M₀ : Tim79.QuadModel Q Z K₂ γ}

theorem Ctx.le_sup_imgQInfQB_sp (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K)
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) {u : Fin m ⊕ Fin m → K}
    (hW : ∀ x : Fin m ⊕ Fin m → K,
      (∃ w : ↥(Vt M (LB M Q B) B Z t),
        (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ QB B ∧ secVec ψ w = x) ↔ spForm m K x u = 0)
    (huu' : spForm m K u
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0)
    (T : Submodule K₂ M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ (conjSubgroup r B) := by
  classical
  have hW' := Ctx.sp_perp_conj_W hc hs φ hφ ψ hψ hr hW
  set u' : Fin m ⊕ Fin m → K :=
    (φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u with hu'def
  have hspan_nat : (spForm m K).orthogonal (Submodule.span K {u}) ⊔
      (spForm m K).orthogonal (Submodule.span K {u'}) = ⊤ :=
    spForm_orthogonal_sup_eq_top huu'
  have hmem_orth : ∀ w z : Fin m ⊕ Fin m → K,
      w ∈ (spForm m K).orthogonal (Submodule.span K {z}) ↔ spForm m K w z = 0 := by
    intro w z
    rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    rw [LinearMap.mem_ker]
    have hsym : ∀ a b : Fin m ⊕ Fin m → K,
        spForm m K a b = 0 ↔ spForm m K b a = 0 := by
      intro a b
      rw [← spForm_isAlt.neg_eq a b, neg_eq_zero]
    exact ⟨fun h => (hsym z w).mp h, fun h => (hsym w z).mp h⟩
  intro e he
  obtain ⟨v, hvV, hvQ, rfl⟩ := (M₀.mem_img).mp ((hTmem e).mp he)
  let v' : ↥(Vt M (LB M Q B) B Z t) := ⟨v, hvV⟩
  set x : Fin m ⊕ Fin m → K := secVec ψ v' with hxdef
  have hxsum : x ∈ (spForm m K).orthogonal (Submodule.span K {u}) ⊔
      (spForm m K).orthogonal (Submodule.span K {u'}) := by
    rw [hspan_nat]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hxsum
  obtain ⟨a, ha, b, hb, hxab⟩ := hxsum
  have haW : spForm m K a u = 0 := (hmem_orth a u).mp ha
  have hbW : spForm m K b u' = 0 := (hmem_orth b u').mp hb
  obtain ⟨a', ha', ha'x⟩ := (hW a).mpr haW
  obtain ⟨b', hb', hb'x⟩ := (hW' b).mpr hbW
  have habV : (a' : G) * (b' : G) ∈ Vt M (LB M Q B) B Z t :=
    (Vt M (LB M Q B) B Z t).mul_mem a'.2 b'.2
  let w : ↥(Vt M (LB M Q B) B Z t) := ⟨(a' : G) * (b' : G), habV⟩
  have hsecw : secVec ψ w = x := by
    rw [show w = a' * b' from Subtype.ext rfl, secVec_mul, ha'x, hb'x]
    exact hxab
  have hz : (v' : G) * (w : G)⁻¹ ∈ Z :=
    (secVec_eq_iff ψ v' w).mp (by rw [hsecw])
  have hπv : M₀.π (v : G) = M₀.π (a' : G) + M₀.π (b' : G) := by
    have hzQ : (v' : G) * (w : G)⁻¹ ∈ Q := hc.Z_le_Q hz
    have hwQ : (w : G) ∈ Q := hc.Vt_le_Q t w.2
    have hv_eq : (v : G) = ((v' : G) * (w : G)⁻¹) * (w : G) := by
      rw [show (v' : G) = v from rfl]
      group
    rw [hv_eq, M₀.π_mul ((v' : G) * (w : G)⁻¹) hzQ (w : G) hwQ,
      (M₀.π_ker ((v' : G) * (w : G)⁻¹) hzQ).mpr hz, zero_add]
    rw [show (w : G) = (a' : G) * (b' : G) from rfl,
      M₀.π_mul (a' : G) (hc.Vt_le_Q t a'.2) (b' : G) (hc.Vt_le_Q t b'.2)]
  refine Submodule.mem_sup.mpr
    ⟨M₀.π (a' : G), Submodule.subset_span (M₀.pi_mem_img (S := Q ⊓ QB B)
        ⟨hc.Vt_le_Q t a'.2, (Subgroup.mem_inf.mp ha').2⟩ (hc.Vt_le_Q t a'.2)),
      M₀.π (b' : G), Submodule.subset_span (M₀.pi_mem_img (S := Q ⊓ QB (conjSubgroup r B))
        ⟨hc.Vt_le_Q t b'.2, (Subgroup.mem_inf.mp hb').2⟩ (hc.Vt_le_Q t b'.2)), hπv.symm⟩

end SpSpan

section SpFinrank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.finrank_inf_imgQInfQB_of_card
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {X : Subgroup G} (hcX : Ctx M Q Z X) (hnoX : NoA2 Q Z (LB M Q X))
    (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hcard : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB X) = Nat.card Z ^ (2 * m)) :
    Module.finrank K ↥(imgQInfQB M₀ X ⊓ T) + 1 = 2 * m := by
  haveI : FiniteDimensional K M₀.E := M₀.fin
  haveI hTfin : FiniteDimensional K ↥T := FiniteDimensional.finiteDimensional_submodule T
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZQB : Z ≤ QB X := hcX.Z_le_QB.1
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hK2 : 2 ≤ Nat.card K := by rw [hD.card]; exact hq2
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hm1 : 1 ≤ 2 * m := Nat.succ_le_iff.mpr (Nat.mul_pos (by norm_num) hm0)
  have hVcard0 : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z ^ (2 * m + 1) :=
    SpMNat.card_V hV
  have hTcard : Nat.card ↥T = Nat.card Z ^ (2 * m) := by
    have hVT : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card ↥T := by
      rw [M₀.card_eq hVQ hZV]
      exact congrArg (Nat.card Z * ·)
        (Nat.card_congr (Equiv.subtypeEquivRight fun e => (hTmem e).symm))
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
    calc Nat.card Z * Nat.card ↥T = Nat.card ↥(Vt M (LB M Q B) B Z t) := hVT.symm
      _ = Nat.card Z ^ (2 * m + 1) := hVcard0
      _ = Nat.card Z * Nat.card Z ^ (2 * m) := by rw [pow_succ']
  have hZ : Z ≤ Vt M (LB M Q B) B Z t ⊓ QB X := le_inf hZV hZQB
  have hS : Vt M (LB M Q B) B Z t ⊓ QB X ≤ Q := inf_le_left.trans hVQ
  have hcard_img : Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓ QB X)) =
      Nat.card Z ^ (2 * m - 1) := by
    have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB X) =
        Nat.card Z * Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓ QB X)) :=
      M₀.card_eq hS hZ
    refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
    calc Nat.card Z * Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓ QB X))
        = Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ QB X) := h1.symm
      _ = Nat.card Z ^ (2 * m) := hcard
      _ = Nat.card Z * Nat.card Z ^ (2 * m - 1) := by
          rw [← pow_succ']
          congr 1
          exact (Nat.sub_add_cancel hm1).symm
  have hinf_eq : M₀.img (Vt M (LB M Q B) B Z t ⊓ QB X) =
      M₀.img (Vt M (LB M Q B) B Z t) ⊓ M₀.img (Q ⊓ QB X) := by
    have hVtQinf : Vt M (LB M Q B) B Z t ⊓ QB X = Vt M (LB M Q B) B Z t ⊓ (Q ⊓ QB X) := by
      rw [← inf_assoc, inf_eq_left.mpr hVQ]
    rw [hVtQinf]
    exact quadModel_img_inf M₀ hZV (le_inf hc.Z_le_Q hZQB) hVQ inf_le_left
  have hmem : ∀ e : M₀.E, e ∈ imgQInfQB M₀ X ⊓ T ↔
      e ∈ M₀.img (Vt M (LB M Q B) B Z t ⊓ QB X) := by
    intro e
    constructor
    · rintro ⟨heS, heT⟩
      have heA : e ∈ M₀.img (Q ⊓ QB X) :=
        (hcX.mem_imgQInfQB_iff hs.width hs.n_gt hnoX hD e).mp heS
      have heV : e ∈ M₀.img (Vt M (LB M Q B) B Z t) := (hTmem e).mp heT
      rw [hinf_eq]
      exact ⟨heV, heA⟩
    · intro he
      rw [hinf_eq] at he
      exact ⟨(hcX.mem_imgQInfQB_iff hs.width hs.n_gt hnoX hD e).mpr he.2,
        (hTmem e).mpr he.1⟩
  have hcardinf : Nat.card ↥(imgQInfQB M₀ X ⊓ T) = Nat.card Z ^ (2 * m - 1) := by
    calc Nat.card ↥(imgQInfQB M₀ X ⊓ T)
        = Nat.card ↥(M₀.img (Vt M (LB M Q B) B Z t ⊓ QB X)) :=
          Nat.card_congr (Equiv.subtypeEquivRight hmem)
      _ = Nat.card Z ^ (2 * m - 1) := hcard_img
  have hfin : Module.finrank K ↥(imgQInfQB M₀ X ⊓ T) = 2 * m - 1 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := ↥(imgQInfQB M₀ X ⊓ T))
    have h2 : Nat.card K ^ Module.finrank K ↥(imgQInfQB M₀ X ⊓ T) =
        Nat.card K ^ (2 * m - 1) := by
      rw [← h, hcardinf, hD.card]
    exact Nat.pow_right_injective hK2 h2
  rw [hfin]
  exact Nat.sub_add_cancel hm1

theorem Ctx.finrank_imgQInfQB_inf_Vt_sp (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    Module.finrank K ↥(imgQInfQB M₀ B ⊓ T) + 1 = 2 * m :=
  Ctx.finrank_inf_imgQInfQB_of_card hc hs hm hV hc hs.noA2 hD T hTmem
    (card_Vt_inf_QB_sp h34 hRoot hc hs hm hV)

theorem Ctx.finrank_imgQInfQB_conj_inf_Vt_sp (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hm : 2 ≤ m) (hV : SpMNat hc t m)
    (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    Module.finrank K ↥(imgQInfQB M₀ (conjSubgroup r B) ⊓ T) + 1 = 2 * m := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  exact Ctx.finrank_inf_imgQInfQB_of_card hc hs hm hV (hc.conj_of_mem hrM)
    (hc.noA2_conj hs.noA2 hrM) hD T hTmem
    (card_Vt_inf_QB_sp_conj h34 hRoot hc hs hm hV hr)

end SpFinrank

section SpCardVone

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.card_vone_sp_of_hBC (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓
      imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m)
    (hspan : T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ (conjSubgroup r B)) :
    Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z := by
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  exact Ctx.card_vone_of_finrank hc hs hV hcC hnoC hD T hTmem
    (Ctx.finrank_imgQInfQB_inf_Vt_sp h34 hRoot hc hs hm hV hD T hTmem)
    (Ctx.finrank_imgQInfQB_conj_inf_Vt_sp h34 hRoot hc hs hm hV hD T hTmem hr)
    hBC hspan

theorem Ctx.card_vone_sp (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E) (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓
      imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m) :
    Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z := by
  have hV' : SpMNat hc t m := hV
  obtain ⟨K₁, iF, iFin, hK, hrep⟩ := hV'
  letI := iF
  letI := iFin
  haveI : CharP K₁ 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hnat : SpNat hc t := ⟨K₁, iF, iFin, hK, m, hm, hrep⟩
  have hVnat : SpMNat hc t m := ⟨K₁, iF, iFin, hK, hrep⟩
  obtain ⟨φ, hφ, hker, hact⟩ := hrep
  obtain ⟨-, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310NotQB_of_34 h34 G M Q Z B hc n t hs (Or.inl hnat)
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨nn, γ₂, M₀₂, hD₂, θ, hθ, u₀, hu₀, hBiff₀, hW₀⟩ :=
    Ctx.sp_perp_data h34 hc hs hnotQB hK hm φ hφ hker ψ hψ
  obtain ⟨u₁, hu₁, hBiff₁, hL₁, hplane₁⟩ :=
    Ctx.sp_points_core h34 hRoot hc hs hK hm φ hφ hker ψ hψ
  obtain ⟨c, hc₁⟩ := (hBiff₀ u₁).mp ((hBiff₁ u₁).mpr ⟨1, (one_smul K₁ u₁).symm⟩)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu₁
    rw [hc₁, h0, zero_smul]
  have hne₁ : spForm m K₁ u₁
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₁) ≠ 0 :=
    ((hplane₁ ⟨r, hr⟩).1).mp hplane
  have hne₀ : spForm m K₁ u₀
      ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀) ≠ 0 := by
    intro h0
    apply hne₁
    have hform : ∀ x y : Fin m ⊕ Fin m → K₁,
        spForm m K₁ x y = CFSG.Timmesfeld.ARS.CaseM.spForm x y := fun x y =>
      (spForm_apply x y).trans rfl
    rw [hc₁, Matrix.mulVec_smul]
    have hsc : spForm m K₁ (c • u₀)
        (c • ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀)) =
        c * (c * spForm m K₁ u₀
          ((φ ⟨r, hr⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K₁) *ᵥ u₀)) := by
      rw [hform (c • u₀) (c • _),
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left',
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right',
        ← hform u₀ _]
    rw [hsc, h0]
    simp
  have hspan : T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ (conjSubgroup r B) :=
    Ctx.le_sup_imgQInfQB_sp (K := K₁) (K₂ := K) (M₀ := M₀)
      hc hs φ hφ ψ hψ hr hW₀ hne₀ T hTmem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  exact Ctx.card_vone_of_finrank hc hs hVnat hcC hnoC hD T hTmem
    (Ctx.finrank_imgQInfQB_inf_Vt_sp h34 hRoot hc hs hm hVnat hD T hTmem)
    (Ctx.finrank_imgQInfQB_conj_inf_Vt_sp h34 hRoot hc hs hm hVnat hD T hTmem hr)
    hBC hspan

end SpCardVone

theorem stroth53a_of_sp_model_count
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hBC : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ (m : ℕ), SpMNat hc t m →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
        (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∃ T : Submodule K M₀.E,
        (∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) ∧
        Module.finrank K ↥(imgQInfQB M₀ B ⊓
          imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m)
    (hOdd : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t → Odd n) :
    Stroth53aStatement := by
  refine stroth53a_of_vone_card_odd ?_ hOdd
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane C V V₁ hC hV hV₁
  subst hC hV hV₁
  obtain ⟨K, iF, iFin, hK, m, hm, hrep⟩ := hsp
  letI := iF
  letI := iFin
  have hVnat : SpMNat hc t m := ⟨K, iF, iFin, hK, hrep⟩
  have hsp' : SpNat hc t := ⟨K, iF, iFin, hK, m, hm, hrep⟩
  obtain ⟨K₂, iF₂, iFin₂, iCh₂, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  letI := iF₂
  letI := iFin₂
  letI := iCh₂
  obtain ⟨T, hTmem, hBC'⟩ :=
    hBC G M Q Z B hc n t hs hsp' r hr hplane m hVnat K₂ γ M₀ hD
  exact Ctx.card_vone_sp h34 hRoot hc hs hm hVnat hr hplane hD T hTmem hBC'

end CFSG.RankThree.GF2n.Stroth80
