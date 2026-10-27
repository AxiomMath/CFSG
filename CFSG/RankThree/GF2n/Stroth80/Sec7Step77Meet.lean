module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec7OvoidTwoField
public import CFSG.RankThree.GF2n.Stroth80.Sec101SLPt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Pair

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_Hset_card [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hom : OmegaMinusNat hc t 2) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) :
    Nat.card (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B) = Nat.card K ^ 3 ∧
      Nat.card (hc.VtSub hS.model t) = Nat.card K ^ 4 := by
  classical
  obtain ⟨K', fK', finK', hchar, b', c', hirr, φ, θ, Ψ, hKK, hφ, hΨc, hΨr, e₀, he₀U, he₀0, hline,
    hΨe₀0, hQΨe₀, hHperp⟩ := sec7_om4_setup h34 hRoot hc hs hom M₀ ρ b hS
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hHU : ∀ e ∈ sec7Hset M₀ (Vt M (LB M Q B) B Z t) B, e ∈ hc.VtSub hS.model t := fun e he =>
    M₀.img_mono (sup_le inf_le_left hZV) he
  refine ⟨?_, ?_⟩
  · let X : AddSubgroup (Sec7Om4Idx → K') :=
      (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B).comap
        (((hc.VtSub hS.model t).subtype.toAddMonoidHom).comp Ψ.symm.toAddMonoidHom)
    have hX : ∀ y, y ∈ X ↔ polar (quadMinus 2 K' b' c') (Ψ ⟨e₀, he₀U⟩) y = 0 := fun y =>
      hHperp y
    have h1 := sec7_natCard_polar_perp hirr hΨe₀0 X hX
    have hmemX : ∀ w, w ∈ X ↔ ((Ψ.symm w : ↥(hc.VtSub hS.model t)) : M₀.E) ∈
        sec7Hset M₀ (Vt M (LB M Q B) B Z t) B := fun w => Iff.rfl
    have h2 : Nat.card (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B) = Nat.card X := by
      refine Nat.card_congr
        { toFun := fun e => ⟨Ψ ⟨e.1, hHU e.1 e.2⟩, ?_⟩
          invFun := fun w => ⟨((Ψ.symm w.1 : ↥(hc.VtSub hS.model t)) : M₀.E), w.2⟩
          left_inv := fun e => ?_
          right_inv := fun w => ?_ }
      · rw [hmemX, Ψ.symm_apply_apply]
        exact e.2
      · apply Subtype.ext
        show ((Ψ.symm (Ψ ⟨e.1, hHU e.1 e.2⟩) : ↥(hc.VtSub hS.model t)) : M₀.E) = e.1
        rw [Ψ.symm_apply_apply]
      · apply Subtype.ext
        show Ψ ⟨((Ψ.symm w.1 : ↥(hc.VtSub hS.model t)) : M₀.E), _⟩ = w.1
        have : (⟨((Ψ.symm w.1 : ↥(hc.VtSub hS.model t)) : M₀.E), _⟩ :
            ↥(hc.VtSub hS.model t)) = Ψ.symm w.1 := rfl
        rw [this, Ψ.apply_symm_apply]
    rw [h2, h1, hKK]
  · rw [Nat.card_congr Ψ.toEquiv, Nat.card_fun, hKK]
    congr 1
    rw [Nat.card_eq_fintype_card]
    simp [Sec7Om4Idx]


theorem sec7_card_img_conj [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {K : Type}
    [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
    (hS : IsTensorSetup hc n M₀ ρ b) {g : G} (hg : g ∈ M) {S : Subgroup G} (hZS : Z ≤ S) :
    Nat.card (M₀.img (conjSubgroup g S)) = Nat.card (M₀.img S) :=
  (Nat.card_congr (Equiv.subtypeEquiv (ρ (QuotientGroup.mk ⟨g, hg⟩)).toAdd.toEquiv
    (fun e => (sec7_img_conj_iff hc M₀ ρ b hS hg hZS e).symm))).symm

theorem step77FromOneMeet_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) : Step77FromOneMeetStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV y hy
  classical
  haveI := hc.normal_Q_in_M
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨hHcard, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hd : g⁻¹ * y * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy
  have hyM : y ∈ M := by
    have h3 := M.mul_mem (M.mul_mem hgM (hc.LB_le_M hd.1)) (M.inv_mem hgM)
    simpa [mul_assoc] using h3
  have hc' := hc.conj_of_mem hgM
  have hyL : y ∈ LB M Q (conjSubgroup g B) := by
    rw [hc.LB_conj hgM]
    exact mem_conjSubgroup.mpr hd.1
  have hcommQB : ∀ v ∈ Vt M (LB M Q B) B Z t,
      ⁅y, v⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup g B) := by
    intro v hv
    refine ⟨sec7_D1_comm_mem h71 h310chi h52a hA hc hs hno hgM hs1 hs2 hy v hv, ?_⟩
    have hvN : v ∈ Subgroup.normalizer ((conjSubgroup g B : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun b' hb' => ?_
      have hb0 : g⁻¹ * b' * g ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht (mem_conjSubgroup.mp hb')
      have hW := sec7_pair_mem_W h71 h310chi hc hs hno hgM hs1 hs2 _ hb0
      have e : g * (g⁻¹ * b' * g) * g⁻¹ = b' := by group
      rw [e] at hW
      have h1 := Subgroup.mem_centralizer_iff.mp hW.2 v hv
      have e2 : v * b' * v⁻¹ = b' := by
        rw [h1]
        group
      rw [e2]
      exact hb'
    have h1 := Ctx.comm_mem_inf_QB_of_mem_normalizer hc' (hVQ hv) hvN hyL
    rw [← commutatorElement_inv]
    exact (QB (conjSubgroup g B)).inv_mem h1.2
  let S' : Subgroup G :=
    (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup g B)) ⊔ Z
  let ν : M₀.E ≃+ M₀.E := (ρ (QuotientGroup.mk ⟨y, hyM⟩)).toAdd
  have hrange : ∀ u : ↥(hc.VtSub hS.model t), ν (u : M₀.E) - (u : M₀.E) ∈ M₀.img S' := by
    intro u
    obtain ⟨v, hvV, hvQ, hv⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp u.2)
    have hyvQ : y * v * y⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hyM).1 v hvQ
    have h1 : M₀.π (y * v * y⁻¹) = ν (M₀.π v) := hS.conj ⟨y, hyM⟩ v hvQ
    have h2 : M₀.π ⁅y, v⁆ = ν (M₀.π v) - M₀.π v := by
      have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
      rw [e, M₀.π_mul _ hyvQ _ (Q.inv_mem hvQ), M₀.pi_inv hvQ, ← h1, sub_eq_add_neg]
    have hcQ : ⁅y, v⁆ ∈ Q := by
      have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
      rw [e]
      exact Q.mul_mem hyvQ (Q.inv_mem hvQ)
    rw [← hv, ← h2]
    exact M₀.pi_mem_img (Subgroup.mem_sup_left (hcommQB v hvV)) hcQ
  have hS'card : Nat.card (M₀.img S') = Nat.card K ^ 3 := by
    have hS'eq : S' = conjSubgroup g ((Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z) := by
      show (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup g B)) ⊔ Z = _
      rw [conjSubgroup_sup', conjSubgroup_inf, QB_conj, hc.conj_Z_eq hgM]
    rw [hS'eq, sec7_card_img_conj hc M₀ ρ b hS hgM le_sup_right]
    exact hHcard
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hnotinj : ¬ Function.Injective
      (fun u : ↥(hc.VtSub hS.model t) =>
        (⟨ν (u : M₀.E) - (u : M₀.E), hrange u⟩ : ↥(M₀.img S'))) := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hS'card, hUcard] at h1
    have hq : 1 < Nat.card K := Finite.one_lt_card
    exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right hq (by norm_num)))
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨u₁, u₂, hu12, hne⟩ := hnotinj
  have hfix : ν ((u₁ : M₀.E) - (u₂ : M₀.E)) = (u₁ : M₀.E) - (u₂ : M₀.E) := by
    have h := congrArg Subtype.val hu12
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  have hu0 : (u₁ : M₀.E) - (u₂ : M₀.E) ≠ 0 := by
    intro h0
    exact hne (Subtype.ext (sub_eq_zero.mp h0))
  have hmemU : (u₁ : M₀.E) - (u₂ : M₀.E) ∈ hc.VtSub hS.model t :=
    (hc.VtSub hS.model t).sub_mem u₁.2 u₂.2
  obtain ⟨v₀, hv₀V, hv₀Q, hv₀⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hmemU)
  have hv₀Z : v₀ ∉ Z := by
    intro hz
    exact hu0 (hv₀.symm.trans ((M₀.π_ker v₀ hv₀Q).mpr hz))
  have hyv₀Q : y * v₀ * y⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hyM).1 v₀ hv₀Q
  have hcomm : ⁅y, v₀⁆ ∈ Z := by
    have h1 : M₀.π (y * v₀ * y⁻¹) = ν (M₀.π v₀) := hS.conj ⟨y, hyM⟩ v₀ hv₀Q
    have h2 : M₀.π ⁅y, v₀⁆ = 0 := by
      have e : ⁅y, v₀⁆ = (y * v₀ * y⁻¹) * v₀⁻¹ := rfl
      rw [e, M₀.π_mul _ hyv₀Q _ (Q.inv_mem hv₀Q), M₀.pi_inv hv₀Q, h1, hv₀, hfix, sub_eq_add_neg]
      exact add_neg_cancel _
    have hcQ : ⁅y, v₀⁆ ∈ Q := by
      have e : ⁅y, v₀⁆ = (y * v₀ * y⁻¹) * v₀⁻¹ := rfl
      rw [e]
      exact Q.mul_mem hyv₀Q (Q.inv_mem hv₀Q)
    exact (M₀.π_ker _ hcQ).mp h2
  intro hmeet
  have hwV : y * v₀ * y⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    have e : y * v₀ * y⁻¹ = ⁅y, v₀⁆ * v₀ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hZV hcomm) hv₀V
  have hwy : y * v₀ * y⁻¹ ∈ conjSubgroup y (Vt M (LB M Q B) B Z t) := by
    rw [mem_conjSubgroup]
    have e : y⁻¹ * (y * v₀ * y⁻¹) * y = v₀ := by group
    rw [e]
    exact hv₀V
  have hwZ : y * v₀ * y⁻¹ ∈ Z := by
    rw [← hmeet]
    exact ⟨hwV, hwy⟩
  apply hv₀Z
  have e : v₀ = ⁅y, v₀⁆⁻¹ * (y * v₀ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Z.mul_mem (Z.inv_mem hcomm) hwZ


theorem step77FromOneCore_of_moves (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hMoves : Step77FromOneMovesStatement) :
    Step77FromOneCoreStatement :=
  step77FromOneCore_of_moves_meet h34 h71 h310chi hZc hZV hZcard h52a hA hMoves
    (step77FromOneMeet_of_inputs h34 hRoot h71 h310chi h52a hA)

end CFSG.RankThree.GF2n.Stroth80
