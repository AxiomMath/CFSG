module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusFrame
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourSpinLifts
public import CFSG.LocalAnalysis.StandardType.GGHyperplaneMem
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGResQTwoLinearJ
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.RankThree.PartOne.S15K.OrthModel
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal Multiplicative Module
open CFSG.RankThree.Classical2 (orthDerived)

section Transport

variable {G : Type} [Group G] {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem plusFrame_spAct_of_mem_ggAutomizer {p : ℕ} {Bs L : Subgroup G}
    {ψΩ : ↥(orthDerived Q) →* G} (hψinj : Function.Injective ψΩ) (hψrange : ψΩ.range = L)
    (hcen : Subgroup.center ↥(orthDerived Q) = ⊥) {ℓΩ : ↥Bs →* ↥(orthDerived Q)}
    (hcompat : ∀ (b : ↥Bs) (z : ↥(orthDerived Q)),
      (b : G)⁻¹ * ψΩ z * (b : G) = ψΩ (ℓΩ b * z * (ℓΩ b)⁻¹))
    {τ : (Fin 3 → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)}
    (hnorm : ∀ g : V ≃ₗ[K] V, (∀ a ∈ ℓΩ.range.map (orthDerived Q).subtype,
        g * a * g⁻¹ ∈ ℓΩ.range.map (orthDerived Q).subtype) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    {c : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))}
    (hc : ∀ b, τ (c b) = ((ℓΩ b : ↥(orthDerived Q)) : V ≃ₗ[K] V))
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer L Bs) :
    (∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ b i, toAdd (c (φ b) (π i)) = ε i * toAdd (c b i)) ∧
      ∀ b, ℓΩ b = 1 → φ b = b := by
  classical
  unfold ggAutomizer at hφ
  induction hφ using Subgroup.closure_induction with
  | mem φ hφ =>
    obtain ⟨g, hgL, -, hφg⟩ := hφ
    rw [← hψrange] at hgL
    obtain ⟨g₀, rfl⟩ := hgL
    have hconj : ∀ b : ↥Bs, ℓΩ (φ b) = g₀ * ℓΩ b * g₀⁻¹ := by
      intro b
      set s₂ := g₀ * ℓΩ b * g₀⁻¹ with hs₂
      have key : ∀ z, ψΩ (ℓΩ (φ b) * z * (ℓΩ (φ b))⁻¹) = ψΩ (s₂ * z * s₂⁻¹) := by
        intro z
        rw [← hcompat (φ b) z, hφg b]
        have h1 := hcompat b (g₀⁻¹ * z * g₀)
        have e1 : (ψΩ g₀ * (b : G) * (ψΩ g₀)⁻¹)⁻¹ * ψΩ z * (ψΩ g₀ * (b : G) * (ψΩ g₀)⁻¹) =
            ψΩ g₀ * ((b : G)⁻¹ * ψΩ (g₀⁻¹ * z * g₀) * (b : G)) * (ψΩ g₀)⁻¹ := by
          simp only [map_mul, map_inv]
          group
        rw [e1, h1, hs₂]
        simp only [map_mul, map_inv]
        group
      have hcomm_z : ∀ z, z * (s₂⁻¹ * ℓΩ (φ b)) = (s₂⁻¹ * ℓΩ (φ b)) * z := by
        intro z
        have h := hψinj (key z)
        calc z * (s₂⁻¹ * ℓΩ (φ b)) = s₂⁻¹ * (s₂ * z * s₂⁻¹) * ℓΩ (φ b) := by group
          _ = s₂⁻¹ * (ℓΩ (φ b) * z * (ℓΩ (φ b))⁻¹) * ℓΩ (φ b) := by rw [h]
          _ = (s₂⁻¹ * ℓΩ (φ b)) * z := by group
      have hmem : s₂⁻¹ * ℓΩ (φ b) ∈ Subgroup.center ↥(orthDerived Q) :=
        Subgroup.mem_center_iff.mpr hcomm_z
      rw [hcen, Subgroup.mem_bot] at hmem
      exact (inv_mul_eq_one.mp hmem).symm
    refine ⟨?_, fun b hb => ?_⟩
    · obtain ⟨π, ε, hε, hπ⟩ := hnorm (g₀ : V ≃ₗ[K] V) (by
        rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
        refine ⟨ℓΩ (φ b), ⟨φ b, rfl⟩, ?_⟩
        simp only [Subgroup.coe_subtype, hconj, Subgroup.coe_mul, Subgroup.coe_inv])
      refine ⟨π, ε, hε, fun b i => hπ (c b) (c (φ b)) ?_ i⟩
      rw [hc, hc, hconj]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    · apply Subtype.ext
      rw [hφg b]
      have h1 := hcompat b g₀
      rw [hb, one_mul, inv_one, mul_one] at h1
      calc ψΩ g₀ * (b : G) * (ψΩ g₀)⁻¹ = (b : G) * ((b : G)⁻¹ * ψΩ g₀ * (b : G)) * (ψΩ g₀)⁻¹ := by
            group
        _ = (b : G) := by rw [h1]; group
  | one =>
    exact ⟨⟨1, fun _ => 1, fun _ => Or.inl rfl, fun b i => by simp⟩, fun b _ => rfl⟩
  | mul φ₁ φ₂ _ _ ih₁ ih₂ =>
    obtain ⟨⟨π₁, ε₁, hε₁, h₁⟩, hk₁⟩ := ih₁
    obtain ⟨⟨π₂, ε₂, hε₂, h₂⟩, hk₂⟩ := ih₂
    refine ⟨⟨π₁ * π₂, fun i => ε₁ (π₂ i) * ε₂ i, fun i => ?_, fun b i => ?_⟩, fun b hb => ?_⟩
    · rcases hε₁ (π₂ i) with h | h <;> rcases hε₂ i with h' | h' <;> simp [h, h']
    · rw [MulAut.mul_apply, Equiv.Perm.mul_apply, h₁, h₂, mul_assoc]
    · rw [MulAut.mul_apply, hk₂ b hb, hk₁ b hb]
  | inv φ _ ih =>
    obtain ⟨⟨π, ε, hε, h⟩, hk⟩ := ih
    refine ⟨⟨π⁻¹, fun i => ε (π⁻¹ i), fun i => hε _, fun b i => ?_⟩, fun b hb => ?_⟩
    · have h1 := h (φ⁻¹ b) (π⁻¹ i)
      have hπi : π (π⁻¹ i) = i := (Equiv.Perm.inv_eq_iff_eq.mp rfl).symm
      rw [MulAut.apply_inv_self, hπi] at h1
      have hsq : ε (π⁻¹ i) * ε (π⁻¹ i) = 1 := by
        rcases hε (π⁻¹ i) with h' | h' <;> rw [h'] <;> ring
      rw [h1, ← mul_assoc, hsq, one_mul]
    · have h1 := hk b hb
      calc φ⁻¹ b = φ⁻¹ (φ b) := by rw [h1]
        _ = b := MulAut.inv_apply_self _ _ _

end Transport

section Position


set_option maxHeartbeats 1000000 in
theorem ggOppPlus_plane_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmark : GGCentralImage .POmegaMinus 4 f L) {r u : MulAut ↥Bs}
    (hrL : r ∈ ggAutomizer L Bs) (huL : u ∈ ggAutomizer L Bs) (hr2 : r * r = 1)
    (hu2 : u * u = 1) (hru4 : (r * u) ^ 4 = 1) (hru2 : (r * u) ^ 2 ≠ 1) {xB d : ↥Bs}
    (hxB : (xB : G) = x) (hrx : r xB = xB) (hux : u xB = xB) (hrd : r d = d) (hud : u d = d)
    (hpl : ∀ z : ↥Bs, r z = z → u z = z → ∃ i j : ℕ, z = xB ^ i * d ^ j)
    (hmv : ∃ φ ∈ ggAutomizer L Bs, φ d ≠ d) {J' : Subgroup G}
    (hJ' : LargeEvenLayer (L ⊓ Subgroup.centralizer
      ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) = J') :
    CFSG.Assembly.IsComponentOf J' (L ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) ∧
      Bs ⊓ Subgroup.centralizer (J' : Set G) = ggHyperplane Bs r ⊓ ggHyperplane Bs u ∧
      ggRankOneIn L Bs r ≤ J' ∧ ggRankOneIn L Bs u ≤ J' ∧
      p ∣ Nat.card J' ∧ ¬ LargeEvenSmall J' ∧
      GGHasLabel ⟨.A, 3, f⟩ (↥J' ⧸ Subgroup.center ↥J') ∧ Subgroup.center ↥J' = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hBs, -, hLx, -⟩ := GGConfig.tableB_facts hcfg.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : (2 : ℕ) ∣ 1 :=
      (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hpq
    omega
  have hcommBs : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hpowBs : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  obtain ⟨ψ, hker, hrange, ℓ, hℓ, -, -, hrankℓ⟩ :=
    F4KGPosition.exists_spinMinus_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg (Or.inl rfl)
      hmark
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hirr := minusCoeffs_irr 2 f
  let Q := Spin.quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  let ψn : ↥(spinGroup Q) →* G := ψ
  let ℓn : ↥Bs →* ↥(spinGroup Q) := ℓ
  have hcenU : Subgroup.center ↥(spinGroup Q) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (by decide : 4 ≤ 4) hirr
  have hψinj : Function.Injective ψn := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcenU.le
  let ι := Spin.spinEquivCommutatorQuadMinus (n := 4) le_rfl hirr
    (CharTwo.two_eq_zero (R := GaloisField 2 f))
  let ψΩ : ↥(orthDerived Q) →* G := ψn.comp ι.symm.toMonoidHom
  let ℓΩ : ↥Bs →* ↥(orthDerived Q) := ι.toMonoidHom.comp ℓn
  have hψΩinj : Function.Injective ψΩ := hψinj.comp ι.symm.injective
  have hψΩrange : ψΩ.range = L := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.symm.surjective,
      ← MonoidHom.range_eq_map]
    exact hrange
  have hcompat : ∀ (b : ↥Bs) (z : ↥(orthDerived Q)),
      (b : G)⁻¹ * ψΩ z * (b : G) = ψΩ (ℓΩ b * z * (ℓΩ b)⁻¹) := by
    intro b z
    have h1 : ι.symm (ℓΩ b * z * (ℓΩ b)⁻¹) = ℓn b * ι.symm z * (ℓn b)⁻¹ := by
      simp only [ℓΩ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
        MulEquiv.symm_apply_apply]
    show (b : G)⁻¹ * ψn (ι.symm z) * b = ψn (ι.symm (ℓΩ b * z * (ℓΩ b)⁻¹))
    rw [h1]
    exact hℓ b (ι.symm z)
  have hcenΩ : Subgroup.center ↥(orthDerived Q) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : ι.symm z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply ι.injective
      rw [map_mul, map_mul, ι.apply_symm_apply]
      exact hz (ι g)
    rw [hcenU, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← ι.apply_symm_apply z, hz', map_one]
  have hEΩ : ℓΩ.range.map (orthDerived Q).subtype ≤ orthDerived Q := Subgroup.map_subtype_le _
  have hpowE : ∀ a ∈ ℓΩ.range.map (orthDerived Q).subtype, a ^ p = 1 := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow, hpowBs b, map_one, map_one]
  have hcommE : ∀ a ∈ ℓΩ.range.map (orthDerived Q).subtype,
      ∀ b ∈ ℓΩ.range.map (orthDerived Q).subtype, a * b = b * a := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩ _ ⟨_, ⟨b', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcommBs b b']
  have hcardE : p ^ 3 ≤ Nat.card (ℓΩ.range.map (orthDerived Q).subtype) := by
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective]
    have hr : ℓΩ.range = ℓn.range.map ι.toMonoidHom := MonoidHom.range_comp _ _
    rw [hr, Subgroup.card_map_of_injective ι.injective]
    exact hrankℓ
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.RankThree.PartOne.S15K.polar_nondegenerate_quadMinus hirr
  have hdim8 : finrank (GaloisField 2 f) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) =
      8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega) hirr
  have hpqF : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hF]; exact hpq
  obtain ⟨τ, hτinj, hτrange, hsingle, hnorm⟩ :=
    OmPlusFrame.exists_plusFrame hQnd hdim8 hminus hp hp2 hpqF hEΩ hpowE hcommE hcardE
  have hmemτ : ∀ b : ↥Bs, (orthDerived Q).subtype.comp ℓΩ b ∈ τ.range := fun b => by
    rw [hτrange]
    exact ⟨ℓΩ b, ⟨b, rfl⟩, rfl⟩
  let c : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)) :=
    (MonoidHom.ofInjective hτinj).symm.toMonoidHom.comp
      (((orthDerived Q).subtype.comp ℓΩ).codRestrict τ.range hmemτ)
  have hc : ∀ b, τ (c b) = (ℓΩ b).1 := fun b =>
    congrArg Subtype.val ((MonoidHom.ofInjective hτinj).apply_symm_apply
      (((orthDerived Q).subtype.comp ℓΩ).codRestrict τ.range hmemτ b))
  have hcker : ∀ b, c b = 1 ↔ ℓΩ b = 1 := by
    intro b
    constructor
    · intro h
      have := hc b
      rw [h, map_one] at this
      exact Subtype.ext this.symm
    · intro h
      apply hτinj
      rw [hc, h, map_one]
      rfl
  have hcsurj : ∀ f' : Fin 3 → Multiplicative (ZMod p), ∃ b, c b = f' := by
    intro f'
    have h1 : τ f' ∈ ℓΩ.range.map (orthDerived Q).subtype := hτrange ▸ ⟨f', rfl⟩
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h1
    exact ⟨b, hτinj ((hc b).trans hb)⟩
  have hA := fun {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer L Bs) =>
    plusFrame_spAct_of_mem_ggAutomizer hψΩinj hψΩrange hcenΩ hcompat hnorm hc hφ
  obtain ⟨⟨πr, εr, hεr, hcr⟩, hkr⟩ := hA hrL
  obtain ⟨⟨πu, εu, hεu, hcu⟩, hku⟩ := hA huL
  let cv : ↥Bs → Fin 3 → ZMod p := fun b i => toAdd (c b i)
  have hcv_act : ∀ {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → ZMod p} {φ : MulAut ↥Bs},
      (∀ b i, toAdd (c (φ b) (π i)) = ε i * toAdd (c b i)) →
        ∀ b, cv (φ b) = OmPlusFrame.spAct π ε (cv b) := by
    intro π ε φ hφ b
    funext k
    have h1 := hφ b (π.symm k)
    rw [Equiv.apply_symm_apply] at h1
    exact h1
  have hcvr := hcv_act hcr
  have hcvu := hcv_act hcu
  have hcvsurj : ∀ v : Fin 3 → ZMod p, ∃ b, cv b = v := by
    intro v
    obtain ⟨b, hb⟩ := hcsurj fun i => ofAdd (v i)
    exact ⟨b, funext fun i => by simp only [cv, hb, toAdd_ofAdd]⟩
  have hcv0 : ∀ b, cv b = 0 ↔ ℓΩ b = 1 := by
    intro b
    rw [← hcker]
    constructor
    · intro h
      funext i
      have := congrFun h i
      simpa [cv] using this
    · intro h
      funext i
      simp [cv, h]
  have h2 : ∀ v, OmPlusFrame.spAct πr εr (OmPlusFrame.spAct πr εr v) = v := by
    intro v
    obtain ⟨b, rfl⟩ := hcvsurj v
    rw [← hcvr, ← hcvr, ← MulAut.mul_apply, hr2, MulAut.one_apply]
  have h2' : ∀ v, OmPlusFrame.spAct πu εu (OmPlusFrame.spAct πu εu v) = v := by
    intro v
    obtain ⟨b, rfl⟩ := hcvsurj v
    rw [← hcvu, ← hcvu, ← MulAut.mul_apply, hu2, MulAut.one_apply]
  have h4 : ∀ v, OmPlusFrame.spAct πr εr (OmPlusFrame.spAct πu εu (OmPlusFrame.spAct πr εr
      (OmPlusFrame.spAct πu εu (OmPlusFrame.spAct πr εr (OmPlusFrame.spAct πu εu
        (OmPlusFrame.spAct πr εr (OmPlusFrame.spAct πu εu v))))))) = v := by
    intro v
    obtain ⟨b, rfl⟩ := hcvsurj v
    simp only [← hcvr, ← hcvu]
    congr 1
    have h1 := congrArg (fun φ : MulAut ↥Bs => φ b) hru4
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h1
  have hnc : ∃ w, OmPlusFrame.spAct πr εr (OmPlusFrame.spAct πu εu w) ≠
      OmPlusFrame.spAct πu εu (OmPlusFrame.spAct πr εr w) := by
    by_contra hcon
    push Not at hcon
    apply hru2
    have hfix : ∀ b : ↥Bs, cv (((r * u) ^ 2) b) = cv b := by
      intro b
      rw [pow_two, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hcvr, hcvu, hcvr, hcvu,
        hcon (cv b), h2', h2]
    set α := (r * u) ^ 2 with hα
    have hcα : ∀ b, c (α b) = c b := fun b =>
      funext fun i => toAdd.injective (congrFun (hfix b) i)
    have hkα : ∀ b, ℓΩ (α b * b⁻¹) = 1 := fun b =>
      (hcker _).mp (by rw [map_mul, map_inv, hcα, mul_inv_cancel])
    have hαk : ∀ k, ℓΩ k = 1 → α k = k := by
      intro k hk
      rw [hα, pow_two, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hku k hk, hkr k hk,
        hku k hk, hkr k hk]
    have hαα : ∀ b, α (α b) = b := by
      intro b
      have h1 := congrArg (fun φ : MulAut ↥Bs => φ b) hru4
      have h4α : (r * u) ^ 4 = α * α := by rw [hα, ← pow_add]
      simp only [h4α, MulAut.mul_apply, MulAut.one_apply] at h1
      exact h1
    ext b
    have hk := hkα b
    obtain ⟨k, hkdef⟩ : ∃ k, k = α b * b⁻¹ := ⟨_, rfl⟩
    rw [← hkdef] at hk
    have hαb : α b = k * b := by rw [hkdef, inv_mul_cancel_right]
    have h3 : α (α b) = k * k * b := by
      rw [hαb, map_mul, hαk k hk, hαb, mul_assoc]
    rw [hαα] at h3
    have hkk : k * k = 1 := by
      have h5 := congrArg (· * b⁻¹) h3
      simpa [mul_assoc] using h5.symm
    have hk1 : k = 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
      have h6 := (pow_gcd_eq_one (a := k) (m := 2) (n := p)).mpr ⟨by rw [pow_two, hkk],
        hpowBs k⟩
      rwa [hcop.gcd_eq_one, pow_one] at h6
    rw [hαb, hk1, one_mul, MulAut.one_apply]
  have hvr : OmPlusFrame.spAct πr εr (cv d) = cv d := by rw [← hcvr, hrd]
  have hvu : OmPlusFrame.spAct πu εu (cv d) = cv d := by rw [← hcvu, hud]
  obtain ⟨j₀, hj₀⟩ := OmPlusFrame.eq_single_of_spAct_pair hp2 hεr hεu h2 h2' h4 hnc hvr hvu
  have hd1 : ℓΩ d ≠ 1 := by
    intro h
    obtain ⟨φ, hφ, hφd⟩ := hmv
    exact hφd ((hA hφ).2 d h)
  have ha : cv d j₀ ≠ 0 := by
    intro h0
    apply hd1
    rw [← hcv0]
    funext i
    by_cases hi : i = j₀
    · subst hi
      exact h0
    · exact hj₀ i hi
  have hcd : c d = Pi.mulSingle j₀ (ofAdd (cv d j₀)) := by
    funext i
    by_cases hi : i = j₀
    · subst hi
      rw [Pi.mulSingle_eq_same]
      rfl
    · rw [Pi.mulSingle_eq_of_ne hi]
      exact toAdd_eq_zero.mp (hj₀ i hi)
  have ht2 : finrank (GaloisField 2 f)
      (CFSG.RankThree.PartOne.LIT.commSpace (ℓΩ d).1) = 2 := by
    rw [← hc d, hcd]
    exact hsingle j₀ _ ha
  set t : ↥(orthDerived Q) := ℓΩ d with htdef
  have htp : t ^ p = 1 := by rw [htdef, ← map_pow, hpowBs d, map_one]
  have hK1 := OmPlusFrame.eq_one_of_pow_eq_one_of_dvd_add_one hp hp2 hpqF
  have hAel : IsElemAbelian p ℓΩ.range := isElemAbelian_range_of_isElemAbelian hBs ℓΩ
  obtain ⟨-, -, hcomp, hcent⟩ := OrthRestOdd.isEndNode_of_commSpace_two hQnd (by omega) hp hp2
    hK1 hAel ⟨d, rfl⟩ hd1 ht2
  have hx := OmPlusFrame.oddOrderIsometry_of_orthDerived hQnd hp hp2 htp
  obtain ⟨h6, hplus⟩ := OmPlusFrame.isPlusType_fixedSpace_of_commSpace_two hdim8 hminus hp hp2
    hpqF hx ht2
  have hT := OmPlusFrame.exists_three_of_isPlusType h6 hplus
  set H := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hHdef
  have hmemH : ∀ z : ↥Bs, (z : G) ∈ H ↔ r z = z ∧ u z = z := fun z => by
    rw [hHdef, Subgroup.mem_inf, mem_ggHyperplane_iff', mem_ggHyperplane_iff']
  have hxH : x ∈ H := by
    rw [← hxB]
    exact (hmemH xB).mpr ⟨hrx, hux⟩
  have hdH : (d : G) ∈ H := (hmemH d).mpr ⟨hrd, hud⟩
  have hHBs : H ≤ Bs := fun z hz => by
    obtain ⟨⟨w, -, rfl⟩, -⟩ := hz
    exact w.2
  have hHform : ∀ z ∈ H, ∃ i j : ℕ, z = x ^ i * (d : G) ^ j := by
    intro z hz
    obtain ⟨h1, h2⟩ := (hmemH ⟨z, hHBs hz⟩).mp hz
    obtain ⟨i, j, hij⟩ := hpl _ h1 h2
    refine ⟨i, j, ?_⟩
    have h3 := congrArg Subtype.val hij
    simpa [hxB] using h3
  have hdcomm : ∀ w : ↥(orthDerived Q), (d : G) * ψΩ w = ψΩ w * d ↔ w * t = t * w := by
    intro w
    have h1 := hcompat d w
    rw [← htdef] at h1
    constructor
    · intro h
      have h2 : ψΩ (t * w * t⁻¹) = ψΩ w := by
        rw [← h1, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
      have h3 := hψΩinj h2
      calc w * t = t * w * t⁻¹ * t := by rw [h3]
        _ = t * w := by group
    · intro h
      have h3 : t * w * t⁻¹ = w := by
        rw [← h]
        group
      have h2 : (d : G)⁻¹ * ψΩ w * d = ψΩ w := by rw [h1, h3]
      calc (d : G) * ψΩ w = d * ((d : G)⁻¹ * ψΩ w * d) := by rw [h2]
        _ = ψΩ w * d := by group
  have hψL : ∀ w, ψΩ w ∈ L := fun w => hψΩrange ▸ ⟨w, rfl⟩
  have hCH : L ⊓ Subgroup.centralizer (H : Set G) =
      (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))).map ψΩ := by
    ext z
    constructor
    · rintro ⟨hzL, hzC⟩
      rw [← hψΩrange] at hzL
      obtain ⟨w, rfl⟩ := hzL
      refine ⟨w, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hdcomm w).mp ((Subgroup.mem_centralizer_iff.mp hzC) d hdH))
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hψL w, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      obtain ⟨i, j, rfl⟩ := hHform h hh
      have hxw : Commute x (ψΩ w) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hLx (hψL w))).symm
      have hdw : Commute (d : G) (ψΩ w) :=
        (hdcomm w).mpr (Subgroup.mem_centralizer_singleton_iff.mp hw)
      exact ((hxw.pow_left i).mul_left (hdw.pow_left j)).eq
  have hJ'eq : J' = (LargeEvenLayer (Subgroup.centralizer ({t} : Set ↥(orthDerived Q)))).map ψΩ :=
    by rw [← hJ', hCH, largeEvenLayer_map_of_injective _ hψΩinj]
  have hrank : ∀ {v : MulAut ↥Bs}, H ≤ ggHyperplane Bs v → ggRankOneIn L Bs v ≤ J' := by
    intro v hv
    unfold ggRankOneIn ggOTwoPrime
    rw [Subgroup.closure_le]
    rintro y ⟨⟨hyL, hyC⟩, k, hyk⟩
    have hyCH : y ∈ L ⊓ Subgroup.centralizer (H : Set G) :=
      ⟨hyL, Subgroup.centralizer_le hv hyC⟩
    rw [hCH] at hyCH
    obtain ⟨w, hw, rfl⟩ := hyCH
    have hwk : w ^ (2 ^ k) = 1 := hψΩinj (by rw [map_pow, hyk, map_one])
    rw [hJ'eq]
    exact ⟨w, OmPlusFrame.mem_layer_of_two_pow hQnd (by omega) hp hp2 hK1 htp ht2 hT hw hwk, rfl⟩
  have hq4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨⟨eSL⟩, hcenX, h7X, hpX⟩ := OmPlusFrame.layer_facts hQnd hdim8 hminus hp hp2 hpqF hF
    hq4 htp ht2
  obtain ⟨eJ⟩ : Nonempty (↥J' ≃*
      ↥(LargeEvenLayer (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))))) :=
    ⟨(MulEquiv.subgroupCongr hJ'eq).trans
      ((LargeEvenLayer (Subgroup.centralizer ({t} : Set ↥(orthDerived Q)))).equivMapOfInjective
        ψΩ hψΩinj).symm⟩
  refine ⟨?_, ?_, hrank inf_le_left, hrank inf_le_right, ?_, ?_, ?_, ?_⟩
  · rw [hJ'eq, hCH]
    exact isComponentOf_map_of_injective _ hψΩinj hcomp
  · apply le_antisymm
    · rintro z ⟨hzBs, hzC⟩
      set zB : ↥Bs := ⟨z, hzBs⟩ with hzB
      have hs : ∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))),
          ℓΩ zB * j = j * ℓΩ zB := by
        intro j hj
        have hjJ : ψΩ j ∈ J' := by
          rw [hJ'eq]
          exact ⟨j, hj, rfl⟩
        have h1 : ψΩ j * z = z * ψΩ j := Subgroup.mem_centralizer_iff.mp hzC _ hjJ
        have h2 : ψΩ (ℓΩ zB * j * (ℓΩ zB)⁻¹) = ψΩ j := by
          rw [← hcompat zB j]
          show z⁻¹ * ψΩ j * z = ψΩ j
          rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
        have h3 := hψΩinj h2
        calc ℓΩ zB * j = (ℓΩ zB * j * (ℓΩ zB)⁻¹) * ℓΩ zB := by group
          _ = j * ℓΩ zB := by rw [h3]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hcent (ℓΩ zB) ⟨zB, rfl⟩).mp hs)
      have hker' : ℓΩ (zB * (d ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, ← htdef, hk, mul_inv_cancel]
      have hmemk : ((zB * (d ^ k)⁻¹ : ↥Bs) : G) ∈ H :=
        (hmemH _).mpr ⟨hkr _ hker', hku _ hker'⟩
      have hdk : ((d ^ k : ↥Bs) : G) ∈ H := by
        rw [Subgroup.coe_zpow]
        exact zpow_mem hdH k
      have hz : z = ((zB * (d ^ k)⁻¹ : ↥Bs) : G) * ((d ^ k : ↥Bs) : G) := by
        simp [hzB]
      rw [hz]
      exact mul_mem hmemk hdk
    · intro z hz
      refine ⟨hHBs hz, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro j hj
      have hjC : j ∈ L ⊓ Subgroup.centralizer (H : Set G) := by
        rw [← hJ'] at hj
        exact largeEvenLayer_le _ hj
      exact ((Subgroup.mem_centralizer_iff.mp hjC.2) z hz).symm
  · rw [Nat.card_congr eJ.toEquiv]
    exact hpX
  · refine IOneOrthEnd.not_largeEvenSmall_of_seven_dvd ?_
    rw [Nat.card_congr eJ.toEquiv]
    exact h7X
  · have hlab : GGHasLabel ⟨.A, 4 - 1, f⟩ (↥J' ⧸ Subgroup.center ↥J') :=
      ggHasLabel_of_mulEquiv_specialLinear (X := G) (J := J') (K := GaloisField 2 f) (k := 4)
        (f := f) (by norm_num) hF (by simp) (by simp) (eSL.symm.trans eJ.symm)
    norm_num at hlab
    exact hlab
  · rw [eq_bot_iff]
    intro z hz
    have hz' : eJ z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply eJ.symm.injective
      rw [map_mul, map_mul, eJ.symm_apply_apply]
      exact hz (eJ.symm g)
    rw [hcenX, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← eJ.symm_apply_apply z, hz', map_one]

end Position

end CFSG.StandardType

end
