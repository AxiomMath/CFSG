module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L34FixedPoints
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenP
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08Use
public import CFSG.GroupTheory.ChiefFactors.OddElement
public import CFSG.GroupTheory.SteinbergCBFTHall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CentSectionConj
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sh
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
public import CFSG.Quasithin.H13.L32A520f
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem not_centralizes_pCoreOf_of_orderOf_three (D : Data G) {z : G} (hzM : z ∈ D.M)
    (hz3 : orderOf z = 3) :
    ∃ q ∈ pCoreOf 2 D.M, z * q * z⁻¹ * q⁻¹ ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hzC : z ∈ centralizer (pCoreOf 2 D.M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : z * q * z⁻¹ = q := by
      have := hcon q hq
      rwa [mul_inv_eq_one] at this
    calc q * z = (z * q * z⁻¹) * z := by rw [h1]
      _ = z * q := by group
  have hchar : D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) ≤ pCoreOf 2 D.M :=
    D.standing.charTwo D.M D.maxLocal.1
  have hzQ : z ∈ pCoreOf 2 D.M := hchar (Subgroup.mem_inf.mpr ⟨hzM, hzC⟩)
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).exists_orderOf_eq_pow
    (⟨z, hzQ⟩ : ↥(pCoreOf 2 D.M))
  rw [Subgroup.orderOf_mk, hz3] at hk
  have hdvd : 3 ∣ 2 ^ k := hk ▸ dvd_rfl
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32


theorem exists_bar2_rep {N R₁ R₂ L : Subgroup G} [(R₂.subgroupOf R₁).Normal]
    [IsElementaryAbelian 2 (R₁ ⧸ R₂.subgroupOf R₁)]
    (hch : CFSG.ABGLocalTools.IsChiefFactorUnder 2 N R₁ R₂)
    (hL : L ≤ N) (hO2L : pCoreOf 2 L ≤ N)
    (htriv : ∀ (x : G) (hx : x ∈ pCoreOf 2 L),
      CFSG.ABGLocalTools.chiefRep (p := 2) hch.2.1 hch.2.2.1 (⟨x, hO2L hx⟩ : ↥N) = 1) :
    ∃ ρ : Representation (ZMod 2) (Bar2 L)
        (Additive (R₁ ⧸ R₂.subgroupOf R₁)),
      ∀ (l : ↥L),
        ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) =
          (Units.coeHom _) (CFSG.ABGLocalTools.chiefRep (p := 2) hch.2.1 hch.2.2.1
            (⟨l.1, hL l.2⟩ : ↥N)) := by
  let ρN := CFSG.ABGLocalTools.chiefRep (p := 2) hch.2.1 hch.2.2.1
  let ρL : ↥L →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (R₁ ⧸ R₂.subgroupOf R₁)) :=
    ρN.comp (Subgroup.inclusion hL)
  have hker : CFSG.pCore 2 ↥L ≤ ρL.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxG : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩
    have h1 : ρL x = 1 := by
      change ρN ⟨(x : G), hL x.2⟩ = 1
      exact htriv (x : G) hxG
    exact h1
  let ρbar : Bar2 L →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (R₁ ⧸ R₂.subgroupOf R₁)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) ρL hker
  refine ⟨(Units.coeHom _).comp ρbar, ?_⟩
  intro l
  change Units.coeHom _ (ρbar (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l)) =
    Units.coeHom _ (ρN ⟨l.1, hL l.2⟩)
  rw [show ρbar (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) = ρL l from
    QuotientGroup.lift_mk' _ _ _]
  rfl

theorem four_le_card_pCoreOf_inf_centralizer_mul (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    {z b : G} (hzL : z ∈ L) (hz3 : orderOf z = 3)
    (hbCL : b ∈ F08.CentOverO2 D.M L) (hb3 : orderOf b = 3)
    (hzb3 : orderOf (z * b) = 3) (hK : K_L34Fix) :
    4 ≤ Nat.card ↥(pCoreOf 2 D.M ⊓ centralizer ({z * b} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup G := pCoreOf 2 D.M
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hQM : Q ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hMQ : D.M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hLQ : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hbM : b ∈ D.M := (mem_centOverO2_iff.mp hbCL).1
  let S : Set G := (Q : Set G) ∪ (L : Set G) ∪ ({b} : Set G)
  let N : Subgroup G := Subgroup.closure S
  have hQN : Q ≤ N := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl (Or.inl hx))
  have hLN : L ≤ N := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl (Or.inr hx))
  have hbN : b ∈ N := Subgroup.subset_closure (Or.inr (by simp))
  have hNM : N ≤ D.M := by
    refine (Subgroup.closure_le (D.M)).mpr ?_
    rintro x ((hxQ | hxL) | hxb)
    · exact hQM hxQ
    · exact hLQ hxL
    · rw [Set.mem_singleton_iff] at hxb
      subst hxb
      exact hbM
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := hNM.trans hMQ
  have hzM : z ∈ D.M := hLQ hzL
  have hzN : z ∈ N := hLN hzL
  have hzNot : ∃ q ∈ Q, z * q * z⁻¹ * q⁻¹ ≠ 1 :=
    not_centralizes_pCoreOf_of_orderOf_three D hzM hz3
  have hzOdd : Odd (orderOf z) := by rw [hz3]; decide
  obtain ⟨R₁, R₂, hlt, hR₁Q, hN₁, hN₂, hR₁₂, hchief, hzact⟩ :=
    CFSG.GroupTheory.exists_chief_factor_of_odd (N := N) (R := Q) hQ2 hQN hNQ hzN hzOdd hzNot
  have hR₁2 : IsPGroup 2 R₁ := hQ2.to_le hR₁Q
  have hR₁N : R₁ ≤ N := hR₁Q.trans hQN
  haveI hHn : (R₂.subgroupOf R₁).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hR₁₂
  have hch2 : CFSG.Quasithin.IsTwoChiefFactor N R₁ R₂ := by
    refine ⟨hlt, hR₁N, hN₁, hN₂, ?_, ?_⟩
    · intro C hR₂C hCR₁ hNC
      rcases hchief C hR₂C.le hCR₁.le hNC with h | h
      · exact hR₂C.ne' h
      · exact hCR₁.ne h
    · intro a ha
      obtain ⟨k, hk⟩ := hR₁2.exists_orderOf_eq_pow (⟨a, ha⟩ : ↥R₁)
      have h1 : (⟨a, ha⟩ : ↥R₁) ^ orderOf (⟨a, ha⟩ : ↥R₁) = 1 := pow_orderOf_eq_one _
      have h2 : a ^ orderOf (⟨a, ha⟩ : ↥R₁) = 1 := by
        simpa using congrArg Subtype.val h1
      exact ⟨k, by rw [← hk, h2]; exact R₂.one_mem⟩
  have hch : CFSG.ABGLocalTools.IsChiefFactorUnder 2 N R₁ R₂ := by
    refine ⟨hlt, hN₁, hN₂, ?_, ?_, ?_, hchief⟩
    · intro x hx y hy
      exact (Subgroup.mem_normalizer_iff.mp (hR₁₂ hx) y).mp hy
    · intro x hx y hy
      exact CFSG.GroupTheory.commutator_mem_of_chief (N := N) (P := R₁) hR₁2 hR₁N hN₁
        hR₁2 hlt hN₁ hN₂ hR₁₂ hchief x hx y hy
    · intro x hx
      rw [pow_two]
      exact CFSG.Quasithin.H13.S3320.sq_mem_of_chief hch2 x hx
  haveI : IsElementaryAbelian 2 (R₁ ⧸ R₂.subgroupOf R₁) := hch.isElementaryAbelian
  have hQtriv : ∀ (q : G) (hq : q ∈ Q),
      CFSG.ABGLocalTools.chiefRep (p := 2) hch.2.1 hch.2.2.1 (⟨q, hQN hq⟩ : ↥N) = 1 := by
    intro q hq
    rw [CFSG.ABGLocalTools.chiefRep_eq_one_iff]
    intro w hw
    have h := CFSG.GroupTheory.commutator_mem_of_chief (N := N) (P := Q) hQ2 hQN hNQ
      hR₁2 hlt hN₁ hN₂ hR₁₂ hchief q hq w hw
    have h' : w * q * w⁻¹ * q⁻¹ ∈ R₂ := by
      convert R₂.inv_mem h using 1
      group
    simpa [commutatorElement_def] using h'
  have hO2LQ : pCoreOf 2 L ≤ Q := by
    have hLM : L ≤ D.M := hLQ
    have hnormL : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLQ).mp (ctx.hyp54.2 L ctx.memC).1
    have hchar : Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 L : Set G) := by
      simpa [pCoreOf] using
        CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (H := L) (K := CFSG.pCore 2 ↥L)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer
      (N := pCoreOf 2 L) (H := D.M) (r := 2) ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLQ)
      (hnormL.trans hchar) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hO2LN : pCoreOf 2 L ≤ N := hO2LQ.trans hQN
  have htrivL : ∀ (x : G) (hx : x ∈ pCoreOf 2 L),
      CFSG.ABGLocalTools.chiefRep (p := 2) hch.2.1 hch.2.2.1 (⟨x, hO2LN hx⟩ : ↥N) = 1 := by
    intro x hx
    exact hQtriv x (hO2LQ hx)
  obtain ⟨ρ, hρ⟩ := exists_bar2_rep hch hLN hO2LN htrivL
  let ρN := CFSG.ABGLocalTools.chiefRep (p := 2) hch.2.1 hch.2.2.1
  let V := Additive (R₁ ⧸ R₂.subgroupOf R₁)
  let ρE : ↥N →* Module.End (ZMod 2) V :=
    (Units.coeHom (V →ₗ[ZMod 2] V)).comp ρN
  let β : V →ₗ[ZMod 2] V := (ρN ⟨b, hbN⟩).val
  have hb3' : b ^ 3 = 1 := by
    rw [← hb3]
    exact pow_orderOf_eq_one b
  have hβ3 : β ^ 3 = 1 := by
    have hbN3 : (⟨b, hbN⟩ : ↥N) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hb3'
    have hGL : (ρN ⟨b, hbN⟩) ^ 3 = 1 := by
      rw [← map_pow, hbN3, map_one]
    change ((ρN ⟨b, hbN⟩).val : Module.End (ZMod 2) V) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, hGL, Units.val_one]
  have hcomm : ∀ x : Bar2 L, ρ x ∘ₗ β = β ∘ₗ ρ x := by
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
    have hbcomm : b * (l : G) * b⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L :=
      (mem_centOverO2_iff.mp hbCL).2 l l.2
    have h1 : ρN ⟨b * (l : G) * b⁻¹ * (l : G)⁻¹, hO2LN hbcomm⟩ = 1 :=
      htrivL _ hbcomm
    have hGLcomm : ρN ⟨b, hbN⟩ * ρN ⟨l, hLN l.2⟩ =
        ρN ⟨l, hLN l.2⟩ * ρN ⟨b, hbN⟩ := by
      apply mul_inv_eq_one.mp
      have hprod : ρN (⟨b, hbN⟩ * ⟨l, hLN l.2⟩ * ⟨b, hbN⟩⁻¹ *
          ⟨l, hLN l.2⟩⁻¹) =
          ρN ⟨b, hbN⟩ * ρN ⟨l, hLN l.2⟩ * (ρN ⟨b, hbN⟩)⁻¹ *
            (ρN ⟨l, hLN l.2⟩)⁻¹ := by
        simp only [map_mul, map_inv]
      have h2 : ρN ⟨b, hbN⟩ * ρN ⟨l, hLN l.2⟩ * (ρN ⟨b, hbN⟩)⁻¹ *
          (ρN ⟨l, hLN l.2⟩)⁻¹ = 1 := by
        rw [← hprod]
        convert h1 using 1
      exact h2
    have hEnd : ((ρN ⟨b, hbN⟩ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V) * ((ρN ⟨l, hLN l.2⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) =
        ((ρN ⟨l, hLN l.2⟩ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V) * ((ρN ⟨b, hbN⟩ :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) := by
      simpa using congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) V =>
        (u : Module.End (ZMod 2) V)) hGLcomm
    rw [hρ l]
    ext v
    have h := congrArg (fun f : Module.End (ZMod 2) V => f v) hEnd
    simpa [Module.End.mul_apply] using h.symm
  have hIrr : ∀ W : Submodule (ZMod 2) V,
      (∀ x : Bar2 L, W.map (ρ x) ≤ W) → W.map β ≤ W → W = ⊥ ∨ W = ⊤ := by
    intro W hWρ hWβ
    apply CFSG.ABGLocalTools.chiefRep_irreducible hch W
    intro n v hv
    have hinv : ∀ x : ↥N, W.map (ρE x) ≤ W → W.map (ρE x⁻¹) ≤ W := by
      intro x hx
      let e : V ≃ₗ[ZMod 2] V :=
        { toFun := ρE x
          invFun := ρE x⁻¹
          left_inv := by
            intro v
            have h : (ρE x * ρE x⁻¹) = 1 := by
              rw [← map_mul, mul_inv_cancel, map_one]
            simpa [Module.End.mul_apply] using congrArg (fun f : Module.End (ZMod 2) V => f v) h
          right_inv := by
            intro v
            have h : (ρE x⁻¹ * ρE x) = 1 := by
              rw [← map_mul, inv_mul_cancel, map_one]
            simpa [Module.End.mul_apply] using congrArg (fun f : Module.End (ZMod 2) V => f v) h
          map_add' := map_add _
          map_smul' := map_smul _ }
      have hxmap : W.map (e : V →ₗ[ZMod 2] V) ≤ W := hx
      have hxeq : W.map (e : V →ₗ[ZMod 2] V) = W := by
        apply Submodule.eq_of_le_of_finrank_eq hxmap
        rw [LinearEquiv.finrank_map_eq]
      have hcomp : ((e.symm : V →ₗ[ZMod 2] V).comp (e : V →ₗ[ZMod 2] V)) = 1 := by
        ext v
        exact e.symm_apply_apply v
      have hxeq2 : (W.map (e : V →ₗ[ZMod 2] V)).map (e.symm : V →ₗ[ZMod 2] V) = W := by
        calc (W.map (e : V →ₗ[ZMod 2] V)).map (e.symm : V →ₗ[ZMod 2] V)
            = W.map ((e.symm : V →ₗ[ZMod 2] V).comp (e : V →ₗ[ZMod 2] V)) := by
                exact (Submodule.map_comp (e : V →ₗ[ZMod 2] V) (e.symm : V →ₗ[ZMod 2] V) W).symm
          _ = W.map 1 := by rw [hcomp]
          _ = W := by
                change W.map (LinearMap.id : V →ₗ[ZMod 2] V) = W
                rw [Submodule.map_id]
      have hEq : W.map (e.symm : V →ₗ[ZMod 2] V) = W := by
        calc W.map (e.symm : V →ₗ[ZMod 2] V)
            = (W.map (e : V →ₗ[ZMod 2] V)).map (e.symm : V →ₗ[ZMod 2] V) := by rw [hxeq]
          _ = W := hxeq2
      exact le_of_eq hEq
    have hmapone : W.map (1 : V →ₗ[ZMod 2] V) ≤ W := by
      change W.map (LinearMap.id : V →ₗ[ZMod 2] V) ≤ W
      rw [Submodule.map_id]
    have hstep : ∀ x (hx : x ∈ S), W.map (ρE ⟨x, Subgroup.subset_closure hx⟩) ≤ W := by
      intro x hx
      have hx0 : x ∈ S := hx
      rcases hx with (hxQ | hxL) | hxb
      · have hxQ' : x ∈ Q := hxQ
        have hx1 : ρN ⟨x, hQN hxQ'⟩ = 1 := hQtriv x hxQ'
        have hx1' : ρE ⟨x, Subgroup.subset_closure (Or.inl (Or.inl hxQ'))⟩ = 1 := by
          simpa [ρE, hx1]
        rw [hx1']
        exact hmapone
      · have hxL' : x ∈ L := hxL
        have hρx : ρE ⟨x, Subgroup.subset_closure (Or.inl (Or.inr hxL'))⟩ =
            ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL'⟩) := by
          simpa [ρE] using (hρ ⟨x, hxL'⟩).symm
        rw [hρx]
        exact hWρ _
      · have hxb' : x = b := by simpa using hxb
        have hxsub : (⟨x, Subgroup.subset_closure hx0⟩ : ↥N) = ⟨b, hbN⟩ :=
          Subtype.ext hxb'
        rw [hxsub]
        exact hWβ
    have hn : (n : G) ∈ Subgroup.closure S := n.2
    have hmap : W.map (ρE n) ≤ W := by
      change W.map (ρE ⟨(n : G), hn⟩) ≤ W
      refine Subgroup.closure_induction (p := fun x hx => W.map (ρE ⟨x, hx⟩) ≤ W) ?_ ?_ ?_ ?_ hn
      · intro x hx
        exact hstep x hx
      · have h1 : ρE (⟨1, N.one_mem⟩ : ↥N) = 1 := by
          rw [show (⟨1, N.one_mem⟩ : ↥N) = 1 from rfl]
          exact map_one ρE
        rw [h1]
        exact hmapone
      · intro x y hx hy ihx ihy
        have h1 : W.map (ρE (⟨x, hx⟩ * ⟨y, hy⟩ : ↥N)) =
            (W.map (ρE ⟨y, hy⟩)).map (ρE ⟨x, hx⟩) := by
          rw [map_mul]
          exact Submodule.map_comp _ _ _
        have h2 : W.map (ρE ⟨x * y, Subgroup.mul_mem (Subgroup.closure S) hx hy⟩) =
            (W.map (ρE ⟨y, hy⟩)).map (ρE ⟨x, hx⟩) := by
          simpa using h1
        rw [h2]
        exact (Submodule.map_mono ihy).trans ihx
      · intro x hx ih
        exact hinv ⟨x, hx⟩ ih
    exact hmap (Submodule.mem_map_of_mem hv)
  have hnontriv : ∃ (x : Bar2 L) (v : V), ρ x v ≠ v := by
    obtain ⟨r, hrR, hract⟩ := hzact
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩,
      Additive.ofMul (QuotientGroup.mk' (R₂.subgroupOf R₁) ⟨r, hrR⟩), ?_⟩
    intro hfix
    apply hract
    have hzE : ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) = ρE ⟨z, hzN⟩ := by
      simpa [ρE] using hρ ⟨z, hzL⟩
    rw [hzE] at hfix
    have happly := CFSG.ABGLocalTools.chiefRep_apply_mk (p := 2) hN₁ hN₂
      (⟨z, hzN⟩ : ↥N) (⟨r, hrR⟩ : ↥R₁)
    have hq : (QuotientGroup.mk' (R₂.subgroupOf R₁)
        (CFSG.ABGLocalTools.chiefConj hN₁ ⟨z, hzN⟩ ⟨r, hrR⟩ : ↥R₁)) =
        QuotientGroup.mk' (R₂.subgroupOf R₁) ⟨r, hrR⟩ := by
      apply Additive.ofMul.injective
      rw [← hfix]
      exact happly
    have hmem : (CFSG.ABGLocalTools.chiefConj hN₁ ⟨z, hzN⟩ ⟨r, hrR⟩ : ↥R₁) /
        (⟨r, hrR⟩ : ↥R₁) ∈ R₂.subgroupOf R₁ :=
      (QuotientGroup.eq_iff_div_mem).mp hq
    rw [Subgroup.mem_subgroupOf] at hmem
    have hcoe := CFSG.ABGLocalTools.chiefConj_apply_coe hN₁ ⟨z, hzN⟩ ⟨r, hrR⟩
    rw [div_eq_mul_inv] at hmem
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at hmem
    rw [hcoe] at hmem
    simpa using hmem
  have haz3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) = 3 := by
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) ∣ 3 := by
      rw [← hz3]
      simpa [Subgroup.orderOf_coe] using
        orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨z, hzL⟩
    have hne : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) ≠ 1 := by
      intro h1
      have hz1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩ = 1 := by
        rw [← orderOf_eq_one_iff]
        exact h1
      have hzO2 : z ∈ pCoreOf 2 L := by
        have hmem : (⟨z, hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
          (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) (x := ⟨z, hzL⟩)).mp hz1
        exact Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, hmem, rfl⟩
      have hz2 : orderOf z ∣ Nat.card (pCoreOf 2 L) :=
        Subgroup.orderOf_dvd_natCard (pCoreOf 2 L) hzO2
      obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      have h3dvd : 3 ∣ 2 ^ k := by
        rw [hk] at hz2
        simpa [hz3] using hz2
      have h32 : 3 = 2 := Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two h3dvd
      omega
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne
    · exact h3
  have hfixV := hK (Bar2 L) ctx.shapeL V ρ β hcomm hβ3 hIrr hnontriv
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) haz3
  let x : G := z * b
  have hxN : x ∈ N := mul_mem hzN hbN
  have hxord : orderOf x = 3 := hzb3
  let A : Subgroup G := Subgroup.zpowers x
  have hAx : A ≤ Subgroup.normalizer (R₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hN₁ hxN)
  have hAx₂ : A ≤ Subgroup.normalizer (R₂ : Set G) :=
    Subgroup.zpowers_le.mpr (hN₂ hxN)
  let Nsub : Subgroup ↥R₁ := R₂.subgroupOf R₁
  letI : MulDistribMulAction ↥A ↥R₁ := CFSG.Walter.JT.conjAct A R₁ hAx
  have hInv : CFSG.IsInvariant ↥A ↥R₁ Nsub := by
    refine ⟨fun a w => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (w : G) ∈ R₂ ↔ (a : G) * (w : G) * (a : G)⁻¹ ∈ R₂
    exact Subgroup.mem_normalizer_iff.mp (hAx₂ a.2) (w : G)
  letI : CFSG.IsInvariant ↥A ↥R₁ Nsub := hInv
  letI : MulDistribMulAction ↥A (↥R₁ ⧸ Nsub) :=
    CFSG.quotientMulDistribMulAction (A := ↥A) (G := ↥R₁) Nsub hInv
  have hsolvR₁ : Group.IsSolvable ↥R₁ :=
    CFSG.GorensteinWalter.isSolvable_of_isPGroup hR₁2
  have hcopA : Nat.Coprime (Nat.card ↥A) (Nat.card ↥R₁) := by
    have hAcard : Nat.card ↥A = 3 := by
      rw [Nat.card_zpowers, hxord]
    obtain ⟨k, hk⟩ := hR₁2.exists_card_eq
    rw [hAcard, hk]
    exact (by norm_num : Nat.Coprime 3 2).pow_right k
  have hfac := CFSG.Wielandt.fixedPointSubgroup_card_eq_mul_quotient_action
    (A := ↥A) (M := ↥R₁) (N := Nsub) hInv hsolvR₁ hcopA
  have hxrep : ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) ∘ₗ β =
      ρE ⟨x, hxN⟩ := by
    have hρz : ρ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨z, hzL⟩) =
        (ρN ⟨z, hzN⟩).val := by
      simpa [ρE] using hρ ⟨z, hzL⟩
    have hβ : β = (ρN ⟨b, hbN⟩).val := rfl
    rw [hρz, hβ]
    change ((ρN ⟨z, hzN⟩).val * (ρN ⟨b, hbN⟩).val) = (ρN ⟨x, hxN⟩).val
    rw [← Units.val_mul, ← map_mul]
    congr 1
  have hfixV' : 4 ≤ Nat.card (LinearMap.ker (ρE ⟨x, hxN⟩ - 1)) := by
    rw [← hxrep]
    exact hfixV
  have hmem_fix (q : ↥R₁ ⧸ Nsub) :
      q ∈ CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub) ↔
        (⟨x, Subgroup.mem_zpowers x⟩ : A) • q = q := by
    constructor
    · intro h
      exact h ⟨x, Subgroup.mem_zpowers x⟩
    · intro h a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have ha : a = (⟨x, Subgroup.mem_zpowers x⟩ : A) ^ k := by
        apply Subtype.ext
        simpa [Subgroup.coe_zpow] using hk.symm
      rw [ha]
      exact MulAction.mem_fixedBy_zpow (α := ↥R₁ ⧸ Nsub) h k
  have hconj_mem (w : ↥R₁) : x * (w : G) * x⁻¹ ∈ R₁ :=
    (Subgroup.mem_normalizer_iff.mp (hN₁ hxN) (w : G)).mp w.2
  have hsmul_mk (w : ↥R₁) :
      (⟨x, Subgroup.mem_zpowers x⟩ : A) • (QuotientGroup.mk' Nsub w) =
        QuotientGroup.mk' Nsub (⟨x * (w : G) * x⁻¹, hconj_mem w⟩ : ↥R₁) := by
    change (⟨x, Subgroup.mem_zpowers x⟩ : A) • (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨x * (w : G) * x⁻¹, hconj_mem w⟩ : ↥R₁)
    rw [MulAction.Quotient.smul_mk]
    rfl
  have hker_iff (w : ↥R₁) :
      Additive.ofMul (QuotientGroup.mk' Nsub w) ∈
          LinearMap.ker (ρE ⟨x, hxN⟩ - 1) ↔
        QuotientGroup.mk' Nsub (⟨x * (w : G) * x⁻¹, hconj_mem w⟩ : ↥R₁) =
          QuotientGroup.mk' Nsub w := by
    have happly : ρE ⟨x, hxN⟩ (Additive.ofMul (QuotientGroup.mk' Nsub w)) =
        Additive.ofMul (QuotientGroup.mk' Nsub
          (⟨x * (w : G) * x⁻¹, hconj_mem w⟩ : ↥R₁)) := by
      have hc := CFSG.ABGLocalTools.chiefRep_apply_mk (p := 2) hN₁ hN₂
        (⟨x, hxN⟩ : ↥N) w
      have hc' : ρE ⟨x, hxN⟩ (Additive.ofMul (QuotientGroup.mk' Nsub w)) =
          Additive.ofMul (QuotientGroup.mk' Nsub
            (((CFSG.ABGLocalTools.chiefConj hN₁) ⟨x, hxN⟩) w)) := by
        simpa [ρE, ρN] using hc
      rw [hc']
      apply congrArg Additive.ofMul
      apply congrArg (QuotientGroup.mk' Nsub)
      exact Subtype.ext (CFSG.ABGLocalTools.chiefConj_apply_coe hN₁ ⟨x, hxN⟩ w)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change ρE ⟨x, hxN⟩ (Additive.ofMul (QuotientGroup.mk' Nsub w)) =
      Additive.ofMul (QuotientGroup.mk' Nsub w) ↔
        (QuotientGroup.mk' Nsub) (⟨x * (w : G) * x⁻¹, hconj_mem w⟩ : ↥R₁) =
          QuotientGroup.mk' Nsub w
    constructor
    · intro h
      have h' : Additive.ofMul (QuotientGroup.mk' Nsub
          (⟨x * (w : G) * x⁻¹, hconj_mem w⟩ : ↥R₁)) =
          Additive.ofMul (QuotientGroup.mk' Nsub w) := by
        rw [← happly]
        exact h
      exact Additive.ofMul.injective h'
    · intro h
      rw [happly]
      exact congrArg Additive.ofMul h
  have hmem_iff (q : ↥R₁ ⧸ Nsub) :
      q ∈ CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub) ↔
        Additive.ofMul q ∈ LinearMap.ker (ρE ⟨x, hxN⟩ - 1) := by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Nsub q
    rw [hmem_fix, hsmul_mk]
    exact (hker_iff w).symm
  have hcardQ : Nat.card (CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub)) =
      Nat.card (LinearMap.ker (ρE ⟨x, hxN⟩ - 1)) :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul hmem_iff)
  have h4quot : 4 ≤ Nat.card (CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub)) := by
    rw [hcardQ]
    exact hfixV'
  have h4R₁ : 4 ≤ Nat.card (CFSG.fixedPointSubgroup ↥A ↥R₁) := by
    have hpos : 0 < Nat.card (CFSG.fixedPointSubgroup ↥A ↥Nsub) := Nat.card_pos
    calc 4 ≤ Nat.card (CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub)) := h4quot
      _ = Nat.card (CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub)) * 1 := (Nat.mul_one _).symm
      _ ≤ Nat.card (CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub)) *
            Nat.card (CFSG.fixedPointSubgroup ↥A ↥Nsub) :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hpos.ne')
      _ = Nat.card (CFSG.fixedPointSubgroup ↥A ↥Nsub) *
            Nat.card (CFSG.fixedPointSubgroup ↥A (↥R₁ ⧸ Nsub)) := Nat.mul_comm _ _
      _ = Nat.card (CFSG.fixedPointSubgroup ↥A ↥R₁) := hfac.symm
  have hcardR : Nat.card (CFSG.fixedPointSubgroup ↥A ↥R₁) =
      Nat.card ↥(R₁ ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [CFSG.Walter.JT.card_fixedPointSubgroup_conjAct_top A R₁ hAx]
    rw [show Subgroup.centralizer (A : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) from rfl]
    rw [CFSG.Walter.JT.inf_centralizer_zpowers]
  have h4R : 4 ≤ Nat.card ↥(R₁ ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [← hcardR]
    exact h4R₁
  have hsub : R₁ ⊓ Subgroup.centralizer ({x} : Set G) ≤
      pCoreOf 2 D.M ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ hR₁Q
  have hsubcard : Nat.card ↥(R₁ ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      Nat.card ↥(pCoreOf 2 D.M ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hsub)
      (Subgroup.inclusion_injective hsub)
  exact h4R.trans hsubcard





theorem exists_sylow_three_le_centralizer (D : Data G) {p : ℕ} (hp : Hyp1754 D p)
    {L : Subgroup G} (hL : L ∈ calC D.M)
    {Y : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hYcard : Nat.card Y = r)
    (hYM : Y ≤ D.M)
    (hYcent : barImage D.M Y ≤
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M))) :
    ∃ A' : Subgroup G, A' ≤ L ⊓ Subgroup.centralizer (Y : Set G) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 A' L := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hLnorm : (L.subgroupOf D.M).Normal := (hp.2 L hL).1
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hcentral : ∀ a ∈ Y, CentralizesBar a L := by
    intro a ha
    have haM : a ∈ D.M := hYM ha
    refine ⟨hMnorm haM, ?_⟩
    intro l hl
    have hlM : l ∈ D.M := hLM hl
    have hconjL : a * l * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hMnorm haM) l).mp hl
    have hcommL : a * l * a⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem hconjL (L.inv_mem hl)
    have hmemM : a * l * a⁻¹ * l⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem haM hlM) (D.M.inv_mem haM))
        (D.M.inv_mem hlM)
    have hcommBar : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨l, hlM⟩) =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨l, hlM⟩) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩) := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩) ∈
          barImage D.M Y := Subgroup.mem_map_of_mem _ ha
      have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨l, hlM⟩) ∈
          barImage D.M L := Subgroup.mem_map_of_mem _ hl
      exact (Subgroup.mem_centralizer_iff.mp (hYcent h1) _ h2).symm
    have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
        ⟨a * l * a⁻¹ * l⁻¹, hmemM⟩ = 1 := by
      have hmap : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
          ⟨a * l * a⁻¹ * l⁻¹, hmemM⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨l, hlM⟩) *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a, haM⟩)⁻¹ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨l, hlM⟩)⁻¹ := by
        rw [show (⟨a * l * a⁻¹ * l⁻¹, hmemM⟩ : ↥D.M) =
          ⟨a, haM⟩ * ⟨l, hlM⟩ * ⟨a, haM⟩⁻¹ * ⟨l, hlM⟩⁻¹ from rfl]
        simp only [map_mul, map_inv]
      rw [hmap, hcommBar]
      group
    have hO2M : (⟨a * l * a⁻¹ * l⁻¹, hmemM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M :=
      (QuotientGroup.eq_one_iff _).mp hker
    have hO2M' : a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 D.M :=
      Subgroup.mem_map_of_mem D.M.subtype hO2M
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLM ⟨hcommL, hO2M'⟩
  have hsup : (L ⊓ Subgroup.centralizer (Y : Set G)) ⊔ pCoreOf 2 L = L :=
    uc22p21d_sup_pCore_eq hr hr2 hYcard hcentral
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A', hA'sylC⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf (G := G) 3
      (L ⊓ Subgroup.centralizer (Y : Set G))
  refine ⟨A', hA'sylC.le, ?_⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hA'sylC ⊢
  obtain ⟨hA'C, hA'3, hA'notC⟩ := hA'sylC
  refine ⟨hA'C.trans inf_le_left, hA'3, ?_⟩
  set C : Subgroup G := L ⊓ Subgroup.centralizer (Y : Set G) with hCdef
  have hCnorm : C ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    rw [hCdef]
    exact inf_le_left.trans
      (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hCrel : C.relIndex L ∣ Nat.card (pCoreOf 2 L) := by
    calc C.relIndex L = C.relIndex (C ⊔ pCoreOf 2 L) := by rw [hsup]
      _ = C.relIndex (pCoreOf 2 L) :=
        (CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hCnorm).symm
      _ ∣ Nat.card (pCoreOf 2 L) := Subgroup.relIndex_dvd_card _ _
  have hO2p : IsPGroup 2 (pCoreOf 2 L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  obtain ⟨n, hn⟩ := hO2p.exists_card_eq
  rw [hn] at hCrel
  have h3C : ¬ 3 ∣ C.relIndex L := by
    intro h3
    have h32 : 3 ∣ 2 ^ n := h3.trans hCrel
    have h32' : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h32
    norm_num at h32'
  have hmul : A'.relIndex C * C.relIndex L = A'.relIndex L :=
    Subgroup.relIndex_mul_relIndex A' C L hA'C inf_le_left
  intro h3L
  rw [← hmul] at h3L
  rcases Nat.prime_three.dvd_mul.mp h3L with h | h
  · exact hA'notC h
  · exact h3C h

theorem three_dvd_card_bar2_of_mem_calC {D : Data G} {p : ℕ} (hp : Hyp1754 D p)
    (hThin : PartTwo.ThinList13) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKnot : ¬ ∃ n : ℕ, Odd n ∧ (IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n)) :
    3 ∣ Nat.card (Bar2 K) := by
  rcases (hp.2 K hK).2 with hthin | ⟨n, hU3⟩ | hL3
  · rcases (PartTwo.s13_list_bar hThin D hK hthin).2 with
      ⟨a, hL2⟩ | ⟨q, hq, hq2, hL2odd⟩ | ⟨a, hSz⟩ | hJ1
    · exact three_dvd_card_of_isL2 hL2
    · exact UC22.three_dvd_card_of_isL2Odd
        (by have := PartTwo.s13_five_le_of_isL2Odd hL2odd; omega) hL2odd
    · exact absurd ⟨a, (PartTwo.s13_odd_three_le_of_isSz hSz).1, Or.inr hSz⟩ hKnot
    · exact UC22.three_dvd_card_of_isJ1 hJ1
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel_PSU3 hU3
  · rw [card_bar_of_isL3 hL3]
    norm_num

theorem normalizer_zpowers_le_of_mem_centralizer_sylow {D : Data G}
    {A : Subgroup G} {z : G}
    (h63 : UC6.R6_3 D) (hAM : A ≤ D.M)
    (hAea : IsElemAbelian 3 A) (hAcard : Nat.card A = 9)
    (hΓA : rankThreeGamma 1 3 A ≤ D.M)
    (hzA : z ∈ A) (hz3 : orderOf z = 3) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ D.M := by
  have hAU : UniqueMax D.M A :=
    h63 3 Nat.prime_three (by norm_num) A hAM hAea hAcard hΓA
  have hEaZ : IsElemAbelian 3 (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers (by simpa [hz3] using pow_orderOf_eq_one z)
  have hzrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers z) := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
      (le_refl (Subgroup.zpowers z)) hEaZ (k := 1)
      (by rw [Nat.card_zpowers, hz3]; norm_num)
    simpa using h
  exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (Subgroup.zpowers_le.mpr hzA) hzrank).trans hΓA

theorem normalizer_elemAbelian_centralizing_sylow_le {D : Data G}
    {A P E : Subgroup G} {z : G}
    (h63 : UC6.R6_3 D) (hAM : A ≤ D.M)
    (hAea : IsElemAbelian 3 A) (hAcard : Nat.card A = 9)
    (hΓA : rankThreeGamma 1 3 A ≤ D.M)
    (hAP : A ≤ P) (hPM : P ≤ D.M)
    (hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (hzE : z ∈ E)
    (hz_norm : Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ D.M) :
    Subgroup.normalizer (E : Set G) ≤ D.M := by
  have hAU : UniqueMax D.M A :=
    h63 3 Nat.prime_three (by norm_num) A hAM hAea hAcard hΓA
  have hNP : Subgroup.normalizer (P : Set G) ≤ D.M :=
    TwelveSeven.normalizer_le_of_uniqueMax_le D hAU hAP hPM
  have hPp : IsPGroup 3 P := hPsyl.isPGroup
  have hC_le_M : Subgroup.centralizer (E : Set G) ≤ D.M := by
    have hsub : (Subgroup.zpowers z : Set G) ⊆ (E : Set G) := by
      intro x hx
      exact Subgroup.zpowers_le.mpr hzE hx
    exact (Subgroup.centralizer_le hsub).trans
      ((Subgroup.centralizer_le_normalizer (Subgroup.zpowers z : Set G)).trans hz_norm)
  intro x hx
  let H := Subgroup.normalizer (E : Set G)
  let C := Subgroup.centralizer (E : Set G)
  have hCsubH : (C.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G)
  have hCH : C ≤ H := Subgroup.centralizer_le_normalizer _
  have hHnormC : H ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mp hCsubH
  have hPC : P ≤ C := (Subgroup.le_centralizer_iff).mpr hEcentP
  have h3notrel : ¬ 3 ∣ P.relIndex C := by
    intro hd
    have hmul := Subgroup.relIndex_mul_relIndex P C D.M hPC hC_le_M
    have hdM : 3 ∣ P.relIndex D.M := by
      rw [← hmul]
      exact dvd_mul_of_dvd_left hd _
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hPsyl).2.2 hdM
  have hPCsyl : CFSG.ABGLocalTools.IsSylowOf 3 P C :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPC, hPp, h3notrel⟩
  have hPCfusion : CFSG.Open.fusionIsSylowIn 3 P C :=
    ⟨hPC, hPp, fun Q hQC hQ hPQ => hPCsyl.eq_of_le hPQ hQC hQ⟩
  obtain ⟨n, hn, hxn⟩ :=
    CFSG.Quasithin.H13.L32A.exists_mul_mem_normalizer (p := 3) hPCfusion (hHnormC hx)
  have hnM : n ∈ D.M := hC_le_M hn
  have hxnM : n⁻¹ * x ∈ D.M := hNP hxn
  rw [← show n * (n⁻¹ * x) = x by group]
  exact D.M.mul_mem hnM hxnM

theorem normalizer_zpowers_le_of_mem_centOverO2 {D : Data G}
    {V₀ V L A : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (h869 : F08.R869 D)
    (hAL : A ≤ L) (hAea : IsElemAbelian 3 A) (hAcard : Nat.card A = 9)
    {b' : G} (hb'CL : b' ∈ F08.CentOverO2 D.M L) (hb'3 : orderOf b' = 3) :
    Subgroup.normalizer (Subgroup.zpowers b' : Set G) ≤ D.M := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hLnormM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (ctx.hyp54.2 L ctx.memC).1
  have hLprod : F08.IsProdOfCalC D.M L := by
    refine ⟨1, fun _ => L, fun _ => ctx.memC, ?_⟩
    simp
  have hnthin : ¬ F08.Thin8 L := by
    intro hthin
    have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
      have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hAL hAea
        (k := 2) (by rw [hAcard]; norm_num)
      simpa using h
    have h1 := hthin 3 Nat.prime_three (by norm_num)
    omega
  have hBcard : Nat.card (Subgroup.zpowers b') = 3 := by
    rw [Nat.card_zpowers, hb'3]
  have hBcentral : ∀ a ∈ Subgroup.zpowers b', CentralizesBar a L := by
    intro a ha
    have haCL : a ∈ F08.CentOverO2 D.M L := Subgroup.zpowers_le.mpr hb'CL ha
    exact (uc22p21d_centralizesBar_iff).mpr fun l hl => (mem_centOverO2_iff.mp haCL).2 l hl
  have hsupB : (L ⊓ Subgroup.centralizer (Subgroup.zpowers b' : Set G)) ⊔
      pCoreOf 2 L = L :=
    uc22p21d_sup_pCore_eq Nat.prime_three (by norm_num) hBcard hBcentral
  have h869N : F08.R869N D := F08.R869N_of_R869 D h869
  exact h869N L hLM hLnormM hLprod hnthin 3 Nat.prime_three (by norm_num)
    (Subgroup.zpowers b') (Subgroup.zpowers_le.mpr (mem_centOverO2_iff.mp hb'CL).1)
    hBcard hsupB

theorem normalizer_zpowers_le_of_mem_sup_centralizing_sylow {D : Data G}
    {V₀ V L A P E : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p)
    (h69 : UC6.R6_9 D) (hsig1 : D.sig ⊆ D.sig1)
    (hAM : A ≤ D.M) (hAea : IsElemAbelian 3 A) (hAcard : Nat.card A = 9)
    (hΓA : rankThreeGamma 1 3 A ≤ D.M)
    (hAP : A ≤ P) (hPM : P ≤ D.M)
    (hEP : E ≤ P) (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    {z b' x : G} (hz3 : orderOf z = 3) (hb'3 : orderOf b' = 3)
    (hzL : z ∈ L) (hb'CL : b' ∈ F08.CentOverO2 D.M L)
    (hcomm_zb : Commute z b')
    (hKfix : K_L34Fix)
    (hEeq : E = Subgroup.zpowers z ⊔ Subgroup.zpowers b')
    (hxE : x ∈ E) (hx3 : orderOf x = 3)
    (hxz : x ∉ Subgroup.zpowers z) (hxb : x ∉ Subgroup.zpowers b') :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M := by
  by_contra hN
  have hxE' : x ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers b' := hEeq ▸ hxE
  have hxM : x ∈ D.M := hPM (hEP hxE)
  have hxcenP : x ∈ Subgroup.centralizer (P : Set G) := hEcentP hxE
  have hAx : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have hAC : A ≤ Subgroup.centralizer ({x} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hxcenP a (hAP ha)).symm
    have hcent_eq : Subgroup.centralizer ({x} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      simpa using (CFSG.Walter.JT.inf_centralizer_zpowers (⊤ : Subgroup G) x).symm
    exact hAC.trans (hcent_eq ▸ Subgroup.centralizer_le_normalizer _)
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hx3]
  have hxzp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num)
  have h69le := (h69 hsig1 3 Nat.prime_three (by norm_num) A hAM hAea hAcard hΓA
    3 (Subgroup.zpowers x) Nat.prime_three (Subgroup.zpowers_le.mpr hxM) hxcard hAx hN
    (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hxM) hxzp le_rfl).1
  have hcommZ : ∀ a ∈ Subgroup.zpowers z, ∀ c ∈ Subgroup.zpowers b', a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hi, ← hj]
    exact (hcomm_zb.zpow_zpow i j).eq
  obtain ⟨a, ha, c, hc, hxac⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommZ hxE'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
  have ha1 : a ≠ 1 := by
    intro ha1
    apply hxb
    rw [← hxac, ha1, one_mul]
    exact hc
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hxz
    rw [← hxac, hc1, mul_one]
    exact ha
  have hzi3 : orderOf (z ^ i) = 3 := by
    have hdvd : orderOf (z ^ i) ∣ Nat.card ↥(Subgroup.zpowers z) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) (Subgroup.zpow_mem_zpowers z i)
    rw [Nat.card_zpowers, hz3] at hdvd
    have hne : orderOf (z ^ i) ≠ 1 := by
      intro h1
      apply ha1
      rw [← hi, orderOf_eq_one_iff.mp h1]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hcj3 : orderOf (b' ^ j) = 3 := by
    have hdvd : orderOf (b' ^ j) ∣ Nat.card ↥(Subgroup.zpowers b') :=
      Subgroup.orderOf_dvd_natCard (Subgroup.zpowers b') (Subgroup.zpow_mem_zpowers b' j)
    rw [Nat.card_zpowers, hb'3] at hdvd
    have hne : orderOf (b' ^ j) ≠ 1 := by
      intro h1
      apply hc1
      rw [← hj, orderOf_eq_one_iff.mp h1]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hxac' : z ^ i * b' ^ j = x := by rw [hi, hj, hxac]
  have hzb3 : orderOf (z ^ i * b' ^ j) = 3 := by rw [hxac']; exact hx3
  have h4 := four_le_card_pCoreOf_inf_centralizer_mul D ctx (z := z ^ i) (b := b' ^ j)
    (L.zpow_mem hzL i) hzi3
    (Subgroup.zpow_mem (F08.CentOverO2 D.M L) hb'CL j) hcj3 hzb3 hKfix
  have h4' : 4 ≤ Nat.card ↥(pCoreOf 2 D.M ⊓ Subgroup.centralizer ({x} : Set G)) := by
    have h := h4
    rw [hxac'] at h
    exact h
  have h69le' : Nat.card ↥(pCoreOf 2 D.M ⊓
      Subgroup.centralizer ({x} : Set G)) ≤ 2 := by
    simpa [CFSG.Walter.JT.inf_centralizer_zpowers] using h69le
  omega

theorem exists_elemAbelian_three_central_sylow (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hThin : PartTwo.ThinList13)
    (hk2 : D.k = 2) (h61 : R17_61At D V₀ V) (h59 : R17_59At D V₀ V)
    (h869 : F08.R869 D) (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D) (hKfix : K_L34Fix) :
    ∃ (E P : Subgroup G), E ≤ P ∧ E ≤ Subgroup.centralizer (P : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      CFSG.ABGLocalTools.IsSylowOf 3 P D.M ∧ rankThreeGamma 1 3 E ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.memC
  have hsig1 : D.sig ⊆ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns
  have h3not : 3 ∉ D.sig := by
    intro h3
    exact ((Data.k_eq_two_iff D).mp hk2) (hSg.sig1_sp 3 (hsig1 h3))
  have hLM : L ≤ D.M := s13_le_of_mem_calC ctx.memC
  have hLnormM : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (ctx.hyp54.2 L ctx.memC).1
  obtain ⟨K, hKcal, hKne, hKnot⟩ := h61 L p ctx
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hKcal
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have h3barK : 3 ∣ Nat.card (Bar2 K) :=
    three_dvd_card_bar2_of_mem_calC ctx.hyp54 hThin hKcalM hKnot
  have h3K : 3 ∣ Nat.card K :=
    h3barK.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
  obtain ⟨bK, hb3K⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3K
  let b : G := bK
  have hbK : b ∈ K := bK.2
  have hb3 : orderOf b = 3 := by
    change orderOf (bK : G) = 3
    rw [Subgroup.orderOf_coe, hb3K]
  have hbM : b ∈ D.M := hKM hbK
  have hKcent : K ≤ F08.CentOverO2 D.M L := by
    intro k hk
    rw [mem_centOverO2_iff]
    refine ⟨hKM hk, fun l hl => ?_⟩
    have hcomm : ⁅l, k⁆ ∈ pCoreOf 2 L :=
      (PartTwo.calC_commutator_le_of_ne ctx.memC hKcalM hKne.symm
        (Subgroup.commutator_mem_commutator hl hk)).1
    simpa [commutatorElement_def, mul_assoc] using (pCoreOf 2 L).inv_mem hcomm
  have hbCL : b ∈ F08.CentOverO2 D.M L := hKcent hbK
  have hbCB : CentralizesBar b L :=
    (uc22p21d_centralizesBar_iff).mpr fun l hl => (mem_centOverO2_iff.mp hbCL).2 l hl
  have hCLnormM : D.M ≤ Subgroup.normalizer (F08.CentOverO2 D.M L : Set G) := by
    rw [centOverO2_eq_centSection]
    exact centSection_le_normalizer hLnormM
  have hbBarCent : barImage D.M (Subgroup.zpowers b) ≤
      Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    have hmG : (m : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hm
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hmCB : CentralizesBar (m : G) L := uc22p21d_centralizesBar_of_mem_zpowers hbCB hmG
    let cl : ↥D.M := m * l * m⁻¹ * l⁻¹
    have hclO : (cl : G) ∈ pCoreOf 2 D.M :=
      (CFSG.LocalAnalysis.UniquenessCase.UC22.P22s.pCoreOf_le_of_isSubnormal ctx.memC.1)
        (hmCB.2 (l : G) hlL)
    have hclPC : cl ∈ CFSG.pCore 2 ↥D.M := by
      obtain ⟨y', hy', hy'cl⟩ := Subgroup.mem_map.mp hclO
      have hEq : y' = cl := Subtype.ext hy'cl
      rwa [hEq] at hy'
    have hker : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) cl = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hclPC
    have hprod : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) m) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) l) *
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) l) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) m))⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) cl := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) m) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) l) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (m * l) := (map_mul _ _ _).symm
      have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) l) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) m) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (l * m) := (map_mul _ _ _).symm
      have h3 : ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (l * m))⁻¹) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ((l * m)⁻¹) := (map_inv _ _).symm
      rw [h1, h2, h3, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [cl, mul_assoc]
    have hAB : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) m) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) l) =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) l) *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) m) :=
      mul_inv_eq_one.mp (hprod.trans hker)
    exact hAB.symm
  obtain ⟨A, hAb, hAsylL⟩ :=
    exists_sylow_three_le_centralizer D ctx.hyp54 ctx.memC
      (Y := Subgroup.zpowers b) (r := 3) Nat.prime_three (by norm_num)
      (by rw [Nat.card_zpowers, hb3]) (Subgroup.zpowers_le.mpr hbM) hbBarCent
  have hAb' : A ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := hAb.trans inf_le_right
  have hAM : A ≤ D.M := hAsylL.le.trans hLM
  have hAea : IsElemAbelian 3 A := isElemAbelian_sylow_three ctx.shapeL hAsylL
  have hAcard : Nat.card A = 9 := card_sylow_three_eq_nine ctx.shapeL hAsylL
  have hΓA : rankThreeGamma 1 3 A ≤ D.M := h59 L p ctx A hAsylL
  let H : Subgroup G := A ⊔ Subgroup.zpowers b
  have hAH : A ≤ H := le_sup_left
  have hbH : b ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hHM : H ≤ D.M := sup_le hAM (Subgroup.zpowers_le.mpr hbM)
  have hAbsup : A ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hAb'.trans (Subgroup.centralizer_le_normalizer _)
  have hbzp : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3]; norm_num)
  have hHp : IsPGroup 3 H := IsPGroup.to_sup_of_normal_right' hAsylL.isPGroup hbzp hAbsup
  have hHsub : IsPGroup 3 (H.subgroupOf D.M) := hHp.comap_subtype
  obtain ⟨Q, hHQ⟩ := hHsub.exists_le_sylow
  let P : Subgroup G := (Q : Subgroup ↥D.M).map D.M.subtype
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P D.M := ⟨Q, rfl⟩
  have hPM : P ≤ D.M := hPsyl.le
  have hHP : H ≤ P := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hHM hx⟩, hHQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hAP : A ≤ P := hAH.trans hHP
  have hbP : b ∈ P := hHP hbH

  have hLsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) ctx.shapeL
  have hZbar : Subgroup.center (Bar2 L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar2 L)) with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative (Bar2 L) := Subgroup.center_eq_top_iff.mp h
      letI : CommGroup (Bar2 L) := IsMulCommutative.instCommGroup
      have hp := IsSimpleGroup.prime_card (α := Bar2 L)
      rw [card_bar_of_isL3 ctx.shapeL] at hp
      norm_num at hp
  have hA_CL_bot : A ⊓ F08.CentOverO2 D.M L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxCL⟩ := Subgroup.mem_inf.mp hx
    have hxL : x ∈ L := hAsylL.le hxA
    have hxCB : CentralizesBar x L :=
      (uc22p21d_centralizesBar_iff).mpr fun l hl => (mem_centOverO2_iff.mp hxCL).2 l hl
    have hxCM : x ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L)
        (Subgroup.normalizer (L : Set G)) L :=
      ⟨hxCB.1, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxCB.1, hxCB.2⟩
    have hxO2 : x ∈ pCoreOf 2 L :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.P2251c.mem_pCoreOf_of_mem_centralizerMod
        hZbar hxL hxCM
    have hcopAO : Nat.Coprime (Nat.card A) (Nat.card (pCoreOf 2 L)) := by
      rw [hAcard]
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
      rw [hk]
      exact (by norm_num : Nat.Coprime 9 2).pow_right k
    have hdisjAO : A ⊓ pCoreOf 2 L = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcopAO).eq_bot
    have hxbot : x ∈ A ⊓ pCoreOf 2 L := ⟨hxA, hxO2⟩
    rw [hdisjAO] at hxbot
    simpa using hxbot
  have hPp : IsPGroup 3 P := hPsyl.isPGroup
  haveI : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hAeq : P ⊓ L = A :=
    hAsylL.eq_of_le (le_inf hAP hAsylL.le) inf_le_right hPp.to_inf_left
  have hPLnorm : ((P ⊓ L).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer (hPM.trans hLnormM)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hAsub : A.subgroupOf P = (P ⊓ L).subgroupOf P := by
    ext x
    change ((x : G) ∈ A) ↔ ((x : G) ∈ P ⊓ L)
    rw [hAeq]
  have hAnormalP : (A.subgroupOf P).Normal := hAsub.symm ▸ hPLnorm
  have hAne : A.subgroupOf P ≠ ⊥ := by
    intro hbot
    have hmap : (A.subgroupOf P).map P.subtype = A :=
      Subgroup.map_subgroupOf_eq_of_le hAP
    have h1 : Nat.card A = 1 := by
      rw [← hmap]
      simp [hbot]
    omega
  have hZne : (A.subgroupOf P) ⊓ Subgroup.center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hAne
  obtain ⟨zP, hzPmem, hzPne⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hZne
  let z : G := zP
  have hzA : z ∈ A := Subgroup.mem_subgroupOf.mp hzPmem.1
  have hzL : z ∈ L := hAsylL.le hzA
  have hzP : z ∈ P := hAP hzA
  have hzC : z ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzPmem.2 ⟨p, hp⟩)
  have hz1 : z ≠ 1 := by
    intro h
    exact hzPne (Subtype.ext h)
  have hz3 : orderOf z = 3 := by
    exact orderOf_eq_prime (hAea.2 z hzA) (by simpa using hz1)
  have hz_not_CL : z ∉ F08.CentOverO2 D.M L := by
    intro hzCL
    have hxbot : z ∈ A ⊓ F08.CentOverO2 D.M L := ⟨hzA, hzCL⟩
    rw [hA_CL_bot] at hxbot
    exact hz1 (Subgroup.mem_bot.mp hxbot)
  have hPCLnorm : ((P ⊓ F08.CentOverO2 D.M L).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((le_inf Subgroup.le_normalizer (hPM.trans hCLnormM)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  haveI : ((P ⊓ F08.CentOverO2 D.M L).subgroupOf P).Normal := hPCLnorm
  have hN2ne : (P ⊓ F08.CentOverO2 D.M L).subgroupOf P ≠ ⊥ := by
    intro hbot
    have hbPsub : (⟨b, hbP⟩ : ↥P) ∈ (P ⊓ F08.CentOverO2 D.M L).subgroupOf P :=
      Subgroup.mem_subgroupOf.mpr ⟨hbP, hbCL⟩
    rw [hbot] at hbPsub
    have hb1' : (⟨b, hbP⟩ : ↥P) = 1 := by simpa using hbPsub
    have hb1 : b = 1 := congrArg Subtype.val hb1'
    rw [← orderOf_eq_one_iff, hb3] at hb1
    norm_num at hb1
  have hMsubne : ((P ⊓ F08.CentOverO2 D.M L).subgroupOf P) ⊓
      Subgroup.center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hN2ne
  have hMsubp : IsPGroup 3 ↥(((P ⊓ F08.CentOverO2 D.M L).subgroupOf P) ⊓
      Subgroup.center ↥P) := by
    have htop : IsPGroup 3 (⊤ : Subgroup ↥P) :=
      hPp.of_equiv (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥P) ≃* ↥P).symm
    exact htop.to_le le_top
  have h3dvdMsub : 3 ∣ Nat.card ↥(((P ⊓ F08.CentOverO2 D.M L).subgroupOf P) ⊓
      Subgroup.center ↥P) := by
    obtain ⟨k, hk⟩ := hMsubp.exists_card_eq
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hk
      exact hMsubne (Subgroup.eq_bot_of_card_eq _ hk)
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨bP, hbP3⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(((P ⊓ F08.CentOverO2 D.M L).subgroupOf P) ⊓ Subgroup.center ↥P)) 3 h3dvdMsub
  let b' : G := bP
  have hb'PCL : b' ∈ P ⊓ F08.CentOverO2 D.M L :=
    Subgroup.mem_subgroupOf.mp bP.2.1
  have hb'P : b' ∈ P := hb'PCL.1
  have hb'CL : b' ∈ F08.CentOverO2 D.M L := hb'PCL.2
  have hb'center : (bP : ↥P) ∈ Subgroup.center ↥P := bP.2.2
  have hb'C : b' ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hb'center ⟨p, hp⟩)
  have hb'3 : orderOf b' = 3 := by
    change orderOf ((bP : ↥P) : G) = 3
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hbP3]
  let E : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers b'
  have hzE : z ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hb'E : b' ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers b')
  have hzZP : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := ⟨hzP, hzC⟩
  have hb'ZP : b' ∈ P ⊓ Subgroup.centralizer (P : Set G) := ⟨hb'P, hb'C⟩
  have hE_ZP : E ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hzZP) (Subgroup.zpowers_le.mpr hb'ZP)
  have hEP : E ≤ P := hE_ZP.trans inf_le_left
  have hEcentP : E ≤ Subgroup.centralizer (P : Set G) := hE_ZP.trans inf_le_right
  have hz_not_b' : z ∉ Subgroup.zpowers b' := by
    intro hzB
    exact hz_not_CL (Subgroup.zpowers_le.mpr hb'CL hzB)
  have hcomm_zb : Commute z b' := by
    have h := Subgroup.mem_centralizer_iff.mp hzC b' hb'P
    exact h.symm
  have hdisj : Disjoint (Subgroup.zpowers b') (Subgroup.zpowers z) := by
    rw [disjoint_iff]
    let K := Subgroup.zpowers z
    let N := Subgroup.zpowers b' ⊓ K
    haveI : Fact (Nat.Prime (Nat.card K)) := ⟨by rw [Nat.card_zpowers, hz3]; norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (N.subgroupOf K) with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have hxN : (⟨x, hx.2⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hxN
      simpa using hxN
    · exfalso
      have hle : K ≤ N := by
        intro x hx
        have hxN : (⟨x, hx⟩ : K) ∈ N.subgroupOf K := by
          rw [htop]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hxN
      exact hz_not_b' ((hle (Subgroup.mem_zpowers z)).1)
  have hz_normalizes : z ∈ Subgroup.normalizer (Subgroup.zpowers b' : Set G) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [Subgroup.mem_comap]
      change z * y * z⁻¹ ∈ Subgroup.zpowers b'
      rw [← hj]
      have hc := (hcomm_zb.zpow_zpow 1 j).eq
      rw [show z = z ^ (1 : ℤ) by simp, hc, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj z).injective]
  have hnormalZ : Subgroup.zpowers z ≤
      Subgroup.normalizer (Subgroup.zpowers b' : Set G) :=
    Subgroup.zpowers_le.mpr hz_normalizes
  have hEcard : Nat.card E = 9 := by
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (A := Subgroup.zpowers b') (B := Subgroup.zpowers z) hnormalZ hdisj
    have hEeq : Subgroup.zpowers z ⊔ Subgroup.zpowers b' =
        Subgroup.zpowers b' ⊔ Subgroup.zpowers z := sup_comm _ _
    calc Nat.card E
        = Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers b') := rfl
      _ = Nat.card ↥(Subgroup.zpowers b' ⊔ Subgroup.zpowers z) := by rw [hEeq]
      _ = Nat.card ↥(Subgroup.zpowers b') * Nat.card ↥(Subgroup.zpowers z) := hcard
      _ = 3 * 3 := by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hb'3]
      _ = 9 := by norm_num
  have hEea : IsElemAbelian 3 E := by
    have hzEa : CFSG.IsElementaryAbelian 3 ↥(Subgroup.zpowers z) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr
        (CFSG.Open.isElemAbelian_zpowers (by simpa [hz3] using pow_orderOf_eq_one z))
    have hbEa : CFSG.IsElementaryAbelian 3 ↥(Subgroup.zpowers b') :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr
        (CFSG.Open.isElemAbelian_zpowers (by simpa [hb'3] using pow_orderOf_eq_one b'))
    have hle : Subgroup.zpowers b' ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hi, ← hj]
      exact (hcomm_zb.zpow_zpow i j).eq
    have hclass : CFSG.IsElementaryAbelian 3 ↥E :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).mp hclass
  have hz_norm : Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ D.M :=
    normalizer_zpowers_le_of_mem_centralizer_sylow h63 hAM hAea hAcard hΓA hzA hz3
  have hNE : Subgroup.normalizer (E : Set G) ≤ D.M :=
    normalizer_elemAbelian_centralizing_sylow_le h63 hAM hAea hAcard hΓA hAP hPM hPsyl
      hEcentP hzE hz_norm
  have hb'_norm : Subgroup.normalizer (Subgroup.zpowers b' : Set G) ≤ D.M :=
    normalizer_zpowers_le_of_mem_centOverO2 ctx h869 hAsylL.le hAea hAcard hb'CL hb'3
  have hcross : ∀ x ∈ E, orderOf x = 3 → x ∉ Subgroup.zpowers z →
      x ∉ Subgroup.zpowers b' →
      Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M := by
    intro x hxE hx3 hxz hxb
    exact normalizer_zpowers_le_of_mem_sup_centralizing_sylow ctx h69 hsig1 hAM hAea hAcard
      hΓA hAP hPM hEP hEcentP hz3 hb'3 hzL hb'CL hcomm_zb hKfix rfl hxE hx3 hxz hxb
  have hQ : ∀ Q : Subgroup G, Q ≤ E → 1 ≤ CFSG.Open.pRank 3 Q →
      Subgroup.normalizer (Q : Set G) ≤ D.M := by
    intro Q hQE hQrank
    by_cases hQeq : Q = E
    · rw [hQeq]; exact hNE
    · have hdvd : Nat.card Q ∣ Nat.card E := Subgroup.card_dvd_of_le hQE
      rw [hEcard] at hdvd
      obtain ⟨R, hRQ, hRea, hRcard⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
      have h3le : 3 ≤ Nat.card Q := by
        have h3R : 3 ≤ Nat.card R := by
          rw [hRcard]
          calc 3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ CFSG.Open.pRank 3 Q := Nat.pow_le_pow_right (by norm_num) hQrank
        exact h3R.trans (Subgroup.card_le_of_le hRQ)
      have hcardQ : Nat.card Q = 3 := by
        have hdvd' : Nat.card Q ∣ 3 ^ 2 := by simpa using hdvd
        obtain ⟨k, hk2, hk⟩ :=
          (Nat.dvd_prime_pow Nat.prime_three (m := 2) (i := Nat.card Q)).mp hdvd'
        have hle : Nat.card Q ≤ 9 := by
          rw [← hEcard]
          exact Subgroup.card_le_of_le hQE
        have hlt : Nat.card Q < 9 := by
          have hne : Nat.card Q ≠ 9 := by
            intro h9
            apply hQeq
            apply Subgroup.eq_of_le_of_card_ge hQE
            rw [h9, hEcard]
          omega
        rw [hk] at hle hlt h3le ⊢
        interval_cases k
        · norm_num at h3le
        · norm_num
        · norm_num at hlt
      have hQne : Q ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcardQ
        norm_num at hcardQ
      obtain ⟨x, hxQ, hx1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hQne
      have hx3 : orderOf x = 3 := by
        have hdvd2 : orderOf x ∣ Nat.card Q := Subgroup.orderOf_dvd_natCard Q hxQ
        rw [hcardQ] at hdvd2
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd2 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1
        · exact h
      have hQx : Q = Subgroup.zpowers x := by
        exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ)
          (by rw [Nat.card_zpowers, hx3, hcardQ])).symm
      rw [hQx]
      have hxE : x ∈ E := hQE hxQ
      by_cases hxz : x ∈ Subgroup.zpowers z
      · have hzx : Subgroup.zpowers x = Subgroup.zpowers z := by
          apply Subgroup.eq_of_le_of_card_ge
          · exact Subgroup.zpowers_le.mpr hxz
          · rw [Nat.card_zpowers, Nat.card_zpowers, hx3, hz3]
        rw [hzx]; exact hz_norm
      · by_cases hxb : x ∈ Subgroup.zpowers b'
        · have hb'x : Subgroup.zpowers x = Subgroup.zpowers b' := by
            apply Subgroup.eq_of_le_of_card_ge
            · exact Subgroup.zpowers_le.mpr hxb
            · rw [Nat.card_zpowers, Nat.card_zpowers, hx3, hb'3]
          rw [hb'x]; exact hb'_norm
        · exact hcross x hxE hx3 hxz hxb
  refine ⟨E, P, hEP, hEcentP, hEea, hEcard, hPsyl, ?_⟩
  exact CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall hQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
