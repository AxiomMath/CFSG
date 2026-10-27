module

public import CFSG.Quasithin.Recognition.St84.Sp44Data
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalC
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NatSL2Mat
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open CFSG.GH74.QTGen4.DSGen4.Lin2A CFSG.GH74.QTGen4.DSGen4.Lin2B
  CFSG.GH74.QTGen4.DSGen4.Lin2C
open CFSG.QuasithinUnique.A5.Delta5 (Alt5)
open CFSG.SL2MinimalFaithful CFSG.CGT.PushingUpLit.CGT6.TwoThree
open Certificates.A5GL42 (HN Facts)
open scoped commutatorElement Matrix

namespace Sp44

variable {G : Type} [Group G]

@[expose] def NatFrame (L : Subgroup G)
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (β : ↥(pCoreOf 2 L) →* Multiplicative (Fin 2 → GaloisField 2 2)) : Prop :=
  Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ Function.Surjective β ∧
    (∀ q, β q = 1 ↔ (q : G) ∈ centerOf L) ∧
    ∀ (l : ↥L) (q q' : ↥(pCoreOf 2 L)), (q' : G) = l * q * l⁻¹ →
      Multiplicative.toAdd (β q') =
        (α l : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ Multiplicative.toAdd (β q)

theorem a5Pre_sec [Finite G] {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L))
    (hQe : IsElemAbelian 2 (pCoreOf 2 L)) (hZQ : centerOf L ≤ pCoreOf 2 L)
    (hidx : (centerOf L).relIndex (pCoreOf 2 L) = 16)
    (hnat : NatSec L (centerOf L) (pCoreOf 2 L)) :
    A5Pre L L (pCoreOf 2 L) (centerOf L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm1 : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, ⁅a, b⁆ = 1 := fun a ha b hb =>
    commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a ha b hb)
  have hKnorm : L ≤ Subgroup.normalizer (centerOf L : Set G) := by
    have hconj : ∀ g ∈ L, ∀ c ∈ centerOf L, g * c * g⁻¹ ∈ centerOf L := by
      intro g hg c hc
      have hc' : c ∈ L ⊓ Subgroup.centralizer (L : Set G) := hc
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) c).mp hc'.1
      · have hcC : c ∈ Subgroup.centralizer (L : Set G) := hc'.2
        rw [Subgroup.mem_centralizer_iff] at hcC ⊢
        intro x hx
        have hxg : g⁻¹ * x * g ∈ L := by
          simpa using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (L.inv_mem hg)) x).mp hx
        have hcomm' := hcC (g⁻¹ * x * g) hxg
        calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm']
          _ = (g * c * g⁻¹) * x := by group
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro c
    exact ⟨hconj l hl c, fun hc => by
      have := hconj l⁻¹ (L.inv_mem hl) (l * c * l⁻¹) hc
      simpa [mul_assoc] using this⟩
  refine ⟨le_rfl, Subgroup.le_normalizer, le_normalizer_pCore, hKnorm, ?_,
    hidx, ?_, hq, ?_⟩
  · refine ⟨hZQ, ?_, ?_⟩
    · exact Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [hcomm1 a ha b hb]
        exact (centerOf L).one_mem
    · intro e he
      rw [hQe.2 e he]
      exact (centerOf L).one_mem
  · intro q hq' e he
    rw [hcomm1 q hq' e he]
    exact (centerOf L).one_mem
  · by_contra hcon
    push Not at hcon
    obtain ⟨x, hxL, hx3⟩ := exists_orderOf_eq_three_of_isL2Quot hq
    have hQZ : pCoreOf 2 L ≤ centerOf L := by
      intro e he
      apply hnat x hxL hx3 e he
      have hc := hcon x hxL e he
      rw [← commutatorElement_inv]
      exact (centerOf L).inv_mem hc
    have hZeq : centerOf L = pCoreOf 2 L := le_antisymm hZQ hQZ
    rw [hZeq] at hidx
    simp at hidx

theorem natFrame_of_natSec [Finite G] {L : Subgroup G}
    (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hQe : IsElemAbelian 2 (pCoreOf 2 L))
    (hZQ : centerOf L ≤ pCoreOf 2 L) (hidx : (centerOf L).relIndex (pCoreOf 2 L) = 16)
    (hnat : NatSec L (centerOf L) (pCoreOf 2 L)) :
    ∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
      (β : ↥(pCoreOf 2 L) →* Multiplicative (Fin 2 → GaloisField 2 2)),
      NatFrame L α β := by
  classical
  have hF : Facts := a5Facts
  have hA5 : A5Pre L L (pCoreOf 2 L) (centerOf L) :=
    a5Pre_sec hq hQe hZQ hidx hnat
  obtain ⟨Mdl⟩ : Nonempty (A5Model L L (pCoreOf 2 L) (centerOf L) HN) := by
    rcases hA5.exists_model' with ⟨-, hm⟩ | ⟨hno, -⟩
    · exact hm
    · exact absurd hnat hno
  have hker : ∀ y : ↥L, y ∈ CFSG.pCore 2 ↥L → Mdl.F.M (Subgroup.inclusion hA5.le y) = 1 := by
    intro y hy
    exact Mdl.core (Subgroup.inclusion hA5.le y) ((mem_pCore_iff_pCoreOf y).mp hy)
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  have hιinj : Function.Injective (iotaOf Mdl.F hA5 hker e) := iotaOf_injective Mdl.F hA5 hker e
  set ι : Alt5 →* GL (Fin 4) (ZMod 2) := iotaOf Mdl.F hA5 hker e with hιdef
  have hιM : ∀ ℓ : ↥L,
      ((ι (e (QuotientGroup.mk ℓ)) : GL (Fin 4) (ZMod 2)) : Mat4) = (Mdl.F.M ℓ : Mat4) := by
    intro ℓ
    rw [hιdef, iotaOf_mk Mdl.F hA5 hker e ℓ]
    rfl
  have hlift : ∀ σ : Alt5, ∃ ℓ : ↥L, e (QuotientGroup.mk ℓ) = σ := by
    intro σ
    obtain ⟨q, hq'⟩ := e.surjective σ
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨ℓ, hq'⟩
  obtain ⟨ℓ₀, hℓ₀⟩ := hlift y0
  have hy0 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) = (Mdl.F.M ℓ₀ : Mat4) := by
    rw [← hℓ₀]
    exact hιM ℓ₀
  have hy0HN : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) ∈ HN := by
    rw [hy0]
    exact Mdl.imgL ℓ₀ ℓ₀.2
  have hy0ne : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) ≠ 1 := by
    intro h
    apply y0_ne_one
    apply hιinj
    rw [map_one]
    exact Units.ext h
  have hy0cube : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) * ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *
      ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) = 1 := by
    have h3 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, y0_cube, map_one, Units.val_one]
    rw [pow_three] at h3
    rw [mul_assoc]
    exact h3
  have hVff : ∀ v : Fin 4 → ZMod 2, ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v → v = 0 :=
    fun v hv => hF.fixN _ hy0HN hy0ne hy0cube v hv
  have hVx : ι x0 ≠ 1 := by
    intro h
    apply x0_ne_one
    apply hιinj
    rw [map_one]
    exact h
  have hFdim : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 := GaloisField.finrank 2 (by norm_num)
  set κ := kappa (GaloisField 2 2) hFdim with hκdef
  obtain ⟨eqPSL⟩ := hq
  set χ : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    eqPSL.trans (pslEquivSL _) with hχdef
  set ψ : Alt5 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) := e.symm.trans χ with hψdef
  have hψe : ∀ ℓ : ↥L, ψ (e (QuotientGroup.mk ℓ)) = χ (QuotientGroup.mk ℓ) := by
    intro ℓ
    rw [hψdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set WmA : Alt5 →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    (natMat (GaloisField 2 2) κ).comp ψ.toMonoidHom with hWmA
  set Wu : Alt5 →* GL (Fin 4) (ZMod 2) := toUnitsHom WmA with hWu
  have hWuc : ∀ σ : Alt5,
      ((Wu σ : GL (Fin 4) (ZMod 2)) : Mat4) = natMat (GaloisField 2 2) κ (ψ σ) := fun σ => rfl
  have hWx : Wu x0 ≠ 1 := by
    intro h
    have h1 : natMat (GaloisField 2 2) κ (ψ x0) = 1 := by
      rw [← hWuc, h, Units.val_one]
    have h2 : ψ x0 = 1 := eq_one_of_natMat_eq_one κ h1
    apply x0_ne_one
    apply ψ.injective
    rw [h2, map_one]
  have hWff : ∀ v : Fin 4 → ZMod 2, ((Wu y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v → v = 0 := by
    intro v hv
    rw [hWuc] at hv
    have hg3 : (ψ y0) ^ 3 = 1 := by rw [← map_pow, y0_cube, map_one]
    have hg1 : ψ y0 ≠ 1 := by
      intro h
      apply y0_ne_one
      apply ψ.injective
      rw [h, map_one]
    exact natMat_fixFree κ (ψ y0) hg3 hg1 v hv
  obtain ⟨TU, hTU⟩ := exists_intertwiner hF ι Wu hVx hVff hWx hWff
  have hTUM : ∀ ℓ : ↥L,
      (TU : Mat4) * (Mdl.F.M ℓ : Mat4) =
        natMat (GaloisField 2 2) κ (χ (QuotientGroup.mk ℓ)) * (TU : Mat4) := by
    intro ℓ
    have h1 := congrArg Units.val (hTU (e (QuotientGroup.mk ℓ)))
    rw [Units.val_mul, Units.val_mul, hιM ℓ, hWuc, hψe] at h1
    exact h1
  let β : ↥(pCoreOf 2 L) →* Multiplicative (Fin 2 → GaloisField 2 2) :=
    (linMul κ (TU : Mat4)).comp Mdl.F.φ
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    χ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  refine ⟨α, β, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (χ.symm s)
    refine ⟨x, ?_⟩
    show χ (QuotientGroup.mk x) = s
    rw [hx, MulEquiv.apply_symm_apply]
  ·
    ext ℓ
    rw [MonoidHom.mem_ker]
    show χ (QuotientGroup.mk ℓ) = 1 ↔ ℓ ∈ CFSG.pCore 2 ↥L
    rw [map_eq_one_iff χ χ.injective, QuotientGroup.eq_one_iff]
  ·
    intro w
    set z : Fin 4 → ZMod 2 :=
      ((TU⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ κ.symm (Multiplicative.toAdd w) with hz
    obtain ⟨q, hqφ⟩ := Mdl.F.surj (Multiplicative.ofAdd z)
    refine ⟨q, ?_⟩
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ q)) = Multiplicative.toAdd w
    rw [toAdd_linMul, hqφ, toAdd_ofAdd, hz, Matrix.mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  ·
    have hTUinj : ∀ y : Fin 4 → ZMod 2, (TU : Mat4) *ᵥ y = 0 → y = 0 := by
      intro y hy
      have h := congrArg (fun z => ((TU⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ z) hy
      simpa [Matrix.mulVec_mulVec] using h
    intro q
    rw [← Mdl.F.ker q]
    constructor
    · intro h
      have h' : Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ q)) = 0 := by
        simpa [β, toAdd_one] using congrArg Multiplicative.toAdd h
      rw [toAdd_linMul] at h'
      have h2 : (TU : Mat4) *ᵥ Multiplicative.toAdd (Mdl.F.φ q) = 0 :=
        κ.map_eq_zero_iff.mp h'
      exact toAdd_eq_zero.mp (hTUinj _ h2)
    · intro h
      change (linMul κ (TU : Mat4)) (Mdl.F.φ q) = 1
      rw [h, map_one]
  ·
    intro l q q' hq'
    have hact := Mdl.F.act l q q' hq'
    show Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ q')) =
      (α l : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ
        Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ q))
    rw [toAdd_linMul, toAdd_linMul, ← hact, Matrix.mulVec_mulVec, hTUM l,
      ← Matrix.mulVec_mulVec, natMat_mulVec, LinearEquiv.apply_symm_apply]
    rfl

theorem invariant_le_center_or_eq [Finite G] {L : Subgroup G}
    {α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)}
    {β : ↥(pCoreOf 2 L) →* Multiplicative (Fin 2 → GaloisField 2 2)}
    (hframe : NatFrame L α β) (hind : ⁅pCoreOf 2 L, L⁆ = pCoreOf 2 L)
    {W : Subgroup G} (hWQ : W ≤ pCoreOf 2 L) (hWn : L ≤ Subgroup.normalizer (W : Set G)) :
    W ≤ centerOf L ∨ W = pCoreOf 2 L := by
  classical
  obtain ⟨hαsurj, -, -, hβker, heq⟩ := hframe
  let Q := pCoreOf 2 L
  let Wsub : Subgroup ↥Q := W.subgroupOf Q
  let S : Subgroup (Multiplicative (Fin 2 → GaloisField 2 2)) := Wsub.map β
  have hSinv : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
      (x : Multiplicative (Fin 2 → GaloisField 2 2)), x ∈ S →
      Multiplicative.ofAdd ((M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ
        Multiplicative.toAdd x) ∈ S := by
    intro M x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨l, hl⟩ := hαsurj M
    have hqW : (q : G) ∈ W := Subgroup.mem_subgroupOf.mp hq
    have hq'Q : (l : G) * (q : G) * (l : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCore (L := L) l.2) (q : G)).mp q.2
    let q' : ↥Q := ⟨(l : G) * (q : G) * (l : G)⁻¹, hq'Q⟩
    have hq'W : (q' : G) ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWn l.2) (q : G)).mp hqW
    refine ⟨q', Subgroup.mem_subgroupOf.mpr hq'W, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, heq l q q' rfl, hl]
  have hStop_or_bot : S = ⊥ ∨ S = ⊤ := by
    by_cases hSbot : S = ⊥
    · exact Or.inl hSbot
    · right
      obtain ⟨x, hxS, hx1⟩ : ∃ x ∈ S, x ≠ 1 := by
        by_contra h
        push Not at h
        exact hSbot (le_antisymm (fun y hy => by rw [Subgroup.mem_bot]; exact h y hy) bot_le)
      have hv : Multiplicative.toAdd x ≠ 0 := fun h => hx1 (toAdd_eq_zero.mp h)
      obtain ⟨M, hM⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq
        (K := GaloisField 2 2) (v := Multiplicative.toAdd x) hv
      have hMM : ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
          (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = 1 := by
        have h1 : ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
            Matrix.adjugate (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) := rfl
        have hdet : (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).det = 1 := M.2
        rw [h1, Matrix.adjugate_mul, hdet, one_smul]
      have hM' : ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *ᵥ Multiplicative.toAdd x = ![1, 0] := by
        rw [← hM, Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
      have he1 : Multiplicative.ofAdd ![1, 0] ∈ S := by
        have hmem := hSinv M⁻¹ x hxS
        rwa [hM'] at hmem
      rw [eq_top_iff]
      intro y _
      by_cases hy1 : y = 1
      · rw [hy1]; exact S.one_mem
      · have hv' : Multiplicative.toAdd y ≠ 0 := fun h => hy1 (toAdd_eq_zero.mp h)
        obtain ⟨N, hN⟩ := CFSG.Timmesfeld.ARS.NaturalModule.exists_mulVec_eq
          (K := GaloisField 2 2) (v := Multiplicative.toAdd y) hv'
        have hmem := hSinv N (Multiplicative.ofAdd ![1, 0]) he1
        rw [toAdd_ofAdd, hN] at hmem
        simpa using hmem
  rcases hStop_or_bot with hSbot | hStop
  · left
    intro w hw
    have hq : (⟨w, hWQ hw⟩ : ↥Q) ∈ Wsub := Subgroup.mem_subgroupOf.mpr hw
    have hmem : β ⟨w, hWQ hw⟩ ∈ S := ⟨_, hq, rfl⟩
    rw [hSbot] at hmem
    exact (hβker ⟨w, hWQ hw⟩).mp (Subgroup.mem_bot.mp hmem)
  · right
    have hQW : Q ≤ W := by
      change pCoreOf 2 L ≤ W
      rw [← hind]
      refine Subgroup.commutator_le.mpr ?_
      intro q hq l hl
      have hqS : β ⟨q, hq⟩ ∈ S := by rw [hStop]; exact Subgroup.mem_top _
      obtain ⟨q₀, hq₀, hβq₀⟩ := Subgroup.mem_map.mp hqS
      have hwW : (q₀ : G) ∈ W := Subgroup.mem_subgroupOf.mp hq₀
      have hwL : (q₀ : G) ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L q₀.2
      have hker : β (⟨q, hq⟩ * q₀⁻¹) = 1 := by
        rw [map_mul, map_inv, hβq₀, mul_inv_cancel]
      have hZ : q * (q₀ : G)⁻¹ ∈ centerOf L := by
        have := (hβker (⟨q, hq⟩ * q₀⁻¹)).mp hker
        simpa using this
      have hZc : q * (q₀ : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := hZ.2
      have hz_l : (q * (q₀ : G)⁻¹) * l = l * (q * (q₀ : G)⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hZc l hl).symm
      have hcom : ⁅q, l⁆ = ⁅(q₀ : G), l⁆ := by
        rw [show q = (q * (q₀ : G)⁻¹) * (q₀ : G) from by group]
        have hmemc : ⁅(q₀ : G), l⁆ ∈ L := by
          simpa [commutatorElement_def] using
            L.mul_mem (L.mul_mem (L.mul_mem hwL hl) (L.inv_mem hwL)) (L.inv_mem hl)
        have hzc : (q * (q₀ : G)⁻¹) * ⁅(q₀ : G), l⁆ * (q * (q₀ : G)⁻¹)⁻¹ = ⁅(q₀ : G), l⁆ := by
          have hcomm : ⁅(q₀ : G), l⁆ * (q * (q₀ : G)⁻¹) = (q * (q₀ : G)⁻¹) * ⁅(q₀ : G), l⁆ :=
            hZc _ hmemc
          rw [← hcomm]; group
        have hzl1 : ⁅(q * (q₀ : G)⁻¹), l⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr hz_l
        calc ⁅(q * (q₀ : G)⁻¹) * (q₀ : G), l⁆
            = (q * (q₀ : G)⁻¹) * ⁅(q₀ : G), l⁆ * (q * (q₀ : G)⁻¹)⁻¹ *
                ⁅(q * (q₀ : G)⁻¹), l⁆ :=
              commutatorElement_mul_left_eq_conj_mul _ _ _
          _ = ⁅(q₀ : G), l⁆ := by rw [hzc, hzl1, mul_one]
      have hwcomm : ⁅(q₀ : G), l⁆ ∈ W := by
        simp only [commutatorElement_def]
        have h1 : l * (q₀ : G)⁻¹ * l⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWn hl) (q₀ : G)⁻¹).mp (W.inv_mem hwW)
        have h2 : (q₀ : G) * (l * (q₀ : G)⁻¹ * l⁻¹) ∈ W := W.mul_mem hwW h1
        simpa [mul_assoc] using h2
      rw [hcom]
      exact hwcomm
    exact le_antisymm hWQ hQW

theorem eq_smul_of_commute_sl {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = 4)
    (f : (Fin 2 → K) →+ (Fin 2 → K))
    (hf : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) K) v,
      f ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ f v) :
    ∃ ν : K, ∀ v, f v = ν • v := by
  classical
  set e1 : Fin 2 → K := ![1, 0] with he1
  set e2 : Fin 2 → K := ![0, 1] with he2
  have hA : (f e1) 1 = 0 := by
    have hu1 : ((unipotent (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = e1 := by
      rw [unipotent_mulVec]
      ext i; fin_cases i <;> simp [e1]
    have h := hf (unipotent (1 : K)) e1
    rw [hu1] at h
    have h' : f e1 = ![(f e1) 0 + (f e1) 1, (f e1) 1] := by
      calc f e1 = ((unipotent (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) *ᵥ f e1 := h
        _ = ![(f e1) 0 + (f e1) 1, (f e1) 1] := by
              rw [unipotent_mulVec]; simp
    have h2 : (f e1) 0 = (f e1) 0 + (f e1) 1 := by
      simpa using congrFun h' 0
    exact add_left_cancel (a := (f e1) 0) (by simpa using h2.symm)
  have hB : (f e2) 0 = 0 := by
    have hl1 : ((lowerUni (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *ᵥ e2 = e2 := by
      rw [lowerUni_mulVec]
      ext i; fin_cases i <;> simp [e2]
    have h := hf (lowerUni (1 : K)) e2
    rw [hl1] at h
    have h' : f e2 = ![(f e2) 0, (f e2) 0 + (f e2) 1] := by
      calc f e2 = ((lowerUni (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) *ᵥ f e2 := h
        _ = ![(f e2) 0, (f e2) 0 + (f e2) 1] := by
              rw [lowerUni_mulVec]; simp
    have h2 : (f e2) 1 = (f e2) 0 + (f e2) 1 := by
      simpa using congrFun h' 1
    exact add_right_cancel (b := (f e2) 1) (by simpa using h2.symm)
  have hfe1 : f e1 = ![f e1 0, 0] := by
    ext i; fin_cases i <;> simp [hA]
  have hfe2 : f e2 = ![0, f e2 1] := by
    ext i; fin_cases i <;> simp [hB]
  have hC1 : ∀ a : K, f (a • e1) = a • f e1 := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    · let u : Kˣ := Units.mk0 a ha
      have hu : (u : K) = a := rfl
      have h := hf (diagSL u) e1
      have hvec : ((diagSL u : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) *ᵥ e1 = a • e1 := by
        rw [diagSL_mulVec]
        ext i; fin_cases i <;> simp [e1, hu]
      rw [hvec] at h
      rw [h, hfe1, diagSL_mulVec]
      ext i; fin_cases i <;> simp [hu]
  have hC2 : ∀ b : K, f (b • e2) = b • f e2 := by
    intro b
    by_cases hb : b = 0
    · simp [hb]
    · let u : Kˣ := (Units.mk0 b hb)⁻¹
      have hu : (u : K) = b⁻¹ := rfl
      have hu' : ((u⁻¹ : Kˣ) : K) = b := by simp [u]
      have h := hf (diagSL u) e2
      have hvec : ((diagSL u : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) *ᵥ e2 = b • e2 := by
        rw [diagSL_mulVec]
        ext i; fin_cases i <;> simp [e2, hu, hu']
      rw [hvec] at h
      rw [h, hfe2, diagSL_mulVec]
      ext i; fin_cases i <;> simp [hu, hu']
  have hD : (f e1) 0 = (f e2) 1 := by
    have h := hf (unipotent (1 : K)) e2
    have hvec : ((unipotent (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *ᵥ e2 = e1 + e2 := by
      rw [unipotent_mulVec]
      ext i; fin_cases i <;> simp [e1, e2]
    rw [hvec] at h
    rw [f.map_add, unipotent_mulVec] at h
    have := congrFun h 0
    simpa [hB] using this
  set ν : K := (f e1) 0 with hν
  refine ⟨ν, fun v => ?_⟩
  have hv : v = v 0 • e1 + v 1 • e2 := by
    ext i; fin_cases i <;> simp [e1, e2]
  rw [hv, f.map_add, hC1, hC2, hfe1, hfe2, smul_add, smul_smul, smul_smul]
  ext i; fin_cases i <;> simp [he1, he2, Pi.smul_apply, hD]
  · ring
  · ring

end Sp44

end CFSG.Quasithin.F112R.St84
