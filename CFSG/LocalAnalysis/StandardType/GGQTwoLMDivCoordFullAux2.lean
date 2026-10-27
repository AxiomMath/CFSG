module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux3
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullWnorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTlift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTker
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTidRange
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTclNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerQuot
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKind
import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
import CFSG.LocalAnalysis.StandardType.GGQTwoLMModQm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord CFSG.Assembly
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

theorem qTwoLMDivF_fullT_suFull {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hlink : ∀ n : ↥L, MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
        MulAut.conj n' = MulAut.conj n)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hk : QTwoDivKind.facts .suFull m Bs L) :
    ∃ ΘT : ↥(sumZero m 3) ≃* ↥(Bs ⊓ L),
      (∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
        ∃ π' : Equiv.Perm (Fin m), ∀ v : ↥(sumZero m 3),
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (permAutVHom m 3 π' v) : ↥(Bs ⊓ L)) : G)) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
        (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : ↥(sumZero m 3),
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (permAutVHom m 3 σ v) : ↥(Bs ⊓ L)) : G)) := by
  obtain ⟨h1, hcardBs⟩ := hk
  obtain ⟨δ, hδ⟩ := qTwoLMDivCoordInner_torus hU.card h3
  obtain ⟨τ, hτ⟩ := qTwoLMDivCoordInner_tlift hBs hN hU hδ
  have hrange : ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t :=
    qTwoLMDivCoordInner_tid_range hBs hN (by omega) h3 hU hδ hτ
  have hinj : Function.Injective τ :=
    (qTwoLMDivCoordInner_tker hG hN hm h3 hU hδ hτ).1 h1
  have hcl1 := qTwoLMDivCoordInner_tcl_norm hBs hN (by omega) h3 hU hδ hτ hrange
  let φT : ↥(sumZero m 3) →* ↥(Bs ⊓ L) :=
    { toFun := fun f => ⟨(τ f : G), Subgroup.mem_inf.mpr ⟨hτ.mem f, (τ f).2⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun f g => by apply Subtype.ext; simp }
  have hφT_apply : ∀ f, ((φT f : ↥(Bs ⊓ L)) : G) = (τ f : G) := fun f => rfl
  have hinjT : Function.Injective φT := by
    intro f g hfg
    apply hinj
    apply Subtype.ext
    simpa [hφT_apply] using congrArg (fun y : ↥(Bs ⊓ L) => (y : G)) hfg
  have hsurjT : Function.Surjective φT := by
    intro y
    obtain ⟨f, hf⟩ := hrange ⟨(y : G), y.2.2⟩ y.2.1
    refine ⟨f, Subtype.ext ?_⟩
    rw [hφT_apply]
    exact congrArg (fun z : ↥L => (z : G)) hf
  let ΘT : ↥(sumZero m 3) ≃* ↥(Bs ⊓ L) :=
    MulEquiv.ofBijective φT ⟨hinjT, hsurjT⟩
  have hΘT : ∀ f, ((ΘT f : ↥(Bs ⊓ L)) : G) = (τ f : G) := by
    intro f
    show ((φT f : ↥(Bs ⊓ L)) : G) = (τ f : G)
    rfl
  refine ⟨ΘT, ?_, ?_⟩
  · intro n hn
    obtain ⟨π', hπ'⟩ := hcl1 n hn
    exact ⟨π', fun v => by
      simpa only [hΘT, permAutVHom_apply] using hπ' v⟩
  · intro σ
    have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
    have hxB : x ∈ B := hS.2.1
    have hxBs : x ∈ Bs := hBs.1 hxB
    have hx3 : orderOf x = 3 := orderOf_eq_prime (hBs.2.1.2 x hxBs) hS.2.2.1
    have hker := qTwoLMSkel_div_ker hG hBs hN
    obtain ⟨δF, hδF⟩ := qTwoLMDivF_torus hU.card m
    have hsurj : Function.Surjective (qTwoLMDivF_phi (by omega) hU hU.card hδF) :=
      qTwoLMDivF_phi_surjective (by omega) (qTwoLMFrameC_perfect hG) hU hU.card hδF hx3 hker
        hxBs hcardBs (qTwoLMSkel_isQmModel_card (qTwoLMDivF_isQmModel m))
    obtain ⟨n, hn⟩ := hU.c_surj (π (ggPermSU σ⁻¹))
    have hconjG : ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ =
        ((τ (permAutV σ f) : ↥L) : G) := by
      intro f
      have hc : c (n * τ f * n⁻¹) = c (τ (permAutV σ f)) := by
        rw [map_mul, map_mul, map_inv, hn, hτ.comm f, hτ.comm (permAutV σ f),
          ← map_mul, ← map_inv, ← map_mul, hδ.perm σ f]
      have h3 : (n * τ f * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hτ.cube f]; group
      have heq : n * τ f * n⁻¹ = τ (permAutV σ f) :=
        CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq
          hU.c_ker hU.c_two h3 (hτ.cube (permAutV σ f)) hc
      simpa using congrArg (fun y : ↥L => (y : G)) heq
    have hu : ∀ f, ((ggPermSU σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) * δF f *
        ((ggPermSU σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0)⁻¹ =
          δF (SpCoord.permAut σ f) := by
      intro f
      rw [qTwoLMDivF_ggPermSU_coe]
      exact hδF.perm σ f
    have hWn := qTwoLMDivF_wnorm_full (by omega) (qTwoLMFrameC_perfect hG) hU hU.card hδF
      hsurj hn σ hu
    obtain ⟨n', hn'B, hn'eq⟩ := hlink n hWn
    refine ⟨n', hn'B, fun v => ?_⟩
    have h1 : (n' : G) * ((τ v : ↥L) : G) * (n' : G)⁻¹ =
        (n : G) * ((τ v : ↥L) : G) * (n : G)⁻¹ :=
      congrArg (fun y : ↥L => (y : G)) (congrArg (fun φ : MulAut ↥L => φ (τ v)) hn'eq)
    rw [hΘT v, hΘT (permAutVHom m 3 σ v), h1]
    exact hconjG v

theorem qTwoLMDivF_fullT_psuFull {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hlink : ∀ n : ↥L, MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
        MulAut.conj n' = MulAut.conj n)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hk : QTwoDivKind.facts .psuFull m Bs L) :
    ∃ ΘT : QTwoHm m h3 ≃* ↥(Bs ⊓ L),
      (∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
        ∃ π' : Equiv.Perm (Fin m), ∀ v : QTwoHm m h3,
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (qTwoLMDivF_permH m h3 π' v) : ↥(Bs ⊓ L)) : G)) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
        (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : QTwoHm m h3,
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (qTwoLMDivF_permH m h3 σ v) : ↥(Bs ⊓ L)) : G)) := by
  obtain ⟨h1, hcardBs⟩ := hk
  obtain ⟨δ, hδ⟩ := qTwoLMDivCoordInner_torus hU.card h3
  obtain ⟨τ, hτ⟩ := qTwoLMDivCoordInner_tlift hBs hN hU hδ
  have hrange : ∀ t : ↥L, (t : G) ∈ Bs → ∃ f, τ f = t :=
    qTwoLMDivCoordInner_tid_range hBs hN (by omega) h3 hU hδ hτ
  have hτker : ∀ f, τ f = 1 ↔ f ∈ Subgroup.zpowers (qTwoOneVec m h3) :=
    (qTwoLMDivCoordInner_tker hG hN hm h3 hU hδ hτ).2.1 h1
  have hcl1 := qTwoLMDivCoordInner_tcl_norm hBs hN (by omega) h3 hU hδ hτ hrange
  let φT : ↥(sumZero m 3) →* ↥(Bs ⊓ L) :=
    { toFun := fun f => ⟨((τ f : ↥L) : G), hτ.mem f, (τ f).2⟩
      map_one' := by apply Subtype.ext; simp only [Subgroup.coe_one, map_one]
      map_mul' := fun f g => by apply Subtype.ext; simp only [Subgroup.coe_mul, map_mul] }
  have hφT_ker : φT.ker = Subgroup.zpowers (qTwoOneVec m h3) := by
    ext f
    rw [MonoidHom.mem_ker]
    constructor
    · intro hf
      have h_eq : τ f = 1 := by
        apply Subtype.ext
        have h := congrArg (fun x : ↥(Bs ⊓ L) => (x : G)) hf
        simpa [φT] using h
      exact (hτker f).mp h_eq
    · intro hf
      have h_tau_one : τ f = 1 := (hτker f).mpr hf
      apply Subtype.ext
      show ((τ f : ↥L) : G) = 1
      simp [h_tau_one]
  have hφT_surj : Function.Surjective φT := by
    intro y
    obtain ⟨f, hf⟩ := hrange ⟨(y : G), y.2.2⟩ y.2.1
    refine ⟨f, Subtype.ext ?_⟩
    exact congrArg (fun z : ↥L => (z : G)) hf
  obtain ⟨ΘT, hΘT⟩ := qTwoLMDivCoordInner_quot h3 φT hφT_surj hφT_ker
  have hΘT' : ∀ f, ((ΘT (QuotientGroup.mk f) : ↥(Bs ⊓ L)) : G) = ((τ f : ↥L) : G) := by
    intro f
    rw [hΘT]
    rfl
  refine ⟨ΘT, ?_, ?_⟩
  · intro n hn
    obtain ⟨π', hπ'⟩ := hcl1 n hn
    refine ⟨π', fun v => ?_⟩
    refine QuotientGroup.induction_on v fun f => ?_
    simpa only [qTwoLMDivF_permH_mk, hΘT', permAutVHom_apply] using hπ' f
  · intro σ
    have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
    have hxB : x ∈ B := hS.2.1
    have hxBs : x ∈ Bs := hBs.1 hxB
    have hx3 : orderOf x = 3 := orderOf_eq_prime (hBs.2.1.2 x hxBs) hS.2.2.1
    have hker := qTwoLMSkel_div_ker hG hBs hN
    obtain ⟨δF, hδF⟩ := qTwoLMDivF_torus hU.card m
    have hsurj : Function.Surjective (qTwoLMDivF_phi (by omega) hU hU.card hδF) :=
      qTwoLMDivF_phi_surjective (by omega) (qTwoLMFrameC_perfect hG) hU hU.card hδF hx3 hker
        hxBs hcardBs (qTwoLMSkel_isQmModel_card (qTwoLMDivF_isQmModel m))
    obtain ⟨n, hn⟩ := hU.c_surj (π (ggPermSU σ⁻¹))
    have hconjG : ∀ f, (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ =
        ((τ (permAutV σ f) : ↥L) : G) := by
      intro f
      have hc : c (n * τ f * n⁻¹) = c (τ (permAutV σ f)) := by
        rw [map_mul, map_mul, map_inv, hn, hτ.comm f, hτ.comm (permAutV σ f),
          ← map_mul, ← map_inv, ← map_mul, hδ.perm σ f]
      have h3 : (n * τ f * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hτ.cube f]; group
      have heq : n * τ f * n⁻¹ = τ (permAutV σ f) :=
        CFSG.LocalAnalysis.ComponentInitial.eq_of_pow_three_eq_one_of_map_eq
          hU.c_ker hU.c_two h3 (hτ.cube (permAutV σ f)) hc
      simpa using congrArg (fun y : ↥L => (y : G)) heq
    have hu : ∀ f, ((ggPermSU σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) * δF f *
        ((ggPermSU σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0)⁻¹ =
          δF (SpCoord.permAut σ f) := by
      intro f
      rw [qTwoLMDivF_ggPermSU_coe]
      exact hδF.perm σ f
    have hWn := qTwoLMDivF_wnorm_full (by omega) (qTwoLMFrameC_perfect hG) hU hU.card hδF
      hsurj hn σ hu
    obtain ⟨n', hn'B, hn'eq⟩ := hlink n hWn
    refine ⟨n', hn'B, fun v => ?_⟩
    refine QuotientGroup.induction_on v fun f => ?_
    have h1 : (n' : G) * ((τ f : ↥L) : G) * (n' : G)⁻¹ =
        (n : G) * ((τ f : ↥L) : G) * (n : G)⁻¹ :=
      congrArg (fun y : ↥L => (y : G)) (congrArg (fun φ : MulAut ↥L => φ (τ f)) hn'eq)
    rw [hΘT' f, qTwoLMDivF_permH_mk, hΘT' (permAutVHom m 3 σ f), h1]
    exact hconjG f


end CFSG.StandardType.QTwo

end
