module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassicalSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFour
import CFSG.GroupTheory.PLayer.Bootstrap
import CFSG.RankThree.PartOne.KE.CTTorusFixed
import CFSG.GroupTheory.PLayer.PIndex
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import Certificates.Certificate41501

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore CFSG.RankThree.PartOne.KE
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem rck_coord_rootDiagUnit
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (a : Fin τ.rank → Lˣ) :
    rckTorusCoord (rootDiagUnit τ a) = a := by
  have h : rootDiagUnit τ (rckTorusCoord (rootDiagUnit τ a)) = rootDiagUnit τ a :=
    rck_rootDiagUnit_coord (rootDiagUnit_mem_torusGroup a)
  exact rootDiagUnit_injective h

theorem rck_coord_mul
    {τ : Tag} {L : Type} [Field L] {y₁ y₂ : ModGL τ L} (h₁ : y₁ ∈ torusGroup τ L)
    (h₂ : y₂ ∈ torusGroup τ L) :
    rckTorusCoord (y₁ * y₂) = rckTorusCoord y₁ * rckTorusCoord y₂ := by
  apply rootDiagUnit_injective
  rw [rck_rootDiagUnit_coord (mul_mem h₁ h₂)]
  have h : rootDiagUnit τ (rckTorusCoord y₁ * rckTorusCoord y₂) =
      rootDiagUnit τ (rckTorusCoord y₁) * rootDiagUnit τ (rckTorusCoord y₂) :=
    (rootDiagUnitHom τ L).map_mul _ _
  rw [h, rck_rootDiagUnit_coord h₁, rck_rootDiagUnit_coord h₂]

theorem rck_rootChar_closure
    {t : StatedLieTag} {g0 : ModGL (langTag t) GGL}
    {S : Subgroup (ModGL (langTag t) GGL)} {T : Set (ModGL (langTag t) GGL)}
    (hS : S = Subgroup.closure T)
    (hSt : ∀ x ∈ S, g0⁻¹ * x * g0 ∈ torusGroup (langTag t) GGL)
    {γ : Fin (langTag t).rank → ℤ}
    (hT : ∀ x ∈ T, rootChar (rckTorusCoord (g0⁻¹ * x * g0)) γ = 1) :
    ∀ x ∈ S, rootChar (rckTorusCoord (g0⁻¹ * x * g0)) γ = 1 := by
  intro x hx
  have hx' : x ∈ Subgroup.closure T := hS ▸ hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem x hxT => exact hT x hxT
  | one =>
    have h1 : g0⁻¹ * (1 : ModGL (langTag t) GGL) * g0 = rootDiagUnit (langTag t) 1 := by
      rw [rootDiagUnit_one]
      group
    rw [h1, rck_coord_rootDiagUnit]
    exact CTTorus.rootChar_one γ
  | mul x y hx hy ihx ihy =>
    have hxS : x ∈ S := hS ▸ hx
    have hyS : y ∈ S := hS ▸ hy
    have h1 : g0⁻¹ * (x * y) * g0 = (g0⁻¹ * x * g0) * (g0⁻¹ * y * g0) := by group
    rw [h1, rck_coord_mul (hSt x hxS) (hSt y hyS), CTTorus.rootChar_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have hxS : x ∈ S := hS ▸ hx
    have h1 : g0⁻¹ * x⁻¹ * g0 = (g0⁻¹ * x * g0)⁻¹ := by group
    have hinv : rckTorusCoord ((g0⁻¹ * x * g0)⁻¹) = (rckTorusCoord (g0⁻¹ * x * g0))⁻¹ := by
      have hmul := rck_coord_mul (inv_mem (hSt x hxS)) (hSt x hxS)
      rw [inv_mul_cancel] at hmul
      have h0 : rckTorusCoord (1 : ModGL (langTag t) GGL) = 1 := by
        have := rck_coord_rootDiagUnit (L := GGL) (τ := langTag t) 1
        rwa [rootDiagUnit_one] at this
      rw [h0] at hmul
      exact eq_inv_of_mul_eq_one_left hmul.symm
    have h2 := ih
    rw [h1, hinv]
    have h3 : rootChar (rckTorusCoord (g0⁻¹ * x * g0))⁻¹ γ =
        (rootChar (rckTorusCoord (g0⁻¹ * x * g0)) γ)⁻¹ := by
      have hm := CTTorus.rootChar_mul (rckTorusCoord (g0⁻¹ * x * g0))⁻¹ (rckTorusCoord (g0⁻¹ * x * g0)) γ
      rw [inv_mul_cancel, CTTorus.rootChar_one] at hm
      exact eq_inv_of_mul_eq_one_left hm.symm
    rw [h3, h2, inv_one]

@[expose] noncomputable def rckConjTorus
    (τ : Tag) (g : ModGL τ GGL) : Subgroup (ModGL τ GGL) :=
  (torusGroup τ GGL).comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_rckConjTorus
    {τ : Tag} {g x : ModGL τ GGL} :
    x ∈ rckConjTorus τ g ↔ g⁻¹ * x * g ∈ torusGroup τ GGL := by
  simp [rckConjTorus, MulAut.conj_apply]

theorem rck_kernel_fam_gens
    {t : StatedLieTag} {g0 : ModGL (langTag t) GGL}
    {S : Subgroup (ModGL (langTag t) GGL)} {T : Set (ModGL (langTag t) GGL)}
    (hS : S = Subgroup.closure T) (hSt : S ≤ rckConjTorus (langTag t) g0) :
    kernelRoots (rckFamChar g0 (fun x : S => (x : ModGL (langTag t) GGL))) =
      {γ | IsRoot (langTag t) γ ∧ ∀ x ∈ T, rootChar (rckTorusCoord (g0⁻¹ * x * g0)) γ = 1} := by
  have hTS : T ⊆ S := fun x hx => hS ▸ Subgroup.subset_closure hx
  ext γ
  constructor
  · rintro ⟨hγ, h1⟩
    refine ⟨hγ, fun x hx => ?_⟩
    exact congrFun h1 ⟨x, hTS hx⟩
  · rintro ⟨hγ, hT⟩
    refine ⟨hγ, ?_⟩
    funext x
    exact rck_rootChar_closure hS (fun y hy => mem_rckConjTorus.1 (hSt hy)) hT x x.2

theorem rck_zpowers_le_conjTorus
    {t : StatedLieTag} {g0 xa : ModGL (langTag t) GGL} {a : Fin (langTag t).rank → GGLˣ}
    (hxa : g0⁻¹ * xa * g0 = rootDiagUnit (langTag t) a) :
    Subgroup.zpowers xa ≤ rckConjTorus (langTag t) g0 :=
  Subgroup.zpowers_le.2 (mem_rckConjTorus.2 (hxa ▸ rootDiagUnit_mem_torusGroup a))

theorem rck_fam_zpowers_kernel
    {t : StatedLieTag} {g0 xa : ModGL (langTag t) GGL} {a : Fin (langTag t).rank → GGLˣ}
    (hxa : g0⁻¹ * xa * g0 = rootDiagUnit (langTag t) a) :
    kernelRoots (rckFamChar g0 (fun x : Subgroup.zpowers xa => (x : ModGL (langTag t) GGL))) =
      kernelRoots (rootCharHom a) := by
  rw [rck_kernel_fam_gens (T := {xa}) (by rw [Subgroup.zpowers_eq_closure])
    (rck_zpowers_le_conjTorus hxa)]
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, hxa, rck_coord_rootDiagUnit]
  exact Iff.rfl

theorem rck_fam_pair_kernel
    {t : StatedLieTag} {g0 xa xb : ModGL (langTag t) GGL} {a b : Fin (langTag t).rank → GGLˣ}
    (hxa : g0⁻¹ * xa * g0 = rootDiagUnit (langTag t) a)
    (hxb : g0⁻¹ * xb * g0 = rootDiagUnit (langTag t) b) :
    kernelRoots (rckFamChar g0 (fun x : (Subgroup.zpowers xa ⊔ Subgroup.zpowers xb :
      Subgroup (ModGL (langTag t) GGL)) => (x : ModGL (langTag t) GGL))) =
      kernelRoots ((rootCharHom a).prod (rootCharHom b)) := by
  have hS : (Subgroup.zpowers xa ⊔ Subgroup.zpowers xb : Subgroup (ModGL (langTag t) GGL)) =
      Subgroup.closure ({xa, xb} : Set (ModGL (langTag t) GGL)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [rck_kernel_fam_gens (T := {xa, xb}) hS
    (sup_le (rck_zpowers_le_conjTorus hxa) (rck_zpowers_le_conjTorus hxb))]
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, hxa, hxb, rck_coord_rootDiagUnit]
  constructor
  · rintro ⟨hγ, h1, h2⟩
    refine ⟨hγ, ?_⟩
    exact Prod.ext h1 h2
  · rintro ⟨hγ, h⟩
    exact ⟨hγ, congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem rckRelOneUse_holds :
    RCKRelOneUse := by
  intro hR1 X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hFP b hbE hbp iJ hsub
    hshape
  have hcfg' := hcfg
  unfold RCKRPConfig at hcfg'
  obtain ⟨hGG, -, hp, hp2, -⟩ := hcfg'
  obtain ⟨hframe, htoral, -, -, -, hq, hΦ, -, hE', hEt, hEel, -, haE, ha1, hap, -, -, -, -, -, -,
    -⟩ := hFP
  haveI : Fact p.Prime := ⟨hp⟩
  have hA'T : ∀ x ∈ A', S.D.g0⁻¹ * x * S.D.g0 ∈ S.D.torus := fun x hx => by
    have h1 : (MulAut.conj S.D.g0⁻¹).toMonoidHom x ∈ E' := hE' ▸ Subgroup.mem_map_of_mem _ hx
    simpa [MulAut.conj_apply] using hEt h1
  have hxof : ∀ c : Fin (langTag t).rank → GGLˣ, rootDiagUnit (langTag t) c ∈ E' →
      ∃ x ∈ A', S.D.g0⁻¹ * x * S.D.g0 = rootDiagUnit (langTag t) c := fun c hc => by
    rw [hE'] at hc
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 hc
    exact ⟨x, hx, by simpa [MulAut.conj_apply] using hxc⟩
  obtain ⟨xa, hxaA, hxa⟩ := hxof a haE
  obtain ⟨xb, hxbA, hxb⟩ := hxof b hbE
  by_cases hb : rootDiagUnit (langTag t) b ∈ Subgroup.zpowers (rootDiagUnit (langTag t) a)
  ·
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hbk : b = a ^ k := by
      have h : rootDiagUnit (langTag t) (a ^ k) = rootDiagUnit (langTag t) a ^ k :=
        (rootDiagUnitHom (langTag t) GGL).map_zpow a k
      exact (rootDiagUnit_injective (h.trans hk)).symm
    have hker : kernelRoots ((rootCharHom a).prod (rootCharHom b)) = kernelRoots (rootCharHom a) := by
      ext γ
      constructor
      · rintro ⟨hγ, h⟩
        exact ⟨hγ, congrArg Prod.fst h⟩
      · rintro ⟨hγ, h⟩
        refine ⟨hγ, Prod.ext h ?_⟩
        have h1 : rootChar a γ = 1 := h
        show rootChar b γ = 1
        rw [hbk, rck_rootChar_zpow, h1, one_zpow]
    obtain ⟨j, hj⟩ := rck_component_transfer hker iJ
    obtain ⟨α, hα⟩ : (componentRoots ((rootCharHom a).prod (rootCharHom b)) iJ).Nonempty := by
      induction iJ using Quotient.inductionOn with
      | h α => exact ⟨α.1, α.2, rfl⟩
    have hαj : α ∈ componentRoots (rootCharHom a) j := hj ▸ hα
    have hαi : α ∈ componentRoots (rootCharHom a) i := hsub hα
    have hji : j = i := hαj.2.symm.trans hαi.2
    rw [hj, hji]
  ·
    have hA'el := hframe.2.2.2.1
    have hxa1 : xa ≠ 1 := by
      intro h
      apply ha1
      rw [← hxa, h]
      group
    have hxap : xa ^ p = 1 := hA'el.2 xa hxaA
    have hxbp : xb ^ p = 1 := hA'el.2 xb hxbA
    haveI hfin : Finite A' := by
      apply Nat.finite_of_card_ne_zero
      rw [hframe.2.2.2.2.1]
      exact Nat.card_pos.ne'
    have hcomm : (⟨xa, hxaA⟩ : A') * ⟨xb, hxbA⟩ = ⟨xb, hxbA⟩ * ⟨xa, hxaA⟩ :=
      (isMulCommutative_iff.mp hA'el.1) _ _
    have hx1' : (⟨xa, hxaA⟩ : A') ≠ 1 := fun h => hxa1 (congrArg Subtype.val h)
    have hyx : (⟨xb, hxbA⟩ : A') ∉ Subgroup.zpowers (⟨xa, hxaA⟩ : A') := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      apply hb
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have h1 : xa ^ k = xb := congrArg Subtype.val hk
      have h2 : S.D.g0⁻¹ * xa ^ k * S.D.g0 = (S.D.g0⁻¹ * xa * S.D.g0) ^ k := by
        have := conj_zpow (a := S.D.g0⁻¹) (b := xa) (i := k)
        rw [inv_inv] at this
        exact this.symm
      rw [← hxa, ← h2, h1, hxb]
    have h2card : Nat.card (Subgroup.zpowers xa : Subgroup (ModGL (langTag t) GGL)) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxap hxa1]
    have h1card : Nat.card (Subgroup.zpowers xa ⊔ Subgroup.zpowers xb :
        Subgroup (ModGL (langTag t) GGL)) = p ^ 2 := by
      have h := CFSG.card_zpowers_sup_zpowers_eq_prime_sq hp (x := (⟨xa, hxaA⟩ : A'))
        (y := (⟨xb, hxbA⟩ : A')) (Subtype.ext (by simpa using hxap))
        (Subtype.ext (by simpa using hxbp)) hx1' hyx hcomm
      have hmap : (Subgroup.zpowers (⟨xa, hxaA⟩ : A') ⊔ Subgroup.zpowers (⟨xb, hxbA⟩ : A')).map
          A'.subtype = Subgroup.zpowers xa ⊔ Subgroup.zpowers xb := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] <;> rfl
      rw [← hmap, Subgroup.card_map_of_injective A'.subtype_injective]
      exact h
    have hle : (Subgroup.zpowers xa ⊔ Subgroup.zpowers xb : Subgroup (ModGL (langTag t) GGL)) ≤ A' :=
      sup_le (Subgroup.zpowers_le.2 hxaA) (Subgroup.zpowers_le.2 hxbA)
    have hker2 := rck_fam_zpowers_kernel (g0 := S.D.g0) hxa
    have hker1 := rck_fam_pair_kernel (g0 := S.D.g0) hxa hxb
    obtain ⟨iK, hiK⟩ := rck_component_transfer hker2.symm i
    obtain ⟨iJ', hiJ⟩ := rck_component_transfer hker1.symm iJ
    have hres := hR1 X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' hframe htoral S.D S.ρ hΦ
      S.frob hA'T (Subgroup.zpowers xa ⊔ Subgroup.zpowers xb) (Subgroup.zpowers xa) le_sup_left hle
      h1card h2card iJ' iK (by rw [← hiJ, ← hiK]; exact hsub) (by rw [← hiK]; exact hshape)
    rw [← hiJ, ← hiK] at hres
    exact hres

end CFSG.StandardType.RCKRP
