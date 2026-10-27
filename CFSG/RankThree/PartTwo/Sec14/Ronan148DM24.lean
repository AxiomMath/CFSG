module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofCompOne
import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofOuter
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofW
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Descent2
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofObs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec4.Item413Cases

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Transport

variable {Γ : Type} [Group Γ] {C : Subgroup Γ}

theorem map_subtype_le_sup_inf_centralizer {K A : Subgroup Γ} (hKC : K ≤ C) {E₀ : Subgroup ↥C}
    (hE₀ : E₀ ≤ K.subgroupOf C ⊔ (A.subgroupOf C ⊓
      Subgroup.centralizer ((K.subgroupOf C : Subgroup ↥C) : Set ↥C))) :
    E₀.map C.subtype ≤ K ⊔ (A ⊓ Subgroup.centralizer (K : Set Γ)) := by
  refine (Subgroup.map_mono hE₀).trans ?_
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKC]
  refine sup_le_sup_left ?_ _
  rintro _ ⟨x, ⟨hxA, hxC⟩, rfl⟩
  refine ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hxC ⟨k, hKC hk⟩
    (show (⟨k, hKC hk⟩ : ↥C) ∈ K.subgroupOf C from hk)
  exact congrArg Subtype.val h1

theorem isE27_map_subtype {E₀ : Subgroup ↥C} (hE₀ : Late.IsE27 E₀) :
    Late.IsE27 (E₀.map C.subtype) :=
  ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 C.subtype E₀ hE₀.1,
    (Subgroup.card_map_of_injective C.subtype_injective).trans hE₀.2⟩

theorem coe_mem_normalizer_map_subtype {E₀ : Subgroup ↥C} {g : ↥C}
    (hg : g ∈ Subgroup.normalizer (E₀ : Set ↥C)) :
    (g : Γ) ∈ Subgroup.normalizer ((E₀.map C.subtype : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨x₀, hx₀, rfl⟩
    exact ⟨g * x₀ * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x₀).mp hx₀, rfl⟩
  · rintro ⟨y₀, hy₀, hy⟩
    have hxC : x ∈ C := by
      have h1 : (g : Γ) * x * (g : Γ)⁻¹ ∈ C := hy ▸ y₀.2
      have h2 := C.mul_mem (C.mul_mem (C.inv_mem g.2) h1) g.2
      simpa [mul_assoc] using h2
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    have hy' : g * ⟨x, hxC⟩ * g⁻¹ = y₀ := Subtype.ext hy.symm
    exact (Subgroup.mem_normalizer_iff.mp hg ⟨x, hxC⟩).mpr (hy' ▸ hy₀)

theorem mem_normalizer_zpowers_of_coe {d g : ↥C}
    (hg : (g : Γ) ∈ Subgroup.normalizer (Subgroup.zpowers (d : Γ) : Set Γ)) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set ↥C) := by
  have hz : ∀ w : ↥C, w ∈ Subgroup.zpowers d ↔ (w : Γ) ∈ Subgroup.zpowers (d : Γ) := by
    intro w
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [hz z, hz (g * z * g⁻¹)]
  simpa using Subgroup.mem_normalizer_iff.mp hg (z : Γ)

end Transport

section Fix

theorem item4_25Fix_of_le_E (h425 : Sec4.Item4_25Fix) {Γ : Type} [Group Γ] [Finite Γ]
    (C : Subgroup Γ) (hC4 : SectionFourHyp ↥C)
    (hCr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 3) (hCθ : aschbacherSolvableCore 3 ↥C = ⊥)
    {A L K : Subgroup Γ} {d : Γ} (hAC : A ≤ C) (hLC : L ≤ C) (hA : Late.IsE27 A)
    (hW : ∀ g ∈ C, g ∈ Subgroup.normalizer (A : Set Γ) →
      g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set Γ))
    (hLq : IsQuasisimple ↥L) (hLn : C ≤ Subgroup.normalizer (L : Set Γ))
    (hKL : K ≤ L ⊓ Subgroup.centralizer {d}) (hKq : IsQuasisimple ↥K)
    (hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal)
    (htype : Sec4.IsExtOf (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6))
      (Multiplicative (ZMod 3)))
    (hcent : A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) = Subgroup.zpowers d) :
    K = L ∨ Nonempty (↥L ≃* Blueprint.NativeSporadic.J2) ∨
      (∃ p f : ℕ, Sec4.IsSLThreePiAt ↥K (p ^ f)) ∨
      (Nonempty (↥L ≃* Blueprint.NativeSporadic.M24) ∧
        ∃ E : Subgroup Γ, E ≤ C ∧ E ≤ K ⊔ (A ⊓ Subgroup.centralizer (K : Set Γ)) ∧
          Late.IsE27 E ∧ ∃ g ∈ C, g ∈ Subgroup.normalizer (E : Set Γ) ∧
            g ∉ Subgroup.normalizer (Subgroup.zpowers d : Set Γ)) ∨
      Sec4.IsExtOf ↥K (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3)) := by
  have hdA : d ∈ A := by
    have h : d ∈ A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) := hcent ▸ Subgroup.mem_zpowers d
    exact h.1
  have hdC : d ∈ C := hAC hdA
  have hKC : K ≤ C := (hKL.trans inf_le_left).trans hLC
  set d' : ↥C := ⟨d, hdC⟩ with hd'def
  set L' : Subgroup ↥C := L.subgroupOf C with hL'def
  set A' : Subgroup ↥C := A.subgroupOf C with hA'def
  set K' : Subgroup ↥C := K.subgroupOf C with hK'def
  set M : Subgroup ↥C := L' ⊓ Subgroup.centralizer ({d'} : Set ↥C) with hMdef
  have hK'M : K' ≤ M := by
    intro x hx
    have hx' : (x : Γ) ∈ L ⊓ Subgroup.centralizer {d} := hKL hx
    refine ⟨hx'.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.2
  set K₀ : Subgroup ↥M := K'.subgroupOf M with hK₀def
  let eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  let eK : ↥K₀ ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hK'M).trans (Subgroup.subgroupOfEquivOfLe hKC)
  have hA' : Late.IsE27 A' := by
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
    · have h := congrArg Subtype.val
        (hA.1.1.is_comm.comm ⟨((x : ↥C) : Γ), x.2⟩ ⟨((y : ↥C) : Γ), y.2⟩)
      simpa using h
    · simpa using hA.1.2 _ hx
    · rw [← hA.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hLn
  have hL' : IsComponent L' := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq,
    hL'n.isSubnormal⟩
  have hW' : Subgroup.normalizer (A' : Set ↥C) ≤
      Subgroup.normalizer (Subgroup.zpowers d' : Set ↥C) := by
    intro x hx
    have hxA : (x : Γ) ∈ Subgroup.normalizer (A : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨z, hAC hz⟩).mp hz
        exact h1
      · intro hz
        have hzC : z ∈ C := by
          have h1 : (x : Γ) * z * (x : Γ)⁻¹ ∈ C := hAC hz
          have h2 := C.mul_mem (C.mul_mem (C.inv_mem x.2) h1) x.2
          simpa [mul_assoc] using h2
        exact (Subgroup.mem_normalizer_iff.mp hx ⟨z, hzC⟩).mpr hz
    exact mem_normalizer_zpowers_of_coe (hW x x.2 hxA)
  have hfmem : ∀ m : ↥M, ((m : ↥C) : Γ) ∈ L ⊓ Subgroup.centralizer {d} := by
    intro m
    refine ⟨m.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp m.2.2)
  let f : ↥M →* ↥(L ⊓ Subgroup.centralizer {d}) :=
    MonoidHom.codRestrict (C.subtype.comp M.subtype) (L ⊓ Subgroup.centralizer {d}) hfmem
  have hK₀eq : K₀ = (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).comap f := by
    ext m
    exact Iff.rfl
  have hK₀ : IsComponent K₀ := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq,
    hK₀eq ▸ hKsub.comap f⟩
  have hK'eq : K₀.map M.subtype = K' := Subgroup.map_subgroupOf_eq_of_le hK'M
  have htype' : Sec4.IsSLThreePi (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) ∨
      Sec4.IsExtOf (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) (alternatingGroup (Fin 6))
        (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) (alternatingGroup (Fin 7))
        (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) Blueprint.NativeSporadic.M22
        (Multiplicative (ZMod 3)) :=
    Or.inr (Or.inl (Sec4.IsExtOf.of_mulEquiv (quotThetaEquiv eK).symm htype))
  have hcent' : A' ⊓ (K₀.map M.subtype ⊓
      Subgroup.centralizer ((K₀.map M.subtype : Subgroup ↥C) : Set ↥C)) =
      Subgroup.zpowers d' := by
    rw [hK'eq]
    ext x
    constructor
    · rintro ⟨hxA, hxK, hxc⟩
      have hx : (x : Γ) ∈ A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) := by
        refine ⟨hxA, hxK, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hxc ⟨k, hKC hk⟩ (show _ ∈ K' from hk)
        exact congrArg Subtype.val h1
      rw [hcent] at hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [hd'def] using hn)⟩
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hd : d ^ n ∈ A ⊓ (K ⊓ Subgroup.centralizer (K : Set Γ)) :=
        hcent ▸ zpow_mem (Subgroup.mem_zpowers d) n
      refine ⟨?_, ?_, ?_⟩
      · show ((d' ^ n : ↥C) : Γ) ∈ A
        simpa [hd'def] using hd.1
      · show ((d' ^ n : ↥C) : Γ) ∈ K
        simpa [hd'def] using hd.2.1
      · show d' ^ n ∈ Subgroup.centralizer (K' : Set ↥C)
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        have h1 := Subgroup.mem_centralizer_iff.mp hd.2.2 (k : Γ) hk
        simpa [hd'def] using h1
  rcases h425 ↥C hC4 A' hA' hCr hCθ L' hL' d' K₀ hK₀ (K₀.map M.subtype) rfl htype' hcent' hW'
    with h1 | ⟨-, ⟨φ⟩⟩ | ⟨p, f, hSL, -⟩ | ⟨⟨-, ⟨φ⟩⟩ | ⟨h7, -⟩, E₀, hE₀le, hE₀, hE₀N⟩
  · left
    rw [hK'eq] at h1
    have h' := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_of_le_left hKC, inf_of_le_left hLC] at h'
  · exact Or.inr (Or.inl ⟨eL.symm.trans φ⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨p, f, ?_⟩))
    obtain ⟨F, hF, hFf, hcase⟩ := hSL
    refine ⟨F, hF, hFf, ?_⟩
    rcases hcase with ⟨h1, h2, ⟨ψ⟩⟩ | ⟨h1, h2, ⟨ψ⟩⟩
    · exact Or.inl ⟨h1, h2, ⟨eK.symm.trans ψ⟩⟩
    · exact Or.inr ⟨h1, h2, ⟨eK.symm.trans ψ⟩⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨eL.symm.trans φ⟩, E₀.map C.subtype,
      Subgroup.map_subtype_le _, ?_, isE27_map_subtype hE₀, ?_⟩)))
    · rw [hK'eq] at hE₀le
      exact map_subtype_le_sup_inf_centralizer hKC hE₀le
    · obtain ⟨g₀, hg₀E, hg₀d⟩ := Set.not_subset.mp hE₀N
      exact ⟨g₀, g₀.2, coe_mem_normalizer_map_subtype hg₀E,
        fun hg => hg₀d (mem_normalizer_zpowers_of_coe hg)⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Sec4.IsExtOf.of_mulEquiv eK h7))))

end Fix

section Elem

variable {Γ : Type} [Group Γ]

theorem isElemAbelian_zpowers_sup {E : Subgroup Γ} {z : Γ} (hE : CFSG.Open.IsElemAbelian 3 E)
    (hz3 : z ^ 3 = 1) (hzC : z ∈ Subgroup.centralizer (E : Set Γ)) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z ⊔ E) := by
  have hcomm : ∀ e ∈ E, ∀ k : ℤ, e * z ^ k = z ^ k * e := fun e he k =>
    (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hzC e he) k).eq
  have hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨f, hf⟩)
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨k, e, he, hx⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hzC x.2
    obtain ⟨l, f, hf, hy⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hzC y.2
    show (x : Γ) * y = y * x
    rw [hx, hy]
    calc z ^ k * e * (z ^ l * f) = z ^ k * (e * z ^ l) * f := by group
      _ = z ^ k * (z ^ l * e) * f := by rw [hcomm e he l]
      _ = z ^ (k + l) * (e * f) := by rw [zpow_add]; group
      _ = z ^ (l + k) * (f * e) := by rw [add_comm, hEc e he f hf]
      _ = z ^ l * (z ^ k * f) * e := by rw [zpow_add]; group
      _ = z ^ l * (f * z ^ k) * e := by rw [hcomm f hf k]
      _ = z ^ l * f * (z ^ k * e) := by group
  · obtain ⟨k, e, he, rfl⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hzC hx
    have h1 : (z ^ k * e) ^ 3 = (z ^ k) ^ 3 * e ^ 3 := Commute.mul_pow (hcomm e he k).symm 3
    have h2 : (z ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    rw [h1, h2, hE.2 e he, mul_one]

variable [Finite Γ]

theorem card_zpowers_sup {E : Subgroup Γ} {z : Γ} (hz3 : z ^ 3 = 1)
    (hzC : z ∈ Subgroup.centralizer (E : Set Γ)) (hzE : z ∉ E) :
    Nat.card (Subgroup.zpowers z ⊔ E : Subgroup Γ) = 3 * Nat.card E := by
  have h := KFacts.KS14.card_eq_three_mul_card_inf hzC hzE hz3 le_rfl
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  rwa [inf_of_le_right le_sup_right] at h

end Elem

theorem exists_lift_elemAbelian {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : p.Prime) (φ : X →* Y) (hker : ¬ p ∣ Nat.card φ.ker) {U : Subgroup X}
    {E : Subgroup Y} (hEU : E ≤ U.map φ) (hE : CFSG.Open.IsElemAbelian p E) {D : Subgroup X}
    (hDU : D ≤ U) (hDE : D.map φ ≤ E) (hD : IsPGroup p D) :
    ∃ T : Subgroup X, T ≤ U ∧ D ≤ T ∧ T.map φ = E ∧ Nat.card T = Nat.card E ∧
      CFSG.Open.IsElemAbelian p T := by
  have : Fact p.Prime := ⟨hp⟩
  set W : Subgroup X := U ⊓ E.comap φ with hW
  let ψ : W →* E := (φ.comp W.subtype).codRestrict E fun w => w.2.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨u, hu, hue⟩ := hEU e.2
    exact ⟨⟨u, hu, show φ u ∈ E by rw [hue]; exact e.2⟩, Subtype.ext hue⟩
  have hDW : D ≤ W := fun x hx => ⟨hDU hx, hDE ⟨x, hx, rfl⟩⟩
  obtain ⟨T, hDT⟩ := (hD.comap_of_injective W.subtype W.subtype_injective).exists_le_sylow
  have hEp : IsPGroup p E := Sec5.isPGroup_of_isElemAbelian hE
  have htop : ((T.mapSurjective hψ : Sylow p E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  set T' : Subgroup X := (T : Subgroup W).map W.subtype with hT'
  have hT'p : IsPGroup p T' := T.isPGroup'.map _
  have hT'K : T' ⊓ φ.ker = ⊥ := Sec4.inf_eq_bot_of_isPGroup_of_not_dvd hp hT'p hker
  have hinj : ∀ x ∈ T', ∀ y ∈ T', φ x = φ y → x = y := by
    intro x hx y hy hxy
    have hm : x * y⁻¹ ∈ T' ⊓ φ.ker :=
      ⟨T'.mul_mem hx (T'.inv_mem hy), show φ (x * y⁻¹) = 1 by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]⟩
    rw [hT'K, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  have hT'E : T'.map φ = E := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
      exact w.2.2
    · intro e he
      have : (⟨e, he⟩ : E) ∈ ((T.mapSurjective hψ : Sylow p E) : Subgroup E) := htop ▸ trivial
      rw [Sylow.coe_mapSurjective] at this
      obtain ⟨w, hw, hwe⟩ := this
      exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩
  have hcard : Nat.card T' = Nat.card E := by
    rw [← hT'E]
    exact Nat.card_congr (Equiv.ofBijective (fun x : T' => (⟨φ x, ⟨x, x.2, rfl⟩⟩ : T'.map φ))
      ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy)),
        fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩)
  have hT'e : CFSG.Assembly.IsElemAbelian p T' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj _ (T'.mul_mem a.2 b.2) _ (T'.mul_mem b.2 a.2) ?_)⟩⟩,
      fun x hx => hinj _ (T'.pow_mem hx p) _ T'.one_mem ?_⟩
    · have ha : φ a ∈ E := hT'E ▸ Subgroup.mem_map_of_mem φ a.2
      have hb : φ b ∈ E := hT'E ▸ Subgroup.mem_map_of_mem φ b.2
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨φ a, ha⟩ ⟨φ b, hb⟩)
    · have hx' : φ x ∈ E := hT'E ▸ Subgroup.mem_map_of_mem φ hx
      rw [map_pow, hE.2 _ hx', map_one]
  have hT'U : T' ≤ U := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2.1
  refine ⟨T', hT'U, fun x hx => ⟨⟨x, hDW hx⟩, hDT hx, rfl⟩, hT'E, hcard, hT'e⟩

section Ambient

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation in
theorem mem_normalizer_alpha_of_le {A Y R : Subgroup G} [(ker148 A Y).Normal]
    (hR3 : IsPGroup 3 R) (hRM : R ≤ Y ⊔ A) {r : G} (hrA : r ∈ A)
    (hW : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers r : Set G))
    {g : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hg : g ∈ Subgroup.normalizer (img148 A Y R : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    g ∈ Subgroup.normalizer
      (Subgroup.zpowers (alpha148 A Y r hrA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) g
  set R' : Subgroup ↥(Y ⊔ A) := R.subgroupOf (Y ⊔ A) with hR'
  set C := ker148 A Y with hC
  have hR3' : IsPGroup 3 R' :=
    hR3.comap_of_injective (Y ⊔ A).subtype (Y ⊔ A).subtype_injective
  have hC3 : ¬ 3 ∣ Nat.card C := Main148.not_three_dvd_card_ker148
  have hpre : ∀ y : ↥(Y ⊔ A), y ∈ C ⊔ R' ↔ QuotientGroup.mk' C y ∈ img148 A Y R := by
    intro y
    have h1 : (img148 A Y R).comap (QuotientGroup.mk' C) = R' ⊔ C := by
      rw [img148, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← Subgroup.mem_comap, h1]
    exact ⟨fun h => (sup_comm C R').le h, fun h => (sup_comm R' C).le h⟩
  have hxn : x ∈ Subgroup.normalizer ((C ⊔ R' : Subgroup ↥(Y ⊔ A)) : Set ↥(Y ⊔ A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hpre, hpre, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hg _
  obtain ⟨o, ho, hon⟩ := StrongThree.exists_mul_mem_normalizer_of_sup hR3' hC3 hxn
  have hoxR : ((o * x : ↥(Y ⊔ A)) : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzM : z ∈ Y ⊔ A := hRM hz
      have h1 := (Subgroup.mem_normalizer_iff.mp hon ⟨z, hzM⟩).mp hz
      exact h1
    · intro hz
      set w : ↥(Y ⊔ A) := o * x with hw
      have hzM : z ∈ Y ⊔ A := by
        have h1 : (w : G) * z * (w : G)⁻¹ ∈ Y ⊔ A := hRM hz
        have h2 := (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem w.2) h1) w.2
        simpa [mul_assoc] using h2
      have h1 := (Subgroup.mem_normalizer_iff.mp hon ⟨z, hzM⟩).mpr hz
      exact h1
  have hoxr := hW hoxR
  have hoxr' : ((o * x : ↥(Y ⊔ A)) : G) * r * ((o * x : ↥(Y ⊔ A)) : G)⁻¹ ∈
      Subgroup.zpowers r :=
    (Subgroup.mem_normalizer_iff.mp hoxr r).mp (Subgroup.mem_zpowers r)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hoxr'
  have hoα : QuotientGroup.mk' C o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  refine mem_normalizer_of_conj_mem fun u hu => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  refine Subgroup.mem_zpowers_iff.mpr ⟨k * m, ?_⟩
  have hconj : QuotientGroup.mk' C x * alpha148 A Y r hrA * (QuotientGroup.mk' C x)⁻¹ =
      alpha148 A Y r hrA ^ k := by
    have e1 : QuotientGroup.mk' C (o * x) = QuotientGroup.mk' C x := by
      rw [map_mul, hoα, one_mul]
    rw [← e1, alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul, ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk.symm)
  rw [zpow_mul, ← hconj, conj_zpow]


theorem card_le_nine_of_le_lb {A B Lb E : Subgroup G} {b d : G} (hc : IsLBConfig A B b d Lb)
    (hEL : E ≤ Lb) (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φJ⟩ := Item148HJ.j2_of_isLBConfig hc
  have hZ : Subgroup.center (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) = ⊥ :=
    KFacts.KS14.center_eq_bot_of_mulEquiv φJ
      (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
  set θ := aschbacherSolvableCore 3 ↥Lb with hθ
  set f : ↥Lb →* MulAut (↥Lb ⧸ θ) :=
    (MulAut.conj : (↥Lb ⧸ θ) →* MulAut (↥Lb ⧸ θ)).comp (QuotientGroup.mk' θ) with hf
  set E' := E.subgroupOf Lb with hE'
  have hinj : ∀ x ∈ E', f x = 1 → x = 1 := by
    intro x hx hfx
    have hcen : (QuotientGroup.mk' θ x) ∈ Subgroup.center (↥Lb ⧸ θ) := by
      rw [Subgroup.mem_center_iff]
      intro q
      have h1 := DFunLike.congr_fun hfx q
      simp only [hf, MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply,
        MulAut.one_apply] at h1
      calc q * QuotientGroup.mk' θ x = QuotientGroup.mk' θ x * q * (QuotientGroup.mk' θ x)⁻¹ *
            QuotientGroup.mk' θ x := by rw [h1]
        _ = QuotientGroup.mk' θ x * q := by group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    exact eq_one_of_mem_aschbacherSolvableCore hcen (Subtype.ext (by simpa using hE.2 _ hx))
  have hcard : Nat.card (E'.map f) = Nat.card E' := card_map_eq_of_ker148 hinj
  have h9 := Sec10.Item1015Proof.card_le_nine_of_mulAut_J2 φJ (E'.map f)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f E'
      (isElemAbelian_subgroupOf hE))
  rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at h9
  exact h9

theorem pRank_le_two_of_le_lb {A B Lb S : Subgroup G} {b d : G} (hc : IsLBConfig A B b d Lb)
    (hSL : S ≤ Lb) : CFSG.Open.pRank 3 S ≤ 2 := by
  obtain ⟨E, hES, hE, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three S
  have h9 := card_le_nine_of_le_lb hc (hES.trans hSL) hE
  rw [hEcard] at h9
  by_contra hlt
  have : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 S := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Ambient

section Conj

variable {G : Type} [Group G]

theorem mem_conjugate_iff' {H : Subgroup G} {x y : G} :
    y ∈ conjugate H x ↔ x * y * x⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hy
    refine ⟨x * y * x⁻¹, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_conjugate_iff {H : Subgroup G} {x w : G} :
    w ∈ Subgroup.normalizer ((conjugate H x : Subgroup G) : Set G) ↔
      x * w * x⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, mem_conjugate_iff']
  constructor
  · intro hw z
    have h1 := hw (x⁻¹ * z * x)
    have e1 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
    have e2 : x * (w * (x⁻¹ * z * x) * w⁻¹) * x⁻¹ = x * w * x⁻¹ * z * (x * w * x⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro hw z
    have h1 := hw (x * z * x⁻¹)
    have e2 : x * w * x⁻¹ * (x * z * x⁻¹) * (x * w * x⁻¹)⁻¹ = x * (w * z * w⁻¹) * x⁻¹ := by
      group
    rw [e2] at h1
    exact h1

theorem conjugate_zpowers (d x : G) :
    conjugate (Subgroup.zpowers d) x = Subgroup.zpowers (x⁻¹ * d * x⁻¹⁻¹) := by
  rw [conjugate, MonoidHom.map_zpowers]
  rfl

end Conj

section Main

variable {G : Type} [Group G] [Finite G]

open Desc143X Main148 HJRes148

theorem false_of_m24 (h425 : Sec4.Item4_25Fix)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement) (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L B Lb : Subgroup G} {c a b d : G} (h : One A c L a b d B Lb)
    {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 a) (hJX : lB A B ≤ X)
    (φ24 : ↥X ⧸ aschbacherSolvableCore 3 ↥X ≃* Blueprint.NativeSporadic.M24) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h.std.isE27'
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  obtain ⟨hb1, hd1⟩ := h.config.ne_one h.hyp hA
  have hbB : b ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := h.hyp.1 hdB
  have hbA : b ∈ A := h.hyp.1 hbB
  have hd3 : d ^ 3 = 1 := hA3 d hdA
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  set J := lB A B with hJdef
  have hJeq : J = inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) :=
    h.lB_eq
  set Y := Subgroup.centralizer ({a} : Set G) with hYdef
  have hAY' : A ≤ Y := Desc143X.le_centralizer_of_isE27 hA h.mem
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hAY'.trans Subgroup.le_normalizer
  let := ker148_normal hAY
  have hYA : Y ⊔ A = Y := sup_of_le_left hAY'
  have hYtop : Y ≠ ⊤ :=
    centralizer_singleton_ne_top h.std.isSimpleGroup h.std.nonabelian h.ne_one
  have hYsc : Y ∈ scriptY A := ⟨hYtop, hAY⟩
  have hX' : X ∈ thetaComponentsIn Y := hX
  have hXY : X ≤ Y := le_of_mem_thetaComponentsIn hX'
  have hXM : X ≤ Y ⊔ A := hXY.trans le_sup_left
  have hJM : J ≤ Y ⊔ A := hJX.trans hXM
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hAY'.trans (h.le_normalizer hX hJX)
  obtain ⟨hdL, S, hdS, hSd⟩ := h.config.2.2.2.2
  have hdJ : d ∈ J := hJeq ▸ Item148HJ.inf_le_residual h.std h.hyp h.config ⟨hdA, hdL⟩
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h3J : 3 ∣ Nat.card J := by
    rw [← hod, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdJ)
  have h3X : 3 ∣ Nat.card X := h3J.trans (Subgroup.card_dvd_of_le hJX)
  have hXs : ¬ Group.IsSolvable ↥Y := by
    intro hYs
    have hXs' : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXY)
    have : Nontrivial ↥X := ⟨⟨⟨d, hJX hdJ⟩, 1, fun h1 => hd1 (congrArg Subtype.val h1)⟩⟩
    exact Sec4.Item419ThetaProof.not_isSolvable_of_isPerfect
      (isPerfect_of_mem_thetaComponentsIn hX') hXs'
  obtain ⟨hC4, -⟩ := hyp429In148_of h41 G A c L h.std Y hYsc hXs X hX' hAX h3X
  obtain ⟨hXq, hXθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hX' h3X
  set C := img148 A Y (X ⊔ A) with hCdef
  have hCeq : C = img148 A Y X ⊔ img148 A Y A := img148_sup hXM le_sup_right
  have hAαXα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y X : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAX
  have hAα3 : ∀ x ∈ img148 A Y A, x ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥C = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαXα hAα3 hXθ
  have hAC : img148 A Y A ≤ C := img148_mono le_sup_right
  have hLC : img148 A Y X ≤ C := img148_mono le_sup_left
  have hLn : C ≤ Subgroup.normalizer (img148 A Y X : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαXα
  have hXArank : CFSG.Open.pRank 3 (X ⊔ A) ≤ 3 :=
    pRank_le_three h134 h48 h le_sup_right (sup_le hXY hAY')
  have hCle : CFSG.Open.pRank 3 C ≤ 3 := by
    have h2 := Sec4.pRank_map_le_of_not_dvd Nat.prime_three (QuotientGroup.mk' (ker148 A Y))
      (by rw [QuotientGroup.ker_mk']; exact not_three_dvd_card_ker148)
      ((X ⊔ A).subgroupOf (Y ⊔ A))
    have h3 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three (Y ⊔ A).subtype (Y ⊔ A).subtype_injective ((X ⊔ A).subgroupOf (Y ⊔ A))
    rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hXM le_sup_right)] at h3
    exact h2.trans (h3.trans hXArank)
  have hCr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) = 3 := by
    apply le_antisymm
    · have h1 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
        Nat.prime_three C.subtype C.subtype_injective ⊤
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      exact h1.trans hCle
    · have hE := isE27_subgroupOf hAC (img148_isE27 hA)
      refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3
        Nat.prime_three ⊤) ⟨(img148 A Y A).subgroupOf C, le_top, hE.1, ?_⟩
      rw [hE.2]
      norm_num
  have hYd := h.lB_mem
  have hM4 : SectionFourHyp ↥(Y ⊔ A) :=
    h.std.toTheoremFourHyp.sectionFourHyp (by rw [hYA]; exact hYtop)
  have hθ := theta_commutator_le hGW hAY hM4 hdA hd3 hYd hX' hJX h3J
  obtain ⟨hKle, hKsub, hKp, hKθ, ⟨η⟩⟩ := ydAlpha_facts hAY hdA hd3 hYd hX' hJX hAX h3J hθ
  have hJ2 := Item148HJ.j2_of_isLBConfig h.config
  obtain ⟨-, htc, -, -⟩ := residual_facts h415 hJ2 hdL hd1 ⟨S, hdS, hSd⟩
  rw [← hJeq] at htc
  have htcα := KFacts.KS14.isTripleCover_congr η htc
  have hKq' : IsQuasisimple (↥(img148 A Y J) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y J)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv η (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd)
  have : Group.IsPerfect ↥(img148 A Y J) := hKp
  have hKq : IsQuasisimple ↥(img148 A Y J) :=
    (CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(img148 A Y J)))
      (QuotientGroup.mk'_surjective _) (by rwa [QuotientGroup.ker_mk'])).mpr hKq'
  have hdα1 : alpha148 A Y d hdA ≠ 1 := alpha148_ne_one hdA hd1 hd3
  have hdα3 : alpha148 A Y d hdA ^ 3 = 1 := hAα3 _ (alpha148_mem_img148 hdA)
  have hJd : J ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hJeq]
    exact Item148HJ.residual_le_centralizer_singleton Lb d
  have hcent : img148 A Y A ⊓ (img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) =
      Subgroup.zpowers (alpha148 A Y d hdA) := by
    have hle : Subgroup.zpowers (alpha148 A Y d hdA) ≤ img148 A Y A ⊓ (img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) := by
      rw [Subgroup.zpowers_le]
      refine ⟨alpha148_mem_img148 hdA, mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdJ,
        rfl⟩, ?_⟩
      show alpha148 A Y d hdA ∈
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨j, hj, hjJ, rfl⟩ := mem_img148_iff.mp hx
      rw [alpha148_eq_mk', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJd hjJ)
    have hcard := card_le_three_of_le_center (E := img148 A Y A ⊓ (img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)))) inf_le_right
      (fun x hx => hAα3 x hx.1) htcα.1
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime hdα3 hdα1]
    exact hcard
  have hW := normalizer_le_normalizer_zpowers_d h134 h48 h.std h.hyp h.config
  have hW' : ∀ g ∈ C, g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      g ∈ Subgroup.normalizer
        (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun g _ hg => mem_normalizer_alpha_of (isPGroup_three_of_pow148 hA3) hdA hW hg
  obtain ⟨ηX⟩ := nonempty_quotTheta_equiv_img148 (A := A) (Y := Y) hX' h3X
  rcases item4_25Fix_of_le_E h425 C hC4 hCr hCθ hAC hLC (img148_isE27 hA) hW' hXq hLn hKle hKq
      hKsub htcα.isExtOf hcent with h1 | ⟨⟨φ⟩⟩ | ⟨p, f, hSL⟩ |
      ⟨-, E, hEC, hEle, hE27, g, -, hgE, hgd⟩ | h7
  ·
    have hXeq := eq_sup_theta_of_img148_eq hX' h3X hXM hJX h1
    have h1080 := Desc143X.card_quotTheta_eq h hJX hXeq
    rw [Nat.card_congr φ24.toEquiv, CFSG.Sporadic.Mathieu.card_M24] at h1080
    norm_num at h1080
  ·
    have hc := Nat.card_congr ((φ24.symm.trans (ηX.trans φ)).toEquiv)
    rw [CFSG.Sporadic.Mathieu.card_M24, CFSG.Sporadic.J2.card_J2] at hc
    norm_num at hc
  · exact false_of_isSLThreePiAt hKθ htcα.isExtOf hSL
  ·
    set Kα := img148 A Y J with hKα
    set aα := alpha148 A Y a h.mem with haαdef
    set dα := alpha148 A Y d hdA with hdαdef
    have hJY : J ≤ Y := hJX.trans hXY
    have hJLb : J ≤ Lb := hJeq ▸ Item148HJ.residual_le Lb d
    have haαC : ∀ x : ↥(Y ⊔ A) ⧸ ker148 A Y, x * aα = aα * x := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) x
      rw [haαdef, alpha148_eq_mk', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hy : (y : G) ∈ Y := sup_le le_rfl hAY' y.2
      exact Subgroup.mem_centralizer_singleton_iff.mp hy
    have haα3 : aα ^ 3 = 1 := hAα3 _ (alpha148_mem_img148 h.mem)
    have haαC' : ∀ H : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), aα ∈ Subgroup.centralizer (H : Set _) :=
      fun H => Subgroup.mem_centralizer_iff.mpr fun x _ => haαC x
    have haαCmem : aα ∈ C := hAC (alpha148_mem_img148 h.mem)
    have hdαK : dα ∈ Kα := mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hdJ, rfl⟩
    have hdαcent : dα ∈ Subgroup.centralizer (Kα : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      have h1 : dα ∈ Subgroup.zpowers dα := Subgroup.mem_zpowers dα
      rw [← hcent] at h1
      exact h1.2.2
    have hKle2 : CFSG.Open.pRank 3 Kα ≤ 2 := by
      have h2 := Sec4.pRank_map_le_of_not_dvd Nat.prime_three (QuotientGroup.mk' (ker148 A Y))
        (by rw [QuotientGroup.ker_mk']; exact not_three_dvd_card_ker148) (J.subgroupOf (Y ⊔ A))
      have h3 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
        Nat.prime_three (Y ⊔ A).subtype (Y ⊔ A).subtype_injective (J.subgroupOf (Y ⊔ A))
      rw [Subgroup.map_subgroupOf_eq_of_le hJM] at h3
      exact h2.trans (h3.trans (pRank_le_two_of_le_lb h.config hJLb))
    have haJ : a ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJY hj)
    have hAαle : img148 A Y A ≤ Subgroup.zpowers aα ⊔ Kα := by
      intro x hx
      obtain ⟨α, hα, hαA, rfl⟩ := mem_img148_iff.mp hx
      have hαs : α ∈ Subgroup.zpowers a ⊔ J := h.le_sup_of_le le_rfl hαA
      obtain ⟨k, j, hj, hαkj⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup haJ hαs
      have hjM : j ∈ Y ⊔ A := hJM hj
      have e1 : QuotientGroup.mk' (ker148 A Y) ⟨α, hα⟩ =
          aα ^ k * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ := by
        rw [haαdef, alpha148_eq_mk', ← map_zpow, ← map_mul]
        congr 1
        apply Subtype.ext
        simp [hαkj]
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _
        (Subgroup.mem_zpowers _) k)) (Subgroup.mem_sup_right (mem_img148_iff.mpr ⟨j, hjM, hj, rfl⟩))
    have hEle' : E ≤ Subgroup.zpowers aα ⊔ Kα :=
      hEle.trans (sup_le le_sup_right (inf_le_left.trans hAαle))
    have haE : aα ∈ E := by
      by_contra haE
      have hS := isElemAbelian_zpowers_sup hE27.1 haα3 (haαC' E)
      have hcard := card_zpowers_sup haα3 (haαC' E) haE
      rw [hE27.2] at hcard
      have hSC : Subgroup.zpowers aα ⊔ E ≤ C := sup_le (Subgroup.zpowers_le.mpr haαCmem) hEC
      have := Sec5.le_pRank_of_elemAbelian (k := 4) Nat.prime_three hSC hS
        (by rw [hcard]; norm_num)
      omega
    have haK : aα ∉ Kα := by
      intro haK
      have hEK : E ≤ Kα := hEle'.trans (sup_le (Subgroup.zpowers_le.mpr haK) le_rfl)
      have := Sec5.le_pRank_of_elemAbelian (k := 3) Nat.prime_three hEK hE27.1
        (by rw [hE27.2]; norm_num)
      omega
    have h9' : Nat.card ↥(E ⊓ Kα) = 9 := by
      have := KFacts.KS14.card_eq_three_mul_card_inf (haαC' Kα) haK haα3 hEle' haE
      rw [hE27.2] at this
      omega
    set E₉ := E ⊓ Kα with hE₉
    have h9 : Nat.card E₉ = 9 := h9'
    have hE₉ab : CFSG.Open.IsElemAbelian 3 E₉ := isElemAbelian_of_le148 hE27.1 inf_le_left
    have hdE₉ : dα ∈ E₉ := by
      by_contra hdE
      have hdc : dα ∈ Subgroup.centralizer (E₉ : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right) hdαcent
      have hS := isElemAbelian_zpowers_sup hE₉ab hdα3 hdc
      have hcard := card_zpowers_sup hdα3 hdc hdE
      rw [h9] at hcard
      have hSK : Subgroup.zpowers dα ⊔ E₉ ≤ Kα := sup_le (Subgroup.zpowers_le.mpr hdαK) inf_le_right
      have := Sec5.le_pRank_of_elemAbelian (k := 3) Nat.prime_three hSK hS (by rw [hcard]; norm_num)
      omega
    set dM : ↥(Y ⊔ A) := ⟨d, Subgroup.mem_sup_right hdA⟩ with hdM
    have hdMJ : dM ∈ J.subgroupOf (Y ⊔ A) := hdJ
    have hDp : IsPGroup 3 (Subgroup.zpowers dM) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, hod]
    have hDE : (Subgroup.zpowers dM).map (QuotientGroup.mk' (ker148 A Y)) ≤ E₉ := by
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hdE₉
    obtain ⟨T, hTU, hDT, hTE, hTcard, hTab⟩ := exists_lift_elemAbelian Nat.prime_three
      (QuotientGroup.mk' (ker148 A Y))
      (by rw [QuotientGroup.ker_mk']; exact not_three_dvd_card_ker148)
      (U := J.subgroupOf (Y ⊔ A)) (E := E₉) inf_le_right hE₉ab
      (Subgroup.zpowers_le.mpr hdMJ) hDE hDp
    set F := T.map (Y ⊔ A).subtype with hFdef
    have hFJ : F ≤ J := by
      rw [hFdef, ← Subgroup.map_subgroupOf_eq_of_le hJM]
      exact Subgroup.map_mono hTU
    have hdF : d ∈ F := ⟨dM, hDT (Subgroup.mem_zpowers dM), rfl⟩
    have hFcard : Nat.card F = 9 := by
      rw [hFdef, Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective, hTcard, h9]
    have hFsub : F.subgroupOf (Y ⊔ A) = T := by
      rw [hFdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        (Y ⊔ A).subtype_injective]
    have hFα : img148 A Y F = E₉ := by
      rw [img148, hFsub, hTE]
    have hS' := Item148HJ.sec14Std_of_isLBConfig h.std h.config
    obtain ⟨hbL, -, hAb⟩ := j2_point_facts hS'.toSec13Data hJ2
    have hLbmem : Lb ∈ lA A b := h.config.2.2.1 ▸ Set.mem_singleton Lb
    have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hLbmem.1
    have hbLC : b ∈ Subgroup.centralizer (Lb : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLbC hy)
    have hbFC : b ∈ Subgroup.centralizer (F : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hFJ.trans hJLb)) hbLC
    have hbF : b ∉ F := fun hb => hbL (hJLb (hFJ hb))
    set R := Subgroup.zpowers b ⊔ F with hRdef
    have hR27 : Nat.card R = 27 := by
      rw [hRdef, card_zpowers_sup hb3 hbFC hbF, hFcard]
    have hRle : R ≤ Subgroup.zpowers b ⊔ Lb := sup_le_sup_left (hFJ.trans hJLb) _
    have hAle : A ≤ Subgroup.zpowers b ⊔ Lb := hAb ▸ sup_le_sup_left inf_le_right _
    have hbR : b ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
    have hdR : d ∈ R := Subgroup.mem_sup_right hdF
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
    obtain ⟨x, hxL, hRA⟩ := KFacts.KS14.j2_exists_conjugate_of_card_twentySeven_of_quot h415
      (L := Lb) (N := aschbacherSolvableCore 3 ↥Lb) hθ3 hJ2 hbLC hbL hb3 hAle hRle
      hbA hbR hA.2 hR27
    have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by rw [hR27]; norm_num)
    have hxinvN : x⁻¹ ∈ Subgroup.normalizer (Lb : Set G) :=
      Subgroup.le_normalizer (Lb.inv_mem hxL)
    set d' := x⁻¹ * d * x⁻¹⁻¹ with hd'def
    have hd'L : d' ∈ Lb :=
      Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hxL) hdL) (Lb.inv_mem (Lb.inv_mem hxL))
    have hd'R : d' ∈ R := by
      rw [hRA]
      exact ⟨d, hdA, rfl⟩
    have hd'1 : d' ≠ 1 := by
      intro h1
      apply hd1
      calc d = x * d' * x⁻¹ := by rw [hd'def]; group
        _ = 1 := by rw [h1]; group
    have hc₂ := Item134SylowBarProof.central_conj hxinvN hdL ⟨S, hdS, hSd⟩ hd'L
    have hzz := Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ2 hRp hdR hd'R
      hdL hd'L hd1 hd'1 ⟨S, hdS, hSd⟩ hc₂
    have hNR : Subgroup.normalizer (R : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      intro w hw
      rw [hRA, mem_normalizer_conjugate_iff] at hw
      have h2 : w ∈ Subgroup.normalizer
          ((conjugate (Subgroup.zpowers d) x : Subgroup G) : Set G) :=
        mem_normalizer_conjugate_iff.mpr (hW hw)
      rw [conjugate_zpowers, ← hzz] at h2
      exact h2
    have hRM : R ≤ Y ⊔ A :=
      sup_le ((Subgroup.zpowers_le.mpr hbA).trans le_sup_right) (hFJ.trans hJM)
    have had : a * d = d * a := congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, h.mem⟩ ⟨d, hdA⟩)
    have hbα : alpha148 A Y b hbA ∈ E := by
      have hbB' : b ∈ Subgroup.closure {d, a} := h.closure_d_a ▸ hbB
      rw [closure_pair_eq_sup, sup_comm] at hbB'
      obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup had hbB'
      have e1 : alpha148 A Y b hbA = aα ^ i * dα ^ j := by
        rw [haαdef, hdαdef, alpha148_eq_mk', alpha148_eq_mk', alpha148_eq_mk', ← map_zpow,
          ← map_zpow, ← map_mul]
        congr 1
        apply Subtype.ext
        simp [hij]
      rw [e1]
      exact E.mul_mem (E.zpow_mem haE i) (E.zpow_mem hdE₉.1 j)
    have hRαle : img148 A Y R ≤ E := by
      intro y hy
      obtain ⟨r, hr, hrR, rfl⟩ := mem_img148_iff.mp hy
      obtain ⟨k, f, hf, hrkf⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup hbFC hrR
      have hfM : f ∈ Y ⊔ A := hJM (hFJ hf)
      have e1 : QuotientGroup.mk' (ker148 A Y) ⟨r, hr⟩ =
          alpha148 A Y b hbA ^ k * QuotientGroup.mk' (ker148 A Y) ⟨f, hfM⟩ := by
        rw [alpha148_eq_mk', ← map_zpow, ← map_mul]
        congr 1
        apply Subtype.ext
        simp [hrkf]
      rw [e1]
      refine E.mul_mem (E.zpow_mem hbα k) ?_
      have hfα : QuotientGroup.mk' (ker148 A Y) ⟨f, hfM⟩ ∈ img148 A Y F :=
        mem_img148_iff.mpr ⟨f, hfM, hf, rfl⟩
      rw [hFα] at hfα
      exact hfα.1
    have hRαcard : Nat.card (img148 A Y R) = 27 := by
      rw [img148, card_map_eq_of_ker148, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv,
        hR27]
      intro y hy hy1
      rw [mk'_ker148_eq_one_iff] at hy1
      obtain ⟨k, hk⟩ := hRp ⟨(y : G), hy⟩
      exact Subtype.ext (eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) hy1
        (k := k) (by simpa using congrArg Subtype.val hk))
    have hRαE : img148 A Y R = E :=
      Subgroup.eq_of_le_of_card_ge hRαle (by rw [hE27.2, hRαcard])
    apply hgd
    exact mem_normalizer_alpha_of_le hRp hRM hdA hNR (g := g) (by rw [hRαE]; exact hgE)
  · exact false_of_isExtOf_seven htcα.isExtOf h7

theorem step143HJCompM24_of (h425 : Sec4.Item4_25Fix)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement) (h134 : Item134)
    (h48 : Sec4.Item4_8) : Step143HJCompM24 := by
  intro G _ _ A c L hS a ha ha1 hΩ B b d Lb hB haB hc hne X hX hJX ⟨φ⟩
  exact false_of_m24 h425 h41 hGW h134 h48 ⟨hS, ha, ha1, hΩ, hB, haB, hc, hne⟩ hX hJX φ

theorem step143HJCompOne_of_item4_25Fix'
    (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement) : Step143HJCompOne :=
  step143HJCompOne_of h425 h41 hGW h134 h48 (step143HJCompRank_of h134 h48) step143HJObs
    (step143HJCompM24_of h425 h41 hGW h134 h48)

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
