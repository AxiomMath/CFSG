module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux2
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.LieType.Steinberg.CentralExt.SUThree
import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
  CFSG.RankThree.PartOne.S15K Matrix

private theorem ggNSLie_ker_proj_comp_le_center {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2] {m : ℕ} {lab : LargeEvenLabel}
    (hSU : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) = SUid (unitaryInvolution K 2 lab.n) m) :
    ((LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))).comp
        (MulEquiv.subgroupCongr hSU.symm).toMonoidHom).ker ≤
      Subgroup.center (Su K 2 lab.n m) := by
  intro x hx
  let e : Su K 2 lab.n m ≃* ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    MulEquiv.subgroupCongr hSU.symm
  change LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) (e x) = 1 at hx
  have h1 : (e x : ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n))) ∈
      (CFSG.Open.StatedScalars (Fin m) K).subgroupOf
        (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    (QuotientGroup.eq_one_iff (e x)).mp hx
  have h3 : (e x : ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n))) ∈
      Subgroup.center ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    scalars_le_center_statedSU h1
  rw [Subgroup.mem_center_iff] at h3 ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact h3 (e y)

private theorem ggNSLie_ker_comp_le_center {G : Type} [Group G] {X : Subgroup G}
    {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
    {m : ℕ} {lab : LargeEvenLabel}
    (hSU : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) = SUid (unitaryInvolution K 2 lab.n) m)
    (α : ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) →* ↥X)
    (η : ↥X →* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)))
    (hαη : ∀ s, η (α s) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) s) :
    (α.comp (MulEquiv.subgroupCongr hSU.symm).toMonoidHom).ker ≤
      Subgroup.center (Su K 2 lab.n m) := by
  intro x hx
  apply ggNSLie_ker_proj_comp_le_center hSU
  rw [MonoidHom.mem_ker] at hx ⊢
  have hx' : α ((MulEquiv.subgroupCongr hSU.symm) x) = 1 := hx
  show LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))
    ((MulEquiv.subgroupCongr hSU.symm) x) = 1
  rw [← hαη ((MulEquiv.subgroupCongr hSU.symm) x), hx', map_one]

private theorem ggNSLie_conj_SUid_exists {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2] {m f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {g : GL (Fin m) K}
    (hgu : ggIsUnitaryMat (p := 2) (f := f) g) :
    ∃ c : Su K 2 f m →* Su K 2 f m,
      ∀ x, (c x : GL (Fin m) K) = g * (x : GL (Fin m) K) * g⁻¹ := by
  refine ⟨MonoidHom.mk' (fun x => ⟨g * (x : GL (Fin m) K) * g⁻¹,
    conj_mem_SUid (isUnitaryInvolution_unitaryInvolution hK).invol hgu x.2⟩) ?_,
    fun x => rfl⟩
  intro x y
  apply Subtype.ext
  show g * ((x * y : Su K 2 f m) : GL (Fin m) K) * g⁻¹ =
    (g * (x : GL (Fin m) K) * g⁻¹) * (g * (y : GL (Fin m) K) * g⁻¹)
  rw [Subgroup.coe_mul]
  group

private theorem ggNSLie_acts_of_lift {G : Type} [Group G] {Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] {m : ℕ} {lab : LargeEvenLabel}
    [Fact (Nat.Prime 2)] [CharP K 2]
    (hK : Nat.card K = (2 ^ lab.n) ^ 2) (h4m : 4 ≤ m)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)))
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)))
        (LargeEvenGUSet (Fin m) K (2 ^ lab.n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hSU : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) = SUid (unitaryInvolution K 2 lab.n) m)
    (α : Su K 2 lab.n m →* ↥X)
    (hαπ : ∀ s, θ (QuotientGroup.mk (α s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))
        ((MulEquiv.subgroupCongr hSU.symm) s)) :
    GGActsUnitarily (p := 2) (f := lab.n) (X.subtype.comp α) Bs := by
  intro b hb; obtain ⟨φ, hφI, hInd⟩ := hbs b hb
  obtain ⟨A, hAgu, hgraph⟩ := hφI
  obtain ⟨g, hgu, hconj⟩ := ggNSLieN3A_gu_rescale hK hAgu
  have hbN : b ∈ Subgroup.normalizer (X : Set G) := hBsN hb; refine ⟨g, hgu, fun x => ?_⟩
  obtain ⟨c, hc⟩ := ggNSLie_conj_SUid_exists hK hgu
  let τ₁ : Su K 2 lab.n m →* ↥X :=
    MonoidHom.mk' (fun x => ⟨b * ((α x : ↥X) : G) * b⁻¹,
      (Subgroup.mem_normalizer_iff.mp hbN _).1 (α x).2⟩)
      (by
        intro x y
        apply Subtype.ext
        show b * ((α (x * y) : ↥X) : G) * b⁻¹ =
          (b * ((α x : ↥X) : G) * b⁻¹) * (b * ((α y : ↥X) : G) * b⁻¹)
        rw [map_mul, Subgroup.coe_mul]
        group)
  let τ₂ : Su K 2 lab.n m →* ↥X := α.comp c
  have hmod : ∀ u, QuotientGroup.mk' (Subgroup.center ↥X) (τ₁ u) =
      QuotientGroup.mk' (Subgroup.center ↥X) (τ₂ u) := by
    intro u
    apply θ.injective
    apply φ.injective
    have h1 : φ (θ (QuotientGroup.mk (τ₁ u))) = θ (QuotientGroup.mk (α u)) :=
      hInd (τ₁ u) (α u) (by
        show ((α u : ↥X) : G) = b⁻¹ * (b * ((α u : ↥X) : G) * b⁻¹) * b
        group)
    have h2 : φ (θ (QuotientGroup.mk (τ₂ u))) = θ (QuotientGroup.mk (α u)) := by
      have e1 : θ (QuotientGroup.mk (τ₂ u)) =
          LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))
            ((MulEquiv.subgroupCongr hSU.symm) (c u)) := hαπ (c u)
      have e2 : θ (QuotientGroup.mk (α u)) =
          LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))
            ((MulEquiv.subgroupCongr hSU.symm) u) := hαπ u
      rw [e1, e2]
      exact hgraph ((MulEquiv.subgroupCongr hSU.symm) (c u))
        ((MulEquiv.subgroupCongr hSU.symm) u)
        (by
          show (((MulEquiv.subgroupCongr hSU.symm) u : ↥(LargeEvenSUGroup (Fin m) K
            (2 ^ lab.n))) : GL (Fin m) K) = A *
            (((MulEquiv.subgroupCongr hSU.symm) (c u) : ↥(LargeEvenSUGroup (Fin m) K
              (2 ^ lab.n))) : GL (Fin m) K) * A⁻¹
          rw [MulEquiv.subgroupCongr_apply, MulEquiv.subgroupCongr_apply, hc u]
          exact (hconj (u : GL (Fin m) K)).symm)
    exact h1.trans h2.symm
  have heq := eq_of_perfect_of_map_eq (QuotientGroup.mk' (Subgroup.center ↥X))
    (by rw [QuotientGroup.ker_mk']) (isPerfect_SUid
      (isUnitaryInvolution_unitaryInvolution hK) (by omega)
      (fun h3 => absurd h3 (by omega))) τ₁ τ₂ hmod x
  exact ⟨c x, hc x, congrArg Subtype.val heq⟩

theorem ggNSLie_lift_of_ne
    {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {lab : LargeEvenLabel} {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = (2 ^ lab.n) ^ 2) (h4m : 4 ≤ m) (hmrank : m = lab.rank + 1)
    (hne : ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))
    (hperf : commutator X = ⊤)
    (η : ↥X →* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)))
    (hηsurj : Function.Surjective η) (hηker : η.ker ≤ Subgroup.center ↥X) :
    ∃ α : ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) →* ↥X,
      Function.Surjective α ∧ ∀ s, η (α s) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  have hm4 : ¬ (m = 4 ∧ lab.n = 1) := by
    rintro ⟨hm, hn1⟩
    exact hne ⟨hn1, Or.inl (by omega)⟩
  have hm6 : ¬ (m = 6 ∧ lab.n = 1) := by
    rintro ⟨hm, hn1⟩
    exact hne ⟨hn1, Or.inr (by omega)⟩
  have hSU : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) = SUid (unitaryInvolution K 2 lab.n) m := by
    have h2 : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) =
        CFSG.Open.StatedSU m (2 ^ lab.n) K := rfl
    rw [h2]
    exact (SUid_eq_statedSU (F := K) (p := 2) (f := lab.n) hK m).symm
  let e : Su K 2 lab.n m ≃* ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    MulEquiv.subgroupCongr hSU.symm
  let ρ : Su K 2 lab.n m →* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    (LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))).comp e.toMonoidHom
  have hρsurj : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp e.surjective
  have hρker : ρ.ker ≤ Subgroup.center (Su K 2 lab.n m) :=
    ggNSLie_ker_proj_comp_le_center hSU
  have hclosed : ∀ (E : Type) [Group E] [Finite E] (π' : E →* Su K 2 lab.n m),
      Function.Surjective π' → π'.ker ≤ Subgroup.center E →
      ∃ s : Su K 2 lab.n m →* E, ∀ g, π' (s g) = g :=
    fun E _ _ π' hπ' hc' =>
      (ggSU_central_extension_splits K lab.n m hK h4m hm4 hm6 E π' hπ' hc').imp
        (fun s hs g => DFunLike.congr_fun hs g)
  obtain ⟨α, hαsurj, -, hαπ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin
      hclosed hperf η hηsurj hηker ρ hρsurj hρker
  refine ⟨α.comp e.symm.toMonoidHom, hαsurj.comp e.symm.surjective, fun s => ?_⟩
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ρ, e,
    MulEquiv.apply_symm_apply] using hαπ (e.symm s)

theorem ggNSLie_cover_of_esu_of_lift
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {P : ℕ → LargeEvenLabel → Prop}
    (hP : ∀ p lab, P p lab → ggRowP_ESU p lab)
    (h : GGInnerDiagOnLabel P p Bs X)
    (hlift : ∀ (lab : LargeEvenLabel) (m : ℕ) (K : Type) [Field K] [Finite K],
      P p lab → Nat.card K = (2 ^ lab.n) ^ 2 → 4 ≤ m → m = lab.rank + 1 →
      commutator X = ⊤ →
      ∀ η : ↥X →* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)),
        Function.Surjective η → η.ker ≤ Subgroup.center ↥X →
        ∃ α : ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) →* ↥X,
          Function.Surjective α ∧ ∀ s, η (α s) =
            LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) s) :
    ∃ (lab : LargeEvenLabel) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ)
      (ψ : Su K 2 f n →* G), P p lab ∧ n = lab.rank + 1 ∧ f = lab.n ∧
      Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
        p ∣ 2 ^ f + 1 ∧ GGActsUnitarily (p := 2) (f := f) ψ Bs ∧
        ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X) := by
  classical
  obtain ⟨K, hf, hfin, lab, m, θ, hK, h4m, hmrank, hSide, hdvd, hperf, hlab, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore h hP
  have hlabel : ∃ b : ℕ, m = b + 1 ∧ GGHasLabel ⟨.twA, b, lab.n⟩ (↥X ⧸ Subgroup.center ↥X) := by
    obtain ⟨b, hb⟩ : ∃ b, m = b + 1 := ⟨lab.rank, hmrank⟩
    subst hb
    exact ⟨b, rfl, K, hf, hfin, hK, ⟨θ⟩⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := lab.n) hK
  have hSU : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) = SUid (unitaryInvolution K 2 lab.n) m := by
    have h2 : LargeEvenSUGroup (Fin m) K (2 ^ lab.n) =
        CFSG.Open.StatedSU m (2 ^ lab.n) K := rfl
    rw [h2]
    exact (SUid_eq_statedSU (F := K) (p := 2) (f := lab.n) hK m).symm
  let e : Su K 2 lab.n m ≃* ↥(LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    MulEquiv.subgroupCongr hSU.symm
  let π : ↥X →* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hπsurj : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker ≤ Subgroup.center ↥X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change θ (QuotientGroup.mk x) = 1 at hx
    exact (QuotientGroup.eq_one_iff x).mp (θ.map_eq_one_iff.mp hx)
  obtain ⟨α, hαsurj, hαη⟩ := hlift lab m K hSide hK h4m hmrank hperf π hπsurj hπker
  let α' : Su K 2 lab.n m →* ↥X := α.comp e.toMonoidHom
  have hα'surj : Function.Surjective α' := hαsurj.comp e.surjective
  have hα'ker : α'.ker ≤ Subgroup.center (Su K 2 lab.n m) :=
    ggNSLie_ker_comp_le_center hSU α π hαη
  have hacts : GGActsUnitarily (p := 2) (f := lab.n) (X.subtype.comp α') Bs :=
    ggNSLie_acts_of_lift hK h4m θ hBsN hbs hSU α' (fun s => hαη (e s))
  refine ⟨lab, K, hf, hfin, inferInstance, lab.n, m, X.subtype.comp α', hSide, hmrank, rfl, hK,
    h4m, ?_, ?_, hdvd, hacts, hlabel⟩
  · intro x hx
    apply hα'ker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (α' x).2
    · intro hg
      obtain ⟨x, hx⟩ := hα'surj ⟨g, hg⟩
      exact ⟨x, by rw [MonoidHom.comp_apply, hx]; rfl⟩

theorem ggNSLie_cover_of_esu_pred
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {P : ℕ → LargeEvenLabel → Prop}
    (hP : ∀ p lab, P p lab → ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))
    (h : GGInnerDiagOnLabel P p Bs X) :
    ∃ (lab : LargeEvenLabel) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ)
      (ψ : Su K 2 f n →* G), P p lab ∧ n = lab.rank + 1 ∧ f = lab.n ∧
      Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
        p ∣ 2 ^ f + 1 ∧ GGActsUnitarily (p := 2) (f := f) ψ Bs ∧
        ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X) :=
  ggNSLie_cover_of_esu_of_lift (fun p lab hl => (hP p lab hl).1) h
    (fun lab m K _ _ hlab hK h4m hmrank hperf η hηsurj hηker =>
      ggNSLie_lift_of_ne hK h4m hmrank (hP p lab hlab).2 hperf η hηsurj hηker)

theorem ggNSLie_cover_of_esu
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f n : ℕ) (ψ : Su K 2 f n →* G),
      Nat.card K = (2 ^ f) ^ 2 ∧ 4 ≤ n ∧ ψ.ker ≤ Subgroup.center (Su K 2 f n) ∧ ψ.range = X ∧
        p ∣ 2 ^ f + 1 ∧ GGActsUnitarily (p := 2) (f := f) ψ Bs ∧
        ∃ b : ℕ, n = b + 1 ∧ GGHasLabel ⟨.twA, b, f⟩ (↥X ⧸ Subgroup.center ↥X) := by
  obtain ⟨-, K, hf, hfin, hc, f, n, ψ, -, -, -, hcard, h4n, hker, hrange, hdvd, hacts, hlabel⟩ :=
    ggNSLie_cover_of_esu_pred
      (P := fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))
      (fun _ _ hh => hh) h
  exact ⟨K, hf, hfin, hc, f, n, ψ, hcard, h4n, hker, hrange, hdvd, hacts, hlabel⟩

end CFSG.StandardType

end
