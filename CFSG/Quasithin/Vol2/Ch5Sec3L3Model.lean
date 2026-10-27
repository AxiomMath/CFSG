module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Am
public import CFSG.Quasithin.Background.F1AmalgamRestrict
import CFSG.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.H13.F431.L3 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

section Model

variable {P : Type} [Group P] [Finite P] {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P}

theorem le_perfectCore_normalizer (hD : L3DData U R₁ R₂ B₀ s₁ s₂) :
    R₁ ≤ perfectCore (Subgroup.normalizer (R₁ : Set P)) := by
  set N := Subgroup.normalizer (R₁ : Set P) with hN
  set X := perfectCore N with hX
  have hXN : X ≤ N := perfectCore_le N
  have hXnorm : N ≤ Subgroup.normalizer (X : Set P) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore N)
  have hXne : X ≠ ⊥ := fun h => hD.half₁.nonsolv ((isSolvable_iff_perfectCore_eq_bot N).mpr h)
  have hXR : X ⊓ R₁ ≠ ⊥ := by
    intro h0
    apply hXne
    rw [eq_bot_iff]
    intro x hx
    have hxR : x ∈ R₁ := by
      refine hD.borel.cent₁ x fun r hr => ?_
      have h1 : x * r * x⁻¹ * r⁻¹ ∈ X ⊓ R₁ := by
        refine ⟨?_, ?_⟩
        · have : r * x⁻¹ * r⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp (hXnorm (Subgroup.le_normalizer hr)) _).mp
              (X.inv_mem hx)
          have := X.mul_mem hx this
          simpa [mul_assoc] using this
        · have : x * r * x⁻¹ ∈ R₁ := (Subgroup.mem_normalizer_iff.mp (hXN hx) r).mp hr
          exact R₁.mul_mem this (R₁.inv_mem hr)
      rw [h0, Subgroup.mem_bot] at h1
      have h2 : x * r * x⁻¹ = r := by
        rw [mul_inv_eq_one] at h1
        exact h1
      calc x * r = x * r * x⁻¹ * x := by group
        _ = r * x := by rw [h2]
    have : x ∈ X ⊓ R₁ := ⟨hx, hxR⟩
    rwa [h0] at this
  obtain ⟨r₀, hr₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXR
  have hr₀X : (r₀ : P) ∈ X := (Subgroup.mem_inf.mp r₀.2).1
  have hr₀R : (r₀ : P) ∈ R₁ := (Subgroup.mem_inf.mp r₀.2).2
  have hr₀1' : (r₀ : P) ≠ 1 := fun h => hr₀1 (Subtype.ext h)
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1]; exact X.one_mem
  have hconj : ∀ {m y : P}, y ≠ 1 → m * y * m⁻¹ ≠ 1 := fun {m y} hy h => hy (by
    have := congrArg (fun z => m⁻¹ * z * m) h
    simpa [mul_assoc] using this)
  obtain ⟨m, hm, hmr⟩ := hD.half₁.cov r hr hr1
  obtain ⟨m₀, hm₀, hm₀r⟩ := hD.half₁.cov (r₀ : P) hr₀R hr₀1'
  obtain ⟨b, hb, hbr⟩ := hD.trans _ hm₀r (hconj hr₀1') _ hmr (hconj hr1)
  have hbN : b ∈ N := hD.borel.lt₁.le (hD.B₀_le hb)
  have hgN : m⁻¹ * b * m₀ ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hm) hbN) hm₀
  have e : r = (m⁻¹ * b * m₀) * (r₀ : P) * (m⁻¹ * b * m₀)⁻¹ := by
    calc r = m⁻¹ * (m * r * m⁻¹) * m := by group
      _ = m⁻¹ * (b * (m₀ * (r₀ : P) * m₀⁻¹) * b⁻¹) * m := by rw [hbr]
      _ = (m⁻¹ * b * m₀) * (r₀ : P) * (m⁻¹ * b * m₀)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hXnorm hgN) _).mp hr₀X

theorem pCoreOf_perfectCore_normalizer (hD : L3DData U R₁ R₂ B₀ s₁ s₂) :
    pCoreOf 2 (perfectCore (Subgroup.normalizer (R₁ : Set P))) = R₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (R₁ : Set P) with hN
  set X := perfectCore N with hX
  have hXN : X ≤ N := perfectCore_le N
  apply le_antisymm
  · rw [← hD.borel.core₁]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXN) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    exact (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore N)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_perfectCore_normalizer hD)
      hXN hD.borel.isPGroup₁

omit [Finite P] in
theorem normalizer_inf_normalizer (hD : L3DData U R₁ R₂ B₀ s₁ s₂) :
    Subgroup.normalizer (R₁ : Set P) ⊓ Subgroup.normalizer (R₂ : Set P) =
      Subgroup.normalizer (U : Set P) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [← hD.borel.sup, Subgroup.map_sup, h1, h2]
  · exact le_inf hD.borel.lt₁.le hD.borel.lt₂.le

omit [Finite P] in
theorem pCoreOf_normalizer_inf (hD : L3DData U R₁ R₂ B₀ s₁ s₂) :
    pCoreOf 2 (Subgroup.normalizer (R₁ : Set P) ⊓ Subgroup.normalizer (R₂ : Set P)) = U := by
  rw [normalizer_inf_normalizer hD]
  exact Borel252.pCoreOf_normalizer_sylow hD.borel.sylow

theorem isSolvable_normalizer_U (hD : L3DData U R₁ R₂ B₀ s₁ s₂) (hB : Group.IsSolvable B₀) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set P)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 U := hD.borel.sylow.2.1
  have : Group.IsNilpotent U := hUp.isNilpotent
  have : Group.IsSolvable U := inferInstance
  have hle : Subgroup.normalizer (U : Set P) ≤ U ⊔ B₀ := by
    intro h hh
    obtain ⟨u, hu, b, hb, rfl⟩ := hD.mul h hh
    exact (U ⊔ B₀).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hb)
  have hs : Group.IsSolvable ↥(U ⊔ B₀) := A3.isSolvable_sup_of_le_normalizer hD.B₀_le
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

end Model

theorem isSolvable_torus3 (F : Type) [Field F] : Group.IsSolvable ↥(P3.torus3 F) := by
  have : Group.IsSolvable (Fˣ × Fˣ) := Group.isSolvable_of_comm fun a b => mul_comm a b
  exact Group.isSolvable_of_surjective (f := (P3.dHom F).rangeRestrict)
    (P3.dHom F).rangeRestrict_surjective

theorem mem_pCoreOf_iff_of_equiv {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {C : Subgroup Y} (e : ↥A ≃* ↥C) (a : ↥A) :
    (a : X) ∈ pCoreOf 2 A ↔ ((e a : ↥C) : Y) ∈ pCoreOf 2 C := by
  unfold pCoreOf
  rw [show (a : X) = A.subtype a from rfl, show ((e a : ↥C) : Y) = C.subtype (e a) from rfl,
    Subgroup.mem_map_iff_mem A.subtype_injective, Subgroup.mem_map_iff_mem C.subtype_injective,
    ← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]
  exact (Subgroup.mem_map_iff_mem e.injective).symm

section Transport

variable {G : Type} [Group G]

abbrev sec53G1 (M L H B : Subgroup G) : Subgroup G := L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)

abbrev sec53G2 (M L H D : Subgroup G) : Subgroup G := D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H

structure L3Model (G₁ G₂ : Subgroup G) (F : Type) [Field F] [CharP F 2] where
  R₁ : Subgroup (projectiveSL 3 F)
  R₂ : Subgroup (projectiveSL 3 F)
  s₁ : projectiveSL 3 F
  s₂ : projectiveSL 3 F
  data : L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂
  radicals : (R₁ = Fin257.L3.V1 ∧ R₂ = Fin257.L3.V2) ∨ (R₁ = Fin257.L3.V2 ∧ R₂ = Fin257.L3.V1)
  iso : (RankTwoAmalgam.ofSubgroups G₁ G₂).Iso
    (RankTwoAmalgam.ofSubgroups (Subgroup.normalizer (R₁ : Set (projectiveSL 3 F)))
      (Subgroup.normalizer (R₂ : Set (projectiveSL 3 F))))

theorem exists_l3Model {M L H B D T : Subgroup G} {f : ℕ}
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ f ∧
      Nonempty (L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) := by
  obtain ⟨Y, _, hY, TY, M₁, M₂, hpair, ⟨Φ⟩⟩ := hty.1
  obtain ⟨-, F, hFf, hFfin, hFchar, hFcard, ⟨e1⟩⟩ := exists_equiv_projSL3 hY
  have hy1 := hpair.map e1
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1 (Fin257.L3.isSylowTwoOf_U (F := F))
  let E : Y ≃* projectiveSL 3 F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (projUnitriangular 3 F) (M₁.map E.toMonoidHom)
      (M₂.map E.toMonoidHom) := by
    have := hpair.map E
    have hTD : TY.map E.toMonoidHom = projUnitriangular 3 F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  have hq4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdata := l3DData_projectiveSL hq4
  let Ψ := F431.U42.Am.isoTrans Φ (F431.U42.Am.ofSubgroupsMapInj E.toMonoidHom E.injective M₁ M₂)
  refine ⟨F, hFf, hFfin, hFchar, hFcard, ?_⟩
  rcases Borel252.BorelData.yam_cases Borel252.L3.borelData_L3 no_normal_two_subgroup hy2 with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨{
      R₁ := Fin257.L3.V1
      R₂ := Fin257.L3.V2
      s₁ := _
      s₂ := _
      data := hdata
      radicals := Or.inl ⟨rfl, rfl⟩
      iso := F431.U42.Am.isoTrans Ψ (F431.U42.Am.ofSubgroupsCongr h1 h2) }⟩
  · exact ⟨{
      R₁ := Fin257.L3.V2
      R₂ := Fin257.L3.V1
      s₁ := _
      s₂ := _
      data := hdata.swap
      radicals := Or.inr ⟨rfl, rfl⟩
      iso := F431.U42.Am.isoTrans Ψ (F431.U42.Am.ofSubgroupsCongr h1 h2) }⟩

variable [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2]

namespace L3Model

omit [Finite G] in
theorem isSolvable_inf (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F) :
    Group.IsSolvable ↥(sec53G1 M L H B ⊓ sec53G2 M L H D) := by
  have h1 := isSolvable_normalizer_U Mo.data (isSolvable_torus3 F)
  have h2 : Group.IsSolvable ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) := by
    rw [normalizer_inf_normalizer Mo.data]
    exact h1
  exact Group.isSolvable_of_surjective (f := (isoφ12 Mo.iso).symm.toMonoidHom)
    (isoφ12 Mo.iso).symm.surjective

theorem perfectCore_G1 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    perfectCore (sec53G1 M L H B) = L := by
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hN := hyp.notation59
  have hBM : B ≤ M := hN.1.1.trans inf_le_left
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hsup : sec53G1 M L H B = L ⊔ ((sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) := sup_assoc _ _ _
  have hnorm : sec53G1 M L H B ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (inf_le_right.trans Subgroup.le_normalizer))
      (inf_le_left.trans (hBM.trans h.normal))
  have hAn : (L.subgroupOf (sec53G1 M L H B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr hnorm
  have hle : (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ≤ sec53G1 M L H B ⊓ sec53G2 M L H D :=
    sup_le (le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left))
      (le_inf le_sup_right (inf_le_right.trans le_sup_right))
  have := Mo.isSolvable_inf
  have hs : Group.IsSolvable ↥((sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact le_antisymm (perfectCore_le_of_sup_solvable hLG hAn hsup hs)
    (le_perfectCore_of_perfect hLG h.commutator_eq)

theorem perfectCore_G2 (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) : perfectCore (sec53G2 M L H D) = oTwoUpper H := by
  have hN := hyp.notation59
  have hDL : D ≤ L := hN.2.1.1.trans inf_le_left
  have hKG : oTwoUpper H ≤ sec53G2 M L H D := le_sup_right
  have hsup : sec53G2 M L H D = oTwoUpper H ⊔ (D ⊔ (sec52S M H ⊓ L)) := sup_comm _ _
  have hSH : sec52S M H ≤ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (M ⊓ H)).trans inf_le_right
  have hnorm : sec53G2 M L H D ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    sup_le (sup_le hyp.D_le (inf_le_left.trans (hSH.trans (le_normalizer_oTwoUpper H))))
      Subgroup.le_normalizer
  have hAn : ((oTwoUpper H).subgroupOf (sec53G2 M L H D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mpr hnorm
  have hle : D ⊔ (sec52S M H ⊓ L) ≤ sec53G1 M L H B ⊓ sec53G2 M L H D :=
    sup_le (le_inf (hDL.trans (le_sup_left.trans le_sup_left)) (le_sup_left.trans le_sup_left))
      (le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left))
  have := Mo.isSolvable_inf
  have hs : Group.IsSolvable ↥(D ⊔ (sec52S M H ⊓ L)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact le_antisymm (perfectCore_le_of_sup_solvable hKG hAn hsup hs)
    (le_perfectCore_of_perfect hKG hty.2.1.2.1.2.1)

theorem pCoreOf_inf (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    pCoreOf 2 (sec53G1 M L H B ⊓ sec53G2 M L H D) = sec53S T L := by
  obtain ⟨-, ⟨e1, e2, -, hST, -, hO2⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [sec53G1, sec53G2, e1, e2, ← hO2, hST]

theorem mem_L_iff (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (x : ↥(sec53G1 M L H B)) :
    (x : G) ∈ L ↔ ((isoφ1 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) :
      projectiveSL 3 F) ∈ perfectCore (Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F))) := by
  rw [← mem_perfectCore_iff_of_equiv (isoφ1 Mo.iso) x, Mo.perfectCore_G1 hyp]

theorem mem_K_iff (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (x : ↥(sec53G2 M L H D)) :
    (x : G) ∈ oTwoUpper H ↔
      ((isoφ2 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ perfectCore (Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) := by
  rw [← mem_perfectCore_iff_of_equiv (isoφ2 Mo.iso) x, Mo.perfectCore_G2 hyp hty]

theorem mem_pCoreOf_L_iff (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (x : ↥(sec53G1 M L H B)) :
    (x : G) ∈ pCoreOf 2 L ↔
      ((isoφ1 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ Mo.R₁ := by
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  let e := restrictEquiv (isoφ1 Mo.iso) hLG (perfectCore_le _) (Mo.mem_L_iff hyp)
  have hcore := pCoreOf_perfectCore_normalizer Mo.data
  constructor
  · intro hx
    have hxL : (x : G) ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
    have h1 := (mem_pCoreOf_iff_of_equiv e ⟨x, hxL⟩).mp hx
    rw [hcore, coe_restrictEquiv] at h1
    exact h1
  · intro hx
    have hxX : ((isoφ1 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ perfectCore (Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F))) :=
      le_perfectCore_normalizer Mo.data hx
    have hxL : (x : G) ∈ L := (Mo.mem_L_iff hyp x).mpr hxX
    refine (mem_pCoreOf_iff_of_equiv e ⟨x, hxL⟩).mpr ?_
    rw [hcore, coe_restrictEquiv]
    exact hx

theorem mem_pCoreOf_K_iff (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (x : ↥(sec53G2 M L H D)) :
    (x : G) ∈ pCoreOf 2 (oTwoUpper H) ↔
      ((isoφ2 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ Mo.R₂ := by
  have hKG : oTwoUpper H ≤ sec53G2 M L H D := le_sup_right
  let e := restrictEquiv (isoφ2 Mo.iso) hKG (perfectCore_le _) (Mo.mem_K_iff hyp hty)
  have hcore := pCoreOf_perfectCore_normalizer Mo.data.swap
  constructor
  · intro hx
    have hxK : (x : G) ∈ oTwoUpper H := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have h1 := (mem_pCoreOf_iff_of_equiv e ⟨x, hxK⟩).mp hx
    rw [hcore, coe_restrictEquiv] at h1
    exact h1
  · intro hx
    have hxX : ((isoφ2 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) ∈ perfectCore (Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) :=
      le_perfectCore_normalizer Mo.data.swap hx
    have hxK : (x : G) ∈ oTwoUpper H := (Mo.mem_K_iff hyp hty x).mpr hxX
    refine (mem_pCoreOf_iff_of_equiv e ⟨x, hxK⟩).mpr ?_
    rw [hcore, coe_restrictEquiv]
    exact hx

omit [Finite F] in
theorem mem_S_iff (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (h527 : Stmt5_2_7) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (x : ↥(sec53G1 M L H B ⊓ sec53G2 M L H D)) :
    (x : G) ∈ sec53S T L ↔
      ((isoφ12 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
        Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) : projectiveSL 3 F) ∈
        projUnitriangular 3 F := by
  rw [← pCoreOf_inf h527 hyp, mem_pCoreOf_iff_of_equiv (isoφ12 Mo.iso) x,
    pCoreOf_normalizer_inf Mo.data]

omit [Finite G] [Finite F] in
theorem coe_iso_agree (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (x : G) (h₁ : x ∈ sec53G1 M L H B) (h₂ : x ∈ sec53G2 M L H D) :
    ((isoφ1 Mo.iso ⟨x, h₁⟩ : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) :
      projectiveSL 3 F) =
      ((isoφ2 Mo.iso ⟨x, h₂⟩ : ↥(Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F)))) :
        projectiveSL 3 F) :=
  (coe_isoφ12_eq_φ1 Mo.iso ⟨x, Subgroup.mem_inf.mpr ⟨h₁, h₂⟩⟩).symm.trans
    (coe_isoφ12_eq_φ2 Mo.iso ⟨x, Subgroup.mem_inf.mpr ⟨h₁, h₂⟩⟩)

omit [Finite G] [Finite F] in
theorem mem_G2_of_mem_normalizer (Mo : L3Model (sec53G1 M L H B) (sec53G2 M L H D) F)
    (x : ↥(sec53G1 M L H B))
    (hx : ((isoφ1 Mo.iso x : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)))) :
      projectiveSL 3 F) ∈ Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) :
    (x : G) ∈ sec53G2 M L H D := by
  set y : ↥(Subgroup.normalizer (Mo.R₁ : Set (projectiveSL 3 F)) ⊓
      Subgroup.normalizer (Mo.R₂ : Set (projectiveSL 3 F))) :=
    ⟨_, Subgroup.mem_inf.mpr ⟨(isoφ1 Mo.iso x).2, hx⟩⟩ with hy
  set x' := (isoφ12 Mo.iso).symm y with hx'
  have h1 := coe_isoφ12_eq_φ1 Mo.iso x'
  rw [hx', MulEquiv.apply_symm_apply, hy] at h1
  have h2 : (⟨(x' : G), (Subgroup.mem_inf.mp x'.2).1⟩ : ↥(sec53G1 M L H B)) = x :=
    (isoφ1 Mo.iso).injective (Subtype.ext h1.symm)
  rw [← h2]
  exact (Subgroup.mem_inf.mp x'.2).2

end L3Model

end Transport

end CFSG.Quasithin.H13.Sec53L3
