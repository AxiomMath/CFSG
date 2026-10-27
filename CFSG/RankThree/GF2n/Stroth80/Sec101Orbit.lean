module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec56Frame
public import CFSG.RankThree.GF2n.Stroth80.Sec56CentIndex

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] noncomputable def Ctx.commHom (hc : Ctx M Q Z B) {y : G} (hy : y ∈ Q)
    {V : Subgroup G} (hV : V ≤ Q) : ↥V →* ↥Z where
  toFun x := ⟨⁅(x : G), y⁆, hc.hyp.toHyp79.comm_mem_V (hV x.2) hy⟩
  map_one' := by
    ext
    simp [commutatorElement_def]
  map_mul' x x' := by
    ext
    show ⁅(x : G) * (x' : G), y⁆ = ⁅(x : G), y⁆ * ⁅(x' : G), y⁆
    have hcomm : (x : G) * ⁅(x' : G), y⁆ = ⁅(x' : G), y⁆ * (x : G) :=
      (hc.hyp.toHyp79.V_central
        (hc.hyp.toHyp79.comm_mem_V (hV x'.2) hy) (hV x.2)).symm
    have hZcomm : ⁅(x : G), y⁆ * ⁅(x' : G), y⁆ =
        ⁅(x' : G), y⁆ * ⁅(x : G), y⁆ :=
      hc.hyp.toHyp79.V_central
        (hc.hyp.toHyp79.comm_mem_V (hV x.2) hy)
        (hc.hyp.Z_normal.1 (hc.hyp.toHyp79.comm_mem_V (hV x'.2) hy))
    rw [show ⁅(x : G) * (x' : G), y⁆ =
      (x : G) * ⁅(x' : G), y⁆ * (x : G)⁻¹ * ⁅(x : G), y⁆ by
        simp only [commutatorElement_def]; group]
    rw [show (x : G) * ⁅(x' : G), y⁆ * (x : G)⁻¹ = ⁅(x' : G), y⁆ by
      rw [hcomm, mul_inv_cancel_right]]
    exact hZcomm.symm

private theorem commHom_surjective (hc : Ctx M Q Z B) {y c : G} (hy : y ∈ Q) (hcB : c ∈ B)
    (hcy : c * y ≠ y * c) : Function.Surjective (hc.commHom hy hc.le) := by
  intro z
  obtain ⟨β, hβB, hβ⟩ := hc.exists_mem_comm_eq hcB hy hcy z.2
  exact ⟨⟨β, hβB⟩, Subtype.ext hβ⟩

theorem Ctx.centralizes_of_comm (hc : Ctx M Q Z B) {y b : G} (hy : y ∈ Q) (hb : b ∈ B)
    (hb1 : b ≠ 1) (hyb : y * b = b * y) : ∀ c ∈ B, y * c = c * y := by
  by_contra hnot
  push Not at hnot
  obtain ⟨c, hcB, hcy⟩ := hnot
  have hcy' : c * y ≠ y * c := fun h => hcy h.symm
  let φ := hc.commHom hy hc.le
  have hsurj : Function.Surjective φ := commHom_surjective hc hy hcB hcy'
  have hcardBZ : Nat.card ↥B = Nat.card ↥Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  letI : Fintype ↥B := Fintype.ofFinite _
  letI : Fintype ↥Z := Fintype.ofFinite _
  have hFcard : Fintype.card ↥B = Fintype.card ↥Z := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardBZ
  let e : ↥B ≃ ↥Z := Fintype.equivOfCardEq hFcard
  have hinj : Function.Injective φ := Function.Surjective.injective_of_finite e hsurj
  have hker : φ ⟨b, hb⟩ = 1 := by
    ext
    show ⁅b, y⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr hyb.symm
  have hb1' : (⟨b, hb⟩ : ↥B) = 1 := hinj (by rw [hker, map_one])
  exact hb1 (congrArg Subtype.val hb1')


theorem IsRootB.isZConjugate (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) : Smith81.IsZConjugate Z E := by
  obtain ⟨m, -, hEB⟩ := hE
  obtain ⟨g, hg⟩ := hc.conj
  exact ⟨m * g, by rw [hEB, hg, conjSubgroup_mul]⟩

private theorem conj_inf_QB_of_mem_QB (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {c : G} (hcE : c ∈ QB E) :
    conjSubgroup c (Q ⊓ QB E) = Q ⊓ QB E := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSubgroup c _).ge
  intro x hx
  have hy : c⁻¹ * x * c ∈ Q ⊓ QB E := mem_conjSubgroup.mp hx
  obtain ⟨hyQ, hyQB⟩ := Subgroup.mem_inf.mp hy
  have hcomm : ⁅c, c⁻¹ * x * c⁆ ∈ E := (IsRootB.ctx hc hE).QB_comm_mem hcE hyQB
  have hx' : x = ⁅c, c⁻¹ * x * c⁆ * (c⁻¹ * x * c) := by
    rw [commutatorElement_def]; group
  rw [hx']
  exact Subgroup.mem_inf.mpr
    ⟨Q.mul_mem ((IsRootB.ctx hc hE).le hcomm) hyQ,
      (QB E).mul_mem
        (Smith81.IsZConjugate.le_QB_self hc.hyp (IsRootB.isZConjugate hc hE) hcomm)
        hyQB⟩

private theorem conj_sup_Z_of_mem_QB (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {c : G} (hcE : c ∈ QB E) :
    conjSubgroup c (E ⊔ Z) = E ⊔ Z := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (card_conjSubgroup c _).ge
  intro x hx
  have hx' : c⁻¹ * x * c ∈ E ⊔ Z := mem_conjSubgroup.mp hx
  have hmem := (IsRootB.ctx hc hE).conj_mem_sup (IsRootB.ctx hc hE).Z_le_QB.1 hcE hx'
  rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at hmem

private theorem conj_inf_QB_of_mem_Q (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {p : G} (hp : p ∈ Q) :
    conjSubgroup p (Q ⊓ QB E) = Q ⊓ QB E := by
  calc conjSubgroup p (Q ⊓ QB E)
      = conjSubgroup p Q ⊓ conjSubgroup p (QB E) := conjSubgroup_inf p Q (QB E)
    _ = Q ⊓ QB (conjSubgroup p E) := by
        rw [(IsRootB.ctx hc hE).conj_Q_eq (hc.hyp.Q_normal.1 hp), ← QB_conj]
    _ = Q ⊓ QB E := (IsRootB.ctx hc hE).conj_inf_QB_of_mem_Q hp

private theorem le_inf_and_not_le_sup_of_conj_eq {E D : Subgroup G} {g : G}
    (hinf : conjSubgroup g (Q ⊓ QB E) = Q ⊓ QB E)
    (hsup : conjSubgroup g (E ⊔ Z) = E ⊔ Z)
    (hDle : D ≤ Q ⊓ QB E) (hDZ : ¬ D ≤ E ⊔ Z) :
    conjSubgroup g D ≤ Q ⊓ QB E ∧ ¬ conjSubgroup g D ≤ E ⊔ Z := by
  constructor
  · rw [← hinf]
    exact Subgroup.map_mono hDle
  · intro h
    apply hDZ
    have hsup' : conjSubgroup g⁻¹ (E ⊔ Z) = E ⊔ Z := by
      calc conjSubgroup g⁻¹ (E ⊔ Z) = conjSubgroup g⁻¹ (conjSubgroup g (E ⊔ Z)) := by
            rw [hsup]
        _ = E ⊔ Z := by rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have h2 : conjSubgroup g⁻¹ (conjSubgroup g D) ≤ conjSubgroup g⁻¹ (E ⊔ Z) :=
      Subgroup.map_mono h
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, hsup'] at h2

private theorem frame_QB (hc : Ctx M Q Z B) {E D : Subgroup G} (hE : IsRootB M B E)
    (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E) (hDZ : ¬ D ≤ E ⊔ Z) :
    ∃ h : G, E = conjSubgroup h Z ∧ QB E = conjSubgroup h Q ∧
      Ctx (conjSubgroup h M) (QB E) E D := by
  have hEroot : IsRootB M B E := hE
  have hDroot : IsRootB M B D := hD
  obtain ⟨mE, -, hEB⟩ := hE
  obtain ⟨g, hg⟩ := hc.conj
  have hEconj : E = conjSubgroup (mE * g) Z := by rw [hEB, hg, conjSubgroup_mul]
  obtain ⟨mD, -, hDB⟩ := hD
  have hDconjZ : D = conjSubgroup (mD * g) Z := by rw [hDB, hg, conjSubgroup_mul]
  have hDE : D ≠ E := fun h => hDZ (h ▸ le_sup_left)
  have hcE : Ctx M Q Z E := IsRootB.ctx hc hEroot
  have hcED0 := Ctx.frame (hc := hcE) hEconj hDconjZ (hDle.trans inf_le_right) hDE
  have hQB : QB E = conjSubgroup (mE * g) Q := (Ctx.QB_eq hcE hEconj).2
  refine ⟨mE * g, hEconj, hQB, ?_⟩
  rwa [← hQB] at hcED0

private theorem card_centralizer_QB (hc : Ctx M Q Z B) {E D : Subgroup G}
    (hE : IsRootB M B E) (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E)
    (hDZ : ¬ D ≤ E ⊔ Z) :
    Nat.card ↥(QB E ⊓ Subgroup.centralizer (Z : Set G)) =
      Nat.card ↥(QB E ⊓ Subgroup.centralizer (Z : Set G) ⊓
        Subgroup.centralizer (D : Set G)) * Nat.card E := by
  have hEroot : IsRootB M B E := hE
  have hDroot : IsRootB M B D := hD
  obtain ⟨mE, hmE, hEB⟩ := hE
  obtain ⟨g, hg⟩ := hc.conj
  have hEZ : E ≠ Z := by
    intro h
    apply hc.ne
    have h2 : Z = conjSubgroup mE B := h.symm.trans hEB
    have h3 : B = conjSubgroup mE⁻¹ Z := by
      rw [h2, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    rw [h3, hc.conj_Z_eq (M.inv_mem hmE)]
  obtain ⟨mD, -, hDB⟩ := hD
  have hDconjZ : D = conjSubgroup (mD * g) Z := by rw [hDB, hg, conjSubgroup_mul]
  have hDE : D ≠ E := fun h => hDZ (h ▸ le_sup_left)
  obtain ⟨h, hEconj, -, hcED⟩ := frame_QB hc hEroot hDroot hDle hDZ
  have hZconj : Z = conjSubgroup h⁻¹ E := by
    rw [hEconj, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hDconjE : D = conjSubgroup ((mD * g) * h⁻¹) E := by
    calc D = conjSubgroup (mD * g) Z := hDconjZ
      _ = conjSubgroup (mD * g) (conjSubgroup h⁻¹ E) := by rw [hZconj]
      _ = conjSubgroup ((mD * g) * h⁻¹) E := (conjSubgroup_mul _ _ E).symm
  have hcE : Ctx M Q Z E := IsRootB.ctx hc hEroot
  exact StrothHyp.card_cent_inf hcED.hyp hZconj hDconjE hcE.Z_le_QB.1
    (hDle.trans inf_le_right) (Ne.symm hEZ) hDE (by simpa [sup_comm] using hDZ)

private noncomputable def commHomE (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {d : G} (hdQB : d ∈ QB E) :
    ↥(QB E ⊓ Subgroup.centralizer (Z : Set G)) →* ↥E := {
  toFun x := ⟨⁅(x : G), d⁆, (IsRootB.ctx hc hE).QB_comm_mem x.2.1 hdQB⟩
  map_one' := by ext; simp [commutatorElement_def]
  map_mul' x x' := by
    ext
    show ⁅(x : G) * (x' : G), d⁆ = ⁅(x : G), d⁆ * ⁅(x' : G), d⁆
    have hcomm : (x : G) * ⁅(x' : G), d⁆ = ⁅(x' : G), d⁆ * (x : G) :=
      (IsRootB.ctx hc hE).QB_comm x.2.1
        ((IsRootB.ctx hc hE).QB_comm_mem x'.2.1 hdQB)
    have hZcomm : ⁅(x : G), d⁆ * ⁅(x' : G), d⁆ =
        ⁅(x' : G), d⁆ * ⁅(x : G), d⁆ :=
      (IsRootB.ctx hc hE).QB_comm
        (Smith81.IsZConjugate.le_QB_self hc.hyp (IsRootB.isZConjugate hc hE)
          ((IsRootB.ctx hc hE).QB_comm_mem x.2.1 hdQB))
        ((IsRootB.ctx hc hE).QB_comm_mem x'.2.1 hdQB)
    rw [show ⁅(x : G) * (x' : G), d⁆ =
      (x : G) * ⁅(x' : G), d⁆ * (x : G)⁻¹ * ⁅(x : G), d⁆ by
        simp only [commutatorElement_def]; group]
    rw [show (x : G) * ⁅(x' : G), d⁆ * (x : G)⁻¹ = ⁅(x' : G), d⁆ by
      rw [hcomm, mul_inv_cancel_right]]
    exact hZcomm.symm }

private theorem commHomE_range_eq_top (hc : Ctx M Q Z B) {E D : Subgroup G}
    (hE : IsRootB M B E) (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E)
    (hDZ : ¬ D ≤ E ⊔ Z) {d : G} (hdD : d ∈ D) (hdZ : d ∉ E ⊔ Z) :
    (commHomE hc hE (hDle hdD).2).range = ⊤ := by
  have hd1 : d ≠ 1 := fun h => hdZ (h ▸ Subgroup.one_mem _)
  obtain ⟨h, hEconj, hQB, hcED⟩ := frame_QB hc hE hD hDle hDZ
  set T : Subgroup G := QB E ⊓ Subgroup.centralizer (Z : Set G)
  have hcardT : Nat.card ↥T =
      Nat.card ↥(T ⊓ Subgroup.centralizer (D : Set G)) * Nat.card E := by
    simpa [T] using card_centralizer_QB hc hE hD hDle hDZ
  let ψ : ↥T →* ↥E := commHomE hc hE (hDle hdD).2
  have hker_eq : ψ.ker = (T ⊓ Subgroup.centralizer (D : Set G)).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hxd : ⁅(x.1 : G), d⁆ = 1 := by
        have := congrArg Subtype.val hx
        simpa [ψ, commHomE] using this
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Ctx.centralizes_of_comm hcED x.2.1 hdD hd1
          (commutatorElement_eq_one_iff_mul_comm.mp hxd) y hy).symm
    · rintro ⟨-, hxD⟩
      have hcomm : (x.1 : G) * d = d * (x.1 : G) :=
        (Subgroup.mem_centralizer_iff.mp hxD d hdD).symm
      show ψ x = 1
      ext
      simpa [ψ, commHomE] using commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hker : Nat.card ψ.ker = Nat.card ↥(T ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hker_eq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ Subgroup.centralizer (D : Set G) ≤ T)
        ).toEquiv
  have hrange : Nat.card ψ.range = Nat.card E := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hker, hcardT] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  exact Subgroup.eq_top_of_card_eq _ hrange

private theorem exists_centralizer_comm_of_mem_E (hc : Ctx M Q Z B) {E D : Subgroup G}
    (hE : IsRootB M B E) (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E)
    (hDZ : ¬ D ≤ E ⊔ Z) {d : G} (hdD : d ∈ D) (hdZ : d ∉ E ⊔ Z)
    {y : G} (hyE : y ∈ E) :
    ∃ c₁ ∈ QB E ⊓ Subgroup.centralizer (Z : Set G), ⁅c₁, d⁆ = y := by
  have htop := commHomE_range_eq_top hc hE hD hDle hDZ hdD hdZ
  have hmem : (⟨y, hyE⟩ : ↥E) ∈ (commHomE hc hE (hDle hdD).2).range := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_range] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨(x : G), x.2, ?_⟩
  have := congrArg Subtype.val hx
  simpa [commHomE] using this

private theorem exists_centralizer_comm (hc : Ctx M Q Z B) {E D : Subgroup G}
    (hE : IsRootB M B E) (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E)
    (hDZ : ¬ D ≤ E ⊔ Z) {c d : G} (hcE : c ∈ QB E) (hdD : d ∈ D)
    (hdZ : d ∉ E ⊔ Z) :
    ∃ c₁ ∈ QB E ⊓ Subgroup.centralizer (Z : Set G), ⁅c₁, d⁆ = ⁅c, d⁆ := by
  refine exists_centralizer_comm_of_mem_E hc hE hD hDle hDZ hdD hdZ ?_
  exact (IsRootB.ctx hc hE).QB_comm_mem hcE (hDle hdD).2

private theorem conj_eq_of_comm_eq (hc : Ctx M Q Z B) {D : Subgroup G}
    (hD : IsRootB M B D) {c c₁ d : G} (hdD : d ∈ D) (hd1 : d ≠ 1)
    (hcomm : ⁅c₁, d⁆ = ⁅c, d⁆) :
    conjSubgroup c D = conjSubgroup c₁ D := by
  obtain ⟨mD, -, hDB⟩ := hD
  obtain ⟨g, hg⟩ := hc.conj
  have hDconjZ : D = conjSubgroup (mD * g) Z := by rw [hDB, hg, conjSubgroup_mul]
  have hxeq : c * d * c⁻¹ = c₁ * d * c₁⁻¹ := by
    have e1 : c * d * c⁻¹ = ⁅c, d⁆ * d := by rw [commutatorElement_def]; group
    have e2 : c₁ * d * c₁⁻¹ = ⁅c₁, d⁆ * d := by rw [commutatorElement_def]; group
    rw [e1, e2, hcomm]
  have hxne : c * d * c⁻¹ ≠ 1 := by
    intro h
    apply hd1
    have := congrArg (fun t => c⁻¹ * t * c) h
    simpa [mul_assoc] using this
  have hmemc : c * d * c⁻¹ ∈ conjSubgroup c D := by
    rw [mem_conjSubgroup]
    rwa [show c⁻¹ * (c * d * c⁻¹) * c = d by group]
  have hmemc₁ : c₁ * d * c₁⁻¹ ∈ conjSubgroup c₁ D := by
    rw [mem_conjSubgroup]
    rwa [show c₁⁻¹ * (c₁ * d * c₁⁻¹) * c₁ = d by group]
  have hZc : Smith81.IsZConjugate Z (conjSubgroup c D) := by
    refine ⟨c * (mD * g), ?_⟩
    calc conjSubgroup c D = conjSubgroup c (conjSubgroup (mD * g) Z) := by rw [hDconjZ]
      _ = conjSubgroup (c * (mD * g)) Z := (conjSubgroup_mul c (mD * g) Z).symm
  have hZc₁ : Smith81.IsZConjugate Z (conjSubgroup c₁ D) := by
    refine ⟨c₁ * (mD * g), ?_⟩
    calc conjSubgroup c₁ D = conjSubgroup c₁ (conjSubgroup (mD * g) Z) := by rw [hDconjZ]
      _ = conjSubgroup (c₁ * (mD * g)) Z := (conjSubgroup_mul c₁ (mD * g) Z).symm
  exact Smith81.IsZConjugate.eq_of_mem hc.hyp hZc hZc₁ hxne hmemc (hxeq.symm ▸ hmemc₁)

private theorem isRootB_conj_of_mem_QB (hc : Ctx M Q Z B) {E D : Subgroup G}
    (hE : IsRootB M B E) (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E)
    (hDZ : ¬ D ≤ E ⊔ Z) {c : G} (hcE : c ∈ QB E) :
    IsRootB M B (conjSubgroup c D) := by
  obtain ⟨d, hdD, hdZ⟩ := Set.not_subset.mp hDZ
  have hd1 : d ≠ 1 := fun h => hdZ (h ▸ Subgroup.one_mem _)
  obtain ⟨c₁, hc₁T, hcomm⟩ := exists_centralizer_comm hc hE hD hDle hDZ hcE hdD hdZ
  have heq := conj_eq_of_comm_eq hc hD hdD hd1 hcomm
  have hc₁M : c₁ ∈ M := by
    rw [← hc.hyp.normalizer_Z.1]
    exact Subgroup.centralizer_le_normalizer (Z : Set G) hc₁T.2
  rw [heq]
  exact hD.conj hc₁M

private def PermutesRoots101 (M Q Z B E : Subgroup G) (g : G) : Prop :=
  ∀ D : Subgroup G, IsRootB M B D → D ≤ Q ⊓ QB E → ¬ D ≤ E ⊔ Z →
    IsRootB M B (conjSubgroup g D) ∧ conjSubgroup g D ≤ Q ⊓ QB E ∧
      ¬ conjSubgroup g D ≤ E ⊔ Z

private theorem permutesRoots101_one (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) : PermutesRoots101 M Q Z B E 1 := by
  intro D hD hDle hDZ
  rw [conjSubgroup_one]
  exact ⟨hD, hDle, hDZ⟩

private theorem permutesRoots101_mul (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {g h : G} (hg : PermutesRoots101 M Q Z B E g)
    (hh : PermutesRoots101 M Q Z B E h) : PermutesRoots101 M Q Z B E (g * h) := by
  intro D hD hDle hDZ
  obtain ⟨hDroot, hDle', hDZ'⟩ := hh D hD hDle hDZ
  obtain ⟨hroot, hle, hZ⟩ := hg (conjSubgroup h D) hDroot hDle' hDZ'
  rw [conjSubgroup_mul]
  exact ⟨hroot, hle, hZ⟩

private theorem permutesRoots101_of_mem_Q (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {p : G} (hp : p ∈ Q) : PermutesRoots101 M Q Z B E p := by
  intro D hD hDle hDZ
  obtain ⟨hle, hZ⟩ := le_inf_and_not_le_sup_of_conj_eq
    (conj_inf_QB_of_mem_Q hc hE hp) ((IsRootB.ctx hc hE).conj_sup_Z_of_mem_Q hp) hDle hDZ
  exact ⟨hD.conj (hc.hyp.Q_normal.1 hp), hle, hZ⟩

private theorem permutesRoots101_of_mem_QB (hc : Ctx M Q Z B) {E : Subgroup G}
    (hE : IsRootB M B E) {c : G} (hcE : c ∈ QB E) : PermutesRoots101 M Q Z B E c := by
  intro D hD hDle hDZ
  obtain ⟨hle, hZ⟩ := le_inf_and_not_le_sup_of_conj_eq
    (conj_inf_QB_of_mem_QB hc hE hcE) (conj_sup_Z_of_mem_QB hc hE hcE) hDle hDZ
  exact ⟨isRootB_conj_of_mem_QB hc hE hD hDle hDZ hcE, hle, hZ⟩

theorem Ctx.root_conj_of_mem_sup (hc : Ctx M Q Z B) {E D : Subgroup G}
    (hE : IsRootB M B E) (hD : IsRootB M B D) (hDle : D ≤ Q ⊓ QB E)
    (hDZ : ¬ D ≤ E ⊔ Z) {g : G} (hg : g ∈ Q ⊔ QB E) :
    IsRootB M B (conjSubgroup g D) ∧ conjSubgroup g D ≤ Q ⊓ QB E ∧
      ¬ conjSubgroup g D ≤ E ⊔ Z := by
  have hg' : g ∈ Subgroup.closure ((Q : Set G) ∪ (QB E : Set G)) := by
    rw [← Subgroup.sup_eq_closure]
    exact hg
  refine Subgroup.closure_induction'' (p := fun x _ => PermutesRoots101 M Q Z B E x)
    (fun x hx => ?_) (fun x hx => ?_) (permutesRoots101_one hc hE)
    (fun x y _ _ hx hy => permutesRoots101_mul hc hE hx hy) hg' D hD hDle hDZ
  · rcases hx with hxQ | hxQB
    · exact permutesRoots101_of_mem_Q hc hE hxQ
    · exact permutesRoots101_of_mem_QB hc hE hxQB
  · rcases hx with hxQ | hxQB
    · exact permutesRoots101_of_mem_Q hc hE (Q.inv_mem hxQ)
    · exact permutesRoots101_of_mem_QB hc hE ((QB E).inv_mem hxQB)


end CFSG.RankThree.GF2n.Stroth80
