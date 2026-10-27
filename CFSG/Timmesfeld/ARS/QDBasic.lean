module

public import CFSG.Timmesfeld.ARS.Sec3Collinear
public import CFSG.Timmesfeld.ARS.Sec3Components
public import CFSG.Timmesfeld.ARS.Sec3Special
public import CFSG.Timmesfeld.ARS.Sec3Commuting
public import CFSG.Timmesfeld.ARS.Sec4Defs

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace QD

theorem commutator_le_of_le {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) : ⁅H, K⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem (hH hh) (hK hk)) (L.inv_mem (hH hh))) (L.inv_mem (hK hk))

theorem commuting_commutator {B C M : Subgroup G} (hB : Commuting B M)
    (hC : C ≤ Subgroup.normalizer (M : Set G)) : Commuting ⁅B, C⁆ M := by
  refine (commuting_iff_le_centralizer.2 ?_).symm
  rw [Subgroup.commutator_le]
  intro b hb c hc
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hcm : c⁻¹ * m * c ∈ M := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hC hc)) m).1 hm
    rwa [inv_inv] at this
  have h1 : b * m = m * b := (hB b hb m hm).eq
  have h2 : b⁻¹ * (c⁻¹ * m * c) = (c⁻¹ * m * c) * b⁻¹ := ((hB b hb _ hcm).inv_left).eq
  calc m * ⁅b, c⁆ = m * b * (c * b⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
    _ = b * m * (c * b⁻¹ * c⁻¹) := by rw [h1]
    _ = b * c * (c⁻¹ * m * c) * b⁻¹ * c⁻¹ := by group
    _ = b * c * (b⁻¹ * (c⁻¹ * m * c)) * c⁻¹ := by rw [h2]; group
    _ = ⁅b, c⁆ * m := by rw [commutatorElement_def]; group

theorem exists_forall_not_le_commutator [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {P : Set (Subgroup G)} (hPQ : ∀ B ∈ P, B ≤ Q) (hne : ∀ B ∈ P, B ≠ ⊥) {B₀ : Subgroup G}
    (hB₀ : B₀ ∈ P) : ∃ B ∈ P, ∀ B' ∈ P, ¬ B' ≤ ⁅B, Q⁆ := by
  by_contra! h
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries Q).1 hQ.isNilpotent
  have key : ∀ k, ∃ B ∈ P, B ≤ Q.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact ⟨B₀, hB₀, hPQ B₀ hB₀⟩
    | succ k ih =>
      obtain ⟨B, hB, hBk⟩ := ih
      obtain ⟨B', hB', hle⟩ := h B hB
      exact ⟨B', hB', hle.trans (Subgroup.commutator_mono hBk le_rfl)⟩
  obtain ⟨B, hB, hBn⟩ := key n
  rw [hn, le_bot_iff] at hBn
  exact hne B hB hBn

theorem conjSub_mem_centralSet (hR : IsRootClass R) {D B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hB : B ∈ centralSet R D) :
    conjSub B g ∈ centralSet R D := by
  refine ⟨hR.conjSub_mem hB.1 g, ?_⟩
  have := hB.2.conjSub g
  rwa [conjSub_eq_self_iff.2 hg] at this

theorem le_normalizer_of_mem_centralSet {D B : Subgroup G} (hB : B ∈ centralSet R D) :
    B ≤ Subgroup.normalizer (D : Set G) :=
  (commuting_iff_le_centralizer.1 hB.2).trans (Subgroup.centralizer_le_normalizer _)

theorem eq_of_le_of_mem (hR : IsRootClass R) (hiso : NoIsolated R) {A B : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (hle : A ≤ B) : A = B := by
  by_contra hne
  have := inf_eq_bot hR hiso hA hB hne
  rw [inf_of_le_left hle] at this
  exact hR.ne_bot A hA this

section Q

variable {D : Subgroup G}

theorem Q_eq_gen : Q R D = gen (isolatedSet R D) := rfl

theorem le_Q {B : Subgroup G} (hB : B ∈ isolatedSet R D) : B ≤ Q R D := le_gen hB

theorem Q_le_centralizer : Q R D ≤ Subgroup.centralizer (D : Set G) :=
  gen_le fun _ hB => commuting_iff_le_centralizer.1 hB.1.2

theorem Q_le_normalizer : Q R D ≤ Subgroup.normalizer (D : Set G) :=
  Q_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)

theorem le_M_self : D ≤ M R D := le_sup_left

theorem le_M {B : Subgroup G} (hB : B ∈ lambdaSet R D) : B ≤ M R D :=
  (le_iSup₂ (f := fun E (_ : E ∈ lambdaSet R D) => E) B hB).trans le_sup_right

theorem mem_stabSet_of_forall {Δ : Set (Subgroup G)} {g : G} (h : ∀ A ∈ Δ, conjSub A g ∈ Δ)
    (h' : ∀ A ∈ Δ, conjSub A g⁻¹ ∈ Δ) : g ∈ stabSet Δ := by
  rw [mem_stabSet]
  refine Set.Subset.antisymm (Set.image_subset_iff.2 h) fun B hB => ⟨conjSub B g⁻¹, h' B hB, ?_⟩
  change conjSub (conjSub B g⁻¹) g = B
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

variable (hR : IsRootClass R)
include hR

theorem mem_isolatedSet_self (hD : D ∈ R) : D ∈ isolatedSet R D :=
  ⟨⟨hD, hR.commuting_self hD⟩, fun _ hC hop => hop.not_commuting (hR.ne_bot D hD) hC.2⟩

theorem le_Q_self (hD : D ∈ R) : D ≤ Q R D := le_Q (mem_isolatedSet_self hR hD)

theorem conjSub_mem_isolatedSet {B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hB : B ∈ isolatedSet R D) :
    conjSub B g ∈ isolatedSet R D := by
  refine ⟨conjSub_mem_centralSet hR hg hB.1, fun C hC hop => ?_⟩
  refine hB.2 _ (conjSub_mem_centralSet hR (Subgroup.inv_mem _ hg) hC) ?_
  have := Opposite.conj hop g⁻¹
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this

theorem conjSub_Q {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    conjSub (Q R D) g = Q R D :=
  Sec3.conjSub_iSup_isolatedIn_eq (Δ := centralSet R D)
    (fun _ hB => conjSub_mem_centralSet hR hg hB)
    (fun _ hB => conjSub_mem_centralSet hR (Subgroup.inv_mem _ hg) hB)

theorem normalizer_le_normalizer_Q :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer ((Q R D : Subgroup G) : Set G) :=
  fun _ hg => conjSub_eq_self_iff.1 (conjSub_Q hR hg)

theorem isPGroup_Q [Finite G] : IsPGroup 2 (Q R D) := by
  refine Sec3.isPGroup_iSup_isolatedIn hR (Δ := centralSet R D) (fun _ hB => hB.1) ?_
  intro g hg B hB
  have hle : (⨆ B ∈ centralSet R D, B) ≤ Subgroup.normalizer (D : Set G) :=
    iSup₂_le fun _ hC => le_normalizer_of_mem_centralSet hC
  exact conjSub_mem_centralSet hR (hle hg) hB

theorem mem_isolatedSet_of_le [Finite G] {B : Subgroup G} (hB : B ∈ R) (hle : B ≤ Q R D) :
    B ∈ isolatedSet R D := by
  refine ⟨⟨hB, commuting_iff_le_centralizer.2 (hle.trans Q_le_centralizer)⟩, fun C hC hop => ?_⟩
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hC.1
  have hBc : conjSub B c ≤ Q R D := by
    rw [← conjSub_Q hR (le_normalizer_of_mem_centralSet hC hc)]
    exact Subgroup.map_mono hle
  have hne : conjSub B 1 ≠ conjSub B c := by
    rw [conjSub_one]
    intro h
    exact hc1 (hop.symm.eq_one_of_conjSub_eq hc h.symm)
  have hsup := hop.sup_conjSub_eq (hR.mul_self B hB) (one_mem _) (Subgroup.mem_sup_right hc) hne
  rw [conjSub_one] at hsup
  have hP : IsPGroup 2 ↥(B ⊔ C) := (isPGroup_Q hR).to_le (hsup ▸ sup_le hle hBc)
  exact Sec3.not_opposite_of_isPGroup_sup hR hB hC.1 hP hop

theorem lambdaSet_subset_isolatedSet [Finite G] (hD : D ∈ R) :
    lambdaSet R D ⊆ isolatedSet R D := fun _ hB =>
  ⟨⟨hB.1.1, hB.1.2.2⟩, fun _ hC hop => not_commuting_of_opposite_of_mem_lambdaSet hR hC.1
    hop.symm (mem_lambdaSet_comm hD hB) hC.2.symm⟩

theorem M_le_Q [Finite G] (hD : D ∈ R) : M R D ≤ Q R D :=
  sup_le (le_Q_self hR hD) (iSup₂_le fun _ hB => le_Q (lambdaSet_subset_isolatedSet hR hD hB))

theorem commuting_M [Finite G] (hD : D ∈ R) : Commuting D (M R D) :=
  commuting_iff_le_centralizer.2 ((M_le_Q hR hD).trans Q_le_centralizer)

theorem le_normalizer_M [Finite G] (hD : D ∈ R) {C : Subgroup G} (hC : C ∈ centralSet R D) :
    C ≤ Subgroup.normalizer ((M R D : Subgroup G) : Set G) := fun _ hc =>
  conjSub_eq_self_iff.1 ((isPGroup_M hR hD).2.2 _ (le_normalizer_of_mem_centralSet hC hc))

theorem special_of_mem_isolatedSet [Finite G] {E F : Subgroup G} (hE : E ∈ isolatedSet R D)
    (hF : F ∈ isolatedSet R D) (h : ¬ Commuting E F) :
    Special R E F ∧ ⁅E, F⁆ ∈ isolatedSet R D := by
  have hne : E ≠ F := fun e => h (e ▸ hR.commuting_self hE.1.1)
  have hs : Special R E F := by
    rcases hR.rel E hE.1.1 F hF.1.1 hne with h' | h' | h'
    · exact absurd h' h
    · exact absurd h' (hE.2 F hF.1)
    · exact h'
  exact ⟨hs, mem_isolatedSet_of_le hR hs.1 (commutator_le_of_le (le_Q hE) (le_Q hF))⟩

theorem commutator_le_Q {B C : Subgroup G} (hB : B ≤ Subgroup.normalizer (D : Set G))
    (hC : C ≤ Q R D) : ⁅B, C⁆ ≤ Q R D := by
  rw [Subgroup.commutator_le]
  intro b hb c hc
  rw [commutatorElement_def]
  refine (Q R D).mul_mem ?_ ((Q R D).inv_mem (hC hc))
  rw [← conjSub_Q hR (hB hb)]
  exact ⟨c, hC hc, rfl⟩

omit hR in
theorem exists_opposite_of_notMem_isolatedSet {B : Subgroup G} (hB : B ∈ centralSet R D)
    (hBI : B ∉ isolatedSet R D) : ∃ C ∈ centralSet R D, Opposite B C := by
  by_contra! h
  exact hBI ⟨hB, h⟩

end Q

section Lines

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
include hR hiso

theorem exists_eq_conjSub_of_le_sup {A B P : Subgroup G} (hA : A ∈ R) (hB : B ∈ R)
    (h : Special R A B) (hP : P ∈ R) (hPle : P ≤ ⁅A, B⁆ ⊔ A) (hPne : P ≠ ⁅A, B⁆) :
    ∃ b ∈ B, P = conjSub A b := by
  obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hP
  have hle : ⁅A, B⁆ ≤ Subgroup.normalizer (A : Set G) := fun c hc =>
    RankOne.map_conj_eq_self_iff.1 (conjSub_of_forall_commute fun a ha => h.2.1 c hc a ha)
  have hpmem : p ∈ ((⁅A, B⁆ : Subgroup G) : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hPle hp
  obtain ⟨c, hc, a, ha, rfl⟩ := hpmem
  dsimp only at hp hp1
  by_cases ha1 : a = 1
  · subst ha1
    rw [mul_one] at hp hp1
    exact absurd (Sec3.eq_of_mem_of_mem hR hiso hP h.1 hp hc hp1) hPne
  obtain ⟨b, hb, hbc⟩ := (bijOn_commutator hR hiso hA hB h ha ha1).surjOn
    (Subgroup.inv_mem _ hc)
  have hbc' : ⁅a, b⁆ = c⁻¹ := hbc
  have hba : b * a * b⁻¹ = c * a := by
    rw [conj_eq_commutator_mul, ← commutatorElement_inv, hbc', inv_inv]
  refine ⟨b, hb, Sec3.eq_of_mem_of_mem hR hiso hP (hR.conjSub_mem hA b) hp ?_ hp1⟩
  rw [← hba]
  exact conj_mem_conjSub b ha

theorem conjSub_mem_lambdaSet_of_special {B C : Subgroup G} (hB : B ∈ R) (hC : C ∈ R)
    (h : Special R B C) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) : conjSub C b ∈ lambdaSet R C := by
  refine ⟨⟨hR.conjSub_mem hC b, Sec3.conjSub_ne_of_special hR hiso hB hC h hb hb1,
    commuting_conjSub_of_special hR hC h.symm hb⟩, ?_⟩
  rw [Sec3.sup_conjSub_eq_of_special hR hiso hB hC h hb hb1]
  exact (mem_lambdaSet_commutator hR hiso hC hB h.symm).1.2

theorem not_commuting_conjSub_of_opposite {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R)
    (hAB : Opposite A B) (hBC : C ∈ psiSet R B) (hAC : Commuting A C) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : ¬ Commuting A (conjSub C b) := by
  intro h
  have h1 : Commuting A (C ⊔ conjSub C b) := hAC.sup_right h
  rw [Sec3.sup_conjSub_eq_of_special hR hiso hB hBC.1 hBC.2 hb hb1,
    Subgroup.commutator_comm] at h1
  exact not_commuting_of_opposite_of_mem_lambdaSet hR hA hAB
    (Sec3.commutator_mem_lambdaSet_left hR hiso hB hBC) (h1.mono le_rfl le_sup_left)

theorem exists_mem_lambdaSet_not_commuting {D E : Subgroup G} (hD : D ∈ R)
    (hE : E ∈ lambdaSet R D) : ∃ E' ∈ lambdaSet R D, ¬ Commuting E E' := by
  have hER : E ∈ R := hE.1.1
  obtain ⟨C, hC, hCn⟩ := Set.not_subset.1 (not_subset_centralSet_union_psiSet hR hiso hD hE)
  have hCR : C ∈ R := by rcases hC with h | h <;> exact h.1
  have hEC : Opposite E C := by
    have hne : E ≠ C := fun e => hCn (Or.inl ⟨hCR, e ▸ hR.commuting_self hER⟩)
    rcases hR.rel E hER C hCR hne with h | h | h
    · exact absurd (Or.inl ⟨hCR, h⟩) hCn
    · exact h
    · exact absurd (Or.inr ⟨hCR, h⟩) hCn
  have hCD : ¬ Commuting C D :=
    not_commuting_of_opposite_of_mem_lambdaSet hR hCR hEC.symm (mem_lambdaSet_comm hD hE)
  have hs : Special R D C := by
    rcases hC with h | h
    · exact absurd h.2.symm hCD
    · exact h.2
  have hl := mem_lambdaSet_commutator hR hiso hD hCR hs
  exact ⟨_, mem_lambdaSet_comm hs.1 hl.1, not_commuting_of_opposite_of_mem_lambdaSet hR hER hEC
    (mem_lambdaSet_comm hs.1 hl.2)⟩

theorem exists_mem_lambdaSet_opposite {D F : Subgroup G} (hD : D ∈ R) (hF : F ∈ R)
    (h : Special R D F) : ∃ B ∈ lambdaSet R D, Opposite F B := by
  set D₁ := ⁅D, F⁆ with hD₁
  have hD₁R : D₁ ∈ R := h.1
  have hDl : D ∈ lambdaSet R D₁ := (mem_lambdaSet_commutator hR hiso hD hF h).1
  obtain ⟨D'', hD''R, hD₁D''⟩ := hiso D₁ hD₁R
  obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hD₁R hD''R hD₁D'' hDl
  have hPD₁ : P ≠ D₁ := fun e => Special.not_opposite hR hD''R hPψ.2 (e ▸ hD₁D''.symm)
  obtain ⟨f, hf, hPf⟩ := exists_eq_conjSub_of_le_sup hR hiso hD hF h hPR hPle hPD₁
  have hD₁f : conjSub D₁ f⁻¹ = D₁ :=
    conjSub_of_forall_commute fun x hx => (h.2.2 x hx f⁻¹ (F.inv_mem hf)).symm
  set D' := conjSub D'' f⁻¹ with hD'
  have hD'R : D' ∈ R := hR.conjSub_mem hD''R f⁻¹
  have hD₁D' : Opposite D₁ D' := by
    have := Opposite.conj hD₁D'' f⁻¹
    rwa [hD₁f] at this
  have hD'D : Special R D' D := by
    have := Sec3.special_conjSub hR hPψ.2 f⁻¹
    rwa [hPf, ← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD'R
  obtain ⟨-, hcomm, hDl', hBnorm, hBcent⟩ :=
    Sec3.conjSub_props hR hiso hD₁R hD'R hD₁D' hDl ⟨hD, hD'D⟩ hd hd1
  set B := conjSub D d with hBdef
  have hBR : B ∈ R := hR.conjSub_mem hD d
  have hBl : B ∈ lambdaSet R D := mem_lambdaSet_comm hBR hDl'
  have hBD : Commuting B D := hBl.1.2.2.symm
  have hFnorm : ∀ x ∈ F, conjSub (D₁ ⊔ D) x ≤ D₁ ⊔ D := by
    intro x hx
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun y hy => (h.2.2 y hy x hx).symm]
    exact sup_le le_sup_left (conjSub_le_commutator_sup hx)
  have hFcent : ∀ x ∈ D₁ ⊔ D, (∀ e ∈ F, Commute e x) → x ∈ D₁ := by
    intro x hx hxF
    have hle : D₁ ≤ Subgroup.normalizer (D : Set G) := fun c hc =>
      RankOne.map_conj_eq_self_iff.1 (conjSub_of_forall_commute fun a ha => h.2.1 c hc a ha)
    have hx' : x ∈ (D₁ : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    dsimp only at hxF ⊢
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hF
    have hez : Commute e z := by
      have h1 := hxF e he
      have h2 : Commute e y := (h.2.2 y hy e he).symm
      have := h2.inv_right.mul_right h1
      rwa [inv_mul_cancel_left] at this
    rw [eq_one_of_commute_of_special hR hiso hF hD h.symm he he1 hz hez, mul_one]
    exact hy
  have hkey : ⁅⁅D, F⁆, B⁆ ≠ ⊥ := by
    rw [← hD₁, hcomm]
    exact hR.ne_bot D hD
  have hnc : ¬ Commuting F B := by
    intro hc
    apply hkey
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [commuting_iff_commutator_eq_bot.1 hc, Subgroup.commutator_bot_left]
    · rw [commuting_iff_commutator_eq_bot.1 hBD, Subgroup.commutator_bot_left]
  have hns : ¬ Special R F B := by
    intro hs
    have hLR : ⁅F, B⁆ ∈ R := hs.1
    have hFBn : F ⊔ B ≤ Subgroup.normalizer ((D₁ ⊔ D : Subgroup G) : Set G) :=
      sup_le (le_normalizer_of_conjSub_le hFnorm) (le_normalizer_of_conjSub_le hBnorm)
    have hLn : ⁅F, B⁆ ≤ Subgroup.normalizer ((D₁ ⊔ D : Subgroup G) : Set G) :=
      (commutator_le_of_le le_sup_left le_sup_right).trans hFBn
    have hLD : Commuting ⁅F, B⁆ D := by
      refine Sec3.commuting_of_forall_conjSub_eq hR hLR hD (fun l hl => ?_) hiso
      refine conjSub_eq_self_iff.2 (le_normalizer_of_conjSub_le (F := ⁅F, B⁆) (fun l' hl' => ?_) hl)
      rintro _ ⟨x, hx, rfl⟩
      change l' * x * l'⁻¹ ∈ D
      have h1 : l' * x * l'⁻¹ ∈ D₁ ⊔ D := by
        rw [← conjSub_eq_self_iff.2 (hLn hl')]
        exact conj_mem_conjSub l' (Subgroup.mem_sup_right hx)
      refine hBcent _ h1 fun e he => ?_
      have hle : Commute e l' := (hs.2.2 l' hl' e he).symm
      have hxe : Commute e x := (hBD e he x hx)
      exact (hle.mul_right hxe).mul_right hle.inv_right
    apply hkey
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact commuting_iff_commutator_eq_bot.1 hLD
    · rw [commuting_iff_commutator_eq_bot.1 hBD, Subgroup.commutator_bot_left]
  have hne : F ≠ B := fun e => hnc (e ▸ hR.commuting_self hF)
  refine ⟨B, hBl, ?_⟩
  rcases hR.rel F hF B hBR hne with h' | h' | h'
  · exact absurd h' hnc
  · exact h'
  · exact absurd h' hns

end Lines

end QD

end CFSG.Timmesfeld.ARS
