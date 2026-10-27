module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Hyp64 (n : ℕ) (M V₀ V : Subgroup G) (g : G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  le : V₀ ≤ V
  normalizer_eq : normalizer (V : Set G) = M
  le_normalizer₀ : M ≤ normalizer (V₀ : Set G)
  isTI : V₀ ≠ ⊥ → CFSG.CGT.Timmesfeld75.IsTI V₀
  normalizer₀ : V₀ ≠ ⊥ → normalizer (V₀ : Set G) = M
  inCalOStar : InCalOStar n M V₀ V g

@[expose] def UOf (M V : Subgroup G) (g : G) : Subgroup G := V ⊓ conjSubgroup M g

@[expose] def BOf (M V : Subgroup G) (g : G) : Subgroup G := conjSubgroup V g ⊓ M

@[expose] def NOf (M V : Subgroup G) (g : G) : Subgroup G := UOf M V g ⊓ BOf M V g

@[expose] def LOf (V : Subgroup G) (g : G) : Subgroup G := V ⊔ conjSubgroup V g

@[expose] def GenHyp (M V : Subgroup G) (g : G) : Prop :=
  ∀ x ∈ conjSubgroup V g, x ∉ UOf M V g ⊔ BOf M V g →
    LOf V g ≤ (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g)

@[expose] def SwapHyp (V : Subgroup G) (g : G) : Prop :=
  ∃ l ∈ LOf V g, conjSubgroup V l = conjSubgroup V g ∧ conjSubgroup (conjSubgroup V g) l = V

theorem conjSubgroup_mono {A B : Subgroup G} (h : A ≤ B) (g : G) :
    conjSubgroup A g ≤ conjSubgroup B g :=
  Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h

theorem conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  rw [Subgroup.map_sup]

theorem conjSubgroup_inf (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊓ B) g = conjSubgroup A g ⊓ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conjSubgroup_commutator (A B : Subgroup G) (g : G) :
    conjSubgroup ⁅A, B⁆ g = ⁅conjSubgroup A g, conjSubgroup B g⁆ := by
  unfold conjSubgroup
  rw [Subgroup.map_commutator]

theorem conjSubgroup_V₀_eq_of_conjSubgroup_eq {A M V : Subgroup G} {x y : G}
    (hM : normalizer (V : Set G) = M) (hAM : M ≤ normalizer (A : Set G))
    (hxy : conjSubgroup V x = conjSubgroup V y) :
    conjSubgroup A x = conjSubgroup A y := by
  have hmem : x * y⁻¹ ∈ normalizer (V : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup V x y⁻¹, hxy]
    exact conjSubgroup_conjSubgroup_inv V y
  have hmemM : x * y⁻¹ ∈ M := by rwa [hM] at hmem
  have hA : conjSubgroup A (x * y⁻¹) = A :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hAM hmemM)
  calc conjSubgroup A x = conjSubgroup A ((x * y⁻¹) * y) := by
        rw [show (x * y⁻¹) * y = x by group]
    _ = conjSubgroup (conjSubgroup A (x * y⁻¹)) y := by rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup A y := by rw [hA]

theorem timmesfeld_conjSubgroup_eq (A : Subgroup G) (g : G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g A = conjSubgroup A g⁻¹ := by
  ext x
  simp only [CFSG.CGT.Timmesfeld75.conjSubgroup, conjSubgroup, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨a, ha, by rw [← hx]; simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨a, ha, by rw [← hx]; simp [MulAut.conj_apply, mul_assoc]⟩

@[expose] def StepFHyp (M V₀ V : Subgroup G) (g : G) : Prop :=
  ∀ v ∈ V, v ∉ UOf M V g → ∀ b ∈ BOf M V g,
    ⁅b, v⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g →
      b ∈ conjSubgroup V₀ g ⊔ NOf M V g

theorem NOf_eq (M V : Subgroup G) (g : G) (hVM : V ≤ M) :
    NOf M V g = V ⊓ conjSubgroup V g := by
  ext x
  simp only [NOf, UOf, BOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨hxV, -⟩, hxVg, -⟩
    exact ⟨hxV, hxVg⟩
  · rintro ⟨hxV, hxVg⟩
    exact ⟨⟨hxV, conjSubgroup_mono hVM g hxVg⟩, hxVg, hVM hxV⟩

private theorem UOf_le_normalizer_conjV {M V : Subgroup G} {g : G}
    (hM : normalizer (V : Set G) = M) :
    UOf M V g ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  have hmap := Subgroup.map_normalizer_eq_of_bijective V
    (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).bijective
  rw [hM] at hmap
  have h : conjSubgroup M g = Subgroup.normalizer (conjSubgroup V g : Set G) := hmap
  intro x hx
  rw [← h]
  exact hx.2

theorem six_four_four_centralizer_V {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    V ⊓ Subgroup.centralizer (BOf M V g : Set G) = NOf M V g ⊔ V₀ := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  rw [NOf_eq M V g hVM]
  exact hcen

private theorem V₀_inf_conjVg_eq_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : V₀ ⊓ conjSubgroup V g = ⊥ := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hVg_notM : ¬ conjSubgroup V g ≤ M := hO.1.1
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx0, hxg⟩ := hx
  by_contra hx1
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hx0
    exact hx1 (Subgroup.mem_bot.1 hx0)
  have hC : Subgroup.centralizer ({x} : Set G) ≤ M := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy
    have hxy : x * y = y * x := hy x (Set.mem_singleton x)
    have hyx : y⁻¹ * x * y = x := by
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [hxy]
        _ = x := by group
    have hxVy : x ∈ conjSubgroup V₀ y := by
      rw [mem_conjSubgroup_iff]
      have hyy : y * x * y⁻¹ = x := by
        calc y * x * y⁻¹ = y * (y⁻¹ * x * y) * y⁻¹ := by rw [hyx]
          _ = x := by group
      rw [hyy]; exact hx0
    have hne : V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ := by
      intro hbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hbot]; exact ⟨hx0, hxVy⟩
      exact hx1 (Subgroup.mem_bot.1 hxbot)
    have hTI' : V₀ ⊓ conjSubgroup V₀ y = ⊥ ∨ V₀ ⊓ conjSubgroup V₀ y = V₀ := by
      have hh := hTI hV0ne y⁻¹
      rwa [timmesfeld_conjSubgroup_eq, inv_inv] at hh
    rcases hTI' with h | h
    · exact absurd h hne
    · have hle : V₀ ≤ conjSubgroup V₀ y := by
        calc V₀ = V₀ ⊓ conjSubgroup V₀ y := h.symm
          _ ≤ conjSubgroup V₀ y := inf_le_right
      have heq : conjSubgroup V₀ y = V₀ := by
        symm
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        show Nat.card ↥(V₀.map (MulAut.conj y⁻¹).toMonoidHom) ≤ Nat.card ↥V₀
        rw [Subgroup.card_map_of_injective (f := (MulAut.conj y⁻¹).toMonoidHom)
          (MulAut.conj y⁻¹).injective]
      rw [← hN0 hV0ne, ← conjSubgroup_eq_iff_mem_normalizer]
      exact heq
  have hVgC : conjSubgroup V g ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact IsElemAbelian.comm hVgel hxg hy
  exact hVg_notM (hVgC.trans hC)

private theorem NOf_le_cTilde {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : NOf M V g ≤ F11.CTilde M V₀ V := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hM_le : M ≤ normalizer (V : Set G) := le_of_eq hM.symm
  intro x hx
  rw [NOf_eq M V g hVM, Subgroup.mem_inf] at hx
  obtain ⟨hxV, hxVg⟩ := hx
  rw [mem_cTilde_iff hV hM_le]
  refine ⟨hVM hxV, ⟨Subgroup.le_normalizer hxV, hM0 (hVM hxV)⟩, ?_⟩
  rw [actTil_eq_one_iff]
  intro v hv
  have hcomm : x * v = v * x := IsElemAbelian.comm hV hxV hv
  have hone : x * v * x⁻¹ * v⁻¹ = 1 := by rw [hcomm]; group
  rw [hone]
  exact V₀.one_mem

private theorem conjSubgroup_V₀_le_cTilde {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hM_le : M ≤ normalizer (V : Set G) := le_of_eq hM.symm
  intro y hy
  have hy2 : y * y = 1 :=
    IsElemAbelian.mul_self_eq_one (IsElemAbelian.mono hV hV0 |>.map _) hy
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hy_normV : y ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h1 : ⁅y, v⁆ ∈ V₀ := hcomm (Subgroup.commutator_mem_commutator hy hv)
      rw [show y * v * y⁻¹ = ⁅y, v⁆ * v by rw [commutatorElement_def]; group]
      exact V.mul_mem (hV0 h1) hv
    · intro hv
      have h1 : ⁅y, (y * v * y⁻¹)⁆ ∈ V₀ := hcomm (Subgroup.commutator_mem_commutator hy hv)
      have h2 : y * (y * v * y⁻¹) * y⁻¹ ∈ V := by
        rw [show y * (y * v * y⁻¹) * y⁻¹ = ⁅y, (y * v * y⁻¹)⁆ * (y * v * y⁻¹) by
          rw [commutatorElement_def]; group]
        exact V.mul_mem (hV0 h1) hv
      rwa [show y * (y * v * y⁻¹) * y⁻¹ = v by
        rw [hyinv]
        calc y * (y * v * y) * y = (y * y) * v * (y * y) := by group
          _ = v := by rw [hy2, one_mul, mul_one]] at h2
  have hy_normV0 : y ∈ Subgroup.normalizer (V₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h1 : ⁅y, v⁆ ∈ V₀ := hcomm (Subgroup.commutator_mem_commutator hy (hV0 hv))
      rw [show y * v * y⁻¹ = ⁅y, v⁆ * v by rw [commutatorElement_def]; group]
      exact V₀.mul_mem h1 hv
    · intro hv
      have h1 : ⁅y, (y * v * y⁻¹)⁆ ∈ V₀ :=
        hcomm (Subgroup.commutator_mem_commutator hy (hV0 hv))
      have h2 : y * (y * v * y⁻¹) * y⁻¹ ∈ V₀ := by
        rw [show y * (y * v * y⁻¹) * y⁻¹ = ⁅y, (y * v * y⁻¹)⁆ * (y * v * y⁻¹) by
          rw [commutatorElement_def]; group]
        exact V₀.mul_mem h1 hv
      rwa [show y * (y * v * y⁻¹) * y⁻¹ = v by
        rw [hyinv]
        calc y * (y * v * y) * y = (y * y) * v * (y * y) := by group
          _ = v := by rw [hy2, one_mul, mul_one]] at h2
  rw [mem_cTilde_iff hV hM_le]
  have hyM : y ∈ M := by rw [← hM]; exact hy_normV
  refine ⟨hyM, ⟨hy_normV, hy_normV0⟩, ?_⟩
  rw [actTil_eq_one_iff]
  intro v hv
  exact hcomm (Subgroup.commutator_mem_commutator hy hv)

theorem commutator_U_B_le_N {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : ⁅UOf M V g, BOf M V g⁆ ≤ NOf M V g := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hM_le : M ≤ normalizer (V : Set G) := le_of_eq hM.symm
  rw [Subgroup.commutator_le]
  intro u hu b hb
  rw [NOf_eq M V g hVM, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · have hbu : b * u⁻¹ * b⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hM_le hb.2) u⁻¹).1 (V.inv_mem hu.1)
    rw [commutatorElement_def,
      show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group]
    exact V.mul_mem hu.1 hbu
  · have hbu : u * b * u⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 (UOf_le_normalizer_conjV hM hu) b).1 hb.1
    rw [commutatorElement_def]
    exact (conjSubgroup V g).mul_mem hbu ((conjSubgroup V g).inv_mem hb.1)

private theorem centralizerMod_le_U {n : ℕ} {M V₀ V D : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hfix : StepFHyp M V₀ V g)
    (hD : D ≤ BOf M V g) (hDbar : ¬ D ≤ F11.CTilde M V₀ V) :
    ∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) → v ∈ UOf M V g := by
  intro v hvV hv0
  by_contra hvU
  have hD_le : D ≤ conjSubgroup V₀ g ⊔ NOf M V g := by
    intro d hd
    have hdv : ⁅d, v⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g := by
      have h1 : ⁅v, d⁆ ∈ V₀ := hv0 d hd
      have h2 : ⁅d, v⁆ = ⁅v, d⁆⁻¹ := (commutatorElement_inv v d).symm
      rw [h2]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (V₀.inv_mem h1))
    exact hfix v hvV hvU d (hD hd) hdv
  exact hDbar (hD_le.trans (sup_le (conjSubgroup_V₀_le_cTilde h) (NOf_le_cTilde h)))

theorem six_four_three {n : ℕ} {M V₀ V D : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hfix : StepFHyp M V₀ V g)
    (hD : D ≤ BOf M V g) (hDbar : ¬ D ≤ F11.CTilde M V₀ V) :
    V ⊓ Subgroup.centralizer (D : Set G) ≤ UOf M V g ∧
      (∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) →
        v ∈ V ⊓ Subgroup.centralizer (D : Set G)) := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hV0Vg : V₀ ⊓ conjSubgroup V g = ⊥ := V₀_inf_conjVg_eq_bot hcopy
  constructor
  · intro v hv
    rw [Subgroup.mem_inf] at hv
    exact centralizerMod_le_U hcopy hfix hD hDbar v hv.1 fun d hd => by
      have h1 : ⁅v, d⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hv.2 d hd).symm
      rw [h1]; exact V₀.one_mem
  · intro v hvV hv0
    have hvU : v ∈ UOf M V g := centralizerMod_le_U hcopy hfix hD hDbar v hvV hv0
    refine Subgroup.mem_inf.2 ⟨hvV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hdv : d ∈ conjSubgroup V g := (hD hd).1
    have hvu : v ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
      UOf_le_normalizer_conjV hM hvU
    have h2 : ⁅v, d⁆ ∈ conjSubgroup V g := by
      have h1 : v * d * v⁻¹ ∈ conjSubgroup V g :=
        (Subgroup.mem_normalizer_iff.1 hvu d).1 hdv
      rw [commutatorElement_def]
      exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem hdv)
    have hv1 : ⁅v, d⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← hV0Vg]
      exact ⟨hv0 d hd, h2⟩
    rw [← commutatorElement_inv v d, hv1, inv_one]

theorem six_four_four_centralizer_B {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hfix : StepFHyp M V₀ V g) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hM_le : M ≤ normalizer (V : Set G) := le_of_eq hM.symm
  have hV_notMg : ¬ V ≤ conjSubgroup M g := hO.2.1
  apply le_antisymm
  · intro b hb
    rw [Subgroup.mem_inf] at hb
    obtain ⟨hbB, hbC⟩ := hb
    obtain ⟨v, hvV, hvMg⟩ : ∃ v ∈ V, v ∉ conjSubgroup M g := by
      by_contra h
      push Not at h
      exact hV_notMg h
    have hvU : v ∉ UOf M V g := fun hv => hvMg (Subgroup.mem_inf.1 hv).2
    have hbv : ⁅b, v⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g := by
      rw [mem_cTilde_iff hV hM_le] at hbC
      obtain ⟨-, hbs, hbact⟩ := hbC
      have h1 : ⁅b, v⁆ ∈ V₀ := (actTil_eq_one_iff V₀ V hV ⟨b, hbs⟩).1 hbact v hvV
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left h1)
    have hb' := hfix v hvV hvU b hbB hbv
    exact (le_of_eq (sup_comm (a := conjSubgroup V₀ g) (b := NOf M V g))) hb'
  · refine sup_le ?_ ?_
    · refine le_inf ?_ (NOf_le_cTilde hcopy)
      intro x hx
      rw [NOf_eq M V g hVM, Subgroup.mem_inf] at hx
      exact ⟨hx.2, hVM hx.1⟩
    · refine le_inf ?_ (conjSubgroup_V₀_le_cTilde hcopy)
      intro x hx
      have hxM : x ∈ M := (mem_cTilde_iff hV hM_le).1 (conjSubgroup_V₀_le_cTilde hcopy hx) |>.1
      exact ⟨conjSubgroup_mono hV0 g hx, hxM⟩

theorem six_four_four_iff {n : ℕ} {M V₀ V : Subgroup G} {g : G} {b : G}
    (h : Hyp64 n M V₀ V g) (hfix : StepFHyp M V₀ V g)
    (hbB : b ∈ BOf M V g) (hb : b ∉ F11.CTilde M V₀ V) :
    ∀ v ∈ V, ⁅v, b⁆ ∈ V ⊓ Subgroup.centralizer (BOf M V g : Set G) ↔ v ∈ UOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hCen : V ⊓ Subgroup.centralizer (BOf M V g : Set G) = NOf M V g ⊔ V₀ :=
    six_four_four_centralizer_V hcopy
  intro v hvV
  constructor
  · intro hv
    by_contra hvU
    have hvb : ⁅b, v⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g := by
      have h1 : ⁅v, b⁆ ∈ NOf M V g ⊔ V₀ := by rw [← hCen]; exact hv
      have h2 : ⁅b, v⁆ = ⁅v, b⁆⁻¹ := (commutatorElement_inv v b).symm
      have hle : NOf M V g ⊔ V₀ ≤ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g :=
        sup_le le_sup_right (le_sup_left.trans le_sup_left)
      rw [h2]
      exact hle ((NOf M V g ⊔ V₀).inv_mem h1)
    have hb' : b ∈ conjSubgroup V₀ g ⊔ NOf M V g := hfix v hvV hvU b hbB hvb
    exact hb ((sup_le (conjSubgroup_V₀_le_cTilde hcopy) (NOf_le_cTilde hcopy)) hb')
  · intro hvU
    rw [hCen]
    exact Subgroup.mem_sup_left
      (commutator_U_B_le_N hcopy (Subgroup.commutator_mem_commutator hvU hbB))

theorem centralizer_le_M_of_mem_V₀ {M V₀ : Subgroup G} {x : G}
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀) (hN0 : normalizer (V₀ : Set G) = M)
    (hx : x ∈ V₀) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hy
  have hxy : x * y = y * x := hy x (Set.mem_singleton x)
  have hyx : y⁻¹ * x * y = x := by
    calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
      _ = y⁻¹ * (y * x) := by rw [hxy]
      _ = x := by group
  have hxVy : x ∈ conjSubgroup V₀ y := by
    rw [mem_conjSubgroup_iff]
    have hyy : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = y * (y⁻¹ * x * y) * y⁻¹ := by rw [hyx]
        _ = x := by group
    rw [hyy]; exact hx
  have hne : V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact ⟨hx, hxVy⟩
    exact hx1 (Subgroup.mem_bot.1 hxbot)
  have hTI' : V₀ ⊓ conjSubgroup V₀ y = ⊥ ∨ V₀ ⊓ conjSubgroup V₀ y = V₀ := by
    have hh := hTI y⁻¹
    rwa [timmesfeld_conjSubgroup_eq, inv_inv] at hh
  rcases hTI' with h | h
  · exact absurd h hne
  · have hle : V₀ ≤ conjSubgroup V₀ y := by
      calc V₀ = V₀ ⊓ conjSubgroup V₀ y := h.symm
        _ ≤ conjSubgroup V₀ y := inf_le_right
    have heq : conjSubgroup V₀ y = V₀ := by
      symm
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      show Nat.card ↥(V₀.map (MulAut.conj y⁻¹).toMonoidHom) ≤ Nat.card ↥V₀
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj y⁻¹).toMonoidHom)
        (MulAut.conj y⁻¹).injective]
    rw [← hN0, ← conjSubgroup_eq_iff_mem_normalizer]
    exact heq

theorem NOf_le_centralizer_L {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    NOf M V g ≤ Subgroup.centralizer (LOf V g : Set G) := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  intro x hx
  rw [NOf_eq M V g hVM, Subgroup.mem_inf] at hx
  obtain ⟨hxV, hxVg⟩ := hx
  have hVcent : V ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (IsElemAbelian.comm hV hy hxV).symm
  have hVgcent : conjSubgroup V g ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (IsElemAbelian.comm hVgel hy hxVg).symm
  have hL : LOf V g ≤ Subgroup.centralizer ({x} : Set G) := sup_le hVcent hVgcent
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (hL hy) x (Set.mem_singleton x)).symm

private theorem mem_normalizer_of_conj_mem {V : Subgroup G} {y : G} (hy2 : y * y = 1)
    (h : ∀ v ∈ V, y * v * y⁻¹ ∈ V) : y ∈ Subgroup.normalizer (V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact h v
  · intro hv
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have h2 : y * (y * v * y⁻¹) * y⁻¹ ∈ V := h (y * v * y⁻¹) hv
    rwa [show y * (y * v * y⁻¹) * y⁻¹ = v by
      rw [hyinv]
      calc y * (y * v * y) * y = (y * y) * v * (y * y) := by group
        _ = v := by rw [hy2, one_mul, mul_one]] at h2

theorem conjSubgroup_V₀_centralizer_le {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) {x : G} (hx : x ∈ conjSubgroup V₀ g) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup M g := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [conjSubgroup_eq_bot_iff.mpr hbot] at hx
    exact hx1 (Subgroup.mem_bot.1 hx)
  have hy0 : g * x * g⁻¹ ∈ V₀ := (mem_conjSubgroup_iff).1 hx
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro hh
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hh]; group
  have hCy : Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M :=
    centralizer_le_M_of_mem_V₀ (hTI hV0ne) (hN0 hV0ne) hy0 hy1
  intro z hz
  rw [mem_conjSubgroup_iff]
  apply hCy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  rw [Subgroup.mem_centralizer_iff] at hz
  have hxz : x * z = z * x := hz x (Set.mem_singleton x)
  calc (g * x * g⁻¹) * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
    _ = g * (z * x) * g⁻¹ := by rw [hxz]
    _ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group

theorem conjSubgroup_V₀_inf_V_eq_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : conjSubgroup V₀ g ⊓ V = ⊥ := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hV_notMg : ¬ V ≤ conjSubgroup M g := hO.2.1
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxV0g, hxV⟩ := hx
  by_contra hx1
  have hC : Subgroup.centralizer ({x} : Set G) ≤ conjSubgroup M g :=
    conjSubgroup_V₀_centralizer_le hcopy hxV0g hx1
  have hVC : V ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (IsElemAbelian.comm hV hy hxV).symm
  exact hV_notMg (hVC.trans hC)

private theorem conjSubgroup_V₀_le_B {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : conjSubgroup V₀ g ≤ BOf M V g := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  intro y hy
  have hy2 : y * y = 1 :=
    IsElemAbelian.mul_self_eq_one (IsElemAbelian.mono hV hV0 |>.map _) hy
  have hy_normV : y ∈ Subgroup.normalizer (V : Set G) :=
    mem_normalizer_of_conj_mem hy2 fun v hv => by
      have h1 : ⁅y, v⁆ ∈ V₀ := hcomm (Subgroup.commutator_mem_commutator hy hv)
      rw [show y * v * y⁻¹ = ⁅y, v⁆ * v by rw [commutatorElement_def]; group]
      exact V.mul_mem (hV0 h1) hv
  exact ⟨conjSubgroup_mono hV0 g hy, by rw [← hM]; exact hy_normV⟩

private theorem V₀_le_U {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : V₀ ≤ UOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hM_le : M ≤ normalizer (V : Set G) := le_of_eq hM.symm
  by_cases hV0bot : V₀ = ⊥
  · rw [hV0bot]; exact bot_le
  · obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hO.2.2.2 hV0bot)
    have hxg : (x : G) ∈ conjSubgroup V₀ g := x.2.1
    have hxVg : (x : G) ∈ conjSubgroup V g := conjSubgroup_mono hV0 g hxg
    have hxM : (x : G) ∈ M := x.2.2
    have hxB : (x : G) ∈ BOf M V g := ⟨hxVg, hxM⟩
    have hxC : Subgroup.centralizer ({(x : G)} : Set G) ≤ conjSubgroup M g :=
      conjSubgroup_V₀_centralizer_le hcopy hxg (fun h => hx1 (Subtype.ext h))
    have hV0V0g : conjSubgroup V₀ g ⊓ V = ⊥ := conjSubgroup_V₀_inf_V_eq_bot hcopy
    have hux : ∀ u ∈ UOf M V g, ⁅u, (x : G)⁆ = 1 := by
      intro u hu
      have hmem : ⁅u, (x : G)⁆ ∈ (⊥ : Subgroup G) := by
        rw [← hV0V0g]
        refine ⟨?_, ?_⟩
        · have huNorm : u ∈ Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
            have hnorm : conjSubgroup M g = Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
              have hmap := Subgroup.map_normalizer_eq_of_bijective V₀
                (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).bijective
              rw [hN0 hV0bot] at hmap
              exact hmap
            rw [← hnorm]; exact hu.2
          have hxu : u * (x : G) * u⁻¹ ∈ conjSubgroup V₀ g :=
            (Subgroup.mem_normalizer_iff.1 huNorm (x : G)).1 hxg
          rw [commutatorElement_def]
          exact (conjSubgroup V₀ g).mul_mem hxu ((conjSubgroup V₀ g).inv_mem hxg)
        · have hxu : (x : G) * u⁻¹ * (x : G)⁻¹ ∈ V :=
            (Subgroup.mem_normalizer_iff.1 (hM_le hxM) u⁻¹).1 (V.inv_mem hu.1)
          rw [commutatorElement_def,
            show u * (x : G) * u⁻¹ * (x : G)⁻¹ = u * ((x : G) * u⁻¹ * (x : G)⁻¹) by group]
          exact V.mul_mem hu.1 hxu
      exact Subgroup.mem_bot.1 hmem
    have hU_le : UOf M V g ≤ V ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
      intro u hu
      refine ⟨hu.1, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 := hux u hu
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hCxU : V ⊓ Subgroup.centralizer ({(x : G)} : Set G) ≤ UOf M V g := by
      intro y hy
      exact ⟨hy.1, hxC hy.2⟩
    have hCx_eq : V ⊓ Subgroup.centralizer ({(x : G)} : Set G) = UOf M V g :=
      le_antisymm hCxU hU_le
    have hV0_le_CB : V₀ ≤ V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
      change V₀ ≤ V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G)
      rw [hcen]
      exact le_sup_right
    have hCB_le_Cx : V ⊓ Subgroup.centralizer (BOf M V g : Set G) ≤
        V ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
      intro y hy
      obtain ⟨hyV, hys⟩ := hy
      refine ⟨hyV, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subgroup.mem_centralizer_iff.1 hys (x : G) hxB
    calc V₀ ≤ V ⊓ Subgroup.centralizer (BOf M V g : Set G) := hV0_le_CB
      _ ≤ V ⊓ Subgroup.centralizer ({(x : G)} : Set G) := hCB_le_Cx
      _ = UOf M V g := hCx_eq

theorem inCalOStar_K_facts {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    ∃ K : Subgroup G,
      K = UOf M V g ⊔ BOf M V g ∧
      LOf V g ≤ Subgroup.normalizer (K : Set G) ∧
      (∃ l ∈ LOf V g, conjSubgroup V g = conjSubgroup V l) ∧
      ⁅conjSubgroup V₀ g, V⁆ ≤ V₀ ∧
      (K : Set G) = (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨hO, K, hKnorm, hKset, hquot, hlK, hcomm, hcen, hne⟩ := hg
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hK_eq : K = UOf M V g ⊔ BOf M V g := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) := by
        rw [show (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) = ↑K from hKset.symm]
        exact hy
      obtain ⟨b, hbB, u, huU, rfl⟩ := hy'
      exact (UOf M V g ⊔ BOf M V g).mul_mem (Subgroup.mem_sup_right hbB) (Subgroup.mem_sup_left huU)
    · refine sup_le ?_ ?_
      · intro u hu
        have : u ∈ (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) :=
          ⟨1, (BOf M V g).one_mem, u, hu, one_mul u⟩
        rw [show (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) = ↑K from hKset.symm] at this
        exact this
      · intro b hb
        have : b ∈ (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) :=
          ⟨b, hb, 1, (UOf M V g).one_mem, mul_one b⟩
        rw [show (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) = ↑K from hKset.symm] at this
        exact this
  have hK_le_L : K ≤ LOf V g := by
    rw [hK_eq]
    exact sup_le (fun u hu => Subgroup.mem_sup_left hu.1) (fun b hb => Subgroup.mem_sup_right hb.1)
  have hK_le_L' : K ≤ V ⊔ conjSubgroup V g := hK_le_L
  have hKnorm_L : LOf V g ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_L').1 hKnorm
  refine ⟨K, hK_eq, hKnorm_L, hlK, hcomm, ?_⟩
  simpa only [BOf, UOf] using hKset

theorem conjSubgroup_V_inf_sup_U_B_eq_B {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    conjSubgroup V g ⊓ (UOf M V g ⊔ BOf M V g) = BOf M V g := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    have hUBM : UOf M V g ⊔ BOf M V g ≤ M :=
      sup_le (fun u hu => hVM hu.1) (fun b hb => hb.2)
    exact ⟨hy.1, hUBM hy.2⟩
  · exact le_inf inf_le_left le_sup_right

theorem V_inf_K_eq_U {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) {K : Subgroup G}
    (hKset : (K : Set G) = (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G)) :
    V ⊓ K = UOf M V g := by
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hVMg : conjSubgroup V g ≤ conjSubgroup M g := conjSubgroup_mono hVM g
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyV, hyK⟩ := hy
    have hy' : y ∈ (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) := by
      rw [← hKset]; exact hyK
    obtain ⟨b, hbB, u, huU, rfl⟩ := hy'
    have hbV : b ∈ V := by
      have : b = (b * u) * u⁻¹ := by group
      rw [this]
      exact V.mul_mem hyV (V.inv_mem huU.1)
    have hbU : b ∈ UOf M V g := ⟨hbV, hVMg hbB.1⟩
    exact (UOf M V g).mul_mem hbU huU
  · intro u hu
    refine ⟨hu.1, ?_⟩
    have : u ∈ (↑(BOf M V g) : Set G) * (↑(UOf M V g) : Set G) :=
      ⟨1, (BOf M V g).one_mem, u, hu, one_mul u⟩
    rwa [← hKset] at this

theorem conjSubgroup_NOf_eq {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) {m : G} (hm : m ∈ LOf V g) :
    conjSubgroup (NOf M V g) m = NOf M V g := by
  have hcopy := h
  apply le_antisymm
  · intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hc := NOf_le_centralizer_L hcopy hy
    have hcomm := Subgroup.mem_centralizer_iff.1 hc m hm
    have hEq : m⁻¹ * (m * y * m⁻¹) * m = m * y * m⁻¹ := by
      calc m⁻¹ * (m * y * m⁻¹) * m = m⁻¹ * ((m * y * m⁻¹) * m) := by group
        _ = m⁻¹ * (m * (m * y * m⁻¹)) := by rw [← hcomm]
        _ = m * y * m⁻¹ := by group
    have hy' : y = m⁻¹ * (m * y * m⁻¹) * m := by group
    rw [hy', hEq]
    exact hy
  · intro n hn
    rw [mem_conjSubgroup_iff]
    have hc := NOf_le_centralizer_L hcopy hn
    have hcomm := Subgroup.mem_centralizer_iff.1 hc m hm
    rwa [show m * n * m⁻¹ = n by rw [hcomm]; group]

theorem U_centralizesMod_le_N {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {x : G}
    (hxVg : x ∈ conjSubgroup V g) (hxB : x ∉ BOf M V g) :
    ∀ u ∈ UOf M V g, ⁅u, x⁆ ∈ NOf M V g → u ∈ NOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, -⟩ := inCalOStar_K_facts hcopy
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  have hUL : UOf M V g ≤ LOf V g := fun u hu => Subgroup.mem_sup_left hu.1
  have hxL : x ∈ LOf V g := Subgroup.mem_sup_right hxVg
  have hx_notK : x ∉ UOf M V g ⊔ BOf M V g := by
    intro hxK
    exact hxB (by
      have : x ∈ conjSubgroup V g ⊓ (UOf M V g ⊔ BOf M V g) := ⟨hxVg, hxK⟩
      rwa [conjSubgroup_V_inf_sup_U_B_eq_B hcopy] at this)
  let S : Subgroup G :=
    { carrier := {u | u ∈ UOf M V g ∧ ⁅u, x⁆ ∈ NOf M V g}
      mul_mem' := by
        rintro u w ⟨huU, huN⟩ ⟨hwU, hwN⟩
        refine ⟨(UOf M V g).mul_mem huU hwU, ?_⟩
        have hw : u * ⁅w, x⁆ * u⁻¹ = ⁅w, x⁆ := by
          have hcommu :=
            Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy hwN) u (hUL huU)
          rw [hcommu]; group
        rw [commutatorElement_mul_left_eq_conj_mul, hw]
        exact (NOf M V g).mul_mem hwN huN
      one_mem' := ⟨(UOf M V g).one_mem, by simp⟩
      inv_mem' := by
        rintro u ⟨huU, huN⟩
        refine ⟨(UOf M V g).inv_mem huU, ?_⟩
        rw [commutatorElement_inv_left]
        have hcommu := Subgroup.mem_centralizer_iff.1
          (NOf_le_centralizer_L hcopy ((NOf M V g).inv_mem huN)) u (hUL huU)
        have hxu : ⁅x, u⁆ = ⁅u, x⁆⁻¹ := (commutatorElement_inv u x).symm
        have hEq : u⁻¹ * ⁅u, x⁆⁻¹ * u = ⁅u, x⁆⁻¹ := by
          calc u⁻¹ * ⁅u, x⁆⁻¹ * u = u⁻¹ * (⁅u, x⁆⁻¹ * u) := by group
            _ = u⁻¹ * (u * ⁅u, x⁆⁻¹) := by rw [← hcommu]
            _ = ⁅u, x⁆⁻¹ := by group
        rw [hxu, hEq]
        exact (NOf M V g).inv_mem huN }
  have hNS : NOf M V g ≤ S := by
    intro n hn
    refine ⟨(Subgroup.mem_inf.1 hn).1, ?_⟩
    rw [NOf_eq M V g hVM] at hn
    have hnVg : n ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hn).2
    have hn2 : n * x = x * n := IsElemAbelian.comm hVgel hnVg hxVg
    have h1 : ⁅n, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hn2
    rw [h1]
    exact (NOf M V g).one_mem
  let C : Subgroup G :=
    { carrier := {y | y ∈ LOf V g ∧ ∀ s ∈ S, ⁅s, y⁆ ∈ NOf M V g}
      mul_mem' := by
        rintro y z ⟨hyL, hyN⟩ ⟨hzL, hzN⟩
        refine ⟨(LOf V g).mul_mem hyL hzL, ?_⟩
        intro s hs
        have hz : y * ⁅s, z⁆ * y⁻¹ = ⁅s, z⁆ := by
          have hcommy :=
            Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy (hzN s hs)) y hyL
          rw [hcommy]; group
        have hyz : ⁅s, y⁆ * y * ⁅s, z⁆ * y⁻¹ = ⁅s, y⁆ * ⁅s, z⁆ := by
          calc ⁅s, y⁆ * y * ⁅s, z⁆ * y⁻¹ = ⁅s, y⁆ * (y * ⁅s, z⁆ * y⁻¹) := by group
            _ = ⁅s, y⁆ * ⁅s, z⁆ := by rw [hz]
        rw [commutatorElement_mul_right_eq_mul_conj, hyz]
        exact (NOf M V g).mul_mem (hyN s hs) (hzN s hs)
      one_mem' := ⟨(LOf V g).one_mem, by intro s hs; simp⟩
      inv_mem' := by
        rintro y ⟨hyL, hyN⟩
        refine ⟨(LOf V g).inv_mem hyL, ?_⟩
        intro s hs
        rw [commutatorElement_inv_right]
        have hyu : ⁅y, s⁆ = ⁅s, y⁆⁻¹ := (commutatorElement_inv s y).symm
        rw [hyu]
        have hcommy := Subgroup.mem_centralizer_iff.1
          (NOf_le_centralizer_L hcopy ((NOf M V g).inv_mem (hyN s hs))) y⁻¹ ((LOf V g).inv_mem hyL)
        have hEq : y⁻¹ * ⁅s, y⁆⁻¹ * y = ⁅s, y⁆⁻¹ := by rw [hcommy]; group
        rw [hEq]
        exact (NOf M V g).inv_mem (hyN s hs) }
  have hVC : V ≤ C := by
    intro v hv
    refine ⟨Subgroup.mem_sup_left hv, ?_⟩
    intro s hs
    have h1 : ⁅s, v⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hs.1.1 hv)
    rw [h1]
    exact (NOf M V g).one_mem
  have hxC : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.2 ⟨hxL, fun s hs => hs.2⟩
  have hUC : UOf M V g ≤ C := by
    intro u hu
    refine ⟨hUL hu, ?_⟩
    intro s hs
    have h1 : ⁅s, u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hs.1.1 hu.1)
    rw [h1]
    exact (NOf M V g).one_mem
  have hBC : BOf M V g ≤ C := by
    intro b hb
    refine ⟨Subgroup.mem_sup_right hb.1, ?_⟩
    intro s hs
    exact commutator_U_B_le_N hcopy (Subgroup.commutator_mem_commutator hs.1 hb)
  have hsupC : (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g) ≤ C :=
    sup_le (sup_le hVC hxC) (sup_le hUC hBC)
  have hLC : LOf V g ≤ C := (hgen x hxVg hx_notK).trans hsupC
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hlV' : conjSubgroup V l = conjSubgroup V g := hlV.symm
  have hlC := hLC hlL
  have hconjS_le_S : conjSubgroup S l ≤ S := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    obtain ⟨s, hs, hs_eq⟩ : ∃ s ∈ S, l⁻¹ * s * l = y := ⟨l * y * l⁻¹, hy, by group⟩
    rw [← hs_eq]
    have hsl : ⁅s, l⁆ ∈ NOf M V g := hlC.2 s hs
    have hcomml := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy hsl) l hlL
    have hEq : l⁻¹ * s * l = (l⁻¹ * ⁅s, l⁆ * l) * s := by
      rw [commutatorElement_def]; group
    rw [hEq]
    have hNl : l⁻¹ * ⁅s, l⁆ * l = ⁅s, l⁆ := by
      calc l⁻¹ * ⁅s, l⁆ * l = l⁻¹ * (⁅s, l⁆ * l) := by group
        _ = l⁻¹ * (l * ⁅s, l⁆) := by rw [← hcomml]
        _ = ⁅s, l⁆ := by group
    rw [hNl]
    exact S.mul_mem (hNS hsl) hs
  have hconjS_le_B : conjSubgroup S l ≤ BOf M V g := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    obtain ⟨s, hs, hs_eq⟩ : ∃ s ∈ S, l⁻¹ * s * l = y := ⟨l * y * l⁻¹, hy, by group⟩
    rw [← hs_eq]
    have hVg : l⁻¹ * s * l ∈ conjSubgroup V g := by
      have hmem : l⁻¹ * s * l ∈ conjSubgroup (UOf M V g) l := by
        rw [mem_conjSubgroup_iff]
        rw [show l * (l⁻¹ * s * l) * l⁻¹ = s by group]
        exact hs.1
      exact hlV' ▸ conjSubgroup_mono (fun u (hu : u ∈ UOf M V g) => hu.1) l hmem
    have hK : l⁻¹ * s * l ∈ UOf M V g ⊔ BOf M V g := by
      have hsK : s ∈ K := by rw [hK_eq]; exact Subgroup.mem_sup_left hs.1
      have hmem : l⁻¹ * s * l ∈ conjSubgroup K l := by
        rw [mem_conjSubgroup_iff]
        rw [show l * (l⁻¹ * s * l) * l⁻¹ = s by group]
        exact hsK
      rwa [conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hlL), hK_eq] at hmem
    have hy' : l⁻¹ * s * l ∈ conjSubgroup V g ⊓ (UOf M V g ⊔ BOf M V g) := ⟨hVg, hK⟩
    rwa [conjSubgroup_V_inf_sup_U_B_eq_B hcopy] at hy'
  have hS_le_N : S ≤ NOf M V g := by
    have hconjS_le_N : conjSubgroup S l ≤ NOf M V g :=
      le_inf (hconjS_le_S.trans (fun s hs => hs.1)) hconjS_le_B
    have hmono : conjSubgroup (conjSubgroup S l) l⁻¹ ≤ conjSubgroup (NOf M V g) l⁻¹ :=
      conjSubgroup_mono hconjS_le_N l⁻¹
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
      conjSubgroup_NOf_eq hcopy ((LOf V g).inv_mem hlL)] at hmono
    exact hmono
  intro u hu huN
  exact hS_le_N ⟨hu, huN⟩

theorem stepA {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {x : G}
    (hxVg : x ∈ conjSubgroup V g) (hxB : x ∉ BOf M V g) :
    ∀ k ∈ UOf M V g ⊔ BOf M V g, ⁅k, x⁆ ∈ NOf M V g → k ∈ BOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hVgel : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N hcopy).trans inf_le_right
  intro k hkUB hkN
  change k ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) at hkUB
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB] at hkUB
  obtain ⟨u, huU, b, hbB, rfl⟩ := hkUB
  have hux : ⁅u, x⁆ ∈ NOf M V g := by
    have hbx : ⁅b, x⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hVgel hbB.1 hxVg)
    have : u * ⁅b, x⁆ * u⁻¹ * ⁅u, x⁆ = ⁅u, x⁆ := by rw [hbx]; group
    rwa [commutatorElement_mul_left_eq_conj_mul, this] at hkN
  have huN : u ∈ NOf M V g := U_centralizesMod_le_N hcopy hgen hxVg hxB u huU hux
  exact (BOf M V g).mul_mem ((Subgroup.mem_inf.1 huN).2) hbB

theorem stepB {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {v : G}
    (hvV : v ∈ V) (hvU : v ∉ UOf M V g) :
    ∀ k ∈ UOf M V g ⊔ BOf M V g, ⁅k, v⁆ ∈ NOf M V g → k ∈ UOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  obtain ⟨-, K0, -, hKset0, -, -, -, -, -⟩ := hg
  obtain ⟨K, hK_eq, hKnorm_L, hlK, hcomm, hKset⟩ := inCalOStar_K_facts hcopy
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hlV' : conjSubgroup V l = conjSubgroup V g := hlV.symm
  set x : G := l⁻¹ * v * l with hxdef
  have hxVg : x ∈ conjSubgroup V g := by
    rw [← hlV', mem_conjSubgroup_iff]
    rw [show l * x * l⁻¹ = v by rw [hxdef]; group]
    exact hvV
  have hgl : g * l⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    rw [show g * l⁻¹ = (l * g⁻¹)⁻¹ by group]
    refine (Subgroup.normalizer (V : Set G)).inv_mem ?_
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, hlV',
      conjSubgroup_conjSubgroup_inv]
  have hKl : conjSubgroup K l⁻¹ = K :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hlL))
  have hBK : BOf M V g = conjSubgroup V g ⊓ K := by
    rw [hK_eq]; exact (conjSubgroup_V_inf_sup_U_B_eq_B hcopy).symm
  have hBl : conjSubgroup (BOf M V g) l⁻¹ = UOf M V g := by
    rw [hBK, conjSubgroup_inf, conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.2 hgl, hKl]
    exact V_inf_K_eq_U hcopy hKset
  have hx_notB : x ∉ BOf M V g := by
    intro hxB
    apply hvU
    have hmem : l * x * l⁻¹ ∈ conjSubgroup (BOf M V g) l⁻¹ := by
      rw [mem_conjSubgroup_iff]
      rw [show l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x by group]
      exact hxB
    rw [hBl] at hmem
    rwa [show l * x * l⁻¹ = v by rw [hxdef]; group] at hmem
  intro k hkUB hkN
  set k' : G := l⁻¹ * k * l with hk'def
  have hk'_K : k' ∈ UOf M V g ⊔ BOf M V g := by
    have hmem : k' ∈ conjSubgroup (UOf M V g ⊔ BOf M V g) l := by
      rw [mem_conjSubgroup_iff]
      rw [show l * k' * l⁻¹ = k by rw [hk'def]; group]
      exact hkUB
    have hUl : conjSubgroup (UOf M V g ⊔ BOf M V g) l = UOf M V g ⊔ BOf M V g := by
      rw [← hK_eq]
      exact conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hlL)
    rwa [hUl] at hmem
  have hk'x : ⁅k', x⁆ ∈ NOf M V g := by
    have hconj : l * ⁅k', x⁆ * l⁻¹ = ⁅k, v⁆ := by
      have h1 : l * k' * l⁻¹ = k := by rw [hk'def]; group
      have h2 : l * x * l⁻¹ = v := by rw [hxdef]; group
      have hcc := conjugate_commutatorElement k' x l
      rwa [h1, h2] at hcc
    have hmem : l * ⁅k', x⁆ * l⁻¹ ∈ NOf M V g := by rw [hconj]; exact hkN
    have hc := NOf_le_centralizer_L hcopy hmem
    have hcomml := Subgroup.mem_centralizer_iff.1 hc l hlL
    have hEq : ⁅k', x⁆ = l * ⁅k', x⁆ * l⁻¹ := by
      calc ⁅k', x⁆ = l⁻¹ * (l * ⁅k', x⁆ * l⁻¹) * l := by group
        _ = l⁻¹ * ((l * ⁅k', x⁆ * l⁻¹) * l) := by group
        _ = l⁻¹ * (l * (l * ⁅k', x⁆ * l⁻¹)) := by rw [← hcomml]
        _ = l * ⁅k', x⁆ * l⁻¹ := by group
    rwa [hEq]
  have hk'B : k' ∈ BOf M V g := stepA hcopy hgen hxVg hx_notB k' hk'_K hk'x
  have hkilB : k ∈ conjSubgroup (BOf M V g) l⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rw [show (l⁻¹) * k * (l⁻¹)⁻¹ = k' by rw [hk'def]; group]
    exact hk'B
  rwa [hBl] at hkilB

private theorem commutator_B_V_le_U {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : ⁅BOf M V g, V⁆ ≤ UOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, hcomm, hKset⟩ := inCalOStar_K_facts hcopy
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hM_le : M ≤ normalizer (V : Set G) := le_of_eq hM.symm
  have hKle : K ≤ conjSubgroup M g := by
    rw [hK_eq]
    exact sup_le (fun u hu => hu.2) (fun b hb => conjSubgroup_mono hVM g hb.1)
  rw [Subgroup.commutator_le]
  intro b hb v hv
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 (hM_le hb.2) v).1 hv) (V.inv_mem hv)
  · have hbK : b ∈ K := by rw [hK_eq]; exact Subgroup.mem_sup_right hb
    have hvK : v * b⁻¹ * v⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKnorm_L (Subgroup.mem_sup_left hv)) b⁻¹).1
        (K.inv_mem hbK)
    have hcommK : ⁅b, v⁆ ∈ K := by
      rw [commutatorElement_def, show b * v * b⁻¹ * v⁻¹ = b * (v * b⁻¹ * v⁻¹) by group]
      exact K.mul_mem hbK hvK
    exact hKle hcommK

private theorem U_inf_sup_V0_conjV0_eq_V0 {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) : UOf M V g ⊓ (V₀ ⊔ conjSubgroup V₀ g) = V₀ := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨-, K, -, hKset, -, hlK, hcomm, hcen, hne⟩ := hg
  have hV0U : V₀ ≤ UOf M V g := V₀_le_U hcopy
  have hV0g_norm : conjSubgroup V₀ g ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl hV0).trans hcomm
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyU, hyL0⟩ := hy
    have hL0eq : (↑(V₀ ⊔ conjSubgroup V₀ g) : Set G)
        = (↑(conjSubgroup V₀ g) : Set G) * (↑V₀ : Set G) := by
      rw [sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup V₀ g) V₀ hV0g_norm
    change y ∈ (↑(V₀ ⊔ conjSubgroup V₀ g) : Set G) at hyL0
    rw [hL0eq] at hyL0
    obtain ⟨c, hc, v0, hv0, rfl⟩ := hyL0
    have hcV : c ∈ V := by
      have : (c * v0) * v0⁻¹ ∈ V := V.mul_mem hyU.1 (V.inv_mem (hV0 hv0))
      simpa using this
    have hcbot : c ∈ (⊥ : Subgroup G) := by
      rw [← conjSubgroup_V₀_inf_V_eq_bot hcopy]
      exact ⟨hc, hcV⟩
    have hc1 : c = 1 := Subgroup.mem_bot.1 hcbot
    simpa [hc1] using hv0
  · exact le_inf hV0U le_sup_left

private theorem commutator_mul_modN {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) {b₁ b₂ v : G}
    (hb₁ : b₁ ∈ BOf M V g) (hb₂ : b₂ ∈ BOf M V g) (hv : v ∈ V) :
    ⁅b₁ * b₂, v⁆ * (⁅b₁, v⁆ * ⁅b₂, v⁆)⁻¹ ∈ NOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hBU : ⁅BOf M V g, UOf M V g⁆ ≤ NOf M V g := by
    rw [Subgroup.commutator_comm]
    exact commutator_U_B_le_N hcopy
  have hb₂v : ⁅b₂, v⁆ ∈ UOf M V g :=
    commutator_B_V_le_U hcopy (Subgroup.commutator_mem_commutator hb₂ hv)
  have hb₁v : ⁅b₁, v⁆ ∈ UOf M V g :=
    commutator_B_V_le_U hcopy (Subgroup.commutator_mem_commutator hb₁ hv)
  have hN : b₁ * ⁅b₂, v⁆ * b₁⁻¹ * ⁅b₂, v⁆⁻¹ ∈ NOf M V g :=
    hBU (Subgroup.commutator_mem_commutator hb₁ hb₂v)
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hsplit : (b₁ * ⁅b₂, v⁆ * b₁⁻¹ * ⁅b₁, v⁆) * (⁅b₁, v⁆ * ⁅b₂, v⁆)⁻¹
      = (b₁ * ⁅b₂, v⁆ * b₁⁻¹ * ⁅b₂, v⁆⁻¹)
        * (⁅b₂, v⁆ * ⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹ * ⁅b₁, v⁆⁻¹) := by group
  rw [hsplit]
  refine (NOf M V g).mul_mem hN ?_
  have hcomm : ⁅b₂, v⁆ * ⁅b₁, v⁆ = ⁅b₁, v⁆ * ⁅b₂, v⁆ :=
    IsElemAbelian.comm hV hb₂v.1 hb₁v.1
  rw [show ⁅b₂, v⁆ * ⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹ * ⁅b₁, v⁆⁻¹ = 1 by rw [hcomm]; group]
  exact (NOf M V g).one_mem

private theorem commutator_mul_modN_inv {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) {b₁ b₂ v : G}
    (hb₁ : b₁ ∈ BOf M V g) (hb₂ : b₂ ∈ BOf M V g) (hv : v ∈ V)
    (heq : ⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹ ∈ NOf M V g) :
    ⁅b₁ * b₂⁻¹, v⁆ ∈ NOf M V g := by
  have h₂ := commutator_mul_modN h hb₂ ((BOf M V g).inv_mem hb₂) hv
  have h₂inv : (⁅b₂, v⁆ * ⁅b₂⁻¹, v⁆)⁻¹ ∈ NOf M V g := by simpa using h₂
  have h₂' : ⁅b₂, v⁆ * ⁅b₂⁻¹, v⁆ ∈ NOf M V g := by simpa using (NOf M V g).inv_mem h₂inv
  have h₁ := commutator_mul_modN h hb₁ ((BOf M V g).inv_mem hb₂) hv
  have hprod : ⁅b₁, v⁆ * ⁅b₂⁻¹, v⁆ ∈ NOf M V g := by
    have he : ⁅b₁, v⁆ * ⁅b₂⁻¹, v⁆
        = (⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹) * (⁅b₂, v⁆ * ⁅b₂⁻¹, v⁆) := by group
    rw [he]
    exact (NOf M V g).mul_mem heq h₂'
  have hfin : ⁅b₁ * b₂⁻¹, v⁆
      = (⁅b₁ * b₂⁻¹, v⁆ * (⁅b₁, v⁆ * ⁅b₂⁻¹, v⁆)⁻¹) * (⁅b₁, v⁆ * ⁅b₂⁻¹, v⁆) := by group
  rw [hfin]
  exact (NOf M V g).mul_mem h₁ hprod

private theorem exists_conj_eq_of_mem_V₀ {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {v : G}
    (hvV : v ∈ V) (hvU : v ∉ UOf M V g) {c : G} (hc : c ∈ V₀) :
    ∃ b₀ ∈ conjSubgroup V₀ g, ⁅b₀, v⁆ = c := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨-, K, -, hKset, -, hlK, hcomm, hcen, hne⟩ := hg
  let φ : ↥(conjSubgroup V₀ g) → ↥V₀ :=
    fun b₀ => ⟨⁅(b₀ : G), v⁆, hcomm (Subgroup.commutator_mem_commutator b₀.2 hvV)⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ heq
    have h1 : ⁅b₁, v⁆ = ⁅b₂, v⁆ := Subtype.ext_iff.1 heq
    have hb₁B : b₁ ∈ BOf M V g := conjSubgroup_V₀_le_B hcopy hb₁
    have hb₂B : b₂ ∈ BOf M V g := conjSubgroup_V₀_le_B hcopy hb₂
    have hhyp : ⁅b₁, v⁆ * ⁅b₂, v⁆⁻¹ ∈ NOf M V g := by
      rw [h1, mul_inv_cancel]
      exact (NOf M V g).one_mem
    have hmemN : ⁅b₁ * b₂⁻¹, v⁆ ∈ NOf M V g :=
      commutator_mul_modN_inv hcopy hb₁B hb₂B hvV hhyp
    have hb₁b₂B : b₁ * b₂⁻¹ ∈ BOf M V g :=
      (BOf M V g).mul_mem hb₁B ((BOf M V g).inv_mem hb₂B)
    have hUB : b₁ * b₂⁻¹ ∈ UOf M V g ⊔ BOf M V g := Subgroup.mem_sup_right hb₁b₂B
    have hU : b₁ * b₂⁻¹ ∈ UOf M V g :=
      stepB hcopy hgen hvV hvU (b₁ * b₂⁻¹) hUB hmemN
    have hV0g : b₁ * b₂⁻¹ ∈ conjSubgroup V₀ g :=
      (conjSubgroup V₀ g).mul_mem hb₁ ((conjSubgroup V₀ g).inv_mem hb₂)
    have hbot : b₁ * b₂⁻¹ ∈ (⊥ : Subgroup G) := by
      have : b₁ * b₂⁻¹ ∈ conjSubgroup V₀ g ⊓ V :=
        ⟨hV0g, (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 ⟨hU, hb₁b₂B⟩).1).1⟩
      rwa [conjSubgroup_V₀_inf_V_eq_bot hcopy] at this
    exact Subtype.ext (mul_inv_eq_one.1 (Subgroup.mem_bot.1 hbot))
  have hφsurj : Function.Surjective φ :=
    (Finite.injective_iff_surjective_of_equiv
      (Subgroup.equivMapOfInjective V₀ (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).symm.toEquiv).1 hφinj
  obtain ⟨b₀, hb₀⟩ := hφsurj ⟨c, hc⟩
  exact ⟨(b₀ : G), b₀.2, congrArg Subtype.val hb₀⟩

private theorem stepF {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {v b : G}
    (hvV : v ∈ V) (hvU : v ∉ UOf M V g) (hbB : b ∈ BOf M V g)
    (hbv : ⁅b, v⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g) :
    b ∈ conjSubgroup V₀ g ⊔ NOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨-, K, -, hKset, -, hlK, hcomm, hcen, hne⟩ := hg
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hbvU : ⁅b, v⁆ ∈ UOf M V g :=
    commutator_B_V_le_U hcopy (Subgroup.commutator_mem_commutator hbB hvV)
  have hLcentN : LOf V g ≤ Subgroup.centralizer (NOf M V g : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy hn) y hy).symm
  have hV0L : V₀ ≤ LOf V g := hV0.trans le_sup_left
  have hV0gL : conjSubgroup V₀ g ≤ LOf V g := (conjSubgroup_mono hV0 g).trans le_sup_right
  have hL0normN : V₀ ⊔ conjSubgroup V₀ g ≤ Subgroup.normalizer (NOf M V g : Set G) :=
    sup_le (hV0L.trans (hLcentN.trans (Subgroup.centralizer_le_normalizer _)))
      (hV0gL.trans (hLcentN.trans (Subgroup.centralizer_le_normalizer _)))
  have hL0N : (↑((V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g) : Set G)
      = (↑(V₀ ⊔ conjSubgroup V₀ g) : Set G) * (↑(NOf M V g) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (V₀ ⊔ conjSubgroup V₀ g) (NOf M V g) hL0normN
  have hbv' : ⁅b, v⁆ ∈ (↑(V₀ ⊔ conjSubgroup V₀ g) : Set G) * (↑(NOf M V g) : Set G) := by
    change ⁅b, v⁆ ∈ (↑((V₀ ⊔ conjSubgroup V₀ g) ⊔ NOf M V g) : Set G) at hbv
    rwa [hL0N] at hbv
  obtain ⟨y, hyL0, n, hnN, hy_eq⟩ := hbv'
  have hnU : n ∈ UOf M V g := (Subgroup.mem_inf.1 hnN).1
  have hyU : y ∈ UOf M V g := by
    have : ⁅b, v⁆ * n⁻¹ ∈ UOf M V g := (UOf M V g).mul_mem hbvU ((UOf M V g).inv_mem hnU)
    rwa [show ⁅b, v⁆ * n⁻¹ = y by rw [← hy_eq]; group] at this
  have hyV0 : y ∈ V₀ := by
    have : y ∈ UOf M V g ⊓ (V₀ ⊔ conjSubgroup V₀ g) := ⟨hyU, hyL0⟩
    rwa [U_inf_sup_V0_conjV0_eq_V0 hcopy] at this
  obtain ⟨b₀, hb₀g, hb₀eq⟩ := exists_conj_eq_of_mem_V₀ hcopy hgen hvV hvU hyV0
  have hb₀B : b₀ ∈ BOf M V g := conjSubgroup_V₀_le_B hcopy hb₀g
  have hL0L : V₀ ⊔ conjSubgroup V₀ g ≤ LOf V g := sup_le hV0L hV0gL
  have hhyp : ⁅b, v⁆ * ⁅b₀, v⁆⁻¹ ∈ NOf M V g := by
    rw [← hy_eq, hb₀eq]
    have hc := NOf_le_centralizer_L hcopy hnN
    have hcommn := Subgroup.mem_centralizer_iff.1 hc y (hL0L hyL0)
    rw [show y * n * y⁻¹ = n by rw [hcommn]; group]
    exact hnN
  have hmemN : ⁅b * b₀⁻¹, v⁆ ∈ NOf M V g :=
    commutator_mul_modN_inv hcopy hbB hb₀B hvV hhyp
  have hb₀B' : b₀ ∈ BOf M V g := hb₀B
  have hUB : b * b₀⁻¹ ∈ UOf M V g ⊔ BOf M V g :=
    Subgroup.mem_sup_right ((BOf M V g).mul_mem hbB ((BOf M V g).inv_mem hb₀B'))
  have hU : b * b₀⁻¹ ∈ UOf M V g :=
    stepB hcopy hgen hvV hvU (b * b₀⁻¹) hUB hmemN
  have hN : b * b₀⁻¹ ∈ NOf M V g := ⟨hU, (BOf M V g).mul_mem hbB ((BOf M V g).inv_mem hb₀B')⟩
  have hb₀invb : b₀⁻¹ * b ∈ NOf M V g := by
    have hconj : b₀⁻¹ * (b * b₀⁻¹) * b₀ ∈ NOf M V g := by
      rw [← conjSubgroup_NOf_eq hcopy (hV0gL hb₀g)]
      rw [mem_conjSubgroup_iff]
      rw [show b₀ * (b₀⁻¹ * (b * b₀⁻¹) * b₀) * b₀⁻¹ = b * b₀⁻¹ by group]
      exact hN
    rwa [show b₀⁻¹ * (b * b₀⁻¹) * b₀ = b₀⁻¹ * b by group] at hconj
  have hb₀sup : b₀ ∈ conjSubgroup V₀ g ⊔ NOf M V g := Subgroup.mem_sup_left hb₀g
  have hNsup : b₀⁻¹ * b ∈ conjSubgroup V₀ g ⊔ NOf M V g := Subgroup.mem_sup_right hb₀invb
  rw [show b = b₀ * (b₀⁻¹ * b) by group]
  exact (conjSubgroup V₀ g ⊔ NOf M V g).mul_mem hb₀sup hNsup

theorem StepFHyp_of_genHyp {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) : StepFHyp M V₀ V g :=
  fun v hvV hvU b hbB hbv => stepF h hgen hvV hvU hbB hbv

theorem six_four_three_of_gen {n : ℕ} {M V₀ V D : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hD : D ≤ BOf M V g) (hDbar : ¬ D ≤ F11.CTilde M V₀ V) :
    V ⊓ Subgroup.centralizer (D : Set G) ≤ UOf M V g ∧
      (∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) →
        v ∈ V ⊓ Subgroup.centralizer (D : Set G)) :=
  six_four_three h (StepFHyp_of_genHyp h hgen) hD hDbar

theorem six_four_four_centralizer_B_of_gen {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g :=
  six_four_four_centralizer_B h (StepFHyp_of_genHyp h hgen)

theorem six_four_four_iff_of_gen {n : ℕ} {M V₀ V : Subgroup G} {g : G} {b : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hbB : b ∈ BOf M V g) (hb : b ∉ F11.CTilde M V₀ V) :
    ∀ v ∈ V, ⁅v, b⁆ ∈ V ⊓ Subgroup.centralizer (BOf M V g : Set G) ↔ v ∈ UOf M V g :=
  six_four_four_iff h (StepFHyp_of_genHyp h hgen) hbB hb

theorem six_four_five {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g)
        * (UOf M V g).relIndex V
      = (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, hcomm, hKset⟩ := inCalOStar_K_facts hcopy
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hlV' : conjSubgroup V l = conjSubgroup V g := hlV.symm
  have hV0l : conjSubgroup V₀ l = conjSubgroup V₀ g :=
    conjSubgroup_V₀_eq_of_conjSubgroup_eq hM hM0 hlV'
  have hBm : conjSubgroup (BOf M V g) l⁻¹ = UOf M V g := by
    have hgl : g * l⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      rw [show g * l⁻¹ = (l * g⁻¹)⁻¹ by group]
      refine (Subgroup.normalizer (V : Set G)).inv_mem ?_
      rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, hlV',
        conjSubgroup_conjSubgroup_inv]
    have hKl : conjSubgroup K l⁻¹ = K :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hlL))
    have hBK : BOf M V g = conjSubgroup V g ⊓ K := by
      rw [hK_eq]; exact (conjSubgroup_V_inf_sup_U_B_eq_B hcopy).symm
    rw [hBK, conjSubgroup_inf, conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.2 hgl, hKl]
    exact V_inf_K_eq_U hcopy hKset
  have hNm : conjSubgroup (NOf M V g) l⁻¹ = NOf M V g :=
    conjSubgroup_NOf_eq hcopy ((LOf V g).inv_mem hlL)
  have hV0gm : conjSubgroup (conjSubgroup V₀ g) l⁻¹ = V₀ := by
    calc conjSubgroup (conjSubgroup V₀ g) l⁻¹ = conjSubgroup (conjSubgroup V₀ l) l⁻¹ := by
          rw [hV0l]
      _ = conjSubgroup V₀ (l * l⁻¹) := by rw [conjSubgroup_conjSubgroup]
      _ = V₀ := by rw [mul_inv_cancel, conjSubgroup_one]
  have hL0gm : conjSubgroup (NOf M V g ⊔ conjSubgroup V₀ g) l⁻¹ = NOf M V g ⊔ V₀ := by
    rw [conjSubgroup_sup, hNm, hV0gm]
  have hNmap : (NOf M V g).map (MulAut.conj l).toMonoidHom = NOf M V g := by
    simpa only [conjSubgroup, inv_inv] using hNm
  have hBmap : (BOf M V g).map (MulAut.conj l).toMonoidHom = UOf M V g := by
    simpa only [conjSubgroup, inv_inv] using hBm
  have hL0map : (NOf M V g ⊔ conjSubgroup V₀ g).map (MulAut.conj l).toMonoidHom
      = NOf M V g ⊔ V₀ := by
    simpa only [conjSubgroup, inv_inv] using hL0gm
  have hcard1 : (NOf M V g).relIndex (UOf M V g) = (NOf M V g).relIndex (BOf M V g) := by
    have := Subgroup.relIndex_map_map_of_injective (NOf M V g) (BOf M V g)
      (f := (MulAut.conj l).toMonoidHom) (MulAut.conj l).injective
    rwa [hNmap, hBmap] at this
  have hcard2 : (NOf M V g).relIndex (NOf M V g ⊔ V₀)
      = (NOf M V g).relIndex (NOf M V g ⊔ conjSubgroup V₀ g) := by
    have := Subgroup.relIndex_map_map_of_injective (NOf M V g)
      (NOf M V g ⊔ conjSubgroup V₀ g)
      (f := (MulAut.conj l).toMonoidHom) (MulAut.conj l).injective
    rwa [hNmap, hL0map] at this
  have hL0g_le_B : NOf M V g ⊔ conjSubgroup V₀ g ≤ BOf M V g :=
    sup_le inf_le_right (conjSubgroup_V₀_le_B hcopy)
  have hL0_le_U : NOf M V g ⊔ V₀ ≤ UOf M V g :=
    sup_le inf_le_left (V₀_le_U hcopy)
  have h1 := Subgroup.relIndex_mul_relIndex (H := NOf M V g)
    (K := NOf M V g ⊔ conjSubgroup V₀ g) (L := BOf M V g) le_sup_left hL0g_le_B
  have h2 := Subgroup.relIndex_mul_relIndex (H := NOf M V g)
    (K := NOf M V g ⊔ V₀) (L := UOf M V g) le_sup_left hL0_le_U
  have hmain : (NOf M V g ⊔ conjSubgroup V₀ g).relIndex (BOf M V g)
      = (NOf M V g ⊔ V₀).relIndex (UOf M V g) := by
    have hEq : (NOf M V g).relIndex (NOf M V g ⊔ conjSubgroup V₀ g)
          * (NOf M V g ⊔ conjSubgroup V₀ g).relIndex (BOf M V g)
        = (NOf M V g).relIndex (NOf M V g ⊔ conjSubgroup V₀ g)
          * (NOf M V g ⊔ V₀).relIndex (UOf M V g) := by
      rw [h1, ← hcard1, ← hcard2, ← h2]
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (E3.relIndex_ne_zero' (NOf M V g ⊔ conjSubgroup V₀ g)
        (NOf M V g))) hEq
  have hCB := six_four_four_centralizer_B_of_gen hcopy hgen
  have hCV := six_four_four_centralizer_V hcopy
  have hCV_le_U : V ⊓ Subgroup.centralizer (BOf M V g : Set G) ≤ UOf M V g := by
    rw [hCV]; exact hL0_le_U
  have hsplit := Subgroup.relIndex_mul_relIndex
    (H := V ⊓ Subgroup.centralizer (BOf M V g : Set G)) (K := UOf M V g) (L := V)
    hCV_le_U inf_le_left
  rw [hCB, hmain, ← hCV]
  exact hsplit

theorem genHyp_of_relIndex_two {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hindex : (UOf M V g).relIndex V = 2) :
    GenHyp M V g := by
  intro x hxVg hxK
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hBrel : (BOf M V g).relIndex (conjSubgroup V g) = 2 := by
    have hcard := Subgroup.relIndex_map_map_of_injective (UOf M V g) V
      (f := (MulAut.conj l⁻¹).toMonoidHom) (MulAut.conj l⁻¹).injective
    have hUmap : (UOf M V g).map (MulAut.conj l⁻¹).toMonoidHom = BOf M V g := by
      change conjSubgroup (UOf M V g) l = BOf M V g
      rw [← V_inf_K_eq_U h hKset, conjSubgroup_inf, ← hlV,
        conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hlL), hK_eq]
      exact conjSubgroup_V_inf_sup_U_B_eq_B h
    have hVmap : V.map (MulAut.conj l⁻¹).toMonoidHom = conjSubgroup V g := by
      change conjSubgroup V l = conjSubgroup V g
      exact hlV.symm
    rw [hUmap, hVmap] at hcard
    exact hcard.trans hindex
  have hxB : x ∉ BOf M V g := fun hxB => hxK (Subgroup.mem_sup_right hxB)
  have hLx_le : BOf M V g ⊔ Subgroup.zpowers x ≤ conjSubgroup V g :=
    sup_le inf_le_left (Subgroup.zpowers_le.2 hxVg)
  have hx_mem : x ∈ BOf M V g ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hne : BOf M V g ⊔ Subgroup.zpowers x ≠ BOf M V g := by
    intro heq
    exact hxB (heq ▸ hx_mem)
  have hmul := Subgroup.relIndex_mul_relIndex (H := BOf M V g)
    (K := BOf M V g ⊔ Subgroup.zpowers x) (L := conjSubgroup V g) le_sup_left hLx_le
  rw [hBrel] at hmul
  have hfirst : (BOf M V g).relIndex (BOf M V g ⊔ Subgroup.zpowers x) = 2 := by
    have hne1 : (BOf M V g).relIndex (BOf M V g ⊔ Subgroup.zpowers x) ≠ 1 := by
      intro hone
      exact hne (le_antisymm (Subgroup.relIndex_eq_one.1 hone) le_sup_left)
    have hdvd : (BOf M V g).relIndex (BOf M V g ⊔ Subgroup.zpowers x) ∣ 2 :=
      ⟨(BOf M V g ⊔ Subgroup.zpowers x).relIndex (conjSubgroup V g), hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  have hsecond : (BOf M V g ⊔ Subgroup.zpowers x).relIndex (conjSubgroup V g) = 1 := by
    have h2 := hmul
    rw [hfirst] at h2
    omega
  have hVg_le : conjSubgroup V g ≤ BOf M V g ⊔ Subgroup.zpowers x :=
    Subgroup.relIndex_eq_one.1 hsecond
  calc LOf V g = V ⊔ conjSubgroup V g := rfl
    _ ≤ V ⊔ (BOf M V g ⊔ Subgroup.zpowers x) :=
        sup_le le_sup_left (hVg_le.trans le_sup_right)
    _ = (V ⊔ Subgroup.zpowers x) ⊔ BOf M V g := by ac_rfl
    _ ≤ (V ⊔ Subgroup.zpowers x) ⊔ (UOf M V g ⊔ BOf M V g) :=
        sup_le le_sup_left (le_sup_right.trans le_sup_right)

theorem six_four_three_of_relIndex_two {n : ℕ} {M V₀ V D : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hindex : (UOf M V g).relIndex V = 2)
    (hD : D ≤ BOf M V g) (hDbar : ¬ D ≤ F11.CTilde M V₀ V) :
    V ⊓ Subgroup.centralizer (D : Set G) ≤ UOf M V g ∧
      (∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) →
        v ∈ V ⊓ Subgroup.centralizer (D : Set G)) :=
  six_four_three h (StepFHyp_of_genHyp h (genHyp_of_relIndex_two h hindex)) hD hDbar

theorem six_four_four_centralizer_B_of_relIndex_two {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hindex : (UOf M V g).relIndex V = 2) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g :=
  six_four_four_centralizer_B h (StepFHyp_of_genHyp h (genHyp_of_relIndex_two h hindex))

theorem six_four_four_iff_of_relIndex_two {n : ℕ} {M V₀ V : Subgroup G} {g : G} {b : G}
    (h : Hyp64 n M V₀ V g) (hindex : (UOf M V g).relIndex V = 2)
    (hbB : b ∈ BOf M V g) (hb : b ∉ F11.CTilde M V₀ V) :
    ∀ v ∈ V, ⁅v, b⁆ ∈ V ⊓ Subgroup.centralizer (BOf M V g : Set G) ↔ v ∈ UOf M V g :=
  six_four_four_iff h (StepFHyp_of_genHyp h (genHyp_of_relIndex_two h hindex)) hbB hb

theorem six_four_five_of_relIndex_two {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hindex : (UOf M V g).relIndex V = 2) :
    (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g)
        * (UOf M V g).relIndex V
      = (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V :=
  six_four_five h (genHyp_of_relIndex_two h hindex)

theorem commutator_U_sup_B_le_N {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    ⁅UOf M V g, UOf M V g ⊔ BOf M V g⁆ ≤ NOf M V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N hcopy).trans inf_le_right
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have hk' : k ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) := hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB] at hk'
  obtain ⟨u', hu', b, hb, rfl⟩ := hk'
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅u, u'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hu.1 hu'.1)
  have h2 : ⁅u, b⁆ ∈ NOf M V g :=
    commutator_U_B_le_N hcopy (Subgroup.commutator_mem_commutator hu hb)
  rw [h1, one_mul]
  have hcomm := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy h2) u'
    (Subgroup.mem_sup_left hu'.1)
  rwa [show u' * ⁅u, b⁆ * u'⁻¹ = ⁅u, b⁆ by rw [hcomm]; group]

theorem mem_U_of_commutator_le_N {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hindex : (UOf M V g).relIndex V = 2)
    {k : G} (hkK : k ∈ UOf M V g ⊔ BOf M V g)
    (hkV : ∀ v ∈ V, ⁅k, v⁆ ∈ NOf M V g) : k ∈ UOf M V g := by
  have hne : UOf M V g ≠ V := by
    intro heq
    have h1 := hindex
    rw [heq, Subgroup.relIndex_self] at h1
    exact (by norm_num at h1 : (1 : ℕ) ≠ 2) h1
  obtain ⟨v₀, hv₀V, hv₀U⟩ : ∃ v ∈ V, v ∉ UOf M V g := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm inf_le_left hcon)
  exact stepB h hgen hv₀V hv₀U k hkK (hkV v₀ hv₀V)

theorem conjSubgroup_U_eq_of_sup_eq {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hindex : (UOf M V g).relIndex V = 2)
    {x : G} (hxL : x ∈ LOf V g)
    (hxK : conjSubgroup V x ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g)) :
    conjSubgroup (UOf M V g) x = UOf M V g := by
  have hcopy := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hKx : conjSubgroup K x = K :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hxL)
  have hxK' : conjSubgroup V x ⊔ K = V ⊔ K := by rw [hK_eq]; exact hxK
  have hxinvK' : conjSubgroup V x⁻¹ ⊔ K = V ⊔ K := by
    have h1 := congrArg (fun H : Subgroup G => conjSubgroup H x⁻¹) hxK'
    rw [conjSubgroup_sup, conjSubgroup_sup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one,
      conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hxL))] at h1
    exact h1.symm
  have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
    fun v hv => hKnorm_L (Subgroup.mem_sup_left hv)
  have stepGen : ∀ w ∈ LOf V g, conjSubgroup V w⁻¹ ⊔ K = V ⊔ K →
      ∀ u ∈ UOf M V g, w⁻¹ * u * w ∈ UOf M V g := by
    intro w hwL hwKinv u hu
    apply mem_U_of_commutator_le_N hcopy hgen hindex
    · have hmem : w⁻¹ * u * w ∈ conjSubgroup K w := by
        rw [mem_conjSubgroup_iff]
        rw [show w * (w⁻¹ * u * w) * w⁻¹ = u by group]
        exact hK_eq ▸ Subgroup.mem_sup_left hu
      rw [conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hwL)] at hmem
      simpa [hK_eq] using hmem
    · intro v hv
      have hvv : w * v * w⁻¹ ∈ V ⊔ K := by
        have hv1 : w * v * w⁻¹ ∈ conjSubgroup V w⁻¹ := by
          rw [mem_conjSubgroup_iff]
          rw [show (w⁻¹) * (w * v * w⁻¹) * (w⁻¹)⁻¹ = v by group]
          exact hv
        rw [← hwKinv]
        exact Subgroup.mem_sup_left hv1
      have hvv' : w * v * w⁻¹ ∈ (↑(V ⊔ K) : Set G) := hvv
      rw [Subgroup.coe_mul_of_left_le_normalizer_right V K hVK] at hvv'
      obtain ⟨v₁, hv₁V, k₁, hk₁K, hvv1⟩ := hvv'
      have key1 : ⁅u, v₁ * k₁⁆ ∈ NOf M V g := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : ⁅u, v₁⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hu.1 hv₁V)
        have h2 : ⁅u, k₁⁆ ∈ NOf M V g :=
          commutator_U_sup_B_le_N hcopy
            (Subgroup.commutator_mem_commutator hu (hK_eq ▸ hk₁K))
        rw [h1, one_mul]
        have hcomm2 := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy h2) v₁
          (Subgroup.mem_sup_left hv₁V)
        rwa [show v₁ * ⁅u, k₁⁆ * v₁⁻¹ = ⁅u, k₁⁆ by rw [hcomm2]; group]
      have hxv : w * v * w⁻¹ = v₁ * k₁ := hvv1.symm
      have hfin : w⁻¹ * ⁅u, w * v * w⁻¹⁆ * w ∈ NOf M V g := by
        rw [hxv]
        have hc := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy key1) w⁻¹
          ((LOf V g).inv_mem hwL)
        rwa [show w⁻¹ * ⁅u, v₁ * k₁⁆ * w = ⁅u, v₁ * k₁⁆ by rw [hc]; group]
      have hconj : ⁅w⁻¹ * u * w, v⁆ = w⁻¹ * ⁅u, w * v * w⁻¹⁆ * w := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [hconj]
      exact hfin
  have step : ∀ u ∈ UOf M V g, x⁻¹ * u * x ∈ UOf M V g :=
    stepGen x hxL hxinvK'
  have step' : ∀ u ∈ UOf M V g, (x⁻¹)⁻¹ * u * x⁻¹ ∈ UOf M V g :=
    stepGen x⁻¹ ((LOf V g).inv_mem hxL) (by simpa using hxK')
  apply le_antisymm
  · intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have := step (x * y * x⁻¹) hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
  · intro u hu
    rw [mem_conjSubgroup_iff]
    simpa using step' u hu

theorem conjSubgroup_V_eq_of_sup_eq {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hindex : (UOf M V g).relIndex V = 2)
    {x : G} (hxL : x ∈ LOf V g)
    (hxK : conjSubgroup V x ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g)) :
    conjSubgroup V x = V := by
  have hcopy := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hxle : conjSubgroup V x ≤ V ⊔ (UOf M V g ⊔ BOf M V g) := by
    rw [← hxK]; exact le_sup_left
  have hUx := conjSubgroup_U_eq_of_sup_eq hcopy hgen hindex hxL hxK
  have hKx : conjSubgroup K x = K :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hxL)
  have hXK : conjSubgroup V x ⊓ K = UOf M V g := by
    have hconj : conjSubgroup (V ⊓ K) x = conjSubgroup V x ⊓ K := by
      rw [conjSubgroup_inf, hKx]
    rw [V_inf_K_eq_U hcopy hKset, hUx] at hconj
    exact hconj.symm
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N hcopy).trans inf_le_right
  have hBV : BOf M V g ≤ Subgroup.normalizer (V : Set G) := by
    intro b hb
    rw [hM]
    exact hb.2
  have hXea : IsElemAbelian 2 (conjSubgroup V x) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj x⁻¹).toMonoidHom
  have hVgea : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  have hXleV : conjSubgroup V x ≤ V := by
    intro y hy
    by_cases hyK : y ∈ K
    · have hy' : y ∈ conjSubgroup V x ⊓ K := ⟨hy, hyK⟩
      rw [hXK] at hy'
      exact (Subgroup.mem_inf.1 hy').1
    · have hyVB : y ∈ V ⊔ BOf M V g := by
        have h1 : y ∈ V ⊔ (UOf M V g ⊔ BOf M V g) := hxle hy
        have heq : V ⊔ (UOf M V g ⊔ BOf M V g) = V ⊔ BOf M V g := by
          apply le_antisymm
          · exact sup_le le_sup_left
              (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
          · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
        rwa [heq] at h1
      have hyVB' : y ∈ (↑(V ⊔ BOf M V g) : Set G) := hyVB
      rw [Subgroup.coe_mul_of_right_le_normalizer_left V (BOf M V g) hBV] at hyVB'
      obtain ⟨v, hvV, b, hbB, hvb⟩ := hyVB'
      have hvb' : v * b = y := hvb
      have hy2 : (v * b) * (v * b) = 1 := by
        rw [hvb']; exact IsElemAbelian.mul_self_eq_one hXea hy
      have hbb : b * b = 1 := IsElemAbelian.mul_self_eq_one hVgea hbB.1
      have hvv : v * v = 1 := IsElemAbelian.mul_self_eq_one hV hvV
      have hcomm : v * b = b * v := by
        have h1 : v * b * v * b = 1 := by simpa [mul_assoc] using hy2
        have h3 : v * b * v = b := by
          have := congrArg (fun z => z * b) h1
          simpa [mul_assoc, hbb] using this
        have hleft : v * (v * b * v) = v * b := by rw [h3]
        have hright : v * (v * b * v) = b * v := by
          calc v * (v * b * v) = (v * v) * (b * v) := by group
            _ = b * v := by rw [hvv, one_mul]
        exact (hright.symm.trans hleft).symm
      have hvb1 : ⁅v, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm
      have hbv1 : ⁅b, v⁆ = 1 := by
        rw [show ⁅b, v⁆ = ⁅v, b⁆⁻¹ from (commutatorElement_inv v b).symm, hvb1, inv_one]
      have hvU : v ∉ UOf M V g := by
        intro hvU
        apply hyK
        have hmem : v * b ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) := by
          rw [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB]
          exact ⟨v, hvU, b, hbB, rfl⟩
        rw [hvb'] at hmem
        rwa [← hK_eq] at hmem
      have hbU : b ∈ UOf M V g :=
        stepB hcopy hgen hvV hvU b (Subgroup.mem_sup_right hbB)
          (by rw [hbv1]; exact (NOf M V g).one_mem)
      rw [← hvb']
      exact V.mul_mem hvV (Subgroup.mem_inf.1 hbU).1
  exact Subgroup.eq_of_le_of_card_ge hXleV (by
    have hcard : Nat.card (conjSubgroup V x) = Nat.card V := by
      simpa [conjSubgroup] using Subgroup.card_map_of_injective (K := V)
        (f := (MulAut.conj x⁻¹).toMonoidHom) (MulAut.conj x⁻¹).injective
    rw [hcard])

theorem conjSubgroup_V_eq_conjSubgroup_V_of_sup_eq {n : ℕ} {M V₀ V : Subgroup G}
    {g : G} (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hindex : (UOf M V g).relIndex V = 2) {w : G} (hwL : w ∈ LOf V g)
    (hwK : conjSubgroup V w ⊔ (UOf M V g ⊔ BOf M V g)
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g)) :
    conjSubgroup V w = conjSubgroup V g := by
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨l₀, hl₀L, hl₀V⟩ := hlK
  have hwK' : conjSubgroup V w ⊔ K = conjSubgroup V g ⊔ K := by rw [hK_eq]; exact hwK
  have hgl : conjSubgroup (conjSubgroup V g) l₀⁻¹ = V := by
    rw [hl₀V, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hxL : w * l₀⁻¹ ∈ LOf V g := (LOf V g).mul_mem hwL ((LOf V g).inv_mem hl₀L)
  have hxK : conjSubgroup V (w * l₀⁻¹) ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g) := by
    have h1 := congrArg (fun H : Subgroup G => conjSubgroup H l₀⁻¹) hwK'
    rw [conjSubgroup_sup, conjSubgroup_sup,
      conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hl₀L))] at h1
    rw [conjSubgroup_conjSubgroup, hgl, hK_eq] at h1
    exact h1
  have hVx := conjSubgroup_V_eq_of_sup_eq h hgen hindex hxL hxK
  have h2 : conjSubgroup V w = conjSubgroup V l₀ := by
    have h2 := congrArg (fun H : Subgroup G => conjSubgroup H l₀) hVx
    rw [conjSubgroup_conjSubgroup] at h2
    simpa [mul_assoc] using h2
  exact h2.trans hl₀V.symm

theorem swapHyp_of_sup_eq_and_mem {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hindex : (UOf M V g).relIndex V = 2) {w : G} (hwL : w ∈ LOf V g)
    (hwK : conjSubgroup V w ⊔ (UOf M V g ⊔ BOf M V g)
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g))
    (hw2 : w * w ∈ UOf M V g ⊔ BOf M V g) :
    SwapHyp V g := by
  have hcopy := h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hVM : V ≤ M := by rw [← hM]; exact Subgroup.le_normalizer
  have hVw := conjSubgroup_V_eq_conjSubgroup_V_of_sup_eq hcopy hgen hindex hwL hwK
  have hKM : UOf M V g ⊔ BOf M V g ≤ M :=
    sup_le (fun u hu => hVM (Subgroup.mem_inf.1 hu).1) (fun b hb => hb.2)
  have hsqV : conjSubgroup V (w * w) = V :=
    conjSubgroup_eq_iff_mem_normalizer.2 (by rw [hM]; exact hKM hw2)
  refine ⟨w, hwL, hVw, ?_⟩
  rw [← hVw, conjSubgroup_conjSubgroup]
  exact hsqV

theorem mul_sq_eq_one_of_odd {m : ℕ} (hm : Odd m) {z a : DihedralGroup m}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hz2 : z * z ≠ 1) : (a * z) * (a * z) = 1 := by
  cases a with
  | r i =>
    exfalso
    apply ha1
    have hii : i + i = 0 := by
      have h : DihedralGroup.r (i + i) = DihedralGroup.r 0 := by
        simpa [DihedralGroup.r_mul_r] using ha2
      injection h
    rw [(ZMod.add_self_eq_zero_iff_eq_zero hm).1 hii]
    exact DihedralGroup.r_zero
  | sr j =>
    cases z with
    | r i => simp
    | sr k => exact absurd (DihedralGroup.sr_mul_self k) hz2

private theorem map_conj_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (A : Subgroup X) (z : X) :
    (A.map (MulAut.conj z⁻¹).toMonoidHom).map e.toMonoidHom
      = (A.map e.toMonoidHom).map (MulAut.conj (e z)⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

theorem exists_involution_conj_of_dihedral {X : Type*} [Group X] {m : ℕ} (hm : Odd m)
    (e : X ≃* DihedralGroup m) {A B : Subgroup X} {z₀ : X}
    (hz₀ : conjSubgroup A z₀ = B)
    (ha : ∃ a ∈ A, a ≠ 1 ∧ a * a = 1) :
    ∃ z : X, z * z = 1 ∧ conjSubgroup A z = B := by
  obtain ⟨a, haA, ha1, ha2⟩ := ha
  set A' : Subgroup (DihedralGroup m) := A.map e.toMonoidHom with hA'def
  set B' : Subgroup (DihedralGroup m) := B.map e.toMonoidHom with hB'def
  have hmem : e a ∈ A' := by
    rw [hA'def]; exact Subgroup.mem_map_of_mem e.toMonoidHom haA
  have ha1' : e a ≠ 1 := fun h => ha1 (e.injective (by simpa using h))
  have ha2' : e a * e a = 1 := by rw [← map_mul, ha2, map_one]
  have hz₀' : conjSubgroup A' (e z₀) = B' := by
    show A'.map (MulAut.conj (e z₀)⁻¹).toMonoidHom = B'
    rw [hB'def, hA'def, ← map_conj_eq e A z₀]
    exact congrArg (fun H : Subgroup X => H.map e.toMonoidHom)
      (by simpa [conjSubgroup] using hz₀)
  have key : ∃ z' : DihedralGroup m, z' * z' = 1 ∧ conjSubgroup A' z' = B' := by
    by_cases h1 : (e z₀) * (e z₀) = 1
    · exact ⟨e z₀, h1, hz₀'⟩
    · refine ⟨e a * e z₀, mul_sq_eq_one_of_odd hm ha2' ha1' h1, ?_⟩
      rw [← conjSubgroup_conjSubgroup,
        conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hmem), hz₀']
  obtain ⟨z', hz'2, hz'conj⟩ := key
  refine ⟨e.symm z', ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_one]
    simpa using hz'2
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    show (A.map (MulAut.conj (e.symm z')⁻¹).toMonoidHom).map e.toMonoidHom = B.map e.toMonoidHom
    rw [map_conj_eq e A (e.symm z'), show e (e.symm z') = z' by simp, ← hA'def]
    change conjSubgroup A' z' = B'
    rw [hz'conj]

end CFSG.LocalAnalysis.WeakClosure81

