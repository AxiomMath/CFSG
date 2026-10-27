module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5AllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepRefl
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepCore
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggJoin_weyl_a5 (hAll : LR6A5All) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp3 : p = 3) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs) {z : G} (hz : z ∈ Bs)
    {A₁ A₂ : Subgroup (MulAut ↥Bs)} (hA : A₁ ⊔ A₂ ≤ ggAutomizer ⊤ Bs)
    (hstab : Nat.card ↥((A₁ ⊔ A₂) ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥A₁)
    (hgen₂ : GGReflGenerated p A₂)
    (hmove : ∃ t ∈ A₂, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (e : Fin (6 - 1) ≃ Λ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hA₁ : A₁ = Subgroup.closure (Set.range φ))
    (F : GGIndepAFrame p 6 (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨z, hz⟩))) :
    GGWeylReflectionGroup p (A₁ ⊔ A₂) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardA1 : Nat.card ↥A₁ ≤ Nat.factorial 6 :=
    ggIndep_card_A1 hp2 (by norm_num) hz ι hφ hA₁ e F
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
  have hdim : Module.finrank (ZMod p) V ≤ 6 := ggIndepFrame_finrank_le (by norm_num) F
  have hBs : Nat.card ↥Bs ≤ p ^ 6 := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdim
  let r : Fin (6 - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hr : ∀ (i : Fin (6 - 1)) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hφsup : ∀ i, φ i ∈ A₁ ⊔ A₂ := fun i =>
    Subgroup.mem_sup_left (by rw [hA₁]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hgen' : GGReflGenerated p (A₁ ⊔ A₂) :=
    ggIndep_reflGenerated_sup (ggIndep_reflGenerated_of_closure hrefl hA₁) hgen₂
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (MulAut ↥Bs), A' = A₁ ⊔ A₂ := ⟨_, rfl⟩
  rw [← hA'] at hgen' hA hφsup hstab
  have hrA : ∀ i : Fin (6 - 1), r i ∈ A'.map (ggLin (p := p) ι) := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφsup (e i), rfl⟩
  have hgenA : A'.map (ggLin (p := p) ι) =
      Subgroup.closure {s | s ∈ A'.map (ggLin (p := p) ι) ∧ GGLinRefl s} := by
    apply le_antisymm
    · calc A'.map (ggLin (p := p) ι)
          = (Subgroup.closure {ψ | ψ ∈ A' ∧ GGIsReflection p ψ}).map (ggLin (p := p) ι) := by
            rw [← hgen']
        _ = Subgroup.closure ((ggLin (p := p) ι) '' {ψ | ψ ∈ A' ∧ GGIsReflection p ψ}) :=
            MonoidHom.map_closure _ _
        _ ≤ Subgroup.closure {s | s ∈ A'.map (ggLin (p := p) ι) ∧ GGLinRefl s} := by
            apply Subgroup.closure_mono
            rintro _ ⟨ψ, ⟨hψA, hψr⟩, rfl⟩
            exact ⟨Subgroup.mem_map.mpr ⟨ψ, hψA, rfl⟩,
              (ggRC_isReflection_iff_linRefl (p := p) ι ψ).mp hψr⟩
    · rw [Subgroup.closure_le]
      intro w hw
      exact hw.1
  have hnt : ∀ g ∈ A'.map (ggLin (p := p) ι),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hmem := hA hψA
      rw [ggAutomizer_eq] at hmem
      exact hmem
    exact hNT ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hcardA : Nat.card ↥(A'.map (ggLin (p := p) ι)) ≤ p ^ 6 * (6 * (p - 1) * Nat.factorial 6) := by
    have hjoin := ggIndep_card_join_le A' ⟨z, hz⟩ hstab
    calc Nat.card ↥(A'.map (ggLin (p := p) ι)) = Nat.card ↥A' :=
          (Nat.card_congr (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥A₁) := hjoin
      _ ≤ p ^ 6 * ((p - 1) * 6 * Nat.factorial 6) :=
          Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hcardA1)
      _ = p ^ 6 * (6 * (p - 1) * Nat.factorial 6) := by ring
  obtain ⟨t, ht2, htrefl, htmove⟩ := hmove
  have hmoveA : ∃ s ∈ A'.map (ggLin (p := p) ι), GGLinRefl s ∧
      s (ι (Additive.ofMul ⟨z, hz⟩)) ≠ ι (Additive.ofMul ⟨z, hz⟩) := by
    refine ⟨ggLin (p := p) ι t, Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩,
      (ggRC_isReflection_iff_linRefl (p := p) ι t).mp htrefl, ?_⟩
    · rw [hA']
      exact Subgroup.mem_sup_right ht2
    · intro hfix
      exact htmove ((ggLin_fix_iff (p := p) ι t ⟨z, hz⟩).mpr hfix)
  have hlin := hAll p hp3 V hdim (fun i => h (e i)) (fun i => α (e i))
    (ι (Additive.ofMul ⟨z, hz⟩)) r F hr (A'.map (ggLin (p := p) ι)) hrA hgenA hnt hcardA hmoveA
  rw [← hA']
  exact ggRC_weylReflGroup_of_linWeyl ι A' hlin

theorem ggTwoNodeIndepAtL_a5_of_moving_K (hAll : LR6A5All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin (6 - 1) ≃ Λ)
    (hML : ML = (CoxeterMatrix.A (6 - 1)).reindex e) (hCL : GGIntCartan ML CL) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V} (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hpN : p ∣ 6 := by rw [hp3]; norm_num
  have F := ggXDatumA_indep_frame hFix hp2 hH hx (by norm_num) hpN e hML hCL hφ hpair hAL hind
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  exact ggJoin_weyl_a5 hAll hp3 hH.2.2.2.1 hx hA (hOrb G p B Bs x L D J y K hH hx)
    hH.2.2.2.2.2.1 hmoveK e hφ hrefl hAL F

theorem ggTwoNodeIndepAtL_a5 (hAll : LR6A5All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin (6 - 1) ≃ Λ)
    (hML : ML = (CoxeterMatrix.A (6 - 1)).reindex e) (hCL : GGIntCartan ML CL) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V} (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exact ggTwoNodeIndepAtL_a5_of_moving_K hAll hOrb hFix hp3 hH hx
    (ggIndep_moving_K hFixK hH hx) e hML hCL hφ hrefl hpair hAL hind

theorem ggTwoNodeIndepAtK_a5 (hAll : LR6A5All) (hOrbK : GGResCentBoundNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs))
    (hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (6 - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (6 - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hpN : p ∣ 6 := by rw [hp3]; norm_num
  have F := ggXDatumA_indep_frame_K hp2 hH hy hstrong (by norm_num) hpN e hMK hCK hφ hpair hAK hind
  have hA : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hstab : Nat.card ↥((ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
    rw [sup_comm]
    exact hOrbK G p B Bs x L D J y K hH hy
  exact ggJoin_weyl_a5 hAll hp3 hH.2.2.2.1 hy hA hstab hLrefl hmove e hφ hrefl hAK F

private lemma a5C_row_facts {p : ℕ} {J X : LargeEvenLabel} (h : ggRowTwoNode p J X)
    (htag : X.tag = .A ∨ X.tag = .twA) :
    J.rank + 2 = X.rank ∧ p ∣ X.rank + 1 ∧ (J.tag = .A ∨ J.tag = .twA) := by
  rcases h with ⟨hJ, -, hd, hX⟩ | ⟨hJ, -, hd, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · subst hX
    exact ⟨rfl, by simpa using hd, Or.inl hJ⟩
  · subst hX
    exact ⟨rfl, by simpa using hd, Or.inr hJ⟩
  · exfalso
    have hE : X.tag = .E6 := by rw [hX]
    rcases htag with h | h <;> rw [hE] at h <;> exact absurd h (by decide)
  · exfalso
    have hE : X.tag = .twE6 := by rw [hX]
    rcases htag with h | h <;> rw [hE] at h <;> exact absurd h (by decide)

private lemma a5C_lambda2_rank_lower {lab : LargeEvenLabel} (h : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A ∨ lab.tag = .twA) : 1 ≤ lab.rank := by
  rcases h with ⟨-, h⟩
  rcases htag with hA | hA
  · rw [hA] at h
    exact h.1
  · rw [hA] at h
    omega

private lemma a5C_rank_five {J X : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 J) (h : ggRowTwoNode 3 J X)
    (htag : X.tag = .A ∨ X.tag = .twA) (hsmall : X.rank < (if 3 = 3 then 8 else 9)) : X.rank = 5 := by
  obtain ⟨hrank, hpN, hJtag⟩ := a5C_row_facts h htag
  have hJrank : 1 ≤ J.rank := a5C_lambda2_rank_lower hJΛ hJtag
  have hlt : X.rank < 8 := by simpa using hsmall
  obtain ⟨k, hk⟩ := hpN
  omega

private lemma a5C_datum {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGTwoNodeIndepDatum)
    {X : Subgroup G} {z : G} (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) {labJ labX : LargeEvenLabel}
    (hJΛ : LargeEvenInLambda2 labJ) (hXΛ : LargeEvenInLambda2 labX)
    (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) (hXlab : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hRowN : ggRowTwoNode 3 labJ labX) (htag : labX.tag = .A ∨ labX.tag = .twA) (hz : z ∈ X)
    (hrank : labX.rank = 5) : GGResXDatumAIndep 3 Bs X labX.rank := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hD G 3 B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJlab hXlab hRowN hz with
    ⟨-, hA⟩ | ⟨hE', -⟩
  · rcases hA with hAx | ⟨hpg, -⟩
    · obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        ⟨f, hf⟩, hAL, hind⟩ := hAx
      exact ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair,
        ⟨f, hf⟩, hAL, hind hz⟩
    · exfalso
      have h1 : 3 ^ 2 ∣ labX.rank + 1 := dvd_trans hpg (Nat.gcd_dvd_left _ _)
      rw [hrank] at h1
      omega
  · exfalso
    rcases hE' with h | h <;> rcases htag with h' | h' <;>
      exact absurd (h.symm.trans h') (by decide)

theorem ggResTwoNodeIndepA5L (hAll : LR6A5All) (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) (hD : GGTwoNodeIndepDatum) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowTwoNodeSmallA p J L)
    (hxL : x ∈ L) : GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  subst hp3
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨⟨hRowN, hsmall⟩, htag⟩⟩ := hrow
  have hrank : labX.rank = 5 := a5C_rank_five hJΛ hRowN htag hsmall
  have hXI := a5C_datum hH hD (Or.inl ⟨rfl, rfl⟩) hJΛ hXΛ hJlab hXlab hRowN htag hxL hrank
  rw [hrank] at hXI
  obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩, hAL,
    hind⟩ := hXI
  let := iF; let := iD; let := iAC; let := iM
  exact ggTwoNodeIndepAtL_a5 hAll hOrb hFix hFixK rfl hH hx e hMeq hC hφ hrefl hpair hAL hind

theorem ggResTwoNodeIndepA5K_of_reflGenerated (hAll : LR6A5All) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hKFix : GGTwoNodeKFixLineInput) (hD : GGTwoNodeIndepDatum) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallA p J K) (hyK : y ∈ K)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := by omega
  subst hp3
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨⟨hRowN, hsmall⟩, htag⟩⟩ := hrow
  have hrank : labX.rank = 5 := a5C_rank_five hJΛ hRowN htag hsmall
  have hXI := a5C_datum hH hD (Or.inr ⟨rfl, rfl⟩) hJΛ hXΛ hJlab hXlab hRowN htag hyK hrank
  rw [hrank] at hXI
  have hrowN : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = 6) 3 J K :=
    ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, ⟨hRowN, by omega⟩⟩
  have hXI' : GGResXDatumAIndep 3 Bs K (6 - 1) := hXI
  have hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y :=
    fun b hb => (hKFix G 3 B Bs x L D J y K 6 hH hF hS hE hrowN hp2 (by norm_num) (by norm_num)
      (by norm_num) hyK hXI' b).mp hb
  have hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection 3 t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩ :=
    ggIndep_moving_L hFix hH hy hLrefl
  obtain ⟨Λ, iF, iD, M, C, V, iAC, iM, ι, φ, h, α, e, hMeq, hW, hC, hφ, hrefl, hpair, ⟨f, hf⟩, hAK,
    hind⟩ := hXI
  let := iF; let := iD; let := iAC; let := iM
  rw [sup_comm]
  exact ggTwoNodeIndepAtK_a5 hAll hOrbK rfl hH hy hstrong hLrefl hmove e hMeq hC hφ hrefl hpair hAK hind

theorem ggResTwoNodeIndepA5K (hAll : LR6A5All) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hKFix : GGTwoNodeKFixLineInput) (hD : GGTwoNodeIndepDatum) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hF : ¬ GGCoxeterForkDatum p Bs L K)
    (hS : ¬ GGCoxeterStdDatum p Bs L K) (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (hrow : GGResRowAt ggRowTwoNodeSmallA p J K) (hyK : y ∈ K)
    (hL : GGResTwoNodeSideDatum p Bs L J) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hLrefl : GGReflGenerated p (ggAutomizer L Bs) := by
    obtain ⟨Λ, i1, i2, b₁, b₂, M, C, MJ, V, i3, i4, ι, φ, h, α, hb, hW, hC, hWJ, hMJ, hlin, hrefl,
      hpair, hf, hcl, hfJ, hclJ, hconj⟩ := hL
    exact ggIndep_reflGenerated_of_closure hrefl hcl
  exact ggResTwoNodeIndepA5K_of_reflGenerated hAll hOrbK hFix hKFix hD hp3 hH hF hS hE
    hrow hyK hLrefl

end CFSG.StandardType

end
