module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepThreeChain
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeIndepAtL_three (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 9 ≤ N) (hpN : p ∣ N)
    (hmove : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have F := ggXDatumA_indep_frame hFix hp2 hH hx (by omega) hpN e hML hCL hφ hpair hAL hind
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  obtain ⟨t, ha, αa, htA₂, hform, hαa, hw, hnt⟩ :=
    ggIndep_pos_prep (N := N) hH.2.2.2.1 hx hA hmove e hAL (ι := ι)
  by_cases hmem : ha ∈ Submodule.span (ZMod p) (Set.range fun i => h (e i))
  · exfalso
    subst hp3
    let r : Fin (N - 1) → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
    have hr : ∀ (i : Fin (N - 1)) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
    let A : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range r ∪ {ggLin (p := 3) ι t})
    have hrA : ∀ i, r i ∈ A := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
    have htA : ggLin (p := 3) ι t ∈ A := Subgroup.subset_closure (Or.inr rfl)
    have hcα := ggIndep_center_functional_vanish hpN F.pair hmem
    have hfix0 := ggIndep_p3_fixes_x (fun i => h (e i)) (fun i => α (e i))
      (fun i => (((i : ℕ) + 1 : ℕ) : ZMod 3)) F.pair A hnt r hr hrA (ggLin (p := 3) ι t) htA ha αa
      hcα hform hαa
    obtain ⟨c, hc0, hxc⟩ := ggIndep_x_eq_smul_center hpN (by omega) F.pair F.indep F.fix
    apply hw
    rw [hxc, map_smul, hfix0, smul_zero]
  · exact ggIndep_pos_branch hKG hp2 hN hx hA (hOrb G p B Bs x L D J y K hH hx)
      hH.2.2.2.2.2.1 e hφ hrefl hAL F htA₂ hform hαa hw hnt hmem
      (fun h5 => absurd h5 (by omega))

theorem ggTwoNodeIndepAtK_three (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs)) {N : ℕ} (hN : 9 ≤ N) (hpN : p ∣ N)
    (hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer K Bs ⊔ ggAutomizer L Bs) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have F := ggXDatumA_indep_frame_K hp2 hH hy hstrong (by omega) hpN e hMK hCK hφ hpair hAK hind
  have hA : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hstab : Nat.card ↥((ggAutomizer K Bs ⊔ ggAutomizer L Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
    rw [sup_comm]
    exact hOrbK G p B Bs x L D J y K hH hy
  obtain ⟨t, ha, αa, htA₂, hform, hαa, hw, hnt⟩ :=
    ggIndep_pos_prep (N := N) hH.2.2.2.1 hy hA hmove e hAK (ι := ι)
  by_cases hmem : ha ∈ Submodule.span (ZMod p) (Set.range fun i => h (e i))
  · exfalso
    subst hp3
    let r : Fin (N - 1) → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
    have hr : ∀ (i : Fin (N - 1)) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
    let A : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range r ∪ {ggLin (p := 3) ι t})
    have hrA : ∀ i, r i ∈ A := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
    have htA : ggLin (p := 3) ι t ∈ A := Subgroup.subset_closure (Or.inr rfl)
    have hcα := ggIndep_center_functional_vanish hpN F.pair hmem
    have hfix0 := ggIndep_p3_fixes_x (fun i => h (e i)) (fun i => α (e i))
      (fun i => (((i : ℕ) + 1 : ℕ) : ZMod 3)) F.pair A hnt r hr hrA (ggLin (p := 3) ι t) htA ha αa
      hcα hform hαa
    obtain ⟨c, hc0, hxc⟩ := ggIndep_x_eq_smul_center hpN (by omega) F.pair F.indep F.fix
    apply hw
    rw [hxc, map_smul, hfix0, smul_zero]
  · exact ggIndep_pos_branch hKG hp2 hN hy hA hstab hLrefl e hφ hrefl hAK F htA₂ hform hαa hw hnt hmem
      (fun h5 => absurd h5 (by omega))

theorem ggTwoNodeIndepAtK_three_false_of_finrank
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y) {N : ℕ} (hN : 5 ≤ N) (hpN : p ∣ N)
    (hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) (hdim : Module.finrank (ZMod p) V = N - 1) :
    False := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have F := ggXDatumA_indep_frame_K hp2 hH hy hstrong hN hpN e hMK hCK hφ hpair hAK hind
  have hspan : Submodule.span (ZMod p) (Set.range fun i => h (e i)) = ⊤ :=
    F.indep.span_eq_top_of_card_eq_finrank' (by simpa using hdim.symm)
  have hA : ggAutomizer K Bs ⊔ ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  obtain ⟨t, ha, αa, _, hform, hαa, hw, hnt⟩ :=
    ggIndep_pos_prep (N := N) hH.2.2.2.1 hy hA hmove e hAK (ι := ι)
  have hmem : ha ∈ Submodule.span (ZMod p) (Set.range fun i => h (e i)) := by
    rw [hspan]
    trivial
  subst hp3
  let r : Fin (N - 1) → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin (N - 1)) (v : V), r i v = v - α (e i) v • h (e i) :=
    fun i v => hφ (e i) v
  let A : Subgroup (V ≃ₗ[ZMod 3] V) :=
    Subgroup.closure (Set.range r ∪ {ggLin (p := 3) ι t})
  have hrA : ∀ i, r i ∈ A := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have htA : ggLin (p := 3) ι t ∈ A := Subgroup.subset_closure (Or.inr rfl)
  have hcα := ggIndep_center_functional_vanish hpN F.pair hmem
  have hfix0 := ggIndep_p3_fixes_x (fun i => h (e i)) (fun i => α (e i))
    (fun i => (((i : ℕ) + 1 : ℕ) : ZMod 3)) F.pair A hnt r hr hrA
    (ggLin (p := 3) ι t) htA ha αa hcα hform hαa
  obtain ⟨c, _, hxc⟩ := ggIndep_x_eq_smul_center hpN (by omega) F.pair F.indep F.fix
  apply hw
  rw [hxc, map_smul, hfix0, smul_zero]

theorem ggTwoNodeIndepAtK_three_false_of_card
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y) {N : ℕ} (hN : 5 ≤ N) (hpN : p ∣ N)
    (hmove : ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t ⟨y, hy⟩ ≠ ⟨y, hy⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) (hcardBs : Nat.card ↥Bs = p ^ (N - 1)) :
    False := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  have hcardV : Nat.card V = Nat.card ↥Bs := by
    rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
    exact (Nat.card_congr ι.toEquiv).symm
  have hdim : Module.finrank (ZMod p) V = N - 1 := by
    have heq : p ^ Module.finrank (ZMod p) V = p ^ (N - 1) := by
      rw [← hVcard, hcardV, hcardBs]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le heq
  exact ggTwoNodeIndepAtK_three_false_of_finrank hp3 hH hy hstrong hN hpN hmove
    e hMK hCK hφ hpair hAK hind hdim

end CFSG.StandardType

end
