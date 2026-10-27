module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSigned
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrKernel
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResCentBoundNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], ∀ hy : y ∈ Bs,
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)

@[expose] def GGTBTorNonsingularCov (p : ℕ) (lab : CFSG.Assembly.LargeEvenLabel) : Prop :=
  ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
    GGTBTorRowAt p lab r m N C M ∧ ¬ (p : ℤ) ∣ C.det

theorem ggTBTorCov_of_nonsingular {p : ℕ} {lab : CFSG.Assembly.LargeEvenLabel}
    (h : GGTBTorNonsingularCov p lab) : GGTBTorCov p lab := by
  obtain ⟨r,m,N,C,M,hrow,-⟩ := h
  exact ⟨r,m,N,C,M,hrow⟩

@[expose] def GGTBTorSplitLinearCov (p : ℕ) (lab : CFSG.Assembly.LargeEvenLabel) : Prop :=
  GGTBTorCov p lab ∧ lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGResCentBoundNbrRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], ∀ hy : y ∈ Bs,
    (¬ GGInnerDiagOnLabel GGTBTorCov p Bs K) →
    (¬ GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K) →
    (¬ GGInnerDiagOnLabel GGF4ThreeLabel p Bs K) →
    (¬ GGInnerDiagOnLabel GGTwE6BadLabel p Bs K) →
    (p = 3 → ¬ GGInnerDiagOnLabel GGTableBNbrInnerLinearNsLabel p Bs K) →
    (¬ GGInnerDiagOnLabel GGE6TwoThreeLabel p Bs K) →
    (p = 3 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) p Bs K) →
    (p = 7 → ¬ GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.A,8,1⟩ ∨ lab = ⟨.A,11,1⟩ ∨ lab = ⟨.E6,0,1⟩ ∨
        lab = ⟨.twE6,0,1⟩ ∨ lab = ⟨.E8,0,1⟩) p Bs K) →
    (¬ GGInnerDiagOnLabel
      (fun p lab => GGTableBNbrInnerNineSmallLabel p lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4)
      p Bs K) →
    (¬ GGInnerDiagOnLabel GGTableBNbrInnerNineClassicalLabel p Bs K) →
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)

theorem ggResCentBoundNbrRestInput_of_input (h : GGResCentBoundNbrInput) :
    GGResCentBoundNbrRestInput := by
  intro G _ _ p B Bs x L D J y K hH _ hy _ _ _ _ _ _ _ _ _ _
  exact h G p B Bs x L D J y K hH hy

theorem ggResCentBoundNbr_of_signed_model {G : Type} [Group G] [Finite G]
    {Bs L K : Subgroup G} {y : G} (hy : y ∈ Bs) {n : ℕ}
    (Φ : (Fin n → Multiplicative (ZMod 3)) ≃* ↥Bs) {i j : Fin n} (hij : i ≠ j)
    (hyi : Φ.symm ⟨y, hy⟩ i ≠ 1) (hyj : Φ.symm ⟨y, hy⟩ j ≠ 1)
    (hysupp : ∀ t, t ≠ i → t ≠ j → Φ.symm ⟨y, hy⟩ t = 1)
    (hmodel : ∀ ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs,
      ∃ s ∈ SpJoin.spSignedGroup n 3, ∀ v, ψ (Φ v) = Φ (s v))
    (hKcard : 2 ^ (n - 2) * (n - 2).factorial ≤ Nat.card (ggAutomizer K Bs)) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  let H : Subgroup (MulAut ↥Bs) := (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
    MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)
  let v : Fin n → Multiplicative (ZMod 3) := Φ.symm ⟨y, hy⟩
  let S := SpJoin.spSignedGroup n 3 ⊓ MulAction.stabilizer
    (Equiv.Perm (Fin n → Multiplicative (ZMod 3))) v
  choose s hs hact using fun ψ : H => hmodel ψ.1 ψ.2.1
  have hsf : ∀ ψ : H, s ψ v = v := by
    intro ψ
    apply Φ.injective
    rw [← hact ψ v, Φ.apply_symm_apply]
    exact MulAction.mem_stabilizer_iff.mp ψ.2.2
  let f : H → S := fun ψ => ⟨s ψ, hs ψ, hsf ψ⟩
  have hfinj : Function.Injective f := by
    intro ψ ψ' he
    have hsEq : s ψ = s ψ' := congrArg Subtype.val he
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    obtain ⟨a, rfl⟩ := Φ.surjective b
    rw [hact ψ a, hact ψ' a, hsEq]
  have hb : Nat.card H ≤ 2 * (2 ^ (n - 2) * (n - 2).factorial) :=
    (Nat.card_le_card_of_injective f hfinj).trans
      (GGHalfJoin.card_signed_stabilizer_two_support_le hij hyi hyj hysupp)
  calc Nat.card H ≤ 2 * (2 ^ (n - 2) * (n - 2).factorial) := hb
    _ ≤ 2 * Nat.card (ggAutomizer K Bs) := Nat.mul_le_mul_left 2 hKcard
    _ ≤ (3 - 1) * 6 * Nat.card (ggAutomizer K Bs) := by omega


theorem ggResCentBoundNbr_of_plane_kernel {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {Bs L K : Subgroup G} (hNT : GGNoTransvection p Bs)
    {y : G} (hy : y ∈ Bs) {T : Type} [Group T]
    (q : ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) →* T)
    (hqcard : Nat.card q.range ≤ 2 * Nat.card ↥(ggAutomizer K Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (yV z : V) (hyV : yV ≠ 0) (a d : Module.Dual (ZMod p) V)
    (a' b' d' : ↥q.ker → ZMod p) (c : ↥q.ker →* (ZMod p)ˣ)
    (hshape : ∀ g : ↥q.ker, ∀ v, ggLin (p := p) ι g.1.1 v = v +
      (a' g * a v + b' g * d v) • yV + (((c g : ZMod p) - 1) * a v) • z + (d' g * d v) • z)
    (ha : a yV = 0) (had : d yV = 0) (haz : a z = 1) (hdz : d z = 0)
    (hc : ∀ g : ↥q.ker, c g = 1 ∨ c g = -1) :
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
      MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := by
  classical
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
    MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs)
  let e : ↥H →* MulAut ↥Bs := H.subtype
  let N : Subgroup (MulAut ↥Bs) := q.ker.map e
  let eqN : ↥q.ker ≃* ↥N := q.ker.equivMapOfInjective e Subtype.val_injective
  let cN : ↥N →* (ZMod p)ˣ := c.comp eqN.symm.toMonoidHom
  let aN : ↥N → ZMod p := a' ∘ eqN.symm
  let bN : ↥N → ZMod p := b' ∘ eqN.symm
  let dN : ↥N → ZMod p := d' ∘ eqN.symm
  have hN : N ≤ ggAutomizer ⊤ Bs := by
    rintro _ ⟨g, hg, rfl⟩
    have hj : g.1 ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := g.2.1
    exact sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hj
  have hshapeN : ∀ g : ↥N, ∀ v, ggLin (p := p) ι g.1 v = v +
      (aN g * a v + bN g * d v) • yV + (((cN g : ZMod p) - 1) * a v) • z + (dN g * d v) • z := by
    intro g v
    have heq : (((eqN.symm g).1 : ↥H) : MulAut ↥Bs) = (g : MulAut ↥Bs) := by
      have hg := eqN.apply_symm_apply g
      exact congrArg Subtype.val hg
    change ggLin (p := p) ι g.1 v = v +
      (a' (eqN.symm g) * a v + b' (eqN.symm g) * d v) • yV +
        (((c (eqN.symm g) : ZMod p) - 1) * a v) • z + (d' (eqN.symm g) * d v) • z
    rw [← heq]
    exact hshape (eqN.symm g) v
  have hk : Nat.card q.ker ≤ 2 * p := by
    rw [Nat.card_congr eqN.toEquiv]
    exact card_plane_kernel_le_two_mul_prime hNT ι N hN yV z hyV a d aN bN cN dN hshapeN
      ha had haz hdz (fun g => hc _)
  have hp : p.Prime := Fact.out
  have hp2le : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have hn : 4 * p ≤ (p - 1) * 6 := by omega
  calc Nat.card ↥H = Nat.card q.ker * Nat.card q.range := (Subgroup.card_ker_mul_card_range q).symm
    _ ≤ (2 * p) * (2 * Nat.card ↥(ggAutomizer K Bs)) := Nat.mul_le_mul hk hqcard
    _ = (4 * p) * Nat.card ↥(ggAutomizer K Bs) := by ring
    _ ≤ (p - 1) * 6 * Nat.card ↥(ggAutomizer K Bs) := Nat.mul_le_mul_right _ hn




end CFSG.StandardType
