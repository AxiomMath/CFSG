module

public import CFSG.Quasithin.H13.L32A72d
public import CFSG.Quasithin.H13.L32ASecMod

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.H6

variable {G : Type} [Group G]

namespace SecMod

variable {L X Y : Subgroup G} {θ : ↥L →* Γ}

theorem exists_rep (D : SecMod L X Y θ) [(Y.subgroupOf X).Normal] :
    ∃ ρ : Γ →* AddMonoid.End (Additive (↥X ⧸ Y.subgroupOf X)), ∀ (l : ↥L) (s : ↥X),
      ρ (θ l) (Additive.ofMul (QuotientGroup.mk s)) =
        Additive.ofMul (QuotientGroup.mk (D.conjX l s)) := by
  set N := Y.subgroupOf X with hNdef
  have hle : ∀ l : ↥L, N ≤ N.comap (D.conjX l) := fun l n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_conjX]
    exact (Subgroup.mem_normalizer_iff.mp (D.normY l.2) _).mp (Subgroup.mem_subgroupOf.mp hn)
  let actQ : ↥L → (↥X ⧸ N) →* (↥X ⧸ N) := fun l => QuotientGroup.map N N (D.conjX l) (hle l)
  have hactQ : ∀ (l : ↥L) (s : ↥X),
      actQ l (QuotientGroup.mk s) = QuotientGroup.mk (D.conjX l s) := fun _ _ => rfl
  let actM : ↥L →* AddMonoid.End (Additive (↥X ⧸ N)) :=
    { toFun := fun l => MonoidHom.toAdditive (actQ l)
      map_one' := by
        apply AddMonoidHom.ext
        intro q
        induction q using QuotientGroup.induction_on with
        | H s =>
        show Additive.ofMul (actQ 1 (QuotientGroup.mk s)) = Additive.ofMul (QuotientGroup.mk s)
        rw [hactQ]
        congr 2
        apply Subtype.ext
        simp [coe_conjX]
      map_mul' := fun l l' => by
        apply AddMonoidHom.ext
        intro q
        induction q using QuotientGroup.induction_on with
        | H s =>
        show Additive.ofMul (actQ (l * l') (QuotientGroup.mk s)) =
          Additive.ofMul (actQ l (actQ l' (QuotientGroup.mk s)))
        rw [hactQ, hactQ, hactQ]
        congr 2
        apply Subtype.ext
        simp only [coe_conjX, Subgroup.coe_mul]
        group }
  have hactM : ∀ (l : ↥L) (s : ↥X), actM l (Additive.ofMul (QuotientGroup.mk s)) =
      Additive.ofMul (QuotientGroup.mk (D.conjX l s)) := fun _ _ => rfl
  have hker : θ.ker ≤ actM.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    apply AddMonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H s =>
    show actM l (Additive.ofMul (QuotientGroup.mk s)) = Additive.ofMul (QuotientGroup.mk s)
    rw [hactM]
    congr 1
    rw [D.mk_eq_mk_iff, coe_conjX]
    exact D.ker l hl s s.2
  have hact_eq : ∀ l l' : ↥L, θ l = θ l' → actM l = actM l' := by
    intro l l' h
    have h1 : l'⁻¹ * l ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h3 := hker h1
    rw [MonoidHom.mem_ker] at h3
    calc actM l = actM (l' * (l'⁻¹ * l)) := by rw [mul_inv_cancel_left]
      _ = actM l' := by rw [map_mul, h3, mul_one]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ →* AddMonoid.End (Additive (↥X ⧸ N)), ∀ l : ↥L, ρ (θ l) = actM l := by
    refine ⟨{ toFun := fun g => actM (Function.surjInv D.surj g)
              map_one' := ?_
              map_mul' := fun g g' => ?_ }, fun l => ?_⟩
    · show actM (Function.surjInv D.surj 1) = 1
      rw [hact_eq _ 1 (by rw [Function.surjInv_eq D.surj, map_one]), map_one]
    · show actM (Function.surjInv D.surj (g * g')) =
        actM (Function.surjInv D.surj g) * actM (Function.surjInv D.surj g')
      rw [← map_mul]
      exact hact_eq _ _ (by rw [map_mul, Function.surjInv_eq D.surj, Function.surjInv_eq D.surj,
        Function.surjInv_eq D.surj])
    · exact hact_eq _ _ (Function.surjInv_eq D.surj (θ l))
  exact ⟨ρ, fun l s => by rw [hρ]; rfl⟩

theorem exists_compl [Finite G] (D : SecMod L X Y θ) (h63 : VolI_H_6_3) {S : Subgroup G}
    (hYS : Y ≤ S) (hSX : S ≤ X) (hLS : L ≤ Subgroup.normalizer (S : Set G))
    {χ : ↥S →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))}
    (hχk : χ.ker = Y.subgroupOf S) (hχt : ∀ s, RuType.IsTraceZero (Multiplicative.toAdd (χ s)))
    (hχs : ∀ A, RuType.IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A)
    (hχe : ∀ (l : ↥L) (s t : ↥S), (t : G) = l * s * (l : G)⁻¹ →
      χ t = Multiplicative.ofAdd (RuType.stAct (θ l) (Multiplicative.toAdd (χ s)))) :
    ∃ N : Subgroup G, Y ≤ N ∧ N ≤ X ∧ L ≤ Subgroup.normalizer (N : Set G) ∧ N ⊓ S = Y ∧
      ∀ x ∈ X, ∃ n ∈ N, ∃ s ∈ S, x = n * s := by
  classical
  have : (Y.subgroupOf X).Normal := D.normal
  obtain ⟨ρ, hρ⟩ := D.exists_rep
  set M := Additive (↥X ⧸ Y.subgroupOf X)
  have : Finite M := Finite.of_equiv _ Additive.ofMul
  let mkX : ↥X → M := fun x => Additive.ofMul (QuotientGroup.mk x)
  have hmk_mul : ∀ a b : ↥X, mkX (a * b) = mkX a + mkX b := fun a b => by
    show Additive.ofMul (QuotientGroup.mk (a * b)) = _
    rw [QuotientGroup.mk_mul, ofMul_mul]
  have hmk_inv : ∀ a : ↥X, mkX a⁻¹ = -mkX a := fun a => by
    show Additive.ofMul (QuotientGroup.mk a⁻¹) = _
    rw [QuotientGroup.mk_inv, ofMul_inv]
  have hmk_zero : ∀ a : ↥X, mkX a = 0 ↔ (a : G) ∈ Y := fun a => by
    show Additive.ofMul (QuotientGroup.mk a) = Additive.ofMul 1 ↔ _
    rw [(Additive.ofMul.injective).eq_iff, ← QuotientGroup.mk_one, D.mk_eq_mk_iff]
    simp
  let g : ↥S → M := fun s => mkX ⟨s, hSX s.2⟩
  have hg_mul : ∀ a b : ↥S, g (a * b) = g a + g b := fun a b =>
    hmk_mul ⟨a, hSX a.2⟩ ⟨b, hSX b.2⟩
  have hg_inv : ∀ a : ↥S, g a⁻¹ = -g a := fun a => hmk_inv ⟨a, hSX a.2⟩
  have hg_zero : ∀ a : ↥S, g a = 0 ↔ (a : G) ∈ Y := fun a => hmk_zero ⟨a, hSX a.2⟩
  let st : ↥S → St := fun s => ⟨Multiplicative.toAdd (χ s), hχt s⟩
  have hst_mul : ∀ a b : ↥S, st (a * b) = st a + st b := fun a b => Subtype.ext
    (show Multiplicative.toAdd (χ (a * b)) =
      Multiplicative.toAdd (χ a) + Multiplicative.toAdd (χ b) by rw [map_mul, toAdd_mul])
  have hst_zero : ∀ a : ↥S, st a = 0 ↔ (a : G) ∈ Y := fun a => by
    rw [← Subgroup.mem_subgroupOf, ← hχk, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : Multiplicative.toAdd (χ a) = 0 := congrArg Subtype.val h
      exact Multiplicative.toAdd.injective (h1.trans toAdd_one.symm)
    · intro h
      exact Subtype.ext (show Multiplicative.toAdd (χ a) = 0 by rw [h, toAdd_one])
  have hst_surj : Function.Surjective st := fun A => by
    obtain ⟨s, hs⟩ := hχs A.1 A.2
    exact ⟨s, Subtype.ext (show Multiplicative.toAdd (χ s) = A.1 by rw [hs, toAdd_ofAdd])⟩
  have hwd : ∀ a b : ↥S, st a = st b → g a = g b := by
    intro a b h
    have h1 : st (a * b⁻¹) = 0 := by
      rw [hst_mul, h, ← hst_mul, mul_inv_cancel]
      exact (hst_zero 1).mpr (one_mem _)
    have h2 := (hg_zero _).mpr ((hst_zero _).mp h1)
    rw [hg_mul, hg_inv] at h2
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h2)
  let f₀ : St → M := fun A => g (Function.surjInv hst_surj A)
  have hf₀ : ∀ a : ↥S, f₀ (st a) = g a := fun a =>
    hwd _ _ (Function.surjInv_eq hst_surj (st a))
  let f : St →+ M :=
    { toFun := f₀
      map_zero' := by
        have h0 : (0 : St) = st 1 := ((hst_zero 1).mpr (one_mem _)).symm
        show f₀ 0 = 0
        rw [h0, hf₀]
        exact (hg_zero 1).mpr (one_mem _)
      map_add' := fun A B => by
        obtain ⟨a, rfl⟩ := hst_surj A
        obtain ⟨b, rfl⟩ := hst_surj B
        rw [← hst_mul, hf₀, hf₀, hf₀, hg_mul] }
  have hf : ∀ a : ↥S, f (st a) = g a := hf₀
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro A hA
    obtain ⟨a, rfl⟩ := hst_surj A
    rw [hf, hg_zero] at hA
    exact (hst_zero a).mpr hA
  have hconjS : ∀ (l : ↥L) (a : ↥S), (l : G) * a * (l : G)⁻¹ ∈ S := fun l a =>
    (Subgroup.mem_normalizer_iff.mp (hLS l.2) a).mp a.2
  have hf_eq : ∀ (γ : Γ) (A : St), f (ρSt γ A) = ρ γ (f A) := by
    intro γ A
    obtain ⟨l, rfl⟩ := D.surj γ
    obtain ⟨a, rfl⟩ := hst_surj A
    have h1 : ρSt (θ l) (st a) = st ⟨_, hconjS l a⟩ := Subtype.ext
      (show RuType.stAct (θ l) (Multiplicative.toAdd (χ a)) = Multiplicative.toAdd (χ ⟨_, _⟩) by
        rw [hχe l a ⟨_, hconjS l a⟩ rfl, toAdd_ofAdd])
    rw [h1, hf, hf]
    show mkX ⟨_, _⟩ = ρ (θ l) (mkX ⟨a, hSX a.2⟩)
    rw [hρ]
    rfl
  have h2 : ∀ m : M, m + m = 0 := by
    intro m
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective m
    induction q using QuotientGroup.induction_on with
    | H s =>
    rw [← ofMul_mul, ← QuotientGroup.mk_mul, ← ofMul_one, ← QuotientGroup.mk_one]
    congr 1
    rw [D.mk_eq_mk_iff]
    have := D.sq _ s.2
    simpa [pow_two] using this
  obtain ⟨-, h1b, -⟩ := h63
  obtain ⟨p, hpf, hpe⟩ := h1b M ρ h2 f hf_inj hf_eq
  let N : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ X, p (mkX ⟨x, hx⟩) = 0}
      one_mem' := ⟨one_mem _, by
        rw [show (⟨1, one_mem X⟩ : ↥X) = 1 from rfl, (hmk_zero 1).mpr (one_mem _), map_zero]⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨ha, ha'⟩ := ha
        obtain ⟨hb, hb'⟩ := hb
        refine ⟨mul_mem ha hb, ?_⟩
        rw [show (⟨a * b, mul_mem ha hb⟩ : ↥X) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, hmk_mul, map_add,
          ha', hb', add_zero]
      inv_mem' := fun {a} ha => by
        obtain ⟨ha, ha'⟩ := ha
        refine ⟨inv_mem ha, ?_⟩
        rw [show (⟨a⁻¹, inv_mem ha⟩ : ↥X) = (⟨a, ha⟩)⁻¹ from rfl, hmk_inv, map_neg, ha']
        exact neg_zero }
  have hmemN : ∀ {x : G} (hx : x ∈ X), x ∈ N ↔ p (mkX ⟨x, hx⟩) = 0 := fun hx =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩
  refine ⟨N, fun y hy => (hmemN (D.le hy)).mpr ?_, fun x hx => hx.1, ?_, ?_, ?_⟩
  · rw [(hmk_zero ⟨y, D.le hy⟩).mpr hy, map_zero]
  · refine le_normalizer_of_conj_mem' fun l hl x hx => ?_
    obtain ⟨hxX, hx'⟩ := hx
    have hlx : l * x * l⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (D.normX hl) x).mp hxX
    refine (hmemN hlx).mpr ?_
    have e : mkX ⟨l * x * l⁻¹, hlx⟩ = ρ (θ ⟨l, hl⟩) (mkX ⟨x, hxX⟩) := by
      rw [hρ]
      rfl
    rw [e, hpe, hx', map_zero]
  · refine le_antisymm (fun s hs => ?_) (le_inf (fun y hy => (hmemN (D.le hy)).mpr ?_) hYS)
    · obtain ⟨hsN, hsS⟩ := Subgroup.mem_inf.mp hs
      obtain ⟨hsX, hs'⟩ := hsN
      have e : mkX ⟨s, hsX⟩ = g ⟨s, hsS⟩ := rfl
      rw [e, ← hf, hpf] at hs'
      exact (hst_zero ⟨s, hsS⟩).mp hs'
    · rw [(hmk_zero ⟨y, D.le hy⟩).mpr hy, map_zero]
  · intro x hx
    obtain ⟨a, ha⟩ := hst_surj (p (mkX ⟨x, hx⟩))
    have hxa : x * (a : G)⁻¹ ∈ X := mul_mem hx (inv_mem (hSX a.2))
    refine ⟨x * (a : G)⁻¹, (hmemN hxa).mpr ?_, a, a.2, by group⟩
    have e : mkX ⟨x * (a : G)⁻¹, hxa⟩ = mkX ⟨x, hx⟩ + g a⁻¹ := by
      rw [← hmk_mul]
      rfl
    rw [e, map_add, hg_inv, map_neg, ← hf, hpf, ha]
    exact add_neg_cancel _

end SecMod

end CFSG.Quasithin.H13.L32A
