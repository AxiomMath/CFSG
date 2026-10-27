module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSpOrder
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public section

namespace CFSG.StandardType

namespace OrdPNsOm

open Matrix Module QuadraticMap SUTB NoOffOm OrdPNsGen
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section GenMaxOrth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ}

omit [Finite K] in
theorem polB_self (v : Fin d → K) : polB Q v v = 0 := polar_self_charTwo v

omit [Finite K] [CharP K 2] in
theorem quad_glin_of_mem_isometries {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q)
    (v : Fin d → K) : Q (glin g v) = Q v := by
  rw [glin_apply, ← matrixLinearEquiv_apply]
  exact (mem_matrixIsometries_iff Q g).mp hg v

omit [CharP K 2] in
theorem exists_restrict_mem_omega (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) {c : GL (Fin d) K} (hc : c ∈ matrixDerived Q) (hcp : c ^ p = 1)
    {W : Submodule K (Fin d → K)} (hW : NondegOn (polB Q) W) (hcW : ∀ w ∈ W, glin c w ∈ W) :
    ∃ g ∈ matrixDerived Q, glin g = restrictElt hW (glin c) hcW := by
  have hcl : glin c ^ p = 1 := by rw [← glin_pow, hcp, glin_one]
  have hcQ : ∀ v, Q (glin c v) = Q v :=
    quad_glin_of_mem_isometries (matrixDerived_le_isometries Q hc)
  have hup := restrictElt_pow_eq_one hW hcW hcl
  obtain ⟨g₀, hg₀⟩ := exists_gl_of_pow hp.one_lt.le hup
  have hiso : g₀ ∈ matrixIsometries Q := (mem_matrixIsometries_iff Q g₀).mpr fun v => by
    rw [matrixLinearEquiv_apply, ← glin_apply, hg₀]
    exact restrictElt_quad hW hcW hcQ v
  have hg₀p : g₀ ^ p = 1 := glin_injective (by rw [glin_pow, hg₀, hup, glin_one])
  have hodd : Odd (orderOf g₀) := Odd.of_dvd_nat (hp.odd_of_ne_two hp2)
    (orderOf_dvd_of_pow_eq_one hg₀p)
  exact ⟨g₀, CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd hT
    hiso hodd, hg₀⟩

omit [CharP K 2] in
theorem exists_genMax_le_orth (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) {F : Subgroup (GL (Fin d) K)} (hF : F ≤ matrixDerived Q)
    (hFp : ∀ a ∈ F, a ^ p = 1) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) :
    ∃ E : Subgroup (GL (Fin d) K), GenMax (polB Q) (matrixDerived Q) p E ∧ F ≤ E := by
  classical
  set Γ := matrixDerived Q with hΓ
  set P : Subgroup (GL (Fin d) K) → Prop := fun E =>
    E ≤ Γ ∧ F ≤ E ∧ (∀ a ∈ E, a ^ p = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hP
  set R : ℕ → Prop := fun k => ∃ E, P E ∧ Nat.card E = k with hR
  have hP0 : P F := ⟨hF, le_rfl, hFp, hFc⟩
  have hbound : ∀ k, R k → k ≤ Nat.card (GL (Fin d) K) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hR0 : R (Nat.card F) := ⟨_, hP0, rfl⟩
  set N := Nat.findGreatest R (Nat.card (GL (Fin d) K)) with hN
  obtain ⟨E, hE, hEN⟩ : R N := Nat.findGreatest_spec (hbound _ hR0) hR0
  refine ⟨E, ⟨polB_isSymm, hnd.1, hp, hp2, hE.1, hE.2.2.1, hE.2.2.2, fun g hg hgp hgE => ?_,
    fun g hg v w => polB_glin_of_mem_isometries (matrixDerived_le_isometries Q (hE.1 hg)) v w,
    fun c hc W hW hWA => ?_⟩, hE.2.1⟩
  ·
    set E' := Subgroup.closure ((E : Set (GL (Fin d) K)) ∪ {g}) with hE'
    have h1 := closure_comm_pow (S := (E : Set (GL (Fin d) K)) ∪ {g}) (p := p)
      (by
        rintro x (hx | hx) y (hy | hy)
        · exact hE.2.2.2 x hx y hy
        · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
        · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
        · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
      (by
        rintro x (hx | hx)
        · exact hE.2.2.1 x hx
        · rw [Set.mem_singleton_iff.mp hx]; exact hgp)
    have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hE'Γ : E' ≤ Γ := by
      rw [hE', Subgroup.closure_le]
      rintro x (hx | hx)
      · exact hE.1 hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg
    have hP' : P E' := ⟨hE'Γ, fun x hx => hEE' (hE.2.1 hx), h1.2, h1.1⟩
    have hcard : Nat.card E' ≤ Nat.card E := by
      rw [hEN]
      exact Nat.le_findGreatest (hbound _ ⟨E', hP', rfl⟩) ⟨E', hP', rfl⟩
    have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
    rw [heq]
    exact Subgroup.subset_closure (Or.inr rfl)
  · exact exists_restrict_mem_omega hnd hT hp hp2 (hE.1 hc) (hE.2.2.1 c hc) hW (hWA c hc)

omit [CharP K 2] in
theorem exists_genMax_mem_orth (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hp : p.Prime) (hp2 : p ≠ 2) {u : GL (Fin d) K} (hu : u ∈ matrixDerived Q) (hup : u ^ p = 1) :
    ∃ E : Subgroup (GL (Fin d) K), GenMax (polB Q) (matrixDerived Q) p E ∧ u ∈ E := by
  have h1 := closure_comm_pow (S := {u}) (p := p) (by simp) (by simpa using hup)
  rw [← Subgroup.zpowers_eq_closure] at h1
  obtain ⟨E, hE, hFE⟩ := exists_genMax_le_orth hnd hT hp hp2
    (Subgroup.zpowers_le.mpr hu) h1.2 h1.1
  exact ⟨E, hE, hFE (Subgroup.mem_zpowers u)⟩

end GenMaxOrth

section Pieces

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {σ : K →+* K}
  {B : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K} {Γ : Subgroup (GL (Fin d) K)} {p : ℕ}
  {A : Subgroup (GL (Fin d) K)}

theorem finrank_grng_eq_lcm (hBalt : ∀ v, B v v = 0) (hA : GenMax B Γ p A)
    {S : Finset (GL (Fin d) K)} (hS : GenPieceSet B A S) {y : GL (Fin d) K} (hy : y ∈ S) :
    finrank K (grng y) = Nat.lcm 2 (OrdPNS.ordQ K p) := by
  have hyA := hS.mem y hy
  have hne0 : grng y ≠ ⊥ := grng_ne_bot (hS.ne_one y hy)
  refine le_antisymm (finrank_le_lcm_of_minimal hA.symm hA.sep hA.prime hA.ne_two
    (hA.iso y hyA) (hA.pow y hyA) le_rfl hne0 (nondegOn_grng hA hyA) (grng_inv hA hyA hyA)
    fun W hWle hW0 hWnd hWy => GenPieceSet.minimal hA hS hy hWle hW0 hWnd hWy) ?_
  refine Nat.le_of_dvd ?_ (lcm_dvd_finrank_grng hA.symm hBalt hA.sep hA.prime hA.ne_two
    (hA.iso y hyA) (hA.pow y hyA))
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  exact hne0

omit [CharP K 2] in
theorem exists_lcm_eq (hp : p.Prime) (hpK : (p : K) ≠ 0) :
    ∃ m : ℕ, Nat.lcm 2 (OrdPNS.ordQ K p) = 2 * m + 2 := by
  have hpos : 0 < Nat.lcm 2 (OrdPNS.ordQ K p) := Nat.lcm_pos two_pos (OrdPNS.ordQ_pos hp hpK)
  obtain ⟨k, hk⟩ := Nat.dvd_lcm_left 2 (OrdPNS.ordQ K p)
  refine ⟨k - 1, ?_⟩
  rw [hk] at hpos ⊢
  omega

end Pieces

section Compare

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ} {A : Subgroup (GL (Fin d) K)}

theorem charSum_grng_modEq (hA : GenMax (polB Q) (matrixDerived Q) p A) {y : GL (Fin d) K}
    (hy : y ∈ A) : charSum Q (grng y) ≡ 1 [ZMOD p] := by
  have : Fact p.Prime := ⟨hA.prime⟩
  exact charSum_modEq (y := glin y) (grng_inv hA hy hy)
    (quad_glin_of_mem_isometries (matrixDerived_le_isometries Q (hA.le hy)))
    (hA.lin_pow hy) fun u hu hyu => eq_zero_of_mem_grng hA hy hu hyu

theorem card_le_card_of_genMax (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {E : Subgroup (GL (Fin d) K)} (hA : GenMax (polB Q) (matrixDerived Q) p A)
    (hE : GenMax (polB Q) (matrixDerived Q) p E) : Nat.card A ≤ Nat.card E := by
  classical
  obtain ⟨SA, hSA, htA⟩ := exists_terminal_genPieceSet hA
  obtain ⟨SE, hSE, htE⟩ := exists_terminal_genPieceSet hE
  rw [card_eq_pow_of_terminal hA hSA htA, card_eq_pow_of_terminal hE hSE htE]
  refine Nat.pow_le_pow_right hA.prime.pos ?_
  by_contra hlt
  push Not at hlt
  have hp := hA.prime
  have hp2 := hA.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c₀, hc₀⟩ := exists_not_mem_range_wp (K := K)
  obtain ⟨m, hm⟩ := exists_lcm_eq (K := K) hp hA.natCast_ne_zero
  set yA : Fin SA.card → GL (Fin d) K := fun j => (SA.equivFin.symm j : GL (Fin d) K) with hyA
  set yE : Fin SE.card → GL (Fin d) K := fun j => (SE.equivFin.symm j : GL (Fin d) K) with hyE
  have hyAS : ∀ j, yA j ∈ SA := fun j => (SA.equivFin.symm j).2
  have hyES : ∀ j, yE j ∈ SE := fun j => (SE.equivFin.symm j).2
  have hyAinj : Function.Injective yA := fun i j h =>
    SA.equivFin.symm.injective (Subtype.ext h)
  have hyEinj : Function.Injective yE := fun i j h =>
    SE.equivFin.symm.injective (Subtype.ext h)
  have hdimA : ∀ j, finrank K (grng (yA j)) = 2 * m + 2 := fun j => by
    rw [finrank_grng_eq_lcm polB_self hA hSA (hyAS j), hm]
  have hdimE : ∀ j, finrank K (grng (yE j)) = 2 * m + 2 := fun j => by
    rw [finrank_grng_eq_lcm polB_self hE hSE (hyES j), hm]
  set j₀ : Fin SA.card := ⟨SE.card, hlt⟩ with hj₀
  set y₀ := yA j₀ with hy₀
  have hy₀A : y₀ ∈ A := hSA.mem _ (hyAS j₀)
  obtain ⟨τ₀, -, -, -, -, -, -, hS₀⟩ :=
    exists_frame (Q := Q) hc₀ m (grng y₀) (nondegOn_grng hA hy₀A) (hdimA j₀)
  have hτ₀ : (Nat.card K : ℤ) ^ m * tailSum K τ₀ ≡ 1 [ZMOD p] := hS₀ ▸ charSum_grng_modEq hA hy₀A
  have hfrA : ∀ j, ∃ (e f : Fin m → Fin d → K) (a b : Fin d → K),
      (∀ x, fvec e f a b x ∈ grng (yA j)) ∧ IsFrame Q c₀ τ₀ e f a b := fun j =>
    exists_frame_of_modEq hc₀ hp hp2 hτ₀ (nondegOn_grng hA (hSA.mem _ (hyAS j))) (hdimA j)
      (charSum_grng_modEq hA (hSA.mem _ (hyAS j)))
  have hfrE : ∀ j, ∃ (e f : Fin m → Fin d → K) (a b : Fin d → K),
      (∀ x, fvec e f a b x ∈ grng (yE j)) ∧ IsFrame Q c₀ τ₀ e f a b := fun j =>
    exists_frame_of_modEq hc₀ hp hp2 hτ₀ (nondegOn_grng hE (hSE.mem _ (hyES j))) (hdimE j)
      (charSum_grng_modEq hE (hSE.mem _ (hyES j)))
  choose eA fA aA bA hmA hFA using hfrA
  choose eE fE aE bE hmE hFE using hfrE
  have horthA : ∀ j j', j ≠ j' → ∀ u ∈ grng (yA j), ∀ v ∈ grng (yA j'), polar Q u v = 0 :=
    fun j j' hjj' => hSA.orth _ (hyAS j) _ (hyAS j') fun h => hjj' (hyAinj h)
  have horthE : ∀ j j', j ≠ j' → ∀ u ∈ grng (yE j), ∀ v ∈ grng (yE j'), polar Q u v = 0 :=
    fun j j' hjj' => hSE.orth _ (hyES j) _ (hyES j') fun h => hjj' (hyEinj h)
  set ι : Fin SE.card → Fin SA.card := Fin.castLE hlt.le with hι
  obtain ⟨g, hg, hgF⟩ := exists_orth_frames (Q := Q) hnd (e := eE) (f := fE) (a := aE)
    (b := bE) (e' := fun j => eA (ι j)) (f' := fun j => fA (ι j)) (a' := fun j => aA (ι j))
    (b' := fun j => bA (ι j)) hFE (fun j => hFA (ι j))
    (fun j j' hjj' x y => horthE j j' hjj' _ (hmE j x) _ (hmE j' y))
    (fun j j' hjj' x y => horthA (ι j) (ι j') (fun h => hjj' (Fin.castLE_injective _ h)) _
      (hmA _ x) _ (hmA _ y))
  set G : GL (Fin d) K := matrixLinearIso.symm g with hG
  have hGg : matrixLinearIso G = g := MulEquiv.apply_symm_apply _ _
  have hGv : ∀ v, glin G v = g v := fun v => by
    rw [glin_apply, ← hGg]
    rfl
  have hGiso : G ∈ matrixIsometries Q := by
    change matrixLinearIso.toMonoidHom G ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [MulEquiv.coe_toMonoidHom, hGg]
    exact hg
  obtain ⟨b, hbA, hbon, hboff⟩ := hA.exists_mem_restrict (nondegOn_grng hA hy₀A)
    (fun a ha => grng_inv hA hy₀A ha) hy₀A
  have hb1 : b ≠ 1 := by
    intro hb
    obtain ⟨u, hu, hu0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (grng_ne_bot (hSA.ne_one _ (hyAS j₀)))
    have h1 := hbon u hu
    rw [hb, glin_one, Module.End.one_apply] at h1
    exact hu0 (eq_zero_of_mem_grng hA hy₀A hu h1.symm)
  set z : GL (Fin d) K := G⁻¹ * b * G with hz
  have hzlin : ∀ v, glin z v = glin G⁻¹ (glin b (glin G v)) := fun v => by
    rw [hz, glin_mul, glin_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hbiso : b ∈ matrixIsometries Q := matrixDerived_le_isometries Q (hA.le hbA)
  have hziso : z ∈ matrixIsometries Q :=
    (matrixIsometries Q).mul_mem ((matrixIsometries Q).mul_mem
      ((matrixIsometries Q).inv_mem hGiso) hbiso) hGiso
  have hzp : z ^ p = 1 := by
    have h1 : z = G⁻¹ * b * G⁻¹⁻¹ := by rw [hz, inv_inv]
    rw [h1, conj_pow, hA.pow b hbA, mul_one, mul_inv_cancel]
  have hz1 : z ≠ 1 := by
    intro h1
    apply hb1
    have h2 : b = G * z * G⁻¹ := by rw [hz]; group
    rw [h2, h1, mul_one, mul_inv_cancel]
  have hzodd : Odd (orderOf z) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hzp)
  have hzΓ : z ∈ matrixDerived Q :=
    CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd hT hziso hzodd
  have hfixE : ∀ j x, glin z (fvec (eE j) (fE j) (aE j) (bE j) x) =
      fvec (eE j) (fE j) (aE j) (bE j) x := by
    intro j x
    have hne : ι j ≠ j₀ := by
      intro h
      have h1 := congrArg Fin.val h
      simp only [hι, hj₀, Fin.val_castLE] at h1
      omega
    have hmem : g (fvec (eE j) (fE j) (aE j) (bE j) x) ∈ (grng y₀).orthogonalBilin (polB Q) := by
      rw [hgF j x]
      refine Submodule.mem_orthogonalBilin.mpr fun n hn => ?_
      exact horthA j₀ (ι j) (Ne.symm hne) n hn _ (hmA (ι j) x)
    rw [hzlin, hGv, hboff _ hmem, ← hGv, glin_inv_apply]
  have hle : genPieceSpan SE ≤ LinearMap.ker (glin z - 1) := by
    refine iSup₂_le fun y hy => ?_
    obtain ⟨j, rfl⟩ : ∃ j, yE j = y := ⟨SE.equivFin ⟨y, hy⟩, by simp [hyE]⟩
    rw [← (hFE j).span_eq (hmE j) (hdimE j), Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      hfixE j x, sub_self]
  have hzX : ∀ v ∈ genPieceSpan SE, glin z v = v := fun v hv => by
    have h1 := hle hv
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
  have hXE : ∀ c ∈ E, ∀ v ∈ genPieceSpan SE, glin c v ∈ genPieceSpan SE := by
    intro c hc v hv
    have hle' : genPieceSpan SE ≤ (genPieceSpan SE).comap (glin c) := by
      refine iSup₂_le fun y hy u hu => ?_
      exact (le_iSup₂ (f := fun y (_ : y ∈ SE) => grng y) y hy)
        (grng_inv hE (hSE.mem y hy) hc u hu)
    exact hle' hv
  have hXnd : NondegOn (polB Q) (genPieceSpan SE) := (hSE.nondegOn_card hE).1
  have hcomm : ∀ c ∈ E, z * c = c * z := by
    intro c hc
    apply glin_injective
    rw [glin_mul z c, glin_mul c z]
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, hx, w, hw, rfl⟩ := exists_add_orth hXnd v
    have hcw : glin c w = w := triv_orth_genPieceSpan hE hSE htE hc w hw
    have hzw : glin z w ∈ (genPieceSpan SE).orthogonalBilin (polB Q) := by
      refine Submodule.mem_orthogonalBilin.mpr fun n hn => ?_
      rw [← hzX n hn, polB_glin_of_mem_isometries hziso]
      exact (Submodule.mem_orthogonalBilin.mp hw) n hn
    have hczw : glin c (glin z w) = glin z w := triv_orth_genPieceSpan hE hSE htE hc _ hzw
    simp only [Module.End.mul_apply, map_add]
    rw [hcw, hzX _ (hXE c hc x hx), hzX x hx, hczw]
  exact hz1 (htE z (hE.max z hzΓ hzp hcomm) hzX)

theorem card_le_card_of_genMax_of_le (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {A : Subgroup (GL (Fin d) K)} (hA : GenMax (polB Q) (matrixDerived Q) p A)
    {F : Subgroup (GL (Fin d) K)} (hF : F ≤ matrixDerived Q)
    (hFp : ∀ a ∈ F, a ^ p = 1) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) :
    Nat.card F ≤ Nat.card A := by
  obtain ⟨E, hE, hFE⟩ := exists_genMax_le_orth hnd hT hA.prime hA.ne_two hF hFp hFc
  exact (Subgroup.card_le_of_le hFE).trans (card_le_card_of_genMax hnd hT hE hA)

end Compare

section Setting

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ}

theorem exists_conj_mem_centralizer_of_model {G : Type} [Group G] [Finite G] {U : Type}
    [Group U] {Bs G₀ : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
    {ψ : U →* G} (hS : GGSixFusionSetting p Bs G₀ Δ t n f ψ) (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ)
    (hφG : φ.range ≤ Subgroup.normalizer (G₀ : Set G)) (hBφ : Bs ≤ φ.range)
    {u : matrixDerived Q} (hup : u ^ p = 1) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * φ u * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  have hA := genMax_of_orth hnd hT hp hp2 hS.elem hS.omega φ hφ hBφ
  have hAcard : Nat.card ((Bs.comap φ).map (matrixDerived Q).subtype) = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective,
      ← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hBφ]
  obtain ⟨E, hE, huE⟩ := exists_genMax_mem_orth hnd hT hp hp2 u.2
    (by rw [← SubgroupClass.coe_pow, hup, OneMemClass.coe_one])
  have hcard := card_le_card_of_genMax hnd hT hA hE
  set E₀ := E.comap (matrixDerived Q).subtype with hE₀
  have hE₀map : E₀.map (matrixDerived Q).subtype = E :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hE.le)
  have hE₀card : Nat.card E₀ = Nat.card E := by
    rw [← Subgroup.card_map_of_injective (matrixDerived Q).subtype_injective, hE₀map]
  have hE'el : CFSG.Assembly.IsElemAbelian p (E₀.map φ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, s, hs, rfl⟩ := a
      obtain ⟨_, s', hs', rfl⟩ := b
      apply Subtype.ext
      change φ s * φ s' = φ s' * φ s
      have h1 : s * s' = s' * s := Subtype.ext (hE.comm _ hs _ hs')
      rw [← map_mul, ← map_mul, h1]
    · rintro _ ⟨s, hs, rfl⟩
      have h1 : s ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hE.pow _ hs)
      rw [← map_pow, h1, map_one]
  have hEM : E₀.map φ ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨s, -, rfl⟩
    exact hφG ⟨s, rfl⟩
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS hEM hE'el ?_ ?_
  · rw [Subgroup.card_map_of_injective hφ, hE₀card, ← hAcard]
    exact hcard
  · rintro _ ⟨s, hs, rfl⟩
    have h1 : u * s = s * u := Subtype.ext (hE.comm _ huE _ hs)
    rw [← map_mul, ← map_mul, h1]

end Setting

end OrdPNsOm

end CFSG.StandardType
