module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs
public import CFSG.LocalAnalysis.StandardType.GGR4Order
public import CFSG.LocalAnalysis.StandardType.GGR4Forced
public import CFSG.LocalAnalysis.StandardType.GGR4PComp
public import CFSG.LocalAnalysis.StandardType.GGR4Branch
public import CFSG.LocalAnalysis.StandardType.GGR4Centre
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwNotFiveDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem r4p_three_dvd_four_pow_sub_one (f : ℕ) : 3 ∣ 4 ^ f - 1 := by
  have hthree : ∃ k : ℕ, 4 ^ f = 3 * k + 1 := by
    induction f with
    | zero => exact ⟨0, by norm_num⟩
    | succ f ih =>
        obtain ⟨k, hk⟩ := ih
        exact ⟨4 * k + 1, by rw [pow_succ, hk]; ring⟩
  obtain ⟨k, hk⟩ := hthree
  rw [hk]
  have hsub : 3 * k + 1 - 1 = 3 * k := by omega
  rw [hsub]
  exact dvd_mul_right 3 k

private theorem r4p_not_five_of_pump {a bs N : ℕ} (hbs : bs = 3 ^ 5) (hN3 : 3 ≤ N)
    (hNle : 3 ^ (N + 1) ≤ bs) (hNcard : a = 2 ^ N * N.factorial ∨ (N = 4 ∧ a = 1152)) :
    ¬ 5 ∣ a := by
  have hNle5 : N + 1 ≤ 5 := by
    rw [hbs] at hNle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hNle
  have hN : N = 3 ∨ N = 4 := by omega
  rintro h5
  rcases hN with rfl | rfl
  · rcases hNcard with hc | ⟨h4, -⟩
    · rw [hc] at h5
      norm_num at h5
    · omega
  · rcases hNcard with hc | ⟨-, hc⟩
    · rw [hc] at h5
      norm_num at h5
    · rw [hc] at h5
      norm_num at h5

theorem ggR4_not_five_dvd_pump (hPump : GGPumpCInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 5) {f : ℕ}
    (hlab : GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    {X : Subgroup G} (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X)
    (hJX : J ≤ X) (hJc : LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hmark : GGInnerDiagOn Bs X) (hEJ : 3 ≤ Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)))
    (hnot : ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X) :
    ¬ 5 ∣ Nat.card (ggAutomizer X Bs) := by
  subst hp3
  have hpq : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have h4 : (2 ^ f) ^ 2 = 4 ^ f := by
      have h2 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h2, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [h4]
    exact r4p_three_dvd_four_pow_sub_one f
  obtain ⟨N, hN3, hNle, hNcard⟩ :=
    hPump G 3 B Bs x L D J hcfg f hlab hpq z hzD hz1 X hX hJX hJc hmark hEJ hnot
  exact r4p_not_five_of_pump hcard hN3 hNle hNcard

theorem ggR4_not_five_dvd_pump_lab (hPump : GGPumpCInput) (hPumpTw : GGPumpTwInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hcard : Nat.card Bs = 3 ^ 5)
    (hlab : GGR4JLabel (J ⧸ Subgroup.center J)) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    {X : Subgroup G} (hX : LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X)
    (hJX : J ≤ X) (hJc : LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hmark : GGInnerDiagOn Bs X) (hEJ : 3 ≤ Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)))
    (hnot : ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X) :
    ¬ 5 ∣ Nat.card (ggAutomizer X Bs) := by
  obtain ⟨f, hC | hA | hA | hA⟩ := hlab
  · exact ggR4_not_five_dvd_pump hPump hp3 hcfg hcard hC hzD hz1 hX hJX hJc hmark hEJ hnot
  all_goals
    subst hp3
    obtain ⟨N, hN3, hNle, hNcard⟩ := hPumpTw G 3 B Bs x L D J hcfg rfl f (by tauto) z hzD hz1 X hX
      hJX hJc hmark hEJ hnot
    exact r4p_not_five_of_pump hcard hN3 hNle hNcard

private theorem r4p_alpha_eq_zero {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') {x : G} (hx : x ∈ Bs)
    {H : Subgroup G} (hH : H ≤ Subgroup.centralizer ({x} : Set G)) {o : N}
    (hφ : φ' o ∈ ggAutomizer H Bs) :
    α' o (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) = 0 := by
  obtain ⟨g, hgH, -, hgval⟩ := mem_ggAutomizer_iff.mp hφ
  have hcomm : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hH hgH)
  have hgx : g * x * g⁻¹ = x := by
    rw [hcomm]
    group
  have hfix : φ' o ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [hgval ⟨x, hx⟩, hgx]
  have hlin := hD.lin o (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))
  have hfix' : ggLin (p := p) ι (φ' o) (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) =
      ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) :=
    (ggLin_fix_iff ι (φ' o) ⟨x, hx⟩).mp hfix
  rw [hfix'] at hlin
  have hzero : α' o (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) • h' o = 0 :=
    sub_eq_self.mp hlin.symm
  rcases smul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h (hD.indep.ne_zero o)

private theorem r4p_card_bs {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α')
    (hspan : Submodule.span (ZMod p) (Set.range h') = ⊤) (hcard : Fintype.card Λ = 4) :
    Nat.card Bs = p ^ 5 := by
  have hb : Module.Basis (Option Λ) (ZMod p) V :=
    Module.Basis.mk hD.indep (le_of_eq hspan.symm)
  have hdim : Module.finrank (ZMod p) V = 5 := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_option, hcard]
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Fintype V := Fintype.ofFinite V
  have hcardV : Nat.card V = p ^ 5 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := V), hdim,
      ZMod.card]
  calc Nat.card Bs = Nat.card V := card_eq_of_ggLin ι
    _ = p ^ 5 := hcardV

private theorem r4p_one_le_of_hasLabel_C {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.C, 3, f⟩ R) : 1 ≤ f := by
  unfold GGHasLabel at h
  rw [show CFSG.StandardType.LargeEvenRawDatum ⟨.C, 3, f⟩ =
      LargeEvenRecipeSymplectic 3 (2 ^ f) false from rfl] at h
  unfold LargeEvenRecipeSymplectic at h
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  have := hK
  have := hKfin
  have h2 : 2 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  rw [hKcard] at h2
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0] at h2
  norm_num at h2

private theorem r4p_one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [h] at h2
  norm_num at h2

private theorem r4p_one_le_of_hasLabel_A {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.A, 5, f⟩ R) : 1 ≤ f := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact r4p_one_le_of_card hKcard

private theorem r4p_one_le_of_hasLabel_twA {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 5, f⟩ R) : 1 ≤ f := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  have h2 : 1 ≤ 2 * f := by
    apply r4p_one_le_of_card (K := K) (n := 2 * f)
    rw [← pow_mul] at hKcard
    rw [Nat.mul_comm f 2] at hKcard
    exact hKcard
  omega

private theorem r4p_one_le_of_hasLabel_twD {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twD, 4, f⟩ R) : 1 ≤ f := by
  unfold GGHasLabel at h
  rw [show CFSG.StandardType.LargeEvenRawDatum ⟨.twD, 4, f⟩ =
      LargeEvenRecipeOmegaMinus 3 (2 ^ f) from rfl] at h
  unfold LargeEvenRecipeOmegaMinus at h
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact r4p_one_le_of_card hKcard

private theorem r4p_center_bot {lab : LargeEvenLabel}
    (hAll : LargeEvenLabelAll lab fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥)
    {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hlab : GGHasLabel lab (Y ⧸ Subgroup.center Y)) : Subgroup.center Y = ⊥ := by
  have hmain := hAll (fun R _ _ _ => Nonempty ((Y ⧸ Subgroup.center Y) ≃* R)) hlab
  obtain ⟨R, _, I, F, hQe, hP⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨e⟩ := hQe
  let ψ : Y →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Y) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hP Y ψ hsurj hker.le hperf

private theorem r4p_centre_two (hZ : GGCentreTwoKnown) (hZtw : GGCentreTrivialTwKnown)
    {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hlab : GGR4JLabel (Y ⧸ Subgroup.center Y)) :
    ∀ g ∈ Subgroup.center Y, ∃ k : ℕ, orderOf g = 2 ^ k := by
  have htriv : Subgroup.center Y = ⊥ → ∀ g ∈ Subgroup.center Y, ∃ k : ℕ, orderOf g = 2 ^ k := by
    intro hbot g hg
    rw [hbot, Subgroup.mem_bot] at hg
    exact ⟨0, by rw [hg, orderOf_one, pow_zero]⟩
  obtain ⟨f, hC | ⟨h3, hA⟩ | ⟨h3, hA⟩ | hA⟩ := hlab
  · have hfl : 1 ≤ f := r4p_one_le_of_hasLabel_C hC
    have hlab2 : LargeEvenInLambda2 ⟨.C, 3, f⟩ := by
      simp [LargeEvenInLambda2, hfl]
    exact ggCentreTwo_of_label hZ hlab2 (by simp) hperf hC
  · exact htriv (r4p_center_bot ((hZtw f (r4p_one_le_of_hasLabel_twA hA)).1 h3) hperf hA)
  · exact htriv (r4p_center_bot ((hZtw f (r4p_one_le_of_hasLabel_A hA)).2.1 h3) hperf hA)
  · exact htriv (r4p_center_bot ((hZtw f (r4p_one_le_of_hasLabel_twD hA)).2.2) hperf hA)

theorem ggR4NotFiveAtLine_of_pump (hPump : GGPumpCInput) (hPumpTw : GGPumpTwInput) :
    GGR4NotFiveAtLine := by
  intro G _ _ B Bs x L D J hcfg hcard hlab z hzD hz1 X hX hJX hJc hmark hEJ hnot
  exact ggR4_not_five_dvd_pump_lab hPump hPumpTw rfl hcfg hcard hlab hzD hz1 hX hJX hJc hmark hEJ
    hnot

theorem ggR4NotFiveAtLine_of_notFive (hPump : GGPumpCInput) (hPumpTw : GGPumpTwNotFive) :
    GGR4NotFiveAtLine := by
  intro G _ _ B Bs x L D J hcfg hcard hlab z hzD hz1 X hX hJX hJc hmark hEJ hnot
  obtain ⟨f, hC | hA | hA | hA⟩ := hlab
  · exact ggR4_not_five_dvd_pump hPump rfl hcfg hcard hC hzD hz1 hX hJX hJc hmark hEJ hnot
  all_goals
    exact hPumpTw G 3 B Bs x L D J hcfg rfl hcard f (by tauto) z hzD hz1 X hX hJX hJc hmark hEJ
      hnot

theorem ggFork_R4_false_of_five {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    (hPU : GGPumpupInput) (hNF : GGR4NotFiveAtLine)
    (hZ : GGCentreTwoKnown) (hZtw : GGCentreTrivialTwKnown) (hJleaf : GGR4JInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hOp : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J) (hNT : GGNoTransvection p Bs)
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K)
    (hRG : GGReflGenerated p (ggAutomizer K Bs))
    (hSc : GGScalarsPmOne Bs) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι (ggAttachCartan C c) φ' h' α')
    (hspan : Submodule.span (ZMod p) (Set.range h') = ⊤)
    (hcell : ∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
        (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧
      ((b = e 0 ∧ c = e 1) ∨ (b = e 3 ∧ c = e 2)))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      ((fun i : Λ => φ' (some i)) '' {i | i ≠ b} ∪ {φ' none})) : False := by
  subst hp3
  have hI : GGThmIHyp 3 B x L := hcfg.1
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLle : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hG : GGBstar 3 B Bs := hcfg.2.1
  have hBBs : B ≤ Bs := hG.1
  have hE : IsElemAbelian 3 Bs := hG.2.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hDcard : Nat.card D = 3 ^ 2 := hDJ.1.2.2.1
  have hJcXY : IsComponentOf J (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnbr.2.1
  have hqs : CFSG.Assembly.IsQuasisimple ↥J := hJcXY.2.2
  have hyB : y ∈ B := hnbr.1.2.1
  have hy1 : y ≠ 1 := hnbr.1.2.2.1
  have hyBs : y ∈ Bs := hBBs hyB
  have hKle : K ≤ Subgroup.centralizer ({y} : Set G) := hnbr.1.2.2.2.1
  obtain ⟨hJgen, hlabJ⟩ :=
    hJleaf G 3 B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hSc rfl
      Λ C b c V ι φ' h' α' hD hspan hcell hAL hAK
  have hx : ∀ i : Λ, α' (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0 := by
    intro i
    exact r4p_alpha_eq_zero hD hxBs hLle (by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hy : ∀ o : Option Λ, o ≠ some b → α' o (ι (Additive.ofMul ⟨y, hyBs⟩)) = 0 := by
    intro o ho
    cases o with
    | some i =>
        have hi : i ≠ b := fun h => ho (by rw [h])
        exact r4p_alpha_eq_zero hD hyBs hKle (by
          rw [hAK]
          apply Subgroup.subset_closure
          exact Set.mem_union_left _ ⟨i, hi, rfl⟩)
    | none =>
        exact r4p_alpha_eq_zero hD hyBs hKle (by
          rw [hAK]
          apply Subgroup.subset_closure
          exact Set.mem_union_right _ (Set.mem_singleton _))
  obtain ⟨ρ, hρ, hρxy, s, hsj, h5⟩ :=
    ggR4_order_five rfl hD hspan hcell hxBs hyBs hx1 hy1 hx hy
  let z : G := x * y
  have hzBs : z ∈ Bs := by
    change x * y ∈ Bs
    exact Bs.mul_mem hxBs hyBs
  have hzD : z ∈ D := by
    change x * y ∈ D
    rw [hnbr.2.1]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hzx : z ∉ Subgroup.zpowers x := by
    intro hz
    have hy_zp : y ∈ Subgroup.zpowers x := by
      have hinv : x⁻¹ ∈ Subgroup.zpowers x := Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
      have h := Subgroup.mul_mem _ hinv hz
      simpa [z, mul_assoc] using h
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hnbr.2.1, Subgroup.closure_le]
      intro g hg
      rcases (by simpa using hg : g = x ∨ g = y) with hgx | hgy
      · rw [hgx]
        exact Subgroup.mem_zpowers x
      · rw [hgy]
        exact hy_zp
    have hox : orderOf x = 3 := orderOf_eq_prime (hS.1.1.2 x hxB) hx1
    have hdiv : Nat.card D ∣ Nat.card (Subgroup.zpowers x) := Subgroup.card_dvd_of_le hDle
    rw [Nat.card_zpowers, hox] at hdiv
    have hle3 : Nat.card D ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hzx
    exact hzx (Subgroup.one_mem _)
  have hDz : D = Subgroup.closure ({x, z} : Set G) :=
    eq_closure_pair_of_mem hI hDJ hzD hzx
  have hJ' : ∀ j : Λ, j ≠ b → φ' (some j) ∈ ggAutomizer J Bs := by
    intro j hj
    rw [hJgen]
    exact Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) := ggR4_normalizes_J hcfg hInn.1
  have hZ2 : ∀ g ∈ Subgroup.center ↥J, ∃ k : ℕ, orderOf g = 2 ^ k :=
    r4p_centre_two hZ hZtw hqs.1 hlabJ
  obtain ⟨e, -, -⟩ := hcell
  have hcardΛ : Fintype.card Λ = 4 := by
    simpa using Fintype.card_congr e.symm
  have hcardBs : Nat.card Bs = 3 ^ 5 := r4p_card_bs (p := 3) hD hspan hcardΛ
  have hlogBs : Nat.log 3 (Nat.card Bs) = 5 := by
    rw [hcardBs, Nat.log_pow (by norm_num : 1 < 3) 5]
  have hrank := ggR4_rank (p := 3) rfl hD hspan hcardΛ hNJ hJ' hqs hZ2
  have hEJ : 3 ≤ Nat.log 3 (Nat.card (Bs ⊓ J : Subgroup G)) := by
    rw [hlogBs] at hrank
    omega
  have hne : Nat.card (Bs ⊓ J : Subgroup G) ≠ 0 :=
    (Nat.card_pos (α := ↥(Bs ⊓ J : Subgroup G))).ne'
  have hbound : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
    (Nat.le_log_iff_pow_le (by norm_num : 1 < 3) hne).mp hEJ
  have hdiv : Nat.card (Bs ⊓ J : Subgroup G) ∣ 3 ^ 5 := by
    rw [← hcardBs]
    exact Subgroup.card_dvd_of_le (inf_le_left : Bs ⊓ J ≤ Bs)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdiv
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [hk] at hbound
    norm_num at hbound
  have h3inf : 3 ∣ Nat.card (Bs ⊓ J : Subgroup G) := by
    rw [hk]
    exact dvd_pow_self 3 hk1
  have hpJ : 3 ∣ Nat.card J :=
    h3inf.trans (Subgroup.card_dvd_of_le (inf_le_right : Bs ⊓ J ≤ J))
  obtain ⟨hX0, hJX0, -, hbranch⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hDz
  have hnotfive : ¬ 5 ∣ Nat.card
      (ggAutomizer (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J) Bs) := by
    rcases hbranch with hnbr' | hcomm
    · have hmark : GGInnerDiagOn Bs (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J) :=
        hInn.2 z _ hnbr'
      have hJc : LargeEvenPComponent 3
          (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J ⊓
            Subgroup.centralizer ({x} : Set G)) J :=
        ggJ_pComponent_centralizer hI hDJ hpJ hDz hX0 hJX0
      exact hNF G _ _ _ _ _ _ hcfg hcardBs hlabJ _ hzD hz1 _ hX0 hJX0 hJc hmark hEJ hnbr'.2.2.2
    · have hfix := ggAutomizer_fixes_of_commutator hE hxBs hzBs hX0.1 hcomm
      have hD9 : Nat.card (Subgroup.closure ({x, z} : Set G)) = 3 ^ 2 := by
        rw [← hDz]
        exact hDcard
      exact ggFive_not_dvd_of_fixes rfl hE hcardBs hxBs hzBs hD9 hfix
  have hs : ∀ i : Fin 4, s i ∈ ggAutomizer J Bs := by
    intro i
    obtain ⟨j, hj, hji⟩ := hsj i
    rw [hji]
    exact hJ' j hj
  have hρz : ρ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
    change ρ ⟨x * y, Bs.mul_mem hxBs hyBs⟩ = ⟨x * y, Bs.mul_mem hxBs hyBs⟩
    exact hρxy
  have hfive := ggR4_five_dvd hzBs hE hX0 hJX0 hrank hρ hρz hs h5
  exact hnotfive hfive

end CFSG.StandardType
