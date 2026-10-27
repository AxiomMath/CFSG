module

public import CFSG.Timmesfeld.ARS.QDClass

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def Sec8 (R : Set (Subgroup G)) (A : Subgroup G) : Prop :=
  IsCoatom (Subgroup.normalizer (A : Set G)) ∧ sigmaSet R A ≠ lambdaSet R A

theorem exists_mem_commuting_of_coveredBy (hR : IsRootClass R) (hiso : NoIsolated R)
    {H X : Subgroup G} (hH : CoveredBy R H) (hX : X ∈ R) {n : G} (hn : n ∈ H) (hn1 : n ≠ 1)
    (hnX : ∀ x ∈ X, Commute x n) : ∃ P ∈ R, P ≤ H ∧ n ∈ P ∧ Commuting X P := by
  obtain ⟨P, hP, hPH, hnP⟩ := hH n hn hn1
  refine ⟨P, hP, hPH, hnP, ?_⟩
  by_cases hXP : X = P
  · subst hXP
    exact hR.commuting_self hX
  rcases hR.rel X hX P hP hXP with hc | ho | hs
  · exact hc
  · exact absurd (fun x hx => (hnX x hx).symm) (ho.symm.not_commute_of_mem hnP hn1)
  · obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hX
    exact absurd (eq_one_of_commute_of_special hR hiso hX hP hs hx hx1 hnP (hnX x hx)) hn1

theorem conjSub_mem_sigmaSet (hR : IsRootClass R) {A B : Subgroup G} (hB : B ∈ sigmaSet R A)
    (g : G) : conjSub B g ∈ sigmaSet R (conjSub A g) :=
  ⟨hR.conjSub_mem hB.1 g, fun e => hB.2.1 (RankOne.map_conj_inj.1 e), hB.2.2.conjSub g⟩

theorem sigmaSet_ne_lambdaSet_conjSub (hR : IsRootClass R) {A : Subgroup G}
    (h : sigmaSet R A ≠ lambdaSet R A) (g : G) :
    sigmaSet R (conjSub A g) ≠ lambdaSet R (conjSub A g) := by
  intro heq
  apply h
  ext B
  refine ⟨fun hB => ?_, fun hB => hB.1⟩
  have h1 : conjSub B g ∈ lambdaSet R (conjSub A g) := heq ▸ conjSub_mem_sigmaSet hR hB g
  have h2 := conjSub_mem_lambdaSet hR h1 g⁻¹
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one, ← conjSub_mul, inv_mul_cancel,
    conjSub_one] at h2

theorem sigmaSet_ne_lambdaSet_of_mem (hR : IsRootClass R) {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ R) (h : sigmaSet R A ≠ lambdaSet R A) : sigmaSet R D ≠ lambdaSet R D := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hD
  exact sigmaSet_ne_lambdaSet_conjSub hR h g

theorem normalizer_conjSub (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((conjSub A g : Subgroup G) : Set G) =
      conjSub (Subgroup.normalizer (A : Set G)) g := by
  ext x
  rw [mem_conjSub, ← conjSub_eq_self_iff, ← conjSub_eq_self_iff]
  constructor
  · intro hx
    calc conjSub A (g⁻¹ * x * g) = conjSub (conjSub (conjSub A g) x) g⁻¹ := by
          rw [← conjSub_mul, ← conjSub_mul, mul_assoc]
      _ = A := by rw [hx, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  · intro hx
    calc conjSub (conjSub A g) x = conjSub (conjSub A (g⁻¹ * x * g)) g := by
          rw [← conjSub_mul, ← conjSub_mul, show g * (g⁻¹ * x * g) = x * g by group]
      _ = conjSub A g := by rw [hx]

theorem Sec8.conjSub (hR : IsRootClass R) {A : Subgroup G} (h8 : Sec8 R A) (g : G) :
    Sec8 R (conjSub A g) := by
  refine ⟨?_, sigmaSet_ne_lambdaSet_conjSub hR h8.2 g⟩
  rw [normalizer_conjSub]
  exact ((MulAut.conj g).mapSubgroup.isCoatom_iff _).2 h8.1

theorem Sec8.of_mem (hR : IsRootClass R) {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ R)
    (h8 : Sec8 R A) : Sec8 R D := by
  obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hA hD
  exact h8.conjSub hR g

theorem centralizer_eq_bot_or_mem_of_commuting (h : Hyp G R) {A B C : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ R) (hAB : Opposite A B) (hBC : C ∈ psiSet R B) (hAC : Commuting A C)
    {N Z : Subgroup G} (hN : N = C ⊔ (⁅B, C⁆ ⊔ ⁅A, ⁅B, C⁆⁆))
    (hZ : Z = N ⊓ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G)) :
    (Z = ⊥ ∨ Z ∈ R) ∧ CoveredBy R N := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨⟨hDl, hDp, -, -, hNcov⟩, ⟨-, -, hMnorm, -, -, hNZ, hNZbot⟩, ⟨hcovM, hFZ, -⟩⟩ :=
    natural_module_of_commuting hR hiso hA hB hAB hBC hAC rfl hN hZ
  set D := ⁅B, C⁆ with hD
  set E := ⁅A, D⁆ with hE
  have hDR : D ∈ R := hDp.1
  have hER : E ∈ R := hDp.2.1
  have hCR : C ∈ R := hBC.1
  have hCDl : C ∈ lambdaSet R D := (mem_lambdaSet_commutator hR hiso hB hCR hBC.2).2
  have hDEl : D ∈ lambdaSet R E := (mem_lambdaSet_commutator hR hiso hA hDR hDp.2).2
  have hEDl : E ∈ lambdaSet R D := mem_lambdaSet_comm hER hDEl
  have hAEl : A ∈ lambdaSet R E := (mem_lambdaSet_commutator hR hiso hA hDR hDp.2).1
  have hND : N ≤ M R D := hN ▸ sup_le (QD.le_M hCDl) (sup_le QD.le_M_self (QD.le_M hEDl))
  have hPtD : ∀ F ∈ R, F ≤ N → F = D ∨ F ∈ lambdaSet R D := fun F hF hFN => by
    have hmem : F ∈ {B | B ∈ R ∧ B ≤ M R D} := ⟨hF, hFN.trans hND⟩
    rwa [(Q_eq_M h hDR).2.1] at hmem
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  obtain ⟨x, hx, hxde⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hB hA hAB.symm hDl hDp
    (Subgroup.mem_sup_left hd) hd1 (Subgroup.mem_sup_right he) he1
  have hDx : conjSub D x = E :=
    Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hDR x) hER (hxde ▸ conj_mem_conjSub x hd) he he1
  have hxY : x ∈ A ⊔ B ⊔ C := (sup_comm B A ▸ hx : x ∈ A ⊔ B) |> Subgroup.mem_sup_left
  have hNx : conjSub N x⁻¹ = N := by
    calc conjSub N x⁻¹ = conjSub (conjSub N x) x⁻¹ := by rw [hMnorm x hxY]
      _ = N := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hPtE : ∀ F ∈ R, F ≤ N → F = E ∨ F ∈ lambdaSet R E := fun F hF hFN => by
    have hF' : conjSub F x⁻¹ ≤ N := hNx ▸ Subgroup.map_mono hFN
    have hFF : conjSub (conjSub F x⁻¹) x = F := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    rcases hPtD _ (hR.conjSub_mem hF x⁻¹) hF' with h1 | h1
    · left
      rw [← hFF, h1, hDx]
    · right
      have := conjSub_mem_lambdaSet hR h1 x
      rwa [hFF, hDx] at this
  have hZN : Z ≤ N := hZ ▸ inf_le_left
  have hmain : Z = ⊥ ∨ Z ∈ R := by
    by_cases hZ0 : Z = ⊥
    · exact Or.inl hZ0
    right
    have hCE : C ≠ E := by
      intro hCE
      apply hZ0
      have hNDE : N = D ⊔ E := by
        rw [hN, hCE, sup_eq_right.2 le_sup_right]
      have : Z ≤ (D ⊔ E) ⊓ Z := le_inf (hZN.trans hNDE.le) le_rfl
      rwa [hNZbot, le_bot_iff] at this
    have hCEl : C ∈ lambdaSet R E := (hPtE C hCR (hN ▸ le_sup_left)).resolve_left hCE
    obtain ⟨z, hzZ, hz1'⟩ : ∃ z ∈ Z, z ≠ 1 := by
      obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ0
      exact ⟨z, z.2, fun e => hz1 (Subtype.ext e)⟩
    have hzN : z ∈ N := hZN hzZ
    have hzc : z ∈ Subgroup.centralizer ((A ⊔ B ⊔ C : Subgroup G) : Set G) := by
      have h1 := hzZ
      rw [hZ] at h1
      exact h1.2
    have hzA : ∀ a ∈ A, Commute a z := fun a ha =>
      Subgroup.mem_centralizer_iff.1 hzc a (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
    have hDEC : Commuting (D ⊔ E) C := Commuting.sup_left hCDl.1.2.2 hCEl.1.2.2
    have hCN : C ≤ Subgroup.normalizer ((D ⊔ E : Subgroup G) : Set G) :=
      le_normalizer_of_conjSub_le fun c hc =>
        (conjSub_of_forall_commute fun y hy => (hDEC y hy c hc).symm).le
    have hzmem : z ∈ ((C ⊔ (D ⊔ E) : Subgroup G) : Set G) := by
      rw [← hN]
      exact hzN
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C (D ⊔ E) hCN] at hzmem
    obtain ⟨c, hc, n, hn, hcn⟩ := hzmem
    have hnA : ∀ a ∈ A, Commute a n := fun a ha => by
      have h1 := hzA a ha
      rw [← hcn] at h1
      have h2 := (hAC a ha c hc).inv_right.mul_right h1
      rwa [inv_mul_cancel_left] at h2
    have hnE : n ∈ E := by
      by_cases hn1 : n = 1
      · rw [hn1]
        exact E.one_mem
      obtain ⟨P, hP, hPN, hnP, hAP⟩ :=
        exists_mem_commuting_of_coveredBy hR hiso hNcov hA hn hn1 hnA
      by_cases hPE : P = E
      · exact hPE ▸ hnP
      exfalso
      obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hDR hEDl hP hPN hER le_sup_right hPE
      have hAN : Commuting A (D ⊔ E) := hsup ▸ hAP.sup_right hAEl.1.2.2.symm
      exact Special.not_commuting hR hDp.2 (hAN.mono le_rfl le_sup_left)
    have hzCE : z ∈ E ⊔ C := hcn ▸ Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
      (Subgroup.mem_sup_left hnE)
    obtain ⟨F, hF, hFle, hzF⟩ := hCEl.2 _ hzCE hz1'
    have hFN : F ≤ N :=
      hFle.trans (sup_le (hN ▸ le_sup_right.trans le_sup_right) (hN ▸ le_sup_left))
    rcases hFZ F hF hFN with hbot | hFZ'
    · have : z ∈ F ⊓ Z := ⟨hzF, hzZ⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact absurd this hz1'
    · exact hFZ' ▸ hF
  refine ⟨hmain, fun m hm hm1 => ?_⟩
  by_cases hmZ : m ∈ Z
  · rcases hmain with h0 | hZR
    · rw [h0, Subgroup.mem_bot] at hmZ
      exact absurd hmZ hm1
    · exact ⟨Z, hZR, hZN, hmZ⟩
  · exact hcovM m hm hmZ

end CFSG.Timmesfeld.ARS
