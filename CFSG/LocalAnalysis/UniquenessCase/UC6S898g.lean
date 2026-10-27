module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S898f
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898e
public import CFSG.LocalAnalysis.UniquenessCase.UCK898b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R898Gamma (D : Data G) : Prop :=
  ∀ L ∈ calC D.M, ∀ n : ℕ, IsSU3 (Bar2 L) n → (n = 3 ∨ n = 21) →
    ∀ X : Subgroup G, X ≤ L → Nat.card X = 7 → ¬ IsStronglyPEmbedded 7 D.M →
      ∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 → rankThreeGamma 1 3 E ≤ D.M

theorem mulAut_pow_fix {X : Type*} [Group X] {α : MulAut X} {e : X} (h : α e = e) (k : ℕ) :
    (α ^ k) e = e := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem rho_fix_of_generator {L B : Subgroup G} {b₀ : G} (hbN : b₀ ∈ normalizer (L : Set G))
    (hBN : B ≤ normalizer (L : Set G)) (hgen : ∀ b ∈ B, ∃ k : ℕ, b₀ ^ k = b) {Eb : Subgroup (Bar2 L)}
    (hEb : ∀ e ∈ Eb, rhoL L ⟨b₀, hbN⟩ e = e) :
    ∀ b (hb : b ∈ B), ∀ e ∈ Eb, rhoL L ⟨b, hBN hb⟩ e = e := by
  intro b hb e he
  obtain ⟨k, hk⟩ := hgen b hb
  have hm : (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G))) = ⟨b₀, hbN⟩ ^ k :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hk.symm)
  rw [hm, map_pow]
  exact mulAut_pow_fix (hEb e he) k

theorem mem_map_conj_iff {H : Subgroup G} (g w : G) :
    w ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ H := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨g⁻¹ * w * g, h, by group⟩

theorem normalizer_map_conj_le {A M : Subgroup G} (g : G) (h : normalizer (A : Set G) ≤ M) :
    normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
      M.map (MulAut.conj g).toMonoidHom := by
  intro n hn
  rw [mem_map_conj_iff]
  apply h
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  have h1 := hn (g * x * g⁻¹)
  rw [mem_map_conj_iff, mem_map_conj_iff] at h1
  have e1 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  have e2 : g⁻¹ * (n * (g * x * g⁻¹) * n⁻¹) * g = g⁻¹ * n * g * x * (g⁻¹ * n * g)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem res_of_inputs (D : Data G) (hSg : SigmaStd D) (h846 : UC22.F08.R846 D) (hCen : UCK.U3Center)
    (hFI : UCK.U3FixInner) (hFF : UCK.U3FixField) (hI3 : UCK.U3Fix3Inner) (hF3 : UCK.U3Fix3Field)
    (hCov : UCK.U3E9Cover) (hFix : UCK.U3E9Fix) (hΓ : R898Gamma D) (h63 : UC6.R6_3 D) :
    R898Res D := by
  classical
  intro L hL n hX s hs hsn r hr hrs X hXL hXc hXN hres
  by_contra hXU
  have hr7 : r = 7 := eq_seven_of_residual hr hs hsn hrs hres
  subst hr7
  have hr5 : 5 ≤ 7 := by norm_num
  obtain ⟨g, y, hC⟩ := exists_ctx898 D hSg hCen hL hX hr hr5 hXL hXc hXN hXU
  have hαr := hC.rho_pow
  have hLM : L ≤ D.M := hL.1.le
  have hn : n = 3 ∨ n = 21 := by
    rcases hres with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  have hZ : ¬ 7 ∣ Nat.card (center (Bar2 L)) := by
    intro hdvd
    have h4 : 7 ∣ 3 := hdvd.trans (hCen (Bar2 L) n hX)
    omega
  have key : ∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 → E ∈ uniqueSet D.M := by
    intro E hEL hEel hEc
    have hΓE := hΓ L hL n hX hn X hXL hXc hC.hnsp E hEL hEel hEc
    have hU := h63 3 Nat.prime_three (by norm_num) E (hEL.trans hLM) hEel hEc hΓE
    refine mem_uniqueSet_of_forall D.maxLocal (hEL.trans hLM) (fun H hH hEH => ?_)
    have : H ∈ calMOf E := ⟨hH, hEH⟩
    rw [hU] at this
    exact this
  let Y : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom
  let M'' : Subgroup G := D.M.map (MulAut.conj g⁻¹).toMonoidHom
  have hYpg : IsPGroup 7 ↥Y := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hC.hYc)
  have hYgen : ∀ b ∈ Y, ∃ k : ℕ, y ^ k = b := hC.hyall
  have hBN : Y ≤ normalizer (L : Set G) := hC.mem_normalizer
  by_cases hα : rhoL L ⟨y, hC.hyN⟩ ∈ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range
  · by_cases hn3 : n = 3
    · subst hn3
      obtain ⟨z, hzo, hz⟩ := hI3 (Bar2 L) hX _ hαr hα
      have hzcard : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
      have hZ3 : IsPGroup 3 ↥(Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by simpa using hzcard)
      have hzfix : ∀ e ∈ Subgroup.zpowers z, rhoL L ⟨y, hC.hyN⟩ e = e := by
        intro e he
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
        rw [map_zpow]
        exact congrArg (· ^ j) hz
      obtain ⟨A, hAL, hAc, hAπ, hAcard, hAel⟩ := exists_lift_fixed (B := Y) (ℓ := 7) (q := 3) hr
        (by norm_num) Nat.prime_three (by norm_num) hBN hYpg (Subgroup.zpowers z) hZ3
        (rho_fix_of_generator hC.hyN hBN hYgen hzfix)
      have hAel' : IsElemAbelian 3 A := hAel (isElemAbelian_of_card_prime Nat.prime_three hzcard)
      have hAc3 : Nat.card A = 3 := hAcard.trans hzcard
      obtain ⟨Eb, hEbel, hEbc, hzEb⟩ := hCov (Bar2 L) hX z hzo
      have hAEb : (A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤ Eb :=
        hAπ.trans ((Subgroup.zpowers_le).2 hzEb)
      obtain ⟨S, hSL, hAS, hScard, hSel⟩ := exists_pgroup_containing (L := L) Nat.prime_three
        (by norm_num) Eb hEbel.isPGroup hAL hAel'.isPGroup hAEb
      have hNA : normalizer (A : Set G) ≤ D.M :=
        (normalizer_le_gamma hAS Nat.prime_three hAel' hAc3).trans
          (hΓ L hL 3 hX (Or.inl rfl) X hXL hXc hC.hnsp S hSL (hSel hEbel) (hScard.trans hEbc))
      let A₂ : Subgroup G := A.map (MulAut.conj g).toMonoidHom
      have hA₂c : Nat.card A₂ = 3 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hAc3]
      have hA₂X : ∀ a ∈ A₂, ∀ x ∈ X, a * x * a⁻¹ = x := by
        intro a ha x hx
        obtain ⟨a₀, ha₀, rfl⟩ := ha
        have hy₀ : g⁻¹ * x * g ∈ Y := by
          refine (mem_map_conj_inv g _).2 ?_
          have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
          rw [this]
          exact hx
        have hcomm : (g⁻¹ * x * g) * a₀ = a₀ * (g⁻¹ * x * g) :=
          Subgroup.mem_centralizer_iff.1 (hAc ha₀) _ hy₀
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc g * a₀ * g⁻¹ * x * (g * a₀ * g⁻¹)⁻¹
            = g * (a₀ * (g⁻¹ * x * g) * a₀⁻¹) * g⁻¹ := by group
          _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [← hcomm]; group
          _ = x := by group
      have hA₂cent : A₂ ≤ centralizer (X : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 := hA₂X a ha x hx
        calc x * a = (a * x * a⁻¹) * a := by rw [h1]
          _ = a * x := by group
      have hA₂M : A₂ ≤ D.M := fun a ha =>
        hXN (Subgroup.centralizer_le_normalizer _ (hA₂cent ha))
      have hA₂N : A₂ ≤ normalizer (L : Set G) := fun a ha =>
        mem_normalizer_of_centralizes hL (hA₂M ha) hr (by norm_num) hXL hXc hZ (hA₂X a ha)
      have hA₂pg : IsPGroup 3 ↥A₂ := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA₂c)
      obtain ⟨a₂, ha₂, ha₂o, ha₂gen⟩ := exists_generator Nat.prime_three hA₂c
      have hβ3 : (rhoL L ⟨a₂, hA₂N ha₂⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨a₂, hA₂N ha₂⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 :=
          Subtype.ext (by simpa using (ha₂o ▸ pow_orderOf_eq_one a₂))
        rw [this, map_one]
      obtain ⟨x, hxX, hxo, -⟩ := exists_generator hr hXc
      have hxL : x ∈ L := hXL hxX
      have hXpg : IsPGroup 7 ↥X := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hXc)
      have hxbo : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) = 7 := by
        have hdvd : orderOf (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ∣ 7 := by
          apply orderOf_dvd_of_pow_eq_one
          rw [← QuotientGroup.mk_pow]
          have : (⟨x, hxL⟩ : ↥L) ^ 7 = 1 :=
            Subtype.ext (by simpa using (hxo ▸ pow_orderOf_eq_one x))
          rw [this, QuotientGroup.mk_one]
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h1 | h7
        · exfalso
          have hxk : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
            (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
          have hxO : x ∈ pCoreOf 2 L := ⟨_, hxk, rfl⟩
          have hx1 : x = 1 := eq_one_of_mem_isPGroup_of_mem_isPGroup (by norm_num : Nat.Prime 7)
            (by norm_num : 7 ≠ 2) hXpg (isPGroup_pCoreOf L) hxX hxO
          rw [hx1, orderOf_one] at hxo
          omega
        · exact h7
      have hβx : rhoL L ⟨a₂, hA₂N ha₂⟩ (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) =
          QuotientGroup.mk (⟨x, hxL⟩ : ↥L) := by
        refine (rhoL_fix_iff L ⟨a₂, hA₂N ha₂⟩ ⟨x, hxL⟩).2 ?_
        show a₂ * x * a₂⁻¹ * x⁻¹ ∈ pCoreOf 2 L
        rw [hA₂X a₂ ha₂ x hxX, mul_inv_cancel]
        exact (pCoreOf 2 L).one_mem
      obtain ⟨Eb₂, hEb₂el, hEb₂c, hEb₂fix⟩ := hFix (Bar2 L) hX _ hxbo _ hβ3 hβx
      obtain ⟨E, hEL, hEcent, -, hEcard, hEel⟩ := exists_lift_fixed (B := A₂) (ℓ := 3) (q := 3)
        Nat.prime_three (by norm_num) Nat.prime_three (by norm_num) hA₂N hA₂pg Eb₂ hEb₂el.isPGroup
        (rho_fix_of_generator (hA₂N ha₂) hA₂N ha₂gen hEb₂fix)
      have hEU := key E hEL (hEel hEb₂el) (hEcard.trans hEb₂c)
      have hEMg : E ≤ D.M.map (MulAut.conj g).toMonoidHom := fun e he =>
        normalizer_map_conj_le g hNA (Subgroup.centralizer_le_normalizer _ (hEcent he))
      exact hC.hMg (hEU.2 g hEMg)
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨q, hq, hq3, hqn⟩ := exists_prime_gt_three_dvd hn2 hn3
      obtain ⟨z, hzo, hz⟩ := hFI (Bar2 L) n hX s hs hsn 7 hr hrs _ hαr hα q hq hq3 hqn
      exact false_of_fixed898 D h846 hL hX hr hr5 hC hq hq3 hqn hzo hz
  · by_cases hn3 : n = 3
    · subst hn3
      obtain ⟨m, hnm, -⟩ := hFF (Bar2 L) 3 hX s hs hsn 7 hr hrs _ hαr hα
      omega
    · have hn21 : n = 21 := by omega
      subst hn21
      obtain ⟨Eb, hEbel, hEbc, hEbfix⟩ := hF3 (Bar2 L) hX _ hαr hα
      obtain ⟨E, hEL, hEcent, -, hEcard, hEel⟩ := exists_lift_fixed (B := Y) (ℓ := 7) (q := 3) hr
        (by norm_num) Nat.prime_three (by norm_num) hBN hYpg Eb hEbel.isPGroup
        (rho_fix_of_generator hC.hyN hBN hYgen hEbfix)
      have hEU := key E hEL (hEel hEbel) (hEcard.trans hEbc)
      have hEM'' : E ≤ M'' := fun x hx =>
        hC.hYN (Subgroup.centralizer_le_normalizer _ (hEcent hx))
      exact hC.hM''ne (hEU.2 g⁻¹ hEM'')

theorem r898_full (D : Data G) (hSg : SigmaStd D) (h846 : UC22.F08.R846 D) (hCen : UCK.U3Center)
    (hRange : UCK.U3Range) (hFI : UCK.U3FixInner) (hFF : UCK.U3FixField) (hI3 : UCK.U3Fix3Inner)
    (hF3 : UCK.U3Fix3Field) (hCov : UCK.U3E9Cover) (hFix : UCK.U3E9Fix) (hΓ : R898Gamma D)
    (h63 : UC6.R6_3 D) : UC22.F08.R898 D :=
  r898_of_inputs D hSg h846 hCen hRange hFI hFF
    (res_of_inputs D hSg h846 hCen hFI hFF hI3 hF3 hCov hFix hΓ h63)

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
