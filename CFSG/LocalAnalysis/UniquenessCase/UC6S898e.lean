module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S898d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898c
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCK898

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S898

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

structure Ctx898 (D : Data G) (L X : Subgroup G) (r : ℕ) (g y : G) : Prop where
  hrank : Open.pRank r D.M ≤ 3
  hnsp : ¬ IsStronglyPEmbedded r D.M
  hMg : D.M.map (MulAut.conj g).toMonoidHom ≠ D.M
  hXg : X ≤ D.M.map (MulAut.conj g).toMonoidHom
  hginvM : g⁻¹ ∉ D.M
  hYM : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ D.M
  hYc : Nat.card (X.map (MulAut.conj g⁻¹).toMonoidHom) = r
  hYN : normalizer ((X.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) ≤
    D.M.map (MulAut.conj g⁻¹).toMonoidHom
  hM''ne : D.M.map (MulAut.conj g⁻¹).toMonoidHom ≠ D.M
  hyY : y ∈ X.map (MulAut.conj g⁻¹).toMonoidHom
  hyr : orderOf y = r
  hyall : ∀ e ∈ X.map (MulAut.conj g⁻¹).toMonoidHom, ∃ k : ℕ, y ^ k = e
  hyN : y ∈ normalizer (L : Set G)

theorem Ctx898.mem_normalizer {D : Data G} {L X : Subgroup G} {r : ℕ} {g y : G} (hC : Ctx898 D L X r g y) :
    ∀ e ∈ X.map (MulAut.conj g⁻¹).toMonoidHom, e ∈ normalizer (L : Set G) := by
  intro e he
  obtain ⟨k, hk⟩ := hC.hyall e he
  rw [← hk]
  exact (Subgroup.normalizer _).pow_mem hC.hyN k

theorem Ctx898.rho_pow {D : Data G} {L X : Subgroup G} {r : ℕ} {g y : G} (hC : Ctx898 D L X r g y) :
    (rhoL L ⟨y, hC.hyN⟩) ^ r = 1 := by
  rw [← map_pow]
  have : (⟨y, hC.hyN⟩ : ↥(normalizer (L : Set G))) ^ r = 1 :=
    Subtype.ext (by simpa using (hC.hyr ▸ pow_orderOf_eq_one y))
  rw [this, map_one]

theorem exists_ctx898 (D : Data G) (hSg : SigmaStd D) (hCen : UCK.U3Center) {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (hX : IsSU3 (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : Nat.card X = r) (hXN : normalizer (X : Set G) ≤ D.M)
    (hXU : X ∉ uniqueSet D.M) : ∃ g y : G, Ctx898 D L X r g y := by
  classical
  have hLM : L ≤ D.M := hL.1.le
  have hXM : X ≤ D.M := hXL.trans hLM
  have hex : ∃ g : G, X ≤ D.M.map (MulAut.conj g).toMonoidHom ∧
      D.M.map (MulAut.conj g).toMonoidHom ≠ D.M := by
    by_contra hno
    push Not at hno
    exact hXU ⟨hXM, fun g hg => hno g hg⟩
  obtain ⟨g, hXg, hMg⟩ := hex
  have hr2 : r ≠ 2 := by omega
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hL
  have hgM : g ∉ D.M := fun hgM =>
    hMg (mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hgM))
  have hnsp : ¬ IsStronglyPEmbedded r D.M := by
    intro hsp
    have h1 := hsp.2.2 g hgM
    apply h1
    rw [← hXc]
    exact Subgroup.card_dvd_of_le (le_inf hXM hXg)
  have hrank : Open.pRank r D.M ≤ 3 := by
    by_contra h
    exact hnsp (sp_of_mem_sig hSg hns (hSg.four_mem r hr hr2 (by omega)))
  let Y : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom
  let M'' : Subgroup G := D.M.map (MulAut.conj g⁻¹).toMonoidHom
  have hYM : Y ≤ D.M := by
    intro z hz
    have hz' : g * z * g⁻¹ ∈ X := (mem_map_conj_inv g z).1 hz
    obtain ⟨m, hm, hmz⟩ := hXg hz'
    have : z = m := by
      have h1 : g * m * g⁻¹ = g * z * g⁻¹ := hmz
      simpa using h1.symm
    rw [this]
    exact hm
  have hYc : Nat.card Y = r := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hXc]
  have hYN : normalizer (Y : Set G) ≤ M'' := by
    intro n' hn'
    have h1 := conj_mem_normalizer_of_mem_normalizer_conj g n' hn'
    have h2 := hXN h1
    exact (mem_map_conj_inv g n').2 h2
  have hM''ne : M'' ≠ D.M := by
    intro h
    apply hMg
    have hginv : g⁻¹ ∈ normalizer (D.M : Set G) := mem_normalizer_iff_map_conj.2 h
    exact mem_normalizer_iff_map_conj.1 (by simpa using Subgroup.inv_mem _ hginv)
  have hginvM : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
  obtain ⟨y, hyY, hyr, hyall⟩ := exists_generator hr hYc
  have hyM : y ∈ D.M := hYM hyY
  have hZ : ¬ r ∣ Nat.card (center (Bar2 L)) := by
    intro hdvd
    have h3 := hCen (Bar2 L) n hX
    have h4 : r ∣ 3 := hdvd.trans h3
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  have hyN : y ∈ normalizer (L : Set G) :=
    normalizes_of_rank_lt_four hL hyM hr hr5 hyr hXL hXc hZ hrank
  exact ⟨g, y, hrank, hnsp, hMg, hXg, hginvM, hYM, hYc, hYN, hM''ne, hyY, hyr, hyall, hyN⟩

theorem false_of_fixed898 (D : Data G) (h846 : UC22.F08.R846 D) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hX : IsSU3 (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) {X : Subgroup G} {g y : G}
    (hC : Ctx898 D L X r g y) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) {z : Bar2 L}
    (hzo : orderOf z = q) (hαz : rhoL L ⟨y, hC.hyN⟩ z = z) : False := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hr2 : r ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hLM : L ≤ D.M := hL.1.le
  let Y : Subgroup G := X.map (MulAut.conj g⁻¹).toMonoidHom
  let M'' : Subgroup G := D.M.map (MulAut.conj g⁻¹).toMonoidHom
  let α : MulAut (Bar2 L) := rhoL L ⟨y, hC.hyN⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = q := by rw [Nat.card_zpowers, hzo]
  have hZq : IsPGroup q ↥(Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by simpa using hzcard)
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ :=
    exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker hq hq2 (Subgroup.zpowers z) hZq
  let A : Subgroup G := Q.map L.subtype
  have hAL : A ≤ L := Subgroup.map_subtype_le _
  have hAq : IsPGroup q A := hQp.map _
  have hAc : Nat.card A = q := by
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← card_map_of_disjoint_ker π Q hQdisj, hQmap, hzcard]
  have hfixpow : ∀ k : ℕ, (α ^ k) z = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply]; exact (congrArg _ hαz).trans ih
  have hcomm : ∀ e ∈ Y, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 L := by
    intro e he a ha
    obtain ⟨k, hk⟩ := hC.hyall e he
    obtain ⟨a', ha'Q, rfl⟩ := ha
    have hmem : π a' ∈ Subgroup.zpowers z := by
      rw [← hQmap]
      exact ⟨a', ha'Q, rfl⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
    set m : ↥(normalizer (L : Set G)) := (⟨y, hC.hyN⟩ : ↥(normalizer (L : Set G))) ^ k with hm
    have hmc : (m : G) = e := by
      rw [hm, Subgroup.coe_pow]
      exact hk
    have hρ : rhoL L m = α ^ k := by rw [hm, map_pow]
    have hfix : rhoL L m (QuotientGroup.mk a') = QuotientGroup.mk a' := by
      rw [hρ]
      have h1 : (QuotientGroup.mk a' : Bar2 L) = z ^ j := hj.symm
      rw [h1, map_zpow, hfixpow k]
    have h2 := (rhoL_fix_iff L m a').1 hfix
    rw [hmc] at h2
    exact h2
  have hYpg : IsPGroup r ↥Y := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hC.hYc)
  have hAO : A ≤ normalizer (pCoreOf 2 L : Set G) :=
    hAL.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf L))
  have hYO : Y ≤ normalizer (pCoreOf 2 L : Set G) :=
    fun e he => normalizer_le_normalizer_pCoreOf L (hC.mem_normalizer e he)
  obtain ⟨A', hA'c, hA'le, ⟨eqv⟩⟩ := exists_centralizing_copy hr hr2 hq hq2 (pCoreOf 2 L) A Y
    (isPGroup_pCoreOf L) hAO hYO hAq hYpg hcomm
  have hA'M : A' ≤ D.M :=
    hA'le.trans (sup_le (hAL.trans hLM) ((Subgroup.map_subtype_le _).trans hLM))
  have hA'M'' : A' ≤ M'' := fun x hx =>
    hC.hYN (Subgroup.centralizer_le_normalizer _ (hA'c hx))
  have hA'card : Nat.card A' = q := by rw [Nat.card_congr eqv.toEquiv, hAc]
  have hsp := h846 L hL n hX q hq hq3 hqn
  apply hsp.2.2 g⁻¹ hC.hginvM
  rw [← hA'card]
  exact Subgroup.card_dvd_of_le (le_inf hA'M hA'M'')

theorem r898_of_inputs (D : Data G) (hSg : SigmaStd D) (h846 : UC22.F08.R846 D)
    (hCen : UCK.U3Center) (hRange : UCK.U3Range) (hFI : UCK.U3FixInner) (hFF : UCK.U3FixField)
    (hRes : R898Res D) : UC22.F08.R898 D := by
  classical
  intro L hL n hX s hs hsn r hr hrs X hXL hXc hXN
  by_cases hres : n = 3 ∨ n = 3 * r
  · exact hRes L hL n hX s hs hsn r hr hrs X hXL hXc hXN hres
  by_contra hXU
  have hr5 : 5 ≤ r := prime_ne_two_three_of_dvd hr hs hrs
  have hr2 : r ≠ 2 := by omega
  obtain ⟨g, y, hC⟩ := exists_ctx898 D hSg hCen hL hX hr hr5 hXL hXc hXN hXU
  have hαr := hC.rho_pow
  obtain ⟨q, hq, hq3, hqn, z, hzo, hαz⟩ : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ 2 ^ n + 1 ∧
      ∃ z : Bar2 L, orderOf z = q ∧ rhoL L ⟨y, hC.hyN⟩ z = z := by
    have hn2 : 2 ≤ n := hRange (Bar2 L) n hX
    by_cases hα : rhoL L ⟨y, hC.hyN⟩ ∈ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range
    · have hn3 : n ≠ 3 := fun h => hres (Or.inl h)
      obtain ⟨q, hq, hq3, hqn⟩ := exists_prime_gt_three_dvd hn2 hn3
      obtain ⟨z, hzo, hz⟩ := hFI (Bar2 L) n hX s hs hsn r hr hrs _ hαr hα q hq hq3 hqn
      exact ⟨q, hq, hq3, hqn, z, hzo, hz⟩
    · obtain ⟨m, hnm, hm⟩ := hFF (Bar2 L) n hX s hs hsn r hr hrs _ hαr hα
      have hm0 : m ≠ 0 := by
        rintro rfl
        omega
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [mul_one] at hnm
        rw [hnm] at hsn
        rcases (Nat.dvd_prime hr).1 hsn with rfl | rfl
        · have : r ∣ 1 := by simpa using hrs
          exact hr.one_lt.ne' (Nat.dvd_one.1 this)
        · exact not_dvd_two_pow_sub_one_self hr hrs
      have hm3 : m ≠ 3 := fun h => hres (Or.inr (by rw [hnm, h, mul_comm]))
      obtain ⟨q, hq, hq3, hqm⟩ := exists_prime_gt_three_dvd (by omega) hm3
      have hqn : q ∣ 2 ^ n + 1 :=
        hqm.trans (by rw [hnm]; exact two_pow_add_one_dvd (hr.odd_of_ne_two hr2))
      obtain ⟨z, hzo, hz⟩ := hm q hq hq3 hqm
      exact ⟨q, hq, hq3, hqn, z, hzo, hz⟩
  exact false_of_fixed898 D h846 hL hX hr hr5 hC hq hq3 hqn hzo hαz

end CFSG.LocalAnalysis.UniquenessCase.UC6S898
