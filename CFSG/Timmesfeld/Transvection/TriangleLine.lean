module

public import CFSG.Timmesfeld.Transvection.TriangleLA

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem commuting_of_le_sup_sup [Finite G] (hΔ : IsTransvectionClass Δ) (hiso : NoIsolated Δ)
    (hpts : PointsDetermined Δ) {A P Q R W : Subgroup G} (hA : A ∈ Δ) (hP : P ∈ Δ) (hQ : Q ∈ Δ)
    (hR : R ∈ Δ) (hAP : A ≠ P) (hAQ : A ≠ Q) (hAR : A ≠ R) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hQR : Q ≠ R) (cAQ : Commuting A Q) (cAR : Commuting A R) (cQR : Commuting Q R)
    (hle : P ≤ A ⊔ Q ⊔ R) (hW : W ∈ Δ) (hWA : Commuting W A) (hWP : Commuting W P) :
    Commuting W Q := by
  obtain ⟨p, hp, hp1⟩ := hΔ.root.exists_ne_one hP
  obtain ⟨w, hw, hw1⟩ := hΔ.root.exists_ne_one hW
  obtain ⟨x, hx, r, hr, hxr⟩ := mem_sup_of_commuting (cAR.sup_left cQR) (hle hp)
  obtain ⟨a, ha, q, hq, rfl⟩ := mem_sup_of_commuting cAQ hx
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxr
    have hpm : p ∈ (A ⊔ Q) ⊓ P :=
      ⟨hxr ▸ Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hq), hp⟩
    rw [sup_inf_eq_bot hΔ hiso hpts hA hQ hP hAQ hAP (Ne.symm hPQ) cAQ, Subgroup.mem_bot] at hpm
    exact hp1 hpm
  have hq1 : q ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxr
    have hpm : p ∈ (A ⊔ R) ⊓ P :=
      ⟨hxr ▸ Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hr), hp⟩
    rw [sup_inf_eq_bot hΔ hiso hpts hA hR hP hAR hAP (Ne.symm hPR) cAR, Subgroup.mem_bot] at hpm
    exact hp1 hpm
  have hqr : q * r = a⁻¹ * p := by
    rw [← hxr]
    group
  have hwqr : Commute w (q * r) := by
    rw [hqr]
    exact (hWA w hw a ha).inv_right.mul_right (hWP w hw p hp)
  have hwq := ((commute_mul_iff hΔ hiso hW hQ hR hQR cQR hw hw1 hq hq1 hr hr1).1 hwqr).1
  exact hΔ.commuting_of_commute hiso hW hQ hw hw1 hq hq1 hwq

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem conjSub_corrN_mem_lineOf [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {m : G} (hm : m ∈ corrN A E t) : conjSub A m ∈ lineOf Δ A B := by
  refine ⟨S.cls.root.conjSub_mem S.tri.memA m, fun W hW hWA hWB => ?_⟩
  by_cases hmA : conjSub A m = A
  · rw [hmA]
    exact hWA
  by_cases hmB : conjSub A m = B
  · rw [hmB]
    exact hWB
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hsB : conjSub A (partnerElt A E B e₀) = B := S.conjSub_partnerElt he₀ he₀1
  have hmm : m * m = 1 := S.mul_self_of_mem_corrN htY hq hm
  have hms : Commute m (partnerElt A E B e₀) := S.commute_of_mem_corrN' htY hq hm hsN
  have hnN : m * partnerElt A E B e₀ ∈ corrN A E t := Subgroup.mul_mem _ hm hsN
  have hn : conjSub A (m * partnerElt A E B e₀) = conjSub B m := by rw [conjSub_mul, hsB]
  have hnA : conjSub B m ≠ A := by
    intro h
    apply hmB
    rw [← h, ← conjSub_mul, hmm, conjSub_one]
  have hnB : conjSub B m ≠ B := by
    intro h
    apply hmA
    apply conjSub_injective (partnerElt A E B e₀)
    show conjSub (conjSub A m) (partnerElt A E B e₀) = conjSub A (partnerElt A E B e₀)
    rw [← conjSub_mul, ← hms.eq, conjSub_mul, hsB, h]
  have hnm : conjSub B m ≠ conjSub A m := fun h => S.tri.ne (conjSub_injective m h).symm
  have hAL : A ≤ corrL A E t := le_corrL
  have hBL : B ≤ corrL A E t := S.le_corrL_right
  have hmL := S.conjSub_le_corrL htY hq hm
  have hnL : conjSub B m ≤ corrL A E t := hn ▸ S.conjSub_le_corrL htY hq hnN
  have hmΔ : conjSub A m ∈ Δ := S.cls.root.conjSub_mem S.tri.memA m
  have hnΔ : conjSub B m ∈ Δ := S.cls.root.conjSub_mem S.tri.memB m
  have hL := S.sup_sup_eq_corrL htY hq hpts S.tri.memA hmΔ hnΔ hAL hmL hnL (Ne.symm hmA)
    (Ne.symm hnA) (Ne.symm hnm)
  exact commuting_of_le_sup_sup S.cls S.iso hpts S.tri.memA S.tri.memB hmΔ hnΔ S.tri.ne
    (Ne.symm hmA) (Ne.symm hnA) (Ne.symm hmB) (Ne.symm hnB) (Ne.symm hnm)
    (S.commuting_of_le_corrL htY hq hAL hmL) (S.commuting_of_le_corrL htY hq hAL hnL)
    (S.commuting_of_le_corrL htY hq hmL hnL) (hL ▸ hBL) hW hWA hWB

end TriangleSetting

end CFSG.Timmesfeld.Transvection
