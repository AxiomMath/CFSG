module

public import CFSG.Timmesfeld.Transvection.Sp4Radical
public import CFSG.Timmesfeld.Transvection.TriangleCoordsG

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem mem_corrN_of_mem_centralizer [Finite G] (hq : 4 ≤ Nat.card A) {y : G}
    (hy : y ∈ A ⊔ E ⊔ B) (hyX : ∀ x ∈ A ⊔ E, Commute y x) : y ∈ corrN A E t := by
  have hXN : A ⊔ E ≤ Subgroup.normalizer ((corrN A E t : Subgroup G) : Set G) := fun x hx =>
    conjSub_eq_self_iff.1 (conjSub_corrN hx)
  have hyXN : y ∈ ((A ⊔ E ⊔ corrN A E t : Subgroup G) : Set G) := by
    rw [← S.sup_eq_sup_corrN]
    exact hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXN] at hyXN
  obtain ⟨x, hx, n, hn, hxn⟩ := hyXN
  obtain rfl : x * n = y := hxn
  have hxc : x ∈ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : z * (x * n) * z⁻¹ = x * n := by
      rw [← (hyX z hz).eq]
      group
    have hzx : z * x * z⁻¹ ∈ A ⊔ E :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hz hx) (Subgroup.inv_mem _ hz)
    have hzn : z * n * z⁻¹ ∈ corrN A E t := conj_mem_corrN hz hn
    have h2 : x⁻¹ * (z * x * z⁻¹) = n * (z * n * z⁻¹)⁻¹ := by
      calc x⁻¹ * (z * x * z⁻¹) = x⁻¹ * (z * (x * n) * z⁻¹) * (z * n * z⁻¹)⁻¹ := by group
        _ = x⁻¹ * (x * n) * (z * n * z⁻¹)⁻¹ := by rw [h1]
        _ = n * (z * n * z⁻¹)⁻¹ := by group
    have h3 : x⁻¹ * (z * x * z⁻¹) ∈ corrN A E t ⊓ (A ⊔ E) :=
      ⟨h2 ▸ Subgroup.mul_mem _ hn (Subgroup.inv_mem _ hzn),
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hzx⟩
    rw [S.corrN_inf_sup_eq_bot htY hq, Subgroup.mem_bot, inv_mul_eq_one] at h3
    calc z * x = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [← h3]
  have hx1 : x = 1 :=
    S.tri.oppA.symm.eq_one_of_mem_centralizer (S.cls.root.mul_self A S.tri.memA) hx hxc
  rw [hx1, one_mul]
  exact hn

theorem eq_of_le_sup_of_commuting [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {D : Subgroup G} (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E) {D' : Subgroup G}
    (hD' : D' ∈ Δ) (hD'Y : D' ≤ A ⊔ E ⊔ B) (hD'A : Commuting D' A) (hD'E : Commuting D' E) :
    D' = D := by
  have hle : D' ≤ D := by
    rw [S.eq_corrN_inf_centralizer htY hq hpts hD hDE]
    intro d hd
    have hdX : ∀ x ∈ A ⊔ E, Commute d x := fun x hx =>
      commute_of_mem_sup_of_commute (fun a ha => hD'A d hd a ha) (fun e he => hD'E d hd e he) hx
    exact ⟨S.mem_corrN_of_mem_centralizer htY hq (hD'Y hd) hdX,
      Subgroup.mem_centralizer_iff.2 fun x hx => (hdX x hx).eq.symm⟩
  exact Subgroup.eq_of_le_of_card_ge hle (S.cls.root.card_eq hD.1 hD').le

theorem exists_graph_conjSub_E_eq [Finite G] (hq : 4 ≤ Nat.card A) {n : G}
    (hn : n ∈ corrN A E t) : ∃ f ∈ graph A t, conjSub E n = conjSub E f := by
  let c := S.coords htY hq
  obtain ⟨f, hf, hfv⟩ := c.bijOn_graph.surjOn
    (show ![0, c.vec n 1] ∈ {v : Fin 2 → GaloisField 2 c.k | v 0 = 0} from rfl)
  have hfN : f ∈ corrN A E t := corrM_le_corrN (graph_le_corrM hf)
  have hm : f⁻¹ * n ∈ corrN A E t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hfN) hn
  have hmE : ∀ e ∈ E, Commute (f⁻¹ * n) e := (c.commute_E_iff hm).2 (by
    rw [c.vec_mul (Subgroup.inv_mem _ hfN) hn, c.vec_inv hfN, hfv]
    simp)
  refine ⟨f, hf, ?_⟩
  rw [show n = f * (f⁻¹ * n) by group, conjSub_mul, conjSub_of_forall_commute hmE]

theorem conjSub_E_mem_lineOf [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) {D : Subgroup G} (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E)
    {n : G} (hn : n ∈ corrN A E t) : conjSub E n ∈ lineOf Δ E D := by
  have hΔ := S.cls
  have hE := S.tri.memE
  have hA := S.tri.memA
  obtain ⟨f, hf, hnf⟩ := S.exists_graph_conjSub_E_eq htY hq hn
  rw [hnf]
  have hDE' : D ≠ E := by
    intro h
    have hAD := (commuting_of_mem_lineOf' hΔ hA S.tri.memB S.tri.comm hD).1
    rw [h] at hAD
    exact S.tri.oppA.not_commuting (hΔ.root.ne_bot _ hE) hAD.symm
  by_cases hfE : conjSub E f = E
  · rw [hfE]
    exact left_mem_lineOf hE
  have hEf : conjSub E f ∈ Δ := hΔ.root.conjSub_mem hE f
  have hne : E ≠ conjSub E f := fun h => hfE h.symm
  have hcomm : Commuting E (conjSub E f) := by
    have := commuting_conjSub_graph hΔ S.iso hA hE S.commuting_conjSub S.ne_conjSub S.tri.oppA
      S.centE (graph A t).one_mem hf
    rwa [conjSub_one] at this
  have hAf : conjSub A f = A := conjSub_of_forall_commute fun a ha => S.commute_graph_left hf ha
  have hopp : Opposite A (conjSub E f) := by
    have := S.tri.oppA.conj f
    rw [hAf] at this
    exact this.symm
  have hT : IsTriangle Δ E A (conjSub E f) := ⟨hE, hA, hEf, hne, hcomm, S.tri.oppA.symm, hopp⟩
  obtain ⟨t', ht'Y, S'⟩ := exists_triangleSetting hΔ S.iso hT
  obtain ⟨D', hD'l, hAD'⟩ := hlines E hE (conjSub E f) hEf hne hcomm A hA
  have hq' : 4 ≤ Nat.card E := hΔ.root.card_eq hA hE ▸ hq
  have hD'Y' : D' ≤ E ⊔ A ⊔ conjSub E f :=
    S'.le_sup_of_mem_lineOf ht'Y hq' hpts hD'l hAD'.symm
  have hY'Y : E ⊔ A ⊔ conjSub E f ≤ A ⊔ E ⊔ B := by
    refine sup_le (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)) ?_
    exact conjSub_le (le_sup_right.trans le_sup_left) (S.graph_le_sup hf)
  have hED' : Commuting E D' := (commuting_of_mem_lineOf' hΔ hE hEf hcomm hD'l).1
  have hD'D : D' = D := S.eq_of_le_sup_of_commuting htY hq hpts hD hDE hD'l.1
    (hD'Y'.trans hY'Y) hAD'.symm hED'.symm
  rw [hD'D] at hD'l
  rw [lineOf_eq_of_mem_of_ne hΔ hpts hE hEf hne hcomm hD'l hDE']
  exact right_mem_lineOf hEf

theorem conjSub_mem_lineOf_E [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    (hlines : MeetsLines Δ) {D : Subgroup G} (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E)
    {n : G} (hn : n ∈ corrN A E t) {C : Subgroup G} (hC : C ∈ lineOf Δ E D) :
    conjSub C n ∈ lineOf Δ E D := by
  have hΔ := S.cls
  have hE := S.tri.memE
  have hDn : conjSub D n = D := by
    refine conjSub_of_forall_commute fun d hd => ?_
    rw [S.eq_corrN_inf_centralizer htY hq hpts hD hDE] at hd
    exact (S.commute_of_mem_corrN_inf_centralizer htY hq hd (S.corrN_le_sup hn)).symm
  have hDE' : D ≠ E := by
    intro h
    have hAD := (commuting_of_mem_lineOf' hΔ S.tri.memA S.tri.memB S.tri.comm hD).1
    rw [h] at hAD
    exact S.tri.oppA.not_commuting (hΔ.root.ne_bot _ hE) hAD.symm
  have hEn := S.conjSub_E_mem_lineOf htY hq hpts hlines hD hDE hn
  have h1 := conjSub_mem_lineOf_conjSub hΔ.root hC n
  rw [hDn] at h1
  have hEnD : conjSub E n ≠ D := by
    intro h
    apply hDE'
    rw [← hDn] at h
    exact (conjSub_injective n h).symm
  have hEn' : conjSub E n ∈ lineOf Δ D E := lineOf_comm (Δ := Δ) E D ▸ hEn
  have h2 : lineOf Δ D (conjSub E n) = lineOf Δ D E :=
    lineOf_eq_of_mem_of_ne hΔ hpts hD.1 hE hDE' hDE hEn' hEnD
  rw [lineOf_comm (Δ := Δ) (conjSub E n) D, h2, lineOf_comm (Δ := Δ) D E] at h1
  exact h1

end TriangleSetting

end CFSG.Timmesfeld.Transvection
