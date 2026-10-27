module

public import CFSG.Quasithin.Vol2.KGFactRankInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermK1

public section

namespace CFSG.Quasithin.H13.KGRank

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.QuasithinUnique.K1.SporadicPerm
open scoped Pointwise

section Cayley

variable {Γ : Type} [Group Γ] {N g gi : ℕ} {par cl : Array ℕ} {gens : List Γ} {ι : ℕ → Γ}

theorem card_le_of_forall_mem {E : Subgroup Γ} {L : List ℕ} (hE : ∀ x ∈ E, ∃ y ∈ L, ι y = x) :
    Nat.card E ≤ L.length := by
  classical
  have hsub : (E : Set Γ) ⊆ ↑((L.map ι).toFinset) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hE x hx
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨y, hy, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : Nat.card E = (E : Set Γ).ncard := Nat.card_coe_set_eq _
  rw [h2]
  calc (E : Set Γ).ncard ≤ (L.map ι).toFinset.card := h1
    _ ≤ (L.map ι).length := List.toFinset_card_le _
    _ = L.length := List.length_map _

theorem nodeCheck_sound (h : Cayley N g gi par cl gens ι) {Q : Subgroup Γ}
    (hsurj : ∀ x ∈ Q, ∃ i < N, ι i = x) (hιQ : ∀ i < N, ι i ∈ Q)
    (nodes : Array (List ℕ × List ℕ)) :
    ∀ (fuel j : ℕ) (F D : List ℕ),
      nodeCheck N (mulIdx g gi par cl N) nodes fuel j F D = true →
      (∀ f ∈ F, f < N) → (∀ y ∈ D, y < N) →
      (∀ y < N, (∀ f ∈ F, mulIdx g gi par cl N y f = mulIdx g gi par cl N f y) → y ∈ D) →
      ∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → (∀ f ∈ F, ι f ∈ E) →
        Nat.card E < 2 ^ 8 := by
  set mul := mulIdx g gi par cl N with hmul
  have hms : ∀ i k, i < N → k < N → mul i k < N ∧ ι (mul i k) = ι i * ι k :=
    fun i k hi hk => h.mulIdx_spec N i k hi.le hi hk
  intro fuel
  induction fuel with
  | zero => intro j F D hc; simp [nodeCheck] at hc
  | succ fuel ih =>
    intro j F D hc hF hDN hD E hEQ hE hFE
    have hlift : ∀ x ∈ E, ∃ y ∈ D, ι y = x ∧ mul y y = 0 := by
      intro x hx
      obtain ⟨y, hyN, rfl⟩ := hsurj x (hEQ hx)
      refine ⟨y, hD y hyN fun f hf => ?_, rfl, ?_⟩
      · have h1 := hms y f hyN (hF f hf)
        have h2 := hms f y (hF f hf) hyN
        apply h.inj _ h1.1 _ h2.1
        rw [h1.2, h2.2]
        exact congrArg Subtype.val (hE.1.is_comm.comm ⟨ι y, hx⟩ ⟨ι f, hFE f hf⟩)
      · have h1 := hms y y hyN hyN
        apply h.inj _ h1.1 0 h.pos
        rw [h1.2, h.zero, ← sq]
        exact hE.2 _ hx
    simp only [nodeCheck] at hc
    rcases Bool.or_eq_true_iff.mp hc with hleaf | hint
    ·
      have hlt : (D.filter fun x => mul x x == 0).length < 2 ^ 8 := of_decide_eq_true hleaf
      refine lt_of_le_of_lt (card_le_of_forall_mem (ι := ι) fun x hx => ?_) hlt
      obtain ⟨y, hyD, rfl, hyy⟩ := hlift x hx
      exact ⟨y, List.mem_filter.mpr ⟨hyD, by simp [hyy]⟩, rfl⟩
    ·
      set reps := pairsOf (nodes.getD j ([], [])).1 with hreps
      set wit := triplesOf (nodes.getD j ([], [])).2 with hwit
      set sp := spanIdx mul F with hsp
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hint
      obtain ⟨⟨⟨hsp8, hcands⟩, hwitok⟩, hrepok⟩ := hint
      by_contra hcon
      push Not at hcon
      obtain ⟨x, hxE, hxsp⟩ : ∃ x ∈ E, ∀ s ∈ sp, ι s ≠ x := by
        by_contra hno
        push Not at hno
        have := card_le_of_forall_mem (ι := ι) (E := E) (L := sp) fun x hx => by
          obtain ⟨s, hs, hsx⟩ := hno x hx
          exact ⟨s, hs, hsx⟩
        omega
      obtain ⟨y, hyD, rfl, hyy⟩ := hlift x hxE
      have hycand : y ∈ (D.filter fun x => mul x x == 0).filter fun x => !sp.contains x := by
        refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hyD, by simp [hyy]⟩, ?_⟩
        have hys : y ∉ sp := fun hy => hxsp y hy rfl
        simpa using hys
      rw [hcands] at hycand
      obtain ⟨w, hw, hwy⟩ := List.mem_map.mp hycand
      obtain ⟨⟨⟨hcN, hkr⟩, hcF⟩, hconj⟩ := hwitok w hw
      set c := w.2.1 with hc_def
      set rc := reps.getD w.2.2 (0, 0) with hrc
      have hrcmem : rc ∈ reps := by
        rw [hrc, List.getD_eq_getElem _ _ hkr]
        exact List.getElem_mem hkr
      obtain ⟨hrN, hchild⟩ := hrepok rc hrcmem
      set E' := E.map (MulAut.conj (ι c)).toMonoidHom with hE'
      have hconj' : ι c * ι y * (ι c)⁻¹ = ι rc.1 := by
        have h1 := hms c y hcN (hDN y hyD)
        have h2 := hms rc.1 c hrN hcN
        rw [hwy] at hconj
        have h3 : ι c * ι y = ι rc.1 * ι c := by rw [← h1.2, ← h2.2, hconj]
        rw [h3, mul_inv_cancel_right]
      have hfix : ∀ f ∈ F, ι c * ι f * (ι c)⁻¹ = ι f := by
        intro f hf
        have h1 := hms c f hcN (hF f hf)
        have h2 := hms f c (hF f hf) hcN
        have h3 : ι c * ι f = ι f * ι c := by rw [← h1.2, ← h2.2, hcF f hf]
        rw [h3, mul_inv_cancel_right]
      have hE'Q : E' ≤ Q := by
        rintro _ ⟨e, he, rfl⟩
        show ι c * e * (ι c)⁻¹ ∈ Q
        exact Q.mul_mem (Q.mul_mem (hιQ c hcN) (hEQ he)) (Q.inv_mem (hιQ c hcN))
      have hE'ab : IsElemAbelian 2 E' := CFSG.QuasithinUnique.Lin2.isElemAbelian_map' hE _
      have hFE' : ∀ f ∈ rc.1 :: F, ι f ∈ E' := by
        intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨ι y, hxE, hconj'⟩
        · exact ⟨ι f, hFE f hf, hfix f hf⟩
      have hlt := ih rc.2 (rc.1 :: F) (D.filter fun y => mul y rc.1 == mul rc.1 y) hchild
        (fun f hf => by
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hrN
          · exact hF f hf)
        (fun y hy => hDN y (List.mem_filter.mp hy).1)
        (fun y hyN hyF => List.mem_filter.mpr
          ⟨hD y hyN fun f hf => hyF f (List.mem_cons_of_mem _ hf),
            by simpa using hyF rc.1 List.mem_cons_self⟩)
        E' hE'Q hE'ab hFE'
      have hcard : Nat.card E' = Nat.card E :=
        Subgroup.card_map_of_injective (MulAut.conj (ι c)).injective
      omega

theorem card_lt_of_treeCheck [Finite Γ] (h : Cayley N g gi par cl gens ι) {Q : Subgroup Γ}
    (hsurj : ∀ x ∈ Q, ∃ i < N, ι i = x) (hιQ : ∀ i < N, ι i ∈ Q) {zi : ℕ}
    {nodes : Array (List ℕ × List ℕ)} (hc : treeCheck N g gi par cl zi nodes = true) :
    ∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → Nat.card E < 2 ^ 8 := by
  intro E hEQ hE
  simp only [treeCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hc
  obtain ⟨⟨⟨hzN, hzz⟩, hzc⟩, hnode⟩ := hc
  set mul := mulIdx g gi par cl N with hmul
  have hms : ∀ i k, i < N → k < N → mul i k < N ∧ ι (mul i k) = ι i * ι k :=
    fun i k hi hk => h.mulIdx_spec N i k hi.le hi hk
  set z := ι zi with hz
  have hz2 : z * z = 1 := by
    rw [← (hms zi zi hzN hzN).2, hzz, h.zero]
  have hzcQ : ∀ q ∈ Q, q * z = z * q := by
    intro q hq
    obtain ⟨i, hiN, rfl⟩ := hsurj q hq
    rw [← (hms zi i hzN hiN).2, ← (hms i zi hiN hzN).2, hzc i hiN]
  have hE' := isElemAbelian_sup_zpowers hE hz2 (fun e he => hzcQ e (hEQ he))
  have hE'Q : E ⊔ Subgroup.zpowers z ≤ Q := sup_le hEQ ((Subgroup.zpowers_le).mpr (hιQ zi hzN))
  have hlt := nodeCheck_sound h hsurj hιQ nodes _ 0 [zi] (List.range N) hnode
    (fun f hf => by rw [List.mem_singleton.mp hf]; exact hzN) (fun y hy => List.mem_range.mp hy)
    (fun y hy _ => List.mem_range.mpr hy) (E ⊔ Subgroup.zpowers z) hE'Q hE'
    (fun f hf => by
      rw [List.mem_singleton.mp hf]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  exact lt_of_le_of_lt (Subgroup.card_le_of_le le_sup_left) hlt

end Cayley

theorem elemAbelianLt_of_le_sylow {Γ : Type} [Group Γ] [Finite Γ] {Q : Subgroup Γ}
    (hQ : IsSylowTwoOf Q ⊤) {c : ℕ}
    (h : ∀ E : Subgroup Γ, E ≤ Q → IsElemAbelian 2 E → Nat.card E < c) : ElemAbelianLt Γ c := by
  intro E hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hQ
  have hEp : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨P', hP'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P' (hp.toSylow hi)
  have h2 : MulAut.conj g • (P' : Subgroup Γ) = Q := by
    have := congrArg (fun S : Sylow 2 Γ => (S : Subgroup Γ)) hg
    simpa [Sylow.coe_subgroup_smul] using this
  have hle : MulAut.conj g • E ≤ Q := by
    rw [← h2]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hP'
  have hab : IsElemAbelian 2 (MulAut.conj g • E) := by
    rw [Subgroup.pointwise_smul_def]
    exact CFSG.QuasithinUnique.Lin2.isElemAbelian_map' hE _
  have hcard : Nat.card ↥(MulAut.conj g • E) = Nat.card E :=
    (Nat.card_congr (Subgroup.equivSMul _ _).toEquiv).symm
  rw [← hcard]
  exact h _ hle hab

theorem elemAbelianLt_of_baseCertS {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
    (B : List ℕ) (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (a b : Γ) (prog : List (ℕ × ℕ)) (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ))
    (zn gn gin hn hin : ℕ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ)
    (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) {zi : ℕ} {nodes : Array (List ℕ × List ℕ)}
    (hc : treeCheck Ts.size qp.length qp.length par cl zi nodes = true) :
    ElemAbelianLt Γ (2 ^ 8) := by
  obtain ⟨-, -, hEnum, hQcard⟩ := A5.Kc3SporPerm.baseCertS_data B hB hbase a b prog hv qp zn gn
    gin hn hin Ts par cl k hcert
  obtain ⟨ι, hcay, hιQ, hsurj, -⟩ := exists_cayley_of_baseEnum hB hbase _ Ts par cl hEnum
  rw [List.length_map] at hcay
  refine elemAbelianLt_of_le_sylow ?_ (card_lt_of_treeCheck hcay hsurj hιQ hc)
  refine K1.isSylowTwoOf_top_iff.mpr ⟨IsPGroup.of_card hQcard, ?_⟩
  have h1 := Subgroup.card_mul_index
    (Subgroup.closure {x | x ∈ qp.map fun p => (slpElts a b prog).getD p.1 1})
  rw [hQcard, hcard] at h1
  have hidx := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [hidx]
  exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)

end CFSG.Quasithin.H13.KGRank
