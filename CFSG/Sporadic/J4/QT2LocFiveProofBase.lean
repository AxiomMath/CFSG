
module

public import CFSG.Sporadic.J4.QT2LocFiveCheck
public import CFSG.Sporadic.J4.QT2LocRadGen
public import CFSG.Sporadic.J4.QTOutNorm

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

noncomputable def fiveElt : J := wordProd xJ fiveWord

theorem fiveWord_letters : ∀ ℓ ∈ fiveWord, ℓ ∈ letters := by
  intro ℓ hℓ
  simp only [fiveWord, letters, List.mem_cons, List.not_mem_nil, or_false] at hℓ ⊢
  omega

theorem fiveElt_mem_Hj : fiveElt ∈ Hj := wordProd_mem_Hj fiveWord_letters

theorem fiveElt_conj (hM : MatFacts) (c : ℕ) :
    fiveElt * eta uJ 11 c * fiveElt⁻¹ = eta uJ 11 (fiveAct c) := by
  have := word_conj XJ act fiveWord (fun ℓ hℓ c => hX_all hM (fiveWord_letters ℓ hℓ) c) c
  exact this

theorem fiveAct_masks : (∀ c < 2048, fiveAct c < 2048) ∧ fiveFixed.length = 8 ∧ fiveAct 1 ≠ 1 := by
  have h := chkFiveMasks_true
  unfold chkFiveMasks at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨fun c hc => h1 c hc, h2, h3⟩

theorem mem_fiveFixed {c : ℕ} : c ∈ fiveFixed ↔ c < 2048 ∧ fiveAct c = c := by
  simp [fiveFixed, List.mem_filter, List.mem_range]

theorem nodup_fiveFixed : fiveFixed.Nodup := by
  unfold fiveFixed
  exact (List.nodup_range).filter _

theorem fiveElt_pow (hM : MatFacts) : fiveElt ^ 5 = 1 := by
  apply Mx_injective
  have h := chkFivePow_true
  unfold chkFivePow at h
  rw [map_pow, map_one]
  have e : Mx fiveElt = rowsMatrix fiveRows := Mx_wordProd hM fiveWord
  rw [e, ← rowsMatrix_powRows, eqRows_iff.1 h, rowsMatrix_idRows]

theorem fiveElt_ne_one (hM : MatFacts) : fiveElt ≠ 1 := by
  intro h
  have h1 := fiveElt_conj hM 1
  rw [h] at h1
  obtain ⟨hlt, -, hne⟩ := fiveAct_masks
  have h2 : eta uJ 11 1 = eta uJ 11 (fiveAct 1) := by simpa using h1
  exact hne (eta_inj hM _ (by norm_num) _ (hlt 1 (by norm_num)) h2).symm

theorem orderOf_fiveElt (hM : MatFacts) : orderOf fiveElt = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (fiveElt_pow hM) (fiveElt_ne_one hM)

theorem card_centralizer_inf_Eg_fiveElt (hM : MatFacts) :
    Nat.card ↥(Subgroup.centralizer ({fiveElt} : Set J) ⊓ Eg uJ 11) = 8 := by
  obtain ⟨hlt, hlen, -⟩ := fiveAct_masks
  have hset : ((Subgroup.centralizer ({fiveElt} : Set J) ⊓ Eg uJ 11 : Subgroup J) : Set J) =
      ↑((fiveFixed.map (eta uJ 11)).toFinset) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨hc, hE⟩
      obtain ⟨c, hcl, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hE
      refine ⟨c, mem_fiveFixed.2 ⟨hcl, ?_⟩, rfl⟩
      have h1 := fiveElt_conj hM c
      have h2 : fiveElt * eta uJ 11 c * fiveElt⁻¹ = eta uJ 11 c := by
        rw [← hc]; group
      rw [h2] at h1
      exact (eta_inj hM _ hcl _ (hlt c hcl) h1).symm
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨hcl, hfix⟩ := mem_fiveFixed.1 hc
      refine ⟨?_, eta_mem_Eg 11 le_rfl c⟩
      have h1 := fiveElt_conj hM c
      rw [hfix] at h1
      calc eta uJ 11 c * fiveElt = (fiveElt * eta uJ 11 c * fiveElt⁻¹) * fiveElt := by rw [h1]
        _ = fiveElt * eta uJ 11 c := by group
  have hinj : (fiveFixed.map (eta uJ 11)).Nodup := by
    rw [List.nodup_map_iff_inj_on nodup_fiveFixed]
    intro c hc d hd e
    exact eta_inj hM c (mem_fiveFixed.1 hc).1 d (mem_fiveFixed.1 hd).1 e
  have : Nat.card ↥(Subgroup.centralizer ({fiveElt} : Set J) ⊓ Eg uJ 11) =
      (↑((fiveFixed.map (eta uJ 11)).toFinset) : Set J).ncard := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hinj, List.length_map, hlen]

theorem lt_relIndex_Eg_fiveElt (hM : MatFacts) :
    16 < (Eg uJ 11 ⊓ Subgroup.centralizer ({fiveElt} : Set J)).relIndex (Eg uJ 11) := by
  rw [inf_comm, Subgroup.inf_relIndex_right]
  have h := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({fiveElt} : Set J))
    (K := Eg uJ 11)
  rw [card_centralizer_inf_Eg_fiveElt hM, card_Eg_uJ hM] at h
  omega

theorem card_Hj_factorization_five (hF : J4Facts) : (Nat.card Hj).factorization 5 = 1 := by
  rw [card_Hj hF]
  have h : (501397585920 : ℕ) = 5 * 100279517184 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem lt_relIndex_Eg_of_order_five (hF : J4Facts) {g : J} (hg : g ∈ Hj) (h5 : orderOf g = 5) :
    16 < (Eg uJ 11 ⊓ Subgroup.centralizer ({g} : Set J)).relIndex (Eg uJ 11) := by
  have hM := hF.mat
  exact lt_relIndex_of_sylow Hj (Eg uJ 11) (Hj_normalizes_Eg hM) (card_Hj_factorization_five hF)
    fiveElt_mem_Hj (orderOf_fiveElt hM) (lt_relIndex_Eg_fiveElt hM) hg h5

end CFSG.Sporadic.J4.QT2
