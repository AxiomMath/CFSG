module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightT
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4b

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Eight

section Perm

variable {d : ℕ}

theorem fix_of_pow_five {σ : Perm (Fin d)} (h5 : σ ^ 5 = 1) {S : Finset (Fin d)} (hS : S.card ≤ 4)
    (hσS : σ ∈ setStab S) : ∀ a ∈ S, σ a = a := by
  classical
  intro a ha
  have hall : ∀ i : ℕ, (σ ^ i) a ∈ S := by
    intro i
    induction i with
    | zero => simpa using ha
    | succ i ih =>
      rw [pow_succ', Perm.mul_apply]
      exact (mem_setStab.1 hσS _).2 ih
  have hmaps : ∀ i ∈ (Finset.range 5), (σ ^ i) a ∈ S := fun i _ => hall i
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range 5) (t := S) (by rw [Finset.card_range]; omega) hmaps
  rw [Finset.mem_range] at hi hj
  have key : ∀ i j : ℕ, i < j → j < 5 → (σ ^ i) a = (σ ^ j) a → σ a = a := by
    intro i j hij hj heq
    have hk : (σ ^ (j - i)) ((σ ^ i) a) = (σ ^ i) a := by
      have e : σ ^ j = σ ^ (j - i) * σ ^ i := by rw [← pow_add]; congr 1; omega
      rw [← Perm.mul_apply, ← e]
      exact heq.symm
    have hord : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hcop : (j - i).Coprime (orderOf σ) := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hord with h | h
      · rw [h]
        exact Nat.coprime_one_right _
      · rw [h]
        have h1 : 1 ≤ j - i := by omega
        have h4 : j - i ≤ 4 := by omega
        generalize j - i = k at h1 h4 ⊢
        interval_cases k <;> decide
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hb : σ ((σ ^ i) a) = (σ ^ i) a := by
      have h1 : ((σ ^ (j - i)) ^ m) ((σ ^ i) a) = (σ ^ i) a :=
        Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hk m
      rwa [hm] at h1
    have : (σ ^ i) (σ a) = (σ ^ i) a := by
      rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply]
      exact hb
    exact (σ ^ i).injective this
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj heq
  · exact key j i h hi heq.symm

theorem eq_one_of_pow_five {I : Finset (Fin d)} (hI : I.card = 4) (hIc : Iᶜ.card = 4)
    {σ : Perm (Fin d)} (h5 : σ ^ 5 = 1) (hσ : σ ∈ setStab I ∨ ∀ y, σ y ∈ I ↔ y ∉ I) : σ = 1 := by
  have hσI : σ ∈ setStab I := by
    rcases hσ with h | h
    · exact h
    · have h2 : σ ^ 2 ∈ setStab I := fun y => by
        rw [pow_two, Perm.mul_apply, h, h]
        simp
      have e : σ = (σ ^ 2) ^ 3 := by
        rw [← pow_mul]
        calc σ = σ ^ 5 * σ := by rw [h5, one_mul]
          _ = σ ^ (2 * 3) := by rw [← pow_succ]
      rw [e]
      exact (setStab I).pow_mem h2 3
  have h1 := fix_of_pow_five h5 (by omega) hσI
  have h2 := fix_of_pow_five h5 (by omega) (setStab_le_compl I hσI)
  refine Equiv.ext fun y => ?_
  by_cases hy : y ∈ I
  · exact h1 y hy
  · exact h2 y (Finset.mem_compl.2 hy)

end Perm

section Group

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 8} (D : C.PiData)

theorem five_dvd_card_centralizer {y : G} (hy : y ∈ CFSG.Open.pCoreOf 2 M) {J : Finset (Fin 8)}
    (hJ : J.card ≤ 3) (hπ : Multiplicative.toAdd (D.piQ ⟨y, hy⟩) = barInd J) :
    5 ∣ Nat.card ↥(CGOf y) := by
  have hJc : 5 ≤ Jᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  have hA := altOn_le_theta_CMOf D hy hπ (S := Jᶜ) (Or.inr rfl)
  have h1 : 5 ∣ Nat.card ↥(altOn Jᶜ) := by
    rw [card_altOn (by omega)]
    have hf : 5 ∣ Jᶜ.card.factorial := Nat.dvd_factorial (by norm_num) hJc
    have h2 : 2 ∣ Jᶜ.card.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hk] at hf
    exact (Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 5 2)).1 hf
  have h2 : Nat.card ↥(altOn Jᶜ) ∣ Nat.card ↥(((CMOf M y).subgroupOf M).map C.θ) :=
    Subgroup.card_dvd_of_le hA
  have h3 : Nat.card ↥(((CMOf M y).subgroupOf M).map C.θ) ∣ Nat.card ↥((CMOf M y).subgroupOf M) :=
    Subgroup.card_map_dvd _ C.θ
  have h4 : Nat.card ↥((CMOf M y).subgroupOf M) = Nat.card ↥(CMOf M y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h5 : Nat.card ↥(CMOf M y) ∣ Nat.card ↥(CGOf y) := Subgroup.card_dvd_of_le inf_le_right
  rw [h4] at h3
  exact h1.trans (h2.trans (h3.trans h5))

theorem not_five_dvd_card_CMOf (hR : Nat.card ↥(Rc X) ≤ 2) {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) : ¬ 5 ∣ Nat.card ↥(CMOf M x) := by
  classical
  intro h5
  have hIc := card_compl_eight hI
  have hcard := C.card_eq_card_inf_mul hR (inf_le_left : CMOf M x ≤ M)
  have h2 : IsPGroup 2 ↥(CMOf M x ⊓ CFSG.Open.pCoreOf 2 M) :=
    isPGroup_of_le (isPGroup_pCoreOf' M) inf_le_right
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2
  rw [hcard, hk] at h5
  have h5' : 5 ∣ Nat.card ↥(((CMOf M x).subgroupOf M).map C.θ) :=
    (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right k (by norm_num)) h5)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨⟨σ, hσ⟩, hσo⟩ := exists_prime_orderOf_dvd_card' 5 h5'
  have hσo' : orderOf σ = 5 := by rw [← hσo, Subgroup.orderOf_mk]
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
  have hst := theta_stab_or_swap D hx hπ (Subgroup.mem_subgroupOf.1 hm)
  have hpow : C.θ m ^ 5 = 1 := by rw [← hσo']; exact pow_orderOf_eq_one _
  have h1 := eq_one_of_pow_five hI hIc hpow hst
  rw [h1, orderOf_one] at hσo'
  omega

theorem CGOf_le_CGOf_mul (C' : Cfg G M X 8) (hR : Nat.card ↥(Rc X) ≤ 2) {x r : G}
    (hr : r ∈ Rc X) (hKM : CGOf x ≤ M) : CGOf x ≤ CGOf (r * x) := by
  intro k hk
  have hkM := hKM hk
  have h1 : k * x * k⁻¹ = x := mem_centralizer_zpowers_iff.1 hk
  have h2 : k * r * k⁻¹ = r := C'.R_central hR k hkM r hr
  refine mem_centralizer_zpowers_iff.2 ?_
  calc k * (r * x) * k⁻¹ = (k * r * k⁻¹) * (k * x * k⁻¹) := by group
    _ = r * x := by rw [h1, h2]

theorem mem_M_of_conj_len_four (hR : Nat.card ↥(Rc X) ≤ 2)
    (h4 : ∀ y : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ y)) = 4 →
      CGOf (y : G) ≤ M)
    {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {I : Finset (Fin 8)} (hI : I.card = 4)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd I) {g : G}
    (hg : g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : g ∈ M := by
  classical
  have hIc := card_compl_eight hI
  have hlx : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 4 := by
    rw [hπ, barLen_barInd, hI]
    rfl
  have hKx : CGOf x ≤ M := h4 ⟨x, hx⟩ hlx
  set y : G := g * x * g⁻¹ with hydef
  have hCGy : CGOf y = conjSubgroup g (CGOf x) := H4b.CGOf_conj g x
  have hcardy : Nat.card ↥(CGOf y) = Nat.card ↥(CGOf x) := by
    rw [hCGy]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hCMx : CMOf M x = CGOf x := inf_eq_right.2 hKx
  obtain ⟨J, hJc, hJ⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ ⟨y, hg⟩))
  have hJle : J.card ≤ 4 := by
    rw [hJc]
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (D.piQ ⟨y, hg⟩))
    rw [← hz, barLen_mk]
    omega
  have hJ4 : J.card = 4 := by
    by_contra hne
    have h5 := five_dvd_card_centralizer D hg (by omega) hJ
    rw [hcardy, ← hCMx] at h5
    exact not_five_dvd_card_CMOf D hR hx hI hπ h5
  obtain ⟨τ, hτA, hτJ⟩ := Comb.exists_alt_map_eq (by norm_num) (I := J) (J := I)
    (by rw [hJ4, hI])
  obtain ⟨t, ht⟩ := C.exists_lift hτA
  have htM : (t : G) ∈ M := C.S.le t.2
  set m : ↥M := ⟨(t : G), htM⟩ with hm
  have hθm : C.θ m = τ := ht
  have hmy : (m : G) * y * (m : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M htM hg
  have hconj := D.piQ_conj m ⟨y, hg⟩ ⟨(m : G) * y * (m : G)⁻¹, hmy⟩ rfl
  rw [hJ, barAct_barInd, hθm] at hconj
  have himg : J.image τ = I := by
    rw [← hτJ, Finset.map_eq_image]
    rfl
  rw [himg, ← hπ] at hconj
  set r : G := (m : G) * y * (m : G)⁻¹ * x⁻¹ with hrdef
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem hmy ((CFSG.Open.pCoreOf 2 M).inv_mem hx)
  have hrR : r ∈ Rc X := by
    have h1 : D.piQ ⟨r, hrQ⟩ = 1 := by
      have e : (⟨r, hrQ⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
          ⟨(m : G) * y * (m : G)⁻¹, hmy⟩ * (⟨x, hx⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, hconj, add_neg_cancel, toAdd_one]
    exact (D.piQ_eq_one_iff _).1 h1
  have hmyx : (m : G) * y * (m : G)⁻¹ = r * x := by rw [hrdef]; group
  have hle := CGOf_le_CGOf_mul C hR hrR hKx
  have hcard2 : Nat.card ↥(CGOf (r * x)) = Nat.card ↥(CGOf x) := by
    rw [← hmyx, H4b.CGOf_conj]
    exact (show Nat.card ↥(conjSubgroup (m : G) (CGOf y)) = Nat.card ↥(CGOf y) from
      Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective).trans hcardy
  have heq : CGOf x = CGOf (r * x) := Subgroup.eq_of_le_of_card_ge hle hcard2.le
  set h : G := (m : G) * g with hh
  have hhx : h * x * h⁻¹ = r * x := by rw [← hmyx, hh, hydef]; group
  have hCh : conjSubgroup h (CGOf x) = CGOf x := by
    rw [← H4b.CGOf_conj, hhx, ← heq]
  have hTx : TOf M x = CFSG.Open.pCoreOf 2 (CGOf x) := by
    unfold TOf
    rw [show M ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = CGOf x from
      inf_eq_right.2 hKx]
  have hhK : h ∈ Subgroup.normalizer ((CGOf x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hCh
  have hnormK : ∀ n ∈ Subgroup.normalizer ((CGOf x : Subgroup G) : Set G), ∀ k ∈ CGOf x,
      n * k * n⁻¹ ∈ CGOf x := fun n hn k hk => (Subgroup.mem_normalizer_iff.1 hn k).1 hk
  have hhN : h ∈ Subgroup.normalizer ((TOf M x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hTx]
    refine ⟨fun ht' => pCoreOf_normalized_of_normal hnormK hhK ht', fun ht' => ?_⟩
    have := pCoreOf_normalized_of_normal hnormK
      ((Subgroup.normalizer ((CGOf x : Subgroup G) : Set G)).inv_mem hhK) ht'
    simpa [mul_assoc] using this
  have hhM := normalizer_TOf_le_M D hR hx hI hπ hhN
  have : g = (m : G)⁻¹ * h := by rw [hh]; group
  rw [this]
  exact M.mul_mem (M.inv_mem htM) hhM

end Group

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
