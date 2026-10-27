module

public import CFSG.Quasithin.H13.LocDblDcos
public import CFSG.Quasithin.H13.LocDblLie

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc

variable {Γ : Type} [Group Γ]

theorem sq_card_radQuot_dvd_card [Finite Γ] {Y U V : Subgroup Γ} (hU : U ∈ cComp Y)
    (hV : V ∈ cComp Y) (hUV : U ≠ V) (e : ↥U ≃* ↥V) :
    Nat.card (↥U ⧸ CFSG.solvableRadical ↥U) ^ 2 ∣ Nat.card Y := by
  have hdvd := card_dvd_of_mem_cComp hU hV hUV
    (sup_le (le_of_mem_cComp hU) (le_of_mem_cComp hV))
  rw [← card_radQuot_congr e] at hdvd
  exact (pow_two (Nat.card (↥U ⧸ CFSG.solvableRadical ↥U)) ▸
    mul_dvd_mul_right (card_radQuot_dvd U) _).trans hdvd

theorem noIsoDouble_of_card_dvd [Finite Γ] {Y : Subgroup Γ} {N : ℕ} (hN : N ≠ 0)
    (hY : Nat.card Y ∣ N) (h : (N.primeFactors.filter fun r => r ^ 2 ∣ N).card ≤ 2) :
    NoIsoDouble Y := by
  intro U hU V hV ⟨e⟩
  by_contra hUV
  have hsq := (sq_card_radQuot_dvd_card hU hV hUV e).trans hY
  have h3 := three_le_card_primeFactors_radQuot hU
  have hsub : (Nat.card (↥U ⧸ CFSG.solvableRadical ↥U)).primeFactors ⊆
      N.primeFactors.filter fun r => r ^ 2 ∣ N := by
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    have h2 : r ^ 2 ∣ N := (pow_dvd_pow_of_dvd hr.2.1 2).trans hsq
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hr.1, (dvd_pow_self r two_ne_zero).trans h2, hN⟩, h2⟩
  have := Finset.card_le_card hsub
  omega

theorem slpTabsA_size' (ta tb : Array ℕ) (prog : List (ℕ × ℕ)) :
    (slpTabsA ta tb prog).size = prog.length + 2 := by
  have : ∀ (T : Array (Array ℕ)), (prog.foldl slpStepA T).size = T.size + prog.length := by
    induction prog with
    | nil => intro T; simp
    | cons p prog ih =>
      intro T
      simp only [List.foldl_cons, List.length_cons, ih, slpStepA, Array.size_push]
      omega
  unfold slpTabsA
  rw [this]
  simp only [List.size_toArray, List.length_cons, List.length_nil]
  omega

theorem img_of_tab {n : ℕ} [MulAction Γ (Fin n)] {g : Γ} {s : Array ℕ} (h : tab n g = s.toList)
    (q : ℕ) : img s q = act n g q := by
  change CFSG.QuasithinUnique.K1.SporadicPerm.img s q = act n g q
  rw [← img_tab, h, Array.toArray_toList]

theorem img_inv_of_check {n : ℕ} [MulAction Γ (Fin n)] {g : Γ} {s si : Array ℕ}
    (hs : ∀ q < n, img s q = act n g q) (hinv : ∀ q < n, img si (img s q) = q) :
    ∀ p < n, img si p = act n g⁻¹ p := by
  intro p hp
  have h1 : act n g (act n g⁻¹ p) = p := by rw [← act_mul _ _ hp, mul_inv_cancel, act_one hp]
  have := hinv (act n g⁻¹ p) (act_lt _ hp)
  rw [hs _ (act_lt _ hp), h1] at this
  exact this

theorem sylowNoDouble_of_dc [Finite Γ] (D : DcData) [MulAction Γ (Fin D.n)] (a b : Γ)
    (hbase : ∀ g : Γ, (∀ p ∈ D.B, act D.n g p = p) → g = 1)
    (hta : tab D.n a = (D.AB.getD 0 #[]).toList) (htb : tab D.n b = (D.AB.getD 1 #[]).toList)
    (prog : List (ℕ × ℕ)) (hprog : slpValidAux prog 2 = true) (qp : List ℕ)
    (hqp : ∀ i ∈ qp, i < prog.length + 2)
    (hRT : D.RT =
      (qp.map fun i => (slpTabsA (D.AB.getD 0 #[]) (D.AB.getD 1 #[]) prog)[i]!).toArray)
    (horder : Nat.card Γ = D.order) (k : ℕ) (hk : D.NR = 2 ^ k)
    (hodd : ¬ 2 ∣ D.order / D.NR)
    (hchk : D.chkAll = true)
    (hsq : ∀ V ∈ D.Vs, (V.2.2.2.primeFactors.filter fun r => r ^ 2 ∣ V.2.2.2).card ≤ 2) :
    SylowNoDouble Γ := by
  classical
  simp only [DcData.chkAll, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := hchk
  set T := slpTabsA (D.AB.getD 0 #[]) (D.AB.getD 1 #[]) prog with hT
  set E := slpElts a b prog with hE
  have hTs : T.size = prog.length + 2 := slpTabsA_size' _ _ _
  have hEtab : ∀ i < T.size, tab D.n (E.getD i 1) = (T[i]!).toList := by
    have h := slp_foldl_inv (n := D.n) prog #[a, b] #[(tab D.n a).toArray, (tab D.n b).toArray]
      (by simp) (by
        intro i hi
        have hi' : i < 2 := by simpa using hi
        interval_cases i <;> simp) (by simpa using hprog)
    have e1 : (#[(tab D.n a).toArray, (tab D.n b).toArray] : Array (Array ℕ)) =
        #[D.AB.getD 0 #[], D.AB.getD 1 #[]] := by
      rw [hta, htb, Array.toArray_toList, Array.toArray_toList]
    rw [e1] at h
    exact h.2
  set rg := qp.map fun i => E.getD i 1 with hrg
  simp only [DcData.chkInv, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at c0
  obtain ⟨⟨⟨hAB4, hRTi⟩, hABinv⟩, hRTinv⟩ := c0
  have hta' : ∀ q < D.n, img (D.AB.getD 0 #[]) q = act D.n a q := fun q _ => img_of_tab hta q
  have htb' : ∀ q < D.n, img (D.AB.getD 1 #[]) q = act D.n b q := fun q _ => img_of_tab htb q
  have htai := img_inv_of_check hta' fun q hq => (hABinv q hq).1
  have htbi := img_inv_of_check htb' fun q hq => (hABinv q hq).2
  have hAB : ABOK D.n D.AB a b := by
    intro l hl q hq
    interval_cases l
    · simpa using hta' q hq
    · simpa using htb' q hq
    · simpa using htai q hq
    · simpa using htbi q hq
  have hRTsize : D.RT.size = rg.length := by rw [hRT]; simp [hrg]
  have hRTt : ∀ t < rg.length, ∀ q < D.n,
      img (D.RT.getD t #[]) q = act D.n (rg.getD t 1) q := by
    intro t ht q _
    have htq : t < qp.length := by simpa [hrg] using ht
    have hi := hqp qp[t] (List.getElem_mem htq)
    have e1 : D.RT.getD t #[] = T[qp[t]]! := by
      rw [hRT, Array.getD_eq_getD_getElem?]
      simp [htq]
    have e2 : rg.getD t 1 = E.getD qp[t] 1 := by
      rw [hrg, List.getD_eq_getElem?_getD]
      simp [htq]
    rw [e1, e2]
    exact img_of_tab (hEtab _ (hTs ▸ hi)) q
  have hRTit : ∀ t < rg.length, ∀ q < D.n,
      img (D.RTi.getD t #[]) q = act D.n (rg.getD t 1)⁻¹ q := by
    intro t ht
    exact img_inv_of_check (hRTt t ht) fun q hq => hRTinv t (by omega) q hq
  have hRTok : RTOK D.n D.RT D.RTi rg :=
    ⟨hRTsize, hRTi.trans hRTsize, fun t ht q hq => ⟨hRTt t ht q hq, hRTit t ht q hq⟩⟩
  have c1' := c1
  simp only [DcData.chkBasic, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at c1'
  have hB : ∀ p ∈ D.B, p < D.n := c1'.1.1.1.1.1.1.1
  set R := Subgroup.closure {x | x ∈ rg} with hR
  have hG : ∀ t < D.RT.size, ∀ p < D.n, img (D.RT.getD t #[]) p = act D.n (rg.getD t 1) p :=
    fun t ht p hp => hRTt t (hRTsize ▸ ht) p hp
  have hcardR : Nat.card R = D.NR := card_of_chkR D rg hbase hB hRTsize hG c2
  have hidx : R.index = D.order / D.NR := by
    have h1 := R.card_mul_index
    rw [hcardR, horder] at h1
    have hpos : 0 < D.NR := by rw [hk]; positivity
    rw [← h1, Nat.mul_div_cancel_left _ hpos]
  have hRodd : ¬ 2 ∣ R.index := by rw [hidx]; exact hodd
  have hRsyl : IsSylowTwoOf R ⊤ := ⟨le_top, IsPGroup.of_card (hcardR.trans hk),
    by rw [show (R.subgroupOf ⊤).index = R.index from Subgroup.relIndex_top_right R]; exact hRodd⟩
  have main := dc_main D a b rg hbase hAB hRTok horder hRodd c1 c2 c3 c4 c5 c6 c7
  simp only [DcData.chkVs, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at c6
  refine sylowNoDouble_of_sylow hRsyl fun Y hRY hY => ?_
  obtain ⟨V, hV, hdvd⟩ := main Y hRY hY
  exact noIsoDouble_of_card_dvd (Nat.pos_iff_ne_zero.mp (c6 V hV).1.2) hdvd (hsq V hV)

end CFSG.Quasithin.H13.LocDbl
