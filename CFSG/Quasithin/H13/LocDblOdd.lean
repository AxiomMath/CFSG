module

public import CFSG.Quasithin.H13.LocDblDcSylow

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc

@[expose] def OddIndexBound (A : Type*) [Group A] (L : List ℕ) : Prop :=
  ∀ Y : Subgroup A, ¬ 2 ∣ Y.index → Y ≠ ⊤ → ∃ N ∈ L, Nat.card Y ∣ N

theorem OddIndexBound.of_mulEquiv {A A' : Type*} [Group A] [Group A'] [Finite A] {L : List ℕ}
    (e : A ≃* A') (h : OddIndexBound A L) : OddIndexBound A' L := by
  intro Y hY hne
  have hi : (Y.map e.symm.toMonoidHom).index = Y.index :=
    Subgroup.index_map_equiv (H := Y) e.symm
  have hne' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rw [Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective] at this
    rwa [show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id A' by ext; simp,
      Subgroup.map_id] at this
  obtain ⟨N, hN, hd⟩ := h _ (hi ▸ hY) hne'
  exact ⟨N, hN, by rwa [Subgroup.card_map_of_injective e.symm.injective] at hd⟩

variable {Γ : Type} [Group Γ]

theorem exists_isSylowTwoOf_le_of_odd_index [Finite Γ] {Y : Subgroup Γ} (hY : ¬ 2 ∣ Y.index) :
    ∃ R : Subgroup Γ, IsSylowTwoOf R ⊤ ∧ R ≤ Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 Y := default
  have hPidx : ¬ 2 ∣ (P : Subgroup Y).index := Sylow.not_dvd_index P
  refine ⟨(P : Subgroup Y).map Y.subtype, ⟨le_top, ?_, ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := n) (by
      rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact hn)
  · rw [show (((P : Subgroup Y).map Y.subtype).subgroupOf ⊤).index =
        ((P : Subgroup Y).map Y.subtype).index from
      Subgroup.relIndex_top_right _, Subgroup.index_map_subtype]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hPidx h
    · exact hY h
  · rintro _ ⟨x, -, rfl⟩
    exact x.2

theorem oddIndex_overgroup_of_dc [Finite Γ] (D : DcData) [MulAction Γ (Fin D.n)] (a b : Γ)
    (hbase : ∀ g : Γ, (∀ p ∈ D.B, act D.n g p = p) → g = 1)
    (hta : tab D.n a = (D.AB.getD 0 #[]).toList) (htb : tab D.n b = (D.AB.getD 1 #[]).toList)
    (prog : List (ℕ × ℕ)) (hprog : slpValidAux prog 2 = true) (qp : List ℕ)
    (hqp : ∀ i ∈ qp, i < prog.length + 2)
    (hRT : D.RT =
      (qp.map fun i => (slpTabsA (D.AB.getD 0 #[]) (D.AB.getD 1 #[]) prog)[i]!).toArray)
    (horder : Nat.card Γ = D.order) (k : ℕ) (hk : D.NR = 2 ^ k)
    (hodd : ¬ 2 ∣ D.order / D.NR)
    (hchk : D.chkAll = true) :
    ∀ Y : Subgroup Γ, ¬ 2 ∣ Y.index → Y ≠ ⊤ → ∃ V ∈ D.Vs, Nat.card Y ∣ V.2.2.2 := by
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
  intro Y hYodd hYne
  obtain ⟨R', hR'syl, hR'Y⟩ := exists_isSylowTwoOf_le_of_odd_index hYodd
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hRsyl hR'syl
  set e : Γ ≃* Γ := MulAut.conj g with he
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hYne
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rwa [map_map_symm_self, Subgroup.map_top_of_surjective _ e.surjective] at this
  have hRY : R ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_symm_map_self e R]
    refine Subgroup.map_mono ?_
    rw [show R.map e.toMonoidHom = R' from hg]
    exact hR'Y
  obtain ⟨V, hV, hdvd⟩ := main _ hRY hY'
  refine ⟨V, hV, ?_⟩
  rwa [Subgroup.card_map_of_injective e.symm.injective] at hdvd

theorem oddIndexBound_of_dc [Finite Γ] (D : DcData) [MulAction Γ (Fin D.n)] (a b : Γ)
    (hbase : ∀ g : Γ, (∀ p ∈ D.B, act D.n g p = p) → g = 1)
    (hta : tab D.n a = (D.AB.getD 0 #[]).toList) (htb : tab D.n b = (D.AB.getD 1 #[]).toList)
    (prog : List (ℕ × ℕ)) (hprog : slpValidAux prog 2 = true) (qp : List ℕ)
    (hqp : ∀ i ∈ qp, i < prog.length + 2)
    (hRT : D.RT =
      (qp.map fun i => (slpTabsA (D.AB.getD 0 #[]) (D.AB.getD 1 #[]) prog)[i]!).toArray)
    (horder : Nat.card Γ = D.order) (k : ℕ) (hk : D.NR = 2 ^ k)
    (hodd : ¬ 2 ∣ D.order / D.NR)
    (hchk : D.chkAll = true) :
    OddIndexBound Γ (D.Vs.map fun V => V.2.2.2) := fun Y hY hne => by
  obtain ⟨V, hV, hd⟩ := oddIndex_overgroup_of_dc D a b hbase hta htb prog hprog qp hqp hRT horder k
    hk hodd hchk Y hY hne
  exact ⟨V.2.2.2, List.mem_map.mpr ⟨V, hV, rfl⟩, hd⟩

end CFSG.Quasithin.H13.LocDbl
