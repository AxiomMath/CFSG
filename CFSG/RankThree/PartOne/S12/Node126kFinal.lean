module

public import CFSG.RankThree.PartOne.S12.Sec126a
public import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S12.PhanAssembly
public import CFSG.RankThree.PartOne.S12.TerminalWeyl
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.Torsion37

theorem node126k_of_inputs (h122 : Node122) (h122b : Node122b) (h123 : Node123)
    (h124 : Node124) (h124b : Node124b) (h125 : Node125)
    (hLAF : ∀ (p : ℕ) [Fact p.Prime], LAFaithful p) (hLA : LA126) (hD : ExtDickson)
    (hB : ExtBloomPrime) (hJP : ExtJonesParshall) (hKF : KF126) (hKFU4 : KF126U4)
    (hPhan : ExtPhan) : Node126k := by
  intro G _ _ p A c L E h hirr hcore hp5 hrow hcard hEA
  subst hp5
  obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    exact absurd hpf (by decide)
  have hEel : IsElementaryAbelian 5 E := h.E_elem
  obtain ⟨hBinv, hB0, hBE', hBE, hsup, hinf⟩ := sec126_a h124 h125 h hirr
  set B : Subgroup G := ⁅E, L ⊓ torusNormalizer E⁆ with hBdef
  have hcore' : CFSG.pCore 5 ↥(torusWeyl E) = ⊥ := by
    by_contra hne
    exact hcore hne
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hord : orderOf c = 5 := Sec12Three.orderOf_c h
  have hBcard : Nat.card B = 5 ^ 3 := by
    have hcomm : ∀ k ∈ Subgroup.zpowers c, ∀ l ∈ B, k * l = l * k := fun k hk l hl => by
      have hkE : k ∈ E := (Subgroup.zpowers_le.mpr hcE) hk
      exact congrArg Subtype.val (hEel.is_comm.comm ⟨k, hkE⟩ ⟨l, hBE hl⟩)
    have hdisj : Disjoint (Subgroup.zpowers c) B := disjoint_iff.mpr hinf
    have h1 := card_sup_of_commute_disjoint hcomm hdisj
    rw [← hsup, hcard, Nat.card_zpowers, hord] at h1
    norm_num at h1
    omega
  have hweyl := node126g_weyl_of_inputs h123 h124 h124b h125 hLAF hLA hD hB hJP hKF G 5 A c L E h
    hirr hcore
  have hL : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 4)) := hweyl
  obtain ⟨hclosure, -⟩ := h123 G 5 A c L E h
  have hLgen : torusImage E L =
      Subgroup.closure {t | t ∈ torusImage E L ∧ IsAutReflection 5 E t} := by
    apply le_antisymm
    · calc torusImage E L = Subgroup.closure (reflectionSet 5 E ∩ (torusImage E L : Set _)) :=
            hclosure
        _ ≤ Subgroup.closure {t | t ∈ torusImage E L ∧ IsAutReflection 5 E t} :=
            Subgroup.closure_mono (fun t ht => ⟨ht.2, ht.1.1⟩)
    · exact (Subgroup.closure_le _).2 (fun t ht => ht.1)
  have hirrW : ∀ B' : Subgroup G, B' ≤ B → torusInvariant E ⊤ B' → B' = ⊥ ∨ B' = B :=
    fun B' hle hinv => sec126_c_irred h124 h hinf hBE hBE' hle hinv
  have hno : ∀ C : Subgroup G, C ≤ E → torusInvariant E ⊤ C → C ⊓ B = ⊥ → C ⊔ B = E → False :=
    fun C hCE hCinv hCB hsupC => sec126_d_no_complement h124 h125 h hB0 hBE' hBE hCE hCinv hCB hsupC
  obtain ⟨hfaith, ψ, hsw, hsurj, -, k, hk⟩ := terminal_weyl_structure hD hB hJP hEel hcard hBE
    hBcard hBinv hsup hinf hcore' hirrW hno hL hLgen (Sec12Three.comm_c_L h)
  have hL24 : Nat.card (torusImage E L) = 24 := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hne : ∃ t ∈ reflectionSet 5 E, t ∈ torusImage E L := by
    by_contra hcon
    push Not at hcon
    have hempty : reflectionSet 5 E ∩ (torusImage E L : Set (MulAut E)) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun t ht => hcon t ht.1 ht.2
    rw [hempty, Subgroup.closure_empty] at hclosure
    rw [hclosure, Subgroup.card_bot] at hL24
    omega
  have hsub : reflectionSet 5 E ⊆ torusReflections 5 E := fun t ht =>
    ⟨WeylIso.mem_torusWeyl_of_mem_reflectionSet ht, ht.1⟩
  have hD' : reflectionSet 5 E = torusReflections 5 E := by
    apply Set.Subset.antisymm hsub
    obtain ⟨t0, ht0D, -⟩ := hne
    intro t ht
    obtain ⟨g, hg, hgt⟩ := WeylIso.exists_conj_eq_of_swaps ψ hsw (hsub ht0D) ht
    obtain ⟨w, hw, hwg⟩ := WeylIso.exists_lift (g := g)
      ((Subgroup.closure_le (K := torusWeyl E)).2 (fun _ ht' => ht'.1) hg)
    have h' := conj_mem_reflectionSet Nat.prime_five ht0D hw
    rw [hwg, hgt] at h'
    exact h'
  obtain ⟨W⟩ := WeylIso.nonempty_of_eq (p := 5) (n := 4) hD' ψ hsw hsurj k hk
  have hL24' : Nat.card (torusImage E L) = (4 : ℕ).factorial := by
    rw [hL24]
    rfl
  have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 h
  obtain ⟨hKat, hKpair⟩ := hKFU4 G 5 A c L E f h hF12 hf1 hpf hmodel hcard
  have hKall : ∀ t ∈ reflectionSet 5 E, KFAt 5 E f t := by
    intro t ht
    obtain ⟨w, hw, hwt, -⟩ := W.exists_conj_into_L hL24' ht ht
      (W.exists_common_fixed (by norm_num) ht ht)
    exact KFAt.of_conj hw (hKat _ (conj_mem_reflectionSet Nat.prime_five ht hw) hwt)
  have hPall : ∀ s ∈ reflectionSet 5 E, ∀ t ∈ reflectionSet 5 E, s ≠ t →
      KFPair 5 E f s t := by
    intro s hs t ht hst
    obtain ⟨w, hw, hws, hwt⟩ := W.exists_conj_into_L hL24' hs ht
      (W.exists_common_fixed (by norm_num) hs ht)
    have hne' : conjAut E w hw * s * (conjAut E w hw)⁻¹ ≠
        conjAut E w hw * t * (conjAut E w hw)⁻¹ := fun h' =>
      hst (mul_left_cancel (mul_right_cancel h'))
    exact KFPair.of_conj hw (hKpair _ (conj_mem_reflectionSet Nat.prime_five hs hw) hws _
      (conj_mem_reflectionSet Nat.prime_five ht hw) hwt hne')
  have hP := PhanAssembly.phan_conclusion W hPhan (by norm_num) Nat.prime_five le_rfl hEel hf2 hpf
    hBE hBinv hirrW hfaith hKall hPall
  obtain ⟨tt, htt⟩ := PhanAssembly.exists_chain W
  exact ⟨f, hf1, hpf, projSU_of_statedClassicalModel hP, ⟨W.ψ⟩, hcard, hEA,
    PhanAssembly.even_card_lieGenerated hKall (htt 0).1⟩

end CFSG.RankThree.PartOne
