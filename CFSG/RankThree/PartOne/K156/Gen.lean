module

public import CFSG.RankThree.PartOne.K1320.L4Final
public import CFSG.RankThree.PartOne.K1320.Row5
public import CFSG.RankThree.PartOne.K1320.Row7
public import CFSG.RankThree.PartOne.K1320.L4CT

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL permSL permSL_conj_rt rt ent ent_ext tSep
  tSep_mem cover_three)
open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

theorem exists_noncommuting_of_closure {M : Type*} [Group M] {S : Set M} {W : Subgroup M}
    (hW : W = Subgroup.closure S) (hnc : ∃ a b : W, a * b ≠ b * a) :
    ∃ s ∈ S, ∃ s' ∈ S, s * s' ≠ s' * s := by
  by_contra hcon
  push Not at hcon
  have h1 : S ⊆ (Subgroup.centralizer S : Set M) := fun s hs =>
    Subgroup.mem_centralizer_iff.2 fun s' hs' => (hcon s' hs' s hs)
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 h1
  have h3 : S ⊆ (Subgroup.centralizer (Subgroup.closure S : Set M) : Set M) := fun s hs =>
    Subgroup.mem_centralizer_iff.2 fun x hx => by
      exact (Subgroup.mem_centralizer_iff.1 (h2 hx) s hs).symm
  have h4 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set M) :=
    (Subgroup.closure_le _).2 h3
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  have ha : (a : M) ∈ Subgroup.closure S := hW ▸ a.2
  have hb : (b : M) ∈ Subgroup.closure S := hW ▸ b.2
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (h4 hb) a ha)

theorem dihedral_four_pow_four : ∀ x : DihedralGroup 4, x ^ 4 = 1 := by decide

theorem dihedral_four_noncomm : ∃ a b : DihedralGroup 4, a * b ≠ b * a :=
  ⟨DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩

theorem perm_three_noncomm : ∃ a b : Equiv.Perm (Fin 3), a * b ≠ b * a :=
  ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩

variable {G : Type} [Group G] {p : ℕ} {E X : Subgroup G}

theorem exists_pair_order_four
    (hclos : torusImage E X =
      Subgroup.closure (reflectionSet p E ∩ (torusImage E X : Set (MulAut E))))
    (e : ↥(torusImage E X) ≃* DihedralGroup 4) :
    ∃ s ∈ reflectionSet p E, s ∈ torusImage E X ∧ ∃ s' ∈ reflectionSet p E,
      s' ∈ torusImage E X ∧ orderOf (s * s') = 4 := by
  have hnc : ∃ a b : ↥(torusImage E X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := dihedral_four_noncomm
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  obtain ⟨s, hs, s', hs', hne⟩ := exists_noncommuting_of_closure hclos hnc
  refine ⟨s, hs.1, hs.2, s', hs'.1, hs'.2, ?_⟩
  have hs2 : orderOf s = 2 := hs.1.1.1
  have hs'2 : orderOf s' = 2 := hs'.1.1.1
  have hss : s * s = 1 := by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hs2])
  have hss' : s' * s' = 1 := by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hs'2])
  have h4 : (s * s') ^ 4 = 1 := by
    have := dihedral_four_pow_four (e ⟨s * s', (torusImage E X).mul_mem hs.2 hs'.2⟩)
    have h' : e (⟨s * s', (torusImage E X).mul_mem hs.2 hs'.2⟩ ^ 4) = 1 := by
      rw [map_pow]; exact this
    have h'' := e.injective (h'.trans (map_one e).symm)
    exact congrArg Subtype.val h''
  have hdvd : orderOf (s * s') ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have h2 : ¬ orderOf (s * s') ∣ 2 := by
    intro hd
    apply hne
    have hsq : (s * s') ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    have h1 : (s * s')⁻¹ = s * s' :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq)
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hsi' : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hss'
    have h3 : (s * s')⁻¹ = s' * s := by rw [mul_inv_rev, hsi, hsi']
    exact h1.symm.trans h3
  obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using hdvd :
    orderOf (s * s') ∣ 2 ^ 2)
  interval_cases k
  · exact absurd (by rw [hk2]; simp) h2
  · exact absurd (by rw [hk2]; norm_num) h2
  · rw [hk2]; norm_num

variable [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

omit [Finite G] in
theorem kZero_le_lieGenerated {f : ℕ} {s : MulAut E} (hs : s ∈ reflectionSet p E)
    (hK : KFAt p E f s) : kZero p E s ≤ lieGenerated p E :=
  le_sSup ⟨s, hs, (KFAt.toLiftAt hK).isKt⟩

theorem row5_le
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A) {f : ℕ} (hf1 : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f)
    (e : ↥(torusImage E L) ≃* DihedralGroup 4) : L ≤ lieGenerated p E := by
  obtain ⟨s, hs, hsL, s', hs', hs'L, hord⟩ := exists_pair_order_four hF.three.1 e
  obtain ⟨-, hpairs⟩ := K1320.row5Data_holds hGA G p A c L E f h hF hF13 hT hEA hf1 hpf hmodel
  obtain ⟨hdich, hgen⟩ := hpairs s hs hsL s' hs' hs'L hord
  rw [← hgen]
  rcases hdich with ⟨hK, hK'⟩ | ⟨hK, hK'⟩
  · exact sup_le (kZero_le_lieGenerated hs hK) (kZero_le_lieGenerated hs' hK')
  · exact sup_le (kZero_le_lieGenerated hs hK) (kZero_le_lieGenerated hs' hK')

theorem row7_le
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A) {f : ℕ} (hf1 : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f)
    (e : ↥(torusImage E L) ≃* DihedralGroup 4) : L ≤ lieGenerated p E := by
  obtain ⟨s, hs, hsL, s', hs', hs'L, hord⟩ := exists_pair_order_four hF.three.1 e
  obtain ⟨hAt, -, hpairs⟩ :=
    K1320.row7Data_holds hGA G p A c L E f h hF hF13 hT hEA hf1 hpf hmodel
  rw [← hpairs s hs hsL s' hs' hs'L hord]
  exact sup_le (kZero_le_lieGenerated hs (hAt s hs hsL))
    (kZero_le_lieGenerated hs' (hAt s' hs' hs'L))

theorem row8_le
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) {f : ℕ} (hf1 : 1 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) :
    L ≤ lieGenerated p E := by
  open K1320 in
  obtain ⟨hZ, -, K, _, _, _, ⟨fr⟩⟩ := row8Frame_of hGA h hF hF13 hEA hf1 hpf hmodel
  have hp5 := Sec12Three.five_le h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have hle := Nat.le_of_dvd (by norm_num) hpf
    omega
  have h4q : 4 ≤ Nat.card K := by
    rw [fr.hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hK1eq : kZero p E fr.r₀ = fr.lft (K1320.slB K 0 1) := fr.kz₀ h hF13 hZ
  have hK1req : kZero p E fr.r₁ = fr.lft ((blk8M (K := K)).range) := fr.kz₁ h hF13 hZ
  have h1 : L = fr.lft (K1320.slB K 0 1 ⊔ (blk8M (K := K)).range) := by
    rw [← K1320.blkA_zero_range (K := K), K1320.blkA_zero_sup_blk8M h4q]
    exact (K1320.liftM_top (K1320.q8_surj (K := K))).symm
  rw [h1, fr.lft_sup hZ, ← hK1eq, ← hK1req]
  exact sup_le (le_sSup ⟨fr.r₀, fr.mem₀, (KFAt.toLiftAt fr.kf₀).isKt⟩)
    (le_sSup ⟨fr.r₁, fr.mem₁, (KFAt.toLiftAt fr.kf₁).isKt⟩)

theorem row1_join_eq
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E = A) {f : ℕ}
    (hf : p ∣ 2 ^ f - 1) (hf1 : 1 ≤ f)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f)
    {s t : MulAut E} (hs : s ∈ reflectionSet p E) (hsL : s ∈ torusImage E L)
    (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) (hst : s ≠ t) :
    kZero p E s ⊔ kZero p E t = L := by
  subst hEA
  have hJ : JGood p E c L := jGood_of_row1 h hF rfl ⟨f, hf1, hf, hm⟩
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA hJ hf hm
  have hchar : CharP K 2 := charP_two_of_card hK
  obtain ⟨τ, -, hBs, hks, hse⟩ := kfAt_of_cover hJ hρ hK hf1 hf hs hsL
  obtain ⟨τ', -, hBt, hkt, hte⟩ := kfAt_of_cover hJ hρ hK hf1 hf ht htL
  have hne : Equiv.swap (τ 0) (τ 1) ≠ Equiv.swap (τ' 0) (τ' 1) := by
    intro heq
    apply hst
    have key : ∀ (π π' : Equiv.Perm (Fin 3))
        (hk : ρ (permSL π) ∈ Subgroup.normalizer (E : Set G))
        (hk' : ρ (permSL π') ∈ Subgroup.normalizer (E : Set G)), π = π' →
        E.normalizerMonoidHom ⟨ρ (permSL π), hk⟩ = E.normalizerMonoidHom ⟨ρ (permSL π'), hk'⟩ := by
      rintro π π' hk hk' rfl
      rfl
    rw [← hse, ← hte]
    exact key _ _ hks hkt heq
  rw [hBs, hBt, range_blkφ_conj, range_blkφ_conj, ← Subgroup.map_sup,
    blockConj_sup_eq_top τ τ' hne, ← MonoidHom.range_eq_map, hρ.range_eq]

theorem nonab_of_equiv {M P : Type*} [Group M] [Group P] (e : M ≃* P)
    (hP : ∃ a b : P, a * b ≠ b * a) : ∃ a b : M, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hP
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  apply e.symm.injective
  rw [map_mul, map_mul, h]

omit [Finite G] in
theorem nonabelian_of_rowWeylIso {W : Subgroup (MulAut E)} {r : ℕ} (hr1 : 1 ≤ r) (hr12 : r ≤ 12)
    (h : RowWeylIso E W r) : ∃ a b : ↥W, a * b ≠ b * a := by
  interval_cases r
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e perm_three_noncomm
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e ⟨DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e ⟨DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e ⟨DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e dihedral_four_noncomm
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e dihedral_four_noncomm
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e dihedral_four_noncomm
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e dihedral_four_noncomm
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e
      ⟨(1, Equiv.swap 0 1), (1, Equiv.swap 1 2), by decide⟩
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
  · obtain ⟨e⟩ := h
    exact nonab_of_equiv e ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩

theorem row1_le_of_ne
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E = A) {f : ℕ}
    (hf : p ∣ 2 ^ f - 1) (hf1 : 1 ≤ f)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f)
    {s t : MulAut E} (hs : s ∈ reflectionSet p E) (hsL : s ∈ torusImage E L)
    (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) (hst : s ≠ t) :
    L ≤ lieGenerated p E := by
  rw [← row1_join_eq hGA h hF hEA hf hf1 hm hs hsL ht htL hst]
  exact sup_le (kZero_le_lieGenerated hs (kfAt_row1 hGA h hF hEA hf hf1 hm s hs hsL))
    (kZero_le_lieGenerated ht (kfAt_row1 hGA h hF hEA hf hf1 hm t ht htL))

end CFSG.RankThree.PartOne.K156
