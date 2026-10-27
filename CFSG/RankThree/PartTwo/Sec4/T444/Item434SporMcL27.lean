module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenJ2HSMcLCheck
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.KFacts.K426McL
public import CFSG.Sporadic.SmallOddCore.McLAut

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Sporadic.Schreier (mclP)
open CFSG.RankThree.PartTwo.KFacts.K426 (mcl3Q mcl3QGens mcl3Lines mcl3QCert)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open Item434Kit Item434Alt Item434Spor

namespace Item434SporGen

theorem isElemAbelian_closure_of_comm {Y : Type*} [Group Y] {S : Set Y}
    (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (h3 : ∀ x ∈ S, x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem false_of_e81 (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : P.map (MulAut.conj : X →* MulAut X) = A.map (quotConj e))
    {B E : Subgroup X} (hBP : B ≤ P) (hB9 : 9 ≤ Nat.card B)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : 81 ≤ Nat.card E)
    (hBE : ∀ b ∈ B, ∀ d ∈ E, b * d = d * b) : False := by
  set F := B.map (MulAut.conj : X →* MulAut X) with hF
  have hFA : F ≤ A.map (quotConj e) := hP ▸ Subgroup.map_mono hBP
  have hF9 : 9 ≤ Nat.card F := by
    rw [hF, Subgroup.card_map_of_injective (conj_injective_of_center_eq_bot hcen)]
    exact hB9
  refine false_of_fixed h hZ e inf_le_left (hF9.trans (card_le_card_inf_comap e hFA)) hE hE81 ?_
  intro a ha d hd
  obtain ⟨β, hβ, hβa⟩ := ha.2
  rw [← hβa, MulAut.conj_apply, hBE β hβ d hd, mul_inv_cancel_right]

end Ctx

theorem mem_mclP_of_mclSift
    {x : Array ℕ} (hx : mclSift x = true) : permOfArr 275 x ∈ mclP := by
  simp only [mclSift, Bool.and_eq_true] at hx
  exact KFacts.K426.mem_mclP_of_sift (rep_permOfArr hx.1).1 hx.2

theorem rep_of_mclSift {x : Array ℕ} (hx : mclSift x = true) :
    Monster.B.Co2.Rep 275 x (permOfArr 275 x) ∧
      Monster.B.Co2.Rep 275 (invCand 275 x) (permOfArr 275 x)⁻¹ := by
  simp only [mclSift, Bool.and_eq_true] at hx
  exact rep_permOfArr hx.1

theorem rep_conjN {q t : Array ℕ} {g h : Equiv.Perm (Fin 275)} (hq : Monster.B.Co2.Rep 275 q g)
    (hqi : Monster.B.Co2.Rep 275 (invCand 275 q) g⁻¹) (ht : Monster.B.Co2.Rep 275 t h) :
    Monster.B.Co2.Rep 275 (conjN 275 q t) (g * h * g⁻¹) :=
  rep_compA (rep_compA hq ht) hqi


theorem mcl_d_spec :
    (∀ k < 4, mclSift (mclArr k) = true) ∧
      (∀ k < 4, eqA 275 (powN 275 (mclArr k) 3) (idA 275) = true) ∧
      (∀ k < 4, ∀ l < 4, commN 275 (mclArr k) (mclArr l) = true) ∧
      ∀ u < 81, ∀ v < 81, u = v ∨ eqA 275 (mclDProd u) (mclDProd v) = false := by
  have h := mcl_d_check
  simp only [mclDCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun k hk => allLt_spec h1 hk, fun k hk => allLt_spec h2 hk,
    fun k hk l hl => allLt_spec (allLt_spec h3 hk) hl, fun u hu v hv => ?_⟩
  have := allLt_spec (allLt_spec h4 hu) hv
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  exact this

@[expose] noncomputable def dM
    (k : Fin 4) : mclP :=
  ⟨permOfArr 275 (mclArr k), mem_mclP_of_mclSift (mcl_d_spec.1 k k.2)⟩

@[expose] noncomputable def zM :
    mclP :=
  dM 0

theorem rep_dM (k : Fin 4) :
    Monster.B.Co2.Rep 275 (mclArr k) (dM k : Equiv.Perm (Fin 275)) :=
  (rep_of_mclSift (mcl_d_spec.1 k k.2)).1


@[expose] noncomputable def mclD : Subgroup mclP := Subgroup.closure (Set.range dM)

@[expose] noncomputable def prodM (u : ℕ) : mclP :=
  dM 0 ^ (u % 3) * dM 1 ^ (u / 3 % 3) * dM 2 ^ (u / 9 % 3) * dM 3 ^ (u / 27 % 3)

theorem rep_mclDProd (u : ℕ) :
    Monster.B.Co2.Rep 275 (mclDProd u) (prodM u : Equiv.Perm (Fin 275)) := by
  simp only [prodM, Subgroup.coe_mul, Subgroup.coe_pow]
  exact rep_compA (rep_compA (rep_compA (rep_powN (rep_dM 0) _) (rep_powN (rep_dM 1) _))
    (rep_powN (rep_dM 2) _)) (rep_powN (rep_dM 3) _)

theorem prodM_mem (u : ℕ) : prodM u ∈ mclD := by
  have h : ∀ k, dM k ∈ mclD := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (h 0) _)
    (Subgroup.pow_mem _ (h 1) _)) (Subgroup.pow_mem _ (h 2) _)) (Subgroup.pow_mem _ (h 3) _)

theorem isElemAbelian_mclD : CFSG.Assembly.IsElemAbelian 3 mclD := by
  refine isElemAbelian_closure_of_comm ?_ ?_
  · rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    apply Subtype.ext
    exact mul_comm_of_commN (rep_dM k) (rep_dM l) (mcl_d_spec.2.2.1 k k.2 l l.2)
  · rintro _ ⟨k, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN (rep_dM k) 3) rep_idA (mcl_d_spec.2.1 k k.2)

theorem card_mclD : 81 ≤ Nat.card mclD := by
  set f : Fin 81 → mclD := fun u => ⟨prodM u, prodM_mem u⟩ with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (prodM u : Equiv.Perm (Fin 275)) = prodM v :=
      congrArg (fun w : mclD => ((w : mclP) : Equiv.Perm (Fin 275))) huv
    rcases mcl_d_spec.2.2.2 u u.2 v v.2 with h | h
    · exact Fin.ext h
    · rw [(eqA_iff (rep_mclDProd u) (rep_mclDProd v)).2 h1] at h
      exact absurd h Bool.noConfusion
  have := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem eq_prodM_of_inD {x : Array ℕ} {g : Equiv.Perm (Fin 275)}
    (hx : Monster.B.Co2.Rep 275 x g) (h : mclInD x = true) :
    ∃ u, g = (prodM u : Equiv.Perm (Fin 275)) := by
  simp only [mclInD, List.any_eq_true, List.mem_range] at h
  obtain ⟨u, -, hu⟩ := h
  exact ⟨u, eq_of_eqA hx (rep_mclDProd u) hu⟩

@[expose] noncomputable def mclQ : Subgroup mclP :=
  mcl3Q.subgroupOf mclP

theorem card_mclQ :
    Nat.card mclQ = 3 ^ (Nat.card mclP).factorization 3 := by
  rw [mclQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe KFacts.K426.mcl3Q_le).toEquiv]
  exact KFacts.K426.card_mcl3Q

theorem mcl_z_spec :
    eqA 275 (mclArr 0) (idA 275) = false ∧
      ∀ k < mcl3QGens.size, commN 275 (mclArr 0) mcl3QGens[k]! = true := by
  have h := mcl_z_check
  simp only [mclZCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, fun k hk => allLt_spec h.2 hk⟩

theorem zM_ne_one : zM ≠ 1 := by
  intro h
  have h1 : (zM : Equiv.Perm (Fin 275)) = 1 := by rw [h]; rfl
  have := (eqA_iff (rep_dM 0) rep_idA).2 h1
  rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, mcl_z_spec.1] at this
  exact Bool.noConfusion this

theorem zM_cube : zM ^ 3 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact eq_of_eqA (rep_powN (rep_dM 0) 3) rep_idA (mcl_d_spec.2.1 0 (by norm_num)))

theorem zM_mem_mclD : zM ∈ mclD := Subgroup.subset_closure ⟨0, rfl⟩

theorem commute_zM {s : mclP} (hs : s ∈ mclQ) :
    s * zM = zM * s := by
  have hgen : ∀ g ∈ permsA 275 mcl3QGens,
      g * (zM : Equiv.Perm (Fin 275)) = (zM : Equiv.Perm (Fin 275)) * g := by
    rintro _ ⟨k, hk, rfl⟩
    have hrep : Monster.B.Co2.Rep 275 mcl3QGens[k]! (permOfArr 275 mcl3QGens[k]!) :=
      rep_of_validA (enumOK_gens_valid (KFacts.K426.linesOK3_parts
        KFacts.K426.mcl3_lines_check.1).1 hk)
    exact (mul_comm_of_commN (rep_dM 0) hrep (mcl_z_spec.2 k hk)).symm
  have hle : mcl3Q ≤ Subgroup.centralizer {(zM : Equiv.Perm (Fin 275))} := by
    rw [KFacts.K426.mcl3Q, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hgen g hg)
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle hs))

theorem exists_conj_mem_mclD {s : mclP} (hs : s ∈ mclQ)
    (hs3 : s ^ 3 = 1) : ∃ t : mclP, t * s * t⁻¹ ∈ mclD ∧ t * zM * t⁻¹ ∈ mclD := by
  have hsQ : (s : Equiv.Perm (Fin 275)) ∈ mcl3Q := hs
  have hs3' : (s : Equiv.Perm (Fin 275)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hs3, Subgroup.coe_one]
  rcases KFacts.K426.mcl3_lines hsQ hs3' with h1 | ⟨j, hj, e, -, hje⟩
  · have hs1 : s = 1 := Subtype.ext (by rw [h1]; rfl)
    refine ⟨1, ?_, ?_⟩
    · rw [hs1, mul_one, one_mul]
      exact Subgroup.one_mem _
    · rw [one_mul, inv_one, mul_one]
      exact zM_mem_mclD
  have hline := allLt_spec mcl_line_check hj
  have hrepj : Monster.B.Co2.Rep 275 mcl3Lines[j]! (permOfArr 275 mcl3Lines[j]!) :=
    rep_of_validA (KFacts.K426.mcl3Lines_valid hj)
  rcases Bool.or_eq_true_iff.mp hline with hD | hQ
  ·
    obtain ⟨u, hu⟩ := eq_prodM_of_inD hrepj hD
    refine ⟨1, ?_, ?_⟩
    · have : s = prodM u ^ e := Subtype.ext (by rw [hje, hu, Subgroup.coe_pow])
      rw [this, one_mul, inv_one, mul_one]
      exact Subgroup.pow_mem _ (prodM_mem u) e
    · rw [one_mul, inv_one, mul_one]
      exact zM_mem_mclD
  ·
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at hQ
    obtain ⟨k, -, ⟨⟨hi, hqz⟩, hqs⟩⟩ := hQ
    obtain ⟨i, hi24, hqi⟩ := hi
    generalize mcl3QCert.pts[k]! = qa at hqi hqz hqs
    obtain ⟨hrq, hrqi⟩ := rep_of_mclSift hqs
    obtain ⟨qM, hqM⟩ : ∃ qM : mclP, (qM : Equiv.Perm (Fin 275)) = permOfArr 275 qa :=
      ⟨⟨_, mem_mclP_of_mclSift hqs⟩, rfl⟩
    have hconj := allLt_spec mcl_conj_check hi24
    simp only [Bool.and_eq_true] at hconj
    obtain ⟨⟨⟨hhs, hrv⟩, hhr⟩, hhz⟩ := hconj
    obtain ⟨hrh, hrhi⟩ := rep_of_mclSift hhs
    have hrr : Monster.B.Co2.Rep 275 (mclArr (4 + i)) (permOfArr 275 (mclArr (4 + i))) :=
      (rep_permOfArr hrv).1
    obtain ⟨hM, hhM⟩ : ∃ hM : mclP,
        (hM : Equiv.Perm (Fin 275)) = permOfArr 275 (mclArr (28 + i)) :=
      ⟨⟨_, mem_mclP_of_mclSift hhs⟩, rfl⟩
    have hqx : permOfArr 275 qa * permOfArr 275 mcl3Lines[j]! * (permOfArr 275 qa)⁻¹ =
        permOfArr 275 (mclArr (4 + i)) :=
      eq_of_eqA (rep_conjN hrq hrqi hrepj) hrr hqi
    have hqz' : permOfArr 275 qa * (zM : Equiv.Perm (Fin 275)) * (permOfArr 275 qa)⁻¹ =
        (zM : Equiv.Perm (Fin 275)) :=
      eq_of_eqA (rep_conjN hrq hrqi (rep_dM 0)) (rep_dM 0) hqz
    obtain ⟨u₁, hu₁⟩ := eq_prodM_of_inD (rep_conjN hrh hrhi hrr) hhr
    obtain ⟨u₂, hu₂⟩ := eq_prodM_of_inD (rep_conjN hrh hrhi (rep_dM 0)) hhz
    refine ⟨hM * qM, ?_, ?_⟩
    · have : hM * qM * s * (hM * qM)⁻¹ = prodM u₁ ^ e := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hu₁, ← hqx, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_mul, hhM, hqM, hje]
        rw [show permOfArr 275 (mclArr (28 + i)) *
            (permOfArr 275 qa * permOfArr 275 mcl3Lines[j]! * (permOfArr 275 qa)⁻¹) *
              (permOfArr 275 (mclArr (28 + i)))⁻¹ =
            permOfArr 275 (mclArr (28 + i)) * permOfArr 275 qa * permOfArr 275 mcl3Lines[j]! *
              (permOfArr 275 (mclArr (28 + i)) * permOfArr 275 qa)⁻¹ by group, conj_pow]
      rw [this]
      exact Subgroup.pow_mem _ (prodM_mem u₁) e
    · have : hM * qM * zM * (hM * qM)⁻¹ = prodM u₂ := by
        apply Subtype.ext
        rw [← hu₂, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hhM,
          hqM]
        rw [show (dM 0 : Equiv.Perm (Fin 275)) = (zM : Equiv.Perm (Fin 275)) from rfl]
        nth_rewrite 2 [← hqz']
        group
      rw [this]
      exact prodM_mem u₂

theorem exists_e81_of_e27_le_mclQ {P : Subgroup mclP}
    (hPQ : P ≤ mclQ) (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B E : Subgroup mclP, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hz : zM ∈ P
  ·
    obtain ⟨s, hsP, hsz⟩ : ∃ s ∈ P, s ∉ Subgroup.zpowers zM := by
      by_contra hall
      push Not at hall
      have hle : P ≤ Subgroup.zpowers zM := fun s hs => hall s hs
      have := Subgroup.card_le_of_le hle
      rw [hP27, Nat.card_zpowers, orderOf_eq_prime zM_cube zM_ne_one] at this
      omega
    have hs3 : s ^ 3 = 1 := hP.2 s hsP
    obtain ⟨t, hts, htz⟩ := exists_conj_mem_mclD (hPQ hsP) hs3
    set E := mclD.map (MulAut.conj t⁻¹).toMonoidHom with hE
    have hmemE : ∀ g, t * g * t⁻¹ ∈ mclD → g ∈ E := fun g hg =>
      ⟨t * g * t⁻¹, hg, by simp [mul_assoc]⟩
    have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ isElemAbelian_mclD
    refine ⟨Subgroup.closure {zM, s}, E, ?_, ?_, hEe, ?_, ?_⟩
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hz
      · exact hsP
    · rw [Asc83Table.card_closure_pair_eq_nine zM_cube hs3 (hPab _ hz _ hsP) zM_ne_one hsz]
    · rw [hE, Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective]
      exact card_mclD
    · have hBE : Subgroup.closure {zM, s} ≤ E := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact hmemE _ htz
        · exact hmemE _ hts
      intro b hb d hd
      exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨b, hBE hb⟩ ⟨d, hd⟩)
  ·
    set E := Subgroup.closure ((P : Set mclP) ∪ {zM}) with hE
    have hEe : CFSG.Assembly.IsElemAbelian 3 E := by
      refine isElemAbelian_closure_of_comm ?_ ?_
      · rintro x (hx | rfl) y (hy | rfl)
        · exact hPab x hx y hy
        · exact commute_zM (hPQ hx)
        · exact (commute_zM (hPQ hy)).symm
        · exact Commute.refl _
      · rintro x (hx | rfl)
        · exact hP.2 x hx
        · exact zM_cube
    have hPE : P ≤ E := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hzE : zM ∈ E := Subgroup.subset_closure (Or.inr rfl)
    refine ⟨P, E, le_rfl, by rw [hP27]; norm_num, hEe, ?_, ?_⟩
    · have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by
        rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hEe.2 x x.2)⟩
      obtain ⟨k, hk⟩ := hEp.exists_card_eq
      have hdvd : 27 ∣ Nat.card E := hP27 ▸ Subgroup.card_dvd_of_le hPE
      have hne : Nat.card E ≠ 27 := by
        intro h27
        have := Subgroup.eq_of_le_of_card_ge hPE (by rw [h27, hP27])
        exact hz (this ▸ hzE)
      rw [hk] at hdvd hne ⊢
      have h3k : 3 ^ 3 ∣ 3 ^ k := by simpa using hdvd
      have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3k
      have hk4 : 4 ≤ k := by
        by_contra hlt
        exact hne (by rw [show k = 3 by omega]; norm_num)
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    · intro b hb d hd
      exact congrArg Subtype.val (hEe.1.is_comm.comm ⟨b, hPE hb⟩ ⟨d, hd⟩)

theorem exists_e81_of_e27 {P : Subgroup mclP}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ B E : Subgroup mclP, B ≤ P ∧ 9 ≤ Nat.card B ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E ∧ ∀ b ∈ B, ∀ d ∈ E, b * d = d * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card card_mclQ hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP
  have hP'27 : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27]
  obtain ⟨B, E, hBP, hB9, hEe, hE81, hBE⟩ :=
    exists_e81_of_e27_le_mclQ (Item434AltPerm.map_conj_inv_le hg) hP'e hP'27
  set c := (MulAut.conj g).toMonoidHom with hc
  refine ⟨B.map c, E.map c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Item434AltPerm.map_conj_map_conj_inv P g]
    exact Subgroup.map_mono hBP
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hB9
  · exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hEe
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE81
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul, hBE b hb d hd]

end Item434SporGen

section Families


theorem item434Spor_McL_27 :
    Item434Spor_McL_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b₀ : NativeSporadic.McL ≃* Spor .McL := b
  have eP : NativeSporadic.McL ≃* mclP := CFSG.Sporadic.Schreier.mclPermEquiv
  have e : layer G ⧸ Subgroup.center (layer G) ≃* mclP := e₀.trans (b₀.symm.trans eP)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hc.isQuasisimple.2.1
  have : IsSimpleGroup mclP := e.symm.isSimpleGroup
  have hcen : Subgroup.center mclP = ⊥ :=
    center_eq_bot_of_simple (by rw [CFSG.Sporadic.Schreier.card_mclP]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer mclP) :=
    not_three_dvd_card_outer_of_le_two CFSG.Sporadic.SmallOddCore.mcl_outer_card_le
  have h27' : Nat.card (A.map (quotConj e)) = 27 := by rw [card_map_quotConj hc e]; exact h27
  set P := (A.map (quotConj e)).comap (MulAut.conj : mclP →* MulAut mclP) with hPdef
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := map_comap_conj_eq hc e hout
  have hinj := conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h27']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    isElemAbelian_of_map_injective hinj (hPmap ▸ isElemAbelian_map_quotConj hc e)
  obtain ⟨B, E, hBP, hB9, hEe, hE81, hBE⟩ := Item434SporGen.exists_e81_of_e27 hPe hP27
  exact (Item434SporGen.false_of_e81 hc hZ e hcen hPmap hBP hB9 hEe hE81 hBE).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
