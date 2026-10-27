module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowU4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4OddDiag
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHBlock
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofU4Cent
public import CFSG.RankThree.PartOne.KFOUT3.L12Levi
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofU4Inner
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof (uS)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (dvecD0)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (dvecC)
open CFSG.RankThree.PartOne.KFU (diagU diagU_one torusSU mem_torusSU_iff permGL permGL_conj_diagU
  permGL_mem_unitarySU exists_diag_iso_le_of_iso)

section Product

noncomputable def equivOfSndBij {X Y : Type} [Group X] [Group Y] {H : Subgroup (X × Y)}
    (hinj : ∀ h ∈ H, ∀ h' ∈ H, h.2 = h'.2 → h = h')
    (hsurj : ∀ y : Y, ∃ h ∈ H, h.2 = y) : H ≃* Y :=
  MulEquiv.ofBijective ((MonoidHom.snd X Y).comp H.subtype)
    ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab), fun y => by
      obtain ⟨h, hh, rfl⟩ := hsurj y
      exact ⟨⟨h, hh⟩, rfl⟩⟩

noncomputable def equivOfFstBij {X Y : Type} [Group X] [Group Y] {H : Subgroup (X × Y)}
    (hinj : ∀ h ∈ H, ∀ h' ∈ H, h.1 = h'.1 → h = h')
    (hsurj : ∀ x : X, ∃ h ∈ H, h.1 = x) : H ≃* X :=
  MulEquiv.ofBijective ((MonoidHom.fst X Y).comp H.subtype)
    ⟨fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab), fun x => by
      obtain ⟨h, hh, rfl⟩ := hsurj x
      exact ⟨⟨h, hh⟩, rfl⟩⟩

theorem goursat_prod {X Y : Type} [Group X] [Group Y] (hX : IsSimpleGroup X)
    (hY : IsSimpleGroup Y) {H : Subgroup (X × Y)} (hs : H.IsSubnormal) (hne : H ≠ ⊥) :
    H = ⊤ ∨ Nonempty (H ≃* X) ∨ Nonempty (H ≃* Y) := by
  have hsX : (H.map (MonoidHom.fst X Y)).IsSubnormal :=
    Subgroup.IsSubnormal.map (show Function.Surjective (MonoidHom.fst X Y) from fun x => ⟨(x, 1), rfl⟩) hs
  have hsY : (H.map (MonoidHom.snd X Y)).IsSubnormal :=
    Subgroup.IsSubnormal.map (show Function.Surjective (MonoidHom.snd X Y) from fun y => ⟨(1, y), rfl⟩) hs
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hX hsX with hPX | hPX <;>
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hY hsY with hPY | hPY
  ·
    exfalso
    apply hne
    rw [eq_bot_iff]
    intro h hh
    have h1 : h.1 = 1 := by
      have hm : (MonoidHom.fst X Y) h ∈ H.map (MonoidHom.fst X Y) := Subgroup.mem_map_of_mem _ hh
      rw [hPX, Subgroup.mem_bot] at hm
      exact hm
    have h2 : h.2 = 1 := by
      have hm : (MonoidHom.snd X Y) h ∈ H.map (MonoidHom.snd X Y) := Subgroup.mem_map_of_mem _ hh
      rw [hPY, Subgroup.mem_bot] at hm
      exact hm
    exact Subgroup.mem_bot.mpr (Prod.ext h1 h2)
  ·
    refine Or.inr (Or.inr ⟨equivOfSndBij (fun h hh h' hh' hs' => ?_) ?_⟩)
    · have e1 : h.1 = 1 := by
        have hm : (MonoidHom.fst X Y) h ∈ H.map (MonoidHom.fst X Y) :=
          Subgroup.mem_map_of_mem _ hh
        rw [hPX, Subgroup.mem_bot] at hm
        exact hm
      have e2 : h'.1 = 1 := by
        have hm : (MonoidHom.fst X Y) h' ∈ H.map (MonoidHom.fst X Y) :=
          Subgroup.mem_map_of_mem _ hh'
        rw [hPX, Subgroup.mem_bot] at hm
        exact hm
      exact Prod.ext (e1.trans e2.symm) hs'
    · intro y
      have hm : y ∈ H.map (MonoidHom.snd X Y) := by rw [hPY]; exact Subgroup.mem_top y
      obtain ⟨h, hh, hy⟩ := Subgroup.mem_map.mp hm
      exact ⟨h, hh, hy⟩
  ·
    refine Or.inr (Or.inl ⟨equivOfFstBij (fun h hh h' hh' hf' => ?_) ?_⟩)
    · have e1 : h.2 = 1 := by
        have hm : (MonoidHom.snd X Y) h ∈ H.map (MonoidHom.snd X Y) :=
          Subgroup.mem_map_of_mem _ hh
        rw [hPY, Subgroup.mem_bot] at hm
        exact hm
      have e2 : h'.2 = 1 := by
        have hm : (MonoidHom.snd X Y) h' ∈ H.map (MonoidHom.snd X Y) :=
          Subgroup.mem_map_of_mem _ hh'
        rw [hPY, Subgroup.mem_bot] at hm
        exact hm
      exact Prod.ext hf' (e1.trans e2.symm)
    · intro x
      have hm : x ∈ H.map (MonoidHom.fst X Y) := by rw [hPX]; exact Subgroup.mem_top x
      obtain ⟨h, hh, hx⟩ := Subgroup.mem_map.mp hm
      exact ⟨h, hh, hx⟩
  ·
    set A : Subgroup X := H.comap (MonoidHom.inl X Y) with hA
    set B : Subgroup Y := H.comap (MonoidHom.inr X Y) with hB
    have hmemA : ∀ x : X, x ∈ A ↔ ((x, 1) : X × Y) ∈ H := fun x => Iff.rfl
    have hmemB : ∀ y : Y, y ∈ B ↔ ((1, y) : X × Y) ∈ H := fun y => Iff.rfl
    by_cases hA0 : A = ⊥
    ·
      refine Or.inr (Or.inr ⟨equivOfSndBij (fun h hh h' hh' hs' => ?_) ?_⟩)
      · have hq : h * h'⁻¹ ∈ H := H.mul_mem hh (H.inv_mem hh')
        have hq1 : (h * h'⁻¹).2 = 1 := by
          simp [hs']
        have hq2 : ((h * h'⁻¹).1, (1 : Y)) ∈ H := by
          have e : ((h * h'⁻¹).1, (1 : Y)) = h * h'⁻¹ := Prod.ext rfl hq1.symm
          rw [e]
          exact hq
        have hx : (h * h'⁻¹).1 ∈ A := (hmemA _).mpr hq2
        rw [hA0, Subgroup.mem_bot] at hx
        have : h * h'⁻¹ = 1 := Prod.ext hx hq1
        exact mul_inv_eq_one.mp this
      · intro y
        have hm : y ∈ H.map (MonoidHom.snd X Y) := by rw [hPY]; exact Subgroup.mem_top y
        obtain ⟨h, hh, hy⟩ := Subgroup.mem_map.mp hm
        exact ⟨h, hh, hy⟩
    by_cases hB0 : B = ⊥
    ·
      refine Or.inr (Or.inl ⟨equivOfFstBij (fun h hh h' hh' hf' => ?_) ?_⟩)
      · have hq : h * h'⁻¹ ∈ H := H.mul_mem hh (H.inv_mem hh')
        have hq1 : (h * h'⁻¹).1 = 1 := by
          simp [hf']
        have hq2 : ((1 : X), (h * h'⁻¹).2) ∈ H := by
          have e : ((1 : X), (h * h'⁻¹).2) = h * h'⁻¹ := Prod.ext hq1.symm rfl
          rw [e]
          exact hq
        have hy : (h * h'⁻¹).2 ∈ B := (hmemB _).mpr hq2
        rw [hB0, Subgroup.mem_bot] at hy
        have : h * h'⁻¹ = 1 := Prod.ext hq1 hy
        exact mul_inv_eq_one.mp this
      · intro x
        have hm : x ∈ H.map (MonoidHom.fst X Y) := by rw [hPX]; exact Subgroup.mem_top x
        obtain ⟨h, hh, hx⟩ := Subgroup.mem_map.mp hm
        exact ⟨h, hh, hx⟩
    ·
      have hAn : A.Normal := by
        constructor
        intro a ha g
        obtain ⟨h, hh, hg⟩ := Subgroup.mem_map.mp
          (show g ∈ H.map (MonoidHom.fst X Y) by rw [hPX]; exact Subgroup.mem_top g)
        have hc : h * ((a, 1) : X × Y) * h⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem hh ((hmemA a).mp ha)) (H.inv_mem hh)
        have hc' : (g * a * g⁻¹, (1 : Y)) ∈ H := by
          convert hc using 1
          ext
          · simp [← hg]
          · simp [hh]
        exact (hmemA _).mpr hc'
      have hBn : B.Normal := by
        constructor
        intro b hb g
        obtain ⟨h, hh, hg⟩ := Subgroup.mem_map.mp
          (show g ∈ H.map (MonoidHom.snd X Y) by rw [hPY]; exact Subgroup.mem_top g)
        have hc : h * ((1, b) : X × Y) * h⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem hh ((hmemB b).mp hb)) (H.inv_mem hh)
        have hc' : ((1 : X), g * b * g⁻¹) ∈ H := by
          convert hc using 1
          ext
          · simp [hh]
          · simp [← hg]
        exact (hmemB _).mpr hc'
      have hAt : A = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal A).resolve_left hA0
      have hBt : B = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal B).resolve_left hB0
      left
      rw [eq_top_iff]
      rintro ⟨x, y⟩ -
      have h1 : ((x, 1) : X × Y) ∈ H := (hmemA x).mp (by rw [hAt]; exact Subgroup.mem_top x)
      have h2 : ((1, y) : X × Y) ∈ H := (hmemB y).mp (by rw [hBt]; exact Subgroup.mem_top y)
      have := H.mul_mem h1 h2
      simpa using this

theorem not_noCommNormalPair3_prod {X Y : Type} [Group X] [Group Y] {a : X} (ha : orderOf a = 3)
    {b : Y} (hb : orderOf b = 3) : ¬ NoCommNormalPair3 (X × Y) := by
  intro h
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha
    norm_num at ha
  have hb1 : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hb
    norm_num at hb
  refine h (MonoidHom.ker (MonoidHom.snd X Y)) (MonoidHom.ker (MonoidHom.fst X Y)) inferInstance
    inferInstance ?_ (a, 1) (MonoidHom.mem_ker.mpr rfl) ?_ ?_ (1, b)
    (MonoidHom.mem_ker.mpr rfl) ?_ ?_
  · intro u hu v hv
    have hu2 : u.2 = 1 := MonoidHom.mem_ker.mp hu
    have hv1 : v.1 = 1 := MonoidHom.mem_ker.mp hv
    exact Prod.ext (by simp [hv1]) (by simp [hu2])
  · intro h1
    exact ha1 (congrArg Prod.fst h1)
  · simp [ha3]
  · intro h1
    exact hb1 (congrArg Prod.snd h1)
  · simp [hb3]

end Product

section Simple

theorem isSimpleGroup_of_isQuasisimple_center {Q : Type} [Group Q] (hQ : IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) : IsSimpleGroup Q := by
  haveI := hQ.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isSimpleGroup_of_isTypeEps {X : Type} [Group X] (h : IsTypeEps X) : IsSimpleGroup X := by
  obtain ⟨p, f, hp, -, hf, ⟨-, ⟨ψ⟩⟩ | ⟨-, hq2, ⟨ψ⟩⟩⟩ := h
  · haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField p f) (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact ψ.isSimpleGroup
  · haveI := CFSG.PGLModel.isSimpleGroup_projSU_of_admissible (n := 3) (p := p) (f := f)
      ⟨Fact.out, hf, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega⟩
    exact ψ.isSimpleGroup

theorem false_of_simple_isTypeEpsCube {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hc : IsTypeEpsCube (K ⧸ CFSG.pCore 2 K)) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
  have hcard := le_card_of_isTypeEpsCube hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 K) with hb | ht
  · have e : (K ⧸ CFSG.pCore 2 K) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
    exact not_isTypeEpsCube_of_card_sl2_even hn hK (isTypeEpsCube_of_mulEquiv e.symm hc)
  · have : Subsingleton (K ⧸ CFSG.pCore 2 K) := by
      rw [ht]
      exact QuotientGroup.subsingleton_quotient_top
    have : Nat.card (K ⧸ CFSG.pCore 2 K) = 1 := Nat.card_unique
    omega

end Simple

section Blocks

open CFSG.RankThree.PartOne.KFU (diagU diagU_val apply_eq_zero_of_commute_diagU)
open CFSG.RankThree.PartTwo.Sec21.Item2130Res4Proof (blk3SU blk3SUEquiv mem_blk3SU_of
  blk3SU_le_uS blk3SU_le_centralizer mem_blk3SU_diagonal pattern_of_commute statedSU_eq_uS)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blkGL2 coe_blkGL2 blkSU2 dvecD0
  blkSU2_le_centralizer nonempty_blkSU2_mulEquiv mem_blkSU2_of)
open CFSG.RankThree.PartTwo.Sec4.Item419Res3 (blk2L blkGL2L coe_blkGL2L blkSU2L dvecC centC
  blockUp blockLow blkSU2_le_centC blkSU2L_le_centC commutator_centC_le
  nonempty_blkSU2L_mulEquiv sl2_block_facts ker_blockLow ker_blockUp)

variable {L : Type} [Field L]

theorem u4OddEps_coe_diagU (d : Fin 4 → Lˣ) :
    ((diagU d : GL (Fin 4) L) : Matrix (Fin 4) (Fin 4) L) = Matrix.diagonal fun i => (d i : L) :=
  diagU_val d

theorem u4OddEps_mul_eq_of_mem_centralizer {g D : GL (Fin 4) L} (hg : g ∈ Subgroup.centralizer {D}) :
    (g : Matrix (Fin 4) (Fin 4) L) * (D : Matrix (Fin 4) (Fin 4) L) =
      (D : Matrix (Fin 4) (Fin 4) L) * (g : Matrix (Fin 4) (Fin 4) L) := by
  have := congrArg (fun x : GL (Fin 4) L => (x : Matrix (Fin 4) (Fin 4) L))
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simpa only [Units.val_mul] using this

theorem u4OddEps_mem_uS_of_unitarySU {n : ℕ} (h : UnitaryFieldData 2 n L) {k : GL (Fin 4) L}
    (hk : k ∈ unitarySU 2 n L 4) : k ∈ uS h 4 := by
  rw [unitarySU_eq_gramSU h 4] at hk
  exact hk

theorem u4OddEps_mem_unitarySU_of_uS {n : ℕ} (h : UnitaryFieldData 2 n L) {k : GL (Fin 4) L}
    (hk : k ∈ uS h 4) : k ∈ unitarySU 2 n L 4 := by
  rw [unitarySU_eq_gramSU h 4]
  exact hk

theorem u4OddEps_entry33_eq_one {ω : Lˣ} (hω1 : ω ≠ 1) {K₂ : Subgroup (GL (Fin 4) L)}
    (hC : K₂ ≤ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}) (hKp : ⁅K₂, K₂⁆ = K₂) {k : GL (Fin 4) L}
    (hk : k ∈ K₂) : (k : Matrix (Fin 4) (Fin 4) L) 3 3 = 1 := by
  refine entry_eq_one_of_perfect (v := ![ω, ω, ω, 1]) (l := 3) ?_ hC hKp hk
  intro j hj
  fin_cases j
  · simpa using (Ne.symm hω1)
  · simpa using (Ne.symm hω1)
  · simpa using (Ne.symm hω1)
  · exact absurd rfl hj


theorem u4OddEps_caseA {n : ℕ} (h : UnitaryFieldData 2 n L) (hn : 2 ≤ n) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hωbar : h.bar (ω : L) * (ω : L) = 1)
    {K₂ : Subgroup (GL (Fin 4) L)} (hU : K₂ ≤ unitarySU 2 n L 4)
    (hC : K₂ ≤ Subgroup.centralizer {diagU ![ω, ω, ω, 1]}) (hKp : ⁅K₂, K₂⁆ = K₂)
    (hs : (K₂.subgroupOf (unitarySU 2 n L 4 ⊓
      Subgroup.centralizer {diagU ![ω, ω, ω, 1]})).IsSubnormal)
    (hnt : K₂ ≠ ⊥) (hT : IsTypeEps (K₂ ⧸ CFSG.pCore 2 K₂)) : False := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K₂ := Subgroup.isPerfect_iff.mpr hKp
  haveI : Nontrivial K₂ := (Subgroup.nontrivial_iff_ne_bot K₂).mpr hnt
  have hωL3 : (ω : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hωL1 : (ω : L) ≠ 1 := fun e => hω1 (Units.ext e)
  set D : GL (Fin 4) L := diagU ![ω, ω, ω, 1] with hDdef
  have hDm : (D : Matrix (Fin 4) (Fin 4) L) =
      Matrix.diagonal ![(ω : L), (ω : L), (ω : L), 1] := by
    rw [hDdef, u4OddEps_coe_diagU]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hBC : blk3SU h ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {D} :=
    le_inf (fun g hg => u4OddEps_mem_unitarySU_of_uS h (blk3SU_le_uS h hg))
      (blk3SU_le_centralizer h hDm)
  have hK₂B : K₂ ≤ blk3SU h := by
    intro k hk
    have hkC := u4OddEps_mul_eq_of_mem_centralizer (hC hk)
    rw [hDm] at hkC
    exact mem_blk3SU_of h (u4OddEps_mem_uS_of_unitarySU h (hU hk)) (pattern_of_commute hωL1 hkC)
      (u4OddEps_entry33_eq_one hω1 hC hKp hk)
  have hsB : (K₂.subgroupOf (blk3SU h)).IsSubnormal :=
    RonanK429H.isSubnormal_subgroupOf_of_le hBC hK₂B hs
  have hq3 : IsQuasisimple (blk3SU h) := by
    have hq := CFSG.RankThree.PartOne.KFOUT3.isQuasisimple_unitarySU_three h hn
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr (statedSU_eq_uS h 3)).trans (blk3SUEquiv h).symm) hq
  have hKeq : K₂ = blk3SU h :=
    Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hK₂B hq3 hperf inferInstance hsB
  have hDK : D ∈ K₂ := by
    rw [hKeq]
    exact mem_blk3SU_diagonal h hωL3 hωbar hDm
  have hDc : ∀ k ∈ K₂, k * D = D * k := by
    intro k hk
    rw [hKeq] at hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (blk3SU_le_centralizer h hDm hk)
  set z : K₂ := ⟨D, hDK⟩ with hz
  have hzc : ∀ k : K₂, z * k = k * z := fun k => Subtype.ext (hDc k k.2).symm
  have hD3 : D ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hDm, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [Pi.pow_apply, hωL3]
  have hD1 : D ≠ 1 := by
    intro e
    apply hωL1
    have := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L) 0 0) e
    simpa [hDm] using this
  have hord : orderOf z = 3 := by
    rw [hz, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hD3 hD1
  have hcen : (QuotientGroup.mk' (CFSG.pCore 2 K₂) z : K₂ ⧸ CFSG.pCore 2 K₂) ∈
      Subgroup.center (K₂ ⧸ CFSG.pCore 2 K₂) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K₂) q
    rw [← map_mul, ← map_mul, hzc k']
  rw [center_eq_bot_of_isTypeEps hT, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcen
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K₂)) ⟨_, hcen⟩
  have hm' : z ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hd : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  rw [hord] at hd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)) hd

theorem u4OddEps_caseB {n : ℕ} (h : UnitaryFieldData 2 n L) (hn : 2 ≤ n) {ω : Lˣ} (hω1 : ω ≠ 1)
    (hω2 : ω ≠ ω⁻¹) {K₂ : Subgroup (GL (Fin 4) L)} (hU : K₂ ≤ unitarySU 2 n L 4)
    (hC : K₂ ≤ Subgroup.centralizer {diagU (dvecD0 ω)}) (hKp : ⁅K₂, K₂⁆ = K₂)
    (hs : (K₂.subgroupOf (unitarySU 2 n L 4 ⊓
      Subgroup.centralizer {diagU (dvecD0 ω)})).IsSubnormal)
    (hnt : K₂ ≠ ⊥) (hTc : IsTypeEpsCube (K₂ ⧸ CFSG.pCore 2 K₂)) : False := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hω1' : ω⁻¹ ≠ 1 := fun e => hω1 (inv_eq_one.mp e)
  have hl2 : ∀ j : Fin 4, j ≠ 2 → dvecD0 ω 2 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using hω1
    · simpa [dvecD0] using hω1
    · exact absurd rfl hj
    · simpa [dvecD0] using hω2
  have hl3 : ∀ j : Fin 4, j ≠ 3 → dvecD0 ω 3 ≠ dvecD0 ω j := by
    intro j hj
    fin_cases j
    · simpa [dvecD0] using Ne.symm hω1'
    · simpa [dvecD0] using Ne.symm hω1'
    · simpa [dvecD0] using hω2.symm
    · exact absurd rfl hj
  have hK22 : ∀ k ∈ K₂, (k : Matrix (Fin 4) (Fin 4) L) 2 2 = 1 := fun k hk =>
    entry_eq_one_of_perfect hl2 hC hKp hk
  have hK33 : ∀ k ∈ K₂, (k : Matrix (Fin 4) (Fin 4) L) 3 3 = 1 := fun k hk =>
    entry_eq_one_of_perfect hl3 hC hKp hk
  have hBC : blkSU2 n L ≤ unitarySU 2 n L 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} :=
    blkSU2_le_centralizer h ω
  have e01 : dvecD0 ω 0 ≠ dvecD0 ω 2 := by simpa [dvecD0] using Ne.symm hω1
  have e03 : dvecD0 ω 0 ≠ dvecD0 ω 3 := by simpa [dvecD0] using Ne.symm hω1'
  have e12 : dvecD0 ω 1 ≠ dvecD0 ω 2 := by simpa [dvecD0] using Ne.symm hω1
  have e13 : dvecD0 ω 1 ≠ dvecD0 ω 3 := by simpa [dvecD0] using Ne.symm hω1'
  have e20 : dvecD0 ω 2 ≠ dvecD0 ω 0 := by simpa [dvecD0] using hω1
  have e21 : dvecD0 ω 2 ≠ dvecD0 ω 1 := by simpa [dvecD0] using hω1
  have e23 : dvecD0 ω 2 ≠ dvecD0 ω 3 := by simpa [dvecD0] using hω2
  have e30 : dvecD0 ω 3 ≠ dvecD0 ω 0 := by simpa [dvecD0] using hω1'
  have e31 : dvecD0 ω 3 ≠ dvecD0 ω 1 := by simpa [dvecD0] using hω1'
  have e32 : dvecD0 ω 3 ≠ dvecD0 ω 2 := by simpa [dvecD0] using hω2.symm
  have hK₂N : K₂ ≤ blkSU2 n L := by
    intro k hk
    have hz : ∀ i j : Fin 4, dvecD0 ω i ≠ dvecD0 ω j →
        (k : Matrix (Fin 4) (Fin 4) L) i j = 0 := fun i j hij =>
      apply_eq_zero_of_commute_diagU (Subgroup.mem_centralizer_singleton_iff.mp (hC hk)) hij
    exact mem_blkSU2_of h (hU hk) (hz 0 2 e01) (hz 0 3 e03) (hz 1 2 e12) (hz 1 3 e13)
      (hz 2 0 e20) (hz 2 1 e21) (hz 2 3 e23) (hz 3 0 e30) (hz 3 1 e31) (hz 3 2 e32)
      (hK22 k hk) (hK33 k hk)
  have hsB := hs
  obtain ⟨hq, hcard⟩ := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hn
  have hZ : Subgroup.center (blkSU2 n L) = ⊥ := by
    haveI : CharP h.fixedField 2 :=
      CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq h.card_fixedField
    obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
    exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
  haveI hN₁ : IsSimpleGroup (blkSU2 n L) := isSimpleGroup_of_isQuasisimple_center hq hZ
  have hK : K₂ = blkSU2 n L :=
    eq_of_subnormal_of_le_simple hK₂N hBC hsB hN₁ hnt
  have hKs : IsSimpleGroup K₂ := (MulEquiv.subgroupCongr hK).isSimpleGroup
  exact false_of_simple_isTypeEpsCube (n := n) hKs hTc (by omega)
    (by rw [Nat.card_congr (MulEquiv.subgroupCongr hK).toEquiv, hcard])

theorem u4OddEps_caseC {n : ℕ} (h : UnitaryFieldData 2 n L) (hn : 2 ≤ n) {ω : Lˣ} (hω1 : ω ≠ 1)
    (hω2 : ω ≠ ω⁻¹) {K₂ : Subgroup (GL (Fin 4) L)} (hU : K₂ ≤ unitarySU 2 n L 4)
    (hC : K₂ ≤ centC n L ω) (hKp : ⁅K₂, K₂⁆ = K₂)
    (hs : (K₂.subgroupOf (centC n L ω)).IsSubnormal) (hnt : K₂ ≠ ⊥)
    (hT : IsTypeEps (K₂ ⧸ CFSG.pCore 2 K₂)) (hTc : IsTypeEpsCube (K₂ ⧸ CFSG.pCore 2 K₂)) :
    False := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K₂ := Subgroup.isPerfect_iff.mpr hKp
  haveI : CharP h.fixedField 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq h.card_fixedField
  have hM : blkSU2 n L ⊔ blkSU2L n L ≤ centC n L ω :=
    sup_le (blkSU2_le_centC h ω) (blkSU2L_le_centC h ω)
  have hK₂M : K₂ ≤ blkSU2 n L ⊔ blkSU2L n L := by
    calc K₂ = ⁅K₂, K₂⁆ := hKp.symm
      _ ≤ ⁅centC n L ω, centC n L ω⁆ := Subgroup.commutator_mono hC hC
      _ ≤ blkSU2 n L ⊔ blkSU2L n L := commutator_centC_le h hω2
  have hs' : (K₂.subgroupOf (blkSU2 n L ⊔ blkSU2L n L)).IsSubnormal :=
    RonanK429H.isSubnormal_subgroupOf_of_le hM hK₂M hs
  have hcomm : ∀ a ∈ blkSU2 n L, ∀ b ∈ blkSU2L n L, a * b = b * a := by
    intro a ha b hb
    obtain ⟨X, -, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨Y, -, rfl⟩ := Subgroup.mem_map.mp hb
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_blkGL2, coe_blkGL2L]
    exact RonanK429Lie.blk2_mul_blk2L_comm _ _
  have hdisj : Disjoint (blkSU2 n L) (blkSU2L n L) := by
    rw [Subgroup.disjoint_def]
    intro g hg1 hg2
    obtain ⟨X, -, rfl⟩ := Subgroup.mem_map.mp hg1
    obtain ⟨Y, -, hY⟩ := Subgroup.mem_map.mp hg2
    have e := congrArg (fun g : GL (Fin 4) L => (g : Matrix (Fin 4) (Fin 4) L)) hY
    simp only [coe_blkGL2, coe_blkGL2L] at e
    have e00 : (X : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 0) 0).symm
    have e01 : (X : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 0) 1).symm
    have e10 : (X : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 1) 0).symm
    have e11 : (X : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by
      simpa [blk2, blk2L] using (congrFun (congrFun e 1) 1).symm
    have hX : X = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]
    rw [hX, map_one]
  have hcommΦ : ∀ (a : ↥(blkSU2 n L)) (b : ↥(blkSU2L n L)),
      Commute ((blkSU2 n L).subtype a) ((blkSU2L n L).subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set Φ : ↥(blkSU2 n L) × ↥(blkSU2L n L) →* GL (Fin 4) L :=
    (blkSU2 n L).subtype.noncommCoprod (blkSU2L n L).subtype hcommΦ with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [hΦ, MonoidHom.noncommCoprod_injective]
    refine ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hdisj
  have hΦrange : Φ.range = blkSU2 n L ⊔ blkSU2L n L := by
    rw [hΦ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hK₂range : K₂ ≤ Φ.range := by
    rw [hΦrange]
    exact hK₂M
  have hmapK : (K₂.comap Φ).map Φ = K₂ := Subgroup.map_comap_eq_self hK₂range
  set H : Subgroup (↥(blkSU2 n L) × ↥(blkSU2L n L)) := K₂.comap Φ with hH
  have hHs : H.IsSubnormal := by
    have h1 : (K₂.subgroupOf Φ.range).IsSubnormal := by
      rw [hΦrange]
      exact hs'
    have h2 := Subgroup.IsSubnormal.comap Φ.rangeRestrict h1
    have e : H = (K₂.subgroupOf Φ.range).comap Φ.rangeRestrict := by
      ext x
      simp [hH, Subgroup.mem_subgroupOf]
    rw [e]
    exact h2
  have hHne : H ≠ ⊥ := by
    intro hb
    apply hnt
    rw [← hmapK, hb, Subgroup.map_bot]
  obtain ⟨hqN₁, hcardN₁⟩ := (sl2_block_facts h (nonempty_blkSU2_mulEquiv h)).1 hn
  obtain ⟨hqN₂, hcardN₂⟩ := (sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)).1 hn
  have hZ₁ : Subgroup.center (blkSU2 n L) = ⊥ := by
    obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
    exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
  have hZ₂ : Subgroup.center (blkSU2L n L) = ⊥ := by
    obtain ⟨φ⟩ := nonempty_blkSU2L_mulEquiv h
    exact center_eq_bot_of_mulEquiv φ Sec19.Item19Res2Proof.center_sl2_eq_bot
  haveI hX : IsSimpleGroup (blkSU2 n L) := isSimpleGroup_of_isQuasisimple_center hqN₁ hZ₁
  haveI hY : IsSimpleGroup (blkSU2L n L) := isSimpleGroup_of_isQuasisimple_center hqN₂ hZ₂
  rcases goursat_prod hX hY hHs hHne with hTop | hXH | hYH
  ·
    have eK : K₂ ≃* (↥(blkSU2 n L) × ↥(blkSU2L n L)) :=
      ((Subgroup.equivMapOfInjective H Φ hΦinj).trans (MulEquiv.subgroupCongr hmapK)).symm.trans
        ((MulEquiv.subgroupCongr hTop).trans Subgroup.topEquiv)
    have hNC : NoCommNormalPair3 K₂ :=
      noCommNormalPair3_of_simple (isSimpleGroup_of_isTypeEps hT)
    have hNC' := noCommNormalPair3_of_mulEquiv eK hNC
    have h3 : 3 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Dvd.dvd.mul_left (Res419Two.three_dvd_two_pow_sq_sub_one n) _
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(blkSU2 n L)) 3
      (by rw [hcardN₁]; exact h3)
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(blkSU2L n L)) 3
      (by rw [hcardN₂]; exact h3)
    exact not_noCommNormalPair3_prod ha hb hNC'
  ·
    obtain ⟨eX⟩ := hXH
    have eK : K₂ ≃* ↥(blkSU2 n L) :=
      (((Subgroup.equivMapOfInjective H Φ hΦinj).trans (MulEquiv.subgroupCongr hmapK)).symm).trans
        eX
    haveI : IsSimpleGroup K₂ := eK.isSimpleGroup
    exact false_of_simple_isTypeEpsCube (n := n) inferInstance hTc (by omega)
      (by rw [Nat.card_congr eK.toEquiv, hcardN₁])
  ·
    obtain ⟨eY⟩ := hYH
    have eK : K₂ ≃* ↥(blkSU2L n L) :=
      (((Subgroup.equivMapOfInjective H Φ hΦinj).trans (MulEquiv.subgroupCongr hmapK)).symm).trans
        eY
    haveI : IsSimpleGroup K₂ := eK.isSimpleGroup
    exact false_of_simple_isTypeEpsCube (n := n) inferInstance hTc (by omega)
      (by rw [Nat.card_congr eK.toEquiv, hcardN₂])

end Blocks

theorem u4OddInnerEps : U4OddInnerEps := by
  intro n hodd S _ _ hS σ hin hσ3 hσ1 K hKfix hKperf hsub hT hTc
  obtain ⟨eS⟩ := hS
  haveI := hKperf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hodd.pos
  rcases Nat.eq_or_lt_of_le hn1 with rfl | hn2
  ·
    exfalso
    have hU1 : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
      ⟨Nat.prime_two, le_rfl, GaloisField.card 2 (2 * 1) (by norm_num)⟩
    have hcardS : Nat.card S = 25920 := by
      rw [Nat.card_congr eS.toEquiv,
        Nat.card_congr (Res417Six.unitarySUEquivProjSU le_rfl).symm.toEquiv,
        Item419Res3.card_unitarySU_four hU1]
      norm_num
    have h1 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card S :=
      (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K)
    have h2 := Nat.le_of_dvd Nat.card_pos h1
    have h3 := le_card_of_isTypeEpsCube hTc
    omega
  have hn2' : 2 ≤ n := by omega
  obtain ⟨x, rfl⟩ := hin
  have hZ : Subgroup.center S = ⊥ :=
    center_eq_bot_of_mulEquiv eS (Sec4.RonanK432.center_projSU_four_two_eq_bot hn1)
  have hx3 : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hσ3
    have hc : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut S => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [h2]
        _ = x ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hσ1 (map_one _)
  have hxK : ∀ k ∈ K, x * k = k * x := by
    intro k hk
    have h1 : MulAut.conj x k = k := Sec4.mem_autFix.mp (hKfix hk)
    rw [MulAut.conj_apply] at h1
    calc x * k = x * k * x⁻¹ * x := by group
      _ = k * x := by rw [h1]
  have hxi3 : ∀ i : ℤ, (x ^ i) ^ 3 = 1 := by
    intro i
    calc (x ^ i) ^ 3 = (x ^ i) ^ ((3 : ℕ) : ℤ) := (zpow_natCast _ 3).symm
      _ = x ^ (i * 3) := (_root_.zpow_mul x i 3).symm
      _ = x ^ (3 * i) := congrArg (x ^ ·) (mul_comm i 3)
      _ = (x ^ (3 : ℤ)) ^ i := _root_.zpow_mul x 3 i
      _ = 1 := by
        rw [show x ^ (3 : ℤ) = 1 from (zpow_natCast x 3).trans hx3, _root_.one_zpow]
  set Lf := GaloisField 2 (2 * n) with hLf
  have hU : UnitaryFieldData 2 n Lf :=
    ⟨Nat.prime_two, hn1, GaloisField.card 2 (2 * n) (by omega)⟩
  have := hU.finite
  have h3 : 3 ∣ 2 ^ n + 1 := Res417Six.three_dvd_two_pow_add_one hodd
  have hFexp : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hxi3 i
  have hFcomm : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow_self x i j).eq
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU Nat.prime_three h3
    ((Res417Six.unitarySUEquivProjSU hn1).trans eS.symm) (Subgroup.zpowers x) hFexp hFcomm
  have hFT : ∀ y ∈ Subgroup.zpowers x,
      ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) ∈ torusSU 3 4 Lf :=
    fun y hy => hψ _ (by rw [MulEquiv.apply_symm_apply]; exact hy)
  obtain ⟨v, hv3, hvp, hvx⟩ := mem_torusSU_iff.mp (hFT x (Subgroup.mem_zpowers x))
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : ψ.symm x = 1 := Subtype.ext (by rw [← hvx, diagU_one]; rfl)
    rw [← ψ.apply_symm_apply x, h1, map_one]
  have hdvd : 3 ∣ Nat.card Lf - 1 := by
    rw [hU.card]
    have h4 := Res419Two.three_dvd_two_pow_sq_sub_one n
    rwa [← pow_mul, mul_comm] at h4
  obtain ⟨ζ, hζ⟩ := Res417Six.exists_primitiveRoot_three hdvd
  obtain ⟨π, ω, hω3, hω1, hnf⟩ := Item419Res3.exists_perm_normal_form hζ hv3 hvp hv1
  have hω2 : ω ≠ ω⁻¹ := by
    intro hh
    apply hω1
    have h2' : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hh]; exact mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2', inv_one, one_mul]
  set P : GL (Fin 4) Lf := permGL π with hP
  have hPU : P ∈ unitarySU 2 n Lf 4 := permGL_mem_unitarySU hU π
  set ρ : S →* GL (Fin 4) Lf := (MulAut.conj P).toMonoidHom.comp
    ((unitarySU 2 n Lf 4).subtype.comp ψ.symm.toMonoidHom) with hρ
  have hρapp : ∀ y, ρ y = P * ((ψ.symm y : unitarySU 2 n Lf 4) : GL (Fin 4) Lf) * P⁻¹ :=
    fun y => rfl
  have hρinj : Function.Injective ρ := by
    intro y z h'
    rw [hρapp, hρapp] at h'
    exact ψ.symm.injective (Subtype.ext (mul_left_cancel (mul_right_cancel h')))
  have hρU : ∀ y, ρ y ∈ unitarySU 2 n Lf 4 := fun y =>
    mul_mem (mul_mem hPU (ψ.symm y).2) (inv_mem hPU)
  have hρx : ρ x = diagU (v ∘ π.symm) := by
    rw [hρapp, ← hvx]
    exact permGL_conj_diagU π v
  have hρsurj : ∀ g ∈ unitarySU 2 n Lf 4, ∃ y : S, ρ y = g := by
    intro g hg
    refine ⟨ψ ⟨P⁻¹ * g * P, mul_mem (mul_mem (inv_mem hPU) hg) hPU⟩, ?_⟩
    rw [hρapp, MulEquiv.symm_apply_apply]
    group
  have hmapC : (Sec4.autFix (MulAut.conj x)).map ρ =
      unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {ρ x} := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hxy : x * y = y * x := by
        have h1 : MulAut.conj x y = y := Sec4.mem_autFix.mp hy
        rw [MulAut.conj_apply] at h1
        calc x * y = x * y * x⁻¹ * x := by group
          _ = y * x := by rw [h1]
      refine ⟨hρU y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, hxy]
    · rintro ⟨hgU, hgC⟩
      obtain ⟨y, rfl⟩ := hρsurj _ hgU
      have hgC' := Subgroup.mem_centralizer_singleton_iff.mp hgC
      rw [← map_mul, ← map_mul] at hgC'
      have hxy : x * y = y * x := (hρinj hgC').symm
      refine ⟨y, ?_, rfl⟩
      show MulAut.conj x y = y
      rw [MulAut.conj_apply]
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hxy]
        _ = y := by group
  set K₂ : Subgroup (GL (Fin 4) Lf) := K.map ρ with hK₂
  have hK₂U : K₂ ≤ unitarySU 2 n Lf 4 := by
    rintro _ ⟨k, -, rfl⟩
    exact hρU k
  have hK₂C : K₂ ≤ Subgroup.centralizer {ρ x} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxK k hk]
  have hK₂p : ⁅K₂, K₂⁆ = K₂ := by
    rw [hK₂, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  have hsK₂ : (K₂.subgroupOf (unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {ρ x})).IsSubnormal := by
    have := RonanK429H.isSubnormal_map_subgroupOf hKfix ρ hsub
    rw [hmapC] at this
    exact this
  have hKc : 16482816 ≤ Nat.card K :=
    (le_card_of_isTypeEpsCube hTc).trans
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))
  have hK₂nt : K₂ ≠ ⊥ := by
    intro hb
    have hc : Nat.card K₂ = Nat.card K := Subgroup.card_map_of_injective hρinj
    rw [hb, Subgroup.card_bot] at hc
    omega
  have hT₂ : IsTypeEps (K₂ ⧸ CFSG.pCore 2 K₂) :=
    isTypeEps_of_mulEquiv (quotPCoreTwoCongr (K.equivMapOfInjective ρ hρinj)).symm hT
  have hTc₂ : IsTypeEpsCube (K₂ ⧸ CFSG.pCore 2 K₂) :=
    isTypeEpsCube_of_mulEquiv (quotPCoreTwoCongr (K.equivMapOfInjective ρ hρinj)).symm hTc
  rcases hnf with hA | hB | hC
  ·
    have hDA : ρ x = diagU ![ω, ω, ω, 1] := by rw [hρx, hA]
    have hωbar : hU.bar (ω : Lf) * (ω : Lf) = 1 := by
      rw [UnitaryFieldData.bar_apply, ← pow_succ]
      obtain ⟨k, hk⟩ := h3
      have hω3L : (ω : Lf) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
      rw [hk, pow_mul, hω3L, one_pow]
    exact u4OddEps_caseA hU hn2' hω3 hω1 hωbar hK₂U (by rw [← hDA]; exact hK₂C) hK₂p
      (by rw [← hDA]; exact hsK₂) hK₂nt hT₂
  ·
    have hDB : ρ x = diagU (dvecD0 ω) := by rw [hρx, hB]
    exact u4OddEps_caseB hU hn2' hω1 hω2 hK₂U (by rw [← hDB]; exact hK₂C) hK₂p
      (by rw [← hDB]; exact hsK₂) hK₂nt hTc₂
  ·
    have hDC : ρ x = diagU (dvecC ω) := by rw [hρx, hC]
    exact u4OddEps_caseC hU hn2' hω1 hω2 hK₂U (le_inf hK₂U (by rw [← hDC]; exact hK₂C)) hK₂p
      (show (K₂.subgroupOf (unitarySU 2 n Lf 4 ⊓ Subgroup.centralizer {diagU (dvecC ω)})).IsSubnormal
        by rw [← hDC]; exact hsK₂) hK₂nt hT₂ hTc₂

end CFSG.RankThree.PartTwo.Sec4.RonanEps
