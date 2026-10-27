module

public import CFSG.Quasithin.Vol2.Asc94.HeJ7
public import CFSG.Quasithin.Vol2.Asc94.HeJ12
public import CFSG.Quasithin.Vol2.Asc94.HeK3

public section

namespace CFSG.Quasithin.A94

open Subgroup CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoL3Four

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def HeL (e : ↥(Cz z) ≃* L52.Hc) (B : Subgroup G) : Subgroup G :=
  (normalizer (tr e L52.A1 : Set G) ⊓ centralizer (B : Set G)) ⊔
    (normalizer (tr e L52.A2 : Set G) ⊓ centralizer (B : Set G))

@[expose] def HeB (e : ↥(Cz z) ≃* L52.Hc) (x : G) : Subgroup G :=
  (tr e L52.A1 ⊓ tr e L52.A2) ⊓ centralizer ({x} : Set G)

@[expose] def He42Concl (e : ↥(Cz z) ≃* L52.Hc) (B : Subgroup G) : Prop :=
  HeL e B = centralizer (B : Set G) ∧ TypeL34 (rankTwoQuot (HeL e B)) ∧ TightlyEmbedded B

@[expose] def He42 : Prop :=
  L52.F6Model → ∀ (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
    IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → Setting G z e →
    normalizer (tr e L52.U1 : Set G) = Cz z → normalizer (tr e L52.U2 : Set G) = Cz z →
    ∃ a x : G, a ∈ tr e L52.A1 ⊓ tr e L52.A2 ∧ HeJ.mG e a = 1 ∧
      x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G) ∧
      x ∈ centralizer ({a} : Set G) ∧ orderOf x = 3 ∧ He42Concl e (HeB e x)

section Asm

variable (e : ↥(Cz z) ≃* L52.Hc) (hF6 : L52.F6Model) (S : Setting G z e)
  (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
  {a x : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
  (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
  (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

theorem comm_tr_A1 {y y' : G} (hy : y ∈ tr e L52.A1) (hy' : y' ∈ tr e L52.A1) : y * y' = y' * y := by
  obtain ⟨u, hu, rfl⟩ := hy
  obtain ⟨u', hu', rfl⟩ := hy'
  rw [← map_mul, ← map_mul]
  exact congrArg _ (congrArg Subtype.val (L52.isElemAbelian_A1.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩))

theorem comm_tr_A2 {y y' : G} (hy : y ∈ tr e L52.A2) (hy' : y' ∈ tr e L52.A2) : y * y' = y' * y := by
  obtain ⟨u, hu, rfl⟩ := hy
  obtain ⟨u', hu', rfl⟩ := hy'
  rw [← map_mul, ← map_mul]
  exact congrArg _ (congrArg Subtype.val (L52.isElemAbelian_A2.1.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩))

theorem HeB_le_inf : HeB e x ≤ tr e L52.A1 ⊓ tr e L52.A2 := inf_le_left

theorem isElemAbelian_HeB : IsElemAbelian 2 (HeB e x) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (comm_tr_A1 e (HeB_le_inf e a.2).1 (HeB_le_inf e b.2).1)⟩⟩, ?_⟩
  intro y hy
  exact (isElemAbelian_tr e L52.isElemAbelian_A1).2 y (HeB_le_inf e hy).1

theorem A1_le_HeL : tr e L52.A1 ≤ HeL e (HeB e x) := by
  refine le_trans ?_ le_sup_left
  intro y hy
  refine ⟨Subgroup.le_normalizer hy, ?_⟩
  show y ∈ centralizer ((HeB e x : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  intro b hb
  exact comm_tr_A1 e (HeB_le_inf e (x := x) hb).1 hy

theorem A2_le_HeL : tr e L52.A2 ≤ HeL e (HeB e x) := by
  refine le_trans ?_ le_sup_right
  intro y hy
  refine ⟨Subgroup.le_normalizer hy, ?_⟩
  show y ∈ centralizer ((HeB e x : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  intro b hb
  exact comm_tr_A2 e (HeB_le_inf e (x := x) hb).2 hy

theorem J_le_HeL : (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) ≤ HeL e (HeB e x) :=
  sup_le (A1_le_HeL e) (A2_le_HeL e)

theorem B_le_HeL : HeB e x ≤ HeL e (HeB e x) :=
  le_trans (le_trans (HeB_le_inf e) inf_le_left) (A1_le_HeL e)

include hF6 S h1 h2 ha ham hxN in
theorem x_mem_HeL : x ∈ HeL e (HeB e x) := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  refine (le_sup_left : _ ≤ HeL e (HeB e x)) ⟨hD.N_le_M hxN, ?_⟩
  show x ∈ centralizer ((HeB e x : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  intro b hb
  exact mem_centralizer_singleton_iff.1 hb.2

theorem mem_normalizer_centralizer {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((centralizer (X : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  have key : ∀ c, c ∈ centralizer (X : Set G) → g * c * g⁻¹ ∈ centralizer (X : Set G) := by
    intro c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ X := by
      have := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      simpa using this
    have := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * y := by group
  refine ⟨key c, fun hc => ?_⟩
  have h := key _ hc
  have hg' : g⁻¹ ∈ normalizer (X : Set G) := inv_mem hg
  have := (show ∀ c, c ∈ centralizer (X : Set G) → g⁻¹ * c * g⁻¹⁻¹ ∈ centralizer (X : Set G) from
    fun c hc => by
      rw [mem_centralizer_iff] at hc ⊢
      intro y hy
      have hy' : g * y * g⁻¹ ∈ X := by
        have := (mem_normalizer_iff.1 hg y).1 hy
        exact this
      have := hc _ hy'
      calc y * (g⁻¹ * c * g⁻¹⁻¹) = g⁻¹ * ((g * y * g⁻¹) * c) * g⁻¹⁻¹ := by group
        _ = g⁻¹ * (c * (g * y * g⁻¹)) * g⁻¹⁻¹ := by rw [this]
        _ = g⁻¹ * c * g⁻¹⁻¹ * y := by group) _ hc
  simpa [mul_assoc] using this

include hF6 S h1 h2 ha ham hxN hxa hx3 in
theorem card_HeB : Nat.card ↥(HeB e x) = 4 :=
  (HeJ.data40 e hF6 S h1 h2 ha ham).card_B hxN hxa hx3

variable (hC : He42Concl e (HeB e x))

include hF6 S h1 h2 ha ham hxN hxa hx3 hC

theorem centralizer_HeL : centralizer ((HeL e (HeB e x) : Subgroup G) : Set G) = HeB e x := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  have hxL := x_mem_HeL e hF6 S h1 h2 ha ham hxN
  ext c
  constructor
  · intro hc
    rw [mem_centralizer_iff] at hc
    have hcJ : c ∈ tr e L52.A1 ⊓ tr e L52.A2 :=
      hD.hK.cent c (fun y hy => (hc y (J_le_HeL e hy)).symm)
    have hcx : c ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (hc x hxL).symm
    exact ⟨hcJ, hcx⟩
  · intro hb
    rw [mem_centralizer_iff]
    intro l hl
    rw [hC.1] at hl
    have hl' : l ∈ centralizer ((HeB e x : Subgroup G) : Set G) := hl
    rw [mem_centralizer_iff] at hl'
    exact (hl' c hb).symm

theorem center_HeL :
    center ↥(HeL e (HeB e x)) = (HeB e x).subgroupOf (HeL e (HeB e x)) := by
  have hcl := centralizer_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  ext ⟨y, hy⟩
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  have hmem : y ∈ centralizer ((HeL e (HeB e x) : Subgroup G) : Set G) ↔ y ∈ HeB e x := by
    rw [hcl]
  constructor
  · intro h
    refine hmem.1 ?_
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (h ⟨l, hl⟩)
  · intro hyB l
    have hyB' := hmem.2 hyB
    rw [mem_centralizer_iff] at hyB'
    exact Subtype.ext (hyB' l l.2)

theorem card_HeL : Nat.card ↥(HeL e (HeB e x)) = 80640 := by
  have hq := card_rankTwoQuot_of_typeL34 hC.2.1
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥(HeL e (HeB e x)))
  have hc : Nat.card ↥(center ↥(HeL e (HeB e x))) = 4 := by
    rw [center_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (B_le_HeL e)).toEquiv,
      card_HeB e hF6 S h1 h2 ha ham hxN hxa hx3]
  rw [h, hc]
  have : Nat.card (↥(HeL e (HeB e x)) ⧸ center ↥(HeL e (HeB e x))) = 20160 := hq
  rw [this]

theorem Z_le_commutator_HeL : ∀ y ∈ tr e L52.A1 ⊓ tr e L52.A2,
    y ∈ (commutator ↥(HeL e (HeB e x))).map (HeL e (HeB e x)).subtype := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  set L := HeL e (HeB e x) with hL
  set CL := (commutator ↥L).map L.subtype with hCL
  have hT := hD.hT
  have key : ∀ M : HeJ.M2, ∀ y ∈ tr e L52.A1 ⊓ tr e L52.A2, HeJ.mG e y = M → y ∈ CL := by
    intro M
    induction M using Matrix.induction_on' with
    | h_zero =>
      intro y hy hym
      have : y = 1 := hT.minj y hy 1 (Subgroup.one_mem _) (by rw [hym, hT.m_one])
      subst this
      exact CL.one_mem
    | h_add p q hp hq =>
      intro y hy hym
      obtain ⟨xp, hxp, hxpm⟩ := hT.msurj p
      obtain ⟨xq, hxq, hxqm⟩ := hT.msurj q
      have hyy : y = xp * xq := hT.minj y hy _ ((tr e L52.A1 ⊓ tr e L52.A2).mul_mem hxp hxq) (by
        rw [hym, hT.mmul xp hxp xq hxq, hxpm, hxqm])
      rw [hyy]
      exact CL.mul_mem (hp xp hxp hxpm) (hq xq hxq hxqm)
    | h_std_basis i j c =>
      intro y hy hym
      have hc : c = 0 ∨ c = 1 := by
        clear hym; revert c; decide
      rcases hc with rfl | rfl
      · have : y = 1 := hT.minj y hy 1 (Subgroup.one_mem _) (by
          rw [hym, hT.m_one]; simp)
        subst this
        exact CL.one_mem
      · obtain ⟨xi, hxi, hxiu⟩ := hT.cu.surj (Pi.single i 1)
        obtain ⟨yj, hyj, hyjw⟩ := hT.cw.surj (Pi.single j 1)
        obtain ⟨hzmem, hzm⟩ := hT.comm xi hxi yj hyj
        have hyz : y = xi * yj * xi⁻¹ * yj⁻¹ := hT.minj y hy _ hzmem (by
          rw [hym, hzm, hxiu, hyjw, ← Matrix.single_eq_single_vecMulVec_single])
        rw [hyz]
        exact ⟨_, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top (⟨xi, A1_le_HeL e hxi⟩ : ↥L))
          (Subgroup.mem_top (⟨yj, A2_le_HeL e hyj⟩ : ↥L)), rfl⟩
  exact fun y hy => key _ y hy rfl

include hF6 S h1 h2 ha ham hxN hxa hx3 hC in
theorem commutator_HeL : commutator ↥(HeL e (HeB e x)) = ⊤ := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  set L := HeL e (HeB e x) with hL
  have hsimple : IsSimpleGroup (rankTwoQuot L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hC.2.1).2
  have hq := card_rankTwoQuot_of_typeL34 hC.2.1
  have hcen := center_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  have hZC : center ↥L ≤ commutator ↥L := by
    intro y hy
    rw [hcen, Subgroup.mem_subgroupOf] at hy
    have hyZ : (y : G) ∈ tr e L52.A1 ⊓ tr e L52.A2 := HeB_le_inf e hy
    obtain ⟨w, hw, hwy⟩ := Z_le_commutator_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC _ hyZ
    have : w = y := Subtype.ext hwy
    rw [← this]
    exact hw
  have hQ : commutator (rankTwoQuot L) = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (commutator (rankTwoQuot L)) with h | h
    · exfalso
      have hcz : Subgroup.center (rankTwoQuot L) = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top (rankTwoQuot L)).1 h
      have h2 : 2 ∣ Nat.card (rankTwoQuot L) := by rw [hq]; norm_num
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := rankTwoQuot L) 2 h2
      have hcomm : ∀ g n : rankTwoQuot L, g * n = n * g := fun g n => by
        have hn : n ∈ Subgroup.center (rankTwoQuot L) := by rw [hcz]; exact Subgroup.mem_top _
        exact (Subgroup.mem_center_iff.1 hn) g
      haveI : (Subgroup.zpowers y).Normal := ⟨fun n hn g => by
        have : g * n * g⁻¹ = n := by rw [hcomm g n, mul_inv_cancel_right]
        rw [this]; exact hn⟩
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.zpowers y) with hb | ht
      · have hy1 : y = 1 := by
          have : y ∈ (⊥ : Subgroup (rankTwoQuot L)) := hb ▸ Subgroup.mem_zpowers y
          simpa using this
        rw [hy1, orderOf_one] at hy
        omega
      · have h3 := Nat.card_zpowers y
        rw [ht, Subgroup.card_top, hq, hy] at h3
        omega
    · exact h
  let π := QuotientGroup.mk' (center ↥L)
  have hmap : (commutator ↥L).map π = ⊤ := by
    have h1 : (commutator ↥L).map π =
        ⁅(⊤ : Subgroup ↥L).map π, (⊤ : Subgroup ↥L).map π⁆ := Subgroup.map_commutator ⊤ ⊤ π
    rw [h1, Subgroup.map_top, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    exact hQ
  rw [eq_top_iff]
  intro l _
  have hmem : π l ∈ (commutator ↥L).map π := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨c, hc, hcl⟩ := hmem
  have hker : c⁻¹ * l ∈ center ↥L := by
    rw [← QuotientGroup.ker_mk' (center ↥L), MonoidHom.mem_ker, map_mul, map_inv, hcl,
      inv_mul_cancel]
  have := (commutator ↥L).mul_mem hc (hZC hker)
  simpa using this

theorem standard_HeL : standardComponentIsStandard (HeL e (HeB e x)) := by
  have hcl := centralizer_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  have hcardB := card_HeB e hF6 S h1 h2 ha ham hxN hxa hx3
  have hcardL := card_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  have hsimple : IsSimpleGroup (rankTwoQuot (HeL e (HeB e x))) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hC.2.1).2
  refine ⟨⟨commutator_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC, hsimple⟩, ?_, ?_, ?_, ?_⟩
  · rw [hcl, hcardB]
    exact ⟨2, rfl⟩
  · intro g hg
    rw [hcl] at hg ⊢
    have hg' : g⁻¹ ∉ normalizer ((HeB e x : Subgroup G) : Set G) := fun h => hg (by simpa using inv_mem h)
    have := hC.2.2.2 g⁻¹ hg'
    simpa [rightConjugate] using this
  · rw [hcl]
    apply le_antisymm
    · intro g hg
      have := mem_normalizer_centralizer (X := HeB e x) hg
      rw [← hC.1] at this
      exact this
    · intro g hg
      have := mem_normalizer_centralizer (X := HeL e (HeB e x)) hg
      rw [hcl] at this
      exact this
  · intro g hbot
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    have hle : (HeL e (HeB e x)).map (MulAut.conj g).toMonoidHom ≤ HeB e x := by
      intro y hy
      have hmem : y ∈ centralizer ((HeL e (HeB e x) : Subgroup G) : Set G) ↔ y ∈ HeB e x := by
        rw [hcl]
      refine hmem.1 ?_
      rw [mem_centralizer_iff]
      intro l hl
      exact (mem_centralizer_iff.1 (hbot hl) y hy).symm
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardL, hcardB] at h1
    omega

theorem normalizer_HeL :
    normalizer ((HeL e (HeB e x) : Subgroup G) : Set G) = normalizer ((HeB e x : Subgroup G) : Set G) := by
  have hcl := centralizer_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  apply le_antisymm
  · intro g hg
    have := mem_normalizer_centralizer (X := HeL e (HeB e x)) hg
    rw [hcl] at this
    exact this
  · intro g hg
    have := mem_normalizer_centralizer (X := HeB e x) hg
    rw [← hC.1] at this
    exact this

theorem heGeometry_of_concl : HeGeometry e := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  have hcl := centralizer_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  have hcardB := card_HeB e hF6 S h1 h2 ha ham hxN hxa hx3
  have hcardL := card_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC
  obtain ⟨n, hnN, hinter, hsum⟩ := hD.exists_swap hxN hxa hx3
  have hBle : HeB e x ≤ tr e L52.A1 ⊓ tr e L52.A2 := HeB_le_inf e
  have hZL : tr e L52.A1 ⊓ tr e L52.A2 ≤ HeL e (HeB e x) := le_trans inf_le_left (A1_le_HeL e)
  have hconjZ : ∀ y ∈ HeB e x, n * y * n⁻¹ ∈ tr e L52.A1 ⊓ tr e L52.A2 := fun y hy =>
    hD.mem_Z_conj hnN (hBle hy)
  have hrc : ∀ y, y ∈ rightConjugate (HeB e x) n⁻¹ ↔ n⁻¹ * y * n ∈ HeB e x := by
    intro y
    rw [mem_rightConjugate_iff]
    simp
  have hrcZ : rightConjugate (HeB e x) n⁻¹ ≤ tr e L52.A1 ⊓ tr e L52.A2 := by
    intro y hy
    have := hconjZ _ ((hrc y).1 hy)
    have e' : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
    rwa [e'] at this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨HeL e (HeB e x), HeB e x, n⁻¹, standard_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC,
    hC.2.1, B_le_HeL e, ?_, isElemAbelian_HeB e, hcardB, A1_le_HeL e, A2_le_HeL e,
    (hBle.trans inf_le_left), (hBle.trans inf_le_right), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hcl]
    refine isSylowOf_iff.2 ⟨le_rfl, IsPGroup.of_card (n := 2) (by rw [hcardB]; norm_num), ?_⟩
    rw [Subgroup.relIndex_self]
    norm_num
  ·
    intro hg
    rw [normalizer_HeL e hF6 S h1 h2 ha ham hxN hxa hx3 hC] at hg
    have hn : n ∈ normalizer ((HeB e x : Subgroup G) : Set G) := by simpa using inv_mem hg
    have ha1 := hD.a_ne_one
    have haB := hD.a_mem_B hxN hxa hx3
    have h1' : n * a * n⁻¹ ∈ HeB e x := (mem_normalizer_iff.1 hn a).1 haB
    exact ha1 (hinter a haB _ h1' rfl)
  ·
    intro y hy
    have hyZ := hrcZ hy
    show y ∈ centralizer ((HeB e x : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro b hb
    exact comm_tr_A1 e (hBle hb).1 hyZ.1
  · exact hrcZ.trans hZL
  ·
    apply le_antisymm
    · intro z hz
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hsum z hz
      refine Subgroup.mul_mem_sup hy₁ ?_
      have e' : n⁻¹ * (n * y₂ * n⁻¹) * n = y₂ := by group
      rw [hrc, e']
      exact hy₂
    · exact sup_le hBle hrcZ
  ·
    apply le_antisymm
    · intro z hz
      refine ⟨(le_sup_left : tr e L52.A1 ≤ _) hz.1, ?_⟩
      show z ∈ centralizer (((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G)) : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      exact hD.hT.Z_central hD.hK.Aab hD.hK.A'ab hz hy
    · intro y hy
      exact hD.hK.cent y (fun w hw => (mem_centralizer_iff.1 hy.2 w hw).symm)
  ·
    have hJL : (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) ≤ HeL e (HeB e x) := J_le_HeL e
    refine isSylowOf_iff.2 ⟨hJL, IsPGroup.of_card (n := 8) (by rw [HeJ.card_J e]; norm_num), ?_⟩
    have h := Subgroup.relIndex_mul_card (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) (HeL e (HeB e x))
    rw [inf_eq_left.mpr hJL, HeJ.card_J e, hcardL] at h
    omega

end Asm

theorem heGeometryStmt_of_he42 (h : He42) : HeGeometryStmt := by
  intro hF6 G _ _ z e hs hK S h1 h2
  obtain ⟨a, x, ha, ham, hxN, hxa, hx3, hC⟩ := h hF6 G z e hs hK S h1 h2
  exact heGeometry_of_concl e hF6 S h1 h2 ha ham hxN hxa hx3 hC

section Final


theorem heCaseIIK_of_he42 {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) (hII : L34HypII)
    (hHe : He42) : HeCaseIIK :=
  heCaseIIK_of_geometry hE16 h11 h4 h34 hII (heGeometryStmt_of_he42 hHe)

end Final

end CFSG.Quasithin.A94
