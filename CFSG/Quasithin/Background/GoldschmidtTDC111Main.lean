module

public import CFSG.Quasithin.Background.GoldschmidtTDC111Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.C1PackBasic

public section

namespace CFSG.Quasithin.TDC111

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {ι : Type}

omit [Finite G] in
theorem comm_of_commutator_eq_bot {A A' : Subgroup G} (h : ⁅A, A'⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := by
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha
  exact (Subgroup.mem_centralizer_iff.1 this b hb).symm

omit [Finite G] in
theorem mem_sup_of_commute' {A A' : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ A') : ∃ a ∈ A, ∃ b ∈ A', x = a * b := by
  have hn : A ≤ Subgroup.normalizer (A' : Set G) := le_normalizer_of_commute hc le_rfl
  have hx' : x ∈ ((A ⊔ A' : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A A' hn] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

variable {B : ι → Subgroup G}

omit [Finite G] in
theorem iSup_le_normalizer_of_commute {T : ι → Subgroup G} (hT : ∀ i, T i ≤ B i)
    (hN : ∀ i, B i ≤ Subgroup.normalizer (T i : Set G))
    (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) (i : ι) :
    (⨆ j, B j) ≤ Subgroup.normalizer (T i : Set G) := by
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact hN j
  · exact le_normalizer_of_commute (comm_of_commutator_eq_bot (hc j i hij)) (hT i)

omit [Finite G] in
theorem iSup_le_normalizer_iSup {T : ι → Subgroup G} (hT : ∀ i, T i ≤ B i)
    (hN : ∀ i, B i ≤ Subgroup.normalizer (T i : Set G))
    (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) :
    (⨆ j, B j) ≤ Subgroup.normalizer ((⨆ i, T i : Subgroup G) : Set G) := fun _ hk =>
  mem_normalizer_iSup_of_forall fun i => iSup_le_normalizer_of_commute hT hN hc i hk

theorem blockQ_le_pCoreOf_iSup (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) (i : ι) :
    blockQ (B i) ≤ pCoreOf 2 (⨆ j, B j) :=
  C1.le_pCoreOf_of_normalized ((C1.blockQ_le (B i)).trans (le_iSup B i))
    (iSup_le_normalizer_of_commute (T := fun i => blockQ (B i)) (fun i => C1.blockQ_le (B i))
      (fun i => C1.le_normalizer_blockQ (B i)) hc i)
    (C1.blockQ_isPGroup (B i))

theorem iSup_blockU_le (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) :
    (⨆ i, blockU (B i)) ≤ ⁅pCoreOf 2 (⨆ j, B j), ⨆ j, B j⁆ :=
  iSup_le fun i => Subgroup.commutator_mono (blockQ_le_pCoreOf_iSup hc i) (le_iSup B i)

theorem iSup_le_normalizer_iSup_blockU (hs : ∀ i, IsShort2 (B i))
    (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) :
    (⨆ j, B j) ≤ Subgroup.normalizer ((⨆ i, blockU (B i) : Subgroup G) : Set G) :=
  iSup_le_normalizer_iSup (T := fun i => blockU (B i))
    (fun i => (C1.blockU_le_blockQ (hs i)).trans (C1.blockQ_le (B i)))
    (fun i => C1.le_normalizer_blockU (B i)) hc

section Blocks

variable {H : Subgroup G}

theorem mem_normalizer_of_mem_pCoreOf {B : Subgroup G} (hB : IsBlock2 H B) {y : G}
    (hy : y ∈ pCoreOf 2 H) : y ∈ Subgroup.normalizer (B : Set G) := by
  have hn := (C1Pack.isBlock2_normal_sup_pCore hB).2
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).1 hn)
    (le_sup_right (a := B) hy)

theorem commutator_mem_blockQ_of_mem_pCoreOf' {B : Subgroup G} (hB : IsBlock2 H B) {y : G}
    (hy : y ∈ pCoreOf 2 H) {l : G} (hl : l ∈ B) : y * l * y⁻¹ * l⁻¹ ∈ blockQ B := by
  rw [C1Pack.blockQ_eq_inf_pCoreOf hB]
  have hyN := mem_normalizer_of_mem_pCoreOf hB hy
  refine Subgroup.mem_inf.2 ⟨B.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN l).mp hl)
    (B.inv_mem hl), ?_⟩
  have hPnorm : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have h3 : l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (hPnorm (hB.2.1 hl)) y⁻¹).mp (inv_mem hy)
  have : y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
  rw [this]
  exact mul_mem hy h3

theorem commute_blockU_of_mem_pCoreOf {B : Subgroup G} (hB : IsBlock2 H B) {y : G}
    (hy : y ∈ pCoreOf 2 H) : ∀ u ∈ blockU B, u * y = y * u := by
  have hP2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  exact C1.commute_blockU_of_mem hB.1 (mem_normalizer_of_mem_pCoreOf hB hy)
    (C1.exists_pow_eq_one_of_isPGroup hP2 hy) fun l hl =>
      commutator_mem_blockQ_of_mem_pCoreOf' hB hy hl

theorem commutator_pCoreOf_iSup_le {B : ι → Subgroup G} (hB : ∀ i, IsBlock2 H (B i))
    (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥)
    (hKn : H ≤ Subgroup.normalizer ((⨆ i, B i : Subgroup G) : Set G)) :
    ⁅pCoreOf 2 (⨆ j, B j), ⨆ j, B j⁆ ≤ ⨆ i, blockU (B i) := by
  set K : Subgroup G := ⨆ i, B i with hKdef
  set W : Subgroup G := ⨆ i, blockU (B i) with hWdef
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    iSup_le_normalizer_iSup_blockU (fun i => (hB i).1) hc
  have hKH : K ≤ H := iSup_le fun i => (hB i).2.1
  have hqH : pCoreOf 2 K ≤ pCoreOf 2 H := by
    refine C1.le_pCoreOf_of_normalized ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K).trans
      hKH) (fun g hg => ?_) (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K)
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) K (hKn hg)
  rw [Subgroup.commutator_le]
  intro q hq
  have hqP : q ∈ pCoreOf 2 H := hqH hq
  let D : Subgroup G :=
    { carrier := {k | k ∈ K ∧ q * k * q⁻¹ * k⁻¹ ∈ W}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        have e : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha.2 ((Subgroup.mem_normalizer_iff.mp (hKW ha.1) _).mp hb.2)⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have e : q * a⁻¹ * q⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (hKW (inv_mem ha.1)) _).mp (inv_mem ha.2)
        simpa using this⟩ }
  have hBD : ∀ i, B i ≤ D := fun i l hl => by
    refine ⟨le_iSup B i hl, ?_⟩
    exact le_iSup (fun i => blockU (B i)) i
      (C1.commutator_mem_blockU_of_mem_blockQ (hB i).1
        (fun l' hl' => commutator_mem_blockQ_of_mem_pCoreOf' (hB i) hqP hl') l hl)
  intro k hk
  exact (iSup_le hBD hk).2

theorem inf_centralizer_le_aux {B : ι → Subgroup G} (hs : ∀ i, IsShort2 (B i))
    (hc : ∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) (s : Finset ι) :
    (⨆ i ∈ s, B i) ⊓ Subgroup.centralizer ((⨆ i ∈ s, blockU (B i) : Subgroup G) : Set G) ≤
      ⨆ i ∈ s, blockQ (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_insert]
    intro c hcc
    obtain ⟨hcK, hcC⟩ := hcc
    have hBaU : blockU (B a) ≤ B a := (C1.blockU_le_blockQ (hs a)).trans (C1.blockQ_le (B a))
    have hKs : (⨆ i ∈ s, B i) ≤ Subgroup.centralizer (B a : Set G) :=
      iSup₂_le fun i hi => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (hc i a (fun h => ha (h ▸ hi)))
    have hcomm : ∀ y ∈ B a, ∀ x ∈ ⨆ i ∈ s, B i, y * x = x * y := fun y hy x hx =>
      Subgroup.mem_centralizer_iff.1 (hKs hx) y hy
    obtain ⟨y, hy, x, hx, rfl⟩ := mem_sup_of_commute' hcomm hcK
    have hcUa : ∀ u ∈ blockU (B a), u * (y * x) = (y * x) * u := fun u hu =>
      Subgroup.mem_centralizer_iff.1 hcC u (le_sup_left (a := blockU (B a)) hu)
    have hxUa : ∀ u ∈ blockU (B a), x * u = u * x := fun u hu =>
      (hcomm u (hBaU hu) x hx).symm
    have hyUa : ∀ u ∈ blockU (B a), u * y = y * u := fun u hu => by
      have h1 : u * y * x = y * u * x := by
        calc u * y * x = u * (y * x) := by group
          _ = y * x * u := hcUa u hu
          _ = y * (x * u) := by group
          _ = y * (u * x) := by rw [hxUa u hu]
          _ = y * u * x := by group
      exact mul_right_cancel h1
    have hWsK : (⨆ i ∈ s, blockU (B i)) ≤ ⨆ i ∈ s, B i :=
      iSup₂_le fun i hi => (((C1.blockU_le_blockQ (hs i)).trans (C1.blockQ_le (B i))).trans
        (le_iSup₂ (f := fun i (_ : i ∈ s) => B i) i hi))
    have hcWs : ∀ w ∈ (⨆ i ∈ s, blockU (B i) : Subgroup G), w * (y * x) = (y * x) * w :=
      fun w hw => Subgroup.mem_centralizer_iff.1 hcC w
        (le_sup_right (b := (⨆ i ∈ s, blockU (B i))) hw)
    have hxWs : ∀ w ∈ (⨆ i ∈ s, blockU (B i) : Subgroup G), w * x = x * w := fun w hw => by
      have hyw : y * w = w * y := hcomm y hy w (hWsK hw)
      have h1 : y * (x * w) = y * (w * x) := by
        calc y * (x * w) = y * x * w := by group
          _ = w * (y * x) := (hcWs w hw).symm
          _ = (w * y) * x := by group
          _ = (y * w) * x := by rw [← hyw]
          _ = y * (w * x) := by group
      exact (mul_left_cancel h1).symm
    have hy' : y ∈ blockQ (B a) := C1.inf_centralizer_blockU_le (hs a) ⟨hy,
      Subgroup.mem_centralizer_iff.2 fun u hu => hyUa u hu⟩
    have hx' : x ∈ ⨆ i ∈ s, blockQ (B i) := ih ⟨hx, Subgroup.mem_centralizer_iff.2 hxWs⟩
    exact mul_mem (le_sup_left (a := blockQ (B a)) hy')
      (le_sup_right (b := ⨆ i ∈ s, blockQ (B i)) hx')

end Blocks

omit [Finite G] in
theorem mem_normalizer_commutator {A A' : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hA' : g ∈ Subgroup.normalizer (A' : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, A'⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hA' ⊢
  rw [Subgroup.map_commutator, hA, hA']

end CFSG.Quasithin.TDC111

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.TDC111

theorem asc111Statement_holds (G : Type) [Group G] [Finite G] : ASC111Statement G := by
  intro H K S ι B hι hB hc hK hKH hS hprod
  subst hK
  have hs : ∀ i, IsShort2 (B i) := fun i => (hB i).1
  have hP2 : IsPGroup 2 (pCoreOf 2 H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hPH : pCoreOf 2 H ≤ H :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hle : (⨆ i, B i) ≤ oTwoUpper H := iSup_le fun i =>
    ((C1Pack.isShort2_eq_oTwoUpper (hs i)).le).trans (oTwoUpper_mono (hB i).2.1)
  have hKeq : (⨆ i, B i) = oTwoUpper H :=
    eq_oTwoUpper_of_subnormal_of_mul (isSubnormal_iSup_blocks hB) hKH hS hprod hle
  have hKn : H ≤ Subgroup.normalizer ((⨆ i, B i : Subgroup G) : Set G) :=
    hKeq ▸ le_normalizer_oTwoUpper H
  have hK2 : ∀ h ∈ H, ∃ m : ℕ, h ^ 2 ^ m ∈ (⨆ i, B i : Subgroup G) := fun h hh =>
    hKeq ▸ exists_pow_mem_oTwoUpper H hh
  have hUW : ⁅pCoreOf 2 (⨆ i, B i), ⨆ i, B i⁆ = ⨆ i, blockU (B i) :=
    le_antisymm (commutator_pCoreOf_iSup_le hB hc hKn) (iSup_blockU_le hc)
  rw [hUW]
  apply le_antisymm
  ·
    set C : Subgroup G := H ⊓ Subgroup.centralizer ((⨆ i, blockU (B i) : Subgroup G) : Set G)
      with hCdef
    have hHW : H ≤ Subgroup.normalizer ((⨆ i, blockU (B i) : Subgroup G) : Set G) := by
      rw [← hUW]
      intro g hg
      have hgK := hKn hg
      exact mem_normalizer_commutator
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) _ hgK) hgK
    have hCn : H ≤ Subgroup.normalizer (C : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
        intro g hg c hc'
        refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem hg hc'.1) (H.inv_mem hg), ?_⟩
        refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
        have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ (⨆ i, blockU (B i) : Subgroup G) :=
          (Subgroup.mem_normalizer_iff.mp (hHW (H.inv_mem hg)) w).mp hw
        have h1 := Subgroup.mem_centralizer_iff.1 hc'.2 _ hw'
        simp only [inv_inv] at h1
        calc w * (g * c * g⁻¹) = g * ((g⁻¹ * w * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
          _ = g * c * g⁻¹ * w := by group
      intro x
      refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
      have := key g⁻¹ (H.inv_mem hg) _ hx
      simpa [mul_assoc] using this
    have hQP : (⨆ i, blockQ (B i)) ≤ pCoreOf 2 H := iSup_le fun i =>
      (C1Pack.blockQ_eq_inf_pCoreOf (hB i)).le.trans inf_le_right
    have hC2 : IsPGroup 2 C := by
      intro g
      obtain ⟨m, hm⟩ := hK2 g g.2.1
      have hmC : (g : G) ^ 2 ^ m ∈ C := C.pow_mem g.2 _
      have hmQ : (g : G) ^ 2 ^ m ∈ pCoreOf 2 H := by
        have hfin : Fintype ι := Fintype.ofFinite ι
        have := inf_centralizer_le_aux hs hc Finset.univ
        simp only [Finset.mem_univ, iSup_pos] at this
        exact hQP (this ⟨hm, hmC.2⟩)
      obtain ⟨j, hj⟩ := C1.exists_pow_eq_one_of_isPGroup hP2 hmQ
      refine ⟨m + j, Subtype.ext ?_⟩
      calc ((g ^ 2 ^ (m + j) : C) : G) = ((g : G) ^ 2 ^ m) ^ 2 ^ j := by
            rw [Subgroup.coe_pow, ← pow_mul, ← pow_add]
        _ = 1 := hj
        _ = ((1 : C) : G) := rfl
    exact C1.le_pCoreOf_of_normalized inf_le_left hCn hC2
  ·
    intro y hy
    refine Subgroup.mem_inf.2 ⟨hPH hy, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    have hW : (⨆ i, blockU (B i) : Subgroup G) ≤ Subgroup.centralizer ({y} : Set G) :=
      iSup_le fun i u hu => Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (commute_blockU_of_mem_pCoreOf (hB i) hy u hu).symm
    have := Subgroup.mem_centralizer_iff.1 (hW hu) y (Set.mem_singleton y)
    exact this.symm

end CFSG.Quasithin
