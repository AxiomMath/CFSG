module

public import CFSG.RankThree.GF2n.Tim81.Sec6.RootSetup
import CFSG.RankThree.GF2n.Tim81.Sec6.RootSetupBasic
import CFSG.RankThree.GF2n.Tim81.Sec6.L2Extra
import CFSG.RankThree.GF2n.Tim81.Sec6.RootImages
import CFSG.RankThree.GF2n.Tim81.Cited.SymplecticRootRadical
import CFSG.RankThree.GF2n.Tim79aRootSubgroupOf
import CFSG.RankThree.GF2n.Tim79aSUStatements
import CFSG.GroupTheory.ChiefFactors.RadicalCentralizer
public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {X : Subgroup K} {Δ : Set (Subgroup K)} {f : ℕ}

theorem RootSetup.inf_cenOf_eq_bot (h : RootSetup X Δ f) {T L : Subgroup K} (hT : T ∈ Δ)
    (hL : IsPGroup 2 L) (hZ : L ⊓ cenOf L ≤ T) : L ⊓ cenOf X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hXn : X.Normal := h.normal
  haveI : (cenOf X : Subgroup K).Normal := inferInstance
  set NL : Subgroup K := L ⊓ cenOf X with hNLdef
  have hNLle : NL ≤ L := inf_le_left
  have hNLnormal : (NL.subgroupOf L).Normal := by
    refine ⟨fun n hn l => Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩⟩
    · exact L.mul_mem (L.mul_mem l.2 (Subgroup.mem_subgroupOf.mp hn).1) (L.inv_mem l.2)
    · refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hy' : (l : K)⁻¹ * y * (l : K) ∈ X := by
        simpa using hXn.conj_mem y hy (l : K)⁻¹
      have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn).2
        ((l : K)⁻¹ * y * (l : K)) hy'
      calc y * ((l : K) * (n : K) * (l : K)⁻¹)
          = (l : K) * (((l : K)⁻¹ * y * (l : K)) * (n : K)) * (l : K)⁻¹ := by group
        _ = (l : K) * ((n : K) * ((l : K)⁻¹ * y * (l : K))) * (l : K)⁻¹ := by rw [hc]
        _ = ((l : K) * (n : K) * (l : K)⁻¹) * y := by group
  by_contra hne
  have hsubne : NL.subgroupOf L ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hNLle, hbot, Subgroup.map_bot]
  haveI : Group.IsNilpotent ↥L := hL.isNilpotent
  have hinfne : (NL.subgroupOf L) ⊓ Subgroup.center ↥L ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hsubne
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinfne
  have htNL : ((a : ↥L) : K) ∈ NL := Subgroup.mem_subgroupOf.mp a.2.1
  have htcent : ∀ y : ↥L, y * a.1 = a.1 * y := fun y =>
    Subgroup.mem_center_iff.mp a.2.2 y
  have htcentK : ∀ y ∈ L, y * ((a : ↥L) : K) = ((a : ↥L) : K) * y := by
    intro y hy
    have := congrArg Subtype.val (htcent ⟨y, hy⟩)
    simpa using this
  have htT : ((a : ↥L) : K) ∈ T :=
    hZ ⟨htNL.1, Subgroup.mem_centralizer_iff.mpr fun z hz => htcentK z hz⟩
  set z : ↥X := ⟨((a : ↥L) : K), h.le T hT htT⟩ with hzdef
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hL) a.1
  rw [Subgroup.orderOf_mk] at hk
  have hzcent : z ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp htNL.2 y y.2
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (p := 2) (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk]; exact hk)
  have hle : Subgroup.zpowers z ≤ pCore 2 ↥X :=
    le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcent), hzp⟩
  rw [h.pCore_eq_bot] at hle
  have hz1 : z = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers z))
  apply ha
  apply Subtype.ext
  exact Subtype.ext (congrArg (fun w : ↥X => (w : K)) hz1)

private theorem normalizer_inf_le_normalizer_centralizer
    {T : Subgroup K} : X ⊓ Subgroup.normalizer (T : Set K) ≤
      Subgroup.normalizer ((X ⊓ cenOf T : Subgroup K) : Set K) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    refine ⟨X.mul_mem (X.mul_mem hx.1 hy.1) (X.inv_mem hx.1),
      Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have ht' : x⁻¹ * t * x ∈ T := (Subgroup.mem_normalizer_iff''.mp hx.2 t).mp ht
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 (x⁻¹ * t * x) ht'
    calc t * (x * y * x⁻¹)
        = x * ((x⁻¹ * t * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * t * x)) * x⁻¹ := by rw [hc]
      _ = (x * y * x⁻¹) * t := by group
  · intro hy
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    · have hmem : x⁻¹ * (x * y * x⁻¹) * x ∈ X :=
        X.mul_mem (X.mul_mem (X.inv_mem hx.1) hy.1) hx.1
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hmem
    have ht' : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hx.2 t).mp ht
    have hc := Subgroup.mem_centralizer_iff.mp hy.2 (x * t * x⁻¹) ht'
    calc t * y
        = x⁻¹ * ((x * t * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * t * x⁻¹)) * x := by rw [hc]
      _ = y * t := by group

private theorem RootSetup.pCore_normalizer_le (h : RootSetup X Δ f) {T : Subgroup K}
    (hT : T ∈ Δ) : inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) ≤
      inSubgroup (pCore 2) (X ⊓ cenOf T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup K := X ⊓ Subgroup.normalizer (T : Set K) with hNdef
  set R : Subgroup K := X ⊓ cenOf T with hRdef
  set S : Subgroup K := inSubgroup (pCore 2) N with hSdef
  have hSN : S ≤ N := CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 N
  have hRN : R ≤ N := inf_le_inf_left X (Subgroup.centralizer_le_normalizer (T : Set K))
  have hTleS : T ≤ S := by
    refine CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore (h.isPGroup hT) ?_ ?_
    · exact le_inf (h.le T hT) Subgroup.le_normalizer
    · exact inf_le_right
  have hSnormalN : N ≤ Subgroup.normalizer (S : Set K) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 N
  haveI : (T.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTleS).mpr (hSN.trans inf_le_right)
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hcard := h.card T hT
    rw [hbot, Subgroup.card_bot] at hcard
    have h4 : 4 ≤ 2 ^ f :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num) h.two_le
    omega
  have hHne : T.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [← Subgroup.map_subgroupOf_eq_of_le hTleS, hbot, Subgroup.map_bot]
  haveI : Group.IsNilpotent ↥S :=
    (CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 N).isNilpotent
  have hinfne : (T.subgroupOf S) ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinfne
  have htT : ((a : ↥S) : K) ∈ T := Subgroup.mem_subgroupOf.mp a.2.1
  have htcentK : ∀ y ∈ S, y * ((a : ↥S) : K) = ((a : ↥S) : K) * y := by
    intro y hy
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp a.2.2 ⟨y, hy⟩)
  have ht1 : ((a : ↥S) : K) ≠ 1 := by
    intro h1
    apply ha
    exact Subtype.ext (Subtype.ext h1)
  have hconj : ∀ u ∈ T, ∀ s ∈ S, s * u = u * s := by
    intro u hu s hs
    by_cases hu1 : u = 1
    · subst hu1; simp
    · obtain ⟨B, hB, hTB⟩ := h.partner T hT
      obtain ⟨y, hy, hyconj, hyN⟩ := hTB.exists_conj_of_ne_one htT ht1 hu hu1
      have hyX : y ∈ X := (sup_le (h.le T hT) (h.le B hB)) hy
      have hyNS : y ∈ Subgroup.normalizer (S : Set K) := hSnormalN ⟨hyX, hyN⟩
      have hs' : y⁻¹ * s * y ∈ S := (Subgroup.mem_normalizer_iff''.mp hyNS s).mp hs
      have hcomm := htcentK (y⁻¹ * s * y) hs'
      calc s * u = s * (y * ((a : ↥S) : K) * y⁻¹) := by rw [hyconj]
        _ = y * ((y⁻¹ * s * y) * ((a : ↥S) : K)) * y⁻¹ := by group
        _ = y * (((a : ↥S) : K) * (y⁻¹ * s * y)) * y⁻¹ := by rw [hcomm]
        _ = (y * ((a : ↥S) : K) * y⁻¹) * s := by group
        _ = u * s := by rw [hyconj]
  refine CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore
    (CFSG.RankThree.GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 N) ?_ ?_
  · refine le_inf (hSN.trans inf_le_left) fun s hs => ?_
    rw [Subgroup.mem_centralizer_iff]
    exact fun u hu => (hconj u hu s hs).symm
  · exact hRN.trans hSnormalN

theorem RootSetup.pCore_normalizer_eq (h : RootSetup X Δ f) {T : Subgroup K} (hT : T ∈ Δ) :
    inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) =
      inSubgroup (pCore 2) (X ⊓ cenOf T) := by
  refine le_antisymm (h.pCore_normalizer_le hT) ?_
  exact CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_mono
    (inf_le_inf_left X (Subgroup.centralizer_le_normalizer (T : Set K)))
    normalizer_inf_le_normalizer_centralizer

theorem RootSetup.inf_le_radical (h : RootSetup X Δ f) {T L : Subgroup K}
    (hL : IsPGroup 2 L) (hLT : L ≤ cenOf T)
    (hNL : X ⊓ Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (L : Set K)) :
    L ⊓ X ≤ inSubgroup (pCore 2) (X ⊓ cenOf T) ∧ ⁅X ⊓ cenOf T, L⁆ ≤ L ⊓ X := by
  have hCN : cenOf T ≤ Subgroup.normalizer (T : Set K) :=
    Subgroup.centralizer_le_normalizer (T : Set K)
  have hNRC : X ⊓ cenOf T ≤ Subgroup.normalizer ((L ⊓ X : Subgroup K) : Set K) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact (inf_le_inf_left X hCN).trans hNL
    · haveI : X.Normal := h.normal
      exact Subgroup.le_normalizer_of_normal
  constructor
  · refine CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore hL.to_inf_left ?_ hNRC
    exact le_inf inf_le_right (inf_le_left.trans hLT)
  · refine le_inf ?_ ?_
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((inf_le_inf_left X hCN).trans hNL)
    · haveI : X.Normal := h.normal
      exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
        (Subgroup.commutator_le_left (H₁ := X) (H₂ := L))

private theorem RootSetup.eq_of_inf_eq_of_su (h : RootSetup X Δ f) (hf : 1 ≤ f) {m : ℕ}
    (hm : 4 ≤ m) (hX : IsSUImage X Δ f m hf (by omega)) {T L : Subgroup K} (hT : T ∈ Δ)
    (hL : IsPGroup 2 L) (hTL : T ≤ L) (hLT : L ≤ cenOf T)
    (hNL : X ⊓ Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (L : Set K))
    (hLX : L ⊓ cenOf X = ⊥) (hLXT : L ⊓ X = T) : L = T := by
  haveI hXn : X.Normal := h.normal
  haveI hCn : (cenOf X : Subgroup K).Normal := by infer_instance
  have hIL := h.inf_le_radical hL hLT hNL
  have hLRC := hX.le_pCore_sup_cenOf hm hT hL hLT hNL
  refine le_antisymm (fun l hl => ?_) hTL
  obtain ⟨r, hr, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hLRC hl)
  have hrT : r ∈ T := by
    refine hX.mem_of_forall_commutatorElement_mem hm hT
      ((hX.inSubgroup_pCore_cenOf_eq hm hT).le hr) fun x hx => ?_
    have hcx : Commute x c := Subgroup.mem_centralizer_iff.1 hc x hx.1
    have e : ⁅x, r * c⁆ = ⁅x, r⁆ := by
      have hcx' : c * x⁻¹ = x⁻¹ * c := hcx.inv_left.eq.symm
      calc ⁅x, r * c⁆ = x * r * (c * x⁻¹) * c⁻¹ * r⁻¹ := by rw [commutatorElement_def]; group
        _ = x * r * (x⁻¹ * c) * c⁻¹ * r⁻¹ := by rw [hcx']
        _ = ⁅x, r⁆ := by rw [commutatorElement_def]; group
    rw [← e, ← hLXT]
    exact hIL.2 (Subgroup.commutator_mem_commutator hx hl)
  have hcL : c ∈ L := by
    have h1 := L.mul_mem (L.inv_mem (hTL hrT)) hl
    rwa [inv_mul_cancel_left] at h1
  have hc1 : c = 1 := by
    have hmem : c ∈ L ⊓ cenOf X := ⟨hcL, hc⟩
    rwa [hLX, Subgroup.mem_bot] at hmem
  rw [hc1, mul_one]
  exact hrT

theorem RootSetup.rigid_su (h : RootSetup X Δ f) (hf : 1 ≤ f) {m : ℕ} (hm : 4 ≤ m)
    (hX : IsSUImage X Δ f m hf (Nat.le_trans (Nat.le_add_right 2 2) hm))
    {T L : Subgroup K} (hT : T ∈ Δ) (hL : IsPGroup 2 L) (hTL : T ≤ L) (hLT : L ≤ cenOf T)
    (hNL : X ⊓ Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (L : Set K))
    (hLX : L ⊓ cenOf X = ⊥) :
    L = T ∨ (L = inSubgroup (pCore 2) (X ⊓ Subgroup.normalizer (T : Set K)) ∧
      Nat.card L = (2 ^ f) ^ (2 * m - 3)) := by
  set R : Subgroup K := inSubgroup (pCore 2) (X ⊓ cenOf T) with hRdef
  haveI hXn : X.Normal := h.normal
  have hcardR := hX.natCard_pCore_cenOf hm hT
  have hIL := h.inf_le_radical hL hLT hNL
  have hLRC : L ≤ R ⊔ cenOf X := hX.le_pCore_sup_cenOf hm hT hL hLT hNL
  have hN : X ⊓ Subgroup.normalizer (T : Set K) ≤
      Subgroup.normalizer ((L ⊓ X : Subgroup K) : Set K) := by
    refine (le_inf hNL ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact Subgroup.le_normalizer_of_normal
  have hY : L ⊓ X = T ∨ L ⊓ X = R := by
    have := Tim79a.eq_or_eq_of_rootIrrModel (h.le T hT) (hX.rootIrrModel_subgroupOf hm hT)
      (le_inf hTL (h.le T hT)) (hIL.1.trans (h.pCore_normalizer_eq hT).ge) hN
    rwa [h.pCore_normalizer_eq hT] at this
  rcases hY with hYT | hYR
  · exact Or.inl (h.eq_of_inf_eq_of_su hf hm hX hT hL hTL hLT hNL hLX hYT)
  · right
    have hLR : L ≤ R := by
      intro l hl
      obtain ⟨r, hr, c, hc, hrc⟩ := Subgroup.mem_sup_of_normal_right.mp (hLRC hl)
      have hrL : r ∈ L := by
        have : r ∈ L ⊓ X := by rw [hYR]; exact hr
        exact this.1
      have hcL : c ∈ L := by
        have hceq : c = r⁻¹ * l := by rw [← hrc]; group
        rw [hceq]
        exact L.mul_mem (L.inv_mem hrL) hl
      have hc1 : c = 1 := by
        have hmem : c ∈ L ⊓ cenOf X := ⟨hcL, hc⟩
        rw [hLX] at hmem
        exact Subgroup.mem_bot.mp hmem
      rw [← hrc, hc1, mul_one]
      exact hr
    have hRL : R ≤ L := by rw [← hYR]; exact inf_le_left
    have hEq : L = R := le_antisymm hLR hRL
    refine ⟨by rw [hEq, hRdef, h.pCore_normalizer_eq hT], ?_⟩
    rw [hEq, hRdef]
    exact hcardR

theorem RootSetup.rigid_sp (h : RootSetup X Δ f) (hf : 1 ≤ f) {m : ℕ} (hm : 2 ≤ m)
    (hX : IsSpImage X Δ f m (Nat.one_le_of_lt hm)) {T L : Subgroup K} (hT : T ∈ Δ)
    (hL : IsPGroup 2 L)
    (hTL : T ≤ L) (hLT : L ≤ cenOf T)
    (hNL : X ⊓ Subgroup.normalizer (T : Set K) ≤ Subgroup.normalizer (L : Set K))
    (hLX : L ⊓ cenOf X = ⊥) (hZ : L ⊓ cenOf L ≤ T) : L = T := by
  set R : Subgroup K := inSubgroup (pCore 2) (X ⊓ cenOf T) with hRdef
  set C : Subgroup K := cenOf X with hCdef
  haveI hXn : X.Normal := h.normal
  haveI hCn : C.Normal := by rw [hCdef]; infer_instance
  have hLRC : L ≤ R ⊔ C := by
    have hCR := hX.classicalRoot hf hm hT
    show L ≤ inSubgroup (pCore 2) (X ⊓ cenOf T) ⊔ cenOf X
    rw [← h.pCore_normalizer_eq hT]
    exact CFSG.GroupTheory.le_inSubgroup_pCore_sup_centralizer
      (CFSG.RankThree.GroupTheory.SteinbergBY.le_inSubgroup_pCore (h.isPGroup hT)
        (le_inf (h.le T hT) Subgroup.le_normalizer) inf_le_right)
      (fun Y h1 h2 h3 => Tim79a.eq_or_eq_of_rootIrrModel (h.le T hT)
        (Tim79a.classicalRootIrrStatement_holds ↥X _ hCR) h1 h2 h3)
      (fun l hl hb => Tim79a.mem_pCore_sup_centralizer_of_rootS2Model (h.le T hT)
        (Tim79a.classicalRootS2Statement_holds ↥X _ hCR) hl hb) hL hLT hNL
  have hRabel : R ≤ cenOf R := symplecticRootRadicalAbelian K X Δ f m hm h.two_le hX T hT
  have hRleX : R ≤ X :=
    (CFSG.RankThree.GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left
  have habel : ∀ l ∈ L, ∀ l' ∈ L, Commute l l' := by
    intro l hl l' hl'
    obtain ⟨r, hr, c, hc, hrc⟩ := Subgroup.mem_sup_of_normal_right.mp (hLRC hl)
    obtain ⟨r', hr', c', hc', hrc'⟩ := Subgroup.mem_sup_of_normal_right.mp (hLRC hl')
    have hRR : Commute r r' := (Subgroup.mem_centralizer_iff.mp (hRabel hr) r' hr').symm
    have hRc' : Commute r c' := Subgroup.mem_centralizer_iff.mp hc' r (hRleX hr)
    have hcR' : Commute c r' := (Subgroup.mem_centralizer_iff.mp hc r' (hRleX hr')).symm
    have hcommC : ⁅c, c'⁆ ∈ C :=
      (Subgroup.commutator_le_left (H₁ := C) (H₂ := C))
        (Subgroup.commutator_mem_commutator hc hc')
    have hrX : Commute r ⁅c, c'⁆ := Subgroup.mem_centralizer_iff.mp hcommC r (hRleX hr)
    have hr'X : Commute r' ⁅c, c'⁆ := Subgroup.mem_centralizer_iff.mp hcommC r' (hRleX hr')
    have hzero : ⁅r, r'⁆ = 1 := hRR.commutator_eq
    have hRC : Commute r c := Subgroup.mem_centralizer_iff.mp hc r (hRleX hr)
    have hRC' : Commute r' c' := Subgroup.mem_centralizer_iff.mp hc' r' (hRleX hr')
    have hform : ⁅l, l'⁆ = ⁅c, c'⁆ := by
      have h1 : l = c * r := by rw [← hrc, hRC.eq]
      have h2 : l' = c' * r' := by rw [← hrc', hRC'.eq]
      rw [h1, h2,
        TauCeti.commutatorElement_mul_mul_eq_mul_of_commute (a := c) (b := r) (c := c') (d := r')
          hRc' hcR' (by rw [hzero]; exact Commute.one_right _)
          (by rw [hzero]; exact Commute.one_right _)
          (by rw [hzero]; exact Commute.one_right _),
        hzero, mul_one]
    have hmemL : ⁅l, l'⁆ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl)) (L.inv_mem hl')
    have hbot : ⁅l, l'⁆ ∈ (⊥ : Subgroup K) := by
      have hmem : ⁅l, l'⁆ ∈ L ⊓ C := ⟨hmemL, hform.symm ▸ hcommC⟩
      rwa [hLX] at hmem
    exact commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hbot)
  have hLle : L ≤ T := by
    have hcent : L ≤ cenOf L := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      exact fun l' hl' => (habel l hl l' hl').symm
    exact (le_inf le_rfl hcent).trans hZ
  exact le_antisymm hLle hTL

end CFSG.RankThree.GF2n.Tim81
