module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCStmt
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW CFSG.LocalAnalysis.WeakClosure81.NGW

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_three_mem {Y : Type*} [Group Y] {R : Subgroup Y} {x : Y} {k : ℕ}
    (hk : x ^ 3 ^ k ∈ R) (h3 : ¬ 3 ∣ orderOf x) : x ∈ R := by
  have hcop : Nat.Coprime (3 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact R.pow_mem hk m

omit [Finite G] in
theorem liftSub_le_normalizer {N : Subgroup G} {X : Type} [Group X] {ψ : ↥N →* X}
    {Hb Rb : Subgroup X} (h : Hb ≤ normalizer (Rb : Set X)) :
    liftSub ψ Hb ≤ normalizer (liftSub ψ Rb : Set G) := by
  intro x hx
  obtain ⟨hxN, hxH⟩ := mem_liftSub.1 hx
  exact mem_normalizer_liftSub hxN (h hxH)

namespace Ctx

variable {V T N : Subgroup G} {X : Type} [Group X] [Finite X] {ψ : ↥N →* X}
variable (c : Ctx V T N ψ)
include c

omit [Finite X] in
theorem not_three_dvd_orderOf {g : G} (hgM : conjSubgroup V g ≤ normalizer (V : Set G))
    (hgV : conjSubgroup V g ≠ V) {y : G} (hyN : y ∈ N)
    (hy : y ∈ normalizer (conjSubgroup V g : Set G)) : ¬ 3 ∣ orderOf y := by
  intro h3
  exact c.not_orderOf_three hgM hgV (N.pow_mem hyN _) (Subgroup.pow_mem _ hy _)
    (orderOf_pow_orderOf_div (orderOf_pos y).ne' h3)

omit [Finite X] in
theorem inf_le_wClos {g : G} (hAT : conjSubgroup V g ≤ T) {Rb : Subgroup X}
    (hidx : Rb.relIndex (barSub ψ (conjSubgroup V g)) = 2) :
    liftSub ψ Rb ⊓ conjSubgroup V g ≤ E3.wClos V 1 (liftSub ψ Rb) ∧
      liftSub ψ Rb ⊓ conjSubgroup V g ≠ ⊥ := by
  have hrel : (liftSub ψ Rb).relIndex (conjSubgroup V g) = 2 := by
    rw [relIndex_liftSub_left (hAT.trans c.TN)]
    exact hidx
  refine ⟨E3.le_wClos_of_mQuot_le c.elem g inf_le_left inf_le_right ?_ c.one_lt_rk, ?_⟩
  · show padicValNat 2 ((liftSub ψ Rb ⊓ conjSubgroup V g).relIndex (conjSubgroup V g)) ≤ 1
    rw [Subgroup.inf_relIndex_right, hrel, padicValNat_self]
  · have hcard : 4 ≤ Nat.card ↥(liftSub ψ Rb ⊓ conjSubgroup V g) := by
      have h1 := Subgroup.relIndex_mul_card (liftSub ψ Rb) (conjSubgroup V g)
      rw [hrel] at h1
      have h3 : 8 ≤ Nat.card (conjSubgroup V g) := c.card_conj g
      omega
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    omega

omit [Finite X] in
theorem centralizer_wClos_le_normalizer {g : G} (hAT : conjSubgroup V g ≤ T) {Rb : Subgroup X}
    (hidx : Rb.relIndex (barSub ψ (conjSubgroup V g)) = 2) :
    centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) ≤
      normalizer (conjSubgroup V g : Set G) := by
  obtain ⟨hW, hne⟩ := c.inf_le_wClos hAT hidx
  obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  intro y hy
  refine centralizer_le_normalizer_conj c.ti g ha₀.2 (fun h0 => ha₀1 (Subtype.ext h0)) ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.1 hy) a₀ (hW ha₀)).symm

omit [Finite X] in
theorem pCoreOf_le_of_fiveUseC {Tb Ab Hb Rb : Subgroup X} (hF : FiveUseC Tb Ab Hb Rb) :
    pCoreOf 2 (liftSub ψ Hb) ≤ liftSub ψ Rb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := liftSub ψ Hb with hHdef
  have hHb : barSub ψ H = Hb := barSub_liftSub c.surj Hb
  have hle : pCoreOf 2 H ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans (liftSub_le Hb)
  refine (barSub_le_iff hle).1 (hF.cP _ ?_ ?_ (isPGroup_barSub
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)))
  · rw [← hHb]
    exact barSub_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  · rw [← hHb]
    exact barSub_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)

omit [Finite X] in
theorem commutator_mem_of_fiveUseC {g : G} (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUseC (barSub ψ T) (barSub ψ (conjSubgroup V g)) Hb Rb) {y a : G}
    (hy : y ∈ liftSub ψ Hb ⊓ centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G))
    (ha : a ∈ conjSubgroup V g) : y * a * y⁻¹ * a⁻¹ ∈ liftSub ψ Rb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := conjSubgroup V g with hAdef
  set H := liftSub ψ Hb with hHdef
  set Y := H ⊓ centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) with hYdef
  have hAH : A ≤ H := (barSub_le_iff (hAT.trans c.TN)).1 hF.le
  have hHW : H ≤ normalizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) :=
    (liftSub_le_normalizer hF.R_norm).trans (E3.normalizer_le_normalizer_wClos _)
  have hHY : H ≤ normalizer (Y : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn) (mem_normalizer_centralizer (hHW hn))
  have hYA : Y ≤ normalizer (A : Set G) :=
    inf_le_right.trans (c.centralizer_wClos_le_normalizer hAT hF.idx)
  have hYAR : Y ⊓ A ≤ liftSub ψ Rb := by
    have h1 : Y ⊓ A ≤ pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (E1.le_normalizer_inf_of_le_normalizer hYA)
        ((isElemAbelian_conjSubgroup' c.elem g).isPGroup.to_le inf_le_right)
    have h2 : pCoreOf 2 Y ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans inf_le_left)
        (hHY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    exact h1.trans (h2.trans (c.pCoreOf_le_of_fiveUseC hF))
  apply hYAR
  refine ⟨?_, ?_⟩
  · have h1 : a * y⁻¹ * a⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.1 (hHY (hAH ha)) y⁻¹).1 (Y.inv_mem hy)
    have := Y.mul_mem hy h1
    simpa [mul_assoc] using this
  · have h1 : y * a * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hYA hy) a).1 ha
    exact A.mul_mem h1 (A.inv_mem ha)

omit [Finite X] in
theorem inf_centralizer_wClos_le {g : G} (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUseC (barSub ψ T) (barSub ψ (conjSubgroup V g)) Hb Rb) :
    liftSub ψ Hb ⊓ centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) ≤ liftSub ψ Rb := by
  set H := liftSub ψ Hb with hHdef
  set Y := H ⊓ centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) with hYdef
  have hHb : barSub ψ H = Hb := barSub_liftSub c.surj Hb
  have hHW : H ≤ normalizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) :=
    (liftSub_le_normalizer hF.R_norm).trans (E3.normalizer_le_normalizer_wClos _)
  have hHY : H ≤ normalizer (Y : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn) (mem_normalizer_centralizer (hHW hn))
  have hAV : conjSubgroup V g ≠ V := fun hAV => NGW.not_le_of_relIndex_eq_two hF.idx (by
    rw [hAV]
    exact (barSub_le_iff (c.V_le_T.trans c.TN)).2 (c.V_le_Q.trans (pCoreOf_le_liftSub c.ker Rb)))
  intro y hy
  have hyN : y ∈ N := liftSub_le Hb hy.1
  obtain ⟨k, hk⟩ := hF.cY (barSub ψ Y) (by rw [← hHb]; exact barSub_mono inf_le_left)
    (by rw [← hHb]; exact barSub_le_normalizer hHY) (by
      rintro _ ⟨y', hy', rfl⟩ _ ⟨a, ha, rfl⟩
      have h1 := c.commutator_mem_of_fiveUseC (y := (y' : G)) (a := (a : G)) hAT hF hy' ha
      have e : (y' : G) * a * (y' : G)⁻¹ * (a : G)⁻¹ = ((y' * a * y'⁻¹ * a⁻¹ : ↥N) : G) := rfl
      rw [e, mem_liftSub_iff] at h1
      simpa only [map_mul, map_inv] using h1) (ψ ⟨y, hyN⟩) (mem_barSub_of_mem hyN hy)
  have h3 : ¬ 3 ∣ orderOf (ψ ⟨y, hyN⟩) := fun h3 =>
    c.not_three_dvd_orderOf (hAT.trans c.T_le_M) hAV hyN
      (c.centralizer_wClos_le_normalizer hAT hF.idx hy.2)
      (h3.trans ((orderOf_map_dvd ψ _).trans (by rw [Subgroup.orderOf_mk])))
  exact (mem_liftSub_iff ⟨y, hyN⟩).2 (mem_of_pow_three_mem hk h3)

omit [Finite X] in
theorem mem_cClos {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUseC (barSub ψ T) (barSub ψ (conjSubgroup V g)) Hb Rb) :
    u ∈ E3.cClos V 1 (liftSub ψ Rb) := by
  have hRT : liftSub ψ Rb ≤ T := by
    have := liftSub_mono (π := ψ) hF.R_le_T
    rwa [c.liftSub_barSub_T] at this
  have huY : u ∈ liftSub ψ Hb ⊓ centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) :=
    ⟨c.cClos_le_liftSub hAT hF.core ⟨w.le_T w.mem, w.cent_W1⟩,
      Subgroup.mem_centralizer_iff.2 fun z hz =>
        (Subgroup.mem_centralizer_iff.1 w.cent_W1) z (E3.wClos_mono hRT hz)⟩
  exact ⟨c.inf_centralizer_wClos_le hAT hF huY, huY.2⟩

omit [Finite X] in
theorem not_le_centralizer_cClos {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUseC (barSub ψ T) (barSub ψ (conjSubgroup V g)) Hb Rb) :
    ¬ conjSubgroup V g ≤ centralizer (E3.cClos V 1 (liftSub ψ Rb) : Set G) := by
  have huC1 := c.mem_cClos w hAT hF
  obtain ⟨h, rfl⟩ := w.conj
  intro hle
  set H := liftSub ψ Hb with hHdef
  set D := H ⊓ centralizer (E3.cClos V 1 (liftSub ψ Rb) : Set G) with hD
  have hHb : barSub ψ H = Hb := barSub_liftSub c.surj Hb
  have hHC : H ≤ normalizer (E3.cClos V 1 (liftSub ψ Rb) : Set G) :=
    (liftSub_le_normalizer hF.R_norm).trans (E3.normalizer_le_normalizer_cClos _)
  have hHD : H ≤ normalizer (D : Set G) := fun n hn =>
    mem_normalizer_inf (Subgroup.le_normalizer hn) (mem_normalizer_centralizer (hHC hn))
  obtain ⟨y, hy, hy3⟩ := hF.cD (barSub ψ D)
    (by rw [← hHb]; exact barSub_mono inf_le_left)
    (by rw [← hHb]; exact barSub_le_normalizer hHD)
    (barSub_mono (le_inf ((barSub_le_iff (hAT.trans c.TN)).1 hF.le) hle))
  obtain ⟨x, hxD, hx3⟩ := exists_orderOf_eq_of_barSub hy hy3
  exact c.not_orderOf_three_of_commute (w.le_T.trans c.T_le_M) w.ne w.mem w.ne_one
    (liftSub_le Hb hxD.1) ((Subgroup.mem_centralizer_iff.1 hxD.2) u huC1).symm hx3

omit [Finite X] in
theorem false_of_mem_center {g : G} (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUseC (barSub ψ T) (barSub ψ (conjSubgroup V g)) Hb Rb) {x : G}
    (hxA : x ∈ conjSubgroup V g) (hx1 : x ≠ 1) (hxW : x ∈ E3.wClos V 1 (liftSub ψ Rb))
    (hxZ : x ∈ centralizer (E3.wClos V 1 (liftSub ψ Rb) : Set G)) : False := by
  set A := conjSubgroup V g with hAdef
  have hAN : A ≤ N := hAT.trans c.TN
  have hHW : liftSub ψ Hb ≤ normalizer (E3.wClos V 1 (liftSub ψ Rb) : Set G) :=
    (liftSub_le_normalizer hF.R_norm).trans (E3.normalizer_le_normalizer_wClos _)
  obtain ⟨nb, hnbH, hP, a₁b, ha₁b, b₁b, hb₁b, hnc⟩ := hF.pair
  obtain ⟨n, rfl⟩ := c.surj nb
  have hnH : (n : G) ∈ liftSub ψ Hb := (mem_liftSub_iff n).2 hnbH
  set A' := conjSubgroup A (n : G)⁻¹ with hA'
  have hA'conj : A' = conjSubgroup V (g * (n : G)⁻¹) := conjSubgroup_conjSubgroup V g _
  have hx'A' : (n : G) * x * (n : G)⁻¹ ∈ A' := by
    rw [hA', mem_conjSubgroup_iff]
    simpa [mul_assoc] using hxA
  have hx'1 : (n : G) * x * (n : G)⁻¹ ≠ 1 := by
    intro h0
    apply hx1
    have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h0
    simpa [mul_assoc] using this
  have hxx' : x * ((n : G) * x * (n : G)⁻¹) = ((n : G) * x * (n : G)⁻¹) * x :=
    ((Subgroup.mem_centralizer_iff.1 hxZ) _
      ((Subgroup.mem_normalizer_iff.1 (hHW hnH) x).1 hxW)).symm
  have hNA' : A ⊓ normalizer (A' : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : x ∈ A ⊓ normalizer (A' : Set G) := by
      refine ⟨hxA, ?_⟩
      rw [hA'conj]
      exact centralizer_le_normalizer_conj c.ti (g * (n : G)⁻¹) (hA'conj ▸ hx'A') hx'1
        (Subgroup.mem_centralizer_singleton_iff.2 hxx')
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hA'N : A' ≤ N := by
    intro z hz
    have h1 : (n : G)⁻¹ * z * (n : G) ∈ N := by
      have := hAN (mem_conjSubgroup_iff.1 hz)
      simpa using this
    have := N.mul_mem (N.mul_mem n.2 h1) (N.inv_mem n.2)
    simpa [mul_assoc] using this
  have hP2 : IsPGroup 2 ↥(A ⊔ A') := by
    refine isPGroup_of_barSub c.ker (sup_le hAN hA'N) (hP.to_le ?_)
    rw [barSub_sup hAN hA'N]
    exact sup_le_sup le_rfl (barSub_conj_le n)
  have hcomm := commute_of_isPGroup_sup c.elem c.ti ⟨g, hAdef⟩ ⟨g * (n : G)⁻¹, hA'conj⟩ hNA' hP2
  obtain ⟨a₁, ha₁, rfl⟩ := ha₁b
  obtain ⟨b₁, hb₁, rfl⟩ := hb₁b
  have hb₁' : (b₁ : G) ∈ A := hb₁
  have hb' : ((n * b₁ * n⁻¹ : ↥N) : G) ∈ A' := by
    rw [hA', mem_conjSubgroup_iff]
    simpa [mul_assoc] using hb₁'
  apply hnc
  have h1' : a₁ * (n * b₁ * n⁻¹) = (n * b₁ * n⁻¹) * a₁ := Subtype.ext (hcomm (a₁ : G) ha₁ _ hb')
  simpa only [map_mul, map_inv] using congrArg ψ h1'

omit [Finite X] in
theorem false_of_fiveUseC {U : Subgroup G} {u : G} (w : Witness V T U u) {g : G}
    (hAT : conjSubgroup V g ≤ T) {Hb Rb : Subgroup X}
    (hF : FiveUseC (barSub ψ T) (barSub ψ (conjSubgroup V g)) Hb Rb) : False := by
  set A := conjSubgroup V g with hAdef
  set C1R := E3.cClos V 1 (liftSub ψ Rb) with hC1R
  have hAH : A ≤ liftSub ψ Hb := (barSub_le_iff (hAT.trans c.TN)).1 hF.le
  have hHC1R : liftSub ψ Hb ≤ normalizer (C1R : Set G) :=
    (liftSub_le_normalizer hF.R_norm).trans (E3.normalizer_le_normalizer_cClos _)
  obtain ⟨a, haA, cc, hcc, hne⟩ : ∃ a ∈ A, ∃ cc ∈ C1R, cc * a ≠ a * cc := by
    by_contra hcon
    refine c.not_le_centralizer_cClos w hAT hF fun a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro cc hcc
    by_contra hne
    exact hcon ⟨a, ha, cc, hcc, hne⟩
  have hccA : cc ∈ normalizer (A : Set G) := c.centralizer_wClos_le_normalizer hAT hF.idx hcc.2
  set x := cc * a * cc⁻¹ * a⁻¹ with hx
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hne
    calc cc * a = (cc * a * cc⁻¹ * a⁻¹) * (a * cc) := by group
      _ = a * cc := by rw [← hx, hx1, one_mul]
  have hxA : x ∈ A := A.mul_mem ((Subgroup.mem_normalizer_iff.1 hccA a).1 haA) (A.inv_mem haA)
  have hxC : x ∈ C1R := by
    have h1 : a * cc⁻¹ * a⁻¹ ∈ C1R :=
      (Subgroup.mem_normalizer_iff.1 (hHC1R (hAH haA)) cc⁻¹).1 (C1R.inv_mem hcc)
    have := C1R.mul_mem hcc h1
    simpa [hx, mul_assoc] using this
  exact c.false_of_mem_center hAT hF hxA hx1 ((c.inf_le_wClos hAT hF.idx).1 ⟨hxC.1, hxA⟩) hxC.2

end Ctx

end CFSG.LocalAnalysis.WeakClosure81.TC914
